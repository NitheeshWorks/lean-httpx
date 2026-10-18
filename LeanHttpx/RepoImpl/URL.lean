import LeanHttpx.DataTypes.URL
import LeanHttpx.RepoImpl.Text

/-!
# URL parsing and printing (`httpx/_urlparse.py`)

The parser is upstream's, stage by stage:

1. `checkInput`: at most 65536 characters, no ASCII control character.
2. `splitUrl`: scheme, authority, path, query, fragment (upstream `URL_REGEX`).
3. `splitAuth`: userinfo, host, port (upstream `AUTHORITY_REGEX`).
4. `build`: normalise and validate each component (lower-case scheme and
   host, percent-encode, validate address literals, drop the default port,
   validate the path and remove dot segments).

`build` is shared with `copyWith`, as upstream shares `urlparse` between
parsing and `copy_with`. The printer is upstream `ParseResult.__str__`.

Each stage is the inverse of a printing stage on canonical input; the proofs
are in `Proofs/URL.lean`.
-/

namespace LeanHttpx

open Chars

namespace URLParse

/-- Upstream `MAX_URL_LENGTH`. -/
def maxUrlLength : Nat := 65536

/-- Not the end of an authority: `/`, `?` or `#`. -/
def notAuthEnd (c : Char) : Bool := c != '/' && c != '?' && c != '#'

/-- Not the end of a path: `?` or `#`. -/
def notPathEnd (c : Char) : Bool := c != '?' && c != '#'

/-- The five top-level parts of a URL string, unnormalised. -/
structure RawParts where
  scheme : List Char
  authority : List Char
  path : List Char
  query : Option (List Char)
  fragment : Option (List Char)
  deriving DecidableEq, Repr

/-- The scheme and what follows it. -/
def splitScheme (s : List Char) : List Char × List Char :=
  match schemeOf s with
  | some p => p
  | none => ([], s)

/-- The authority (after `//`) and what follows it. -/
def splitAuthority (r : List Char) : List Char × List Char :=
  match r with
  | '/' :: '/' :: r => (r.takeWhile notAuthEnd, r.dropWhile notAuthEnd)
  | r => ([], r)

/-- The query (after `?`) and what follows it. -/
def splitQuery (r : List Char) : Option (List Char) × List Char :=
  match r with
  | '?' :: q => (some (q.takeWhile (· != '#')), q.dropWhile (· != '#'))
  | r => (none, r)

/-- The fragment (after `#`). -/
def splitFragment (r : List Char) : Option (List Char) :=
  match r with
  | '#' :: f => some f
  | _ => none

/-- Split a URL string into its five parts (upstream `URL_REGEX`). -/
def splitUrl (s : List Char) : RawParts :=
  let (scheme, r) := splitScheme s
  let (authority, r) := splitAuthority r
  let (query, r') := splitQuery (r.dropWhile notPathEnd)
  { scheme, authority, path := r.takeWhile notPathEnd, query, fragment := splitFragment r' }

/-- Print the five parts (upstream `ParseResult.__str__`). -/
def printRaw (p : RawParts) : List Char :=
  (if p.scheme.isEmpty then [] else p.scheme ++ [':']) ++
  (if p.authority.isEmpty then [] else '/' :: '/' :: p.authority) ++
  p.path ++
  (match p.query with | some q => '?' :: q | none => []) ++
  (match p.fragment with | some f => '#' :: f | none => [])

/-- Split an authority into userinfo, host and port text (upstream
`AUTHORITY_REGEX`): the userinfo runs to the last `@`; a host starting with
`[` runs to the last `]`, any other to the first `:`; the port is the rest,
after an optional `:`. -/
def splitAuth (a : List Char) : List Char × List Char × List Char :=
  let (ui, hp) :=
    if a.contains '@' then
      let r := a.reverse
      ((r.dropWhile (· != '@')).tail.reverse, (r.takeWhile (· != '@')).reverse)
    else ([], a)
  let (host, after) :=
    if hp.head? == some '[' && hp.contains ']' then
      let r := hp.reverse
      ((r.dropWhile (· != ']')).reverse, (r.takeWhile (· != ']')).reverse)
    else (hp.takeWhile (· != ':'), hp.dropWhile (· != ':'))
  let port := match after with
    | ':' :: p => p
    | p => p
  (ui, host, port)

/-- Print a host: in brackets if it contains a colon (an IPv6 literal). -/
def printHost (h : List Char) : List Char := if h.contains ':' then '[' :: h ++ [']'] else h

/-- The decimal digits of a port (`Keel.Codec.decimal`). -/
abbrev decimal (n : Nat) : List Char := Keel.Codec.decimal n

/-- Print an authority (upstream `ParseResult.authority`). -/
def printAuth (ui host : List Char) (port : Option Nat) : List Char :=
  (if ui.isEmpty then [] else ui ++ ['@']) ++ printHost host ++
  (match port with | some n => ':' :: decimal n | none => [])

/-- Python `repr` of a character list, for messages. -/
def r (l : List Char) : String := Text.pyRepr (String.ofList l)

/-- Normalise and validate a host (upstream `encode_host`). Non-ASCII hosts
need IDNA, which is not implemented: they are rejected (see CONTRIBUTING). -/
def encodeHost (h : List Char) : Except InvalidURL (List Char) :=
  if h.isEmpty then .ok []
  else if ipv4Style h then
    if validIPv4 h then .ok h else .error ⟨s!"Invalid IPv4 address: {r h}"⟩
  else if h.head? == some '[' && h.getLast? == some ']' && 2 ≤ h.length then
    let inner := (h.drop 1).dropLast
    if validIPv6 inner then .ok inner else .error ⟨s!"Invalid IPv6 address: {r h}"⟩
  else if h.all (·.toNat < 128) then .ok (quote hostSafe (lowerHost h))
  else .error ⟨s!"Invalid IDNA hostname: {r h}"⟩

/-- Parse and normalise a port (upstream `normalize_port`). Only ASCII digits
are a port (RFC 3986 `port = *DIGIT`); upstream's `int()` also takes signs,
spaces and underscores (see CONTRIBUTING). More than `maxIntDigits` digits
is invalid, as `int()` raises. -/
def normalizePort (p : List Char) (scheme : List Char) : Except InvalidURL (Option Nat) :=
  if p.isEmpty then .ok none
  else if p.all Char.isDigit && p.length ≤ maxIntDigits then
    let n := digitsValue p
    .ok (if some n == defaultPort scheme then none else some n)
  else .error ⟨s!"Invalid port: {r p}"⟩

/-- Remove `.` and `..` segments (upstream `normalize_path`, RFC 3986
section 5.2.4 as upstream applies it). -/
def normalizePath (p : List Char) : List Char :=
  if !p.contains '.' then p
  else if noDotSegments p then p
  else
    let out := (splitAt '/' p).foldl (fun (out : List (List Char)) seg =>
      if seg == ['.'] then out
      else if seg == ['.', '.'] then (if out.isEmpty || out == [[]] then out else out.tail)
      else seg :: out) []
    List.intercalate ['/'] out.reverse

/-- Upstream `validate_path`. -/
def validatePath (p : List Char) (hasScheme hasAuthority : Bool) : Except InvalidURL Unit :=
  if hasAuthority && !p.isEmpty && p.head? != some '/' then
    .error ⟨"For absolute URLs, path must be empty or begin with '/'"⟩
  else if !hasScheme && !hasAuthority && p.take 2 == ['/', '/'] then
    .error ⟨"Relative URLs cannot have a path starting with '//'"⟩
  else if !hasScheme && !hasAuthority && p.head? == some ':' then
    .error ⟨"Relative URLs cannot have a path starting with ':'"⟩
  else .ok ()

/-- Normalise and validate all components (the body of upstream `urlparse`
after splitting). The result is checked against `Canonical`; the two extra
path checks are where this port is stricter than upstream (see CONTRIBUTING):
a path that would print as an authority, or as a scheme, is rejected instead
of silently changing meaning when printed. -/
def build (scheme userinfo host port path : List Char) (query fragment : Option (List Char)) :
    Except InvalidURL URL := do
  let scheme := scheme.map Char.toLower
  let userinfo := quote userinfoSafe userinfo
  let host ← encodeHost host
  let port ← normalizePort port scheme
  let hasScheme := !scheme.isEmpty
  let hasAuthority := !userinfo.isEmpty || !host.isEmpty || port.isSome
  validatePath path hasScheme hasAuthority
  let path := quote pathSafe (if hasScheme || hasAuthority then normalizePath path else path)
  if !hasAuthority && path.take 2 == ['/', '/'] then
    throw ⟨"URLs without an authority cannot have a path starting with '//'"⟩
  if !hasScheme && !hasAuthority && (schemeOf path).isSome then
    throw ⟨"Relative URLs cannot have a first path segment that reads as a scheme"⟩
  let res : ParseResult :=
    { scheme := String.ofList scheme, userinfo := String.ofList userinfo,
      host := String.ofList host, port, path := String.ofList path,
      query := query.map fun q => String.ofList (quote querySafe q),
      fragment := fragment.map fun f => String.ofList (quote fragSafe f) }
  if h : res.Canonical then pure ⟨res, h⟩
  else throw ⟨"Internal error: URL normalisation did not reach canonical form"⟩

/-- Upstream's initial checks on a whole URL string. -/
def checkInput (s : List Char) : Except InvalidURL Unit :=
  if s.length > maxUrlLength then .error ⟨"URL too long"⟩
  else match s.findIdx? isAsciiControl with
    | some i =>
      let c := s.getD i ' '
      .error ⟨s!"Invalid non-printable ASCII character in URL, {Text.pyRepr c.toString} at position {i}."⟩
    | none => .ok ()

/-- Parse a URL string (upstream `urlparse(url)`). -/
def parse (s : List Char) : Except InvalidURL URL := do
  checkInput s
  let p := splitUrl s
  let (ui, host, port) := splitAuth p.authority
  build p.scheme ui host port p.path p.query p.fragment

/-- The five parts of a parse result, for printing. -/
def _root_.LeanHttpx.ParseResult.toRaw (r : ParseResult) : RawParts :=
  { scheme := r.scheme.toList,
    authority := printAuth r.userinfo.toList r.host.toList r.port,
    path := r.path.toList,
    query := r.query.map String.toList,
    fragment := r.fragment.map String.toList }

end URLParse

open URLParse

namespace URL

/-- Parse a URL (`httpx.URL(url)`). -/
def parse (s : String) : Except InvalidURL URL := URLParse.parse s.toList

/-- The URL as a string (`str(url)`). -/
protected def toString (u : URL) : String := String.ofList (printRaw u.ref.toRaw)

instance : ToString URL := ⟨URL.toString⟩

/-- The empty relative URL. -/
instance : Inhabited URL := ⟨⟨{}, by decide⟩⟩

instance : Repr URL := ⟨fun u _ => s!"URL({Text.pyRepr u.toString})"⟩

end URL

end LeanHttpx
