import LeanHttpx.DataTypes.Chars
import Keel.Codec

/-!
# URLs: the parsed form and its canonical-form invariant

httpx parses a URL into seven components (`httpx/_urlparse.py`,
`ParseResult`): scheme, userinfo, host, port, path, query and fragment, each
normalised (scheme and host lower-cased, components percent-encoded, default
ports dropped, dot segments removed). `ParseResult` is that tuple.

`ParseResult.Canonical` says the components are in the normal form the parser
produces: exactly the condition under which printing and re-parsing gives the
same URL back. A `URL` is a `ParseResult` with that invariant as a field.

The host classifiers (`ipv4Style`, `validIPv4`, `validIPv6`) follow Python's
`ipaddress`, which upstream uses to validate address literals.
-/

namespace LeanHttpx

open Chars

/-- The error httpx raises as `httpx.InvalidURL`. -/
structure InvalidURL where
  message : String
  deriving DecidableEq, Repr, Inhabited

instance : ToString InvalidURL := ⟨InvalidURL.message⟩

namespace URLParse

/-- The decimal value of a digit string (`Keel.Codec.digitsValue`). -/
abbrev digitsValue (l : List Char) : Nat := Keel.Codec.digitsValue l

/-- Split at every `c`. -/
abbrev splitAt (c : Char) (l : List Char) : List (List Char) := l.splitOn c

/-- Upstream's `IPv4_STYLE_HOSTNAME`: four dot-separated runs of digits. -/
def ipv4Style (l : List Char) : Bool :=
  let parts := splitAt '.' l
  parts.length == 4 && parts.all fun p => !p.isEmpty && p.all Char.isDigit

/-- A decimal octet as Python's `ipaddress` accepts it: one to three digits,
no leading zero, at most 255. -/
def decOctet (p : List Char) : Bool :=
  !p.isEmpty && p.length ≤ 3 && p.all Char.isDigit && (p.length == 1 || p.head? != some '0') &&
    digitsValue p ≤ 255

/-- A dotted-quad IPv4 address (`ipaddress.IPv4Address`). -/
def validIPv4 (l : List Char) : Bool :=
  let parts := splitAt '.' l
  parts.length == 4 && parts.all decOctet

/-- One to four hex digits. -/
def hextet (p : List Char) : Bool := !p.isEmpty && p.length ≤ 4 && p.all isHex

/-- The address part of an IPv6 literal (`ipaddress.IPv6Address._ip_int_from_string`):
eight hextets, or fewer with exactly one `::`, the last two optionally written
as a dotted quad; at most 45 characters. -/
def validIPv6Addr (l : List Char) : Bool :=
  let parts := splitAt ':' l
  if l.isEmpty || l.length > 45 || parts.length < 3 || parts.length > 9 + 1 then false else
  -- A trailing dotted quad stands for two hextets.
  let last := parts.getLastD []
  let (parts, ok4) :=
    if last.contains '.' then (parts.dropLast ++ [['0'], ['0']], validIPv4 last) else (parts, true)
  let n := parts.length
  if !ok4 || n > 9 then false else
  let inner := (List.range n).filter fun i => 0 < i && i + 1 < n && (parts.getD i []).isEmpty
  match inner with
  | [] =>
    n == 8 && parts.all hextet
  | [k] =>
    let lead := (parts.getD 0 []).isEmpty
    let trail := (parts.getD (n - 1) []).isEmpty
    let hi := if lead then k - 1 else k
    let lo := if trail then n - k - 2 else n - k - 1
    !(lead && hi != 0) && !(trail && lo != 0) && hi + lo < 8 &&
      (parts.take hi).all hextet && (parts.drop (n - lo)).all hextet
  | _ => false

/-- An IPv6 literal (`ipaddress.IPv6Address`): an address, optionally with a
zone index after `%`. The zone is limited to unreserved characters (Python
takes any characters but `%`; see CONTRIBUTING, deviations). -/
def validIPv6 (l : List Char) : Bool :=
  match splitAt '%' l with
  | [addr] => validIPv6Addr addr
  | [addr, zone] => validIPv6Addr addr && !zone.isEmpty && zone.all isUnreserved
  | _ => false

/-- Lower-case a host, leaving the two hex digits of each `%XX` escape as
they are. -/
def lowerHost (l : List Char) : List Char :=
  match splitAt '%' l with
  | [] => []
  | first :: rest =>
    let seg : List Char → List Char := fun s =>
      match s with
      | a :: b :: r => if isHex a && isHex b then a :: b :: r.map Char.toLower else s.map Char.toLower
      | _ => s.map Char.toLower
    List.intercalate ['%'] (first.map Char.toLower :: rest.map seg)

/-- The default port of a scheme (WHATWG). -/
def defaultPort (scheme : List Char) : Option Nat :=
  if scheme = "http".toList then some 80 else if scheme = "https".toList then some 443
  else if scheme = "ws".toList then some 80 else if scheme = "wss".toList then some 443
  else if scheme = "ftp".toList then some 21 else none

/-- What follows a leading colon. -/
def afterColon? : List Char → Option (List Char)
  | ':' :: r => some r
  | _ => none

/-- Where a relative reference would be misread as having a scheme: the
scheme that `l` starts with (empty for a leading colon) and what follows the
colon, if any. -/
def schemeOf (l : List Char) : Option (List Char × List Char) :=
  match l with
  | [] => none
  | c :: _ =>
    if c = ':' then some ([], l.tail)
    else if c.isAlpha then
      (afterColon? (l.dropWhile isSchemeChar)).map fun r => (l.takeWhile isSchemeChar, r)
    else none

/-- No path segment is `.` or `..`. -/
def noDotSegments (p : List Char) : Bool :=
  (splitAt '/' p).all fun s => s != ['.'] && s != ['.', '.']

/-- A scheme in normal form: empty, or a letter then scheme characters, all
lower case. -/
def schemeCanonical (s : List Char) : Bool :=
  s.isEmpty || ((s.head?.map Char.isAlpha).getD false && s.all isSchemeChar && s.all fun c => c.toLower == c)

/-- A character that can appear in a parsed host: graphic ASCII other than
the delimiters `@ / ? # [ ]`. -/
def hostChar (c : Char) : Bool :=
  isGraphic c && c != '@' && c != '/' && c != '?' && c != '#' && c != '[' && c != ']'

/-- A host in normal form: empty, an IPv4 address, an IPv6 address (which
contains a colon), or a registered name of host-safe characters that does not
look like an IPv4 address and is lower case outside its escapes. -/
def hostCanonical (h : List Char) : Bool :=
  h.all hostChar && (h.isEmpty || (ipv4Style h && validIPv4 h) || (h.contains ':' && validIPv6 h) ||
    (!ipv4Style h && h.all hostSafe && lowerHost h == h))

end URLParse

open URLParse

/-- The seven components of a parsed URL, each in its encoded form
(upstream `ParseResult`). `query` and `fragment` distinguish absent (`none`)
from empty (a trailing `?` or `#`). -/
structure ParseResult where
  scheme : String := ""
  userinfo : String := ""
  host : String := ""
  port : Option Nat := none
  path : String := ""
  query : Option String := none
  fragment : Option String := none
  deriving DecidableEq, Repr, Inhabited

namespace ParseResult

/-- The URL has an authority part: userinfo, host or port. -/
def hasAuthority (r : ParseResult) : Bool :=
  !r.userinfo.toList.isEmpty || !r.host.toList.isEmpty || r.port.isSome

/-- The path is in normal form for the rest of the URL: path-safe
characters; with an authority it is empty or starts with `/`; without one it
does not start with `//` (it would read as an authority); without scheme and
authority it does not start with something that reads as a scheme; and when
upstream normalises dot segments (scheme or authority present) there are none
left. -/
def pathCanonical (r : ParseResult) : Bool :=
  let p := r.path.toList
  p.all pathSafe &&
  (!r.hasAuthority || p.isEmpty || p.head? == some '/') &&
  (r.hasAuthority || !(p.take 2 == ['/', '/'])) &&
  (!r.scheme.toList.isEmpty || r.hasAuthority || (schemeOf p).isNone) &&
  ((r.scheme.toList.isEmpty && !r.hasAuthority) || noDotSegments p)

/-- **Canonical form**: every component is what the parser produces. -/
def Canonical (r : ParseResult) : Prop :=
  schemeCanonical r.scheme.toList = true ∧
  r.userinfo.toList.all userinfoSafe = true ∧
  hostCanonical r.host.toList = true ∧
  ((r.port.isNone || r.port != defaultPort r.scheme.toList) &&
    r.port.all fun n => (Keel.Codec.decimal n).length ≤ maxIntDigits) = true ∧
  r.pathCanonical = true ∧
  (r.query.map fun q => q.toList.all querySafe).getD true = true ∧
  (r.fragment.map fun f => f.toList.all fragSafe).getD true = true

instance (r : ParseResult) : Decidable r.Canonical := by
  unfold Canonical; exact inferInstance

end ParseResult

/-- A URL: parsed components in canonical form (`httpx.URL`). Two URLs are
equal exactly when their components are, which is when they print the same
(`URL.toString_injective`). -/
structure URL where
  ref : ParseResult
  canonical : ref.Canonical

end LeanHttpx
