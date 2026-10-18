import LeanHttpx.RepoImpl.URL
import LeanHttpx.RepoImpl.Headers

/-!
# URL properties, `copy_with` and `join` (`httpx/_urls.py`)

The properties of `httpx.URL` read the canonical components: `path` and
`fragment` are percent-decoded, `raw_path` is the request target, `netloc`
the `Host` header value. `copyWith` replaces components and normalises the
result exactly as parsing does (upstream `copy_with` calls `urlparse` with
the components as keyword arguments). `join` resolves a reference against
the URL by RFC 3986 section 5.2.
-/

namespace LeanHttpx

open URLParse

namespace URL

variable (u : URL)

/-- `url.scheme`. -/
def scheme : String := u.ref.scheme

/-- `url.userinfo`: the encoded userinfo. -/
def userinfo : String := u.ref.userinfo

/-- `url.username`, decoded. -/
def username : String := Text.unquote ((u.ref.userinfo.splitOn ":").headD "")

/-- `url.password`, decoded. -/
def password : String := Text.unquote (":".intercalate ((u.ref.userinfo.splitOn ":").drop 1))

/-- `url.host`: lower case; IPv6 without brackets. (IDNA hosts are not
supported, so this is also `raw_host`.) -/
def host : String := u.ref.host

/-- `url.port`: `none` for the scheme's default port. -/
def port : Option Nat := u.ref.port

/-- `url.netloc`: the host (in brackets if IPv6) and a non-default port. -/
def netloc : String :=
  String.ofList (printHost u.ref.host.toList) ++ (match u.ref.port with | some p => ":" ++ toString p | none => "")

/-- `url.path`, decoded, `/` when empty. -/
def path : String := Text.unquote (if u.ref.path.isEmpty then "/" else u.ref.path)

/-- `url.query`: the encoded query, without the `?`. -/
def query : String := u.ref.query.getD ""

/-- `url.raw_path`: the encoded path and query, the request target. -/
def rawPath : String :=
  (if u.ref.path.isEmpty then "/" else u.ref.path) ++ (match u.ref.query with | some q => "?" ++ q | none => "")

/-- `url.fragment`, decoded. -/
def fragment : String := Text.unquote (u.ref.fragment.getD "")

/-- `url.params`: the query parsed into a `QueryParams`. -/
def params : QueryParams := QueryParams.parse u.query

/-- `url.is_absolute_url`: a scheme and a host. -/
def isAbsoluteUrl : Bool := !u.ref.scheme.isEmpty && !u.ref.host.isEmpty

/-- `url.is_relative_url`. -/
def isRelativeUrl : Bool := !u.isAbsoluteUrl

instance : BEq URL := ⟨fun a b => a.ref == b.ref⟩

/-- The component patterns `copy_with` keyword arguments must match
(upstream `COMPONENT_REGEX`), and its control-character check. -/
def checkComponent (key : String) (v : List Char) : Except InvalidURL Unit := do
  if v.length > maxUrlLength then throw ⟨s!"URL component '{key}' too long"⟩
  match v.findIdx? Chars.isAsciiControl with
  | some i => throw ⟨s!"Invalid non-printable ASCII character in URL {key} component, {Text.pyRepr (v.getD i ' ').toString} at position {i}."⟩
  | none => pure ()
  let ok := match key with
    | "scheme" => v.isEmpty || ((v.head?.map Char.isAlpha).getD false && v.all Chars.isSchemeChar)
    | "path" => v.all notPathEnd
    | "query" => !v.contains '#'
    | "userinfo" => !v.contains '@'
    | "host" => (v.head? == some '[' && v.getLast? == some ']') || !v.contains ':'
    | _ => true
  unless ok do throw ⟨s!"Invalid URL component '{key}'"⟩

/-- `url.copy_with(...)`: the URL with the given components replaced, all of
them re-normalised. `username` and `password` are percent-encoded; a `host`
with a colon is an IPv6 literal; `params` replaces the query. -/
def copyWith (scheme : String := u.ref.scheme) (username : Option String := none)
    (password : Option String := none) (userinfo : String := u.ref.userinfo) (host : String := u.ref.host)
    (port : Option Nat := u.ref.port) (path : String := u.ref.path)
    (query : Option String := u.ref.query) (fragment : Option String := u.ref.fragment)
    (params : Option QueryParams := none) (netloc : Option String := none)
    (rawPath : Option String := none) : Except InvalidURL URL := do
  let (host, port) := match netloc with
    | some n => match n.splitOn ":" with
      | [h] => (h, none)
      | h :: p :: _ => (h, if p.length > maxIntDigits then none else p.toNat?)
      | [] => (host, port)
    | none => (host, port)
  let (path, query) := match rawPath with
    | some rp => match rp.splitOn "?" with
      | [p] => (p, none)
      | p :: q => (p, some ("?".intercalate q))
      | [] => (path, query)
    | none => (path, query)
  let userinfo :=
    if username.isSome || password.isSome then
      let un := String.ofList (Chars.quote Chars.usernameSafe (username.getD "").toList)
      let pw := String.ofList (Chars.quote Chars.usernameSafe (password.getD "").toList)
      if pw.isEmpty then un else un ++ ":" ++ pw
    else userinfo
  let host := if host.contains ':' && !(host.startsWith "[" && host.endsWith "]") then "[" ++ host ++ "]" else host
  let query := match params with
    | some p => if p.isEmpty then none else some (toString p)
    | none => query
  checkComponent "scheme" scheme.toList
  checkComponent "userinfo" userinfo.toList
  checkComponent "host" host.toList
  checkComponent "path" path.toList
  if let some q := query then checkComponent "query" q.toList
  if let some f := fragment then checkComponent "fragment" f.toList
  build scheme.toList userinfo.toList host.toList ((port.map decimal).getD []) path.toList
    (query.map String.toList) (fragment.map String.toList)

/-- `url.copy_set_param(key, value)`. -/
def copySetParam (key value : String) : Except InvalidURL URL := u.copyWith (params := some (u.params.set key value))

/-- `url.copy_add_param(key, value)`. -/
def copyAddParam (key value : String) : Except InvalidURL URL := u.copyWith (params := some (u.params.add key value))

/-- `url.copy_remove_param(key)`. -/
def copyRemoveParam (key : String) : Except InvalidURL URL := u.copyWith (params := some (u.params.remove key))

/-- `url.copy_merge_params(params)`. -/
def copyMergeParams (p : QueryParams) : Except InvalidURL URL := u.copyWith (params := some (u.params.merge p))

/-- A URL from components (`httpx.URL(scheme=..., host=..., ...)`). -/
def ofComponents (scheme : String := "") (host : String := "") (port : Option Nat := none)
    (path : String := "") (query : Option String := none) (fragment : Option String := none) :
    Except InvalidURL URL :=
  (⟨{}, by decide⟩ : URL).copyWith (scheme := scheme) (host := host) (port := port) (path := path)
    (query := query) (fragment := fragment)

/-- RFC 3986 section 5.2.4, `remove_dot_segments`, on the segments of a path. -/
def removeDotSegments (segs : List (List Char)) : List (List Char) :=
  let out := segs.foldl (fun (out : List (List Char)) s =>
    if s == ['.'] then out else if s == ['.', '.'] then out.drop 1 else s :: out) []
  out.reverse

/-- The merged and dot-free path of a reference against a base
(RFC 3986 sections 5.2.2 to 5.2.4). -/
def resolvePath (baseHasAuthority : Bool) (basePath refPath : List Char) : List Char :=
  let merged :=
    if refPath.head? == some '/' then refPath
    else if baseHasAuthority && basePath.isEmpty then '/' :: refPath
    else List.intercalate ['/'] ((basePath.splitOn '/').dropLast ++ [refPath])
  let segs := merged.splitOn '/'
  let last := segs.getLastD []
  let kept := removeDotSegments segs
  let kept := if last == ['.'] || last == ['.', '.'] then kept ++ [[]] else kept
  -- A leading empty segment is the root: keep it.
  let kept := if merged.head? == some '/' && kept.head? != some [] then [] :: kept else kept
  List.intercalate ['/'] kept

/-- **`url.join(ref)`**: resolve a reference against this URL (RFC 3986
section 5.2.2, non-strict: a reference with the base's scheme is treated as
relative, as browsers and `urllib.parse.urljoin` do). The result is
normalised by `build`, as httpx re-parses it. -/
def join (ref : String) : Except InvalidURL URL := do
  let r ← URL.parse ref
  let b := u.ref
  let r := if r.ref.scheme == b.scheme && r.ref.host.isEmpty && r.ref.userinfo.isEmpty &&
      r.ref.port.isNone && !r.ref.scheme.isEmpty then { r.ref with scheme := "" } else r.ref
  let rHasAuth := !r.userinfo.isEmpty || !r.host.isEmpty || r.port.isSome
  let bHasAuth := b.hasAuthority
  let (scheme, ui, host, port, path, query) :=
    if !r.scheme.isEmpty then (r.scheme, r.userinfo, r.host, r.port, r.path, r.query)
    else if rHasAuth then (b.scheme, r.userinfo, r.host, r.port, r.path, r.query)
    else if r.path.isEmpty then
      (b.scheme, b.userinfo, b.host, b.port, b.path, if r.query.isSome then r.query else b.query)
    else (b.scheme, b.userinfo, b.host, b.port, String.ofList (resolvePath bHasAuth b.path.toList r.path.toList), r.query)
  build scheme.toList ui.toList (printHost host.toList) ((port.map decimal).getD []) path.toList
    (query.map String.toList) (r.fragment.map String.toList)

end URL

end LeanHttpx
