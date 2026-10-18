import LeanHttpx.DataTypes.Models

/-!
# The cookie jar (`httpx.Cookies` over `http.cookiejar`)

httpx keeps cookies in Python's `http.cookiejar.CookieJar` with its
`DefaultCookiePolicy`: Netscape cookies (RFC 2109 cookies are treated as
Netscape ones), liberal domain matching, and no third-party blocking. This
module is that policy, as pure functions of the request URL and the current
time:

* `parseSetCookie` is `parse_ns_headers` and `_cookie_from_cookie_tuple`;
* `setOk` is `DefaultCookiePolicy.set_ok` (the domain check);
* `domainReturnOk`, `pathReturnOk` and `returnOk` decide which cookies a
  request carries, and `cookieHeader` builds the `Cookie` header from them,
  longest path first.

The time is a parameter (`now`, Unix seconds), so the jar is a value; the
client supplies the clock.
-/

namespace LeanHttpx

namespace CookieJar

/-! ## Request host and path (`request_host`, `eff_request_host`, `request_path`) -/

/-- The request host: the URL's host, lower case, IPv6 in brackets. -/
def requestHost (url : URL) : String :=
  asciiLower (String.ofList (URLParse.printHost url.ref.host.toList))

/-- The effective request host: a host without a dot gets `.local`. -/
def effRequestHost (url : URL) : String :=
  let h := requestHost url
  if h.contains '.' then h else h ++ ".local"

/-- `escape_path`: percent-encode characters outside
``%/;:@&=+$,!~*'()`` and the unreserved ones, upper-casing all escapes. -/
def escapePath (p : String) : String :=
  let safe (c : Char) : Bool := Chars.isUnreserved c || "%/;:@&=+$,!~*'()".contains c
  let q := Chars.quote safe p.toList
  let rec up : List Char → List Char
    | '%' :: a :: b :: r => if Chars.isHex a && Chars.isHex b then '%' :: a.toUpper :: b.toUpper :: up r
                            else '%' :: up (a :: b :: r)
    | c :: r => c :: up r
    | [] => []
  String.ofList (up q)

/-- The request path: the URL's path, escaped, starting with `/`. -/
def requestPath (url : URL) : String :=
  let p := escapePath url.ref.path
  if p.startsWith "/" then p else "/" ++ p

/-- Whether the request is over a secure protocol (`https`, `wss`). -/
def isSecure (url : URL) : Bool := url.ref.scheme == "https" || url.ref.scheme == "wss"

/-! ## Matching (`DefaultCookiePolicy`) -/

/-- **Path match** (`path_return_ok`, RFC 6265 section 5.1.4): the request
path is the cookie path, or starts with it at a `/` boundary. -/
def pathReturnOk (cookiePath reqPath : String) : Bool :=
  let c := cookiePath.toList
  let r := reqPath.toList
  r == c || (c.isPrefixOf r && (c.getLast? == some '/' || r[c.length]? == some '/'))

/-- The domain with a leading dot (an empty domain stays empty). -/
def dotted (d : String) : String := if d.isEmpty || d.startsWith "." then d else "." ++ d

/-- **Domain match** for a stored domain (`domain_return_ok` and
`return_ok_domain` for Netscape cookies): the dotted request host ends with
the dotted cookie domain. -/
def domainReturnOk (domain : String) (url : URL) : Bool :=
  let d := (dotted domain).toList
  d.isSuffixOf (dotted (requestHost url)).toList || d.isSuffixOf (dotted (effRequestHost url)).toList

/-- Whether a cookie has expired at time `now`. -/
def _root_.LeanHttpx.Cookie.isExpired (c : Cookie) (now : Int) : Bool :=
  match c.expires with
  | some e => e ≤ now
  | none => false

/-- `return_ok`: secure cookies only over a secure protocol, not expired,
and the domain matches (`return_ok_domain`). -/
def returnOk (c : Cookie) (url : URL) (now : Int) : Bool :=
  (!c.secure || isSecure url) && !c.isExpired now &&
    ("." ++ effRequestHost url).endsWith (dotted c.domain)

/-- `set_ok` under the default policy: a `Domain` attribute must contain an
embedded dot (unless the host is a `.local` one) and the effective request
host must end with it. -/
def setOk (c : Cookie) (url : URL) : Bool :=
  if !c.domainSpecified then true else
  let erhn := effRequestHost url
  let domain := c.domain
  let undotted := if domain.startsWith "." then domain.drop 1 |>.toString else domain
  let embeddedDots := undotted.contains '.'
  if !embeddedDots && !erhn.endsWith ".local" then false
  else
    !(!(erhn.endsWith domain || erhn.endsWith (undotted ++ ".local")) &&
      (!erhn.startsWith "." && !("." ++ erhn).endsWith domain))

/-! ## Expiry dates (`http2time`) -/

/-- Days from 1970-01-01 to a civil date (proleptic Gregorian). -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The three-letter month names. -/
def months : List String := ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]

/-- The month of a name (by its first three letters) or a number. -/
def monthOf (s : String) : Option Nat :=
  let l := asciiLower s
  match months.findIdx? (fun m => l == m || (l.length > 3 && l.startsWith m)) with
  | some i => some (i + 1)
  | none => match s.toNat? with
    | some n => if 1 ≤ n && n ≤ 12 then some n else none
    | none => none

/-- `http2time`, for the formats cookies use: `Wed, 09 Feb 1994 22:23:32 GMT`,
`Wednesday, 09-Feb-94 22:23:32 GMT` and the same without a weekday. Two-digit
years take the century nearest `currentYear`. Only UTC zones and numeric
offsets are understood; anything else is `none`. -/
def httpToTime (text : String) (currentYear : Int) : Option Int := do
  let parts := (text.trimAscii.toString.splitOn " ").flatMap (·.splitOn "-") |>.flatMap (·.splitOn "/")
    |>.filter (!·.isEmpty)
  let parts := match parts with
    | w :: rest => if (w.toList.all Char.isAlpha || w.endsWith ",") && (w.toList.head?.map Char.isAlpha).getD false
                   then rest else w :: rest
    | [] => []
  match parts with
  | day :: mon :: yr :: rest =>
    let d ← day.toNat?
    let m ← monthOf mon
    let y ← yr.toNat?
    let y : Int := if yr.length ≤ 2 then
        let m100 := currentYear % 100
        let y0 := (y : Int) + currentYear - m100
        let diff := m100 - y
        if diff > 50 then y0 + 100 else if diff < -50 then y0 - 100 else y0
      else y
    let (hh, mm, ss, tz) ← match rest with
      | [] => some (0, 0, 0, "UTC")
      | [clock] => (match clock.splitOn ":" with
          | [h, mi] => do pure (← h.toNat?, ← mi.toNat?, 0, "UTC")
          | [h, mi, s] => do pure (← h.toNat?, ← mi.toNat?, ← s.toNat?, "UTC")
          | _ => none)
      | [clock, tz] => (match clock.splitOn ":" with
          | [h, mi] => do pure (← h.toNat?, ← mi.toNat?, 0, tz)
          | [h, mi, s] => do pure (← h.toNat?, ← mi.toNat?, ← s.toNat?, tz)
          | _ => none)
      | _ => none
    if !(y ≥ 1970 && 1 ≤ d && d ≤ 31 && hh ≤ 24 && mm ≤ 59 && ss ≤ 61) then none else
    let tzu := tz.toUpper
    let offset : Option Int :=
      if tzu == "GMT" || tzu == "UTC" || tzu == "UT" || tzu == "Z" then some 0
      else
        let (sign, digits) := if tzu.startsWith "-" then (-1, tzu.drop 1 |>.toString)
          else if tzu.startsWith "+" then (1, tzu.drop 1 |>.toString) else (1, tzu)
        let digits := String.ofList (digits.toList.filter (· != ':'))
        if digits.toList.all Char.isDigit && (digits.length == 2 || digits.length == 4) then
          let h := (digits.take 2).toString.toNat!
          let mi := if digits.length == 4 then (digits.drop 2).toString.toNat! else 0
          some (sign * (3600 * h + 60 * mi))
        else none
    let off ← offset
    pure (daysFromCivil y m d * 86400 + hh * 3600 + mm * 60 + ss - off)
  | _ => none

/-! ## Parsing `Set-Cookie` -/

/-- One `Set-Cookie` value as `parse_ns_headers` splits it: the name and
value, then the attributes (known names lower-cased). An empty name drops
the cookie. -/
def splitSetCookie (header : String) : Option (String × Option String × List (String × Option String)) :=
  let params := (header.splitOn ";").map fun p => p.trimAscii.toString
  let pairs := params.map fun p =>
    match p.splitOn "=" with
    | [k] => (k.trimAscii.toString, none)
    | k :: rest => (k.trimAscii.toString, some ("=".intercalate rest).trimAscii.toString)
    | [] => ("", none)
  match pairs with
  | (name, value) :: attrs =>
    if name.isEmpty then none else
    let known := ["expires", "domain", "path", "secure", "version", "port", "max-age", "discard",
      "comment", "commenturl", "httponly", "samesite"]
    some (name, value, (attrs.filter (!·.1.isEmpty)).map fun (k, v) =>
      let lc := asciiLower k
      (if known.contains lc then lc else k, v))
  | [] => none

/-- Strip one pair of surrounding double quotes. -/
def stripQuotes (s : String) : String :=
  if s.length ≥ 2 && s.startsWith "\"" && s.endsWith "\"" then ((s.drop 1).dropEnd 1).toString else s

/-- The cookie a `Set-Cookie` value sets for a request to `url` at time
`now`, or `none` when it is malformed (`_normalized_cookie_tuples`,
`_cookie_from_cookie_tuple`). The second component says the cookie is
already expired: it deletes any stored cookie with its key. -/
def parseSetCookie (header : String) (url : URL) (now currentYear : Int) : Option (Cookie × Bool) := do
  let (name, value, attrs) ← splitSetCookie header
  -- The first occurrence of each attribute wins; Max-Age beats Expires.
  let first (k : String) : Option (Option String) := (attrs.find? (·.1 == k)).map (·.2)
  let domainAttr := first "domain"
  if domainAttr == some none then none
  let maxAge := first "max-age"
  let expires : Option Int ← match maxAge with
    | some (some v) => match v.toInt? with
      | some n => pure (some (now + n))
      | none => none
    | some none => none
    | none => match first "expires" with
      | some (some v) => pure (httpToTime (stripQuotes v) currentYear)
      | _ => pure none
  let pathAttr := match first "path" with
    | some (some p) => if p.isEmpty then none else some p
    | _ => none
  let (path, pathSpecified) := match pathAttr with
    | some p => (escapePath p, true)
    | none =>
      let rp := requestPath url
      let i := (rp.toList.reverse.findIdx? (· == '/')).map (rp.length - 1 - ·)
      let p := match i with | some i => (rp.take i).toString | none => rp
      (if p.isEmpty then "/" else p, false)
  let (domain, domainSpecified, initialDot) := match domainAttr with
    | some (some d) =>
      let d := asciiLower d
      (if d.startsWith "." then d else "." ++ d, true, d.startsWith ".")
    | _ => (effRequestHost url, false, false)
  let secure := (first "secure").isSome
  let cookie : Cookie := Cookie.mk name value domain domainSpecified initialDot path pathSpecified
    secure expires expires.isNone
  pure (cookie, match expires with | some e => e ≤ now | none => false)

end CookieJar

open CookieJar

namespace Cookies

variable (c : Cookies)

/-- Every cookie, by domain, path and name (`for cookie in jar`). -/
def toList : List Cookie := c.jar

/-- The key a jar stores a cookie under. -/
def _root_.LeanHttpx.Cookie.key (ck : Cookie) : String × String × String := (ck.domain, ck.path, ck.name)

/-- Where a new key goes: after the last cookie of its domain and path, else
after the last of its domain, else at the end (dictionary insertion order,
level by level). -/
def insertPos (l : List Cookie) (ck : Cookie) : Nat :=
  let after (p : Cookie → Bool) : Option Nat :=
    (l.reverse.findIdx? p).map fun i => l.length - i
  ((after fun x => x.domain == ck.domain && x.path == ck.path).orElse
    fun _ => after fun x => x.domain == ck.domain).getD l.length

/-- **Store a cookie** (`CookieJar.set_cookie`): it replaces a cookie with
the same key in place; a new key is inserted in insertion order. -/
def setCookie (ck : Cookie) : Cookies :=
  let pos := (c.jar.findIdx? (·.key == ck.key)).getD (insertPos c.jar ck)
  let rest := c.jar.filter (·.key != ck.key)
  ⟨rest.take pos ++ ck :: rest.drop pos⟩

/-- Remove the cookie with a key (`CookieJar.clear(domain, path, name)`). -/
def clearKey (domain path name : String) : Cookies :=
  ⟨c.jar.filter (·.key != (domain, path, name))⟩

/-- `cookies.set(name, value, domain="", path="/")`. -/
def set (name value : String) (domain : String := "") (path : String := "/") : Cookies :=
  c.setCookie (Cookie.mk name (some value) domain (!domain.isEmpty) (domain.startsWith ".") path true
    false none true)

/-- The cookies with a name, optionally only for a domain and path. -/
def matching (name : String) (domain path : Option String := none) : List Cookie :=
  c.toList.filter fun ck => ck.name == name && (domain.all (· == ck.domain)) && (path.all (· == ck.path))

/-- `cookies.get(name, domain=None, path=None)`: the value, or an error when
several cookies match (`CookieConflict`). -/
def get? (name : String) (domain path : Option String := none) : Except HTTPError (Option String) :=
  match c.matching name domain path with
  | [] => .ok none
  | [ck] => .ok ck.value
  | _ => .error (.cookieConflict s!"Multiple cookies exist with name={name}")

/-- `cookies.delete(name, domain=None, path=None)`. -/
def delete (name : String) (domain path : Option String := none) : Cookies :=
  (c.matching name domain path).foldl (fun j ck => j.clearKey ck.domain ck.path ck.name) c

/-- `cookies.clear(domain=None, path=None)`. -/
def clear (domain path : Option String := none) : Cookies :=
  ⟨c.jar.filter fun ck => !(domain.all (· == ck.domain) && path.all (· == ck.path))⟩

/-- `cookies.update(other)`: store every cookie of `other`. -/
def update (other : Cookies) : Cookies := other.toList.foldl setCookie c

/-- The cookie names (`for name in cookies`). -/
def names : List String := c.toList.map (·.name)

/-- `repr(cookies)`. -/
def pyRepr : String :=
  "<Cookies[" ++ ", ".intercalate (c.toList.map fun ck =>
    s!"<Cookie {ck.name}={ck.value.getD ""} for {ck.domain} />") ++ "]>"

/-- The number of cookies. -/
def size : Nat := c.toList.length

/-- From `(name, value)` pairs (`httpx.Cookies({...})`). -/
def ofList (l : List (String × String)) : Cookies := l.foldl (fun j p => j.set p.1 p.2) {}

instance : Coe (List (String × String)) Cookies := ⟨ofList⟩

/-- A cookie goes with a request: domain match, path match, and `return_ok`
(secure, unexpired, domain). -/
def matchesRequest (ck : Cookie) (url : URL) (now : Int) : Bool :=
  domainReturnOk ck.domain url && pathReturnOk ck.path (requestPath url) && returnOk ck url now

/-- **The cookies a request to `url` carries at time `now`**
(`_cookies_for_request`): those whose domain and path match and that
`return_ok` accepts, in jar order. -/
def cookiesForRequest (url : URL) (now : Int) : List Cookie :=
  c.jar.filter fun ck => matchesRequest ck url now

/-- The `Cookie` header value for a request (`_cookie_attrs`): longest path
first, `name=value` (or the bare name), joined with `"; "`. -/
def cookieHeader (url : URL) (now : Int) : Option String :=
  let cks := (c.cookiesForRequest url now).mergeSort fun a b => a.path.length ≥ b.path.length
  if cks.isEmpty then none else
  some ("; ".intercalate (cks.map fun ck => match ck.value with
    | some v => ck.name ++ "=" ++ v
    | none => ck.name))

/-- Store the cookies a response's `Set-Cookie` headers set, where the
policy allows (`extract_cookies`). An already-expired cookie deletes its
key instead. -/
def extract (setCookies : List String) (url : URL) (now currentYear : Int) : Cookies :=
  setCookies.foldl (fun j h =>
    match parseSetCookie h url now currentYear with
    | some (ck, true) => j.clearKey ck.domain ck.path ck.name
    | some (ck, false) => if setOk ck url then j.setCookie ck else j
    | none => j) c

end Cookies

end LeanHttpx
