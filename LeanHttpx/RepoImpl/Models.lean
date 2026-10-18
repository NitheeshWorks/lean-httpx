import LeanHttpx.RepoImpl.URLOps
import LeanHttpx.RepoImpl.Cookies
import LeanHttpx.DataTypes.Status
import LeanJson

/-!
# Building requests and reading responses (`httpx/_models.py`, `_content.py`)

* `Request.new` is `httpx.Request(method, url, params=, headers=, cookies=,
  content=, data=, json=)`: the body and its `Content-Length` and
  `Content-Type`, then the automatic `Host` and `Content-Length: 0` headers
  first, as upstream's `_prepare` puts them.
* `Response.new` is `httpx.Response(status_code, headers=, content=, text=,
  html=, json=)`.
* The `Response` properties: `text` (decoded by the charset of the content
  type, else the default encoding), `json`, `raiseForStatus` with upstream's
  messages, the status classes, `hasRedirectLocation`, `reasonPhrase`,
  `cookies` and `links`.
-/

namespace LeanHttpx

open LeanJson (Json)

/-- A request body (`content=`): bytes or text (UTF-8). -/
inductive Content where
  | bytes (b : ByteArray)
  | text (s : String)

instance : Coe ByteArray Content := ⟨.bytes⟩
instance : Coe String Content := ⟨.text⟩

/-- The bytes of a body. -/
def Content.toBytes : Content → ByteArray
  | .bytes b => b
  | .text s => s.toUTF8

/-- Compact JSON with non-ASCII characters as they are, as httpx encodes
`json=` (`separators=(",", ":"), ensure_ascii=False`). -/
def jsonBytes (j : Json) : ByteArray := (LeanJson.to_json j).val

/-- The body and its content headers (upstream `encode_request`):
`content=` first, then form `data=`, then `json=`. -/
def encodeRequest (content : Option Content) (data : List (String × String))
    (json : Option Json) : List (String × String) × ByteArray :=
  match content with
  | some c => let b := c.toBytes; ([("Content-Length", toString b.size)], b)
  | none =>
    if !data.isEmpty then
      let b := (toString (QueryParams.ofList data)).toUTF8
      ([("Content-Length", toString b.size), ("Content-Type", "application/x-www-form-urlencoded")], b)
    else match json with
      | some j => let b := jsonBytes j
        ([("Content-Length", toString b.size), ("Content-Type", "application/json")], b)
      | none => ([], .empty)

namespace Request

/-- **`httpx.Request(method, url, ...)`**. `params` replaces the URL's
query, as upstream does. `cookies` sets the `Cookie` header. -/
def new (method : String) (url : URL) (params : Option QueryParams := none) (headers : Headers := {})
    (cookies : Cookies := {}) (content : Option Content := none) (data : List (String × String) := [])
    (json : Option Json := none) (timeout : Timeout := {}) : Except InvalidURL Request := do
  let url ← match params with
    | some p => url.copyWith (params := some p)
    | none => pure url
  let headers := match cookies.cookieHeader url 0 with
    | some v => if headers.contains "Cookie" then headers else headers.set "Cookie" v
    | none => headers
  let (defaults, body) := encodeRequest content data json
  let headers := defaults.foldl (fun h (k, v) =>
    if asciiLower k == "transfer-encoding" && h.contains "Content-Length" then h else h.setdefault k v) headers
  let method := method.toUpper
  let auto : List (String × String) :=
    (if !headers.contains "Host" && !url.host.isEmpty then [("Host", url.netloc)] else []) ++
    (if !(headers.contains "Content-Length" || headers.contains "Transfer-Encoding") &&
        (method == "POST" || method == "PUT" || method == "PATCH") then [("Content-Length", "0")] else [])
  pure { method, url, headers := ⟨auto ++ headers.raw⟩, content := body, timeout }

instance : Repr Request := ⟨fun r _ => s!"<Request({Text.pyRepr r.method}, {Text.pyRepr r.url.toString})>"⟩

end Request

namespace Response

variable (r : Response)

/-- **`httpx.Response(status_code, ...)`**: `content=`, `text=`, `html=` or
`json=`, with the `Content-Length` and `Content-Type` they imply. -/
def new (statusCode : Nat) (headers : Headers := {}) (content : Option Content := none)
    (text : Option String := none) (html : Option String := none) (json : Option Json := none)
    (request : Option Request := none) : Response :=
  let (defaults, body) : List (String × String) × ByteArray :=
    match content, text, html, json with
    | some c, _, _, _ => let b := c.toBytes; ([("Content-Length", toString b.size)], b)
    | none, some t, _, _ =>
      ([("Content-Length", toString t.utf8ByteSize), ("Content-Type", "text/plain; charset=utf-8")], t.toUTF8)
    | none, none, some h, _ =>
      ([("Content-Length", toString h.utf8ByteSize), ("Content-Type", "text/html; charset=utf-8")], h.toUTF8)
    | none, none, none, some j => let b := jsonBytes j
      ([("Content-Length", toString b.size), ("Content-Type", "application/json")], b)
    | none, none, none, none => ([], .empty)
  let headers := defaults.foldl (fun h (k, v) =>
    if asciiLower k == "transfer-encoding" && h.contains "content-length" then h else h.setdefault k v) headers
  { statusCode, headers, content := body, request? := request }

/-- The request that produced it (`response.request`); a default request
when none was attached. -/
def request : Request := r.request?.getD default

/-- `response.url`. -/
def url : URL := r.request.url

/-- `response.reason_phrase`. -/
def reasonPhrase : String := r.reasonPhrase?.getD (codes.getReasonPhrase r.statusCode)

/-- `is_informational`, `is_success`, `is_redirect`, `is_client_error`,
`is_server_error`, `is_error`. -/
def isInformational : Bool := codes.isInformational r.statusCode
def isSuccess : Bool := codes.isSuccess r.statusCode
def isRedirect : Bool := codes.isRedirect r.statusCode
def isClientError : Bool := codes.isClientError r.statusCode
def isServerError : Bool := codes.isServerError r.statusCode
def isError : Bool := codes.isError r.statusCode

/-- `has_redirect_location`: 301, 302, 303, 307 or 308 with a `Location`. -/
def hasRedirectLocation : Bool :=
  [301, 302, 303, 307, 308].contains r.statusCode && r.headers.contains "Location"

/-- A parameter of a `Content-Type` value (as `email.message` reads it). -/
def contentTypeParam (ct name : String) : Option String :=
  ((ct.splitOn ";").drop 1).findSome? fun p =>
    match p.splitOn "=" with
    | k :: v => if asciiLower k.trimAscii.toString == name then
        some (CookieJar.stripQuotes ("=".intercalate v).trimAscii.toString) else none
    | [] => none

/-- `response.charset_encoding`: the `charset` of the content type. -/
def charsetEncoding : Option String :=
  (r.headers.get? "Content-Type").bind fun ct => (contentTypeParam ct "charset").map asciiLower

/-- The encodings `text` can decode. -/
def knownEncoding (e : String) : Bool :=
  ["utf-8", "utf8", "ascii", "us-ascii", "latin-1", "latin1", "iso-8859-1", "iso8859-1"].contains (asciiLower e)

/-- `response.encoding`. -/
def encoding : String :=
  match r.charsetEncoding with
  | some e => if knownEncoding e then e else r.defaultEncoding
  | none => r.defaultEncoding

/-- Decode bytes by an encoding name. -/
def decodeText (enc : String) (b : ByteArray) : String :=
  let e := asciiLower enc
  if e == "latin-1" || e == "latin1" || e == "iso-8859-1" || e == "iso8859-1" then
    b.foldl (fun s x => s.push (Char.ofNat x.toNat)) ""
  else if e == "ascii" || e == "us-ascii" then
    b.foldl (fun s x => s.push (if x < 128 then Char.ofNat x.toNat else '�')) ""
  else Text.utf8DecodeReplace b

/-- `response.text`. -/
def text : String := if r.content.isEmpty then "" else decodeText r.encoding r.content

/-- **`response.json()`**: the content parsed as JSON. -/
def json : Except HTTPError Json :=
  match LeanJson.from_json r.content with
  | .ok v => .ok v.val
  | .error e => .error (.decodingError s!"Invalid JSON: {e.description}")

/-- **`response.raise_for_status()`**: the response itself when it is a
success, else `HTTPStatusError` with upstream's message. -/
def raiseForStatus : Except HTTPError Response :=
  if r.isSuccess then .ok r else
  let errorType := match r.statusCode / 100 with
    | 1 => "Informational response" | 3 => "Redirect response" | 4 => "Client error"
    | 5 => "Server error" | _ => "Invalid status code"
  let head := s!"{errorType} '{r.statusCode} {r.reasonPhrase}' for url '{r.url}'\n"
  let loc := if r.hasRedirectLocation then s!"Redirect location: '{(r.headers.get? "location").getD ""}'\n" else ""
  let tail := s!"For more information check: https://developer.mozilla.org/en-US/docs/Web/HTTP/Status/{r.statusCode}"
  .error (.httpStatusError (head ++ loc ++ tail) r.request r)

/-- `response.cookies`: the cookies its `Set-Cookie` headers set. -/
def cookies (now : Int := 0) (currentYear : Int := 1970) : Cookies :=
  ({} : Cookies).extract (r.headers.getList "set-cookie") r.url now currentYear

/-- `response.links`: the parsed `Link` header, keyed by `rel` (else `url`). -/
def links : List (String × List (String × String)) :=
  match r.headers.get? "link" with
  | none => []
  | some v =>
    let strip (s : String) : String := (s.toList.dropWhile (" '\"".contains ·)).reverse.dropWhile (" '\"".contains ·)
      |>.reverse |> String.ofList
    let v := strip v
    if v.isEmpty then [] else
    -- Split at ", <" (a comma, optional spaces, then "<").
    let parts := (v.splitOn ",").foldl (fun (acc : List String) p =>
      if p.trimAsciiStart.toString.startsWith "<" || acc.isEmpty then acc ++ [p.trimAsciiStart.toString]
      else acc.dropLast ++ [acc.getLastD "" ++ "," ++ p]) []
    parts.map fun part =>
      let (url, params) := match part.splitOn ";" with
        | u :: ps => (u, ps)
        | [] => (part, [])
      let urlS := String.ofList ((url.toList.dropWhile ("<> '\"".contains ·)).reverse.dropWhile ("<> '\"".contains ·)).reverse
      let rec go : List String → List (String × String)
        | [] => []
        | p :: ps => match p.splitOn "=" with
          | [k, v] => (strip k, strip v) :: go ps
          | _ => []
      let fields := ("url", urlS) :: go params
      (((fields.find? (·.1 == "rel")).map (·.2)).getD urlS, fields)

instance : Repr Response := ⟨fun r _ => s!"<Response [{r.statusCode} {r.reasonPhrase}]>"⟩

end Response

end LeanHttpx
