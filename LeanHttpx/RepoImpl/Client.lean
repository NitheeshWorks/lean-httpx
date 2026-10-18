import LeanHttpx.RepoImpl.Redirects
import LeanHttpx.RepoImpl.Auth
import LeanHttpx.RepoImpl.Decoders
import LeanHttpx.Transport

/-!
# The client (`httpx.Client`)

`Client.new (...)` is `httpx.Client(...)` with upstream's parameter names and
defaults. Its logic is pure functions over its `Transport`:

* `buildRequest` merges the client's `base_url`, `params`, `headers` and
  `cookies` into the request (`build_request`, `_merge_*`);
* `send` runs the authentication flow around the redirect loop
  (`sendHandlingRedirects`), each response passing through the event hooks,
  the cookie jar and `read` (content decoding).

The only state is the cookie jar, kept in an `IO.Ref` as httpx keeps it on
the client object, and whether the client is closed.
-/

namespace LeanHttpx

/-- httpx's version and default `User-Agent` for this port. -/
def userAgent : String := "lean-httpx/0.1.0"

/-- The headers every client sends unless told otherwise. -/
def defaultHeaders : Headers :=
  ⟨[("Accept", "*/*"), ("Accept-Encoding", "gzip, deflate"), ("Connection", "keep-alive"),
    ("User-Agent", userAgent)]⟩

/-- Event hooks (`event_hooks={"request": [...], "response": [...]}`). -/
structure EventHooks where
  request : List (Request → IO Unit) := []
  response : List (Response → IO Unit) := []

/-- The most requests one authentication flow sends. Upstream's flows are
generators with no bound; this port bounds them (Basic and Digest send at
most two). -/
def maxAuthRequests : Nat := 32

/-- An HTTP client (`httpx.Client`). -/
structure Client where
  transport : Transport
  auth : Option Auth := none
  params : QueryParams := {}
  headers : Headers := defaultHeaders
  cookieJar : IO.Ref Cookies
  timeout : Timeout := {}
  followRedirects : Bool := false
  maxRedirects : Nat := 20
  baseUrl : URL
  eventHooks : EventHooks := {}
  defaultEncoding : String := "utf-8"
  closed : IO.Ref Bool

/-- `base_url` with a trailing slash (`_enforce_trailing_slash`). -/
def enforceTrailingSlash (u : URL) : URL :=
  if u.rawPath.endsWith "/" then u else
  match u.copyWith (path := u.ref.path ++ "/") with
  | .ok v => v
  | .error _ => u

/-- The current Unix time in seconds and the current year. -/
def clock : IO (Int × Int) := do
  let ms ← IO.monoMsNow
  let _ := ms
  let t ← Std.Time.Timestamp.now
  let secs : Int := t.toSecondsSinceUnixEpoch.val
  -- Days since the epoch to a year, by 400-year cycles.
  let days := secs / 86400
  let year := 1970 + (days * 400) / 146097
  pure (secs, year)

namespace Client

/-- **`httpx.Client(...)`**. -/
def new (auth : Option Auth := none) (params : QueryParams := {}) (headers : Headers := {})
    (cookies : Cookies := {}) (timeout : Timeout := {}) (followRedirects : Bool := false)
    (maxRedirects : Nat := 20) (baseUrl : String := "") (transport : Transport := HTTPTransport)
    (eventHooks : EventHooks := {}) (defaultEncoding : String := "utf-8") : IO Client := do
  let base ← match URL.parse baseUrl with
    | .ok u => pure u
    | .error e => throw (IO.userError (toString (HTTPError.invalidURL e.message)))
  pure {
    transport, auth, params, headers := defaultHeaders.update headers,
    cookieJar := ← IO.mkRef cookies, timeout, followRedirects, maxRedirects,
    baseUrl := enforceTrailingSlash base, eventHooks, defaultEncoding,
    closed := ← IO.mkRef false }

variable (c : Client)

/-- The client's cookies (`client.cookies`). -/
def cookies : IO Cookies := c.cookieJar.get

/-- Replace the client's cookies (`client.cookies = ...`). -/
def setCookies (j : Cookies) : IO Unit := c.cookieJar.set j

/-- **Merge a URL with `base_url`** (`_merge_url`): a relative URL is
appended to the base's path. -/
def mergeUrl (url : URL) : Except HTTPError URL :=
  if url.isRelativeUrl then
    let path := c.baseUrl.ref.path ++ String.ofList (url.ref.path.toList.dropWhile (· == '/'))
    (c.baseUrl.copyWith (path := path) (query := url.ref.query)).mapError fun e => .invalidURL e.message
  else .ok url

/-- **`build_request`**: the request with the client's configuration merged
in. Client headers are overridden by request headers name by name
(`headers_merge_precedence`); client params by request params. -/
def buildRequest (method : String) (url : String) (params : QueryParams := {}) (headers : Headers := {})
    (cookies : Cookies := {}) (content : Option Content := none) (data : List (String × String) := [])
    (json : Option LeanJson.Json := none) (timeout : Option Timeout := none) (jar : Cookies := {}) :
    Except HTTPError Request := do
  let u ← (URL.parse url).mapError fun e => .invalidURL e.message
  let u ← c.mergeUrl u
  let merged := c.headers.update headers
  let cookies := jar.update cookies
  let params : Option QueryParams :=
    if params.isEmpty && c.params.isEmpty then none else some (c.params.merge params)
  (Request.new method u (params := params) (headers := merged) (cookies := cookies) (content := content)
    (data := data) (json := json) (timeout := timeout.getD c.timeout)).mapError fun e => .invalidURL e.message

/-- Read a transport response: decode its raw body (`response.read()`). -/
def read (r : Response) : Except HTTPError Response :=
  match r.stream with
  | none => .ok r
  | some raw =>
    let codings := (r.headers.getList "content-encoding" (splitCommas := true)).map fun s => asciiLower s
    match Decoders.decodeContent codings raw with
    | .ok b => .ok { r with content := b, stream := none }
    | .error e => .error (.decodingError s!"Error -3 while decompressing data: {e}")

/-- Send one request, without redirects (`_send_single_request`): request
hooks, the transport, response hooks, the cookie jar, and reading. -/
def sendSingle (request : Request) : IO (Except HTTPError Response) := do
  for hook in c.eventHooks.request do hook request
  let response ← try c.transport.handleRequest request
    catch e => return .error (.connectError (toString e))
  let response := { response with request? := some request, defaultEncoding := c.defaultEncoding }
  for hook in c.eventHooks.response do hook response
  let (now, year) ← clock
  c.cookieJar.modify fun j => j.extract (response.headers.getList "set-cookie") request.url now year
  pure (read response)

/-- The redirect loop over this client's transport. -/
def sendHandlingRedirects (request : Request) (follow : Bool) (history : List Response) :
    IO (Except HTTPError (Bounded c.maxRedirects)) :=
  LeanHttpx.sendHandlingRedirects c.sendSingle (do pure (← c.cookieJar.get, (← clock).1))
    follow c.maxRedirects request history

/-- The authentication flow around the redirect loop (`_send_handling_auth`). -/
def sendHandlingAuth (request : Request) (auth : Auth) (follow : Bool) : IO (Except HTTPError Response) := do
  let mut request ← auth.start request
  let mut history : List Response := []
  for _ in [0:maxAuthRequests] do
    match ← c.sendHandlingRedirects request follow history with
    | .error e => return .error e
    | .ok ⟨response, _⟩ =>
      match ← auth.next request response with
      | none => return .ok response
      | some next =>
        history := history ++ [{ response with history }]
        request := next
  return .error (.streamError "Authentication flow did not finish")

/-- **`client.send(request, auth=..., follow_redirects=...)`**. With no
auth given, the client's is used; with none there either, credentials in the
URL become Basic auth. -/
def send (request : Request) (auth : Option Auth := none) (followRedirects : Option Bool := none) :
    IO Response := do
  if ← c.closed.get then throw (IO.userError "RuntimeError: Cannot send a request, as the client has been closed.")
  let auth := match auth.orElse fun _ => c.auth with
    | some a => a
    | none =>
      let u := request.url.username
      let p := request.url.password
      if !u.isEmpty || !p.isEmpty then BasicAuth u p else Auth.none
  let r ← c.sendHandlingAuth request auth (followRedirects.getD c.followRedirects)
  liftM (m := Except HTTPError) r

/-- **`client.request(method, url, ...)`**: build and send. -/
def request (method : String) (url : String) (content : Option Content := none)
    (data : List (String × String) := []) (json : Option LeanJson.Json := none)
    (params : QueryParams := {}) (headers : Headers := {}) (cookies : Cookies := {})
    (auth : Option Auth := none) (followRedirects : Option Bool := none)
    (timeout : Option Timeout := none) : IO Response := do
  let jar ← c.cookieJar.get
  let req ← liftM (m := Except HTTPError)
    (c.buildRequest method url params headers cookies content data json timeout jar)
  c.send req auth followRedirects

/-- `client.get(url, ...)`. -/
def get (url : String) (params : QueryParams := {}) (headers : Headers := {}) (cookies : Cookies := {})
    (auth : Option Auth := none) (followRedirects : Option Bool := none) (timeout : Option Timeout := none) :
    IO Response :=
  c.request "GET" url (params := params) (headers := headers) (cookies := cookies) (auth := auth)
    (followRedirects := followRedirects) (timeout := timeout)

/-- `client.options(url, ...)`. -/
def options (url : String) (params : QueryParams := {}) (headers : Headers := {}) (cookies : Cookies := {})
    (auth : Option Auth := none) (followRedirects : Option Bool := none) (timeout : Option Timeout := none) :
    IO Response :=
  c.request "OPTIONS" url (params := params) (headers := headers) (cookies := cookies) (auth := auth)
    (followRedirects := followRedirects) (timeout := timeout)

/-- `client.head(url, ...)`. -/
def head (url : String) (params : QueryParams := {}) (headers : Headers := {}) (cookies : Cookies := {})
    (auth : Option Auth := none) (followRedirects : Option Bool := none) (timeout : Option Timeout := none) :
    IO Response :=
  c.request "HEAD" url (params := params) (headers := headers) (cookies := cookies) (auth := auth)
    (followRedirects := followRedirects) (timeout := timeout)

/-- `client.post(url, content=, data=, json=, ...)`. -/
def post (url : String) (content : Option Content := none) (data : List (String × String) := [])
    (json : Option LeanJson.Json := none) (params : QueryParams := {}) (headers : Headers := {})
    (cookies : Cookies := {}) (auth : Option Auth := none) (followRedirects : Option Bool := none)
    (timeout : Option Timeout := none) : IO Response :=
  c.request "POST" url content data json params headers cookies auth followRedirects timeout

/-- `client.put(url, ...)`. -/
def put (url : String) (content : Option Content := none) (data : List (String × String) := [])
    (json : Option LeanJson.Json := none) (params : QueryParams := {}) (headers : Headers := {})
    (cookies : Cookies := {}) (auth : Option Auth := none) (followRedirects : Option Bool := none)
    (timeout : Option Timeout := none) : IO Response :=
  c.request "PUT" url content data json params headers cookies auth followRedirects timeout

/-- `client.patch(url, ...)`. -/
def patch (url : String) (content : Option Content := none) (data : List (String × String) := [])
    (json : Option LeanJson.Json := none) (params : QueryParams := {}) (headers : Headers := {})
    (cookies : Cookies := {}) (auth : Option Auth := none) (followRedirects : Option Bool := none)
    (timeout : Option Timeout := none) : IO Response :=
  c.request "PATCH" url content data json params headers cookies auth followRedirects timeout

/-- `client.delete(url, ...)`. -/
def delete (url : String) (params : QueryParams := {}) (headers : Headers := {}) (cookies : Cookies := {})
    (auth : Option Auth := none) (followRedirects : Option Bool := none) (timeout : Option Timeout := none) :
    IO Response :=
  c.request "DELETE" url (params := params) (headers := headers) (cookies := cookies) (auth := auth)
    (followRedirects := followRedirects) (timeout := timeout)

/-- `client.close()`. -/
def close : IO Unit := do
  c.closed.set true
  c.transport.close

/-- `client.is_closed`. -/
def isClosed : IO Bool := c.closed.get

end Client

/-- `httpx.AsyncClient`: the same client. Lean's `IO` is the effect for both;
run a request concurrently with `IO.asTask`. -/
abbrev AsyncClient := Client

/-! ## Top-level functions (`httpx.get`, `httpx.post`, ...) -/

/-- `httpx.request(method, url, ...)`: a request with a fresh client. -/
def request (method : String) (url : String) (content : Option Content := none)
    (data : List (String × String) := []) (json : Option LeanJson.Json := none)
    (params : QueryParams := {}) (headers : Headers := {}) (cookies : Cookies := {})
    (auth : Option Auth := none) (followRedirects : Bool := false) (timeout : Timeout := {})
    (transport : Transport := HTTPTransport) : IO Response := do
  let c ← Client.new (cookies := cookies) (timeout := timeout) (transport := transport)
  c.request method url content data json params headers {} auth (some followRedirects)

/-- `httpx.get(url, ...)`. -/
def get (url : String) (params : QueryParams := {}) (headers : Headers := {}) (cookies : Cookies := {})
    (auth : Option Auth := none) (followRedirects : Bool := false) (timeout : Timeout := {})
    (transport : Transport := HTTPTransport) : IO Response :=
  request "GET" url (params := params) (headers := headers) (cookies := cookies) (auth := auth)
    (followRedirects := followRedirects) (timeout := timeout) (transport := transport)

/-- `httpx.post(url, ...)`. -/
def post (url : String) (content : Option Content := none) (data : List (String × String) := [])
    (json : Option LeanJson.Json := none) (params : QueryParams := {}) (headers : Headers := {})
    (cookies : Cookies := {}) (auth : Option Auth := none) (followRedirects : Bool := false)
    (timeout : Timeout := {}) (transport : Transport := HTTPTransport) : IO Response :=
  request "POST" url content data json params headers cookies auth followRedirects timeout transport

end LeanHttpx
