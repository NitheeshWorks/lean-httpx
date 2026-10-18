import LeanHttpx.RepoImpl.URL
import LeanHttpx.RepoImpl.Headers

/-!
# Requests, responses, cookies and errors (`httpx/_models.py`)

The data of httpx's model classes. Bodies are read in full (`content`):
httpx's streaming interface is not ported (see CONTRIBUTING). A response
keeps the request that produced it and the redirect or authentication
responses before it (`history`).
-/

namespace LeanHttpx

/-- Timeouts in seconds (`httpx.Timeout`); `none` disables one. The
default is httpx's five seconds for each. -/
structure Timeout where
  connect : Option Float := some 5.0
  read : Option Float := some 5.0
  write : Option Float := some 5.0
  pool : Option Float := some 5.0
  deriving Repr, Inhabited

namespace Timeout

/-- `httpx.Timeout(t)`: the same timeout for all four. -/
def all (t : Option Float) : Timeout := ⟨t, t, t, t⟩

/-- httpx's default, `Timeout(5.0)`. -/
def default : Timeout := {}

end Timeout

/-- An HTTP request (`httpx.Request`). The method is upper case. -/
structure Request where
  method : String
  url : URL
  headers : Headers := {}
  content : ByteArray := .empty
  /-- The timeout extension httpx attaches to each request. -/
  timeout : Timeout := {}

instance : Inhabited Request where
  default := { method := "GET", url := ⟨{}, by decide⟩ }

/-- An HTTP response (`httpx.Response`). -/
structure Response where
  statusCode : Nat
  headers : Headers := {}
  /-- The decoded body, once read. -/
  content : ByteArray := .empty
  /-- The raw body a transport returned, not yet read: reading decodes its
  `Content-Encoding` into `content` (`response.read()`). -/
  stream : Option ByteArray := none
  /-- The request that produced it, set by the client. -/
  request? : Option Request := none
  /-- The redirect and authentication responses before this one. -/
  history : List Response := []
  /-- With `follow_redirects=False`, the request a redirect would make. -/
  nextRequest : Option Request := none
  /-- The `http_version` extension, e.g. `HTTP/1.1`. -/
  httpVersion : String := "HTTP/1.1"
  /-- The `reason_phrase` extension, when the transport reported one. -/
  reasonPhrase? : Option String := none
  /-- The encoding for `text` when the content type names none. -/
  defaultEncoding : String := "utf-8"

instance : Inhabited Response := ⟨{ statusCode := 200 }⟩

/-- A cookie as `http.cookiejar` keeps it (Netscape cookies, which is every
cookie under httpx's default policy). `domain` starts with `.` when the
`Domain` attribute set it; `expires` is a Unix time. -/
structure Cookie where
  name : String
  value : Option String
  domain : String := ""
  domainSpecified : Bool := false
  domainInitialDot : Bool := false
  path : String := "/"
  pathSpecified : Bool := true
  secure : Bool := false
  expires : Option Int := none
  discard : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- A cookie jar (`http.cookiejar.CookieJar`, wrapped by `httpx.Cookies`):
cookies by domain, then path, then name, each level in insertion order. -/
structure Cookies where
  jar : List (String × List (String × List (String × Cookie))) := []
  deriving DecidableEq, Repr, Inhabited


/-- httpx's exceptions (`httpx/_exceptions.py`), with their messages. -/
inductive HTTPError where
  | invalidURL (message : String)
  | httpStatusError (message : String) (request : Request) (response : Response)
  | tooManyRedirects (message : String) (request : Request)
  | remoteProtocolError (message : String)
  | localProtocolError (message : String)
  | connectError (message : String)
  | readError (message : String)
  | writeError (message : String)
  | connectTimeout (message : String)
  | readTimeout (message : String)
  | writeTimeout (message : String)
  | poolTimeout (message : String)
  | unsupportedProtocol (message : String)
  | decodingError (message : String)
  | cookieConflict (message : String)
  | streamError (message : String)
  /-- An exception raised by an in-process application. -/
  | appError (message : String)

namespace HTTPError

/-- The exception class name. -/
def name : HTTPError → String
  | .invalidURL .. => "InvalidURL"
  | .httpStatusError .. => "HTTPStatusError"
  | .tooManyRedirects .. => "TooManyRedirects"
  | .remoteProtocolError .. => "RemoteProtocolError"
  | .localProtocolError .. => "LocalProtocolError"
  | .connectError .. => "ConnectError"
  | .readError .. => "ReadError"
  | .writeError .. => "WriteError"
  | .connectTimeout .. => "ConnectTimeout"
  | .readTimeout .. => "ReadTimeout"
  | .writeTimeout .. => "WriteTimeout"
  | .poolTimeout .. => "PoolTimeout"
  | .unsupportedProtocol .. => "UnsupportedProtocol"
  | .decodingError .. => "DecodingError"
  | .cookieConflict .. => "CookieConflict"
  | .streamError .. => "StreamError"
  | .appError .. => "Exception"

/-- `str(exc)`. -/
def message : HTTPError → String
  | .invalidURL m | .httpStatusError m _ _ | .tooManyRedirects m _ | .remoteProtocolError m
  | .localProtocolError m | .connectError m | .readError m | .writeError m | .connectTimeout m
  | .readTimeout m | .writeTimeout m | .poolTimeout m | .unsupportedProtocol m | .decodingError m | .cookieConflict m
  | .streamError m | .appError m => m

instance : ToString HTTPError := ⟨fun e => s!"{e.name}: {e.message}"⟩

/-- `HTTPError` is the base of the transport and status errors. -/
def isTransportError : HTTPError → Bool
  | .connectError .. | .readError .. | .writeError .. | .connectTimeout .. | .readTimeout ..
  | .writeTimeout .. | .poolTimeout ..
  | .unsupportedProtocol .. | .remoteProtocolError .. | .localProtocolError .. => true
  | _ => false

end HTTPError

/-- In `IO`, an httpx error is an `IO.userError` with the exception's name
and message, so `client.get url` reads as in Python. -/
instance : MonadLift (Except HTTPError) IO where
  monadLift
    | .ok a => pure a
    | .error e => throw (IO.userError (toString e))

end LeanHttpx
