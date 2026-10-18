import LeanHttpx.RepoImpl.Models

/-!
# The transport interface, `MockTransport` and `ASGITransport`

A `Transport` is httpx's `BaseTransport`: one function from a request to a
response, plus `close`. The client is pure logic over it. Three kinds exist:

* `MockTransport handler` (`httpx.MockTransport`): the handler is the server.
* `ASGITransport app` (`httpx.ASGITransport`): an in-process application
  speaking the ASGI message protocol (`scope`, `receive`, `send`). This is
  the interface an in-process test client builds on: lean-starlette's
  `TestClient` is a `Client` over a transport like this one.
* `HTTPTransport` (`Transport.lean`, the one module that does network I/O).

A transport returns the response body raw in `Response.stream`; the client
reads it, decoding its `Content-Encoding`. A handler that builds its
response with `Response.new` has already read it.
-/

namespace LeanHttpx

/-- An HTTP transport (`httpx.BaseTransport`). -/
structure Transport where
  /-- Send one request and return its response (`handle_request`). -/
  handleRequest : Request → IO Response
  /-- Release resources (`close`). -/
  close : IO Unit := pure ()

/-- **`httpx.MockTransport(handler)`**: every request goes to `handler`. -/
def MockTransport (handler : Request → Response) : Transport where
  handleRequest r := pure (handler r)

/-- `httpx.MockTransport` with a handler that runs in `IO` (an `async`
handler upstream). -/
def MockTransport.io (handler : Request → IO Response) : Transport where
  handleRequest := handler

/-! ## ASGI -/

/-- The messages of the ASGI HTTP protocol. -/
inductive ASGIMessage where
  /-- `{"type": "http.request", "body": ..., "more_body": ...}` -/
  | httpRequest (body : ByteArray) (moreBody : Bool := false)
  /-- `{"type": "http.disconnect"}` -/
  | httpDisconnect
  /-- `{"type": "http.response.start", "status": ..., "headers": [...]}` -/
  | httpResponseStart (status : Nat) (headers : List (ByteArray × ByteArray) := [])
  /-- `{"type": "http.response.body", "body": ..., "more_body": ...}` -/
  | httpResponseBody (body : ByteArray := .empty) (moreBody : Bool := false)

/-- The ASGI connection scope of an HTTP request (`scope` in
`ASGITransport.handle_async_request`). -/
structure ASGIScope where
  type : String := "http"
  asgiVersion : String := "3.0"
  httpVersion : String := "1.1"
  method : String
  /-- Header names lower-cased, as raw bytes. -/
  headers : List (ByteArray × ByteArray)
  scheme : String
  /-- The decoded path. -/
  path : String
  /-- The encoded path, without the query. -/
  rawPath : ByteArray
  /-- The encoded query, without `?`. -/
  queryString : ByteArray
  server : String × Option Nat
  client : String × Nat
  rootPath : String

/-- An ASGI application: called with the scope, a `receive` and a `send`. -/
abbrev ASGIApp := ASGIScope → IO ASGIMessage → (ASGIMessage → IO Unit) → IO Unit

/-- `httpx.ASGITransport(app, raise_app_exceptions=True, root_path="",
client=("127.0.0.1", 123))`. -/
structure ASGITransport where
  app : ASGIApp
  raiseAppExceptions : Bool := true
  rootPath : String := ""
  client : String × Nat := ("127.0.0.1", 123)

/-- The scope httpx builds for a request. -/
def ASGITransport.scope (t : ASGITransport) (r : Request) : ASGIScope where
  method := r.method
  headers := r.headers.raw.map fun (k, v) => ((asciiLower k).toUTF8, v.toUTF8)
  scheme := r.url.scheme
  path := r.url.path
  rawPath := ((r.url.rawPath.splitOn "?").headD "").toUTF8
  queryString := r.url.query.toUTF8
  server := (r.url.host, r.url.port)
  client := t.client
  rootPath := t.rootPath

/-- Run the application on a request (`handle_async_request`): `receive`
gives the whole body once, then `http.disconnect`; `send` collects the
status, headers and body parts (no body for `HEAD`). An exception from the
application is re-raised, or with `raiseAppExceptions := false` becomes a
500 response. -/
def ASGITransport.handle (t : ASGITransport) (r : Request) : IO Response := do
  let requestDone ← IO.mkRef false
  let status ← IO.mkRef (none : Option Nat)
  let headers ← IO.mkRef (none : Option (List (ByteArray × ByteArray)))
  let body ← IO.mkRef (ByteArray.empty)
  let complete ← IO.mkRef false
  let receive : IO ASGIMessage := do
    if ← requestDone.get then return .httpDisconnect
    requestDone.set true
    return .httpRequest r.content false
  let send (m : ASGIMessage) : IO Unit := do
    match m with
    | .httpResponseStart s hs =>
      if (← status.get).isSome then throw (IO.userError "AssertionError: response already started")
      status.set (some s); headers.set (some hs)
    | .httpResponseBody b more =>
      if ← complete.get then throw (IO.userError "AssertionError: response already complete")
      if !b.isEmpty && r.method != "HEAD" then body.modify (· ++ b)
      if !more then complete.set true
    | _ => pure ()
  try
    t.app (t.scope r) receive send
  catch e =>
    if t.raiseAppExceptions then throw e
    complete.set true
    if (← status.get).isNone then status.set (some 500)
    if (← headers.get).isNone then headers.set (some [])
  let some s ← status.get | throw (IO.userError "AssertionError: the application sent no response")
  let hs := ((← headers.get).getD []).map fun (k, v) => (Text.decodeHeader k, Text.decodeHeader v)
  return { statusCode := s, headers := ⟨hs⟩, stream := some (← body.get) }

/-- The transport of an `ASGITransport`. -/
def ASGITransport.toTransport (t : ASGITransport) : Transport where
  handleRequest := t.handle

instance : Coe ASGITransport Transport := ⟨ASGITransport.toTransport⟩

end LeanHttpx
