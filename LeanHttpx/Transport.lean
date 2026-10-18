import LeanHttpx.RepoImpl.Transports
import LeanHttpx.RepoImpl.H1Body
import LeanHttpx.RepoImpl.H1Stream
import Std.Async.TCP
import Std.Async.DNS
import Std.Async.Timer
import Std.Async.Select

/-!
# `HTTPTransport`: HTTP/1.1 over TCP (the effect module)

The only module that does network I/O. It sends one request per connection:
the request is printed by the verified codec (`H1.printRequest`) with
`Connection: close`. The response is read as httpcore reads it: the head
first, at most 100 KiB of it (h11's `max_incomplete_event_size` as httpcore
sets it, "Receive buffer too long"), then exactly the body its framing
gives: `Content-Length` bytes, chunks up to the last one (`H1.scanChunks`),
or to the end of the connection when the head gives neither. The bytes are
then decoded by `H1.readResponse`, which is the verified response codec
(`H1.readResponse_eq_parseResponse`). Connection pooling, HTTP/2, proxies
and TLS are not implemented; an `https` URL is `UnsupportedProtocol` (see
CONTRIBUTING).

Every read is under the read timeout. Errors keep httpx's classes:
`ConnectError`/`ConnectTimeout`, `WriteError`/`WriteTimeout`,
`ReadError`/`ReadTimeout`, `RemoteProtocolError`.
-/

namespace LeanHttpx

open Std.Net Std.Async

/-- Header text as wire bytes (UTF-8). -/
def wireBytes (s : String) : List UInt8 := s.toUTF8.data.toList

/-- The wire request for a client request: its method, target and headers,
with `Connection: close`, as the verified codec takes it. -/
def toH1Request (r : Request) : Except HTTPError H1.Request :=
  let headers := r.headers.set "Connection" "close"
  let headers := if !r.content.isEmpty && !headers.contains "Content-Length" &&
      !headers.contains "Transfer-Encoding" then headers.set "Content-Length" (toString r.content.size)
    else headers
  let req : H1.Request := {
    head := { method := wireBytes r.method, target := wireBytes r.url.rawPath,
              fields := headers.raw.map fun (k, v) => ⟨wireBytes k, wireBytes v⟩ },
    body := r.content }
  if req.ok then .ok req else .error (.localProtocolError "Illegal header name or value, or body framing")

/-- The client response for a wire response. -/
def ofH1Response (r : H1.Response) : Response where
  statusCode := r.head.status
  headers := ⟨r.head.fields.map fun f => (Text.decodeHeader ⟨f.name.toArray⟩, Text.decodeHeader ⟨f.value.toArray⟩)⟩
  stream := some r.body
  httpVersion := r.head.version.toString
  reasonPhrase? := some (Text.decodeHeader ⟨r.head.reason.toArray⟩)

/-- Run `x` with a timeout in seconds (`none`: no timeout). -/
def withTimeout {α : Type} [Inhabited α] (t : Option Float) (onTimeout : HTTPError) (x : Async α) : IO α := do
  match t with
  | none => x.block
  | some secs =>
    let ms : Nat := (secs * 1000).toUInt64.toNat
    let r ← (Async.race (x.map Except.ok) (do sleep (Std.Time.Millisecond.Offset.ofNat ms); pure (.error onTimeout))).block
    match r with
    | .ok a => pure a
    | .error e => throw (IO.userError (toString e))

/-- Raise an httpx error in `IO`. -/
def raise {α : Type} (e : HTTPError) : IO α := throw (IO.userError (toString e))

/-- Run a socket operation; an operating-system error becomes `kind`. -/
def socketOp {α : Type} [Inhabited α] (t : Option Float) (onTimeout : HTTPError) (kind : String → HTTPError)
    (x : Async α) : IO α := do
  try withTimeout t onTimeout x
  catch e =>
    let m := toString e
    if m.startsWith (onTimeout.name ++ ": ") then throw e else raise (kind m)

/-- The bytes asked for per read. -/
def readSize : UInt64 := 262144

/-- No bound on the reads of a body that runs to the end of the connection
or is chunked, as upstream: the read ends at the end of the body, at the end
of the connection, or at a read timeout. The loop needs a number; this one
is not reached. -/
def unbounded : Nat := 2 ^ 64

/-- One read; `none` at the end of the connection. The read and its
timer are selected between (`Selectable.one`), so no buffer outlives its
read waiting on a timer. -/
def recvSome (sock : TCP.Socket.Client) (t : Option Float) : IO (Option ByteArray) := do
  let r ← try
      match t with
      | none => (sock.recv? readSize).block
      | some secs =>
        let ms : Nat := (secs * 1000).toUInt64.toNat
        let r ← (do
          let timer ← Selector.sleep (Std.Time.Millisecond.Offset.ofNat ms)
          Selectable.one #[.case (sock.recvSelector readSize) (fun b => pure (some b)),
            .case timer (fun _ => pure none)]).block
        match r with
        | some b => pure b
        | none => raise (.readTimeout "timed out")
    catch e =>
      let m := toString e
      if m.startsWith "ReadTimeout: " then throw e else raise (.readError m)
  pure (match r with | some b => if b.isEmpty then none else some b | none => none)

/-- Read until the buffer holds a whole head: the position after its blank
line. At most `maxIncompleteEventSize` bytes are buffered without one
(httpcore's limit, "Receive buffer too long"). -/
def readHead (sock : TCP.Socket.Client) (t : Option Float) (buf : ByteArray) : IO (ByteArray × Nat) := do
  let mut buf := buf
  let mut scanned := 0
  -- every read adds at least one byte, so this bound is never reached first
  for _ in [0:H1.maxIncompleteEventSize + 2] do
    if let some e := H1.headEnd? buf scanned then
      if e > H1.maxIncompleteEventSize then raise (.remoteProtocolError "Receive buffer too long")
      return (buf, e)
    if buf.size > H1.maxIncompleteEventSize then raise (.remoteProtocolError "Receive buffer too long")
    scanned := buf.size
    match ← recvSome sock t with
    | some b => buf := buf ++ b
    | none =>
      if buf.isEmpty then raise (.remoteProtocolError "Server disconnected without sending a response.")
      raise (.remoteProtocolError "peer unexpectedly closed connection")
  raise (.remoteProtocolError "Receive buffer too long")

/-- The most bytes reserved ahead for a `Content-Length` body (1 GiB). -/
def maxReserve : Nat := 1024 * 1024 * 1024

/-- Read until the buffer holds `need` bytes; if the connection ends first,
the bytes it holds. Each read adds at least one byte, so there are at most
`need` reads. -/
def readUntil (sock : TCP.Socket.Client) (t : Option Float) (buf : ByteArray) (need : Nat) :
    IO (Except ByteArray ByteArray) := do
  -- room for the whole message up front (reserved, not touched), so the
  -- buffer is never copied to grow; a larger length grows as it arrives
  let mut buf := if need ≤ maxReserve && buf.size < need then
    (ByteArray.emptyWithCapacity need).append buf else buf
  for _ in [0:need + 1] do
    if buf.size ≥ need then return .ok buf
    match ← recvSome sock t with
    | some b => buf := buf ++ b
    | none => return .error buf
  return .ok buf

/-- Read a chunked body that starts at `start` to its last chunk. -/
def readChunked (sock : TCP.Socket.Client) (t : Option Float) (buf : ByteArray) (start : Nat) :
    IO ByteArray := do
  let mut buf := buf
  let mut pos := start
  for _ in [0:unbounded] do
    match H1.scanChunks buf pos with
    | .done _ => return buf
    | .bad m => raise (.remoteProtocolError m)
    | .more p =>
      pos := p
      match ← recvSome sock t with
      | some b => buf := buf ++ b
      | none => raise (.remoteProtocolError
          "peer closed connection without sending complete message body (incomplete chunked read)")
  return buf

/-- Read to the end of the connection. -/
def readToEnd (sock : TCP.Socket.Client) (t : Option Float) (buf : ByteArray) : IO ByteArray := do
  let mut buf := buf
  for _ in [0:unbounded] do
    match ← recvSome sock t with
    | some b => buf := buf ++ b
    | none => return buf
  return buf

/-- Read one response to a request with method `m`: the head (bounded), then
exactly the body its framing gives, then decode the bytes with the verified
reader `H1.readResponse` (`= H1.parseResponse`). Informational (1xx)
responses before it are skipped, as httpcore does. -/
def readResponse (sock : TCP.Socket.Client) (t : Option Float) (m : List UInt8) : IO H1.Response := do
  let mut buf := ByteArray.empty
  for _ in [0:H1.maxIncompleteEventSize] do
    let (b, e) ← readHead sock t buf
    let some (head, _) := H1.responseHead.decodeBytes (b.extract 0 e)
      | raise (.remoteProtocolError "illegal status line or header")
    if head.status / 100 == 1 && head.status != 101 then
      buf := b.extract e b.size
      continue
    let b ← match H1.responseFraming m head with
      | .none => pure b
      | .length n =>
        match ← readUntil sock t b (e + n) with
        | .ok b => pure b
        | .error b => raise (.remoteProtocolError
            s!"peer closed connection without sending complete message body (received {b.size - e} bytes, expected {n})")
      | .chunked => readChunked sock t b e
      | .close => readToEnd sock t b
      | .invalid => raise (.remoteProtocolError
          (if (H1.valuesOf head.fields (H1.ascii "transfer-encoding")).isEmpty then "bad Content-Length"
           else "Only Transfer-Encoding: chunked is supported"))
    -- a chunked body is copied chunk by chunk (`H1.readChunked`); any other
    -- is decoded by `H1.readResponse`, the response codec itself
    if H1.responseFraming m head == .chunked then
      let some ⟨_, j⟩ := (H1.responseHead.parser (ε := Unit)).run b 0 |> fun
          | .ok h j => some (h, j) | .error _ _ => none
        | raise (.remoteProtocolError "illegal status line or header")
      match H1.readChunked b j with
      | some (body, _) => return ⟨head, body⟩
      | none => raise (.remoteProtocolError "illegal chunk header")
    match H1.readResponse m b with
    | some (resp, _) => return resp
    | none => raise (.remoteProtocolError "Malformed HTTP response")
  raise (.remoteProtocolError "too many informational responses")

/-- **`httpx.HTTPTransport()`**: HTTP/1.1 over TCP, one connection per
request. -/
def HTTPTransport : Transport where
  handleRequest r := do
    let scheme := r.url.scheme
    if scheme == "https" then
      raise (.unsupportedProtocol "HTTPS is not supported: this transport has no TLS")
    if scheme != "http" then
      raise (.unsupportedProtocol s!"Request URL has an unsupported protocol '{scheme}://'.")
    let host := r.url.host
    let port := r.url.port.getD 80
    let wire ← match toH1Request r with
      | .ok w => pure w
      | .error e => raise e
    let addrs ← try (DNS.getAddrInfo host (toString port)).block
      catch e => raise (.connectError s!"[Errno -2] Name or service not known: {e}")
    let some ip := addrs[0]? | raise (.connectError "No address for host")
    let addr : SocketAddress := match ip with
      | .v4 a => .v4 ⟨a, port.toUInt16⟩
      | .v6 a => .v6 ⟨a, port.toUInt16⟩
    let sock ← TCP.Socket.Client.mk
    socketOp r.timeout.connect (.connectTimeout "timed out") .connectError (sock.connect addr)
    socketOp r.timeout.write (.writeTimeout "timed out") .writeError (sock.send (H1.printRequest wire))
    let resp ← readResponse sock r.timeout.read (wireBytes r.method)
    pure (ofH1Response resp)

end LeanHttpx
