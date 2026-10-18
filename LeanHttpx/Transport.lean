import LeanHttpx.RepoImpl.Transports
import LeanHttpx.RepoImpl.H1Body
import Std.Async.TCP
import Std.Async.DNS
import Std.Async.Timer

/-!
# `HTTPTransport`: HTTP/1.1 over TCP (the effect module)

The only module that does network I/O. It sends one request per connection:
the request is printed by the verified codec (`H1.printRequest`) with
`Connection: close`, the response is read to the end of the connection and
parsed by the verified codec (`H1.parseResponse`). Connection pooling,
HTTP/2, proxies and TLS are not implemented; an `https` URL is
`UnsupportedProtocol` (see CONTRIBUTING).

Every loop is bounded: at most `maxReads` reads, each under the read
timeout, so a transport call always ends.
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

/-- The most reads of one response (65536 bytes each, so 64 GiB). -/
def maxReads : Nat := 1048576

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

/-- **`httpx.HTTPTransport()`**: HTTP/1.1 over TCP, one connection per
request. -/
def HTTPTransport : Transport where
  handleRequest r := do
    let scheme := r.url.scheme
    if scheme == "https" then
      throw (IO.userError (toString (HTTPError.unsupportedProtocol "HTTPS is not supported: this transport has no TLS")))
    if scheme != "http" then
      throw (IO.userError (toString (HTTPError.unsupportedProtocol s!"Request URL has an unsupported protocol '{scheme}://'.")))
    let host := r.url.host
    let port := (portOrDefault' r.url).getD 80
    let wire ← IO.ofExcept ((toH1Request r).mapError toString)
    let addrs ← try (DNS.getAddrInfo host (toString port)).block
      catch e => throw (IO.userError (toString (HTTPError.connectError s!"[Errno -2] Name or service not known: {e}")))
    let some ip := addrs[0]? | throw (IO.userError (toString (HTTPError.connectError "No address for host")))
    let addr : SocketAddress := match ip with
      | .v4 a => .v4 ⟨a, port.toUInt16⟩
      | .v6 a => .v6 ⟨a, port.toUInt16⟩
    let sock ← TCP.Socket.Client.mk
    withTimeout r.timeout.connect (.connectTimeout "timed out") (sock.connect addr)
    withTimeout r.timeout.write (.writeTimeout "timed out") (sock.send (H1.printRequest wire))
    let mut buf := ByteArray.empty
    for _ in [0:maxReads] do
      match ← withTimeout r.timeout.read (.readTimeout "timed out") (sock.recv? 65536) with
      | none => break
      | some b => if b.isEmpty then break else buf := buf ++ b
    match H1.parseResponse (wireBytes r.method) buf with
    | some (resp, _) => pure (ofH1Response resp)
    | none =>
      if buf.isEmpty then throw (IO.userError (toString (HTTPError.remoteProtocolError "Server disconnected without sending a response.")))
      else throw (IO.userError (toString (HTTPError.remoteProtocolError "Malformed HTTP response")))
where
  portOrDefault' (u : URL) : Option Nat := match u.port with
    | some p => some p
    | none => some 80

end LeanHttpx
