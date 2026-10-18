import LeanHttpx.Transport
import LeanHttpx.RepoImpl.H2Conn
import Std.Sync.Mutex

/-!
# `HTTP2Transport`: HTTP/2 over TCP with prior knowledge (the effect module)

httpcore's HTTP/2 connection, over cleartext TCP (`h2c` with prior
knowledge, what `httpx.Client(http1=False, http2=True)` does for an `http`
URL; there is no TLS here, so no ALPN). One connection per origin is kept
and shared: requests from several tasks are multiplexed on it, each on its
own stream.

The protocol is the sans-I/O `H2.Conn`; this module only moves bytes. Two
locks: the connection state, held briefly to start a request, feed bytes or
take output; and the socket's read side. A request waiting for its response
takes the read lock, reads once (under its read timeout), feeds the state,
and lets go, so whichever request is waiting reads for all of them, and no
task runs in the background.
-/

namespace LeanHttpx

open Std.Net Std.Async H2 Hpack

/-- A shared HTTP/2 connection. -/
structure H2Link where
  sock : TCP.Socket.Client
  state : Std.Mutex Conn
  reader : Std.Mutex Unit

/-- The fields of a request on HTTP/2 (httpcore's `_send_request_headers`):
the pseudo-headers, then every field lower-cased but `Host` and
`Transfer-Encoding`. -/
def h2Fields (r : Request) : List HeaderField :=
  let authority := (r.headers.get? "Host").getD r.url.netloc
  let pseudo : List HeaderField := [
    ⟨":method".toUTF8, r.method.toUTF8, false⟩, ⟨":authority".toUTF8, authority.toUTF8, false⟩,
    ⟨":scheme".toUTF8, r.url.scheme.toUTF8, false⟩, ⟨":path".toUTF8, r.url.rawPath.toUTF8, false⟩]
  let rest := r.headers.raw.filterMap fun (k, v) =>
    let k := asciiLower k
    if k == "host" || k == "transfer-encoding" then none
    else some ⟨k.toUTF8, v.toUTF8, k == "authorization" || k == "proxy-authorization"⟩
  pseudo ++ rest

/-- Write what the connection has to send. -/
def H2Link.flush (l : H2Link) (t : Option Float) : IO Unit := do
  let out ← l.state.atomically do
    let c ← get
    let (out, c) := c.takeOutput
    set c
    pure out
  if out.size > 0 then
    socketOp t (.writeTimeout "timed out") .writeError (l.sock.send out)

/-- Open a connection to an address and send the preface. -/
def H2Link.connect (addr : SocketAddress) (timeout : Timeout) : IO H2Link := do
  let sock ← TCP.Socket.Client.mk
  socketOp timeout.connect (.connectTimeout "timed out") .connectError (sock.connect addr)
  let l : H2Link := { sock, state := ← Std.Mutex.new (Conn.new), reader := ← Std.Mutex.new () }
  l.flush timeout.write
  pure l

/-- Wait for a stream's outcome, reading for everyone while waiting. -/
def H2Link.await (l : H2Link) (sid : Nat) (t : Option Float) :
    IO (Except String (Nat × List HeaderField × ByteArray)) := do
  for _ in [0:unbounded] do
    if let some o ← l.state.atomically (do pure ((← get).outcome sid)) then
      l.state.atomically (modify (·.release sid))
      return o
    l.reader.atomically do
      -- someone else may have read our response while we waited for the lock
      if (← l.state.atomically (do pure ((← get).outcome sid))).isSome then return
      let data ← recvSome l.sock t
      l.state.atomically do
        match data with
        | some b => modify (·.receive b)
        | none => modify fun c => if c.error.isSome then c else
            { c with error := some ⟨.noError, "Server disconnected without sending a response."⟩ }
      l.flush t
  return .error "unreachable"

/-- Start a request, waiting while the connection has no stream free. -/
def H2Link.start (l : H2Link) (fields : List HeaderField) (body : ByteArray) (t : Timeout) : IO Nat := do
  for _ in [0:unbounded] do
    let r ← l.state.atomically do
      match (← get).startRequest fields body with
      | .ok (c, sid) => set c; pure (Except.ok (some sid))
      | .error e =>
        if e.code == .refusedStream && e.message == "Too many concurrent streams" then pure (.ok none)
        else pure (.error e)
    match r with
    | .ok (some sid) => l.flush t.write; return sid
    | .error e => raise (.remoteProtocolError s!"{e.code.name}: {e.message}")
    | .ok none =>
      -- read once, so that finished streams free a slot
      l.reader.atomically do
        let data ← recvSome l.sock t.read
        l.state.atomically (modify fun c => match data with
          | some b => c.receive b
          | none => { c with error := some ⟨.noError, "Server disconnected"⟩ })
      l.flush t.write
  raise (.poolTimeout "no stream became free")

/-- The pool: one connection per origin, behind a lock, so that requests
started together share one connection. -/
structure H2Pool where
  links : Std.Mutex (List (String × H2Link))

/-- A connection to the request's origin: the open one, or a new one. -/
def H2Pool.link (p : H2Pool) (r : Request) : IO H2Link := do
  let origin := s!"{r.url.scheme}://{r.url.netloc}"
  p.links.atomically do
    if let some (_, l) := (← get).find? (·.1 == origin) then
      let c ← l.state.atomically get
      if c.error.isNone && c.goaway.isNone then return l
      modify (·.filter (·.1 != origin))
    let host := r.url.host
    let port := r.url.port.getD 80
    let addrs ← try (DNS.getAddrInfo host (toString port)).block
      catch e => raise (.connectError s!"[Errno -2] Name or service not known: {e}")
    let some ip := addrs[0]? | raise (.connectError "No address for host")
    let addr : SocketAddress := match ip with
      | .v4 a => .v4 ⟨a, port.toUInt16⟩
      | .v6 a => .v6 ⟨a, port.toUInt16⟩
    let l ← H2Link.connect addr r.timeout
    modify ((origin, l) :: ·)
    return l

/-- **`HTTP2Transport`**: HTTP/2 with prior knowledge over TCP, one
multiplexed connection per origin. -/
def HTTP2Transport.new : IO Transport := do
  let p : H2Pool := { links := ← Std.Mutex.new [] }
  return {
    handleRequest := fun r => do
      if r.url.scheme == "https" then
        raise (.unsupportedProtocol "HTTPS is not supported: this transport has no TLS")
      if r.url.scheme != "http" then
        raise (.unsupportedProtocol s!"Request URL has an unsupported protocol '{r.url.scheme}://'.")
      let l ← p.link r
      let sid ← l.start (h2Fields r) r.content r.timeout
      match ← l.await sid r.timeout.read with
      | .error m => raise (.remoteProtocolError m)
      | .ok (status, fields, body) =>
        pure {
          statusCode := status,
          headers := ⟨fields.map fun f => (Text.decodeHeader f.name, Text.decodeHeader f.value)⟩,
          stream := some body, httpVersion := "HTTP/2" }
    close := p.links.atomically do
      let links : List (String × H2Link) ← get
      for (_, l) in links do
        try (l.sock.shutdown).block catch _ => pure ()
      set ([] : List (String × H2Link)) }

/-- `httpx.HTTPTransport(http1=..., http2=...)`: HTTP/2 with prior
knowledge when HTTP/1.1 is off, else HTTP/1.1 (without TLS there is no
ALPN to negotiate HTTP/2, as with httpx on an `http` URL). -/
def httpTransport (http1 : Bool := true) (http2 : Bool := false) : IO Transport :=
  if http2 && !http1 then HTTP2Transport.new else pure HTTPTransport

end LeanHttpx
