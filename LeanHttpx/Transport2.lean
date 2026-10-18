import LeanHttpx.Transport
import LeanHttpx.RepoImpl.H2Conn
import LeanHttpx.RepoImpl.H2Request
import Std.Sync.Mutex

/-!
# `HTTP2Transport`: HTTP/2 over TCP with prior knowledge (the effect module)

httpcore's HTTP/2 connection, over cleartext TCP (`h2c` with prior
knowledge, what `httpx.Client(http1=False, http2=True)` does for an `http`
URL; there is no TLS here, so no ALPN). One connection per origin is kept
and shared: requests from several tasks are multiplexed on it, each on its
own stream.

The protocol is the sans-I/O `H2.Conn`; this module only moves bytes, and
no lock is ever held across a socket operation or a wait:

* one reader per connection, on its own thread, does every read and feeds
  the bytes to the connection state; it runs while the connection has a
  stream open, as httpcore reads only for a waiting request, so an idle
  connection holds no thread (and a program need not close its client to
  exit);
* the state's lock is held only to update it, never while waiting;
* a task waiting for its response, or for a free stream, leaves a promise
  and waits on it (a task the runtime knows is waiting, so it does not hold
  up the other tasks), with its timeout; the reader resolves the promises
  after every change;
* whoever has output to send writes it, and anyone else's that arrives
  meanwhile; tasks finding a write in progress leave theirs to it.

A read timeout is per stream: it fires when that stream has made no
progress for the timeout, whatever the other streams do, and the stream is
then reset (`RST_STREAM CANCEL`).
-/

namespace LeanHttpx

open Std.Net Std.Async H2 Hpack

/-- What the tasks using one connection share. -/
structure Shared where
  conn : Conn
  /-- Tasks waiting for a change. -/
  waiters : Array (IO.Promise Unit) := #[]
  /-- A task is writing; others leave their output to it. -/
  writing : Bool := false
  /-- The socket failed (`ReadError`, `WriteError`): every request fails with it. -/
  failure : Option String := none
  /-- The connection has ended or failed: no more reading. -/
  stopped : Bool := false
  /-- A reader is running. -/
  reading : Bool := false

/-- A shared HTTP/2 connection. -/
structure H2Link where
  sock : TCP.Socket.Client
  shared : Std.Mutex Shared

/-- Milliseconds of a timeout in seconds. -/
def toMs (secs : Float) : Nat := (secs * 1000).toUInt64.toNat

/-- Wake every waiting task. -/
def H2Link.wake (l : H2Link) : IO Unit := do
  let ws ← l.shared.atomically do
    let s ← get
    set { s with waiters := #[] }
    pure s.waiters
  for p in ws do p.resolve ()

/-- Wait for a promise for at most `ms` milliseconds (`none`: no bound). -/
def waitWake (p : IO.Promise Unit) (ms : Option Nat) : IO Unit := do
  match ms with
  | none => discard <| IO.wait p.result?
  | some ms =>
    discard <| (Async.race (do discard <| await p.result?; pure ())
      (sleep (Std.Time.Millisecond.Offset.ofNat ms))).block

/-- Write what the connection has to send: this task's output and any that
arrives while it writes. If another task is writing, it sends ours. -/
def H2Link.flush (l : H2Link) (t : Option Float) : IO Unit := do
  let mine ← l.shared.atomically do
    let s ← get
    if s.writing then pure false else set { s with writing := true }; pure true
  unless mine do return
  for _ in [0:unbounded] do
    let out ← l.shared.atomically do
      let s ← get
      let (out, c) := s.conn.takeOutput
      set { s with conn := c, writing := out.size > 0 }
      pure out
    if out.size == 0 then return
    try socketOp t (.writeTimeout "timed out") .writeError (l.sock.send out)
    catch e =>
      l.shared.atomically (modify fun s => { s with writing := false, failure := s.failure <|> some (toString e) })
      l.wake
      throw e

/-- How long the reader waits for bytes before it looks again whether the
connection still has a stream open. -/
def readerTick : Float := 0.25

/-- The reader: read, feed the state, send what it answers, wake the
waiting tasks; until the connection has no stream open, ends or fails. -/
def H2Link.readLoop (l : H2Link) : IO Unit := do
  for _ in [0:unbounded] do
    let idle ← l.shared.atomically do
      let s ← get
      let idle := s.stopped || (s.conn.active == 0 && s.conn.block.isNone)
      if idle then set { s with reading := false }
      pure idle
    if idle then return
    let data ← try pure (Except.ok (some (← recvSome l.sock (some readerTick))))
      catch e =>
        let m := toString e
        pure (if m.startsWith "ReadTimeout: " then .ok none else .error m)
    let stop ← l.shared.atomically do
      let s ← get
      let s := match data with
        | .ok none => s
        | .ok (some (some b)) => { s with conn := s.conn.receive b }
        | .ok (some none) => { s with conn := if s.conn.error.isSome then s.conn else
            { s.conn with error := some ⟨.noError, "Server disconnected without sending a response."⟩ } }
        | .error m => { s with failure := s.failure <|> some m }
      let stop := s.conn.error.isSome || s.failure.isSome
      set { s with stopped := stop, reading := !stop }
      pure stop
    try l.flush none catch _ => pure ()
    l.wake
    if stop then return

/-- Start the reader unless one is running. -/
def H2Link.ensureReader (l : H2Link) : IO Unit := do
  let start ← l.shared.atomically do
    let s ← get
    if s.reading || s.stopped then pure false else set { s with reading := true }; pure true
  if start then
    let _ ← IO.asTask (prio := .dedicated) (try l.readLoop catch _ =>
      l.shared.atomically (modify fun s => { s with reading := false }))

/-- Open a connection to an address, send the preface and start its reader. -/
def H2Link.connect (addr : SocketAddress) (timeout : Timeout) : IO H2Link := do
  let sock ← TCP.Socket.Client.mk
  socketOp timeout.connect (.connectTimeout "timed out") .connectError (sock.connect addr)
  let l : H2Link := { sock, shared := ← Std.Mutex.new { conn := Conn.new } }
  l.flush timeout.write
  pure l

/-- Leave a promise to be woken at the next change. -/
def Shared.wait : Std.AtomicT Shared IO (IO.Promise Unit) := do
  let p ← IO.Promise.new
  modify fun s => { s with waiters := s.waiters.push p }
  pure p

/-- How far a stream has come: a number that grows with each event on it. -/
def progressOf (c : Conn) (sid : Nat) : Nat :=
  match c.stream? sid with
  | some s => (if s.response.isSome then 1 else 0) + s.body.length + (if s.ended then 1 else 0)
  | none => 0

/-- Wait for a stream's outcome. The read timeout counts from the stream's
last progress; when it passes, the stream is reset and `ReadTimeout` raised. -/
def H2Link.await (l : H2Link) (sid : Nat) (t : Option Float) :
    IO (Except String (Nat × List HeaderField × ByteArray)) := do
  let mut mark := 0
  let mut since ← IO.monoMsNow
  for _ in [0:unbounded] do
    let r ← l.shared.atomically do
      let s ← get
      if let some m := s.failure then
        set { s with conn := s.conn.release sid }; return Sum.inl (Sum.inl m)
      match s.conn.outcome sid with
      | some o => set { s with conn := s.conn.release sid }; return Sum.inl (Sum.inr o)
      | none => return Sum.inr (← Shared.wait, progressOf s.conn sid)
    match r with
    | .inl (.inl m) => l.wake; throw (IO.userError m)
    | .inl (.inr o) => l.wake; return o
    | .inr (p, m) =>
      let now ← IO.monoMsNow
      if m != mark then mark := m; since := now
      match t with
      | none => waitWake p none
      | some secs =>
        let deadline := since + toMs secs
        if now ≥ deadline then
          l.shared.atomically (modify fun s =>
            { s with conn := (s.conn.send (.rstStream sid ErrorCode.cancel.toNat)).release sid })
          try l.flush none catch _ => pure ()
          l.wake
          raise (.readTimeout "timed out")
        waitWake p (some (deadline - now))
  return .error "unreachable"

/-- Start a request, waiting (at most the pool timeout) while the
connection has no stream free. -/
def H2Link.start (l : H2Link) (fields : List HeaderField) (body : ByteArray) (t : Timeout) : IO Nat := do
  let t0 ← IO.monoMsNow
  for _ in [0:unbounded] do
    let r ← l.shared.atomically do
      let s ← get
      if let some m := s.failure then return Except.error (IO.userError m)
      match s.conn.startRequest fields body with
      | .ok (c, sid) => set { s with conn := c }; return .ok (Sum.inl sid)
      | .error e =>
        if e.code == .refusedStream && e.message == "Too many concurrent streams" then
          return .ok (Sum.inr (← Shared.wait))
        return .error (IO.userError (toString (HTTPError.remoteProtocolError s!"{e.code.name}: {e.message}")))
    match r with
    | .error e => throw e
    | .ok (.inl sid) => l.ensureReader; l.flush t.write; return sid
    | .ok (.inr p) =>
      let now ← IO.monoMsNow
      match t.pool with
      | none => waitWake p none
      | some secs =>
        if now ≥ t0 + toMs secs then raise (.poolTimeout "timed out")
        waitWake p (some (t0 + toMs secs - now))
  raise (.poolTimeout "timed out")

/-- Whether a connection can take new requests. -/
def H2Link.usable (l : H2Link) : IO Bool :=
  l.shared.atomically do
    let s ← get
    pure (s.failure.isNone && !s.stopped && s.conn.error.isNone && s.conn.goaway.isNone)

/-- A pool entry: the connection, once open (or the error opening it). -/
abbrev Pending := IO.Promise (Except IO.Error H2Link)

/-- The pool: one connection per origin. Opening one is a promise in the
pool, so requests started together share it, and none holds the pool's
lock while the connection opens. -/
structure H2Pool where
  links : Std.Mutex (List (String × Nat × Pending))
  next : IO.Ref Nat

/-- The address of a request's origin. -/
def originAddr (r : Request) : IO SocketAddress := do
  let host := r.url.host
  let port := r.url.port.getD 80
  let addrs ← try (DNS.getAddrInfo host (toString port)).block
    catch e => raise (.connectError s!"[Errno -2] Name or service not known: {e}")
  let some ip := addrs[0]? | raise (.connectError "No address for host")
  pure (match ip with
    | .v4 a => .v4 ⟨a, port.toUInt16⟩
    | .v6 a => .v6 ⟨a, port.toUInt16⟩)

/-- A connection to the request's origin: the open one, or a new one. -/
def H2Pool.link (p : H2Pool) (r : Request) : IO H2Link := do
  let origin := s!"{r.url.scheme}://{r.url.netloc}"
  for _ in [0:unbounded] do
    let id ← p.next.modifyGet fun n => (n, n + 1)
    let (entry, mine) ← p.links.atomically do
      match (← get).find? (·.1 == origin) with
      | some (_, gen, pend) => pure ((gen, pend), false)
      | none =>
        let pend : Pending ← IO.Promise.new
        modify ((origin, id, pend) :: ·)
        pure ((id, pend), true)
    let (gen, pend) := entry
    if mine then
      let res ← try (do pure (Except.ok (← H2Link.connect (← originAddr r) r.timeout))) catch e => pure (.error e)
      pend.resolve res
    let drop := p.links.atomically (modify (·.filter fun (o, g, _) => !(o == origin && g == gen)))
    match ← IO.wait pend.result? with
    | some (.ok l) =>
      if ← l.usable then return l
      drop
    | some (.error e) => drop; throw e
    | none => drop
  raise (.poolTimeout "timed out")

/-- Tries of a request the server refuses unprocessed. -/
def maxAttempts : Nat := 3

/-- The outcome of a stream above a `GOAWAY`'s last stream: the server
did not process it (RFC 9113 section 6.8), so it may go again. -/
def refusedUnprocessed (m : String) : Bool :=
  m.startsWith "Server sent GOAWAY" && (m.splitOn "was not processed").length > 1

/-- **`HTTP2Transport`**: HTTP/2 with prior knowledge over TCP, one
multiplexed connection per origin. -/
def HTTP2Transport.new : IO Transport := do
  let p : H2Pool := { links := ← Std.Mutex.new [], next := ← IO.mkRef 0 }
  return {
    handleRequest := fun r => do
      if r.url.scheme == "https" then
        raise (.unsupportedProtocol "HTTPS is not supported: this transport has no TLS")
      if r.url.scheme != "http" then
        raise (.unsupportedProtocol s!"Request URL has an unsupported protocol '{r.url.scheme}://'.")
      -- a request the server refused unprocessed (GOAWAY) goes again on a new
      -- connection, as httpcore's pool retries on `ConnectionNotAvailable`
      for attempt in [0:maxAttempts] do
        let l ← p.link r
        let sid ← l.start (H2.requestFields r) r.content r.timeout
        match ← l.await sid r.timeout.read with
        | .error m =>
          if refusedUnprocessed m && attempt + 1 < maxAttempts then continue
          raise (.remoteProtocolError m)
        | .ok (status, fields, body) =>
          return {
            statusCode := status,
            headers := ⟨fields.map fun f => (Text.decodeHeader f.name, Text.decodeHeader f.value)⟩,
            stream := some body, httpVersion := "HTTP/2" }
      raise (.remoteProtocolError "unreachable")
    close := do
      let links ← p.links.atomically do
        let links : List (String × Nat × Pending) ← get
        set ([] : List (String × Nat × Pending))
        pure links
      for (_, _, pend) in links do
        if ← IO.hasFinished pend.result? then
          if let some (.ok l) := pend.result?.get then
            try (l.sock.shutdown).block catch _ => pure ()
            l.wake }

/-- `httpx.HTTPTransport(http1=..., http2=...)`: HTTP/2 with prior
knowledge when HTTP/1.1 is off, else HTTP/1.1 (without TLS there is no
ALPN to negotiate HTTP/2, as with httpx on an `http` URL). -/
def httpTransport (http1 : Bool := true) (http2 : Bool := false) : IO Transport :=
  if http2 && !http1 then HTTP2Transport.new else pure HTTPTransport

end LeanHttpx
