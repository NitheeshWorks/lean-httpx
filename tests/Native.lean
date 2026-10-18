import LeanHttpx

/-!
# Native checks of `HTTPTransport` against a hostile server

`lake exe native` starts a TCP server in this process, on `127.0.0.1` at a
free port, whose behaviour each request path selects, then sends requests
with `HTTPTransport` and checks the outcome, the time it took, and (for the
large cases) the peak resident memory. httpcore 1.0.9 / httpx 0.28.1 on the
same server is the reference: each case names what upstream does.

`lake exe native serve` only runs the server and prints its port, so the
same cases can be run with upstream httpx.

`lake exe native bench <path>` is the benchmark: one 200 MiB body
(`/big-body` with `Content-Length`, `/big-chunked` as one chunk) read by the
client in a fresh process, with bounds of twice upstream's time and memory
(`scripts/bench.sh` runs both).
-/

open LeanHttpx Std.Net Std.Async

def u (s : String) : ByteArray := s.toUTF8

def mib : Nat := 1024 * 1024

/-- `n` copies of a byte. -/
def fill (c : UInt8) (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do out := out.push c
  return out

def peakKB : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  for line in s.splitOn "\n" do
    if line.startsWith "VmHWM:" then
      return (String.ofList (line.toList.filter Char.isDigit)).toNat!
  return 0

/-! ## The server -/

def send (c : TCP.Socket.Client) (b : ByteArray) : IO Unit := (c.send b).block

/-- Read the request head; the request target. -/
def readTarget (c : TCP.Socket.Client) : IO String := do
  let mut buf := ByteArray.empty
  for _ in [0:1000] do
    if (H1.headEnd? buf 0).isSome then break
    match ← (c.recv? 65536).block with
    | some b => if b.isEmpty then break else buf := buf ++ b
    | none => break
  let line := String.ofList ((String.fromUTF8? buf |>.getD "").toList.takeWhile (· != (Char.ofNat 13)))
  return ((line.splitOn " ")[1]?.getD "/")

def ok (body : String) : ByteArray :=
  u s!"HTTP/1.1 200 OK\r\nContent-Length: {body.utf8ByteSize}\r\n\r\n{body}"

/-- Send `block` `n` times (stopping when the peer goes away). -/
def stream (c : TCP.Socket.Client) (block : ByteArray) (n : Nat) : IO Unit := do
  for _ in [0:n] do
    try send c block catch _ => return

def hold : IO Unit := IO.sleep 3000

/-- What the server does for each path. -/
def behave (c : TCP.Socket.Client) : String → IO Unit
  | "/big-header" => send c (u "HTTP/1.1 200 OK\r\nX: " ++ fill 97 mib ++ u "\r\nContent-Length: 0\r\n\r\n")
  | "/many-headers" => do
    let mut head := u "HTTP/1.1 200 OK\r\n"
    for _ in [0:200000] do head := head ++ u "A: b\r\n"
    send c (head ++ u "Content-Length: 0\r\n\r\n")
  | "/endless-head" => do
    send c (u "HTTP/1.1 200 OK\r\nX: ")
    stream c (fill 97 mib) 300
  | "/keep-open" => do send c (ok "hello"); hold
  | "/chunked-open" => do
    send c (u "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5;ext=1\r\nhello\r\n0\r\nT: v\r\n\r\n"); hold
  | "/informational" => do
    send c (u "HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 103 Early Hints\r\nLink: </a>\r\n\r\n")
    send c (ok "after"); hold
  | "/close-delimited" => send c (u "HTTP/1.1 200 OK\r\n\r\nto the end")
  | "/short-body" => send c (u "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nabc")
  | "/short-chunked" => send c (u "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhel")
  | "/long-chunk-line" => do
    send c (u "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5;")
    stream c (fill 97 mib) 300
  | "/huge-chunk-size" => send c (u "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nFFFFFFFFFFFFFFFFFFFFF\r\n")
  | "/long-content-length" =>
    send c (u "HTTP/1.1 200 OK\r\nContent-Length: " ++ fill 55 100000 ++ u "\r\n\r\nabc")
  | "/silent" => hold
  | "/nothing" => pure ()
  | "/garbage" => send c (u "hello there\r\n\r\n")
  | "/big-body" => do
    send c (u s!"HTTP/1.1 200 OK\r\nContent-Length: {200 * mib}\r\n\r\n")
    stream c (fill 120 mib) 200
    hold
  | "/big-chunked" => do
    send c (u s!"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n{String.ofList (Nat.toDigits 16 (200 * mib))}\r\n")
    stream c (fill 120 mib) 200
    send c (u "\r\n0\r\n\r\n")
    hold
  | _ => send c (ok "?")

def serve (srv : TCP.Socket.Server) : IO Unit := do
  for _ in [0:1000000] do
    let c ← srv.accept.block
    let _ ← IO.asTask (prio := .dedicated) do
      let target ← readTarget c
      try behave c target catch _ => pure ()
      try (c.shutdown).block catch _ => pure ()

def startServer : IO Nat := do
  let srv ← TCP.Socket.Server.mk
  srv.bind (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
  srv.listen 128
  let port := match ← srv.getSockName with
    | .v4 a => a.port.toNat
    | .v6 a => a.port.toNat
  let _ ← IO.asTask (prio := .dedicated) (serve srv)
  return port

/-! ## The checks -/

/-- The outcome of a request as text: `200 <body>` or the error. -/
def outcome (port : Nat) (path : String) (read : Float := 2.0) : IO String := do
  try
    let r ← LeanHttpx.get s!"http://127.0.0.1:{port}{path}"
      (timeout := { connect := some 2.0, read := some read, write := some 2.0, pool := some 2.0 })
    return s!"{r.statusCode} {String.fromUTF8? r.content |>.getD "<bytes>"}"
  catch e => return toString e

structure Case where
  path : String
  /-- What the outcome starts with. -/
  expect : String
  /-- What upstream does, for the record. -/
  upstream : String
  /-- The most milliseconds it may take. -/
  ms : Nat := 1000
  read : Float := 2.0

def cases : List Case := [
  { path := "/big-header", expect := "RemoteProtocolError: Receive buffer too long",
    upstream := "RemoteProtocolError: Receive buffer too long" },
  { path := "/many-headers", expect := "RemoteProtocolError: Receive buffer too long",
    upstream := "RemoteProtocolError: Receive buffer too long" },
  { path := "/endless-head", expect := "RemoteProtocolError: Receive buffer too long",
    upstream := "RemoteProtocolError: Receive buffer too long" },
  { path := "/keep-open", expect := "200 hello", upstream := "200 hello" },
  { path := "/chunked-open", expect := "200 hello", upstream := "200 hello" },
  { path := "/informational", expect := "200 after", upstream := "200 after" },
  { path := "/close-delimited", expect := "200 to the end", upstream := "200 to the end" },
  { path := "/short-body", expect := "RemoteProtocolError: peer closed connection without sending complete message body",
    upstream := "RemoteProtocolError: peer closed connection without sending complete message body (received 3 bytes, expected 10)" },
  { path := "/short-chunked", expect := "RemoteProtocolError: peer closed connection without sending complete message body (incomplete chunked read)",
    upstream := "RemoteProtocolError: peer closed connection without sending complete message body (incomplete chunked read)" },
  { path := "/long-chunk-line", expect := "RemoteProtocolError: Receive buffer too long",
    upstream := "RemoteProtocolError: Receive buffer too long" },
  { path := "/huge-chunk-size", expect := "RemoteProtocolError: illegal chunk header",
    upstream := "RemoteProtocolError: illegal chunk header: bytearray(b'FFFFFFFFFFFFFFFFFFFFF\\r\\n')" },
  { path := "/long-content-length", expect := "RemoteProtocolError: bad Content-Length",
    upstream := "RemoteProtocolError: bad Content-Length" },
  { path := "/silent", expect := "ReadTimeout: timed out", upstream := "ReadTimeout: timed out",
    read := 0.3 },
  { path := "/nothing", expect := "RemoteProtocolError: Server disconnected without sending a response.",
    upstream := "RemoteProtocolError: Server disconnected without sending a response." },
  { path := "/garbage", expect := "RemoteProtocolError:",
    upstream := "RemoteProtocolError: illegal status line: bytearray(b'hello there')" }
]

def runCases (port : Nat) : IO Bool := do
  let mut allOk := true
  for c in cases do
    let t0 ← IO.monoMsNow
    let out ← outcome port c.path c.read
    let dt := (← IO.monoMsNow) - t0
    let good := out.startsWith c.expect && dt ≤ c.ms
    allOk := allOk && good
    IO.println s!"{if good then "ok  " else "FAIL"}  {c.path}  {dt} ms  {out.take 120}  [upstream: {c.upstream}]"
    (← IO.getStdout).flush
  -- a refused connection
  let out ← outcome 1 "/"
  let good := out.startsWith "ConnectError:"
  allOk := allOk && good
  IO.println s!"{if good then "ok  " else "FAIL"}  refused  {out.take 120}  [upstream: ConnectError: [Errno 111] Connection refused]"
  let kb ← peakKB
  -- the endless head and the long chunk line send 300 MiB; at most 100 KiB is buffered
  let good := kb ≤ 200 * 1024
  allOk := allOk && good
  IO.println s!"{if good then "ok  " else "FAIL"}  peak memory {kb / 1024} MiB (bound 200 MiB)"
  return allOk

/-- Twice upstream's time (ms) and peak memory (MiB) on the same body.
httpx 0.28.1 took 0.46 s and 445 MB on a 200 MiB `Content-Length` body (the
review's measurement), and 0.59 s and 436 MiB on a 200 MiB chunked one, read
from `lake exe native serve`. -/
def benchBounds : String → Nat × Nat
  | "/big-chunked" => (1190, 872)
  | _ => (920, 890)

def bench (port : Nat) (path : String) : IO Bool := do
  let t0 ← IO.monoMsNow
  let r ← LeanHttpx.get s!"http://127.0.0.1:{port}{path}"
  let dt := (← IO.monoMsNow) - t0
  let mb := (← peakKB) / 1024
  let (ms, mbMax) := benchBounds path
  let good := r.content.size == 200 * mib && dt ≤ ms && mb ≤ mbMax
  IO.println s!"RESULT {path} 200 MiB: {dt} ms, peak {mb} MiB (bounds {ms} ms, {mbMax} MiB)"
  if !good then IO.println "  FAIL"
  return good

def main (args : List String) : IO UInt32 := do
  let port ← startServer
  if args.head? == some "serve" then
    -- for running another client (upstream httpx) against the same server
    IO.println s!"{port}"; (← IO.getStdout).flush
    IO.sleep 600000
    IO.Process.exit 0
  let good ← match args with
    | ["bench", path] => bench port path
    | _ => runCases port
  IO.println (if good then "all clean" else "FAILED")
  (← IO.getStdout).flush
  -- the server's tasks never end; exit without waiting for them
  IO.Process.exit (if good then 0 else 1)
