import LeanHttpx

/-!
# Native checks of `HTTP2Transport` against a hostile HTTP/2 server

`lake exe native2` starts an HTTP/2 (prior knowledge) server in this
process, on `127.0.0.1` at a free port, whose behaviour each request path
selects, then sends requests with a client built as
`Client.new (http1 := false) (http2 := true)` and checks the outcome, the
time it took, and the peak resident memory. Each case names what httpx
0.28.1 with h2 4.4.1 does against the same server (`lake exe native2
serve` runs only the server).

`lake exe native2 bench` reads a 200 MiB body in 16 KiB `DATA` frames, with
bounds of twice upstream's time and memory.
-/

open LeanHttpx Std.Net Std.Async H2 Hpack

def u (s : String) : ByteArray := s.toUTF8

def mib : Nat := 1024 * 1024

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

def sendFrames (c : TCP.Socket.Client) (fs : List Frame) : IO Unit :=
  send c (fs.foldl (fun b f => b ++ printFrame f) .empty)

/-- A response head as an HPACK block (static encoding). -/
def headBlock (status : Nat) (extra : List (String × String) := []) : ByteArray :=
  encodeStatic ((⟨u ":status", u (toString status), false⟩ : HeaderField) ::
    extra.map fun (k, v) => ⟨u k, u v, false⟩)

/-- Server-side connection: buffered input, and the HPACK decoder. -/
structure Peer where
  sock : TCP.Socket.Client
  buf : IO.Ref ByteArray
  dec : IO.Ref Decoder

/-- The next frame from the client (`none` at the end). -/
def Peer.frame (p : Peer) : IO (Option Frame) := do
  for _ in [0:100000] do
    match parseFrame maxFrameSizeLimit (← p.buf.get) with
    | .done f rest => p.buf.set rest; return some f
    | .fail _ => return none
    | .more =>
      match ← (p.sock.recv? 65536).block with
      | some b => if b.isEmpty then return none else p.buf.modify (· ++ b)
      | none => return none
  return none

/-- The next request: its stream and path (skipping other frames). -/
def Peer.request (p : Peer) : IO (Option (Nat × String)) := do
  for _ in [0:10000] do
    match ← p.frame with
    | none => return none
    | some (.headers sid blk _ _ _ _) =>
      match (← p.dec.get).decode blk with
      | .ok (fs, d) =>
        p.dec.set d
        let path := (fs.find? (·.name == u ":path")).map (fun f => (String.fromUTF8? f.value).getD "/")
        return some (sid, path.getD "/")
      | .error _ => return none
    | some _ => pure ()
  return none

def ok (sid : Nat) (body : String) : List Frame :=
  [.headers sid (headBlock 200 [("content-length", toString body.utf8ByteSize)]) false true none none,
   .data sid (u body) true none]

def hold : IO Unit := IO.sleep 3000

/-- What the server does for each path. -/
def behave (p : Peer) (sid : Nat) : String → IO Unit
  | "/ok" => do sendFrames p.sock (ok sid "hello"); hold
  | "/multi" => do
    -- wait for two more requests, then answer all three, interleaved, last first
    let some (s2, _) ← p.request | return
    let some (s3, _) ← p.request | return
    sendFrames p.sock ([s3, s2, sid].map fun s => .headers s (headBlock 200) false true none none)
    sendFrames p.sock ([s3, s2, sid].map fun s => .data s (u s!"part-{s}-") false none)
    sendFrames p.sock ([sid, s2, s3].map fun s => .data s (u s!"end-{s}") true none)
    hold
  | "/big-frame" => do
    send p.sock (encodeRaw ⟨0, 0, sid, fill 120 20000⟩); hold
  | "/continuation-flood" => do
    sendFrames p.sock [.headers sid (headBlock 200) false false none none]
    let one := printFrame (.continuation sid (u "a") false)
    let mut blk := ByteArray.empty
    for _ in [0:100000] do blk := blk ++ one
    try send p.sock blk catch _ => pure ()
    hold
  | "/hpack-bomb" => do
    -- one 4 KiB entry into the dynamic table, then 20000 one-byte references
    let big := encodeReps [.literal .incremental (.lit (u "x-bomb")) (fill 98 4000)]
    let refs := encodeReps (List.replicate 20000 (Rep.indexed 62))
    sendFrames p.sock (Conn.headerFrames sid (headBlock 200 ++ big ++ refs) false defaultMaxFrameSize); hold
  | "/ping-flood" => do
    let one := printFrame (.ping false (fill 0 8))
    let mut blk := ByteArray.empty
    for _ in [0:100000] do blk := blk ++ one
    try send p.sock blk catch _ => pure ()
    hold
  | "/settings-flood" => do
    let one := printFrame (.settings false [(settingsMaxConcurrentStreams, 100)])
    let mut blk := ByteArray.empty
    for _ in [0:100000] do blk := blk ++ one
    try send p.sock blk catch _ => pure ()
    hold
  | "/reset" => do sendFrames p.sock [.rstStream sid ErrorCode.internalError.toNat]; hold
  | "/rst-flood" => do
    sendFrames p.sock (ok sid "hello")
    let one := printFrame (.rstStream sid ErrorCode.cancel.toNat)
    let mut blk := ByteArray.empty
    for _ in [0:100000] do blk := blk ++ one
    try send p.sock blk catch _ => pure ()
    hold
  | "/push" => do
    sendFrames p.sock [.pushPromise sid 2 (headBlock 200) true none]; hold
  | "/window-overflow" => do
    sendFrames p.sock [.windowUpdate 0 (2 ^ 31 - 1)]; hold
  | "/goaway" => do
    sendFrames p.sock [.goaway 0 ErrorCode.noError.toNat .empty]; hold
  | "/silent" => hold
  | "/big-body" => do
    sendFrames p.sock [.headers sid (headBlock 200 [("content-length", toString (200 * mib))]) false true none none]
    let block := fill 120 16384
    let frame := printFrame (.data sid block false none)
    let mut batch := ByteArray.empty
    for _ in [0:64] do batch := batch ++ frame
    for _ in [0:200] do
      try send p.sock batch catch _ => return
    sendFrames p.sock [.data sid .empty true none]
    hold
  | _ => do sendFrames p.sock (ok sid "?"); hold

def serveConn (c : TCP.Socket.Client) : IO Unit := do
  let p : Peer := { sock := c, buf := ← IO.mkRef .empty, dec := ← IO.mkRef {} }
  -- the preface, then our settings and the acknowledgement of theirs
  for _ in [0:100] do
    if (← p.buf.get).size ≥ 24 then break
    match ← (c.recv? 65536).block with
    | some b => if b.isEmpty then return else p.buf.modify (· ++ b)
    | none => return
  p.buf.modify fun b => b.extract 24 b.size
  sendFrames c [.settings false [], .settings true []]
  -- answer every request on this connection, each in its own task
  for _ in [0:1000] do
    let some (sid, path) ← p.request | return
    -- "/multi" reads the next requests itself, so it runs here
    if path == "/multi" then behave p sid path
    else let _ ← IO.asTask (prio := .dedicated) (try behave p sid path catch _ => pure ())

def serve (srv : TCP.Socket.Server) : IO Unit := do
  for _ in [0:1000000] do
    let c ← srv.accept.block
    let _ ← IO.asTask (prio := .dedicated) do
      try serveConn c catch _ => pure ()

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

def outcome (port : Nat) (path : String) (read : Float := 2.0) : IO String := do
  try
    let c ← Client.new (http1 := false) (http2 := true)
      (timeout := { connect := some 2.0, read := some read, write := some 2.0, pool := some 2.0 })
    let r ← c.get s!"http://127.0.0.1:{port}{path}"
    c.close
    return s!"{r.statusCode} {String.fromUTF8? r.content |>.getD "<bytes>"}"
  catch e => return toString e

structure Case where
  path : String
  expect : String
  upstream : String
  ms : Nat := 1000
  read : Float := 2.0

def cases : List Case := [
  { path := "/ok", expect := "200 hello", upstream := "200 hello" },
  { path := "/big-frame", expect := "RemoteProtocolError: FRAME_SIZE_ERROR",
    upstream := "LocalProtocolError: Received overlong frame: length 20000, max 16384" },
  { path := "/continuation-flood", expect := "RemoteProtocolError: PROTOCOL_ERROR: Too many continuation frames",
    upstream := "LocalProtocolError: Too many continuation frames received." },
  { path := "/hpack-bomb", expect := "RemoteProtocolError: COMPRESSION_ERROR: Header list too large",
    upstream := "LocalProtocolError: Oversized header block: A header list larger than 65536 has been received" },
  { path := "/ping-flood", expect := "RemoteProtocolError: ENHANCE_YOUR_CALM", upstream := "ReadError: [Errno 104] Connection reset by peer, after 3 s (h2 answers every PING)" },
  { path := "/settings-flood", expect := "RemoteProtocolError: ENHANCE_YOUR_CALM", upstream := "ReadError: [Errno 104] Connection reset by peer, after 3 s (h2 answers every SETTINGS)" },
  { path := "/reset", expect := "RemoteProtocolError: Stream 1 was reset by the server: INTERNAL_ERROR",
    upstream := "RemoteProtocolError: <StreamReset stream_id:1, error_code:2, remote_reset:True>" },
  { path := "/rst-flood", expect := "200 hello", upstream := "200 hello" },
  { path := "/push", expect := "RemoteProtocolError: PROTOCOL_ERROR: Received PUSH_PROMISE", upstream := "LocalProtocolError: Received pushed stream" },
  { path := "/window-overflow", expect := "RemoteProtocolError: FLOW_CONTROL_ERROR", upstream := "LocalProtocolError: May not increment flow control window past 2147483647" },
  { path := "/goaway", expect := "RemoteProtocolError: Server sent GOAWAY", upstream := "RemoteProtocolError: <ConnectionTerminated error_code:0, last_stream_id:0, additional_data:None>" },
  { path := "/silent", expect := "ReadTimeout: timed out", upstream := "ReadTimeout: timed out", read := 0.3 }
]

/-- Three requests on one connection, answered out of order. -/
def multiplexed (port : Nat) : IO String := do
  let c ← Client.new (http1 := false) (http2 := true)
  let tasks ← (List.range 3).mapM fun _ => IO.asTask (c.get s!"http://127.0.0.1:{port}/multi")
  let mut out := #[]
  for t in tasks do
    match ← IO.wait t with
    | .ok r => out := out.push s!"{r.statusCode} {String.fromUTF8? r.content |>.getD ""} {r.httpVersion}"
    | .error e => out := out.push (toString e)
  c.close
  return ", ".intercalate out.toList

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
  let t0 ← IO.monoMsNow
  let m ← multiplexed port
  let dt := (← IO.monoMsNow) - t0
  let parts := m.splitOn ", "
  let good := parts.length == 3 && parts.all (fun s => s.startsWith "200 part-" && s.endsWith "HTTP/2") && dt ≤ 1000
  allOk := allOk && good
  IO.println s!"{if good then "ok  " else "FAIL"}  multiplexed  {dt} ms  {m}"
  let kb ← peakKB
  let good := kb ≤ 300 * 1024
  allOk := allOk && good
  IO.println s!"{if good then "ok  " else "FAIL"}  peak memory {kb / 1024} MiB (bound 300 MiB)"
  return allOk

/-- Twice httpx 0.28.1 with h2 4.4.1 on the same body from `lake exe
native2 serve`: 0.90 s and 451 MiB. -/
def benchBounds : Nat × Nat := (1808, 902)

def bench (port : Nat) : IO Bool := do
  let c ← Client.new (http1 := false) (http2 := true)
  let t0 ← IO.monoMsNow
  let r ← c.get s!"http://127.0.0.1:{port}/big-body"
  let dt := (← IO.monoMsNow) - t0
  let mb := (← peakKB) / 1024
  let good := r.content.size == 200 * mib && dt ≤ benchBounds.1 && mb ≤ benchBounds.2
  IO.println s!"RESULT /h2/big-body 200 MiB: {dt} ms, peak {mb} MiB (bounds {benchBounds.1} ms, {benchBounds.2} MiB)"
  if !good then IO.println "  FAIL"
  return good

def main (args : List String) : IO UInt32 := do
  let port ← startServer
  if args.head? == some "serve" then
    IO.println s!"{port}"; (← IO.getStdout).flush
    IO.sleep 600000
    IO.Process.exit 0
  let good ← match args with
    | ["bench"] => bench port
    | _ => runCases port
  IO.println (if good then "all clean" else "FAILED")
  (← IO.getStdout).flush
  IO.Process.exit (if good then 0 else 1)
