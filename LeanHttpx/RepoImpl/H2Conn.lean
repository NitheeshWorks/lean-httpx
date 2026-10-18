import LeanHttpx.RepoImpl.H2Frame
import LeanHttpx.RepoImpl.Hpack

/-!
# The HTTP/2 client connection, sans I/O (h2's `H2Connection`, client side)

A `Conn` is the state of one connection: settings on both sides, the HPACK
encoder and decoder, flow-control windows, and the open streams. The
transport feeds it bytes (`receive`), asks it to start requests
(`startRequest`), and writes what it has to send (`takeOutput`). It never
blocks and never does I/O, so every rule below is a pure function of the
bytes received.

Settings and windows are httpcore's: `ENABLE_PUSH 0`,
`MAX_CONCURRENT_STREAMS 100`, `MAX_HEADER_LIST_SIZE 65536`, and the
connection and each stream opened by a further `2 ^ 24` bytes.

What a hostile peer can do, and what stops it (each a connection error, a
`GOAWAY` with the code, then `RemoteProtocolError` for every request):

* **Frame size**: a frame longer than our `SETTINGS_MAX_FRAME_SIZE` (16384)
  is refused from its header (`FRAME_SIZE_ERROR`), so at most one frame is
  buffered.
* **Header blocks**: at most 64 `CONTINUATION` frames per block (h2's
  `CONTINUATION_BACKLOG`) and 256 KiB of block; any other frame in the
  middle of a block is `PROTOCOL_ERROR`; the decoded list is at most
  `MAX_HEADER_LIST_SIZE` and the dynamic table at most what we allowed.
* **Floods**: frames that make no progress on a request (`SETTINGS`, `PING`,
  `PRIORITY`, `RST_STREAM`, `WINDOW_UPDATE`, empty `DATA`, unknown types,
  informational responses) are counted, and the count resets when a
  response makes progress; past `maxControlFrames` it is
  `ENHANCE_YOUR_CALM`. The output our replies queue (`SETTINGS` and `PING`
  acknowledgements) is bounded too, so a peer that sends `PING` without
  reading cannot grow our memory.
* **Streams**: a frame for a stream we never opened (even, or above our
  last), a `PUSH_PROMISE` (push is disabled), a `HEADERS` on a closed
  stream is `PROTOCOL_ERROR`; we open at most the peer's
  `MAX_CONCURRENT_STREAMS` and our own 100. `RST_STREAM` only ends that
  request. Data beyond a window is `FLOW_CONTROL_ERROR`; a window update
  past `2 ^ 31 - 1` likewise.
-/

namespace LeanHttpx

namespace H2

open Hpack

/-- Our side's limits. -/
structure Limits where
  maxFrameSize : Nat := defaultMaxFrameSize
  maxHeaderListSize : Nat := 65536
  maxConcurrentStreams : Nat := 100
  headerTableSize : Nat := 4096
  /-- h2's `CONTINUATION_BACKLOG`. -/
  maxContinuations : Nat := 64
  maxHeaderBlock : Nat := 262144
  /-- Frames without progress on a request before `ENHANCE_YOUR_CALM`. -/
  maxControlFrames : Nat := 10000
  /-- The most output our acknowledgements may queue. -/
  maxPendingOutput : Nat := 1048576
  /-- httpcore's extra window, for the connection and each stream. -/
  windowIncrement : Nat := 2 ^ 24
  deriving Repr, Inhabited

/-- The peer's settings, as far as the client uses them. -/
structure PeerSettings where
  maxFrameSize : Nat := defaultMaxFrameSize
  initialWindowSize : Nat := 65535
  maxConcurrentStreams : Nat := 2 ^ 32
  headerTableSize : Nat := 4096
  deriving Repr, Inhabited

/-- What became of a stream. -/
structure H2Stream where
  id : Nat
  /-- The response head: status and fields (without pseudo-headers). -/
  response : Option (Nat × List HeaderField) := none
  /-- The body so far, in pieces, the last first (a list, so adding a piece
  is constant time even while the stream is shared). -/
  body : List ByteArray := []
  /-- The peer ended the stream. -/
  ended : Bool := false
  /-- We sent END_STREAM. -/
  sentEnd : Bool := false
  /-- The peer reset it (`RST_STREAM`), or a stream error. -/
  reset : Option String := none
  /-- How much we may still send. -/
  sendWindow : Int
  /-- How much the peer may still send; and how much it sent that we have
  not yet given back. -/
  recvWindow : Nat
  unacked : Nat := 0
  /-- Request data waiting for window. -/
  pending : ByteArray := .empty
  pendingEnd : Bool := false
  deriving Inhabited

/-- A stream as a request opens it. -/
def H2Stream.opening (sid : Nat) (sendWindow : Nat) (recvWindow : Nat) (body : ByteArray) : H2Stream :=
  { id := sid, sendWindow := sendWindow, recvWindow := recvWindow, pending := body,
    pendingEnd := body.size != 0, sentEnd := body.size == 0 }

/-- A stream after DATA. -/
def H2Stream.onData (s : H2Stream) (d : ByteArray) (len : Nat) (endStream : Bool) : H2Stream :=
  let body := if d.size == 0 then s.body else d :: s.body
  { s with body, recvWindow := s.recvWindow - len, ended := endStream }

/-- A header block being received. -/
structure HeaderBlock where
  streamId : Nat
  endStream : Bool
  data : ByteArray
  frames : Nat

/-- The connection. -/
structure Conn where
  limits : Limits := {}
  peer : PeerSettings := {}
  enc : Encoder := {}
  dec : Decoder := {}
  streams : List H2Stream := []
  nextStreamId : Nat := 1
  sendWindow : Int := 65535
  recvWindow : Nat := 65535
  unacked : Nat := 0
  inbuf : ByteArray := .empty
  block : Option HeaderBlock := none
  controlFrames : Nat := 0
  /-- `GOAWAY` received: the last stream the peer will process, and the code. -/
  goaway : Option (Nat × Nat) := none
  /-- A connection error, ours or the peer's: no further use. -/
  error : Option Error := none
  out : ByteArray := .empty

/-- The client connection preface (RFC 9113 section 3.4). -/
def preface : ByteArray := "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n".toUTF8

/-- A new connection, with the preface, our settings and the connection
window increment queued (httpcore's `_send_connection_init`). -/
def Conn.new (limits : Limits := {}) : Conn :=
  let settings := Frame.settings false [(settingsEnablePush, 0),
    (settingsMaxConcurrentStreams, limits.maxConcurrentStreams),
    (settingsMaxHeaderListSize, limits.maxHeaderListSize)]
  { limits, dec := { maxTableSize := limits.headerTableSize, maxHeaderListSize := limits.maxHeaderListSize },
    recvWindow := 65535 + limits.windowIncrement,
    out := preface ++ printFrame settings ++ printFrame (.windowUpdate 0 limits.windowIncrement) }

namespace Conn

variable (c : Conn)

/-- Queue a frame. -/
def send (f : Frame) : Conn := { c with out := c.out ++ printFrame f }

/-- Take what there is to send. -/
def takeOutput : ByteArray × Conn := (c.out, { c with out := .empty })

/-- Fail the connection: record the error and queue `GOAWAY`. -/
def fail (e : Error) : Conn :=
  -- a client accepts no streams, so the last stream it processed is 0
  let c := c.send (.goaway 0 e.code.toNat e.message.toUTF8)
  { c with error := some e }

/-- The stream with an identifier. -/
def stream? (sid : Nat) : Option H2Stream := c.streams.find? (·.id == sid)

/-- Change a stream. -/
def modifyStream (sid : Nat) (f : H2Stream → H2Stream) : Conn :=
  { c with streams := c.streams.map fun s => if s.id == sid then f s else s }

/-- Streams still in progress. -/
def active : Nat := (c.streams.filter fun s => !(s.ended || s.reset.isSome)).length

/-- Can another stream start? -/
def canStart : Bool :=
  c.error.isNone && c.goaway.isNone && c.active < min c.peer.maxConcurrentStreams c.limits.maxConcurrentStreams

/-- Send as much pending request data as the windows allow, in frames of
the peer's maximum size. -/
def flushStream (sid : Nat) : Conn := Id.run do
  let some s := c.stream? sid | return c
  let mut c := c
  let mut s := s
  -- every frame carries at least one byte, or ends the stream
  for _ in [0:s.pending.size + 2] do
    let room := min (min c.sendWindow s.sendWindow) c.peer.maxFrameSize
    if s.pending.size == 0 then
      if s.pendingEnd && !s.sentEnd then
        c := c.send (.data sid .empty true none)
        s := { s with sentEnd := true, pendingEnd := false }
      break
    if room ≤ 0 then break
    let n := min s.pending.size room.toNat
    let chunk := s.pending.extract 0 n
    let rest := s.pending.extract n s.pending.size
    let last := rest.size == 0 && s.pendingEnd
    c := c.send (.data sid chunk last none)
    c := { c with sendWindow := c.sendWindow - n }
    s := { s with pending := rest, sendWindow := s.sendWindow - n, sentEnd := s.sentEnd || last,
                  pendingEnd := s.pendingEnd && !last }
  return c.modifyStream sid fun _ => s

/-- Send pending data on every stream. -/
def flushAll : Conn := c.streams.foldl (fun c s => c.flushStream s.id) c

/-- The header block of a request, split into `HEADERS` and `CONTINUATION`
frames of at most the peer's maximum frame size. -/
def headerFrames (sid : Nat) (block : ByteArray) (endStream : Bool) (maxSize : Nat) : List Frame := Id.run do
  let size := max maxSize 1
  let mut out : Array Frame := #[]
  let n := (block.size + size - 1) / size
  let n := max n 1
  for k in [0:n] do
    let piece := block.extract (k * size) ((k + 1) * size)
    let last := k + 1 == n
    if k == 0 then out := out.push (.headers sid piece endStream last none none)
    else out := out.push (.continuation sid piece last)
  return out.toList

/-- **Start a request**: its header fields (pseudo-headers first) and body.
The stream identifier, or why it cannot start now. -/
def startRequest (fields : List HeaderField) (body : ByteArray) : Except Error (Conn × Nat) := do
  if let some e := c.error then throw e
  if c.goaway.isSome then throw ⟨.refusedStream, "The connection received GOAWAY"⟩
  if c.nextStreamId ≥ 2 ^ 31 then throw ⟨.refusedStream, "Stream identifiers exhausted"⟩
  if !c.canStart then throw ⟨.refusedStream, "Too many concurrent streams"⟩
  let sid := c.nextStreamId
  let (block, enc) := c.enc.encode fields
  let endStream := body.size == 0
  let frames := headerFrames sid block endStream c.peer.maxFrameSize
  let s : H2Stream := H2Stream.opening sid c.peer.initialWindowSize (65535 + c.limits.windowIncrement) body

  let c := { c with enc, nextStreamId := sid + 2, streams := c.streams ++ [s] }
  let c := frames.foldl (fun c f => c.send f) c
  let c := c.send (.windowUpdate sid c.limits.windowIncrement)
  pure (c.flushStream sid, sid)

/-- Forget a finished stream. -/
def release (sid : Nat) : Conn := { c with streams := c.streams.filter (·.id != sid) }

/-! ## Receiving -/

/-- Count a frame that makes no progress on a request. -/
def control : Conn :=
  let c := { c with controlFrames := c.controlFrames + 1 }
  if c.controlFrames > c.limits.maxControlFrames then
    c.fail ⟨.enhanceYourCalm, "Too many frames without progress (flood)"⟩
  else c

/-- Progress on a request. -/
def progress : Conn := { c with controlFrames := 0 }

/-- A stream identifier we opened. -/
def opened (sid : Nat) : Bool := sid % 2 == 1 && sid < c.nextStreamId

/-- Why a received field is invalid, if it is (RFC 9113 sections 8.2.1
and 8.2.2, as h2's `validate_headers` checks): a name that is empty or has
upper case, control, space, non-ASCII or (after the first byte) colon
bytes; a value with NUL, CR or LF, or surrounded by space or tab; a
connection-specific field; `te` other than `trailers`. -/
def badField (f : HeaderField) : Option String :=
  let n := f.name.data
  let v := f.value.data
  if n.size == 0 then some "Received header name with zero length."
  else if n.any (fun b => 65 ≤ b && b ≤ 90) then some "Received uppercase header name"
  else if n.any (fun b => b ≤ 32 || b ≥ 127) then some "Illegal character in header name"
  else if (n.extract 1 n.size).any (· == 58) then some "Illegal character ':' in header name"
  else if v.any (fun b => b == 0 || b == 10 || b == 13) then some "Illegal character in header value"
  else if v.size > 0 && (v[0]! == 32 || v[0]! == 9 || v[v.size - 1]! == 32 || v[v.size - 1]! == 9) then
    some "Received header value surrounded by whitespace"
  else if [ "connection", "keep-alive", "proxy-connection", "transfer-encoding", "upgrade"].any
      (fun x => f.name == x.toUTF8) then some "Connection-specific header field present"
  else if f.name == "te".toUTF8 && (String.fromUTF8? f.value |>.map (·.toLower)) != some "trailers" then
    some "Invalid value for TE header"
  else none

/-- Whether a field is a pseudo-header. -/
def isPseudo (f : HeaderField) : Bool := f.name.size > 0 && f.name[0]! == 58

/-- Check a trailer block: no pseudo-headers, every field valid. -/
def trailerCheck (fs : List HeaderField) : Except String Unit := do
  if fs.any isPseudo then throw "Received pseudo-header in trailer"
  if let some f := fs.find? fun f => (badField f).isSome then throw ((badField f).getD "")

/-- Read the status of a response head and keep its regular fields. -/
def responseHead (fs : List HeaderField) : Except String (Nat × List HeaderField) := do
  let pseudos := fs.takeWhile isPseudo
  let rest := fs.dropWhile isPseudo
  if rest.any isPseudo then throw "Received pseudo-header in trailer or after a regular header"
  if let some f := fs.find? fun f => (badField f).isSome then throw ((badField f).getD "")
  let some st := pseudos.find? (·.name == ":status".toUTF8) | throw "Response has no :status"
  if pseudos.any (·.name != ":status".toUTF8) then throw "Unexpected pseudo-header in response"
  if pseudos.length != 1 then throw "Received duplicate pseudo-header field :status"
  let digits := st.value.data.toList
  if digits.length != 3 || !digits.all (fun b => 48 ≤ b && b ≤ 57) then throw "Invalid :status"
  pure (digits.foldl (fun a b => a * 10 + (b.toNat - 48)) 0, rest)

/-- A finished header block on a stream. -/
def onHeaderBlock (sid : Nat) (endStream : Bool) (block : ByteArray) : Conn :=
  match c.dec.decode block with
  | .error e => c.fail e
  | .ok (fs, dec) =>
    let c := { c with dec }
    match c.stream? sid with
    | none => c.control  -- a stream we already released: ignore
    | some s =>
      if s.ended then c.fail ⟨.streamClosed, s!"HEADERS on closed stream {sid}"⟩ else
      match s.response with
      | some _ =>
        -- trailers: must end the stream
        if !endStream then c.fail ⟨.protocolError, "Trailers without END_STREAM"⟩
        else match trailerCheck fs with
          | .error m => (c.modifyStream sid fun s => { s with reset := some m }).send (.rstStream sid ErrorCode.protocolError.toNat)
          | .ok () => (c.modifyStream sid fun s => { s with ended := true }).progress
      | none =>
        match responseHead fs with
        | .error m => (c.modifyStream sid fun s => { s with reset := some m }).send (.rstStream sid ErrorCode.protocolError.toNat)
        | .ok (status, rest) =>
          if status / 100 == 1 then
            if endStream then c.fail ⟨.protocolError, "Informational response with END_STREAM"⟩ else c.control
          else (c.modifyStream sid fun s => { s with response := some (status, rest), ended := endStream }).progress

/-- Give back window once half of it is used (h2's
`acknowledge_received_data`). -/
def ackData (sid : Nat) (n : Nat) : Conn := Id.run do
  let mut c := { c with unacked := c.unacked + n }
  let connMax := 65535 + c.limits.windowIncrement
  if c.unacked * 2 ≥ connMax then
    c := (c.send (.windowUpdate 0 c.unacked))
    c := { c with recvWindow := c.recvWindow + c.unacked, unacked := 0 }
  match c.stream? sid with
  | none => return c
  | some s =>
    let s := { s with unacked := s.unacked + n }
    if s.unacked * 2 ≥ connMax && !s.ended then
      c := c.send (.windowUpdate sid s.unacked)
      return c.modifyStream sid fun _ => { s with recvWindow := s.recvWindow + s.unacked, unacked := 0 }
    return c.modifyStream sid fun _ => s

/-- Handle one frame. -/
def onFrame (len : Nat) (f : Frame) : Conn :=
  match c.block with
  | some b =>
    match f with
    | .continuation sid piece endHeaders =>
      if sid != b.streamId then c.fail ⟨.protocolError, "CONTINUATION on the wrong stream"⟩ else
      let data := b.data ++ piece
      if b.frames + 1 > c.limits.maxContinuations then
        c.fail ⟨.protocolError, "Too many continuation frames received."⟩
      else if data.size > c.limits.maxHeaderBlock then
        c.fail ⟨.enhanceYourCalm, "Header block too large"⟩
      else if endHeaders then { c with block := none }.onHeaderBlock sid b.endStream data
      else { c with block := some { b with data, frames := b.frames + 1 } }
    | _ => c.fail ⟨.protocolError, "Expected CONTINUATION frame"⟩
  | none =>
    match f with
    | .data sid d endStream _ =>
      if !c.opened sid then c.fail ⟨.protocolError, s!"DATA on stream {sid} that was never opened"⟩ else
      if len > c.recvWindow then c.fail ⟨.flowControlError, "DATA beyond the connection window"⟩ else
      let c := { c with recvWindow := c.recvWindow - len }
      match c.stream? sid with
      | none => (c.ackData sid len).control
      | some s =>
        if s.ended then c.fail ⟨.streamClosed, s!"DATA on closed stream {sid}"⟩ else
        if s.response.isNone then c.fail ⟨.protocolError, "DATA before HEADERS"⟩ else
        if len > s.recvWindow then c.fail ⟨.flowControlError, "DATA beyond the stream window"⟩ else
        let c := c.modifyStream sid fun s => s.onData d len endStream
        let c := c.ackData sid len
        if d.size == 0 && !endStream then c.control else c.progress
    | .headers sid blk endStream endHeaders _ _ =>
      if !c.opened sid then c.fail ⟨.protocolError, s!"HEADERS on stream {sid} that was never opened"⟩ else
      if blk.size > c.limits.maxHeaderBlock then c.fail ⟨.enhanceYourCalm, "Header block too large"⟩ else
      if endHeaders then c.onHeaderBlock sid endStream blk
      else { c with block := some ⟨sid, endStream, blk, 1⟩ }
    | .priority .. => c.control
    | .rstStream sid code =>
      if !c.opened sid then c.fail ⟨.protocolError, s!"RST_STREAM on stream {sid} that was never opened"⟩ else
      (c.modifyStream sid fun s =>
        if s.ended then s else { s with reset := some s!"Stream {sid} was reset by the server: {errorName code}" }).control
    | .settings true _ => c.control
    | .settings false ps => Id.run do
      let mut c := c
      for (k, v) in ps do
        -- a server may not enable push (RFC 9113 6.5.2)
        if k == settingsEnablePush && v != 0 then return c.fail ⟨.protocolError, "Invalid ENABLE_PUSH"⟩
        if k == settingsInitialWindowSize then
          if v > 2 ^ 31 - 1 then return c.fail ⟨.flowControlError, "Invalid INITIAL_WINDOW_SIZE"⟩
          let delta : Int := (v : Int) - c.peer.initialWindowSize
          c := { c with peer := { c.peer with initialWindowSize := v },
                        streams := c.streams.map fun s => { s with sendWindow := s.sendWindow + delta } }
          -- RFC 9113 6.9.2: a change that overflows a stream window is a connection error
          if c.streams.any (·.sendWindow > 2 ^ 31 - 1) then
            return c.fail ⟨.flowControlError, "INITIAL_WINDOW_SIZE overflows a stream window"⟩
        if k == settingsMaxFrameSize then
          if v < defaultMaxFrameSize || v > maxFrameSizeLimit then
            return c.fail ⟨.protocolError, "Invalid MAX_FRAME_SIZE"⟩
          c := { c with peer := { c.peer with maxFrameSize := v } }
        if k == settingsMaxConcurrentStreams then
          c := { c with peer := { c.peer with maxConcurrentStreams := v } }
        if k == settingsHeaderTableSize then
          let n := min v 4096
          c := { c with peer := { c.peer with headerTableSize := v }, enc := c.enc.setMaxSize n }
      return (c.send (.settings true [])).flushAll.control
    | .pushPromise .. => c.fail ⟨.protocolError, "Received PUSH_PROMISE, but push is disabled"⟩
    | .ping true _ => c.control
    | .ping false d => (c.send (.ping true d)).control
    | .goaway last code _ =>
      let refuse := fun (s : H2Stream) =>
        if s.id > last && !s.ended && s.reset.isNone then
          { s with reset := some s!"Server sent GOAWAY ({errorName code}); stream {s.id} was not processed" }
        else s
      let c : Conn := { c with goaway := some (last, code), streams := c.streams.map refuse }
      c.control
    | .windowUpdate sid inc =>
      if inc == 0 then c.fail ⟨.protocolError, "WINDOW_UPDATE with an increment of 0"⟩ else
      if sid == 0 then
        if c.sendWindow + inc > 2 ^ 31 - 1 then c.fail ⟨.flowControlError, "Connection window too large"⟩
        else ({ c with sendWindow := c.sendWindow + inc }).flushAll.control
      else
        match c.stream? sid with
        | none => if c.opened sid then c.control else c.fail ⟨.protocolError, "WINDOW_UPDATE on an idle stream"⟩
        | some s =>
          -- a stream error (RFC 9113 6.9.1): reset that stream only
          if s.sendWindow + inc > 2 ^ 31 - 1 then
            (c.modifyStream sid fun s => { s with reset := some s!"Stream {sid} window too large" }).send
              (.rstStream sid ErrorCode.flowControlError.toNat)
          else ((c.modifyStream sid fun s => { s with sendWindow := s.sendWindow + inc }).flushStream sid).control
    | .continuation .. => c.fail ⟨.protocolError, "CONTINUATION without HEADERS"⟩
    | .unknown .. => c.control

/-- **Receive bytes**: handle every whole frame, keep the rest. Each frame
is checked against our maximum frame size from its header, so `inbuf`
never holds more than one frame and a header. -/
def receive (data : ByteArray) : Conn := Id.run do
  if c.error.isSome then return c
  let buf := if c.inbuf.size == 0 then data else c.inbuf ++ data
  let mut c := { c with inbuf := .empty }
  let mut pos := 0
  -- every frame takes at least nine bytes
  for _ in [0:buf.size / frameHeaderSize + 1] do
    if c.error.isSome then break
    -- the frame at `pos`, read by `parseFrame` from a copy of that frame alone
    let len := if buf.size < pos + frameHeaderSize then 0
      else match readHeader (buf.extract pos (pos + frameHeaderSize)) with
        | some (n, _) => n
        | none => 0
    let piece := buf.extract pos (pos + frameHeaderSize + min len (c.limits.maxFrameSize + 1))
    match parseFrame c.limits.maxFrameSize piece with
    | .more => break
    | .fail e => c := c.fail e
    | .done f _ =>
      pos := pos + frameHeaderSize + len
      c := c.onFrame len f
      if c.out.size > c.limits.maxPendingOutput then
        c := c.fail ⟨.enhanceYourCalm, "Too much output queued (the peer is not reading)"⟩
  if c.error.isNone then c := { c with inbuf := buf.extract pos buf.size }
  return c

/-- A stream's outcome: its response with the whole body, its error, or
nothing yet. -/
def outcome (sid : Nat) : Option (Except String (Nat × List HeaderField × ByteArray)) :=
  match c.stream? sid with
  | none => none
  | some s =>
    match s.reset with
    | some m => some (.error m)
    | none =>
      if let some e := c.error then some (.error s!"{e.code.name}: {e.message}") else
      match s.response with
      | some (st, hs) =>
        if s.ended then
          let total := s.body.foldl (fun n b => n + b.size) 0
          some (.ok (st, hs, s.body.foldr (fun b acc => acc ++ b) (ByteArray.emptyWithCapacity total)))
        else none
      | none => none

end Conn

end H2

end LeanHttpx
