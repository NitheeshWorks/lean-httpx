import LeanHttpx.DataTypes.H2
import LeanHttpx.RepoImpl.Bytes

/-!
# HTTP/2 frames on the wire (hyperframe)

Two layers. `RawFrame` is the nine-byte header (24-bit length, type, flags,
reserved bit and 31-bit stream identifier) and the payload; `parseRaw`
refuses a length above the receiver's `SETTINGS_MAX_FRAME_SIZE` from the
header alone, before any payload is buffered. `Frame.ofRaw` reads a payload
by its type (padding, priority, settings, ...) and `Frame.toRaw` prints one.
The proofs are in `Proofs/H2.lean` (`h2_frame_parse_print_ext`).
-/

namespace LeanHttpx

namespace H2

open Bytes

/-- The result of reading from a buffer that may hold only part of a
message: a value and the bytes after it, a need for more bytes, or an error. -/
inductive Step (α : Type) where
  | done (a : α) (rest : ByteArray)
  | more
  | fail (e : Error)

/-- The initial and smallest `SETTINGS_MAX_FRAME_SIZE` (RFC 9113 6.5.2). -/
def defaultMaxFrameSize : Nat := 16384

/-- The largest frame payload the 24-bit length allows. -/
def maxFrameSizeLimit : Nat := 2 ^ 24 - 1

/-- The length of a frame header. -/
def frameHeaderSize : Nat := 9

/-- The nine header bytes of a raw frame. -/
def rawHeader (f : RawFrame) : ByteArray :=
  beArr 3 f.payload.size ++ (beArr 1 f.type ++ (beArr 1 f.flags ++ beArr 4 f.streamId))

/-- The bytes of a raw frame. -/
def encodeRaw (f : RawFrame) : ByteArray := rawHeader f ++ f.payload

/-- The header fields: length, type, flags and the 32 bits holding the
stream identifier. -/
def readHeader (b : ByteArray) : Option (Nat × Nat × Nat × Nat × ByteArray) := do
  let (len, b) ← takeBE 3 b
  let (ty, b) ← takeBE 1 b
  let (fl, b) ← takeBE 1 b
  let (sid, b) ← takeBE 4 b
  pure (len, ty, fl, sid, b)

/-- **Read one raw frame** from the front of a buffer. A length above
`maxFrameSize` is a `FRAME_SIZE_ERROR` as soon as the header is in; the
reserved bit is ignored. -/
def parseRaw (maxFrameSize : Nat) (b : ByteArray) : Step RawFrame :=
  if b.size < frameHeaderSize then .more else
  match readHeader (b.extract 0 frameHeaderSize) with
  | none => .more
  | some (len, ty, fl, sid, _) =>
    if len > maxFrameSize then
      .fail ⟨.frameSizeError, s!"Received overlong frame: length {len}, max {maxFrameSize}"⟩
    else if b.size < frameHeaderSize + len then .more
    else .done ⟨ty, fl, sid % 2 ^ 31, b.extract frameHeaderSize (frameHeaderSize + len)⟩
      (b.extract (frameHeaderSize + len) b.size)

/-! ## Payloads -/

/-- Flag bit `k`. -/
def flag (fl k : Nat) : Bool := fl / 2 ^ k % 2 == 1

/-- `2 ^ k` when `b`. -/
def bitIf (b : Bool) (k : Nat) : Nat := if b then 2 ^ k else 0

/-- The five bytes of a priority. -/
def priorityBytes (p : Priority) : ByteArray :=
  beArr 4 (p.dependency + bitIf p.exclusive 31) ++ beArr 1 p.weight

/-- The padding length byte, when padded. -/
def padHead : Option Nat → ByteArray
  | none => .empty
  | some p => beArr 1 p

/-- The padding bytes. -/
def padTail : Option Nat → ByteArray
  | none => .empty
  | some p => zeros p

/-- The bytes of a settings list. -/
def settingsBytes : List (Nat × Nat) → ByteArray
  | [] => .empty
  | (k, v) :: ps => beArr 2 k ++ (beArr 4 v ++ settingsBytes ps)

/-- **Print a frame**: its type, flags, stream and payload. -/
def Frame.toRaw : Frame → RawFrame
  | .data sid d es pad =>
    ⟨0, bitIf es 0 + bitIf pad.isSome 3, sid, padHead pad ++ (d ++ padTail pad)⟩
  | .headers sid blk es eh prio pad =>
    ⟨1, bitIf es 0 + bitIf eh 2 + bitIf pad.isSome 3 + bitIf prio.isSome 5, sid,
      padHead pad ++ ((match prio with | some p => priorityBytes p | none => .empty) ++ (blk ++ padTail pad))⟩
  | .priority sid p => ⟨2, 0, sid, priorityBytes p⟩
  | .rstStream sid code => ⟨3, 0, sid, beArr 4 code⟩
  | .settings ack ps => ⟨4, bitIf ack 0, 0, settingsBytes ps⟩
  | .pushPromise sid prom blk eh pad =>
    ⟨5, bitIf eh 2 + bitIf pad.isSome 3, sid, padHead pad ++ (beArr 4 prom ++ (blk ++ padTail pad))⟩
  | .ping ack d => ⟨6, bitIf ack 0, 0, d⟩
  | .goaway last code dbg => ⟨7, 0, 0, beArr 4 last ++ (beArr 4 code ++ dbg)⟩
  | .windowUpdate sid inc => ⟨8, 0, sid, beArr 4 inc⟩
  | .continuation sid blk eh => ⟨9, bitIf eh 2, sid, blk⟩
  | .unknown ty fl sid payload => ⟨ty, fl, sid, payload⟩

/-- An error from a missing field. -/
def need {α : Type} (o : Option α) (code : ErrorCode) (msg : String) : Except Error α :=
  match o with
  | some a => .ok a
  | none => .error ⟨code, msg⟩

/-- Read the padding length, when the frame is padded; the payload after it
is then at least that long. -/
def readPad (padded : Bool) (b : ByteArray) : Except Error (Option Nat × ByteArray) :=
  if padded then do
    let (p, b) ← need (takeBE 1 b) .frameSizeError "Padded frame without a padding length"
    if p > b.size then throw ⟨.protocolError, "Padding is too long"⟩
    pure (some p, b)
  else pure (none, b)

/-- The bytes before the padding. -/
def unpad (pad : Option Nat) (b : ByteArray) : ByteArray :=
  match pad with
  | none => b
  | some p => b.extract 0 (b.size - p)

/-- Read a priority. -/
def readPriority (b : ByteArray) : Except Error (Priority × ByteArray) := do
  let (d, b) ← need (takeBE 4 b) .frameSizeError "Priority too short"
  let (w, b) ← need (takeBE 1 b) .frameSizeError "Priority too short"
  pure (⟨d / 2 ^ 31 == 1, d % 2 ^ 31, w⟩, b)

/-- Read a settings list, six bytes per setting. The fuel is the number of
settings the length allows. -/
def readSettings : Nat → ByteArray → Except Error (List (Nat × Nat))
  | 0, b => if b.size == 0 then .ok [] else .error ⟨.frameSizeError, "Invalid SETTINGS frame length"⟩
  | n + 1, b =>
    if b.size == 0 then .ok [] else do
    let (k, b) ← need (takeBE 2 b) .frameSizeError "Invalid SETTINGS frame length"
    let (v, b) ← need (takeBE 4 b) .frameSizeError "Invalid SETTINGS frame length"
    let ps ← readSettings n b
    pure ((k, v) :: ps)

/-- A frame on stream 0 that must be on a stream, or the reverse. -/
def streamCheck (sid : Nat) (onStream : Bool) (name : String) : Except Error Unit :=
  if onStream && sid == 0 then .error ⟨.protocolError, s!"{name} frame with stream ID 0"⟩
  else if !onStream && sid != 0 then .error ⟨.protocolError, s!"{name} frame with non-zero stream ID"⟩
  else .ok ()

/-- **Read a frame's payload by its type.** Errors are connection errors
with the code RFC 9113 gives. -/
def Frame.ofRaw (r : RawFrame) : Except Error Frame :=
  let fl := r.flags
  let sid := r.streamId
  let b := r.payload
  match r.type with
  | 0 => do
    streamCheck sid true "DATA"
    let (pad, b) ← readPad (flag fl 3) b
    pure (.data sid (unpad pad b) (flag fl 0) pad)
  | 1 => do
    streamCheck sid true "HEADERS"
    let (pad, b) ← readPad (flag fl 3) b
    let (prio, b) ← if flag fl 5 then do let (p, b) ← readPriority b; pure (some p, b) else pure (none, b)
    if pad.getD 0 > b.size then throw ⟨.protocolError, "Padding is too long"⟩
    pure (.headers sid (unpad pad b) (flag fl 0) (flag fl 2) prio pad)
  | 2 => do
    streamCheck sid true "PRIORITY"
    if b.size != 5 then throw ⟨.frameSizeError, "PRIORITY frame must be 5 bytes"⟩
    let (p, _) ← readPriority b
    pure (.priority sid p)
  | 3 => do
    streamCheck sid true "RST_STREAM"
    if b.size != 4 then throw ⟨.frameSizeError, "RST_STREAM frame must be 4 bytes"⟩
    let (c, _) ← need (takeBE 4 b) .frameSizeError "RST_STREAM frame must be 4 bytes"
    pure (.rstStream sid c)
  | 4 => do
    streamCheck sid false "SETTINGS"
    if flag fl 0 && b.size != 0 then throw ⟨.frameSizeError, "SETTINGS ACK frame must be empty"⟩
    if b.size % 6 != 0 then throw ⟨.frameSizeError, "Invalid SETTINGS frame length"⟩
    let ps ← readSettings (b.size / 6) b
    pure (.settings (flag fl 0) ps)
  | 5 => do
    streamCheck sid true "PUSH_PROMISE"
    let (pad, b) ← readPad (flag fl 3) b
    let (prom, b) ← need (takeBE 4 b) .frameSizeError "PUSH_PROMISE frame too short"
    if pad.getD 0 > b.size then throw ⟨.protocolError, "Padding is too long"⟩
    pure (.pushPromise sid (prom % 2 ^ 31) (unpad pad b) (flag fl 2) pad)
  | 6 => do
    streamCheck sid false "PING"
    if b.size != 8 then throw ⟨.frameSizeError, "PING frame must be 8 bytes"⟩
    pure (.ping (flag fl 0) b)
  | 7 => do
    streamCheck sid false "GOAWAY"
    let (last, b) ← need (takeBE 4 b) .frameSizeError "GOAWAY frame too short"
    let (code, b) ← need (takeBE 4 b) .frameSizeError "GOAWAY frame too short"
    pure (.goaway (last % 2 ^ 31) code b)
  | 8 => do
    if b.size != 4 then throw ⟨.frameSizeError, "WINDOW_UPDATE frame must be 4 bytes"⟩
    let (inc, _) ← need (takeBE 4 b) .frameSizeError "WINDOW_UPDATE frame must be 4 bytes"
    pure (.windowUpdate sid (inc % 2 ^ 31))
  | 9 => do
    streamCheck sid true "CONTINUATION"
    pure (.continuation sid b (flag fl 2))
  | ty => pure (.unknown ty fl sid b)

/-- A priority that prints: a 31-bit dependency, a one-byte weight. -/
def Priority.ok (p : Priority) : Bool := p.dependency < 2 ^ 31 && p.weight < 256

/-- A padding length that prints in one byte. -/
def padOk : Option Nat → Bool
  | none => true
  | some p => p < 256

/-- **A frame that prints and reads back**: stream identifiers of 31 bits,
non-zero on the frame types that belong to a stream; fields that fit their
widths; a `PING` of eight bytes; a settings `ACK` without settings; an
unknown frame of a type above 9. -/
def Frame.ok : Frame → Bool
  | .data sid _ _ pad => 0 < sid && sid < 2 ^ 31 && padOk pad
  | .headers sid _ _ _ prio pad => 0 < sid && sid < 2 ^ 31 && padOk pad && prio.all Priority.ok
  | .priority sid p => 0 < sid && sid < 2 ^ 31 && p.ok
  | .rstStream sid c => 0 < sid && sid < 2 ^ 31 && c < 2 ^ 32
  | .settings ack ps => (!ack || ps.isEmpty) && ps.all fun kv => kv.1 < 2 ^ 16 && kv.2 < 2 ^ 32
  | .pushPromise sid prom _ _ pad => 0 < sid && sid < 2 ^ 31 && prom < 2 ^ 31 && padOk pad
  | .ping _ d => d.size == 8
  | .goaway last code _ => last < 2 ^ 31 && code < 2 ^ 32
  | .windowUpdate sid inc => sid < 2 ^ 31 && inc < 2 ^ 31
  | .continuation sid _ _ => 0 < sid && sid < 2 ^ 31
  | .unknown ty fl sid _ => 10 ≤ ty && ty < 256 && fl < 256 && sid < 2 ^ 31

/-- The stream a frame is on. -/
def Frame.streamId : Frame → Nat
  | .data s .. | .headers s .. | .priority s .. | .rstStream s .. | .pushPromise s ..
  | .windowUpdate s .. | .continuation s .. | .unknown _ _ s _ => s
  | .settings .. | .ping .. | .goaway .. => 0

/-- **Print a frame** to bytes. -/
def printFrame (f : Frame) : ByteArray := encodeRaw f.toRaw

/-- **Read a frame** from the front of a buffer, refusing a payload above
`maxFrameSize`. -/
def parseFrame (maxFrameSize : Nat) (b : ByteArray) : Step Frame :=
  match parseRaw maxFrameSize b with
  | .done r rest => match Frame.ofRaw r with
    | .ok f => .done f rest
    | .error e => .fail e
  | .more => .more
  | .fail e => .fail e

end H2

end LeanHttpx
