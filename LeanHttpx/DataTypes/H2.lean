/-!
# HTTP/2 frames (RFC 9113)

What `h2` (hyperframe, hpack) handles for httpcore's HTTP/2 connection: the
frames on the wire, the error codes and the settings. A `RawFrame` is the
nine-byte frame header and an uninterpreted payload; a `Frame` is the same
frame with its payload read according to its type.
-/

namespace LeanHttpx

namespace H2

/-- RFC 9113 section 7 error codes. -/
inductive ErrorCode where
  | noError | protocolError | internalError | flowControlError | settingsTimeout
  | streamClosed | frameSizeError | refusedStream | cancel | compressionError
  | connectError | enhanceYourCalm | inadequateSecurity | http11Required
  deriving DecidableEq, Repr, Inhabited

/-- The code on the wire. -/
def ErrorCode.toNat : ErrorCode → Nat
  | .noError => 0 | .protocolError => 1 | .internalError => 2 | .flowControlError => 3
  | .settingsTimeout => 4 | .streamClosed => 5 | .frameSizeError => 6 | .refusedStream => 7
  | .cancel => 8 | .compressionError => 9 | .connectError => 10 | .enhanceYourCalm => 11
  | .inadequateSecurity => 12 | .http11Required => 13

/-- The name h2 prints (`ErrorCodes(n).name`). -/
def ErrorCode.name : ErrorCode → String
  | .noError => "NO_ERROR" | .protocolError => "PROTOCOL_ERROR" | .internalError => "INTERNAL_ERROR"
  | .flowControlError => "FLOW_CONTROL_ERROR" | .settingsTimeout => "SETTINGS_TIMEOUT"
  | .streamClosed => "STREAM_CLOSED" | .frameSizeError => "FRAME_SIZE_ERROR"
  | .refusedStream => "REFUSED_STREAM" | .cancel => "CANCEL" | .compressionError => "COMPRESSION_ERROR"
  | .connectError => "CONNECT_ERROR" | .enhanceYourCalm => "ENHANCE_YOUR_CALM"
  | .inadequateSecurity => "INADEQUATE_SECURITY" | .http11Required => "HTTP_1_1_REQUIRED"

/-- The name of a code on the wire (an unknown code is printed as a number). -/
def errorName (n : Nat) : String :=
  match [ErrorCode.noError, .protocolError, .internalError, .flowControlError, .settingsTimeout,
    .streamClosed, .frameSizeError, .refusedStream, .cancel, .compressionError, .connectError,
    .enhanceYourCalm, .inadequateSecurity, .http11Required].find? (·.toNat == n) with
  | some c => c.name
  | none => toString n

/-- A connection error: the code to send in `GOAWAY`, and why. -/
structure Error where
  code : ErrorCode
  message : String
  deriving Repr, Inhabited

/-- The stream a frame depends on, and its weight (RFC 9113 section 5.3,
deprecated but still on the wire). `weight` is the wire value, 0 to 255. -/
structure Priority where
  exclusive : Bool
  dependency : Nat
  weight : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A frame as it is on the wire: type, flags, stream and payload. -/
structure RawFrame where
  type : Nat
  flags : Nat
  streamId : Nat
  payload : ByteArray
  deriving Inhabited

/-- A frame, its payload interpreted by type. Padding is a length; the
padding bytes are zeros when printed and ignored when read. -/
inductive Frame where
  | data (streamId : Nat) (data : ByteArray) (endStream : Bool) (pad : Option Nat)
  | headers (streamId : Nat) (block : ByteArray) (endStream endHeaders : Bool)
      (priority : Option Priority) (pad : Option Nat)
  | priority (streamId : Nat) (priority : Priority)
  | rstStream (streamId : Nat) (code : Nat)
  | settings (ack : Bool) (params : List (Nat × Nat))
  | pushPromise (streamId : Nat) (promised : Nat) (block : ByteArray) (endHeaders : Bool) (pad : Option Nat)
  | ping (ack : Bool) (data : ByteArray)
  | goaway (lastStreamId : Nat) (code : Nat) (debug : ByteArray)
  | windowUpdate (streamId : Nat) (increment : Nat)
  | continuation (streamId : Nat) (block : ByteArray) (endHeaders : Bool)
  /-- A frame of a type this library does not know: kept, and ignored. -/
  | unknown (type : Nat) (flags : Nat) (streamId : Nat) (payload : ByteArray)
  deriving Inhabited

/-- Setting identifiers (RFC 9113 section 6.5.2). -/
def settingsHeaderTableSize : Nat := 1
def settingsEnablePush : Nat := 2
def settingsMaxConcurrentStreams : Nat := 3
def settingsInitialWindowSize : Nat := 4
def settingsMaxFrameSize : Nat := 5
def settingsMaxHeaderListSize : Nat := 6

end H2

end LeanHttpx
