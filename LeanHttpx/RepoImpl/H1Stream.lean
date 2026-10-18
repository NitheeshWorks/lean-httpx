import LeanHttpx.RepoImpl.H1Body

/-!
# Where a response ends, on a stream

The transport reads a response from a socket a piece at a time and has to
know when to stop reading, before the message can be decoded. Three pure
functions answer that from the bytes received so far, without decoding:

* `headEnd? b from`: the position after the blank line that ends the head;
* `scanChunks b pos`: whether a chunked body is complete, resuming from the
  start of the first chunk not yet known to be whole;
* the limits h11 applies through httpcore: a head, a chunk-size line or a
  trailer block of at most `maxIncompleteEventSize` bytes (100 KiB), and a
  chunk size of at most 20 hex digits.

They only decide when to stop reading; the message itself is then decoded
by the verified codec (`H1.readResponse`).
-/

namespace LeanHttpx

namespace H1

/-- httpcore's `MAX_INCOMPLETE_EVENT_SIZE`: the longest head (or other
incomplete event) h11 buffers before failing with "Receive buffer too long". -/
def maxIncompleteEventSize : Nat := 100 * 1024

/-- The position of the first `CR LF` at or after `start`, if any. -/
def findCRLF (b : ByteArray) (start : Nat) : Option Nat := Id.run do
  for i in [start:b.size - 1] do
    if b[i]! == CR && b[i + 1]! == LF then return some i
  return none

/-- The position after the first `CR LF CR LF` at or after `start`, if any. -/
def findBlankLine (b : ByteArray) (start : Nat) : Option Nat := Id.run do
  for i in [start:b.size - 3] do
    if b[i]! == CR && b[i + 1]! == LF && b[i + 2]! == CR && b[i + 3]! == LF then return some (i + 4)
  return none

/-- Where the head ends: the position after its blank line. `scanned` is how
many bytes were already searched, so a growing buffer is searched once. -/
def headEnd? (b : ByteArray) (scanned : Nat) : Option Nat := findBlankLine b (scanned - 3)

/-- The progress of a chunked body. -/
inductive ChunkScan where
  /-- More bytes are needed; resume at this position (a chunk's start). -/
  | more (pos : Nat)
  /-- The body (with its last chunk and trailers) ends here. -/
  | done (stop : Nat)
  /-- The body cannot be valid (h11's message). -/
  | bad (message : String)
  deriving Repr, DecidableEq

/-- The value of the hex digits at `i`, and how many there are; it stops
after 21 digits (one past h11's 20), so the work is bounded. -/
def hexRun (b : ByteArray) (i stop : Nat) : Nat × Nat := Id.run do
  let mut v := 0
  let mut k := 0
  for j in [i:min stop (i + 21)] do
    let c := b[j]!
    if isHexByte c then v := v * 16 + hexVal c; k := k + 1 else break
  return (v, k)

/-- Scan a chunked body from `pos` (the start of a chunk). Each step passes
one whole chunk, so a scan resumed from the returned position reads every
byte a bounded number of times. -/
def scanChunks (b : ByteArray) (pos : Nat) : ChunkScan := Id.run do
  let mut pos := pos
  -- each pass consumes at least three bytes, so `b.size + 1` passes suffice
  for _ in [0:b.size + 1] do
    match findCRLF b pos with
    | none =>
      if b.size - pos > maxIncompleteEventSize then return .bad "Receive buffer too long"
      return .more pos
    | some eol =>
      if eol - pos > maxIncompleteEventSize then return .bad "Receive buffer too long"
      let (n, k) := hexRun b pos eol
      if k == 0 || k > 20 then return .bad "illegal chunk header"
      if n == 0 then
        -- trailers: an empty line at once, or fields up to a blank line
        if b.size < eol + 4 then return .more pos
        if b[eol + 2]! == CR && b[eol + 3]! == LF then return .done (eol + 4)
        match findBlankLine b (eol + 2) with
        | some e =>
          if e - pos > maxIncompleteEventSize then return .bad "Receive buffer too long"
          return .done e
        | none =>
          if b.size - pos > maxIncompleteEventSize then return .bad "Receive buffer too long"
          return .more pos
      let next := eol + 2 + n + 2
      if b.size < next then return .more pos
      pos := next
  return .more pos

end H1

end LeanHttpx
