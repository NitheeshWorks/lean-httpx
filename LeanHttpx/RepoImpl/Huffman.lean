/-!
# The HPACK Huffman code (RFC 7541 section 5.2 and Appendix B)

The code is canonical: ordered by length, then by symbol, each code is the
previous one plus one, shifted left by the difference in length. So the 257
code lengths of Appendix B determine it, and the table here is just those
lengths (symbol 256 is EOS). `tests/Conformance.lean` checks the codes
against h2's `hpack` and the RFC's examples.

Decoding is canonical decoding, one bit at a time: the code read so far,
compared with the first code of its length. A string ends with at most seven
bits of padding, all ones (a prefix of EOS); EOS itself, longer padding or
padding with a zero is an error (`COMPRESSION_ERROR`).
-/

namespace LeanHttpx

namespace Huffman

/-- The code length of each symbol 0 to 256 (RFC 7541 Appendix B). -/
def codeLengths : Array Nat := #[
  13, 23, 28, 28, 28, 28, 28, 28, 28, 24, 30, 28, 28, 30, 28, 28,
  28, 28, 28, 28, 28, 28, 30, 28, 28, 28, 28, 28, 28, 28, 28, 28,
  6, 10, 10, 12, 13, 6, 8, 11, 10, 10, 8, 11, 8, 6, 6, 6,
  5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 7, 8, 15, 6, 12, 10,
  13, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
  7, 7, 7, 7, 7, 7, 7, 7, 8, 7, 8, 13, 19, 13, 14, 6,
  15, 5, 6, 5, 6, 5, 6, 6, 6, 5, 7, 7, 6, 6, 6, 5,
  6, 7, 6, 5, 5, 6, 7, 7, 7, 7, 7, 15, 11, 14, 13, 28,
  20, 22, 20, 20, 22, 22, 22, 23, 22, 23, 23, 23, 23, 23, 24, 23,
  24, 24, 22, 23, 24, 23, 23, 23, 23, 21, 22, 23, 22, 23, 23, 24,
  22, 21, 20, 22, 22, 23, 23, 21, 23, 22, 22, 24, 21, 22, 23, 23,
  21, 21, 22, 21, 23, 22, 23, 23, 20, 22, 22, 22, 23, 22, 22, 23,
  26, 26, 20, 19, 22, 23, 22, 25, 26, 26, 26, 27, 27, 26, 24, 25,
  19, 21, 26, 27, 27, 26, 27, 24, 21, 21, 26, 26, 28, 27, 27, 27,
  20, 24, 20, 21, 22, 21, 21, 23, 22, 22, 25, 25, 24, 24, 26, 23,
  26, 27, 26, 26, 27, 27, 27, 27, 27, 28, 27, 27, 27, 27, 27, 26,
  30]

/-- The longest code. -/
def maxLen : Nat := 30

/-- Symbols in canonical order: by code length, then by value. -/
def sortedSymbols : Array Nat := Id.run do
  let mut out := #[]
  for len in [1:maxLen + 1] do
    for s in [0:257] do
      if codeLengths[s]! == len then out := out.push s
  return out

/-- The number of codes of each length. -/
def counts : Array Nat := Id.run do
  let mut c := Array.replicate (maxLen + 1) 0
  for s in [0:257] do
    let l := codeLengths[s]!
    c := c.set! l (c[l]! + 1)
  return c

/-- For each length: its first code, and the index in `sortedSymbols` of the
first symbol with that length. -/
def firstCodes : Array (Nat × Nat) := Id.run do
  let mut out := #[(0, 0)]
  let mut code := 0
  let mut index := 0
  for len in [1:maxLen + 1] do
    code := (code + counts[len - 1]!) * 2
    index := index + counts[len - 1]!
    out := out.push (code, index)
  return out

/-- The code of each symbol. -/
def codes : Array Nat := Id.run do
  let mut out := Array.replicate 257 0
  for len in [1:maxLen + 1] do
    let (first, start) := firstCodes[len]!
    for k in [0:counts[len]!] do
      out := out.set! sortedSymbols[start + k]! (first + k)
  return out

/-- Huffman-encode bytes, padding the last byte with ones. -/
def encode (b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut acc : Nat := 0
  let mut bits : Nat := 0
  for x in b.data do
    let s := x.toNat
    acc := acc * 2 ^ codeLengths[s]! + codes[s]!
    bits := bits + codeLengths[s]!
    -- at most 7 + 30 bits are pending, so at most four whole bytes
    for _ in [0:5] do
      if bits ≥ 8 then
        bits := bits - 8
        out := out.push (acc / 2 ^ bits).toUInt8
        acc := acc % 2 ^ bits
  if bits > 0 then
    out := out.push (acc * 2 ^ (8 - bits) + (2 ^ (8 - bits) - 1)).toUInt8
  return out

/-- **Huffman-decode** a string literal; `none` on EOS, on a code longer than
30 bits, or on padding that is not at most seven one bits. The output is at
most `8 * b.size / 5` bytes (the shortest code has five bits). -/
def decode (b : ByteArray) : Option ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (b.size * 8 / 5 + 1)
  let mut code : Nat := 0
  let mut len : Nat := 0
  for x in b.data do
    for k in [0:8] do
      let bit := x.toNat / 2 ^ (7 - k) % 2
      code := code * 2 + bit
      len := len + 1
      if len > maxLen then return none
      let (first, start) := firstCodes[len]!
      if code ≥ first && code - first < counts[len]! then
        let s := sortedSymbols[start + (code - first)]!
        if s == 256 then return none
        out := out.push s.toUInt8
        code := 0
        len := 0
  if len > 7 || code != 2 ^ len - 1 then return none
  return some out

end Huffman

end LeanHttpx
