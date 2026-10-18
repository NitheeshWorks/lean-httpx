/-!
# Content decoders (`httpx/_decoders.py`)

`Content-Encoding: gzip` and `deflate` bodies are decoded when a response
is read, as httpx's `GZipDecoder` and `DeflateDecoder` do. Inflate is
RFC 1951 (in the style of zlib's `puff`), gzip is RFC 1952 and the zlib
wrapper RFC 1950. `deflate` tries the zlib wrapper first and falls back to
raw deflate, as upstream does. Brotli and zstd are not supported (upstream
offers them only when optional packages are installed).

Every loop is a `for` over a range bounded by the input size: each step
consumes at least one bit, so the decoder runs in constant stack and
always stops.
-/

namespace LeanHttpx

namespace Decoders

/-- Bit reader state: byte position, bit buffer, bits in the buffer. -/
structure Bits where
  pos : Nat := 0
  buf : Nat := 0
  cnt : Nat := 0

/-- Read `n ≤ 16` bits, least significant first. -/
def getBits (data : ByteArray) (s : Bits) (n : Nat) : Option (Nat × Bits) := Id.run do
  let mut s := s
  for _ in [0:3] do
    if s.cnt < n then
      if s.pos ≥ data.size then return none
      s := { pos := s.pos + 1, buf := s.buf ||| ((data.get! s.pos).toNat <<< s.cnt), cnt := s.cnt + 8 }
  if s.cnt < n then return none
  return some (s.buf % (2 ^ n), { s with buf := s.buf >>> n, cnt := s.cnt - n })

/-- A canonical Huffman code: the number of codes of each length, and the
symbols in code order. -/
structure Huffman where
  count : Array Nat
  symbol : Array Nat

/-- Build a canonical code from code lengths. -/
def Huffman.build (lengths : Array Nat) : Huffman := Id.run do
  let mut count := Array.replicate 16 0
  for l in lengths do
    count := count.modify l (· + 1)
  let mut offs := Array.replicate 16 0
  for len in [1:15] do
    offs := offs.set! (len + 1) (offs[len]! + count[len]!)
  let mut symbol := Array.replicate lengths.size 0
  for sym in [0:lengths.size] do
    let l := lengths[sym]!
    if l != 0 then
      symbol := symbol.set! offs[l]! sym
      offs := offs.modify l (· + 1)
  return { count := count.set! 0 0, symbol }

/-- Decode one symbol. -/
def decodeSym (data : ByteArray) (h : Huffman) (s : Bits) : Option (Nat × Bits) := Id.run do
  let mut s := s
  let mut code := 0
  let mut first := 0
  let mut index := 0
  for len in [1:16] do
    match getBits data s 1 with
    | none => return none
    | some (b, s') =>
      s := s'
      code := code ||| b
      let count := h.count[len]!
      if code < first + count then return some (h.symbol[index + (code - first)]!, s)
      index := index + count
      first := (first + count) * 2
      code := code * 2
  return none

def lenBase : Array Nat := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
  67, 83, 99, 115, 131, 163, 195, 227, 258]
def lenExtra : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]
def distBase : Array Nat := #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769,
  1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]
def distExtra : Array Nat := #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
  11, 11, 12, 12, 13, 13]

/-- Decode the symbols of a compressed block into `out`. -/
def codes (data : ByteArray) (lit dist : Huffman) (s : Bits) (out : ByteArray) :
    Except String (Bits × ByteArray) := Id.run do
  let mut s := s
  let mut out := out
  for _ in [0:8 * data.size + 1] do
    let some (sym, s1) := decodeSym data lit s | return .error "invalid literal/length code"
    s := s1
    if sym < 256 then out := out.push sym.toUInt8
    else if sym == 256 then return .ok (s, out)
    else
      let sym := sym - 257
      if sym ≥ 29 then return .error "invalid literal/length code"
      let some (e, s2) := getBits data s lenExtra[sym]! | return .error "truncated"
      s := s2
      let len := lenBase[sym]! + e
      let some (dsym, s3) := decodeSym data dist s | return .error "invalid distance code"
      s := s3
      if dsym ≥ 30 then return .error "invalid distance code"
      let some (de, s4) := getBits data s distExtra[dsym]! | return .error "truncated"
      s := s4
      let d := distBase[dsym]! + de
      if d > out.size then return .error "invalid distance too far back"
      for _ in [0:len] do
        out := out.push (out.get! (out.size - d))
  return .error "truncated"

def fixedLit : Huffman := Huffman.build
  ((Array.replicate 144 8) ++ (Array.replicate 112 9) ++ (Array.replicate 24 7) ++ (Array.replicate 8 8))
def fixedDist : Huffman := Huffman.build (Array.replicate 30 5)

def clOrder : Array Nat := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Read the code tables of a dynamic block. -/
def dynamicTables (data : ByteArray) (s : Bits) : Except String (Huffman × Huffman × Bits) := Id.run do
  let some (nlen, s) := getBits data s 5 | return .error "truncated"
  let some (ndist, s) := getBits data s 5 | return .error "truncated"
  let some (ncode, s) := getBits data s 4 | return .error "truncated"
  let nlen := nlen + 257
  let ndist := ndist + 1
  let ncode := ncode + 4
  if nlen > 286 || ndist > 30 then return .error "bad counts"
  let mut s := s
  let mut cl := Array.replicate 19 0
  for i in [0:ncode] do
    let some (v, s') := getBits data s 3 | return .error "truncated"
    s := s'
    cl := cl.set! clOrder[i]! v
  let clCode := Huffman.build cl
  let mut lengths : Array Nat := #[]
  for _ in [0:nlen + ndist] do
    if lengths.size ≥ nlen + ndist then break
    let some (sym, s') := decodeSym data clCode s | return .error "invalid code lengths"
    s := s'
    if sym < 16 then lengths := lengths.push sym
    else
      let (rep, val, s'') ← match sym with
        | 16 =>
          if lengths.isEmpty then return .error "repeat with no first length"
          match getBits data s 2 with
          | some (r, s2) => pure (3 + r, lengths.back!, s2)
          | none => return .error "truncated"
        | 17 => match getBits data s 3 with
          | some (r, s2) => pure (3 + r, 0, s2)
          | none => return .error "truncated"
        | _ => match getBits data s 7 with
          | some (r, s2) => pure (11 + r, 0, s2)
          | none => return .error "truncated"
      s := s''
      if lengths.size + rep > nlen + ndist then return .error "too many lengths"
      for _ in [0:rep] do lengths := lengths.push val
  return .ok (Huffman.build (lengths.extract 0 nlen), Huffman.build (lengths.extract nlen (nlen + ndist)), s)

/-- Inflate raw deflate data (RFC 1951), from byte `start`: the output and
the position after the last block. -/
def inflateFrom (data : ByteArray) (start : Nat) : Except String (ByteArray × Nat) := Id.run do
  let mut s : Bits := { pos := start }
  let mut out := ByteArray.empty
  for _ in [0:data.size + 1] do
    let some (final, s1) := getBits data s 1 | return .error "truncated"
    let some (typ, s2) := getBits data s1 2 | return .error "truncated"
    s := s2
    match typ with
    | 0 =>
      -- Stored: skip to a byte boundary, then LEN and its complement.
      let p := s.pos
      if p + 4 > data.size then return .error "truncated"
      let len := (data.get! p).toNat + (data.get! (p + 1)).toNat * 256
      let nlen := (data.get! (p + 2)).toNat + (data.get! (p + 3)).toNat * 256
      if len != 65535 - nlen then return .error "invalid stored block lengths"
      if p + 4 + len > data.size then return .error "truncated"
      out := out ++ data.extract (p + 4) (p + 4 + len)
      s := { pos := p + 4 + len }
    | 1 =>
      match codes data fixedLit fixedDist s out with
      | .ok (s', o) => s := s'; out := o
      | .error e => return .error e
    | 2 =>
      match dynamicTables data s with
      | .ok (lit, dist, s') =>
        match codes data lit dist s' out with
        | .ok (s'', o) => s := s''; out := o
        | .error e => return .error e
      | .error e => return .error e
    | _ => return .error "invalid block type"
    if final == 1 then return .ok (out, s.pos)
  return .error "truncated"

/-- CRC-32 (ISO 3309), as gzip checks it. -/
def crc32 (data : ByteArray) : UInt32 := Id.run do
  let mut c : UInt32 := 0xFFFFFFFF
  for b in data do
    c := c ^^^ b.toUInt32
    for _ in [0:8] do
      c := if c &&& 1 == 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1
  return c ^^^ 0xFFFFFFFF

/-- Decode a gzip member (RFC 1952). -/
def gunzip (data : ByteArray) : Except String ByteArray := do
  if data.size < 18 || data.get! 0 != 0x1f || data.get! 1 != 0x8b then throw "incorrect header check"
  if data.get! 2 != 8 then throw "unknown compression method"
  let flg := data.get! 3
  let mut p := 10
  if flg &&& 4 != 0 then
    let xlen := (data.get! p).toNat + (data.get! (p + 1)).toNat * 256
    p := p + 2 + xlen
  for flag in [8, 16] do
    if flg &&& flag.toUInt8 != 0 then
      let rest := data.extract p data.size
      match rest.data.findIdx? (· == 0) with
      | some i => p := p + i + 1
      | none => throw "truncated header"
  if flg &&& 2 != 0 then p := p + 2
  let (out, q) ← inflateFrom data p
  if q + 8 > data.size then throw "truncated"
  let crc := (List.range 4).foldl (fun acc k => acc ||| ((data.get! (q + k)).toUInt32 <<< (8 * k).toUInt32)) 0
  if crc != crc32 out then throw "incorrect data check"
  pure out

/-- Decode a zlib stream (RFC 1950). -/
def unzlib (data : ByteArray) : Except String ByteArray := do
  if data.size < 2 then throw "incomplete or truncated stream"
  let cmf := (data.get! 0).toNat
  let flg := (data.get! 1).toNat
  if cmf % 16 != 8 || (cmf * 256 + flg) % 31 != 0 then throw "incorrect header check"
  if flg &&& 32 != 0 then throw "need dictionary"
  let (out, _) ← inflateFrom data 2
  pure out

/-- Decode one content coding (`SUPPORTED_DECODERS`); unknown codings pass
the bytes through, as httpx's `IdentityDecoder` does for them. -/
def decodeOne (coding : String) (data : ByteArray) : Except String ByteArray :=
  match coding with
  | "gzip" => gunzip data
  | "deflate" => match unzlib data with
    | .ok out => .ok out
    | .error _ => (inflateFrom data 0).map (·.1)
  | _ => .ok data

/-- Decode a body by its `Content-Encoding` values, the last applied coding
first (`MultiDecoder`). -/
def decodeContent (codings : List String) (data : ByteArray) : Except String ByteArray :=
  if data.isEmpty then .ok data else
  codings.reverse.foldlM (fun d c => decodeOne c d) data

end Decoders

end LeanHttpx
