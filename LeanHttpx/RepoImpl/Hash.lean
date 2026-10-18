/-!
# Message digests for Digest authentication

MD5 (RFC 1321), SHA-1 (RFC 3174), SHA-256 and SHA-512 (FIPS 180-4), the
four hash families `httpx.DigestAuth` supports, with the hex output
`hashlib.<name>(data).hexdigest()` gives. They are trusted code: tested
against the standard vectors (`tests/Conformance.lean`), not proved; a proof
of a hash function is out of scope here.

Every loop is a `for` over a range (a bounded loop), so the stack is flat.
-/

namespace LeanHttpx

namespace Hash

/-- Lower-case hex of bytes. -/
def hex (b : ByteArray) : String :=
  let d (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  b.foldl (fun s x => (s.push (d (x.toNat / 16))).push (d (x.toNat % 16))) ""

/-- Pad a message to a multiple of `blockBytes`: `0x80`, zeros, then the bit
length in `lenBytes` bytes, big-endian or little-endian. -/
def pad (msg : ByteArray) (blockBytes lenBytes : Nat) (bigEndian : Bool) : ByteArray := Id.run do
  let bitLen := msg.size * 8
  let mut out := msg.push 0x80
  let zeros := (2 * blockBytes - lenBytes - out.size % blockBytes) % blockBytes
  for _ in [0:zeros] do
    out := out.push 0
  for i in [0:lenBytes] do
    let shift := if bigEndian then 8 * (lenBytes - 1 - i) else 8 * i
    out := out.push (bitLen >>> shift).toUInt8
  return out

/-- A 32-bit word from 4 bytes. -/
@[inline] def word32BE (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 <<< 24 ||| (b.get! (i+1)).toUInt32 <<< 16 ||| (b.get! (i+2)).toUInt32 <<< 8 |||
    (b.get! (i+3)).toUInt32

@[inline] def word32LE (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 ||| (b.get! (i+1)).toUInt32 <<< 8 ||| (b.get! (i+2)).toUInt32 <<< 16 |||
    (b.get! (i+3)).toUInt32 <<< 24

@[inline] def word64BE (b : ByteArray) (i : Nat) : UInt64 := Id.run do
  let mut w : UInt64 := 0
  for k in [0:8] do
    w := (w <<< 8) ||| (b.get! (i + k)).toUInt64
  return w

@[inline] def rotl32 (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))
@[inline] def rotr32 (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
@[inline] def rotr64 (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

def be32 (w : UInt32) : List UInt8 := [(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]
def le32 (w : UInt32) : List UInt8 := [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]
def be64 (w : UInt64) : List UInt8 := (List.range 8).map fun k => (w >>> (8 * (7 - k).toUInt64)).toUInt8

/-! ## MD5 -/

def md5S : Array UInt32 := #[7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

def md5K : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

/-- MD5 (RFC 1321). -/
def md5 (msg : ByteArray) : ByteArray := Id.run do
  let m := pad msg 64 8 false
  let mut a0 : UInt32 := 0x67452301
  let mut b0 : UInt32 := 0xefcdab89
  let mut c0 : UInt32 := 0x98badcfe
  let mut d0 : UInt32 := 0x10325476
  for blk in [0:m.size / 64] do
    let base := blk * 64
    let mut a := a0
    let mut b := b0
    let mut c := c0
    let mut d := d0
    for i in [0:64] do
      let (f, g) :=
        if i < 16 then ((b &&& c) ||| (~~~b &&& d), i)
        else if i < 32 then ((d &&& b) ||| (~~~d &&& c), (5 * i + 1) % 16)
        else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
        else (c ^^^ (b ||| ~~~d), (7 * i) % 16)
      let f := f + a + md5K[i]! + word32LE m (base + 4 * g)
      a := d
      d := c
      c := b
      b := b + rotl32 f md5S[i]!
    a0 := a0 + a
    b0 := b0 + b
    c0 := c0 + c
    d0 := d0 + d
  return ⟨(le32 a0 ++ le32 b0 ++ le32 c0 ++ le32 d0).toArray⟩

/-! ## SHA-1 -/

/-- SHA-1 (RFC 3174). -/
def sha1 (msg : ByteArray) : ByteArray := Id.run do
  let m := pad msg 64 8 true
  let mut h0 : UInt32 := 0x67452301
  let mut h1 : UInt32 := 0xEFCDAB89
  let mut h2 : UInt32 := 0x98BADCFE
  let mut h3 : UInt32 := 0x10325476
  let mut h4 : UInt32 := 0xC3D2E1F0
  for blk in [0:m.size / 64] do
    let base := blk * 64
    let mut w : Array UInt32 := Array.replicate 80 0
    for t in [0:16] do
      w := w.set! t (word32BE m (base + 4 * t))
    for t in [16:80] do
      w := w.set! t (rotl32 (w[t-3]! ^^^ w[t-8]! ^^^ w[t-14]! ^^^ w[t-16]!) 1)
    let mut a := h0
    let mut b := h1
    let mut c := h2
    let mut d := h3
    let mut e := h4
    for t in [0:80] do
      let (f, k) :=
        if t < 20 then ((b &&& c) ||| (~~~b &&& d), (0x5A827999 : UInt32))
        else if t < 40 then (b ^^^ c ^^^ d, 0x6ED9EBA1)
        else if t < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8F1BBCDC)
        else (b ^^^ c ^^^ d, 0xCA62C1D6)
      let temp := rotl32 a 5 + f + e + k + w[t]!
      e := d
      d := c
      c := rotl32 b 30
      b := a
      a := temp
    h0 := h0 + a
    h1 := h1 + b
    h2 := h2 + c
    h3 := h3 + d
    h4 := h4 + e
  return ⟨(be32 h0 ++ be32 h1 ++ be32 h2 ++ be32 h3 ++ be32 h4).toArray⟩

/-! ## SHA-256 -/

def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- SHA-256 (FIPS 180-4). -/
def sha256 (msg : ByteArray) : ByteArray := Id.run do
  let m := pad msg 64 8 true
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for blk in [0:m.size / 64] do
    let base := blk * 64
    let mut w : Array UInt32 := Array.replicate 64 0
    for t in [0:16] do
      w := w.set! t (word32BE m (base + 4 * t))
    for t in [16:64] do
      let s0 := rotr32 w[t-15]! 7 ^^^ rotr32 w[t-15]! 18 ^^^ (w[t-15]! >>> 3)
      let s1 := rotr32 w[t-2]! 17 ^^^ rotr32 w[t-2]! 19 ^^^ (w[t-2]! >>> 10)
      w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
    let mut v := h
    for t in [0:64] do
      let a := v[0]!; let b := v[1]!; let c := v[2]!; let d := v[3]!
      let e := v[4]!; let f := v[5]!; let g := v[6]!; let hh := v[7]!
      let S1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
      let ch := (e &&& f) ^^^ (~~~e &&& g)
      let t1 := hh + S1 + ch + sha256K[t]! + w[t]!
      let S0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := S0 + maj
      v := #[t1 + t2, a, b, c, d + t1, e, f, g]
    h := (h.zip v).map fun (x, y) => x + y
  return ⟨(h.toList.flatMap be32).toArray⟩

/-! ## SHA-512 -/

def sha512K : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc, 0x3956c25bf348b538,
  0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118, 0xd807aa98a3030242, 0x12835b0145706fbe,
  0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2, 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235,
  0xc19bf174cf692694, 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5, 0x983e5152ee66dfab,
  0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725,
  0x06ca6351e003826f, 0x142929670a0e6e70, 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed,
  0x53380d139d95b3df, 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218,
  0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8, 0x19a4c116b8d2d0c8, 0x1e376c085141ab53,
  0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373,
  0x682e6ff3d6b2b8a3, 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b, 0xca273eceea26619c,
  0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x06f067aa72176fba, 0x0a637dc5a2c898a6,
  0x113f9804bef90dae, 0x1b710b35131c471b, 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc,
  0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- SHA-512 (FIPS 180-4). -/
def sha512 (msg : ByteArray) : ByteArray := Id.run do
  let m := pad msg 128 16 true
  let mut h : Array UInt64 := #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]
  for blk in [0:m.size / 128] do
    let base := blk * 128
    let mut w : Array UInt64 := Array.replicate 80 0
    for t in [0:16] do
      w := w.set! t (word64BE m (base + 8 * t))
    for t in [16:80] do
      let s0 := rotr64 w[t-15]! 1 ^^^ rotr64 w[t-15]! 8 ^^^ (w[t-15]! >>> 7)
      let s1 := rotr64 w[t-2]! 19 ^^^ rotr64 w[t-2]! 61 ^^^ (w[t-2]! >>> 6)
      w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
    let mut v := h
    for t in [0:80] do
      let a := v[0]!; let b := v[1]!; let c := v[2]!; let d := v[3]!
      let e := v[4]!; let f := v[5]!; let g := v[6]!; let hh := v[7]!
      let S1 := rotr64 e 14 ^^^ rotr64 e 18 ^^^ rotr64 e 41
      let ch := (e &&& f) ^^^ (~~~e &&& g)
      let t1 := hh + S1 + ch + sha512K[t]! + w[t]!
      let S0 := rotr64 a 28 ^^^ rotr64 a 34 ^^^ rotr64 a 39
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := S0 + maj
      v := #[t1 + t2, a, b, c, d + t1, e, f, g]
    h := (h.zip v).map fun (x, y) => x + y
  return ⟨(h.toList.flatMap be64).toArray⟩

end Hash

end LeanHttpx
