import Keel.Codec

/-!
# Reading fixed fields from a `ByteArray`

A binary payload (an HTTP/2 frame, an HPACK block) is read with a cursor: a
position in the buffer, advanced by each read. `Cursor ε α` is `StateT Nat
(Except ε)`, and the reads are `u8`, `be w` (a `w`-byte big-endian number,
`Keel.Codec.beValue`) and `slice n` (a copy of `n` bytes, one
`ByteArray.extract`, not a byte at a time).

Each read has a lemma saying what it returns on a buffer built the way the
printer builds it, `pre ++ (field ++ post)` at position `pre.size`; a
round-trip proof is then a chain of these.
-/

namespace LeanHttpx

namespace Bytes

open Keel.Codec

/-- A read from a buffer: from a position, a value and the next position. -/
abbrev Cursor (ε α : Type) := StateT Nat (Except ε) α

variable {ε : Type}

/-- One byte. -/
def u8 (b : ByteArray) (e : ε) : Cursor ε Nat := fun i =>
  if h : i < b.size then .ok (b[i].toNat, i + 1) else .error e

/-- A `w`-byte big-endian number. -/
def be (b : ByteArray) (w : Nat) (e : ε) : Cursor ε Nat := fun i =>
  if i + w ≤ b.size then .ok (beValue (b.extract i (i + w)).data.toList, i + w) else .error e

/-- `n` bytes, copied as one slice. -/
def slice (b : ByteArray) (n : Nat) (e : ε) : Cursor ε ByteArray := fun i =>
  if i + n ≤ b.size then .ok (b.extract i (i + n), i + n) else .error e

/-- The current position. -/
def pos : Cursor ε Nat := fun i => .ok (i, i)

/-- The bytes of a big-endian number. -/
def beArr (w n : Nat) : ByteArray := (beBytes w n).toByteArray

@[simp] theorem size_beArr (w n : Nat) : (beArr w n).size = w := by
  simp [beArr, length_beBytes]

theorem extract_mid (pre x post : ByteArray) :
    (pre ++ (x ++ post)).extract pre.size (pre.size + x.size) = x := by
  have h1 := ByteArray.extract_append_size_add (a := pre) (b := x ++ post) (i := 0) (j := x.size)
  rw [Nat.add_zero] at h1
  rw [h1]
  exact ByteArray.extract_append_eq_left rfl

theorem size_mid (pre x post : ByteArray) : pre.size + x.size ≤ (pre ++ (x ++ post)).size := by
  simp [ByteArray.size_append]

@[simp] theorem slice_mid (pre x post : ByteArray) (e : ε) :
    slice (pre ++ (x ++ post)) x.size e pre.size = .ok (x, pre.size + x.size) := by
  simp [slice, extract_mid]

theorem slice_mid' (pre x post : ByteArray) (n : Nat) (h : n = x.size) (e : ε) :
    slice (pre ++ (x ++ post)) n e pre.size = .ok (x, pre.size + n) := by
  subst h; exact slice_mid pre x post e

theorem toList_beArr (w n : Nat) : (beArr w n).data.toList = beBytes w n := by
  simp [beArr]

@[simp] theorem be_mid (pre post : ByteArray) (w n : Nat) (h : n < 256 ^ w) (e : ε) :
    be (pre ++ (beArr w n ++ post)) w e pre.size = .ok (n, pre.size + w) := by
  have hs := size_mid pre (beArr w n) post
  simp only [size_beArr] at hs
  have hx := extract_mid pre (beArr w n) post
  simp only [size_beArr] at hx
  simp [be, hx, toList_beArr, beValue_beBytes w n h]

@[simp] theorem u8_mid (pre post : ByteArray) (n : Nat) (h : n < 256) (e : ε) :
    u8 (pre ++ (beArr 1 n ++ post)) e pre.size = .ok (n, pre.size + 1) := by
  have hs := size_mid pre (beArr 1 n) post
  simp only [size_beArr] at hs
  have hl : pre.size < (pre ++ (beArr 1 n ++ post)).size := by omega
  simp only [u8, hl, dite_true, Except.ok.injEq, Prod.mk.injEq, and_true]
  rw [ByteArray.getElem_append_right (by omega)]
  simp only [Nat.sub_self]
  rw [ByteArray.getElem_append_left (by simp)]
  simp [beArr, beBytes, Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt h]

/-! ## Splitting a buffer

The other way to read a payload: split off a field and continue with the
rest. Each split copies the rest once, so it suits short headers in front of
a body. -/

/-- A `w`-byte big-endian number, and the bytes after it. -/
def takeBE (w : Nat) (b : ByteArray) : Option (Nat × ByteArray) :=
  if w ≤ b.size then some (beValue (b.extract 0 w).data.toList, b.extract w b.size) else none

/-- The first `n` bytes, and the bytes after them. -/
def takeN (n : Nat) (b : ByteArray) : Option (ByteArray × ByteArray) :=
  if n ≤ b.size then some (b.extract 0 n, b.extract n b.size) else none

theorem extract_size_append (x r : ByteArray) : (x ++ r).extract x.size (x.size + r.size) = r := by
  have := ByteArray.extract_append_size_add (a := x) (b := r) (i := 0) (j := r.size)
  simp only [Nat.add_zero] at this
  rw [this, ByteArray.extract_zero_size]

@[simp] theorem takeN_append (x r : ByteArray) : takeN x.size (x ++ r) = some (x, r) := by
  simp [takeN, ByteArray.size_append, ByteArray.extract_append_eq_left, extract_size_append]

theorem takeN_append' (x r : ByteArray) (n : Nat) (h : n = x.size) : takeN n (x ++ r) = some (x, r) := by
  subst h; exact takeN_append x r

@[simp] theorem takeBE_beArr (w n : Nat) (h : n < 256 ^ w) (r : ByteArray) :
    takeBE w (beArr w n ++ r) = some (n, r) := by
  have h1 := takeN_append (beArr w n) r
  simp only [takeN, size_beArr, ByteArray.size_append] at h1
  simp only [takeBE, ByteArray.size_append, size_beArr]
  split at h1
  · rename_i hw
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    simp [hw, h1.1, h1.2, toList_beArr, beValue_beBytes w n h]
  · cases h1

/-- Zero bytes of padding. -/
def zeros (n : Nat) : ByteArray := (List.replicate n (0 : UInt8)).toByteArray

@[simp] theorem size_zeros (n : Nat) : (zeros n).size = n := by simp [zeros]

end Bytes

end LeanHttpx
