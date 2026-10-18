import Keel.Codec

/-!
# Codec pieces this library adds to `Keel.Codec`

Three general combinators the HTTP codecs need and `Keel.Codec` does not have
yet, each lawful by construction (the law is the structure field):

* `Codec.guard c P`: the values of `c` satisfying a decidable `P`, at the same
  type (`Codec.refine` moves `P` into a subtype instead).
* `Codec.fail`: the codec of no values, for a framing that is invalid.
* `Codec.bytesN n`: exactly `n` bytes, decoded straight into a `ByteArray` by
  `takeBytes`, a primitive that copies in a loop. Building a list of tokens
  for a body of megabytes, or recursing once per byte as `Parser.take` does,
  is what this avoids.

They are candidates for `Keel.Codec`; until then they live here.
-/

namespace LeanHttpx

open Keel Keel.Parser

/-! ## Reading `n` bytes into a `ByteArray` -/

/-- The bytes `f 0, …, f (n-1)`. -/
def buildBytes (f : Nat → UInt8) (n : Nat) : ByteArray := ⟨Array.ofFn (n := n) fun k => f k.val⟩

theorem buildBytes_toList (l : List UInt8) (n : Nat) (h : n ≤ l.length) :
    (buildBytes (fun k => (l[k]?).getD 0) n).data.toList = l.take n := by
  simp only [buildBytes, Array.toList_ofFn]
  apply List.ext_getElem <;> simp [h]
  intro i h1 _
  simp [List.getElem?_eq_getElem (by omega : i < l.length)]

/-- Read exactly `n` bytes, as a `ByteArray`; `eof` if fewer are left. -/
def takeBytes {ε : Type} [ParseError ε] (n : Nat) : Parser UInt8 ε ByteArray where
  run s i :=
    if Input.size s - i < n then .error ParseError.eof i
    else .ok (buildBytes (fun k => (Input.get? s (i + k)).getD 0) n) (i + n)
  run_eq s i := by
    have hL : Input.size (Input.rest s i) - 0 = Input.size s - i := by
      rw [Input.size_list, Input.length_rest, Nat.sub_zero]
    have hf : (fun k => (Input.get? (Input.rest s i) (0 + k)).getD 0) =
        (fun k => (Input.get? s (i + k)).getD 0) := by
      funext k; rw [Nat.zero_add, Input.get?_list, Input.get?_rest]
    show (if _ then _ else _) = Result.shift i (if _ then _ else _)
    rw [hL, hf]
    by_cases h : Input.size s - i < n
    · simp [h]
    · simp [h, Nat.add_comm]
  pos_le l := by
    show Result.pos (if _ then _ else _) ≤ _
    by_cases h : Input.size l - 0 < n
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp only [Input.size_list, Nat.sub_zero] at h; simp; omega

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by
  rw [Array.length_toList]; rfl

theorem parse_takeBytes {ε : Type} [ParseError ε] (b : ByteArray) (r : List UInt8) :
    (takeBytes b.size : Parser UInt8 ε ByteArray).parse (b.data.toList ++ r) = .ok b r := by
  have hn := size_eq_length b
  have hlen : b.size ≤ (b.data.toList ++ r).length := by rw [List.length_append]; omega
  show ((takeBytes b.size).run (b.data.toList ++ r) 0).toReply _ = _
  simp only [takeBytes, Input.size_list, Nat.sub_zero, Nat.zero_add, Input.get?_list]
  rw [if_neg (by omega)]
  simp only [Result.toReply_ok]
  have hb : buildBytes (fun k => ((b.data.toList ++ r)[k]?).getD 0) b.size = b := by
    have := buildBytes_toList (b.data.toList ++ r) b.size hlen
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at this
    obtain ⟨d⟩ := b
    generalize buildBytes _ _ = x at this
    obtain ⟨d'⟩ := x
    congr 1; exact Array.ext' this
  rw [hb, List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]

/-! The combinators extend `Keel.Codec`, so they read as `c.guard P`. -/

end LeanHttpx

namespace Keel.Codec

open LeanHttpx

variable {τ α : Type}

/-- **Guard**: the values of `c` that satisfy `P`. The decoder checks `P`
and fails with `unexpected` otherwise. -/
def guard (c : Codec τ α) (P : α → Prop) [DecidablePred P] : Codec τ α where
  encode := c.encode
  parser := do
    let a ← c.parser
    if P a then pure a else Parser.fail ParseError.unexpected
  valid a := c.valid a ∧ P a
  follow := c.follow
  parse_encode a r hv hf := by simp [c.parse_encode a r hv.1 hf, hv.2]

/-- The codec of no values. -/
def fail : Codec τ α where
  encode _ := []
  parser := Parser.fail ParseError.unexpected
  valid _ := False
  follow _ := True
  parse_encode _ _ hv _ := hv.elim

/-- Exactly `n` bytes, as a `ByteArray`. -/
def bytesN (n : Nat) : Codec UInt8 ByteArray where
  encode b := b.data.toList
  parser := takeBytes n
  valid b := b.size = n
  follow _ := True
  parse_encode b r hv _ := by subst hv; exact parse_takeBytes b r

@[simp] theorem guard_encode (c : Codec τ α) (P : α → Prop) [DecidablePred P] (a : α) :
    (c.guard P).encode a = c.encode a := rfl
@[simp] theorem guard_valid (c : Codec τ α) (P : α → Prop) [DecidablePred P] (a : α) :
    (c.guard P).valid a ↔ c.valid a ∧ P a := Iff.rfl
@[simp] theorem guard_follow (c : Codec τ α) (P : α → Prop) [DecidablePred P] (r : List τ) :
    (c.guard P).follow r ↔ c.follow r := Iff.rfl
@[simp] theorem bytesN_encode (n : Nat) (b : ByteArray) : (bytesN n).encode b = b.data.toList := rfl
@[simp] theorem bytesN_valid (n : Nat) (b : ByteArray) : (bytesN n).valid b ↔ b.size = n := Iff.rfl
@[simp] theorem bytesN_follow (n : Nat) (r : List UInt8) : (bytesN n).follow r := trivial

end Keel.Codec
