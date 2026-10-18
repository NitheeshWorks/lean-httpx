import LeanHttpx.RepoImpl.Hpack

/-!
# HPACK: decoding what was encoded

Wire layer: `readReps_encodeReps`, the representations of a block read back
from its bytes. Table layer: `applyAll_chooseAll`, the decoder applying the
representations the encoder chose yields the fields, and leaves its table
equal to the encoder's. Together, `hpack_decode_encode` (with a dynamic
table, as a stateful round trip) and `hpack_decode_encode_static` (static
table and literals only).
-/

namespace LeanHttpx

namespace Hpack

open Bytes H2

/-! ## Reading from `pre ++ (x ++ post)` -/

theorem peek_mid (pre post : ByteArray) (n : Nat) (h : n < 256) :
    peek (pre ++ (beArr 1 n ++ post)) pre.size = .ok n := by
  have := u8_mid pre post n h (err "")
  unfold u8 at this
  unfold peek
  split at this
  · rename_i hl; simp only [hl, dite_true]; simp only [Except.ok.injEq, Prod.mk.injEq] at this; rw [this.1]
  · cases this

theorem assoc3 (pre x y post : ByteArray) : pre ++ (x ++ y ++ post) = (pre ++ x) ++ (y ++ post) := by
  simp [ByteArray.append_assoc]

theorem contBytes_eq (x : Nat) : contBytes x =
    if x < 128 then beArr 1 x else beArr 1 (x % 128 + 128) ++ contBytes (x / 128) := by
  rw [contBytes]

theorem size_contBytes_le (k x : Nat) (h : x < 2 ^ (7 * (k + 1))) : (contBytes x).size ≤ k + 1 := by
  induction k generalizing x with
  | zero => rw [contBytes_eq]; simp at h; simp [h]
  | succ k ih =>
    rw [contBytes_eq]
    split
    · simp
    · have : x / 128 < 2 ^ (7 * (k + 1)) := by
        rw [show 7 * (k + 1 + 1) = 7 * (k + 1) + 7 by omega, Nat.pow_add] at h; omega
      have := ih (x / 128) this
      simp [ByteArray.size_append]; omega

theorem readCont_contBytes (x : Nat) : ∀ (pre post : ByteArray) (fuel acc shift : Nat),
    (contBytes x).size ≤ fuel →
    readCont (pre ++ (contBytes x ++ post)) fuel acc shift pre.size =
      .ok (acc + x * 2 ^ shift, pre.size + (contBytes x).size) := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro pre post fuel acc shift hf
    by_cases hx : x < 128
    · rw [contBytes_eq, if_pos hx] at hf ⊢
      simp at hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp [readCont, u8_mid pre post x (by omega), bind, Except.bind, pure, Except.pure, show ¬ 128 ≤ x by omega]
    · rw [contBytes_eq, if_neg hx] at hf ⊢
      have hsz : (beArr 1 (x % 128 + 128) ++ contBytes (x / 128)).size = 1 + (contBytes (x / 128)).size := by
        simp [ByteArray.size_append]
      rw [hsz] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hlt : x % 128 + 128 < 256 := by omega
      rw [ByteArray.append_assoc]
      simp only [readCont, u8_mid pre _ _ hlt, bind, Except.bind]
      rw [if_pos (by omega)]
      have hf' : (contBytes (x / 128)).size ≤ f := by omega
      have := ih (x / 128) (by omega) (pre ++ beArr 1 (x % 128 + 128)) post f
        (acc + (x % 128 + 128 - 128) * 2 ^ shift) (shift + 7) hf'
      rw [ByteArray.append_assoc] at this
      simp only [ByteArray.size_append, size_beArr] at this
      rw [this]
      have e : acc + (x % 128 + 128 - 128) * 2 ^ shift + x / 128 * 2 ^ (shift + 7) = acc + x * 2 ^ shift := by
        rw [Nat.add_sub_cancel, Nat.pow_add, show (2 : Nat) ^ 7 = 128 by rfl]
        have h1 : x = x % 128 + 128 * (x / 128) := (Nat.mod_add_div x 128).symm
        have h2 : x * 2 ^ shift = (x % 128) * 2 ^ shift + (x / 128) * (2 ^ shift * 128) := by
          conv => lhs; rw [h1]
          rw [Nat.add_mul, Nat.mul_comm 128 (x / 128), Nat.mul_assoc, Nat.mul_comm 128]
        omega
      rw [e]
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
      omega

/-- The prefix and flag bits the representations use. -/
def PrefixOk (n flags : Nat) : Prop := 1 ≤ n ∧ n ≤ 7 ∧ flags % 2 ^ n = 0 ∧ flags + 2 ^ n ≤ 256

theorem mod_flags (n flags v : Nat) (hf : flags % 2 ^ n = 0) (hv : v < 2 ^ n) : (flags + v) % 2 ^ n = v := by
  rw [Nat.add_mod, hf, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hv]

theorem readInt_encodeInt (n flags v : Nat) (hp : PrefixOk n flags) (hv : v < 2 ^ 28) (pre post : ByteArray) :
    readInt (pre ++ (encodeInt n flags v ++ post)) n pre.size =
      .ok ((flags, v), pre.size + (encodeInt n flags v).size) := by
  obtain ⟨h1, h7, hf, h256⟩ := hp
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  unfold encodeInt
  by_cases hm : v < 2 ^ n - 1
  · rw [if_pos hm]
    have hx : flags + v < 256 := by omega
    simp only [readInt, u8_mid pre post _ hx, bind, Except.bind]
    rw [mod_flags n flags v hf (by omega), if_pos hm]
    simp [pure, Except.pure]
  · rw [if_neg hm]
    have hx : flags + (2 ^ n - 1) < 256 := by omega
    rw [ByteArray.append_assoc]
    simp only [readInt, u8_mid pre _ _ hx, bind, Except.bind]
    rw [mod_flags n flags _ hf (by omega), if_neg (by omega)]
    have hc : (contBytes (v - (2 ^ n - 1))).size ≤ maxContBytes := by
      have := size_contBytes_le 4 (v - (2 ^ n - 1)) (by
        have : (2 : Nat) ^ 28 ≤ 2 ^ (7 * (4 + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
        omega)
      simp [maxContBytes]; omega
    have := readCont_contBytes (v - (2 ^ n - 1)) (pre ++ beArr 1 (flags + (2 ^ n - 1))) post maxContBytes 0 0 hc
    rw [ByteArray.append_assoc] at this
    simp only [ByteArray.size_append, size_beArr] at this
    rw [this]
    simp [pure, Except.pure, ByteArray.size_append]
    omega

theorem readStr_encodeStr (s : ByteArray) (hs : s.size < 2 ^ 28) (pre post : ByteArray) :
    readStr (pre ++ (encodeStr s ++ post)) pre.size = .ok (s, pre.size + (encodeStr s).size) := by
  have hp : PrefixOk 7 0 := by unfold PrefixOk; decide
  unfold encodeStr
  rw [ByteArray.append_assoc]
  simp only [readStr, readInt_encodeInt 7 0 s.size hp hs, bind, Except.bind]
  have := slice_mid (pre ++ encodeInt 7 0 s.size) s post (err "String literal is longer than the block")
  rw [ByteArray.append_assoc] at this
  rw [ByteArray.size_append] at this
  rw [this]
  simp [pure, Except.pure, ByteArray.size_append]
  omega

theorem encodeInt_head (n flags v : Nat) : ∃ y rest, encodeInt n flags v = beArr 1 y ++ rest ∧
    flags ≤ y ∧ y < flags + 2 ^ n := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  unfold encodeInt
  split
  · exact ⟨flags + v, .empty, by rw [ByteArray.append_empty], by omega, by omega⟩
  · exact ⟨_, _, rfl, by omega, by omega⟩

theorem peek_encodeInt (n flags v : Nat) (h : flags + 2 ^ n ≤ 256) (pre post : ByteArray) :
    ∃ y, peek (pre ++ (encodeInt n flags v ++ post)) pre.size = .ok y ∧ flags ≤ y ∧ y < flags + 2 ^ n := by
  obtain ⟨y, rest, he, h1, h2⟩ := encodeInt_head n flags v
  refine ⟨y, ?_, h1, h2⟩
  rw [he, ByteArray.append_assoc]
  exact peek_mid pre _ y (by omega)

/-- A representation that prints and reads back: indices and lengths below
`2 ^ 28`, and a name index (as opposed to a literal name) of at least 1. -/
def Rep.ok : Rep → Prop
  | .indexed i => i < 2 ^ 28
  | .literal _ (.idx i) v => 1 ≤ i ∧ i < 2 ^ 28 ∧ v.size < 2 ^ 28
  | .literal _ (.lit n) v => n.size < 2 ^ 28 ∧ v.size < 2 ^ 28
  | .sizeUpdate n => n < 2 ^ 28

theorem prefix_ok (k : LitKind) : PrefixOk k.prefix.1 k.prefix.2 := by
  cases k <;> (unfold PrefixOk LitKind.prefix; decide)

theorem readLiteral_encode (k : LitKind) (nr : NameRef) (v : ByteArray) (h : (Rep.literal k nr v).ok)
    (pre post : ByteArray) :
    readLiteral (pre ++ (encodeRep (.literal k nr v) ++ post)) k pre.size =
      .ok (.literal k nr v, pre.size + (encodeRep (.literal k nr v)).size) := by
  cases nr with
  | idx i =>
    obtain ⟨h1, hi, hv⟩ := h
    simp only [encodeRep]
    rw [ByteArray.append_assoc]
    simp only [readLiteral, readInt_encodeInt _ _ i (prefix_ok k) hi, bind, Except.bind, pure, Except.pure]
    rw [if_neg (by simp; omega)]
    have := readStr_encodeStr v hv (pre ++ encodeInt k.prefix.1 k.prefix.2 i) post
    rw [ByteArray.append_assoc, ByteArray.size_append] at this
    simp only [this]
    simp [ByteArray.size_append]; omega
  | lit n =>
    obtain ⟨hn, hv⟩ := h
    simp only [encodeRep]
    rw [ByteArray.append_assoc]
    simp only [readLiteral, readInt_encodeInt _ _ 0 (prefix_ok k) (by omega), bind, Except.bind, pure, Except.pure]
    simp only [beq_self_eq_true, ite_true]
    have h1 := readStr_encodeStr n hn (pre ++ encodeInt k.prefix.1 k.prefix.2 0) (encodeStr v ++ post)
    rw [ByteArray.append_assoc, ByteArray.size_append] at h1
    rw [ByteArray.append_assoc]
    simp only [h1]
    have h2 := readStr_encodeStr v hv (pre ++ encodeInt k.prefix.1 k.prefix.2 0 ++ encodeStr n) post
    simp only [ByteArray.append_assoc, ByteArray.size_append, ← Nat.add_assoc] at h2
    simp only [h2]
    simp [ByteArray.size_append]; omega

theorem readRep_encodeRep (r : Rep) (h : r.ok) (pre post : ByteArray) :
    readRep (pre ++ (encodeRep r ++ post)) pre.size = .ok (r, pre.size + (encodeRep r).size) := by
  cases r with
  | indexed i =>
    obtain ⟨y, hy, h1, h2⟩ := peek_encodeInt 7 128 i (by decide) pre post
    have hp : PrefixOk 7 128 := by unfold PrefixOk; decide
    simp only [encodeRep] at hy ⊢
    simp only [readRep, hy, readInt_encodeInt 7 128 i hp h, bind, Except.bind, pure, Except.pure]
    simp [show 128 ≤ y by omega]
  | sizeUpdate n =>
    obtain ⟨y, hy, h1, h2⟩ := peek_encodeInt 5 32 n (by decide) pre post
    have hp : PrefixOk 5 32 := by unfold PrefixOk; decide
    simp only [encodeRep] at hy ⊢
    simp only [readRep, hy, readInt_encodeInt 5 32 n hp h, bind, Except.bind, pure, Except.pure]
    simp [show ¬ 128 ≤ y by omega, show ¬ 64 ≤ y by omega, show 32 ≤ y by omega]
  | literal k nr v =>
    have hfirst : ∃ y, peek (pre ++ (encodeRep (.literal k nr v) ++ post)) pre.size = .ok y ∧
        k.prefix.2 ≤ y ∧ y < k.prefix.2 + 2 ^ k.prefix.1 := by
      have hb : k.prefix.2 + 2 ^ k.prefix.1 ≤ 256 := (prefix_ok k).2.2.2
      cases nr with
      | idx i =>
        simp only [encodeRep]; rw [ByteArray.append_assoc]
        exact peek_encodeInt _ _ i hb pre _
      | lit n =>
        simp only [encodeRep]; rw [ByteArray.append_assoc]
        exact peek_encodeInt _ _ 0 hb pre _
    obtain ⟨y, hy, h1, h2⟩ := hfirst
    have hl := readLiteral_encode k nr v h pre post
    cases k <;> simp only [LitKind.prefix] at h1 h2 <;> simp only [readRep, hy, bind, Except.bind, pure, Except.pure]
    · simp [show ¬ 128 ≤ y by omega, show 64 ≤ y by omega, hl]
    · simp [show ¬ 128 ≤ y by omega, show ¬ 64 ≤ y by omega, show ¬ 32 ≤ y by omega,
        show ¬ 16 ≤ y by omega, hl]
    · simp [show ¬ 128 ≤ y by omega, show ¬ 64 ≤ y by omega, show ¬ 32 ≤ y by omega,
        show 16 ≤ y by omega, hl]

theorem size_encodeInt_pos (n flags v : Nat) : 1 ≤ (encodeInt n flags v).size := by
  obtain ⟨y, rest, he, -, -⟩ := encodeInt_head n flags v
  rw [he, ByteArray.size_append]; simp

theorem size_encodeRep_pos (r : Rep) : 1 ≤ (encodeRep r).size := by
  cases r with
  | indexed i => exact size_encodeInt_pos _ _ _
  | sizeUpdate n => exact size_encodeInt_pos _ _ _
  | literal k nr v =>
    cases nr with
    | idx i => have := size_encodeInt_pos k.prefix.1 k.prefix.2 i; simp only [encodeRep, ByteArray.size_append]; omega
    | lit n => have := size_encodeInt_pos k.prefix.1 k.prefix.2 0; simp only [encodeRep, ByteArray.size_append]; omega

theorem length_le_size (rs : List Rep) : rs.length ≤ (encodeReps rs).size := by
  induction rs with
  | nil => simp
  | cons r rs ih => have := size_encodeRep_pos r; simp [encodeReps, ByteArray.size_append]; omega

theorem readReps_encodeReps (rs : List Rep) (h : ∀ r ∈ rs, r.ok) :
    ∀ (pre : ByteArray) (fuel : Nat), rs.length ≤ fuel →
      readReps (pre ++ encodeReps rs) fuel pre.size = .ok rs := by
  induction rs with
  | nil =>
    intro pre fuel _
    cases fuel <;> simp [readReps, encodeReps, ByteArray.append_empty]
  | cons r rs ih =>
    intro pre fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hr := readRep_encodeRep r (h r (by simp)) pre (encodeReps rs)
    have hpos := size_encodeRep_pos r
    have hlt : ¬ pre.size ≥ (pre ++ encodeReps (r :: rs)).size := by
      simp [encodeReps, ByteArray.size_append]; omega
    simp only [readReps, encodeReps] at hlt ⊢
    simp only [hlt, ↓reduceIte, hr, bind, Except.bind, pure, Except.pure]
    rw [if_neg (by omega)]
    have := ih (fun x hx => h x (by simp [hx])) (pre ++ encodeRep r) f (by simp at hf; omega)
    rw [ByteArray.append_assoc, ByteArray.size_append] at this
    simp [this]

theorem decodeReps_encodeReps (rs : List Rep) (h : ∀ r ∈ rs, r.ok) : decodeReps (encodeReps rs) = .ok rs := by
  have := readReps_encodeReps rs h .empty (encodeReps rs).size (length_le_size rs)
  rwa [ByteArray.empty_append] at this

/-! ## The tables -/

theorem length_staticTable : staticTable.length = staticSize := by
  simp [staticTable, staticEntries, staticSize]

theorem findIdx_get {α : Type} {l : List α} {p : α → Bool} {j : Nat} (h : l.findIdx? p = some j) :
    ∃ x, l[j]? = some x ∧ p x = true ∧ j < l.length := by
  obtain ⟨hj, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨l[j], by simp [hj], hp, hj⟩

theorem findField_get (t : Table) (f : Field) (i : Nat) (h : t.findField f = some i) :
    t.get i = some f ∧ i ≤ staticSize + t.entries.length := by
  unfold Table.findField at h
  split at h
  · rename_i j hj
    obtain ⟨x, hx, hp, hl⟩ := findIdx_get hj
    simp at hp h; subst hp; subst h
    rw [length_staticTable] at hl
    refine ⟨?_, by omega⟩
    simp [Table.get, show j + 1 ≤ staticSize by omega, hx]
  · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨x, hx, hp, hl⟩ := findIdx_get hj
    simp at hp; subst hp
    refine ⟨?_, by omega⟩
    simp [Table.get, show ¬ j + staticSize + 1 ≤ staticSize by omega, hx, show j + staticSize + 1 - staticSize - 1 = j by omega]

theorem findName_get (t : Table) (n : ByteArray) (i : Nat) (h : t.findName n = some i) :
    (∃ v, t.get i = some (n, v)) ∧ 1 ≤ i ∧ i ≤ staticSize + t.entries.length := by
  unfold Table.findName at h
  split at h
  · rename_i j hj
    obtain ⟨x, hx, hp, hl⟩ := findIdx_get hj
    simp at hp h; subst h
    rw [length_staticTable] at hl
    refine ⟨⟨x.2, ?_⟩, by omega, by omega⟩
    simp [Table.get, show j + 1 ≤ staticSize by omega, hx, ← hp]
  · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨x, hx, hp, hl⟩ := findIdx_get hj
    simp at hp
    refine ⟨⟨x.2, ?_⟩, by omega, by omega⟩
    simp [Table.get, show ¬ j + staticSize + 1 ≤ staticSize by omega, hx,
      show j + staticSize + 1 - staticSize - 1 = j by omega, ← hp]

theorem name_nameRef (t : Table) (n : ByteArray) : t.name (t.nameRef n) = .ok n := by
  unfold Table.nameRef
  split
  · rename_i i hi
    obtain ⟨⟨v, hv⟩, -, -⟩ := findName_get t n i hi
    simp [Table.name, hv]
  · rfl

theorem apply_choose (limit : Nat) (t : Table) (f : HeaderField) :
    apply limit t (choose t f) = .ok (step t (choose t f), some f) := by
  obtain ⟨n, v, sens⟩ := f
  unfold choose
  cases sens with
  | true =>
    simp [apply, step, name_nameRef, bind, Except.bind, pure, Except.pure]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    split
    · rename_i i hi
      have := (findField_get t (n, v) i hi).1
      simp [apply, step, this]
    · simp [apply, step, name_nameRef, bind, Except.bind, pure, Except.pure]

theorem choose_not_sizeUpdate (t : Table) (f : HeaderField) (n : Nat) : choose t f ≠ .sizeUpdate n := by
  unfold choose; split
  · simp
  · split <;> simp


theorem applyAll_chooseAll (limit maxList : Nat) (fs : List HeaderField) :
    ∀ (t : Table) (started : Bool) (total : Nat), total + listSize fs ≤ maxList →
      applyAll limit maxList t (chooseAll t fs).1 started total = .ok (fs, (chooseAll t fs).2) := by
  induction fs with
  | nil => intro t started total _; rfl
  | cons f fs ih =>
    intro t started total hl
    simp only [listSize, List.map_cons, List.sum_cons] at hl
    have hsu : (choose t f).isSizeUpdate = false := by
      cases h : choose t f with
      | sizeUpdate n => exact absurd h (choose_not_sizeUpdate t f n)
      | _ => rfl
    have hih := ih (step t (choose t f)) true (total + fieldSize f) (by simp only [listSize]; omega)
    have hn : ¬ (total + fieldSize f > maxList) := by omega
    simp only [chooseAll, applyAll, hsu, Bool.and_false, Bool.false_eq_true, ite_false,
      apply_choose, bind, Except.bind, pure, Except.pure, hih, hn]

/-! ## Indices stay small -/


theorem sum_fitPrefix (es : List Field) (b : Nat) : ((fitPrefix es b).map entrySize).sum ≤ b := by
  induction es generalizing b with
  | nil => simp [fitPrefix]
  | cons e es ih =>
    unfold fitPrefix
    split
    · have := ih (b - entrySize e); simp; omega
    · simp

theorem wf_add (t : Table) (f : Field) (h : t.Wf) : (t.add f).Wf :=
  ⟨sum_fitPrefix _ _, h.2⟩

theorem wf_resize (t : Table) (n : Nat) (h : n < 2 ^ 28) : (t.resize n).Wf :=
  ⟨sum_fitPrefix _ _, h⟩

theorem entries_length_le (es : List Field) : 32 * es.length ≤ (es.map entrySize).sum := by
  induction es with
  | nil => simp
  | cons e es ih => simp [entrySize]; omega

theorem wf_length (t : Table) (h : t.Wf) : t.entries.length < 2 ^ 23 := by
  have := entries_length_le t.entries
  have := h.1; have := h.2
  simp only [Table.size] at *
  omega

theorem wf_step_choose (t : Table) (f : HeaderField) (h : t.Wf) : (step t (choose t f)).Wf := by
  unfold choose
  split
  · simp [step]; exact h
  · split
    · simp [step]; exact h
    · simp only [step, name_nameRef]; exact wf_add t _ h

theorem choose_ok (t : Table) (f : HeaderField) (h : t.Wf) (hn : f.name.size < 2 ^ 28)
    (hv : f.value.size < 2 ^ 28) : (choose t f).ok := by
  have hl := wf_length t h
  have hname : (Rep.literal .neverIndexed (t.nameRef f.name) f.value).ok ∧
      (Rep.literal .incremental (t.nameRef f.name) f.value).ok := by
    unfold Table.nameRef
    split
    · rename_i i hi
      obtain ⟨-, h1, h2⟩ := findName_get t f.name i hi
      simp only [Rep.ok, staticSize] at *
      omega
    · exact ⟨⟨hn, hv⟩, ⟨hn, hv⟩⟩
  unfold choose
  split
  · exact hname.1
  · split
    · rename_i i hi
      have := (findField_get t _ i hi).2
      simp only [Rep.ok, staticSize] at *
      omega
    · exact hname.2

theorem chooseAll_ok (fs : List HeaderField) (hs : ∀ f ∈ fs, f.name.size < 2 ^ 28 ∧ f.value.size < 2 ^ 28) :
    ∀ t : Table, t.Wf → (∀ r ∈ (chooseAll t fs).1, r.ok) ∧ (chooseAll t fs).2.Wf := by
  induction fs with
  | nil => intro t h; exact ⟨by simp [chooseAll], h⟩
  | cons f fs ih =>
    intro t h
    have hf := hs f (by simp)
    obtain ⟨h1, h2⟩ := ih (fun x hx => hs x (by simp [hx])) (step t (choose t f)) (wf_step_choose t f h)
    refine ⟨?_, h2⟩
    intro r hr
    simp only [chooseAll, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact choose_ok t f h hf.1 hf.2
    · exact h1 r hr

/-! ## The round trips -/

/-- **HPACK round trip with a dynamic table** (card: `hpack_decode_encode`).
An encoder and a decoder whose tables agree: the decoder reads the
encoder's block back as the same fields, and the two tables agree again
afterwards. The hypotheses: a well-formed table; a pending size update the
decoder allows; names and values below `2 ^ 28` bytes; a header list within
the decoder's limit. -/
theorem hpack_decode_encode (e : Encoder) (d : Decoder) (fs : List HeaderField)
    (htab : e.table = d.table) (hwf : e.table.Wf) (hlim : d.maxTableSize < 2 ^ 28)
    (hpend : ∀ n, e.pendingSize = some n → n ≤ d.maxTableSize)
    (hs : ∀ f ∈ fs, f.name.size < 2 ^ 28 ∧ f.value.size < 2 ^ 28)
    (hl : listSize fs ≤ d.maxHeaderListSize) :
    d.decode (e.encode fs).1 = .ok (fs, { d with table := (e.encode fs).2.table }) := by
  unfold Encoder.encode Decoder.decode
  cases hp : e.pendingSize with
  | none =>
    obtain ⟨hok, -⟩ := chooseAll_ok fs hs e.table hwf
    simp only [List.nil_append]
    rw [decodeReps_encodeReps _ hok]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [← htab, applyAll_chooseAll _ _ fs e.table false 0 (by omega)]
  | some n =>
    have hn := hpend n hp
    have hwf' := wf_resize e.table n (by omega)
    obtain ⟨hok, -⟩ := chooseAll_ok fs hs (e.table.resize n) hwf'
    have hok' : ∀ r ∈ [Rep.sizeUpdate n] ++ (chooseAll (e.table.resize n) fs).1, r.ok := by
      intro r hr
      simp only [List.singleton_append, List.mem_cons] at hr
      rcases hr with rfl | hr
      · show n < 2 ^ 28; omega
      · exact hok r hr
    rw [decodeReps_encodeReps _ hok']
    simp only [List.singleton_append, applyAll, Rep.isSizeUpdate, Bool.false_and, Bool.false_eq_true,
      ite_false, apply, show ¬ n > d.maxTableSize by omega, bind, Except.bind, pure, Except.pure]
    rw [← htab, applyAll_chooseAll _ _ fs (e.table.resize n) false 0 (by omega)]

/-- After a block the encoder has no size update pending. -/
theorem encode_pending (e : Encoder) (fs : List HeaderField) : (e.encode fs).2.pendingSize = none := by
  unfold Encoder.encode; split <;> rfl

/-- Encoding keeps the table well formed. -/
theorem wf_encode (e : Encoder) (fs : List HeaderField) (hwf : e.table.Wf)
    (hpend : ∀ n, e.pendingSize = some n → n < 2 ^ 28)
    (hs : ∀ f ∈ fs, f.name.size < 2 ^ 28 ∧ f.value.size < 2 ^ 28) : (e.encode fs).2.table.Wf := by
  unfold Encoder.encode
  cases hp : e.pendingSize with
  | none => exact (chooseAll_ok fs hs e.table hwf).2
  | some n => exact (chooseAll_ok fs hs _ (wf_resize e.table n (hpend n hp))).2

/-- **The stateful round trip**: header lists encoded in order, one block
each, decode in order to the same lists, the decoder's table ending where
the encoder's does. -/
theorem hpack_decode_encode_seq (ls : List (List HeaderField)) : ∀ (e : Encoder) (d : Decoder),
    e.table = d.table → e.table.Wf → d.maxTableSize < 2 ^ 28 →
    (∀ n, e.pendingSize = some n → n ≤ d.maxTableSize) →
    (∀ fs ∈ ls, (∀ f ∈ fs, f.name.size < 2 ^ 28 ∧ f.value.size < 2 ^ 28) ∧ listSize fs ≤ d.maxHeaderListSize) →
    d.decodeAll (e.encodeAll ls).1 = .ok (ls, { d with table := (e.encodeAll ls).2.table }) := by
  induction ls with
  | nil => intro e d htab _ _ _ _; simp [Encoder.encodeAll, Decoder.decodeAll, htab]
  | cons fs ls ih =>
    intro e d htab hwf hlim hpend hls
    obtain ⟨hs, hl⟩ := hls fs (by simp)
    have h1 := hpack_decode_encode e d fs htab hwf hlim hpend hs hl
    have hwf' := wf_encode e fs hwf (fun n hn => by have := hpend n hn; omega) hs
    have ih' := ih (e.encode fs).2 { d with table := (e.encode fs).2.table } rfl hwf' hlim
      (by simp [encode_pending]) (fun fs' h => hls fs' (by simp [h]))
    simp only [Encoder.encodeAll, Decoder.decodeAll, h1, bind, Except.bind, pure, Except.pure]
    rw [ih']

theorem apply_chooseStatic (limit : Nat) (t : Table) (f : HeaderField) :
    apply limit t (chooseStatic f) = .ok (t, some f) := by
  obtain ⟨n, v, sens⟩ := f
  have hname : ∀ k : LitKind, k ≠ .incremental →
      apply limit t (.literal k (({ maxSize := 0 } : Table).nameRef n) v) = .ok (t, some ⟨n, v, k == .neverIndexed⟩) := by
    intro k hk
    have hr : t.name (({ maxSize := 0 } : Table).nameRef n) = .ok n := by
      unfold Table.nameRef
      split
      · rename_i i hi
        obtain ⟨⟨w, hw⟩, h1, h2⟩ := findName_get _ n i hi
        simp only [List.length_nil, Nat.add_zero] at h2
        have hi0 : (i == 0) = false := by simp; omega
        have : t.get i = some (n, w) := by
          unfold Table.get at hw ⊢
          simp only [hi0, Bool.false_eq_true, ite_false, if_pos h2] at hw ⊢; exact hw
        simp [Table.name, this]
      · rfl
    simp [apply, hr, hk, bind, Except.bind, pure, Except.pure]
  unfold chooseStatic
  split
  · rename_i j hj
    cases sens with
    | true => exact hname .neverIndexed (by decide)
    | false =>
      obtain ⟨x, hx, hp, hlen⟩ := findIdx_get hj
      simp at hp; subst hp
      rw [length_staticTable] at hlen
      simp [apply, Table.get, show j + 1 ≤ staticSize by omega, hx]
  · cases sens with
    | true => exact hname .neverIndexed (by decide)
    | false => exact hname .withoutIndexing (by decide)

theorem chooseStatic_ok (f : HeaderField) (hn : f.name.size < 2 ^ 28) (hv : f.value.size < 2 ^ 28) :
    (chooseStatic f).ok := by
  have hname : ∀ k, (Rep.literal k (({ maxSize := 0 } : Table).nameRef f.name) f.value).ok := by
    intro k
    unfold Table.nameRef
    split
    · rename_i i hi
      obtain ⟨-, h1, h2⟩ := findName_get _ f.name i hi
      simp only [Rep.ok, staticSize, List.length_nil] at *
      omega
    · exact ⟨hn, hv⟩
  unfold chooseStatic
  split
  · rename_i j hj
    split
    · exact hname _
    · obtain ⟨-, -, -, hlen⟩ := findIdx_get hj
      rw [length_staticTable] at hlen
      show j + 1 < 2 ^ 28; simp [staticSize] at hlen; omega
  · exact hname _

theorem applyAll_static (limit maxList : Nat) (fs : List HeaderField) :
    ∀ (t : Table) (started : Bool) (total : Nat), total + listSize fs ≤ maxList →
      applyAll limit maxList t (fs.map chooseStatic) started total = .ok (fs, t) := by
  induction fs with
  | nil => intro t started total _; rfl
  | cons f fs ih =>
    intro t started total hl
    simp only [listSize, List.map_cons, List.sum_cons] at hl
    have hsu : (chooseStatic f).isSizeUpdate = false := by
      unfold chooseStatic; split
      · split <;> rfl
      · rfl
    have hih := ih t true (total + fieldSize f) (by simp only [listSize]; omega)
    have hn : ¬ (total + fieldSize f > maxList) := by omega
    simp only [List.map_cons, applyAll, hsu, Bool.and_false, Bool.false_eq_true, ite_false,
      apply_chooseStatic, bind, Except.bind, pure, Except.pure, hih, hn]

/-- **HPACK round trip, static table and literals** (card:
`hpack_decode_encode`, the stateless part). Encoding with the static table
alone (section 2.3) reads back with any decoder, and leaves its table as it
was. -/
theorem hpack_decode_encode_static (d : Decoder) (fs : List HeaderField)
    (hs : ∀ f ∈ fs, f.name.size < 2 ^ 28 ∧ f.value.size < 2 ^ 28)
    (hl : listSize fs ≤ d.maxHeaderListSize) :
    d.decode (encodeStatic fs) = .ok (fs, d) := by
  unfold Decoder.decode encodeStatic
  have hok : ∀ r ∈ fs.map chooseStatic, r.ok := by
    intro r hr
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hr
    exact chooseStatic_ok f (hs f hf).1 (hs f hf).2
  rw [decodeReps_encodeReps _ hok]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [applyAll_static _ _ fs d.table false 0 (by omega)]

end Hpack

end LeanHttpx
