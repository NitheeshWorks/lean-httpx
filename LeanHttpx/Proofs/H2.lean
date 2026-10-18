import LeanHttpx.RepoImpl.H2Frame

/-!
# HTTP/2 frames: print then parse is the identity

`parseRaw_encodeRaw`: a raw frame whose payload fits the receiver's maximum
frame size reads back from its bytes, on any continuation.
`ofRaw_toRaw`: a valid frame's payload reads back as the same frame.
Together, `h2_frame_parse_print_ext`.
-/

namespace LeanHttpx

namespace H2

open Bytes

theorem takeBE_beArr_only (w n : Nat) (h : n < 256 ^ w) : takeBE w (beArr w n) = some (n, .empty) := by
  have := takeBE_beArr w n h .empty
  rwa [ByteArray.append_empty] at this

@[simp] theorem size_rawHeader (f : RawFrame) : (rawHeader f).size = 9 := by
  simp [rawHeader, ByteArray.size_append]

theorem readHeader_rawHeader (f : RawFrame) (hl : f.payload.size < 2 ^ 24) (ht : f.type < 256)
    (hf : f.flags < 256) (hs : f.streamId < 2 ^ 32) :
    readHeader (rawHeader f) = some (f.payload.size, f.type, f.flags, f.streamId, .empty) := by
  simp [readHeader, rawHeader, takeBE_beArr _ _ (by omega : f.payload.size < 256 ^ 3),
    takeBE_beArr _ _ (by omega : f.type < 256 ^ 1), takeBE_beArr _ _ (by omega : f.flags < 256 ^ 1),
    takeBE_beArr_only _ _ (by omega : f.streamId < 256 ^ 4)]

/-- **Raw frame round trip.** -/
theorem parseRaw_encodeRaw (max : Nat) (f : RawFrame) (hp : f.payload.size ≤ max) (hmax : max < 2 ^ 24)
    (ht : f.type < 256) (hf : f.flags < 256) (hs : f.streamId < 2 ^ 31) (rest : ByteArray) :
    parseRaw max (encodeRaw f ++ rest) = .done f rest := by
  have hsize : (encodeRaw f ++ rest).size = 9 + f.payload.size + rest.size := by
    simp [encodeRaw, ByteArray.size_append]
  have hhead : (encodeRaw f ++ rest).extract 0 frameHeaderSize = rawHeader f := by
    rw [encodeRaw, ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_left (by simp [frameHeaderSize])
  have hpay : (encodeRaw f ++ rest).extract frameHeaderSize (frameHeaderSize + f.payload.size) = f.payload := by
    rw [encodeRaw, ByteArray.append_assoc]
    have := extract_mid (rawHeader f) f.payload rest
    simpa [frameHeaderSize] using this
  have hrest : (encodeRaw f ++ rest).extract (frameHeaderSize + f.payload.size) (encodeRaw f ++ rest).size = rest := by
    have := extract_size_append (encodeRaw f) rest
    have he : (encodeRaw f).size = frameHeaderSize + f.payload.size := by
      simp [encodeRaw, ByteArray.size_append, frameHeaderSize]
    rw [he] at this
    rw [ByteArray.size_append, he]
    exact this
  unfold parseRaw
  rw [hhead, readHeader_rawHeader f (by omega) ht hf (by omega)]
  simp only [hsize, frameHeaderSize] at *
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [Nat.mod_eq_of_lt hs, hpay, hrest]

end H2

end LeanHttpx

namespace LeanHttpx

namespace H2

open Bytes

theorem readPad_none (b : ByteArray) : readPad false b = .ok (none, b) := rfl

theorem readPad_some (p : Nat) (hp : p < 256) (x : ByteArray) (hx : p ≤ x.size) :
    readPad true (beArr 1 p ++ x) = .ok (some p, x) := by
  have : ¬ x.size < p := by omega
  simp [readPad, need, takeBE_beArr 1 p (by omega), this, bind, Except.bind, pure, Except.pure]

theorem unpad_append (pad : Option Nat) (x : ByteArray) : unpad pad (x ++ padTail pad) = x := by
  cases pad with
  | none => simp [unpad, padTail, ByteArray.append_empty]
  | some p =>
    simp only [unpad, padTail, ByteArray.size_append, size_zeros, Nat.add_sub_cancel]
    exact ByteArray.extract_append_eq_left rfl

theorem readPad_padHead (pad : Option Nat) (hp : padOk pad = true) (x : ByteArray)
    (hx : pad.getD 0 ≤ x.size) : readPad pad.isSome (padHead pad ++ x) = .ok (pad, x) := by
  cases pad with
  | none => simp [padHead, readPad, ByteArray.empty_append, pure, Except.pure]
  | some p => simpa [padHead] using readPad_some p (by simpa [padOk] using hp) x (by simpa using hx)

theorem le_padTail (pad : Option Nat) (x : ByteArray) : pad.getD 0 ≤ (x ++ padTail pad).size := by
  cases pad <;> simp [padTail, ByteArray.size_append]

theorem readPriority_bytes (p : Priority) (hp : p.ok = true) (r : ByteArray) :
    readPriority (priorityBytes p ++ r) = .ok (p, r) := by
  simp only [Priority.ok, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨e, d, w⟩ := p
  simp only at hp
  have hd : d + bitIf e 31 < 256 ^ 4 := by cases e <;> simp [bitIf] <;> omega
  simp only [readPriority, priorityBytes, ByteArray.append_assoc, need,
    takeBE_beArr 4 _ hd, takeBE_beArr 1 w (by omega : w < 256 ^ 1), bind, Except.bind, pure, Except.pure]
  have h31 : d < 2147483648 := hp.1
  cases e <;> simp [bitIf] <;> omega

theorem readSettings_bytes (ps : List (Nat × Nat)) (h : ps.all (fun kv => kv.1 < 2 ^ 16 && kv.2 < 2 ^ 32) = true) :
    readSettings ps.length (settingsBytes ps) = .ok ps := by
  induction ps with
  | nil => rfl
  | cons kv ps ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have hne : (settingsBytes ((k, v) :: ps)).size ≠ 0 := by simp [settingsBytes, ByteArray.size_append]
    simp only [List.length_cons, readSettings, settingsBytes] at hne ⊢
    simp [hne, need, takeBE_beArr 2 k (by omega), takeBE_beArr 4 v (by omega), ih h.2, bind,
      Except.bind, pure, Except.pure]

theorem size_settingsBytes (ps : List (Nat × Nat)) : (settingsBytes ps).size = 6 * ps.length := by
  induction ps with
  | nil => rfl
  | cons kv ps ih => simp [settingsBytes, ByteArray.size_append, ih]; omega

/-- **Typed frame round trip.** -/
theorem ofRaw_toRaw (f : Frame) (h : f.ok = true) : Frame.ofRaw f.toRaw = .ok f := by
  cases f with
  | data sid d es pad =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    have hf : flag (bitIf es 0 + bitIf pad.isSome 3) 3 = pad.isSome ∧
        flag (bitIf es 0 + bitIf pad.isSome 3) 0 = es := by
      cases es <;> cases pad.isSome <;> decide
    simp only [Frame.toRaw, Frame.ofRaw, hf.1, hf.2, readPad_padHead pad h.2 _ (le_padTail pad d), streamCheck]
    simp [show sid ≠ 0 by omega, unpad_append, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  | headers sid blk es eh prio pad =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    have hf : ∀ a b c d : Bool, flag (bitIf a 0 + bitIf b 2 + bitIf c 3 + bitIf d 5) 0 = a ∧
        flag (bitIf a 0 + bitIf b 2 + bitIf c 3 + bitIf d 5) 2 = b ∧
        flag (bitIf a 0 + bitIf b 2 + bitIf c 3 + bitIf d 5) 3 = c ∧
        flag (bitIf a 0 + bitIf b 2 + bitIf c 3 + bitIf d 5) 5 = d := by decide
    obtain ⟨h0, h2, h3, h5⟩ := hf es eh pad.isSome prio.isSome
    have hsid : sid ≠ 0 := by omega
    have hpad : pad.getD 0 ≤ blk.size + (padTail pad).size := by
      have := le_padTail pad blk; rwa [ByteArray.size_append] at this
    cases prio with
    | none =>
      simp only [Frame.toRaw, Frame.ofRaw, h0, h2, h3, h5, streamCheck, ByteArray.empty_append,
        readPad_padHead pad h.1.2 _ (le_padTail pad blk)]
      simp [hsid, hpad, unpad_append, bind, Except.bind, pure, Except.pure, Functor.map]
    | some p =>
      have hp : p.ok = true := by simpa using h.2
      have hle : pad.getD 0 ≤ (priorityBytes p ++ (blk ++ padTail pad)).size := by
        have := le_padTail pad blk; simp [ByteArray.size_append] at this ⊢; omega
      simp only [Frame.toRaw, Frame.ofRaw, h0, h2, h3, h5, streamCheck,
        readPad_padHead pad h.1.2 _ hle]
      simp [hsid, hpad, unpad_append, readPriority_bytes p hp, bind, Except.bind, pure, Except.pure, Functor.map]
  | priority sid p =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    have hsz : (priorityBytes p).size = 5 := by simp [priorityBytes, ByteArray.size_append]
    have := readPriority_bytes p h.2 .empty
    rw [ByteArray.append_empty] at this
    simp [Frame.toRaw, Frame.ofRaw, streamCheck, show sid ≠ 0 by omega, hsz, this, bind, Except.bind, pure, Except.pure, Functor.map]
  | rstStream sid c =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [Frame.toRaw, Frame.ofRaw, streamCheck, show sid ≠ 0 by omega, need,
      takeBE_beArr_only 4 c (by omega), bind, Except.bind, pure, Except.pure, Functor.map]
  | settings ack ps =>
    simp only [Frame.ok, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    have hf : flag (bitIf ack 0) 0 = ack := by cases ack <;> decide
    have hsz := size_settingsBytes ps
    have hack : ¬ (ack = true ∧ (settingsBytes ps).size ≠ 0) := by
      rintro ⟨ha, hn⟩
      rcases h.1 with h1 | h1
      · simp [ha] at h1
      · simp at h1; subst h1; exact hn rfl
    have hdiv : (settingsBytes ps).size / 6 = ps.length := by omega
    simp only [Frame.toRaw, Frame.ofRaw, streamCheck, hf]
    simp [hack, hsz, readSettings_bytes ps h.2, bind, Except.bind, pure, Except.pure, Functor.map]
    intro ha; rw [← hsz]; exact Classical.byContradiction fun hn => hack ⟨ha, hn⟩
  | pushPromise sid prom blk eh pad =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    have hf : ∀ a b : Bool, flag (bitIf a 2 + bitIf b 3) 2 = a ∧ flag (bitIf a 2 + bitIf b 3) 3 = b := by decide
    obtain ⟨h2, h3⟩ := hf eh pad.isSome
    have hpad : pad.getD 0 ≤ blk.size + (padTail pad).size := by
      have := le_padTail pad blk; rwa [ByteArray.size_append] at this
    have hle : pad.getD 0 ≤ (beArr 4 prom ++ (blk ++ padTail pad)).size := by
      have := le_padTail pad blk; simp [ByteArray.size_append] at this ⊢; omega
    simp only [Frame.toRaw, Frame.ofRaw, h2, h3, streamCheck, readPad_padHead pad h.2 _ hle]
    simp [show sid ≠ 0 by omega, need, takeBE_beArr 4 prom (by omega), hpad, unpad_append,
      Nat.mod_eq_of_lt h.1.2, bind, Except.bind, pure, Except.pure, Functor.map]
  | ping ack d =>
    simp only [Frame.ok, beq_iff_eq] at h
    have hf : flag (bitIf ack 0) 0 = ack := by cases ack <;> decide
    simp [Frame.toRaw, Frame.ofRaw, streamCheck, hf, h, bind, Except.bind, pure, Except.pure, Functor.map]
  | goaway last code dbg =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [Frame.toRaw, Frame.ofRaw, streamCheck, need, takeBE_beArr 4 last (by omega),
      takeBE_beArr 4 code (by omega), Nat.mod_eq_of_lt h.1, bind, Except.bind, pure, Except.pure, Functor.map]
  | windowUpdate sid inc =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [Frame.toRaw, Frame.ofRaw, need, takeBE_beArr_only 4 inc (by omega), Nat.mod_eq_of_lt h.2, bind, Except.bind, pure, Except.pure, Functor.map]
  | continuation sid blk eh =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    have hf : flag (bitIf eh 2) 2 = eh := by cases eh <;> decide
    simp [Frame.toRaw, Frame.ofRaw, streamCheck, hf, show sid ≠ 0 by omega, bind, Except.bind, pure, Except.pure, Functor.map]
  | unknown ty fl sid payload =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨k, rfl⟩ : ∃ k, ty = k + 10 := ⟨ty - 10, by omega⟩
    simp [Frame.toRaw, Frame.ofRaw, bind, Except.bind, pure, Except.pure, Functor.map]

theorem bitIf_le (b : Bool) (k : Nat) : bitIf b k ≤ 2 ^ k := by cases b <;> simp [bitIf]

theorem toRaw_bounds (f : Frame) (h : f.ok = true) :
    f.toRaw.type < 256 ∧ f.toRaw.flags < 256 ∧ f.toRaw.streamId < 2 ^ 31 := by
  cases f with
  | data sid d es pad =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    have := bitIf_le es 0; have := bitIf_le pad.isSome 3
    simp only [Frame.toRaw]; refine ⟨by omega, by simp at *; omega, by omega⟩
  | headers sid blk es eh prio pad =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    have := bitIf_le es 0; have := bitIf_le eh 2; have := bitIf_le pad.isSome 3; have := bitIf_le prio.isSome 5
    simp only [Frame.toRaw]; refine ⟨by omega, by simp at *; omega, by omega⟩
  | priority sid p =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Frame.toRaw]; omega
  | rstStream sid c =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Frame.toRaw]; omega
  | settings ack ps =>
    have := bitIf_le ack 0
    simp only [Frame.toRaw]; refine ⟨by omega, by simp at *; omega, by omega⟩
  | pushPromise sid prom blk eh pad =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    have := bitIf_le eh 2; have := bitIf_le pad.isSome 3
    simp only [Frame.toRaw]; refine ⟨by omega, by simp at *; omega, by omega⟩
  | ping ack d =>
    have := bitIf_le ack 0
    simp only [Frame.toRaw]; refine ⟨by omega, by simp at *; omega, by omega⟩
  | goaway last code dbg => simp only [Frame.toRaw]; omega
  | windowUpdate sid inc =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Frame.toRaw]; omega
  | continuation sid blk eh =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    have := bitIf_le eh 2
    simp only [Frame.toRaw]; refine ⟨by omega, by simp at *; omega, by omega⟩
  | unknown ty fl sid payload =>
    simp only [Frame.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Frame.toRaw]; omega

/-- **HTTP/2 frame round trip** (card: `h2_frame_parse_print_ext`). A valid
frame whose payload fits the receiver's maximum frame size reads back from
its bytes, leaving whatever follows. -/
theorem h2_frame_parse_print_ext (max : Nat) (f : Frame) (h : f.ok = true)
    (hp : f.toRaw.payload.size ≤ max) (hmax : max < 2 ^ 24) (rest : ByteArray) :
    parseFrame max (printFrame f ++ rest) = .done f rest := by
  obtain ⟨ht, hf, hs⟩ := toRaw_bounds f h
  simp [parseFrame, printFrame, parseRaw_encodeRaw max f.toRaw hp hmax ht hf hs rest, ofRaw_toRaw f h]

end H2

end LeanHttpx
