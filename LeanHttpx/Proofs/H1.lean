import LeanHttpx.RepoImpl.H1Body

/-!
# The HTTP/1.1 round trips

The message codecs are lawful by construction (`Keel.Codec`), so each round
trip is the codec law `decodeBytes_encodeBytes` applied to a message the
codec takes as valid. What is proved here is that validity: a message is
valid for the codec exactly when its parts avoid their delimiters, which the
Boolean checks `Field.ok`, `Request.ok` and `Response.ok` state in plain
terms. The side conditions reduce to two `Keel.Codec` lemmas,
`avoids_of_head_not_mem` and `incomparable_of_head_ne`.
-/

namespace LeanHttpx

namespace H1

open Keel

theorem tchar_ne {b : UInt8} (h : isTchar b = true) : b ≠ COLON ∧ b ≠ SP ∧ b ≠ CR := by
  unfold isTchar at h; refine ⟨?_, ?_, ?_⟩ <;> (intro e; subst e; revert h; decide)

theorem token_avoids {l : List UInt8} {x : UInt8} (h : isToken l = true)
    (hx : ∀ b, isTchar b = true → b ≠ x) : x ∉ l := by
  simp only [isToken, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at h
  intro hm; exact hx x (h.2 x hm) rfl

theorem token_head {l : List UInt8} (h : isToken l = true) :
    ∃ b t, l = b :: t ∧ isTchar b = true := by
  simp only [isToken, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at h
  match l, h with
  | b :: t, h => exact ⟨b, t, rfl, h.2 b (by simp)⟩

theorem valueOk_no_cr {v : List UInt8} (h : valueOk v = true) : CR ∉ SP :: v := by
  simp only [valueOk, Bool.and_eq_true, List.all_eq_true] at h
  intro hm
  rcases List.mem_cons.mp hm with e | hm
  · exact absurd e (by decide)
  · have := h.1.1 CR hm; revert this; decide

theorem field_valid (f : Field) (h : f.ok = true) : field.valid f := by
  simp only [Field.ok, Bool.and_eq_true] at h
  simp only [field, fieldName, fieldValue, owsValue, Codec.map_valid, Codec.seq_valid, Codec.delimited_valid, Codec.guard_valid,
    Codec.guard_follow, Codec.guard_encode, Codec.rest_valid, Codec.rest_follow, Codec.rest_encode,
    Codec.delimited_follow, Codec.map_follow, Codec.map_encode, Codec.seq_follow, Codec.seq_encode,
    Codec.delimited_encode, true_and, and_true, implies_true]
  exact ⟨⟨h.1, Codec.avoids_of_head_not_mem rfl (token_avoids h.1 fun b hb => (tchar_ne hb).1)⟩,
    h.2, Codec.avoids_of_head_not_mem rfl (valueOk_no_cr h.2)⟩

theorem fields_valid : ∀ (fs : List Field), fs.all Field.ok = true → fields.valid fs
  | [], _ => trivial
  | f :: fs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    refine ⟨field_valid f h.1, ?_, fun _ => trivial, fields_valid fs h.2⟩
    obtain ⟨b, t, hn, hb⟩ := token_head (by simp only [Field.ok, Bool.and_eq_true] at h; exact h.1.1)
    simp only [field, fieldName, Codec.map_encode, Codec.seq_encode, Codec.delimited_encode,
      Codec.guard_encode, Codec.rest_encode, hn, List.cons_append]
    exact Codec.incomparable_of_head_ne (tchar_ne hb).2.2.symm

theorem bodyCodec_follow (fr : Framing) (r : List UInt8) : (bodyCodec fr).follow r := by
  cases fr <;> trivial

theorem bodyCodec_valid (fr : Framing) (b : ByteArray) (h : bodyFits fr b = true) :
    (bodyCodec fr).valid b := by
  cases fr with
  | none =>
    show b = ByteArray.empty
    simp only [bodyFits, beq_iff_eq] at h
    obtain ⟨d⟩ := b
    have : d = #[] := by simpa using (show d.size = 0 from h)
    subst this; rfl
  | length n => show b.size = n; simpa [bodyFits] using h
  | chunked =>
    intro c hc
    simp only [toChunks] at hc
    split at hc
    · cases hc
    · simp at hc; subst hc; omega
  | close => simp [bodyFits] at h
  | invalid => simp [bodyFits] at h

theorem tag_valid (fr : Framing) (b : ByteArray) {α : Type} (c : Codec UInt8 α) (a : α)
    (hc : ∀ r, c.follow r) : ∀ r, (bodyCodec fr).follow r → c.follow ((bodyCodec fr).encode b ++ r) :=
  fun _ _ => hc _

theorem requestHead_follow (r : List UInt8) : requestHead.follow r := trivial
theorem responseHead_follow (r : List UInt8) : responseHead.follow r := trivial

theorem version_valid {tl tr : List UInt8} (htag : Keel.Incomparable tl tr) (v : Version) :
    (Codec.sum tl tr Codec.unit Codec.unit htag).valid v.toSum := by
  cases v <;> trivial

theorem request_valid (r : Request) (h : r.ok = true) : request.valid r := by
  simp only [Request.ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hm, ht⟩, hf⟩, hb⟩ := h
  refine ⟨?_, bodyCodec_valid _ _ hb, fun _ _ => trivial⟩
  simp only [requestHead, method, target, requestVersion, Codec.map_valid, Codec.seq_valid, Codec.delimited_valid, Codec.guard_valid,
    Codec.guard_follow, Codec.guard_encode, Codec.rest_valid, Codec.rest_follow, Codec.rest_encode,
    Codec.delimited_follow, Codec.map_follow, Codec.map_encode, Codec.seq_follow, Codec.seq_encode,
    Codec.delimited_encode, true_and, and_true, implies_true]
  refine ⟨⟨hm, Codec.avoids_of_head_not_mem rfl (token_avoids hm fun b hb => (tchar_ne hb).2.1)⟩,
    ⟨ht, Codec.avoids_of_head_not_mem rfl ?_⟩, version_valid _ _, fields_valid _ hf,
    fun _ _ => ⟨trivial, trivial⟩⟩
  simp only [isTarget, Bool.and_eq_true, List.all_eq_true] at ht
  intro hm'; have := ht.2 SP hm'; revert this; decide

/-- The status code's digits: three, the first not zero. -/
theorem isStatus_decimalBytes (n : Nat) (h1 : 100 ≤ n) (h2 : n ≤ 999) : isStatus (decimalBytes n) = true := by
  have e : Codec.decimal n = [Codec.digitChar (n / 100), Codec.digitChar (n / 10 % 10), Codec.digitChar (n % 10)] := by
    rw [Codec.decimal, if_neg (by omega), Codec.decimal, if_neg (by omega), Codec.decimal, if_pos (by omega)]
    simp only [List.singleton_append, List.cons_append, List.nil_append]
    congr 2
    omega
  have hd : ∀ d : Fin 10, ((Codec.digitChar d.val).toNat.toUInt8) = (48 + d.val).toUInt8 := by decide
  have h3 := hd ⟨n / 100, by omega⟩
  have h4 := hd ⟨n / 10 % 10, by omega⟩
  have h5 := hd ⟨n % 10, by omega⟩
  simp only at h3 h4 h5
  simp only [decimalBytes, e, List.map_cons, List.map_nil, h3, h4, h5, isStatus]
  have ha : n / 100 < 10 := by omega
  have hb : n / 10 % 10 < 10 := by omega
  have hc : n % 10 < 10 := by omega
  have hz : 1 ≤ n / 100 := by omega
  generalize n / 100 = a at ha hz
  generalize n / 10 % 10 = b at hb
  generalize n % 10 = c at hc
  revert a b c
  decide

theorem reasonOk_no_cr {l : List UInt8} (h : reasonOk l = true) : CR ∉ l := by
  simp only [reasonOk, List.all_eq_true] at h
  intro hm; have := h CR hm; revert this; decide

theorem response_valid (m : List UInt8) (r : Response) (h : r.ok m = true) : (response m).valid r := by
  simp only [Response.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hs1, hs2⟩, hr⟩, hf⟩, hb⟩ := h
  refine ⟨?_, bodyCodec_valid _ _ hb, fun _ _ => trivial⟩
  simp only [responseHead, status, reason, responseVersion, Codec.map_valid, Codec.seq_valid, Codec.delimited_valid, Codec.guard_valid,
    Codec.guard_follow, Codec.guard_encode, Codec.rest_valid, Codec.rest_follow, Codec.rest_encode,
    Codec.delimited_follow, Codec.map_follow, Codec.map_encode, Codec.seq_follow, Codec.seq_encode,
    Codec.delimited_encode, true_and, and_true, implies_true]
  have hst := isStatus_decimalBytes _ hs1 hs2
  refine ⟨version_valid _ _, ⟨⟨hst, Codec.avoids_of_head_not_mem rfl ?_⟩,
    ⟨hr, Codec.avoids_of_head_not_mem rfl (reasonOk_no_cr hr)⟩, fields_valid _ hf⟩,
    fun _ _ => ⟨trivial, trivial⟩⟩
  simp only [isStatus, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hst
  intro hm; have := hst.1.2 SP hm; revert this; decide

theorem request_follow (rest : List UInt8) : request.follow rest :=
  fun t => bodyCodec_follow _ rest

theorem response_follow (m rest : List UInt8) : (response m).follow rest :=
  fun t => bodyCodec_follow _ rest

/-! ## The headline round trips -/

/-- **Request round trip** (card: `h1_request_print_parse`). A valid request
prints to bytes that parse back to it, whatever follows on the connection. -/
theorem h1_request_print_parse (r : Request) (h : r.ok = true) (rest : ByteArray) :
    parseRequest (printRequest r ++ rest) = some (r, rest) :=
  Codec.decodeBytes_encodeBytes _ (request_valid r h) (request_follow _)

/-- **Response round trip** (card: `h1_response_parse_print_ext`). A valid
response prints to bytes that parse back to it on any continuation, so
pipelined responses split correctly. -/
theorem h1_response_parse_print_ext (m : List UInt8) (r : Response) (h : r.ok m = true)
    (rest : ByteArray) : parseResponse m (printResponse m r ++ rest) = some (r, rest) :=
  Codec.decodeBytes_encodeBytes _ (response_valid m r h) (response_follow m _)

/-- **Chunked round trip** (card: `chunked_decode_encode`). Non-empty
chunks, chunk-encoded, decode back to the same chunks, leaving what follows
the last chunk. -/
theorem chunked_decode_encode (cs : List ByteArray) (h : ∀ c ∈ cs, 0 < c.size) (rest : ByteArray) :
    decodeChunked (encodeChunked cs ++ rest) = some (cs, rest) :=
  Codec.decodeBytes_encodeBytes _ h trivial

end H1

end LeanHttpx
