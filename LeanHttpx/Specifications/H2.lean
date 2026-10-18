import LeanHttpx.RepoImpl.H2Frame
import LeanHttpx.RepoImpl.Hpack

/-!
# Specifications: HTTP/2 frames and HPACK

The frame round trip on any continuation of the buffer, and the HPACK round
trips: one block, without the dynamic table, and a sequence of blocks with
the table carried along on both sides. Proved in `Proofs/H2.lean` and
`Proofs/Hpack.lean`.
-/

namespace LeanHttpx.Spec

open H2 Hpack

/-- A valid frame whose payload fits the maximum frame size parses back from
its bytes, leaving what follows. -/
def FrameParsePrint : Prop :=
  ∀ (max : Nat) (f : Frame) (rest : ByteArray), f.ok = true → f.toRaw.payload.size ≤ max → max < 2 ^ 24 →
    parseFrame max (printFrame f ++ rest) = .done f rest

/-- Fields whose name and value fit HPACK's integers here (below 2^28 bytes). -/
def FieldsFit (fs : List HeaderField) : Prop := ∀ f ∈ fs, f.name.size < 2 ^ 28 ∧ f.value.size < 2 ^ 28

instance (fs : List HeaderField) : Decidable (FieldsFit fs) :=
  inferInstanceAs (Decidable (∀ f ∈ fs, f.name.size < 2 ^ 28 ∧ f.value.size < 2 ^ 28))

/-- An encoder in step with a decoder: the same table, well formed, and any
pending size update one the decoder allows. -/
def InStep (e : Encoder) (d : Decoder) : Prop :=
  e.table = d.table ∧ e.table.Wf ∧ d.maxTableSize < 2 ^ 28 ∧ ∀ n, e.pendingSize = some n → n ≤ d.maxTableSize

/-- One block decodes to the fields it encodes, within the header-list
limit, and the tables stay in step. -/
def HpackDecodeEncode : Prop :=
  ∀ (e : Encoder) (d : Decoder) (fs : List HeaderField), InStep e d → FieldsFit fs →
    listSize fs ≤ d.maxHeaderListSize →
    d.decode (e.encode fs).1 = .ok (fs, { d with table := (e.encode fs).2.table })

/-- Without the dynamic table, a block decodes and leaves the decoder as it was. -/
def HpackDecodeEncodeStatic : Prop :=
  ∀ (d : Decoder) (fs : List HeaderField), FieldsFit fs → listSize fs ≤ d.maxHeaderListSize →
    d.decode (encodeStatic fs) = .ok (fs, d)

/-- A sequence of blocks, the table carried along on both sides, decodes to
the sequence of header lists. -/
def HpackDecodeEncodeSeq : Prop :=
  ∀ (e : Encoder) (d : Decoder) (ls : List (List HeaderField)), InStep e d →
    (∀ fs ∈ ls, FieldsFit fs ∧ listSize fs ≤ d.maxHeaderListSize) →
    d.decodeAll (e.encodeAll ls).1 = .ok (ls, { d with table := (e.encodeAll ls).2.table })

end LeanHttpx.Spec
