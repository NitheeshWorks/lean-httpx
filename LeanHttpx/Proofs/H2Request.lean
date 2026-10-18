import LeanHttpx.RepoImpl.H2Request
import LeanHttpx.Proofs.Hpack

/-!
# Proofs: a request on HTTP/2 carries no connection-specific field

`requestFields` never yields one (RFC 9113 section 8.2.2), and so a server
decoding the block we send for a request finds none.
-/

namespace LeanHttpx

namespace H2

open Hpack

theorem requestFields_clean (r : Request) : ∀ f ∈ requestFields r, connectionSpecific f = false := by
  intro f hf
  simp only [requestFields, List.mem_filter] at hf
  simpa using hf.2

/-- **`h2_request_fields_clean`**: what a server decodes from the block we
encode for a request has no connection-specific field. -/
theorem h2_request_fields_clean (r : Request) (e : Encoder) (d : Decoder)
    (htab : e.table = d.table) (hwf : e.table.Wf) (hlim : d.maxTableSize < 2 ^ 28)
    (hpend : ∀ n, e.pendingSize = some n → n ≤ d.maxTableSize)
    (hs : ∀ f ∈ requestFields r, f.name.size < 2 ^ 28 ∧ f.value.size < 2 ^ 28)
    (hl : listSize (requestFields r) ≤ d.maxHeaderListSize)
    (fs : List HeaderField) (d' : Decoder) (hdec : d.decode (e.encode (requestFields r)).1 = .ok (fs, d')) :
    ∀ f ∈ fs, connectionSpecific f = false := by
  rw [hpack_decode_encode e d _ htab hwf hlim hpend hs hl] at hdec
  cases hdec
  exact requestFields_clean r

end H2

end LeanHttpx
