import LeanHttpx.RepoImpl.Headers

/-!
# Header merge precedence

`Headers.update` is how a client merges its default headers with a
request's. The theorem: for every name, the merged headers carry the
request's values if it has any, and the client's otherwise.
-/

namespace LeanHttpx

namespace Headers

theorem contains_iff (h : Headers) (k : String) :
    h.contains k = true ↔ ∃ p ∈ h.raw, asciiLower p.1 = asciiLower k := by
  simp [contains, List.any_eq_true]

/-- `contains` depends only on the lower-cased name. -/
theorem contains_congr (h : Headers) {k k' : String} (e : asciiLower k = asciiLower k') :
    h.contains k = h.contains k' := by
  simp [contains, e]

/-- **Header merge precedence** (card: `headers_merge_precedence`). After
`base.update override`, the values of any name are `override`'s when it
has that name, and `base`'s otherwise. -/
theorem headers_merge_precedence (base override : Headers) (k : String) :
    (base.update override).getList k =
      if override.contains k then override.getList k else base.getList k := by
  unfold getList matching update
  simp only [Bool.false_eq_true, ite_false, List.filter_append, List.map_append, List.filter_filter]
  split
  · rename_i hk
    have : List.filter (fun p => (asciiLower p.1 == asciiLower k) && !override.contains p.1) base.raw = [] := by
      rw [List.filter_eq_nil_iff]
      intro p _ hp
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
      rw [contains_congr override hp.1, hk] at hp
      exact absurd hp.2 (by simp)
    rw [this]
    simp
  · rename_i hk
    have h1 : List.filter (fun p => asciiLower p.1 == asciiLower k) override.raw = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp e
      exact hk ((contains_iff _ _).2 ⟨p, hp, by simpa using e⟩)
    have h2 : List.filter (fun p => (asciiLower p.1 == asciiLower k) && !override.contains p.1) base.raw =
        List.filter (fun p => asciiLower p.1 == asciiLower k) base.raw := by
      apply List.filter_congr
      intro p _
      by_cases e : asciiLower p.1 = asciiLower k
      · rw [contains_congr override e]; simp [hk, e]
      · simp [e]
    rw [h1, h2]
    simp

end Headers

end LeanHttpx
