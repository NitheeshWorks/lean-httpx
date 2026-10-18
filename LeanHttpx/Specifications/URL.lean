import LeanHttpx.RepoImpl.URL

/-!
# Specifications: URLs

The URL round trip, stated in `Prop`. Proved in `Proofs/URL.lean`.
-/

namespace LeanHttpx.Spec

/-- Every URL within upstream's length limit prints to text that parses back
to it. -/
def URLParsePrint : Prop :=
  ∀ u : URL, u.toString.length ≤ URLParse.maxUrlLength → URL.parse u.toString = .ok u

end LeanHttpx.Spec
