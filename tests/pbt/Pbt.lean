import LeanHttpx
import Plausible

/-!
# Plausible properties

Randomised checks of properties tested rather than proved, and smoke tests
of proved theorems on the executable code.
-/

namespace Pbt

open LeanHttpx

/-- Base64 round trip on random byte lists (theorem `Base64.decodeList_encodeList`). -/
example : ∀ l : List UInt8, Base64.decodeList (Base64.encodeList l) = some l := by
  intro l; exact Base64.decodeList_encodeList l

#test ∀ s : String, (Text.utf8DecodeReplace s.toUTF8) = s

#test ∀ (k v : String), (QueryParams.parse (toString (QueryParams.ofList [("k" ++ k, v)]))).getList ("k" ++ k) = [v]

#test ∀ (a b : List (String × String)) (k : String),
  ((Headers.ofList a).update (Headers.ofList b)).getList k =
    (if (Headers.ofList b).contains k then (Headers.ofList b).getList k else (Headers.ofList a).getList k)

/-- `parse ∘ toString` fixes every parsed URL (on text). -/
def reparses (s : String) : Bool := match URL.parse s with
  | .ok u => (URL.parse u.toString).toOption.map (· == u) == some true
  | .error _ => true

#test ∀ s : String, reparses s = true

end Pbt
