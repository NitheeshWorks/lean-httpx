import LeanHttpx.DataTypes
import LeanHttpx.RepoImpl
import LeanHttpx.Specifications
import LeanHttpx.Proofs
import LeanHttpx.APIs
import LeanHttpx.Transport
import LeanHttpx.Transport2
import LeanHttpx.Proofs.Verified

/-!
# LeanHttpx

A clean-room port of httpx and httpcore to Lean 4: a sans-I/O HTTP client: URLs, headers, cookies, auth, redirects, the HTTP/1.1 codec, and HTTP/2 frames and HPACK, with proved round trips.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
