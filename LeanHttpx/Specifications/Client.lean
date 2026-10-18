import LeanHttpx.RepoImpl.Redirects
import LeanHttpx.RepoImpl.Auth

/-!
# Specifications: headers, cookies, redirects, authentication

The client-side properties, in `Prop`. Proved in `Proofs/Headers.lean`,
`Proofs/Cookies.lean`, `Proofs/Redirects.lean` and `Proofs/Auth.lean`.
-/

namespace LeanHttpx.Spec

open CookieJar

/-- Request headers override client headers name by name. -/
def HeadersMergePrecedence : Prop :=
  ∀ (base override : Headers) (k : String),
    (base.update override).getList k = if override.contains k then override.getList k else base.getList k

/-- A request carries exactly the stored cookies that domain-match,
path-match (RFC 6265 section 5.1.4) and that `return_ok` accepts. -/
def CookieMatch : Prop :=
  ∀ (j : Cookies) (url : URL) (now : Int) (ck : Cookie),
    ck ∈ j.cookiesForRequest url now ↔
      ck ∈ j.toList ∧
      ((dotted ck.domain).toList <:+ (dotted (requestHost url)).toList ∨
        (dotted ck.domain).toList <:+ (dotted (effRequestHost url)).toList) ∧
      ((requestPath url).toList = ck.path.toList ∨
        (ck.path.toList <+: (requestPath url).toList ∧
          (ck.path.toList.getLast? = some '/' ∨ (requestPath url).toList[ck.path.toList.length]? = some '/'))) ∧
      returnOk ck url now = true

/-- A cookie set under a name, domain and path is what `get` finds there. -/
def CookieSetGet : Prop :=
  ∀ (j : Cookies) (name value domain path : String),
    (j.set name value domain path).get? name (some domain) (some path) = .ok (some value)

/-- The redirect method rule of RFC 9110 section 15.4 as httpx applies it. -/
def RedirectMethodRewrite : Prop :=
  ∀ (s : Nat) (m : String), redirectMethod s m =
    if ((s = 302 ∨ s = 303) ∧ m ≠ "HEAD") ∨ (s = 301 ∧ m = "POST") then "GET" else m

/-- Following redirects from a server that always redirects ends in
`TooManyRedirects`. -/
def RedirectBounded : Prop :=
  ∀ (send : Request → Except HTTPError Response), (∀ q, ∃ r, send q = .ok r ∧ r.hasRedirectLocation = true ∧
    ∀ (h : List Response) (cs : Cookies) (now : Int), ∃ q',
      buildRedirectRequest q { r with history := h } cs now = .ok q') →
    ∀ (jar : Cookies × Int) (maxRedirects : Nat) (q : Request), ∃ q',
      sendHandlingRedirects (m := Id) (fun q => pure (send q)) (pure jar) true maxRedirects q =
        .error (.tooManyRedirects "Exceeded maximum allowed redirects." q')

/-- The hypothesis of `RedirectBounded` can be met: some server redirects
every request in a way the client can follow. -/
def RedirectBoundedSatisfiable : Prop :=
  ∃ (send : Request → Except HTTPError Response), ∀ q, ∃ r, send q = .ok r ∧ r.hasRedirectLocation = true ∧
    ∀ (h : List Response) (cs : Cookies) (now : Int), ∃ q',
      buildRedirectRequest q { r with history := h } cs now = .ok q'

/-- Basic credentials decode back from the header. -/
def BasicAuthHeader : Prop :=
  ∀ (u p : String), ':' ∉ u.toList → parseBasicAuth (basicAuthHeader u p) = some (u, p)

end LeanHttpx.Spec
