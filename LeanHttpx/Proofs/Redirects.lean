import LeanHttpx.RepoImpl.Redirects

/-!
# Redirects: method rewriting and the redirect bound

* `redirect_method_rewrite`: the method of a redirected request, in one
  equation; 307 and 308 keep method and body (`redirect_307_308_preserve`).
* `redirect_bounded`: a response from the redirect loop has at most
  `maxRedirects` responses before it (this is its type, `Bounded`), and a
  server that redirects every request makes the loop stop with
  `TooManyRedirects`, after exactly `maxRedirects + 1` requests.
-/

namespace LeanHttpx

/-- **Method rewriting** (card: `redirect_method_rewrite`). -/
theorem redirect_method_rewrite (s : Nat) (m : String) :
    redirectMethod s m =
      if ((s = 302 ∨ s = 303) ∧ m ≠ "HEAD") ∨ (s = 301 ∧ m = "POST") then "GET" else m := by
  unfold redirectMethod
  by_cases h3 : s = 303 <;> by_cases h2 : s = 302 <;> by_cases h1 : s = 301 <;>
    by_cases hh : m = "HEAD" <;> by_cases hp : m = "POST" <;> simp_all

/-- 307 and 308 redirects keep the method and the body. -/
theorem redirect_307_308_preserve {q q' : Request} {r : Response} {cs : Cookies} {now : Int}
    (hs : r.statusCode = 307 ∨ r.statusCode = 308) (h : buildRedirectRequest q r cs now = .ok q') :
    q'.method = q.method ∧ q'.content = q.content := by
  have hm : redirectMethod r.statusCode q.method = q.method := by
    rw [redirect_method_rewrite]; rcases hs with hs | hs <;> simp [hs]
  unfold buildRedirectRequest at h
  simp only [hm] at h
  cases hu : redirectUrl q r with
  | error e => simp [hu] at h; cases h
  | ok u =>
    simp only [hu] at h
    cases h
    simp

/-- A transport that answers every request with a followable redirect. -/
def AlwaysRedirects (send : Request → Except HTTPError Response) : Prop :=
  ∀ q, ∃ r, send q = .ok r ∧ r.hasRedirectLocation = true ∧
    ∀ (h : List Response) (cs : Cookies) (now : Int), ∃ q',
      buildRedirectRequest q { r with history := h } cs now = .ok q'

theorem redirectLoop_tooMany (send : Request → Except HTTPError Response) (hs : AlwaysRedirects send)
    (jar : Cookies × Int) (max : Nat) :
    ∀ (b : Nat) (q : Request) (history : List Response) (hh : history.length + b = max + 1),
      ∃ q', redirectLoop (m := Id) (fun q => pure (send q)) (pure jar) true max b q history hh =
        .error (.tooManyRedirects "Exceeded maximum allowed redirects." q')
  | 0, q, _, _ => ⟨q, rfl⟩
  | b + 1, q, history, hh => by
    obtain ⟨r, hr, hloc, hb⟩ := hs q
    obtain ⟨q', hq'⟩ := hb history jar.1 jar.2
    have hloc' : ({ r with history := history } : Response).hasRedirectLocation = true := hloc
    obtain ⟨q'', ih⟩ := redirectLoop_tooMany send hs jar max b q' (history ++ [{ r with history := history }])
      (by simp; omega)
    refine ⟨q'', ?_⟩
    simp only [redirectLoop, hr, pure_bind, hloc', Bool.not_true, Bool.false_eq_true, ite_false, hq',
      ite_true]
    exact ih

/-- **The redirect bound** (card: `redirect_bounded`). Every response the
loop returns has at most `maxRedirects` before it (the `Bounded` type), and
when every response redirects, following them ends in `TooManyRedirects`. -/
theorem redirect_bounded (send : Request → Except HTTPError Response) (hs : AlwaysRedirects send)
    (jar : Cookies × Int) (maxRedirects : Nat) (q : Request) :
    ∃ q', sendHandlingRedirects (m := Id) (fun q => pure (send q)) (pure jar) true maxRedirects q =
      .error (.tooManyRedirects "Exceeded maximum allowed redirects." q') := by
  unfold sendHandlingRedirects
  simp only [List.length_nil, Nat.zero_le, ↓reduceDIte]
  exact redirectLoop_tooMany send hs jar maxRedirects _ q [] _

/-- The bound, as a fact about any result of the loop. -/
theorem redirect_history_le {maxRedirects : Nat} (r : Bounded maxRedirects) :
    r.val.history.length ≤ maxRedirects := r.property

/-! ## The hypothesis of `redirect_bounded` is met

A server that answers every request with `302 Found` to `http://a/#f`. The
location is absolute and has a fragment, so the redirect URL does not depend
on the request, and building the next request always succeeds. -/

/-- The redirect every request gets. -/
def loopResponse : Response := { statusCode := 302, headers := ⟨[("Location", "http://a/#f")]⟩ }

/-- A server that redirects every request. -/
def redirectingServer : Request → Except HTTPError Response := fun _ => .ok loopResponse

/-- The parsed location: `http`, host `a`, path `/`, fragment `f`. -/
def loopRef : ParseResult := { scheme := "http", host := "a", path := "/", fragment := some "f" }

theorem loop_parse : (URL.parse "http://a/#f").toOption.map (·.ref) = some loopRef := by decide +kernel

theorem unquote_f : Text.unquote "f" = "f" := by
  simp [Text.unquote, String.contains_char_eq]

/-- **`redirect_bounded` is not vacuous**: `redirectingServer` satisfies
`AlwaysRedirects`, so for it the loop ends in `TooManyRedirects`. -/
theorem alwaysRedirects_redirectingServer : AlwaysRedirects redirectingServer := by
  intro q
  refine ⟨loopResponse, rfl, by decide +kernel, ?_⟩
  intro h cs now
  have hp := loop_parse
  cases hu : URL.parse "http://a/#f" with
  | error e => rw [hu] at hp; cases hp
  | ok u =>
    rw [hu] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at hp
    have hloc0 : loopResponse.headers.get? "Location" = some "http://a/#f" := by decide +kernel
    have hloc : ({ loopResponse with history := h } : Response).headers.get? "Location" = some "http://a/#f" :=
      hloc0
    have hs : u.scheme.isEmpty = false := by simp [URL.scheme, hp, loopRef]
    have hh : u.host.isEmpty = false := by simp [URL.host, hp, loopRef]
    have hr : u.isRelativeUrl = false := by
      simp [URL.isRelativeUrl, URL.isAbsoluteUrl, hp, loopRef]
    have hf : u.fragment.isEmpty = false := by simp [URL.fragment, hp, loopRef, unquote_f]
    unfold buildRedirectRequest redirectUrl
    simp only [hloc, Option.getD_some, hu, pure_bind, hs, hh, hr, hf, Bool.not_false, Bool.true_and,
      Bool.and_false, Bool.false_eq_true, ite_false, bind_pure]
    exact ⟨_, rfl⟩

theorem redirect_bounded_satisfiable :
    ∃ send, AlwaysRedirects send := ⟨redirectingServer, alwaysRedirects_redirectingServer⟩

end LeanHttpx
