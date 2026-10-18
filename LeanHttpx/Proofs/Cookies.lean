import LeanHttpx.RepoImpl.Cookies

/-!
# Cookie matching and the jar's set/get law

* `cookie_match_domain_path`: a request carries exactly the stored cookies
  whose domain matches its host (the dotted domain is a suffix of the dotted
  host or effective host), whose path matches its path (RFC 6265 section
  5.1.4: equal, or a prefix ending at a `/`), and that `return_ok` accepts.
* `cookie_jar_set_get`: a cookie set under a name, domain and path is what
  `get` returns for them, whatever the jar held before.
-/

namespace LeanHttpx

open CookieJar

/-- RFC 6265 section 5.1.4, path-match, as a proposition. -/
def PathMatch (cookiePath reqPath : List Char) : Prop :=
  reqPath = cookiePath ∨ (cookiePath <+: reqPath ∧ (cookiePath.getLast? = some '/' ∨ reqPath[cookiePath.length]? = some '/'))

theorem pathReturnOk_iff (c r : String) : pathReturnOk c r = true ↔ PathMatch c.toList r.toList := by
  simp [pathReturnOk, PathMatch, List.isPrefixOf_iff_prefix]

/-- Domain match as a proposition: the dotted cookie domain is a suffix of
the dotted request host or effective request host. -/
def DomainMatch (domain : String) (url : URL) : Prop :=
  (dotted domain).toList <:+ (dotted (requestHost url)).toList ∨
    (dotted domain).toList <:+ (dotted (effRequestHost url)).toList

theorem domainReturnOk_iff (d : String) (url : URL) : domainReturnOk d url = true ↔ DomainMatch d url := by
  simp [domainReturnOk, DomainMatch, List.isSuffixOf_iff_suffix]

/-- **Cookie matching** (card: `cookie_match_domain_path`). -/
theorem cookie_match_domain_path (j : Cookies) (url : URL) (now : Int) (ck : Cookie) :
    ck ∈ j.cookiesForRequest url now ↔
      ck ∈ j.toList ∧ DomainMatch ck.domain url ∧ PathMatch ck.path.toList (requestPath url).toList ∧
        returnOk ck url now = true := by
  simp only [Cookies.cookiesForRequest, Cookies.matchesRequest, List.mem_filter, Bool.and_eq_true,
    domainReturnOk_iff, pathReturnOk_iff, Cookies.toList, and_assoc]

theorem key_eq_iff (ck : Cookie) (n d p : String) :
    ((ck.name == n && d == ck.domain) && p == ck.path) = (ck.key == (d, p, n)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, Cookie.key, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2.symm, h3.symm, h1⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h3, h1.symm⟩, h2.symm⟩

/-- `setCookie` leaves exactly one cookie under the new cookie's key. -/
theorem filter_key_setCookie (j : Cookies) (ck : Cookie) :
    (j.setCookie ck).jar.filter (·.key == ck.key) = [ck] := by
  simp only [Cookies.setCookie]
  generalize (j.jar.findIdx? (·.key == ck.key)).getD (Cookies.insertPos j.jar ck) = pos
  have none_in : ∀ x ∈ j.jar.filter (·.key != ck.key), (x.key == ck.key) = false := by
    intro x hx; simp only [List.mem_filter, bne_iff_ne, ne_eq] at hx; simpa using hx.2
  have h1 : (List.take pos (j.jar.filter (·.key != ck.key))).filter (·.key == ck.key) = [] :=
    List.filter_eq_nil_iff.mpr fun x hx => by simp [none_in x (List.mem_of_mem_take hx)]
  have h2 : (List.drop pos (j.jar.filter (·.key != ck.key))).filter (·.key == ck.key) = [] :=
    List.filter_eq_nil_iff.mpr fun x hx => by simp [none_in x (List.mem_of_mem_drop hx)]
  rw [List.filter_append, List.filter_cons, h1, h2]
  simp

/-- **Set, then get** (card: `cookie_jar_set_get`): whatever the jar held,
the value set under a name, domain and path is the one `get` finds there. -/
theorem cookie_jar_set_get (j : Cookies) (name value domain path : String) :
    (j.set name value domain path).get? name (some domain) (some path) = .ok (some value) := by
  let ck := Cookie.mk name (some value) domain (!domain.isEmpty) (domain.startsWith ".") path true false none true
  have hm : (j.set name value domain path).matching name (some domain) (some path) = [ck] := by
    have e := filter_key_setCookie j ck
    simp only [Cookies.set, Cookies.matching, Cookies.toList, Option.all_some]
    rw [List.filter_congr (fun x _ => key_eq_iff x name domain path)]
    exact e
  simp [Cookies.get?, hm, ck]

end LeanHttpx
