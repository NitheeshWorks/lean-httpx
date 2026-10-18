import LeanHttpx.RepoImpl.URLOps

/-!
# `URL.join` on the RFC 3986 examples

RFC 3986 section 5.4 lists the resolution of 42 references against the base
`http://a/b/c/d;p?q`: 23 normal examples (5.4.1) and 19 abnormal ones
(5.4.2). `url_join_rfc3986` checks all of them by evaluation in the kernel
(`decide +kernel`, no extra axioms). For `http:g` the RFC permits two
answers; httpx (and this port) gives the non-strict `http://a/b/c/g`.
-/

namespace LeanHttpx

/-- `URL(base).join(ref)` prints as `expected`. -/
def joinsTo (base ref expected : String) : Bool :=
  match URL.parse base with
  | .ok u => match u.join ref with
    | .ok v => v.toString == expected
    | .error _ => false
  | .error _ => false

/-- RFC 3986 sections 5.4.1 and 5.4.2. -/
def rfc3986Examples : List (String × String) := [
  ("g:h", "g:h"), ("g", "http://a/b/c/g"), ("./g", "http://a/b/c/g"), ("g/", "http://a/b/c/g/"),
  ("/g", "http://a/g"), ("//g", "http://g"), ("?y", "http://a/b/c/d;p?y"), ("g?y", "http://a/b/c/g?y"),
  ("#s", "http://a/b/c/d;p?q#s"), ("g#s", "http://a/b/c/g#s"), ("g?y#s", "http://a/b/c/g?y#s"),
  (";x", "http://a/b/c/;x"), ("g;x", "http://a/b/c/g;x"), ("g;x?y#s", "http://a/b/c/g;x?y#s"),
  ("", "http://a/b/c/d;p?q"), (".", "http://a/b/c/"), ("./", "http://a/b/c/"), ("..", "http://a/b/"),
  ("../", "http://a/b/"), ("../g", "http://a/b/g"), ("../..", "http://a/"), ("../../", "http://a/"),
  ("../../g", "http://a/g"),
  ("../../../g", "http://a/g"), ("../../../../g", "http://a/g"), ("/./g", "http://a/g"),
  ("/../g", "http://a/g"), ("g.", "http://a/b/c/g."), (".g", "http://a/b/c/.g"),
  ("g..", "http://a/b/c/g.."), ("..g", "http://a/b/c/..g"), ("./../g", "http://a/b/g"),
  ("./g/.", "http://a/b/c/g/"), ("g/./h", "http://a/b/c/g/h"), ("g/../h", "http://a/b/c/h"),
  ("g;x=1/./y", "http://a/b/c/g;x=1/y"), ("g;x=1/../y", "http://a/b/c/y"),
  ("g?y/./x", "http://a/b/c/g?y/./x"), ("g?y/../x", "http://a/b/c/g?y/../x"),
  ("g#s/./x", "http://a/b/c/g#s/./x"), ("g#s/../x", "http://a/b/c/g#s/../x"),
  ("http:g", "http://a/b/c/g")]

/-- **Reference resolution** (card: `url_join_rfc3986`): `join` gives the
RFC's answer for every example of RFC 3986 section 5.4. -/
theorem url_join_rfc3986 :
    rfc3986Examples.all (fun e => joinsTo "http://a/b/c/d;p?q" e.1 e.2) = true := by
  decide +kernel

end LeanHttpx
