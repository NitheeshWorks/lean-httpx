import LeanHttpx.RepoImpl.URL
import LeanHttpx.RepoImpl.Lists

/-!
# Splitting a printed URL gives back its parts

The two splitters of the URL parser, `splitUrl` (upstream `URL_REGEX`) and
`splitAuth` (upstream `AUTHORITY_REGEX`), invert the printers `printRaw` and
`printAuth` on parts that respect the delimiters. Both proofs come from two
general facts about `takeWhile` and `dropWhile` on a concatenation whose
second half starts with a stop character (`takeWhile_append_stop`,
`dropWhile_append_stop`).
-/

namespace LeanHttpx

open Chars URLParse

namespace URLParse

/-! ## The top-level split -/

/-- The parts of a URL that print and split back unchanged: each part avoids
the delimiters that end it, an authority is followed by `/` or nothing, a
path without authority does not start with `//`, and a URL without scheme
and authority has no path prefix that reads as a scheme. -/
structure RawParts.Ok (p : RawParts) : Prop where
  scheme : p.scheme = [] ∨ (p.scheme.head?.map Char.isAlpha = some true ∧ ∀ c ∈ p.scheme, isSchemeChar c = true)
  authority : ∀ c ∈ p.authority, notAuthEnd c = true
  path : ∀ c ∈ p.path, notPathEnd c = true
  query : ∀ q, p.query = some q → ∀ c ∈ q, (c != '#') = true
  pathStart : p.authority ≠ [] → p.path = [] ∨ p.path.head? = some '/'
  noSlashes : p.authority = [] → p.path.take 2 ≠ ['/', '/']
  noScheme : p.scheme = [] → p.authority = [] → schemeOf p.path = none

/-- What follows the path: the printed query and fragment. -/
def printTail (p : RawParts) : List Char :=
  (match p.query with | some q => '?' :: q | none => []) ++
  (match p.fragment with | some f => '#' :: f | none => [])

theorem printRaw_eq (p : RawParts) : printRaw p =
    (if p.scheme.isEmpty then [] else p.scheme ++ [':']) ++
    ((if p.authority.isEmpty then [] else '/' :: '/' :: p.authority) ++ (p.path ++ printTail p)) := by
  simp only [printRaw, printTail, List.append_assoc]; rfl

theorem tail_stops (p : RawParts) (f : Char → Bool) (h1 : f '?' = false) (h2 : f '#' = false) :
    StopsAt f (printTail p) := by
  unfold printTail
  cases p.query with
  | some q => exact stopsAt_append (stopsAt_cons h1) (by simp)
  | none =>
    cases p.fragment with
    | some _ => exact stopsAt_cons h2
    | none => exact stopsAt_nil f

theorem schemeOf_stop {l : List Char} (h : ∀ c, l.head? = some c → c ≠ ':' ∧ c.isAlpha = false) :
    schemeOf l = none := by
  cases l with
  | nil => rfl
  | cons c l =>
    have := h c rfl
    simp [schemeOf, this.1, this.2]

theorem afterColon?_append {l r : List Char} (h : l ≠ []) : afterColon? (l ++ r) = (afterColon? l).map (· ++ r) := by
  cases l with
  | nil => exact absurd rfl h
  | cons c l => by_cases hc : c = ':' <;> simp [afterColon?, hc]

theorem stop_of_tail {r : List Char} (hr : StopsAt notPathEnd r) (c : Char) (hc : r.head? = some c) :
    c ≠ ':' ∧ c.isAlpha = false ∧ isSchemeChar c = false ∧ notAuthEnd c = false := by
  have := hr c hc
  simp only [notPathEnd, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at this
  rcases this with rfl | rfl <;> decide

/-- A path that does not start with a scheme still does not when the query
or fragment follows it. -/
theorem schemeOf_append {l r : List Char} (hl : schemeOf l = none) (hp : ∀ c ∈ l, notPathEnd c = true)
    (hr : StopsAt notPathEnd r) : schemeOf (l ++ r) = none := by
  cases l with
  | nil =>
    exact schemeOf_stop fun c hc => ⟨(stop_of_tail hr c hc).1, (stop_of_tail hr c hc).2.1⟩
  | cons c l =>
    by_cases hc : c = ':'
    · simp [schemeOf, hc] at hl
    by_cases ha : c.isAlpha = true
    · simp only [schemeOf, hc, ite_false, ha, ite_true, Option.map_eq_none_iff, List.cons_append] at hl ⊢
      by_cases hd : (c :: l).dropWhile isSchemeChar = []
      · have hall : ∀ x ∈ c :: l, isSchemeChar x = true := by
          intro x hx
          exact all_of_dropWhile_eq_nil hd x hx
        rw [← List.cons_append, dropWhile_append_stop hall
          (fun d hd => (stop_of_tail hr d hd).2.2.1)]
        cases r with
        | nil => rfl
        | cons d r => simp [afterColon?, (stop_of_tail hr d rfl).1]
      · rw [← List.cons_append, dropWhile_append_of_ne_nil hd, afterColon?_append hd, hl]; rfl
    · simp [schemeOf, hc, ha]

theorem splitScheme_print (p : RawParts) (ho : p.Ok) (rest : List Char)
    (hrest : p.scheme = [] → schemeOf rest = none) :
    splitScheme ((if p.scheme.isEmpty then [] else p.scheme ++ [':']) ++ rest) = (p.scheme, rest) := by
  rcases ho.scheme with h | ⟨hh, hall⟩
  · simp [h, splitScheme, hrest h]
  · obtain ⟨c, cs, hcs⟩ : ∃ c cs, p.scheme = c :: cs := by
      cases h : p.scheme with
      | nil => simp [h] at hh
      | cons c cs => exact ⟨c, cs, rfl⟩
    have hca : c.isAlpha = true := by simpa [hcs] using hh
    have hc : c ≠ ':' := by intro h; subst h; simp at hca
    have hstop : StopsAt isSchemeChar (':' :: rest) := stopsAt_cons (by decide)
    have hall' : ∀ x ∈ c :: cs, isSchemeChar x = true := by rw [← hcs]; exact hall
    simp only [hcs, List.isEmpty_cons, Bool.false_eq_true, ite_false, splitScheme, schemeOf,
      List.cons_append, hc, hca, ite_true, List.append_assoc, List.singleton_append, List.nil_append]
    rw [← List.cons_append, dropWhile_append_stop hall' hstop, takeWhile_append_stop hall' hstop]
    rfl

theorem splitAuthority_of_take {l : List Char} (h : l.take 2 ≠ ['/', '/']) :
    splitAuthority l = ([], l) := by
  unfold splitAuthority
  split
  · simp at h
  · rfl

theorem take_two_append {l r : List Char} (hl : l.take 2 ≠ ['/', '/']) (hr : StopsAt (· == '/') r) :
    (l ++ r).take 2 ≠ ['/', '/'] := by
  match l, r with
  | [], [] => simp
  | [], c :: r => have := hr c rfl; simp at this; simp [this]
  | [a], [] => simp
  | [a], c :: r => have := hr c rfl; simp at this; simp [this]
  | a :: b :: l, r => simpa using hl

theorem splitAuthority_print (p : RawParts) (ho : p.Ok) :
    splitAuthority ((if p.authority.isEmpty then [] else '/' :: '/' :: p.authority) ++ (p.path ++ printTail p)) =
      (p.authority, p.path ++ printTail p) := by
  by_cases ha : p.authority = []
  · simp only [ha, List.isEmpty_nil, ite_true, List.nil_append]
    exact splitAuthority_of_take (take_two_append (ho.noSlashes ha) (tail_stops p _ rfl rfl))
  · have htail : StopsAt notAuthEnd (p.path ++ printTail p) := by
      apply stopsAt_append
      · rcases ho.pathStart ha with h | h
        · rw [h]; exact stopsAt_nil _
        · intro c hc; rw [h] at hc; cases hc; rfl
      · intro _; exact tail_stops p _ rfl rfl
    have hne : p.authority.isEmpty = false := by simpa using ha
    simp only [hne, Bool.false_eq_true, ite_false, List.cons_append, splitAuthority]
    rw [takeWhile_append_stop ho.authority htail, dropWhile_append_stop ho.authority htail]

theorem splitQuery_tail (p : RawParts) (ho : p.Ok) :
    splitQuery (printTail p) = (p.query, match p.fragment with | some f => '#' :: f | none => []) := by
  unfold printTail
  have hf : StopsAt (· != '#') (match p.fragment with | some f => '#' :: f | none => []) := by
    cases p.fragment with
    | some f => exact stopsAt_cons rfl
    | none => exact stopsAt_nil _
  cases hq : p.query with
  | some q =>
    have hq' := ho.query q hq
    simp only [splitQuery, List.cons_append]
    rw [takeWhile_append_stop hq' hf, dropWhile_append_stop hq' hf]
  | none =>
    simp only [List.nil_append]
    cases p.fragment with
    | some f => rfl
    | none => rfl

theorem splitFragment_print (f : Option (List Char)) :
    splitFragment (match f with | some f => '#' :: f | none => []) = f := by
  cases f <;> rfl

/-- **The top-level split inverts printing** on parts that respect the
delimiters. -/
theorem splitUrl_printRaw (p : RawParts) (ho : p.Ok) : splitUrl (printRaw p) = p := by
  have hrest : p.scheme = [] → schemeOf ((if p.authority.isEmpty then [] else '/' :: '/' :: p.authority) ++
      (p.path ++ printTail p)) = none := by
    intro hs
    by_cases ha : p.authority = []
    · simp only [ha, List.isEmpty_nil, ite_true, List.nil_append]
      exact schemeOf_append (ho.noScheme hs ha) ho.path (tail_stops p _ rfl rfl)
    · have hne : p.authority.isEmpty = false := by simpa using ha
      simp only [hne, Bool.false_eq_true, ite_false]
      exact schemeOf_stop fun c hc => by simp at hc; subst hc; decide
  have htail : StopsAt notPathEnd (printTail p) := tail_stops p _ rfl rfl
  rw [printRaw_eq]
  simp only [splitUrl, splitScheme_print p ho _ hrest, splitAuthority_print p ho,
    takeWhile_append_stop ho.path htail, dropWhile_append_stop ho.path htail, splitQuery_tail p ho,
    splitFragment_print]

/-! ## The authority split -/

/-- The printed port: `:` and digits, or nothing. -/
def printPort (port : Option Nat) : List Char :=
  match port with | some n => ':' :: decimal n | none => []

/-- The port text the splitter reads back. -/
def portText (port : Option Nat) : List Char :=
  match port with | some n => decimal n | none => []

theorem decimal_mem (n : Nat) (c : Char) (h : c ∈ decimal n) : c.isDigit = true :=
  Keel.Codec.decimal_isDigit n c h

theorem digit_ne {c : Char} (h : c.isDigit = true) :
    c ≠ '@' ∧ c ≠ ']' ∧ c ≠ ':' ∧ c ≠ '[' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro rfl; simp at h)

theorem printPort_mem {port : Option Nat} {c : Char} (h : c ∈ printPort port) :
    c ≠ '@' ∧ c ≠ ']' ∧ c ≠ '[' := by
  cases port with
  | none => simp [printPort] at h
  | some n =>
    simp only [printPort, List.mem_cons] at h
    rcases h with rfl | h
    · decide
    · have := digit_ne (decimal_mem n c h); exact ⟨this.1, this.2.1, this.2.2.2⟩

theorem hostChar_ne {c : Char} (h : hostChar c = true) : c ≠ '@' ∧ c ≠ '[' ∧ c ≠ ']' := by
  simp only [hostChar, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1.1.1.2, h.1.2, h.2⟩

theorem printHost_mem {h : List Char} (hh : ∀ c ∈ h, hostChar c = true) {c : Char}
    (hc : c ∈ printHost h) : c ≠ '@' := by
  unfold printHost at hc
  split at hc
  · simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc | rfl
    · decide
    · exact (hostChar_ne (hh _ hc)).1
    · decide
  · exact (hostChar_ne (hh _ hc)).1

theorem printAuth_eq (ui host : List Char) (port : Option Nat) :
    printAuth ui host port = (if ui.isEmpty then [] else ui ++ ['@']) ++ (printHost host ++ printPort port) := by
  simp only [printAuth, printPort, List.append_assoc]; rfl

/-- The split at the last `@` of a printed authority. -/
theorem splitUserinfo_print (ui host : List Char) (port : Option Nat) (hui : ∀ c ∈ ui, c ≠ '@')
    (hh : ∀ c ∈ host, hostChar c = true) :
    (if (printAuth ui host port).contains '@' then
      ((((printAuth ui host port).reverse.dropWhile (· != '@')).tail.reverse,
        ((printAuth ui host port).reverse.takeWhile (· != '@')).reverse))
      else ([], printAuth ui host port)) = (ui, printHost host ++ printPort port) := by
  have hrest : ∀ c ∈ printHost host ++ printPort port, c ≠ '@' := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact printHost_mem hh hc
    · exact (printPort_mem hc).1
  rw [printAuth_eq]
  by_cases hu0 : ui = []
  · subst hu0
    have : (printHost host ++ printPort port).contains '@' = false := by
      simpa using fun h => hrest '@' h rfl
    simp only [List.isEmpty_nil, ite_true, List.nil_append, this, Bool.false_eq_true, ite_false]
  · have hne : ui.isEmpty = false := by simpa using hu0
    have hall : ∀ c ∈ (printHost host ++ printPort port).reverse, (c != '@') = true := by
      intro c hc; simpa using hrest c (List.mem_reverse.mp hc)
    have hstop : StopsAt (· != '@') ('@' :: ui.reverse) := stopsAt_cons (by decide)
    have hrev : ((ui ++ ['@']) ++ (printHost host ++ printPort port)).reverse =
        (printHost host ++ printPort port).reverse ++ '@' :: ui.reverse := by
      simp [List.reverse_append]
    have hcont : ((ui ++ ['@']) ++ (printHost host ++ printPort port)).contains '@' = true := by simp
    simp only [hne, Bool.false_eq_true, ite_false]
    rw [if_pos hcont, hrev, takeWhile_append_stop hall hstop, dropWhile_append_stop hall hstop]
    simp

/-- The port text after the host: an optional `:` dropped. -/
theorem portOf_printPort (port : Option Nat) :
    (match printPort port with | ':' :: p => p | p => p) = portText port := by
  cases port with
  | none => rfl
  | some n => rfl

theorem splitAuth_printAuth (ui host : List Char) (port : Option Nat) (hui : ∀ c ∈ ui, c ≠ '@')
    (hh : ∀ c ∈ host, hostChar c = true) :
    splitAuth (printAuth ui host port) = (ui, printHost host, portText port) := by
  unfold splitAuth
  simp only [splitUserinfo_print ui host port hui hh]
  by_cases hcol : ':' ∈ host
  · have hpH : printHost host = '[' :: host ++ [']'] := by simp [printHost, hcol]
    have hcond : ((printHost host ++ printPort port).head? == some '[' &&
        (printHost host ++ printPort port).contains ']') = true := by
      simp [hpH]
    have hallP : ∀ c ∈ (printPort port).reverse, (c != ']') = true := by
      intro c hc; simpa using (printPort_mem (List.mem_reverse.mp hc)).2.1
    have hstop : StopsAt (· != ']') (']' :: (host.reverse ++ ['['])) := stopsAt_cons (by decide)
    have hrev : (printHost host ++ printPort port).reverse =
        (printPort port).reverse ++ ']' :: (host.reverse ++ ['[']) := by
      simp [hpH, List.reverse_append]
    rw [if_pos hcond, hrev, takeWhile_append_stop hallP hstop, dropWhile_append_stop hallP hstop]
    simp only [List.reverse_reverse, List.reverse_cons, List.reverse_append, List.reverse_nil,
      List.nil_append, hpH, List.cons_append, List.singleton_append, List.append_assoc]
    exact congrArg (fun x => (ui, _, x)) (portOf_printPort port)
  · have hpH : printHost host = host := by simp [printHost, hcol]
    have hnb : ((host ++ printPort port).head? == some '[') = false := by
      cases host with
      | cons c t => simp [(hostChar_ne (hh c (by simp))).2.1]
      | nil => cases port <;> simp [printPort]
    have hallH : ∀ c ∈ host, (c != ':') = true := by
      intro c hc; simp only [bne_iff_ne, ne_eq]; rintro rfl; exact hcol hc
    have hstop : StopsAt (· != ':') (printPort port) := by
      cases port with
      | none => exact stopsAt_nil _
      | some n => exact stopsAt_cons (by decide)
    rw [hpH]
    simp only [hnb, Bool.false_and, Bool.false_eq_true, ite_false]
    rw [takeWhile_append_stop hallH hstop, dropWhile_append_stop hallH hstop]
    exact congrArg (fun x => (ui, host, x)) (portOf_printPort port)

end URLParse

end LeanHttpx
