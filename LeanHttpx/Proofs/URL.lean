import LeanHttpx.Proofs.URLSplit

/-!
# URL round trip: `URL.parse u.toString = .ok u`

Every URL prints to a string that parses back to it. The proof follows the
parser's stages: the input checks pass on printed text (it is graphic ASCII),
the two splitters invert the printers (`Proofs/URLSplit.lean`), and each
normaliser is the identity on a canonical component (`encodeHost_printHost`,
`normalizePort_portText`, `quote_of_all`, `normalizePath_of_noDots`).

The one hypothesis is upstream's length limit: a URL longer than 65536
characters is rejected on parsing, so its printed form must fit.
-/

namespace LeanHttpx

open Chars URLParse

namespace URLParse

/-! ## Membership through `splitOn` -/

theorem mem_intercalate {sep : List Char} : ∀ {ls : List (List Char)} {c : Char},
    c ∈ sep.intercalate ls → c ∈ sep ∨ ∃ p ∈ ls, c ∈ p
  | [], c, h => by simp at h
  | [l], c, h => by simp at h; exact Or.inr ⟨l, by simp, h⟩
  | l :: l' :: ls, c, h => by
    rw [List.intercalate_cons_cons] at h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · exact Or.inr ⟨l, by simp, h⟩
    · exact Or.inl h
    · rcases mem_intercalate h with h | ⟨p, hp, hc⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hc⟩

theorem mem_splitOn (sep : Char) {l : List Char} {c : Char} (h : c ∈ l) :
    c = sep ∨ ∃ p ∈ l.splitOn sep, c ∈ p := by
  rw [← List.intercalate_splitOn (xs := l) sep] at h
  rcases mem_intercalate h with h | h
  · simp at h; exact Or.inl h
  · exact Or.inr h

/-! ## Character facts -/

theorem ipv4Style_chars {l : List Char} (h : ipv4Style l = true) :
    ∀ c ∈ l, c.isDigit = true ∨ c = '.' := by
  intro c hc
  rcases mem_splitOn '.' hc with h' | ⟨p, hp, hcp⟩
  · exact Or.inr h'
  · simp only [ipv4Style, splitAt, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff] at h
    exact Or.inl ((h.2 p hp).2 c hcp)

theorem ipv4Style_bracket (h : List Char) : ipv4Style ('[' :: (h ++ [']'])) = false := by
  cases hc : ipv4Style ('[' :: (h ++ [']']))
  · rfl
  · have := ipv4Style_chars hc '[' (by simp); simp at this

theorem isGraphic_not_control {c : Char} (h : isGraphic c = true) : isAsciiControl c = false := by
  simp only [isGraphic, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isAsciiControl, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega

theorem pathSafe_graphic {c : Char} (h : pathSafe c = true) : isGraphic c = true := by
  simp only [pathSafe, querySafe, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1

theorem querySafe_graphic {c : Char} (h : querySafe c = true) : isGraphic c = true := by
  simp only [querySafe, Bool.and_eq_true] at h; exact h.1.1.1.1

theorem fragSafe_graphic {c : Char} (h : fragSafe c = true) : isGraphic c = true := by
  simp only [fragSafe, Bool.and_eq_true] at h; exact h.1.1.1.1

theorem userinfoSafe_pathSafe {c : Char} (h : userinfoSafe c = true) : pathSafe c = true := by
  simp only [userinfoSafe, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1.1

theorem hostChar_graphic {c : Char} (h : hostChar c = true) : isGraphic c = true := by
  simp only [hostChar, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1

theorem alnum_range {c : Char} (h : c.isAlphanum = true) : 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x7A := by
  simp [Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit,
    UInt32.le_iff_toNat_le] at h
  omega

theorem digit_range {c : Char} (h : c.isDigit = true) : 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 := by
  simp [Char.isDigit, UInt32.le_iff_toNat_le] at h
  omega

theorem schemeChar_graphic {c : Char} (h : isSchemeChar c = true) : isGraphic c = true := by
  simp only [isSchemeChar, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | rfl) | rfl) | rfl
  · have := alnum_range h
    simp only [isGraphic, Bool.and_eq_true, decide_eq_true_eq]; omega
  all_goals decide

theorem digit_graphic {c : Char} (h : c.isDigit = true) : isGraphic c = true := by
  have := digit_range h
  simp only [isGraphic, Bool.and_eq_true, decide_eq_true_eq]; omega

/-! ## Each normaliser fixes a canonical component -/

theorem map_toLower_of_all {l : List Char} (h : ∀ c ∈ l, (c.toLower == c) = true) :
    l.map Char.toLower = l := by
  conv => rhs; rw [← List.map_id l]
  exact List.map_congr_left fun c hc => by simpa using h c hc

theorem encodeHost_printHost {h : List Char} (hc : hostCanonical h = true) :
    encodeHost (printHost h) = .ok h := by
  simp only [hostCanonical, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
    List.isEmpty_iff, beq_iff_eq, Bool.not_eq_true'] at hc
  obtain ⟨hch, hc⟩ := hc
  by_cases hcol : ':' ∈ h
  · have h6 : validIPv6 h = true := by
      rcases hc with ((h0 | ⟨h4, -⟩) | ⟨-, h6⟩) | ⟨⟨-, hs⟩, -⟩
      · subst h0; simp at hcol
      · have := ipv4Style_chars h4 ':' hcol; simp at this
      · exact h6
      · have := hs ':' hcol; simp [hostSafe, isUnreserved, isSubDelim] at this
    have hpH : printHost h = '[' :: h ++ [']'] := by simp [printHost, hcol]
    have hlast : ('[' :: (h ++ [']'])).getLast? = some ']' := by
      show (('[' :: h) ++ [']']).getLast? = some ']'
      exact List.getLast?_concat
    rw [hpH]
    unfold encodeHost
    simp [ipv4Style_bracket, h6, hlast]
  · have hpH : printHost h = h := by simp [printHost, hcol]
    rw [hpH]
    unfold encodeHost
    rcases hc with ((h0 | ⟨h4, h4'⟩) | ⟨h6, -⟩) | ⟨⟨h4, hs⟩, hl⟩
    · subst h0; rfl
    · have hne : h.isEmpty = false := by
        cases h with
        | nil => simp [ipv4Style, List.splitOn] at h4
        | cons _ _ => rfl
      simp [hne, h4, h4']
    · exact absurd (by simpa using h6) hcol
    · by_cases hne : h = []
      · subst hne; rfl
      have hnb : (h.head? == some '[') = false := by
        match h, hch with
        | [], _ => rfl
        | c :: t, hch => simp [(URLParse.hostChar_ne (hch c (by simp))).2.1]
      have hascii : h.all (·.toNat < 128) = true := by
        simp only [List.all_eq_true, decide_eq_true_eq]
        intro c hc'
        have := hostChar_graphic (hch c hc')
        simp only [isGraphic, Bool.and_eq_true, decide_eq_true_eq] at this
        omega
      have hq : quote hostSafe (lowerHost h) = h := by rw [hl]; exact quote_of_all hs
      simp [List.isEmpty_iff, hne, h4, hnb, hascii, hq]

theorem normalizePort_portText {port : Option Nat} {scheme : List Char}
    (h : (port.isNone || port != defaultPort scheme) = true) :
    normalizePort (portText port) scheme = .ok port := by
  cases port with
  | none => rfl
  | some n =>
    have hd : (decimal n).all Char.isDigit = true := List.all_eq_true.mpr (decimal_mem n)
    have hne : (decimal n).isEmpty = false := by
      simpa [List.isEmpty_iff] using Keel.Codec.decimal_ne_nil n
    simp only [Option.isNone_some, Bool.false_or, bne_iff_ne, ne_eq] at h
    simp only [normalizePort, portText, hne, Bool.false_eq_true, ite_false, hd, ite_true,
      digitsValue, Keel.Codec.digitsValue_decimal]
    simp [h]

theorem normalizePath_of_noDots {p : List Char} (h : noDotSegments p = true) : normalizePath p = p := by
  unfold normalizePath; simp [h]

end URLParse

/-! ## The canonical form, unpacked -/

namespace ParseResult

open URLParse

variable (r : ParseResult)

theorem printAuth_eq_nil_iff :
    printAuth r.userinfo.toList r.host.toList r.port = [] ↔ r.hasAuthority = false := by
  simp only [printAuth, hasAuthority, printHost]
  have hne : ':' ∈ r.host.toList → r.host ≠ "" := by
    rintro hc he; rw [he] at hc; simp at hc
  cases r.port <;> by_cases hc : ':' ∈ r.host.toList <;>
    simp [hc, List.isEmpty_iff, hne]

theorem rawOk (h : r.Canonical) : r.toRaw.Ok := by
  obtain ⟨hs, hu, hh, -, hp, hq, -⟩ := h
  simp only [pathCanonical, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hp
  obtain ⟨⟨⟨⟨hp1, hp2⟩, hp3⟩, hp4⟩, -⟩ := hp
  simp only [hostCanonical, Bool.and_eq_true, List.all_eq_true] at hh
  rw [List.all_eq_true] at hu
  have hauth : ∀ (a : Bool), (a = false ↔ printAuth r.userinfo.toList r.host.toList r.port = []) →
      True := fun _ _ => trivial
  clear hauth
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [toRaw]
    simp only [schemeCanonical, Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true,
      List.all_eq_true] at hs
    rcases hs with hs | ⟨⟨hs1, hs2⟩, -⟩
    · exact Or.inl hs
    · right; refine ⟨?_, hs2⟩
      cases e : r.scheme.toList.head? with
      | none => simp [e] at hs1
      | some c => simp [e] at hs1 ⊢; exact hs1
  · intro c hc
    simp only [toRaw, printAuth, List.mem_append] at hc
    have hgen : ∀ c, isGraphic c = true → c ≠ '/' → c ≠ '?' → c ≠ '#' → notAuthEnd c = true := by
      intro c _ h1 h2 h3; simp [notAuthEnd, h1, h2, h3]
    rcases hc with (hc | hc) | hc
    · split at hc
      · cases hc
      · simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · have := hu c hc
          simp only [userinfoSafe, pathSafe, querySafe, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
          simp only [notAuthEnd, Bool.and_eq_true, bne_iff_ne, ne_eq]
          refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro rfl <;> simp_all
        · rfl
    · simp only [printHost] at hc
      split at hc
      · simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | hc | rfl
        · rfl
        · have := hh.1 c hc
          simp only [hostChar, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
          simp only [notAuthEnd, Bool.and_eq_true, bne_iff_ne, ne_eq]
          exact ⟨⟨this.1.1.1.1.2, this.1.1.1.2⟩, this.1.1.2⟩
        · rfl
      · have := hh.1 c hc
        simp only [hostChar, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
        simp only [notAuthEnd, Bool.and_eq_true, bne_iff_ne, ne_eq]
        exact ⟨⟨this.1.1.1.1.2, this.1.1.1.2⟩, this.1.1.2⟩
    · split at hc
      · simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · rfl
        · have := Keel.Codec.decimal_isDigit _ c hc
          simp only [notAuthEnd, Bool.and_eq_true, bne_iff_ne, ne_eq]
          refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro rfl <;> simp at this
      · cases hc
  · intro c hc
    have := hp1 c hc
    simp only [pathSafe, querySafe, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    simp only [notPathEnd, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨?_, ?_⟩ <;> rintro rfl <;> simp_all
  · intro q hq' c hc
    simp only [toRaw, Option.map_eq_some_iff] at hq'
    obtain ⟨q', hq'', rfl⟩ := hq'
    simp only [hq'', Option.map_some, Option.getD_some, List.all_eq_true] at hq
    have := hq c hc
    simp only [querySafe, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    simp only [bne_iff_ne, ne_eq]; rintro rfl; simp_all
  · intro hne
    have : r.hasAuthority = true := by
      cases e : r.hasAuthority
      · exact absurd ((printAuth_eq_nil_iff r).mpr e) hne
      · rfl
    rcases hp2 with (h | h) | h
    · simp [this] at h
    · exact Or.inl h
    · exact Or.inr h
  · intro hnil
    have : r.hasAuthority = false := (printAuth_eq_nil_iff r).mp hnil
    rcases hp3 with h | h
    · simp [this] at h
    · simpa [toRaw] using h
  · intro hsch hnil
    have : r.hasAuthority = false := (printAuth_eq_nil_iff r).mp hnil
    simp only [toRaw] at hsch
    rcases hp4 with (h | h) | h
    · simp [toRaw, hsch] at h
    · simp [this] at h
    · simpa [toRaw] using h

theorem printHost_graphic {h : List Char} (hh : ∀ c ∈ h, hostChar c = true) :
    ∀ c ∈ printHost h, isGraphic c = true := by
  unfold printHost
  split
  · intro c hc
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc | rfl
    · decide
    · exact hostChar_graphic (hh c hc)
    · decide
  · exact fun c hc => hostChar_graphic (hh c hc)

theorem printPort_graphic (port : Option Nat) : ∀ c ∈ printPort port, isGraphic c = true := by
  cases port with
  | none => intro c hc; cases hc
  | some n =>
    intro c hc
    simp only [printPort, List.mem_cons] at hc
    rcases hc with rfl | hc
    · decide
    · exact digit_graphic (Keel.Codec.decimal_isDigit _ c hc)

theorem printRaw_graphic (hc : r.Canonical) : ∀ c ∈ printRaw r.toRaw, isGraphic c = true := by
  obtain ⟨hs, hu, hh, -, hp, hq, hf⟩ := hc
  simp only [pathCanonical, Bool.and_eq_true] at hp
  have hp1 := List.all_eq_true.mp hp.1.1.1.1
  simp only [hostCanonical, Bool.and_eq_true] at hh
  have hh1 := List.all_eq_true.mp hh.1
  rw [List.all_eq_true] at hu
  simp only [schemeCanonical, Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true] at hs
  have hS : ∀ c ∈ (if r.scheme.toList.isEmpty then [] else r.scheme.toList ++ [':']), isGraphic c = true := by
    split
    · intro c hc; cases hc
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · rcases hs with hs | ⟨⟨-, hs⟩, -⟩
        · rw [hs] at hc; cases hc
        · exact schemeChar_graphic (List.all_eq_true.mp hs c hc)
      · decide
  have hU : ∀ c ∈ (if r.userinfo.toList.isEmpty then [] else r.userinfo.toList ++ ['@']), isGraphic c = true := by
    split
    · intro c hc; cases hc
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact pathSafe_graphic (userinfoSafe_pathSafe (hu c hc))
      · decide
  have hA : ∀ c ∈ (if (printAuth r.userinfo.toList r.host.toList r.port).isEmpty then []
      else '/' :: '/' :: printAuth r.userinfo.toList r.host.toList r.port), isGraphic c = true := by
    split
    · intro c hc; cases hc
    · intro c hc
      rw [printAuth_eq] at hc
      simp only [List.mem_cons, List.mem_append] at hc
      rcases hc with rfl | rfl | (hc | hc | hc)
      · decide
      · decide
      · exact hU c hc
      · exact printHost_graphic hh1 c hc
      · exact printPort_graphic r.port c hc
  intro c hc
  simp only [printRaw, toRaw, List.mem_append] at hc
  rcases hc with (((hc | hc) | hc) | hc) | hc
  · exact hS c hc
  · exact hA c hc
  · exact pathSafe_graphic (hp1 c hc)
  · cases hq' : r.query with
    | none => simp [hq'] at hc
    | some q =>
      simp only [hq', Option.map_some, Option.getD_some, List.all_eq_true] at hq hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · decide
      · exact querySafe_graphic (hq c hc)
  · cases hf' : r.fragment with
    | none => simp [hf'] at hc
    | some f =>
      simp only [hf', Option.map_some, Option.getD_some, List.all_eq_true] at hf hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · decide
      · exact fragSafe_graphic (hf c hc)

theorem path_lemmas (hp : r.pathCanonical = true) :
    validatePath r.path.toList (!r.scheme.toList.isEmpty) r.hasAuthority = .ok () ∧
    quote pathSafe (if (!r.scheme.toList.isEmpty || r.hasAuthority) = true then normalizePath r.path.toList
      else r.path.toList) = r.path.toList ∧
    (!r.hasAuthority && r.path.toList.take 2 == ['/', '/']) = false ∧
    (!!r.scheme.toList.isEmpty && !r.hasAuthority && (schemeOf r.path.toList).isSome) = false := by
  simp only [pathCanonical, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.isEmpty_iff, beq_iff_eq] at hp
  obtain ⟨⟨⟨⟨hp1, hp2⟩, hp3⟩, hp4⟩, hp5⟩ := hp
  have hq := quote_of_all (List.all_eq_true.mp hp1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold validatePath
    have h1 : (r.hasAuthority && !r.path.toList.isEmpty && r.path.toList.head? != some '/') = false := by
      rcases hp2 with (h | h) | h <;> simp [h]
    have h2 : (!!r.scheme.toList.isEmpty && !r.hasAuthority && List.take 2 r.path.toList == ['/', '/']) = false := by
      rcases hp3 with h | h <;> simp [h]
    have h3 : (!!r.scheme.toList.isEmpty && !r.hasAuthority && r.path.toList.head? == some ':') = false := by
      rcases hp4 with (h | h) | h
      · simp [h]
      · simp [h]
      · cases e : r.path.toList with
        | nil => simp
        | cons c t =>
          rw [e] at h
          by_cases hc : c = ':'
          · subst hc; simp [schemeOf] at h
          · simp [hc]
    simp only [h1, h2, h3, Bool.false_eq_true, ite_false]
  · split
    · rename_i hsa
      have : noDotSegments r.path.toList = true := by
        rcases hp5 with ⟨h1, h2⟩ | h
        · simp [h1, h2] at hsa
        · exact h
      rw [normalizePath_of_noDots this, hq]
    · exact hq
  · rcases hp3 with h | h <;> simp [h]
  · rcases hp4 with (h | h) | h
    · simp [h]
    · simp [h]
    · simp [h]

theorem checkInput_print (hc : r.Canonical) (hl : (printRaw r.toRaw).length ≤ maxUrlLength) :
    checkInput (printRaw r.toRaw) = .ok () := by
  have hn : (printRaw r.toRaw).findIdx? isAsciiControl = none :=
    List.findIdx?_eq_none_iff.mpr fun c h => isGraphic_not_control (r.printRaw_graphic hc c h)
  simp [checkInput, hn, Nat.not_lt.mpr hl]

end ParseResult

@[simp] theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

open ParseResult in
/-- **URL round trip** (card: `url_parse_print_ext`). Printing a URL and
parsing the text gives the same URL: every component survives, in its
normal form. The hypothesis is upstream's length limit, which a printed URL
must respect for the parser to accept it at all. -/
theorem url_parse_print_ext (u : URL) (h : u.toString.length ≤ URLParse.maxUrlLength) :
    URL.parse u.toString = .ok u := by
  obtain ⟨r, hc⟩ := u
  simp only [URL.toString, String.length_ofList] at h
  simp only [URL.parse, URL.toString, String.toList_ofList, URLParse.parse,
    checkInput_print r hc h, splitUrl_printRaw _ (rawOk r hc)]
  have hc' := hc
  obtain ⟨hs, hu, hh, hpo, hp, hq, hf⟩ := hc'
  have hui : ∀ c ∈ r.userinfo.toList, c ≠ '@' := by
    intro c hc'
    have := List.all_eq_true.mp hu c hc'
    simp only [userinfoSafe, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    rintro rfl; simp at this
  have hhc : ∀ c ∈ r.host.toList, hostChar c = true := by
    simp only [hostCanonical, Bool.and_eq_true] at hh; exact List.all_eq_true.mp hh.1
  have hsl : r.scheme.toList.map Char.toLower = r.scheme.toList := by
    simp only [schemeCanonical, Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true] at hs
    rcases hs with hs | ⟨-, hs⟩
    · rw [hs]; rfl
    · exact map_toLower_of_all (List.all_eq_true.mp hs)
  have hul : quote userinfoSafe r.userinfo.toList = r.userinfo.toList :=
    quote_of_all (List.all_eq_true.mp hu)
  have hauth : (!r.userinfo.toList.isEmpty || !r.host.toList.isEmpty || r.port.isSome) = r.hasAuthority := rfl
  obtain ⟨hv, hpq, hc1, hc2⟩ := path_lemmas r hp
  have hqq : (r.query.map String.toList).map (fun q => String.ofList (quote querySafe q)) = r.query := by
    cases e : r.query with
    | none => rfl
    | some q =>
      simp only [e, Option.map_some, Option.getD_some] at hq
      simp [quote_of_all (List.all_eq_true.mp hq)]
  have hff : (r.fragment.map String.toList).map (fun f => String.ofList (quote fragSafe f)) = r.fragment := by
    cases e : r.fragment with
    | none => rfl
    | some f =>
      simp only [e, Option.map_some, Option.getD_some] at hf
      simp [quote_of_all (List.all_eq_true.mp hf)]
  simp only [toRaw, splitAuth_printAuth _ _ _ hui hhc, build, hsl, hul,
    encodeHost_printHost hh, normalizePort_portText hpo, except_ok_bind]
  simp only [hauth, hv, hpq, hc1, hc2, hqq, hff, String.ofList_toList, except_ok_bind,
    Bool.false_eq_true, ite_false]
  rw [dif_pos hc]; rfl

end LeanHttpx
