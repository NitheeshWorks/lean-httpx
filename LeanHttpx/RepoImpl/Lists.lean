/-!
# List lemmas: scanning up to a stop element

`takeWhile p` and `dropWhile p` on `l ++ r`, where every element of `l`
satisfies `p` and `r` starts with an element that does not (or is empty):
the scan returns exactly `l` and leaves exactly `r`. Every delimiter-based
splitter in the library (URLs, header lines) inverts its printer by these two
facts.
-/

namespace LeanHttpx

variable {α : Type}

/-- `r` is empty or starts with an element `p` rejects. -/
def StopsAt (p : α → Bool) (r : List α) : Prop := ∀ c, r.head? = some c → p c = false

theorem takeWhile_append_stop {p : α → Bool} {l r : List α} (hl : ∀ c ∈ l, p c = true)
    (hr : StopsAt p r) : (l ++ r).takeWhile p = l := by
  rw [List.takeWhile_append_of_pos hl]
  cases r with
  | nil => simp
  | cons c r => simp [hr c rfl]

theorem dropWhile_append_stop {p : α → Bool} {l r : List α} (hl : ∀ c ∈ l, p c = true)
    (hr : StopsAt p r) : (l ++ r).dropWhile p = r := by
  induction l with
  | nil =>
    cases r with
    | nil => rfl
    | cons c r => simp [hr c rfl]
  | cons x l ih =>
    simp only [List.cons_append, List.dropWhile_cons, hl x (by simp), ite_true]
    exact ih (fun c hc => hl c (by simp [hc]))

theorem all_of_dropWhile_eq_nil {p : α → Bool} : ∀ {l : List α}, l.dropWhile p = [] →
    ∀ x ∈ l, p x = true
  | [], _, x, hx => by cases hx
  | c :: l, h, x, hx => by
    by_cases hc : p c = true
    · simp only [List.dropWhile_cons, hc, ite_true] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hc
      · exact all_of_dropWhile_eq_nil h x hx
    · simp [List.dropWhile_cons, hc] at h

theorem dropWhile_append_of_ne_nil {p : α → Bool} {l r : List α} (h : l.dropWhile p ≠ []) :
    (l ++ r).dropWhile p = l.dropWhile p ++ r := by
  rw [List.dropWhile_append]; simp [h]

theorem stopsAt_nil (p : α → Bool) : StopsAt p [] := by intro c h; cases h

theorem stopsAt_cons {p : α → Bool} {c : α} {r : List α} (h : p c = false) :
    StopsAt p (c :: r) := by
  intro d hd; simp at hd; subst hd; exact h

theorem stopsAt_append {p : α → Bool} {l r : List α} (hl : StopsAt p l)
    (hr : l = [] → StopsAt p r) : StopsAt p (l ++ r) := by
  cases l with
  | nil => exact hr rfl
  | cons c l => intro d hd; simp at hd; subst hd; exact hl _ rfl

theorem takeWhile_all {p : α → Bool} : ∀ {l : List α}, (∀ c ∈ l, p c = true) → l.takeWhile p = l
  | [], _ => rfl
  | c :: l, h => by
    have ih : l.takeWhile p = l := takeWhile_all fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp [h c (by simp), ih]

theorem dropWhile_all {p : α → Bool} {l : List α} (h : ∀ c ∈ l, p c = true) : l.dropWhile p = [] := by
  simpa using dropWhile_append_stop (r := []) h (stopsAt_nil p)

end LeanHttpx
