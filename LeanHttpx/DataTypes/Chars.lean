/-!
# Character classes and percent-encoding

The character sets of RFC 3986 and of the WHATWG percent-encode sets that
httpx uses (`httpx/_urlparse.py`), as Boolean predicates on `Char` written in
terms of the code point, so `omega` and `decide` reason about them.

`quote safe s` percent-encodes every character of `s` outside `safe` as the
`%XX` escapes of its UTF-8 bytes, with upper-case hex. Every safe set here
contains `%`, so upstream's rule "leave existing `%xx` escapes alone" is the
same as encoding character by character, which is how it is defined.
-/

namespace LeanHttpx

namespace Chars

/-- ASCII letters and digits. -/
def isAlnum (c : Char) : Bool := c.isAlphanum

/-- RFC 3986 section 2.3: `ALPHA / DIGIT / "-" / "." / "_" / "~"`. -/
def isUnreserved (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~'

/-- RFC 3986 section 2.2 `sub-delims`: ``!$&'()*+,;=``. -/
def isSubDelim (c : Char) : Bool :=
  c == '!' || c == '$' || c == '&' || c == '\'' || c == '(' || c == ')' || c == '*' ||
  c == '+' || c == ',' || c == ';' || c == '='

/-- An ASCII control character (`0x00`-`0x1F`, `0x7F`): what upstream rejects
as "non-printable ASCII". -/
def isAsciiControl (c : Char) : Bool := c.toNat < 0x20 || c.toNat == 0x7F

/-- Printable ASCII other than space. Every safe set below lies inside it. -/
def isGraphic (c : Char) : Bool := 0x20 < c.toNat && c.toNat < 0x7F

/-- The WHATWG fragment set: graphic ASCII except `"`, `<`, `>` and backquote. -/
def fragSafe (c : Char) : Bool :=
  isGraphic c && c.toNat != 0x22 && c.toNat != 0x3C && c.toNat != 0x3E && c.toNat != 0x60

/-- The WHATWG query set: graphic ASCII except `"`, `#`, `<`, `>`. -/
def querySafe (c : Char) : Bool :=
  isGraphic c && c.toNat != 0x22 && c.toNat != 0x23 && c.toNat != 0x3C && c.toNat != 0x3E

/-- The WHATWG path set: the query set without `?`, backquote, `{`, `}`. -/
def pathSafe (c : Char) : Bool :=
  querySafe c && c.toNat != 0x3F && c.toNat != 0x60 && c.toNat != 0x7B && c.toNat != 0x7D

/-- The joint userinfo set: the path set without `/ ; = @ [ \ ] ^ |`. The
colon stays, since it separates username and password. -/
def userinfoSafe (c : Char) : Bool :=
  pathSafe c && c.toNat != 0x2F && c.toNat != 0x3B && c.toNat != 0x3D && c.toNat != 0x40 &&
  c.toNat != 0x5B && c.toNat != 0x5C && c.toNat != 0x5D && c.toNat != 0x5E && c.toNat != 0x7C

/-- The username and password sets: the userinfo set without the colon. -/
def usernameSafe (c : Char) : Bool := userinfoSafe c && c != ':'

/-- A registered host name: unreserved, sub-delims, and the WHATWG extras
``"`{}%|\``. -/
def hostSafe (c : Char) : Bool :=
  isUnreserved c || isSubDelim c || c == '"' || c == '`' || c == '{' || c == '}' ||
  c == '%' || c == '|' || c == '\\'

/-- A scheme character after the first: ALPHA / DIGIT / `+` / `-` / `.`. -/
def isSchemeChar (c : Char) : Bool := c.isAlphanum || c == '+' || c == '-' || c == '.'

/-- A hexadecimal digit. -/
def isHex (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- The value of a hexadecimal digit. -/
def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87 else c.toNat - 55

/-- The upper-case hex digit of `d < 16`. -/
def hexUpper (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (55 + d)

/-- The `%XX` escape of one byte. -/
def percentByte (b : UInt8) : List Char := ['%', hexUpper (b.toNat / 16), hexUpper (b.toNat % 16)]

/-- The `%XX` escapes of a character's UTF-8 bytes (upstream `PERCENT`). -/
def percentChar (c : Char) : List Char := (String.utf8EncodeChar c).flatMap percentByte

/-- Percent-encode every character outside `safe` (upstream `quote`). -/
def quote (safe : Char → Bool) (s : List Char) : List Char :=
  s.flatMap fun c => if safe c then [c] else percentChar c

/-- Percent-encode every byte outside `safe` (for byte strings). -/
def quoteBytes (safe : Char → Bool) (s : List UInt8) : List Char :=
  s.flatMap fun b => let c := Char.ofNat b.toNat; if b.toNat < 0x80 && safe c then [c] else percentByte b

/-! ## Laws -/

theorem quote_of_all {safe : Char → Bool} : ∀ {s : List Char}, (∀ c ∈ s, safe c = true) →
    quote safe s = s
  | [], _ => rfl
  | c :: s, h => by
    have hc := h c (by simp)
    have ih := quote_of_all (s := s) (fun x hx => h x (by simp [hx]))
    simp only [quote, List.flatMap_cons, hc, ite_true] at ih ⊢
    rw [ih]; rfl

theorem hexUpper_lt (d : Nat) (h : d < 16) : (hexUpper d).toNat < 0x7F ∧ 0x20 < (hexUpper d).toNat ∧
    (hexUpper d).isAlphanum = true := by
  have : ∀ e : Fin 16, (hexUpper e.val).toNat < 0x7F ∧ 0x20 < (hexUpper e.val).toNat ∧
      (hexUpper e.val).isAlphanum = true := by decide
  exact this ⟨d, h⟩

/-- A safe set that contains `%` and the alphanumerics contains every
character of a `%XX` escape. -/
theorem all_percentByte {safe : Char → Bool} (hp : safe '%' = true)
    (ha : ∀ c : Char, c.isAlphanum = true → safe c = true) (b : UInt8) :
    ∀ c ∈ percentByte b, safe c = true := by
  have h1 := hexUpper_lt (b.toNat / 16) (by have := b.toNat_lt; omega)
  have h2 := hexUpper_lt (b.toNat % 16) (by omega)
  intro c hc
  simp only [percentByte, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hp
  · exact ha _ h1.2.2
  · exact ha _ h2.2.2

/-- The output of `quote` is safe, so quoting is idempotent. -/
theorem all_quote {safe : Char → Bool} (hp : safe '%' = true)
    (ha : ∀ c : Char, c.isAlphanum = true → safe c = true) (s : List Char) :
    ∀ c ∈ quote safe s, safe c = true := by
  intro c hc
  simp only [quote, List.mem_flatMap] at hc
  obtain ⟨x, _, hx⟩ := hc
  by_cases hs : safe x = true
  · simp only [hs, ite_true, List.mem_singleton] at hx; subst hx; exact hs
  · simp only [hs, Bool.false_eq_true, ite_false, percentChar, List.mem_flatMap] at hx
    obtain ⟨b, _, hb⟩ := hx
    exact all_percentByte hp ha b c hb

theorem quote_quote {safe : Char → Bool} (hp : safe '%' = true)
    (ha : ∀ c : Char, c.isAlphanum = true → safe c = true) (s : List Char) :
    quote safe (quote safe s) = quote safe s :=
  quote_of_all (all_quote hp ha s)

end Chars

end LeanHttpx
