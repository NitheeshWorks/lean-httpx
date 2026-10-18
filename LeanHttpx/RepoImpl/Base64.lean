/-!
# Base64 (RFC 4648 section 4)

The standard alphabet with `=` padding, as Python's `base64.b64encode` and
`b64decode` use it for HTTP Basic credentials. Encoding is group by group:
three bytes are one 24-bit number, written as four 6-bit digits.
`decode_encode` is proved from the per-group fact `decodeGroup_encodeGroup`,
which is arithmetic on that number.
-/

namespace LeanHttpx

namespace Base64

/-- The digit of a 6-bit value. -/
def digit (d : Nat) : Char :=
  if d < 26 then Char.ofNat (65 + d) else if d < 52 then Char.ofNat (71 + d)
  else if d < 62 then Char.ofNat (d - 4) else if d = 62 then '+' else '/'

/-- The value of a digit. -/
def value (c : Char) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n && n ≤ 90 then some (n - 65) else if 97 ≤ n && n ≤ 122 then some (n - 71)
  else if 48 ≤ n && n ≤ 57 then some (n + 4) else if c = '+' then some 62
  else if c = '/' then some 63 else none

theorem value_digit_fin : ∀ d : Fin 64, value (digit d.val) = some d.val := by decide

theorem value_digit {d : Nat} (h : d < 64) : value (digit d) = some d := value_digit_fin ⟨d, h⟩

theorem digit_ne_pad_fin : ∀ d : Fin 64, digit d.val ≠ '=' := by decide

/-- The four digits of three bytes. -/
def encodeGroup (a b c : UInt8) : List Char :=
  let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
  [digit (n / 262144), digit (n / 4096 % 64), digit (n / 64 % 64), digit (n % 64)]

/-- Encode bytes. -/
def encodeList : List UInt8 → List Char
  | a :: b :: c :: r => encodeGroup a b c ++ encodeList r
  | [a, b] =>
    let n := a.toNat * 65536 + b.toNat * 256
    [digit (n / 262144), digit (n / 4096 % 64), digit (n / 64 % 64), '=']
  | [a] =>
    let n := a.toNat * 65536
    [digit (n / 262144), digit (n / 4096 % 64), '=', '=']
  | [] => []

/-- `base64.b64encode(data).decode()`. -/
def encode (b : ByteArray) : String := String.ofList (encodeList b.data.toList)

/-- Decode four digits (the last one or two may be `=` padding at the end). -/
def decodeGroup (c1 c2 c3 c4 : Char) : Option (List UInt8) := do
  let d1 ← value c1
  let d2 ← value c2
  if c3 = '=' then
    if c4 = '=' then pure [(d1 * 4 + d2 / 16).toUInt8] else none
  else
    let d3 ← value c3
    if c4 = '=' then
      pure [(d1 * 4 + d2 / 16).toUInt8, ((d2 % 16) * 16 + d3 / 4).toUInt8]
    else
      let d4 ← value c4
      let n := d1 * 262144 + d2 * 4096 + d3 * 64 + d4
      pure [(n / 65536).toUInt8, (n / 256 % 256).toUInt8, (n % 256).toUInt8]

/-- Decode digits; padding only in the last group. -/
def decodeList : List Char → Option (List UInt8)
  | c1 :: c2 :: c3 :: c4 :: r => do
    let g ← decodeGroup c1 c2 c3 c4
    if (c3 = '=' || c4 = '=') && !r.isEmpty then none else
    let rest ← decodeList r
    pure (g ++ rest)
  | [] => some []
  | _ => none

/-- `base64.b64decode(s)` (strict: no whitespace, correct padding). -/
def decode (s : String) : Option ByteArray := (decodeList s.toList).map fun l => ⟨l.toArray⟩

/-! ## The law -/

theorem toUInt8_toNat (b : UInt8) : b.toNat.toUInt8 = b := by
  simp [Nat.toUInt8, UInt8.ofNat_toNat]

theorem recon (x y z : Nat) (_hx : x < 2 ^ 8) (hy : y < 2 ^ 8) (hz : z < 2 ^ 8) :
    ((x * 65536 + y * 256 + z) / 262144 * 262144 + (x * 65536 + y * 256 + z) / 4096 % 64 * 4096 +
        (x * 65536 + y * 256 + z) / 64 % 64 * 64 + (x * 65536 + y * 256 + z) % 64) / 65536 = x ∧
    ((x * 65536 + y * 256 + z) / 262144 * 262144 + (x * 65536 + y * 256 + z) / 4096 % 64 * 4096 +
        (x * 65536 + y * 256 + z) / 64 % 64 * 64 + (x * 65536 + y * 256 + z) % 64) / 256 % 256 = y ∧
    ((x * 65536 + y * 256 + z) / 262144 * 262144 + (x * 65536 + y * 256 + z) / 4096 % 64 * 4096 +
        (x * 65536 + y * 256 + z) / 64 % 64 * 64 + (x * 65536 + y * 256 + z) % 64) % 256 = z := by
  omega

theorem decodeGroup_encodeGroup (a b c : UInt8) :
    (match encodeGroup a b c with
     | [c1, c2, c3, c4] => decodeGroup c1 c2 c3 c4
     | _ => none) = some [a, b, c] := by
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt
  simp only [encodeGroup]
  have h1 := value_digit (d := (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 262144) (by omega)
  have h2 := value_digit (d := (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64) (by omega)
  have h3 := value_digit (d := (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64) (by omega)
  have h4 := value_digit (d := (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64) (by omega)
  have p3 := digit_ne_pad_fin ⟨(a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64, by omega⟩
  have p4 := digit_ne_pad_fin ⟨(a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64, by omega⟩
  simp only at p3 p4
  simp only [decodeGroup, h1, h2, h3, h4, p3, p4, ite_false, Option.bind_eq_bind, Option.pure_def,
    Option.bind_some]
  obtain ⟨e1, e2, e3⟩ := recon a.toNat b.toNat c.toNat ha hb hc
  rw [e1, e2, e3, toUInt8_toNat, toUInt8_toNat, toUInt8_toNat]

theorem recon2 (x y : Nat) (hy : y < 2 ^ 8) :
    (x * 65536 + y * 256) / 262144 * 4 + (x * 65536 + y * 256) / 4096 % 64 / 16 = x ∧
    (x * 65536 + y * 256) / 4096 % 64 % 16 * 16 + (x * 65536 + y * 256) / 64 % 64 / 4 = y := by
  omega

theorem recon1 (x : Nat) : x * 65536 / 262144 * 4 + x * 65536 / 4096 % 64 / 16 = x := by omega

theorem digit_ne_pad {d : Nat} (h : d < 64) : digit d ≠ '=' := digit_ne_pad_fin ⟨d, h⟩

/-- **Base64 round trip**: decoding an encoding gives the bytes back. -/
theorem decodeList_encodeList : ∀ l : List UInt8, decodeList (encodeList l) = some l
  | a :: b :: c :: r => by
    have g := decodeGroup_encodeGroup a b c
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt
    simp only [encodeGroup] at g
    simp only [encodeList, encodeGroup, List.cons_append, List.nil_append, decodeList, g,
      Option.bind_eq_bind, Option.bind_some, decodeList_encodeList r,
      digit_ne_pad (d := (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64) (by omega),
      digit_ne_pad (d := (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64) (by omega),
      decide_false, Bool.or_false, Bool.false_and, Bool.false_eq_true, ite_false]
    rfl
  | [a, b] => by
    have ha := a.toNat_lt; have hb := b.toNat_lt
    obtain ⟨e1, e2⟩ := recon2 a.toNat b.toNat hb
    simp only [encodeList, decodeList, decodeGroup,
      value_digit (d := (a.toNat * 65536 + b.toNat * 256) / 262144) (by omega),
      value_digit (d := (a.toNat * 65536 + b.toNat * 256) / 4096 % 64) (by omega),
      value_digit (d := (a.toNat * 65536 + b.toNat * 256) / 64 % 64) (by omega),
      digit_ne_pad (d := (a.toNat * 65536 + b.toNat * 256) / 64 % 64) (by omega),
      Option.bind_eq_bind, Option.bind_some, ite_true, ite_false, e1, e2, toUInt8_toNat]
    rfl
  | [a] => by
    have ha := a.toNat_lt
    simp only [encodeList, decodeList, decodeGroup,
      value_digit (d := a.toNat * 65536 / 262144) (by omega),
      value_digit (d := a.toNat * 65536 / 4096 % 64) (by omega),
      Option.bind_eq_bind, Option.bind_some, ite_true, recon1, toUInt8_toNat]
    rfl
  | [] => rfl

theorem decode_encode (b : ByteArray) : decode (encode b) = some b := by
  simp only [decode, encode, String.toList_ofList, decodeList_encodeList, Option.map_some]

end Base64

end LeanHttpx
