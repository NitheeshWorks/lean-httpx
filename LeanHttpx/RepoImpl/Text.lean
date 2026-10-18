import LeanHttpx.DataTypes.Chars

/-!
# Text helpers: UTF-8 decoding with replacement, Python `repr`, unquoting

* `utf8DecodeReplace` decodes bytes as UTF-8, replacing each maximal invalid
  subpart by U+FFFD, as Python's `bytes.decode("utf-8", "replace")` does. It is
  a loop over the byte position, so it runs in constant stack on any input.
* `pyRepr` renders a string as Python's `repr` does, for error messages that
  match upstream's.
* `unquote` is `urllib.parse.unquote`: `%XX` escapes become bytes, decoded as
  UTF-8 with replacement.
-/

namespace LeanHttpx

namespace Text

/-- A continuation byte in the range `[lo, hi]`. -/
@[inline] def inRange (b : UInt8) (lo hi : UInt8) : Bool := lo ≤ b && b ≤ hi

/-- The number of bytes of a well-formed sequence starting at `i`, or `0` with
the number of bytes of the maximal invalid subpart (at least 1). -/
def utf8Step (bs : ByteArray) (i : Nat) : Bool × Nat × Nat :=
  let b0 := bs.get! i
  let get (k : Nat) : Option UInt8 := if i + k < bs.size then some (bs.get! (i + k)) else none
  -- `(lo, hi)` for the second byte, and the number of continuation bytes.
  let spec : Option (UInt8 × UInt8 × Nat) :=
    if b0 < 0x80 then none
    else if inRange b0 0xC2 0xDF then some (0x80, 0xBF, 1)
    else if b0 == 0xE0 then some (0xA0, 0xBF, 2)
    else if inRange b0 0xE1 0xEC || inRange b0 0xEE 0xEF then some (0x80, 0xBF, 2)
    else if b0 == 0xED then some (0x80, 0x9F, 2)
    else if b0 == 0xF0 then some (0x90, 0xBF, 3)
    else if inRange b0 0xF1 0xF3 then some (0x80, 0xBF, 3)
    else if b0 == 0xF4 then some (0x80, 0x8F, 3)
    else some (0, 0, 0)
  match spec with
  | none => (true, 1, b0.toNat)
  | some (_, _, 0) => (false, 1, 0)
  | some (lo, hi, n) =>
    match get 1 with
    | some b1 =>
      if !inRange b1 lo hi then (false, 1, 0) else
      let v1 := (b0.toNat % (2 ^ (6 - n))) * 64 + (b1.toNat % 64)
      if n == 1 then (true, 2, v1) else
      match get 2 with
      | some b2 =>
        if !inRange b2 0x80 0xBF then (false, 2, 0) else
        let v2 := v1 * 64 + b2.toNat % 64
        if n == 2 then (true, 3, v2) else
        match get 3 with
        | some b3 => if !inRange b3 0x80 0xBF then (false, 3, 0) else (true, 4, v2 * 64 + b3.toNat % 64)
        | none => (false, 3, 0)
      | none => (false, 2, 0)
    | none => (false, 1, 0)

theorem utf8Step_pos (bs : ByteArray) (i : Nat) : 0 < (utf8Step bs i).2.1 := by
  unfold utf8Step
  simp only
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all

/-- Decode from position `i`, appending to `acc`. -/
def utf8DecodeGo (bs : ByteArray) (i : Nat) (acc : String) : String :=
  if h : i < bs.size then
    let (ok, n, v) := utf8Step bs i
    have : bs.size - (i + (utf8Step bs i).2.1) < bs.size - i := by
      have := utf8Step_pos bs i; omega
    utf8DecodeGo bs (i + (utf8Step bs i).2.1) (acc.push (if ok then Char.ofNat v else '�'))
  else acc
termination_by bs.size - i

/-- Decode UTF-8, replacing invalid subparts by U+FFFD (Python
`decode("utf-8", "replace")`). -/
def utf8DecodeReplace (bs : ByteArray) : String :=
  match String.fromUTF8? bs with
  | some s => s
  | none => utf8DecodeGo bs 0 ""

/-- Header bytes as text: UTF-8 when valid, otherwise ISO-8859-1 (httpx's
`Headers.encoding` falls back the same way). -/
def decodeHeader (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => s
  | none => b.foldl (fun s x => s.push (Char.ofNat x.toNat)) ""

/-- Python's `repr` of a single character. -/
def charRepr (c : Char) : String :=
  let n := c.toNat
  if c == '\\' then "\\\\" else if c == '\t' then "\\t" else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if n < 0x20 || n == 0x7F then
    "\\x" ++ String.ofList [Chars.hexUpper (n / 16) |>.toLower, Chars.hexUpper (n % 16) |>.toLower]
  else c.toString

/-- Python's `repr` of a string: single quotes unless the string contains a
single quote and no double quote. -/
def pyRepr (s : String) : String :=
  let q := if s.contains '\'' && !s.contains '"' then '"' else '\''
  let body := s.toList.foldl (fun acc c => if c == q then acc ++ "\\" ++ c.toString else acc ++ charRepr c) ""
  q.toString ++ body ++ q.toString

/-- `%XX` escapes to bytes; everything else as its UTF-8 bytes. A loop with an
accumulator, so the stack stays flat. -/
def unquoteBytesGo : List Char → Array UInt8 → Array UInt8
  | '%' :: a :: b :: r, acc =>
    if Chars.isHex a && Chars.isHex b then
      unquoteBytesGo r (acc.push (Chars.hexValue a * 16 + Chars.hexValue b).toUInt8)
    else unquoteBytesGo (a :: b :: r) (acc.push 37)
  | c :: r, acc => unquoteBytesGo r (acc ++ (String.utf8EncodeChar c).toArray)
  | [], acc => acc

/-- `urllib.parse.unquote`. -/
def unquote (s : String) : String :=
  if !s.contains '%' then s else utf8DecodeReplace ⟨unquoteBytesGo s.toList #[]⟩

/-- `urllib.parse.unquote_plus`: `+` is a space, then `unquote`. -/
def unquotePlus (s : String) : String :=
  unquote (String.ofList (s.toList.map fun c => if c == '+' then ' ' else c))

/-- `urllib.parse.quote_plus(s, safe="")`, the encoding of `urlencode`:
unreserved characters stay, a space is `+`, everything else is `%XX` of its
UTF-8 bytes. -/
def quotePlus (s : String) : String :=
  String.ofList <| s.toList.flatMap fun c =>
    if Chars.isUnreserved c then [c] else if c == ' ' then ['+'] else Chars.percentChar c

end Text

end LeanHttpx
