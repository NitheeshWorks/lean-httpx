import LeanHttpx.DataTypes.H1
import LeanHttpx.RepoImpl.Codec

/-!
# The HTTP/1.1 codecs (RFC 9112), built from `Keel.Codec`

Every message part is a lawful codec, assembled with `Keel.Codec`
combinators, so each message codec is lawful by construction:

* a field line is `name ":" OWS value OWS CRLF`: `delimited ":"` over a token,
  then `delimited CRLF` over `owsValue`, which strips the whitespace;
* the field section is `manyTill CRLF` of field lines;
* the request line and status line are `delimited " "` fields and a version
  chosen by literal tags (`Codec.sum`);
* the body codec is chosen by the head's framing (`Codec.sigma`):
  `Content-Length` is `bytesN`, `Transfer-Encoding: chunked` is
  `chunkedBody`, a response without either runs to the end (`toEnd`, decode
  only), and conflicting framing is `Codec.fail`.

Only `owsValue`, the chunk-size line and the chunk sequence are written by
hand, with their laws in `Proofs/H1.lean`... here, next to them, since a
codec carries its law as a field.

Every loop is `Parser.many` (iterative) and every body is read by `takeBytes`
into a `ByteArray`, so the stack does not grow with the input.
-/

namespace LeanHttpx

namespace H1

open Keel Keel.Parser

/-! ## Byte facts -/

/-- `omega` over byte comparisons. -/
macro "byte_omega" : tactic =>
  `(tactic| (simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_false_iff,
      Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq,
      UInt8.toNat_ofNat] at *; omega))

theorem vchar_not_ows {b : UInt8} (h : isVchar b = true) : isOWS b = false := by
  unfold isVchar isOWS at *; byte_omega

/-- Carriage return, line feed, space, colon. -/
abbrev CR : UInt8 := 13
abbrev LF : UInt8 := 10
abbrev SP : UInt8 := 32
abbrev COLON : UInt8 := 58

/-- `CRLF`. -/
def crlf : List UInt8 := [CR, LF]

/-- ASCII lower case. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII lower case of a byte string. -/
def lowerBytes (l : List UInt8) : List UInt8 := l.map lowerByte

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

/-- Strip leading and trailing whitespace. -/
def stripOWS (v : List UInt8) : List UInt8 := ((v.dropWhile isOWS).reverse.dropWhile isOWS).reverse

/-! ## Decimal and hexadecimal numbers as bytes -/

/-- The decimal digits of `n`, as bytes. -/
def decimalBytes (n : Nat) : List UInt8 := (Codec.decimal n).map fun c => c.toNat.toUInt8

/-- The value of decimal digit bytes. -/
def decimalValue (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 10 + (b.toNat - 48)) 0

/-- All bytes are decimal digits, and there is at least one. -/
def isDigits (l : List UInt8) : Bool := !l.isEmpty && l.all fun b => 48 ≤ b && b ≤ 57

theorem foldl_congr_mem {α β : Type} {f g : β → α → β} :
    ∀ {l : List α} (a : β), (∀ acc x, x ∈ l → f acc x = g acc x) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | x :: l, a, h => by
    simp only [List.foldl_cons]
    rw [h a x (by simp)]
    exact foldl_congr_mem _ fun acc y hy => h acc y (by simp [hy])

theorem decimalValue_decimalBytes (n : Nat) : decimalValue (decimalBytes n) = n := by
  have h := Codec.digitsValue_decimal n
  unfold decimalValue decimalBytes
  rw [List.foldl_map]
  unfold Codec.digitsValue at h
  refine (foldl_congr_mem 0 ?_).trans h
  intro acc c hc
  have := Codec.decimal_isDigit n c hc
  have hc' : c.toNat < 256 := by
    simp [Char.isDigit, UInt32.le_iff_toNat_le] at this
    omega
  simp [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hc', Codec.digitValue]

/-- A lower-case hex digit. -/
def hexByte (d : Nat) : UInt8 := if d < 10 then (48 + d).toUInt8 else (87 + d).toUInt8

/-- A hex digit byte, either case. -/
def isHexByte (b : UInt8) : Bool := (48 ≤ b && b ≤ 57) || (97 ≤ b && b ≤ 102) || (65 ≤ b && b ≤ 70)

/-- The value of a hex digit byte. -/
def hexVal (b : UInt8) : Nat :=
  if b ≤ 57 then b.toNat - 48 else if b ≤ 70 then b.toNat - 55 else b.toNat - 87

/-- The lower-case hex digits of `n` (h11 writes chunk sizes as `%x`). -/
def hexDigits (n : Nat) : List UInt8 :=
  if n < 16 then [hexByte n] else hexDigits (n / 16) ++ [hexByte (n % 16)]

/-- The most hex digits of a chunk size: h11's `chunk_size = HEXDIG{1,20}`.
The size is converted only after this check, so the work is bounded. -/
def maxChunkDigits : Nat := 20

/-- The chunk sizes that fit: below `16 ^ maxChunkDigits` (2^80 bytes). -/
def maxChunkSize : Nat := 16 ^ maxChunkDigits

/-- The value of hex digit bytes. -/
def hexValue (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 16 + hexVal b) 0

theorem hexByte_fin : ∀ d : Fin 16, isHexByte (hexByte d.val) = true ∧ hexVal (hexByte d.val) = d.val ∧
    hexByte d.val ≠ CR := by decide

theorem hexDigits_isHex (n : Nat) : ∀ b ∈ hexDigits n, isHexByte b = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro b hb
    unfold hexDigits at hb
    split at hb
    · simp at hb; subst hb; exact (hexByte_fin ⟨n, by omega⟩).1
    · simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | hb
      · exact ih (n / 16) (by omega) b hb
      · subst hb; exact (hexByte_fin ⟨n % 16, by omega⟩).1

theorem hexDigits_ne_nil (n : Nat) : hexDigits n ≠ [] := by
  unfold hexDigits; split <;> simp

theorem hexValue_hexDigits (n : Nat) : hexValue (hexDigits n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold hexDigits
    split
    · simp [hexValue, (hexByte_fin ⟨n, by omega⟩).2.1]
    · have := ih (n / 16) (by omega)
      simp only [hexValue, List.foldl_append, List.foldl_cons, List.foldl_nil] at this ⊢
      have h2 := (hexByte_fin ⟨n % 16, by omega⟩).2.1
      simp only at h2
      rw [this, h2]
      omega

theorem hexDigits_length_le (k : Nat) : ∀ n, n < 16 ^ (k + 1) → (hexDigits n).length ≤ k + 1 := by
  induction k with
  | zero => intro n h; unfold hexDigits; rw [if_pos (by simpa using h)]; simp
  | succ k ih =>
    intro n h
    unfold hexDigits
    split
    · simp
    · have := ih (n / 16) (by rw [Nat.pow_succ] at h; omega)
      simp; omega

/-! ## Field lines -/

/-- A field value after the colon: optional whitespace, the value, optional
whitespace, to the end of its (delimited) region. Encoded with one space. -/
def owsValue : Codec UInt8 (List UInt8) where
  encode v := SP :: v
  parser := do
    let raw ← takeWhile fun _ => true
    let v := stripOWS raw
    if valueOk v then pure v else Parser.fail ParseError.unexpected
  valid v := valueOk v = true
  follow r := r = []
  parse_encode v r hv hr := by
    subst hr
    have hall : ∀ l : List UInt8, l.takeWhile (fun _ => true) = l ∧ l.dropWhile (fun _ => true) = [] := by
      intro l; induction l <;> simp_all
    have hs : stripOWS (SP :: v) = v := by
      unfold valueOk at hv
      simp only [Bool.and_eq_true] at hv
      obtain ⟨⟨-, hh⟩, hl⟩ := hv
      have h1 : (SP :: v).dropWhile isOWS = v := by
        simp only [List.dropWhile_cons, show isOWS SP = true from rfl, ite_true]
        cases v with
        | nil => rfl
        | cons b t =>
          have : isVchar b = true := by simpa using hh
          simp [vchar_not_ows this]
      have h2 : v.reverse.dropWhile isOWS = v.reverse := by
        cases e : v.reverse with
        | nil => rfl
        | cons b t =>
          have hb : v.getLast? = some b := by
            rw [← List.head?_reverse, e]; rfl
          rw [hb] at hl
          have : isVchar b = true := by simpa using hl
          simp [vchar_not_ows this]
      simp [stripOWS, h1, h2]
    simp only [List.append_nil, parse_bind, parse_takeWhile, (hall _).1, (hall _).2,
      Reply.bind_ok, hs, hv, ite_true, parse_pure]

/-- A field name: a token, ended by a colon. -/
def fieldName : Codec UInt8 (List UInt8) :=
  Codec.delimited [COLON] (Codec.rest.guard fun l => isToken l = true)

/-- A field value: `owsValue`, ended by `CRLF`. -/
def fieldValue : Codec UInt8 (List UInt8) := Codec.delimited crlf owsValue

/-- A field line. -/
def field : Codec UInt8 Field :=
  (fieldName.seq fieldValue).map (fun p => ⟨p.1, p.2⟩) (fun f => (f.name, f.value)) fun _ => rfl

/-- The field section: field lines, then an empty line. -/
def fields : Codec UInt8 (List Field) := field.manyTill crlf

/-! ## Start lines -/

/-- `HTTP/1.1` and `HTTP/1.0`. -/
def http11 : List UInt8 := [72, 84, 84, 80, 47, 49, 46, 49]
def http10 : List UInt8 := [72, 84, 84, 80, 47, 49, 46, 48]

def Version.ofSum : Unit ⊕ Unit → Version
  | .inl _ => .http11
  | .inr _ => .http10

def Version.toSum : Version → Unit ⊕ Unit
  | .http11 => .inl ()
  | .http10 => .inr ()

theorem Version.ofSum_toSum (v : Version) : Version.ofSum (Version.toSum v) = v := by
  cases v <;> rfl

/-- The version at the end of a request line. -/
def requestVersion : Codec UInt8 Version :=
  (Codec.sum (http11 ++ crlf) (http10 ++ crlf) Codec.unit Codec.unit).map
    Version.ofSum Version.toSum Version.ofSum_toSum

/-- The version at the start of a status line. -/
def responseVersion : Codec UInt8 Version :=
  (Codec.sum (http11 ++ [SP]) (http10 ++ [SP]) Codec.unit Codec.unit).map
    Version.ofSum Version.toSum Version.ofSum_toSum

/-- A request method: a token, then a space. -/
def method : Codec UInt8 (List UInt8) := Codec.delimited [SP] (Codec.rest.guard fun l => isToken l = true)

/-- A request target, then a space. -/
def target : Codec UInt8 (List UInt8) := Codec.delimited [SP] (Codec.rest.guard fun l => isTarget l = true)

/-- A status code: three digits, then a space. -/
def status : Codec UInt8 Nat :=
  Codec.delimited [SP] ((Codec.rest.guard fun l => isStatus l = true).map decimalValue decimalBytes
    decimalValue_decimalBytes)

/-- A reason phrase, then `CRLF`. -/
def reason : Codec UInt8 (List UInt8) := Codec.delimited crlf (Codec.rest.guard fun l => reasonOk l = true)

/-- A request head. -/
def requestHead : Codec UInt8 RequestHead :=
  (method.seq (target.seq (requestVersion.seq fields))).map
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun h => (h.method, h.target, h.version, h.fields))
    fun _ => rfl

/-- A response head. -/
def responseHead : Codec UInt8 ResponseHead :=
  (responseVersion.seq (status.seq (reason.seq fields))).map
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun h => (h.version, h.status, h.reason, h.fields))
    fun _ => rfl

/-! ## Framing -/

/-- The values of the fields with a (lower-case) name. -/
def valuesOf (fs : List Field) (name : List UInt8) : List (List UInt8) :=
  (fs.filter fun f => lowerBytes f.name == name).map (·.value)

/-- RFC 9112 section 6.3, as h11 applies it: `Transfer-Encoding` wins and
must be exactly `chunked`; otherwise every `Content-Length` must be the same
digits, at most `maxIntDigits` of them (h11's `int()`), checked before they
are converted; otherwise there is no explicit framing. -/
def framingOf (fs : List Field) : Framing :=
  match valuesOf fs (ascii "transfer-encoding") with
  | [] =>
    match valuesOf fs (ascii "content-length") with
    | [] => .none
    | v :: vs =>
      if isDigits v && v.length ≤ maxIntDigits && vs.all (· == v) then .length (decimalValue v) else .invalid
  | [te] => if lowerBytes te == ascii "chunked" then .chunked else .invalid
  | _ => .invalid

/-- A request without framing headers has no body. -/
def requestFraming (h : RequestHead) : Framing := framingOf h.fields

/-- A response to `HEAD`, a 1xx, 204 or 304 response has no body; one
without framing headers runs to the end of the connection. -/
def responseFraming (requestMethod : List UInt8) (h : ResponseHead) : Framing :=
  if requestMethod == ascii "HEAD" || h.status / 100 == 1 || h.status == 204 || h.status == 304 then .none
  else match framingOf h.fields with
    | .none => .close
    | f => f

/-! ## Chunked transfer coding -/

/-- `chunk-size [chunk-ext] CRLF`: one to `maxChunkDigits` hex digits, an optional extension
(ignored; it must start with `;` or whitespace), `CRLF`. -/
def chunkSizeLine {ε : Type} [ParseError ε] : Parser UInt8 ε Nat := do
  let ds ← takeWhile isHexByte
  if ds.isEmpty || ds.length > maxChunkDigits then Parser.fail ParseError.unexpected else
  let ext ← takeWhile (· != CR)
  if ext.isEmpty || ext.head? == some 59 || (ext.head?.map isOWS).getD false then
    Parser.lit crlf
    pure (hexValue ds)
  else Parser.fail ParseError.unexpected

/-- One chunk of data: its size line, the bytes, `CRLF`. A size of zero is
the last chunk, which this parser does not read (it fails without
consuming). -/
def chunk {ε : Type} [ParseError ε] : Parser UInt8 ε ByteArray := attempt do
  let n ← chunkSizeLine
  if n = 0 then Parser.fail ParseError.unexpected else
  let d ← takeBytes n
  Parser.lit crlf
  pure d

/-- The last chunk: size zero, any trailer fields (ignored), `CRLF`. -/
def lastChunk {ε : Type} [ParseError ε] : Parser UInt8 ε Unit := do
  let n ← chunkSizeLine
  if n ≠ 0 then Parser.fail ParseError.unexpected else
  let _ ← Parser.many (notFollowedBy (Parser.lit crlf) *> field.parser)
  Parser.lit crlf

/-- The encoding of one chunk. -/
def encodeChunk (d : ByteArray) : List UInt8 := hexDigits d.size ++ crlf ++ d.data.toList ++ crlf

/-- The encoding of the last chunk, without trailers. -/
def lastChunkBytes : List UInt8 := hexDigits 0 ++ crlf ++ crlf

end H1

end LeanHttpx
