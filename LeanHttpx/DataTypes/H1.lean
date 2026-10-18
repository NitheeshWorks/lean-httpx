import LeanHttpx.DataTypes.Chars

/-!
# HTTP/1.1 messages on the wire (RFC 9112)

The client side of HTTP/1.1 that httpcore delegates to `h11`: a request head
and body to send, a response head and body to receive. Names and values are
the bytes on the wire; `Headers` (in `Models.lean`) is the decoded view.

The byte classes are RFC 9110 section 5.6.2 (`tchar`), section 5.5
(`field-vchar`, `obs-text`) and RFC 9112 section 3.2 (`request-target`).
-/

namespace LeanHttpx

namespace H1

/-- RFC 9110 `tchar`: a byte of a token. -/
def isTchar (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) ||
  b == 33 || b == 35 || b == 36 || b == 37 || b == 38 || b == 39 || b == 42 || b == 43 ||
  b == 45 || b == 46 || b == 94 || b == 95 || b == 96 || b == 124 || b == 126

/-- A token: one or more `tchar`. -/
def isToken (l : List UInt8) : Bool := !l.isEmpty && l.all isTchar

/-- RFC 9110 `field-vchar`: visible ASCII or `obs-text`. -/
def isVchar (b : UInt8) : Bool := (33 ≤ b && b ≤ 126) || 128 ≤ b

/-- Optional whitespace: space or horizontal tab. -/
def isOWS (b : UInt8) : Bool := b == 32 || b == 9

/-- A field value in normal form: field-vchars and inner whitespace, with
neither leading nor trailing whitespace (the parser strips both). -/
def valueOk (v : List UInt8) : Bool :=
  v.all (fun b => isVchar b || isOWS b) &&
  (v.head?.map isVchar).getD true && (v.getLast?.map isVchar).getD true

/-- A request target: one or more visible ASCII bytes. -/
def isTarget (l : List UInt8) : Bool := !l.isEmpty && l.all fun b => 33 ≤ b && b ≤ 126

/-- A reason phrase: field-vchars and whitespace. -/
def reasonOk (l : List UInt8) : Bool := l.all fun b => isVchar b || isOWS b

/-- Three decimal digits, the first not zero: a status code 100 to 999. -/
def isStatus (l : List UInt8) : Bool :=
  l.length == 3 && l.all (fun b => 48 ≤ b && b ≤ 57) && l.head? != some 48

/-- A header field on the wire. -/
structure Field where
  name : List UInt8
  value : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- A field the codec round-trips: a token name and a normal-form value. -/
def Field.ok (f : Field) : Bool := isToken f.name && valueOk f.value

/-- The protocol version of a message. -/
inductive Version where
  | http10
  | http11
  deriving DecidableEq, Repr, Inhabited

/-- `HTTP/1.0` or `HTTP/1.1`, as `Response.http_version` reports it. -/
def Version.toString : Version → String
  | .http10 => "HTTP/1.0"
  | .http11 => "HTTP/1.1"

/-- How a message body is delimited (RFC 9112 section 6.3). -/
inductive Framing where
  /-- No body. -/
  | none
  /-- `Content-Length: n`. -/
  | length (n : Nat)
  /-- `Transfer-Encoding: chunked`. -/
  | chunked
  /-- A response body that runs to the end of the connection. -/
  | close
  /-- Conflicting or malformed framing headers. -/
  | invalid
  deriving DecidableEq, Repr, Inhabited

/-- A request head: method, target, version and fields. -/
structure RequestHead where
  method : List UInt8
  target : List UInt8
  version : Version := .http11
  fields : List Field
  deriving DecidableEq, Repr, Inhabited

/-- A request message. -/
structure Request where
  head : RequestHead
  body : ByteArray

/-- A status line and fields. -/
structure ResponseHead where
  version : Version := .http11
  status : Nat
  reason : List UInt8
  fields : List Field
  deriving DecidableEq, Repr, Inhabited

/-- A response message. -/
structure Response where
  head : ResponseHead
  body : ByteArray

end H1

end LeanHttpx
