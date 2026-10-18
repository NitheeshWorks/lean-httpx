import LeanHttpx.DataTypes.Models
import LeanHttpx.RepoImpl.URLOps
import LeanHttpx.RepoImpl.Hpack

/-!
# The fields of a request on HTTP/2

What httpcore's `_send_request_headers` hands h2, after h2's
`normalize_outbound_headers`: the pseudo-headers, then the request's fields
but `Host` (it is `:authority`); every name lower-cased; names and values
stripped of surrounding whitespace; the connection-specific fields of RFC
9113 section 8.2.2 removed; `authorization`, `proxy-authorization` and a
`cookie` shorter than 20 bytes never indexed.
-/

namespace LeanHttpx

namespace H2

open Hpack

/-- ASCII lower case of bytes (Python's `bytes.lower`). -/
def lowerBytes (b : ByteArray) : ByteArray :=
  ⟨b.data.map fun x => if 65 ≤ x && x ≤ 90 then x + 32 else x⟩

/-- Python's `bytes.isspace` for one byte: space, tab, LF, VT, FF, CR. -/
def isWs (x : UInt8) : Bool := x == 32 || (9 ≤ x && x ≤ 13)

/-- Python's `bytes.strip()`: surrounding whitespace removed. -/
def stripWs (b : ByteArray) : ByteArray :=
  let l := b.data.toList
  ⟨((l.dropWhile isWs).reverse.dropWhile isWs).reverse.toArray⟩

/-- A field a request on HTTP/2 must not carry (RFC 9113 section 8.2.2):
h2's `CONNECTION_HEADERS`, and `te` with any value but `trailers`. -/
def connectionSpecific (f : HeaderField) : Bool :=
  ["connection", "keep-alive", "proxy-connection", "transfer-encoding", "upgrade"].any
    (fun n => f.name == n.toUTF8) ||
  (f.name == "te".toUTF8 && lowerBytes f.value != "trailers".toUTF8)

/-- h2's `_secure_headers`: credentials, and short cookies, never indexed. -/
def neverIndex (name value : ByteArray) : Bool :=
  name == "authorization".toUTF8 || name == "proxy-authorization".toUTF8 ||
  (name == "cookie".toUTF8 && value.size < 20)

/-- One field as h2 sends it: name lower-cased, both sides stripped. -/
def outbound (name value : ByteArray) : HeaderField :=
  let n := stripWs (lowerBytes name)
  let v := stripWs value
  ⟨n, v, neverIndex n v⟩

/-- **The fields of a request**, in the order sent. -/
def requestFields (r : Request) : List HeaderField :=
  let authority := (r.headers.get? "Host").getD r.url.netloc
  let pseudo := [(":method", r.method), (":authority", authority), (":scheme", r.url.scheme),
    (":path", r.url.rawPath)]
  let rest := r.headers.raw.filter fun (k, _) => (lowerBytes k.toUTF8) != "host".toUTF8
  ((pseudo ++ rest).map fun (k, v) => outbound k.toUTF8 v.toUTF8).filter (!connectionSpecific ·)

end H2

end LeanHttpx
