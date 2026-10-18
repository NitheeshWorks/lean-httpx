import LeanHttpx.Proofs.H1
import LeanHttpx.Proofs.Auth
import LeanHttpx.Proofs.URL

/-!
# APIs: wire encodings with their round trips in the type

The checked forms of the codecs: each takes the weakest precondition (the
Boolean check of the message, decided at run time) and returns the bytes
with the round trip they satisfy on any continuation.
-/

namespace LeanHttpx

namespace H1

/-- Print a request, if it is valid: the bytes parse back to it whatever
follows them. -/
def encodeRequest (r : Request) :
    Option {b : ByteArray // ∀ rest, parseRequest (b ++ rest) = some (r, rest)} :=
  if h : r.ok = true then some ⟨printRequest r, h1_request_print_parse r h⟩ else none

/-- Print a response to a request with method `m`, if it is valid. -/
def encodeResponse (m : List UInt8) (r : Response) :
    Option {b : ByteArray // ∀ rest, parseResponse m (b ++ rest) = some (r, rest)} :=
  if h : r.ok m = true then some ⟨printResponse m r, h1_response_parse_print_ext m r h⟩ else none

/-- Chunk-encode non-empty chunks. -/
def encodeChunks (cs : List ByteArray) :
    Option {b : ByteArray // ∀ rest, decodeChunked (b ++ rest) = some (cs, rest)} :=
  if h : ∀ c ∈ cs, 0 < c.size then some ⟨encodeChunked cs, chunked_decode_encode cs h⟩ else none

end H1

/-- The Basic `Authorization` value of credentials whose user-id has no
colon, with the proof that it decodes back to them. -/
def basicAuthorization (u p : String) (h : ':' ∉ u.toList) :
    {v : String // parseBasicAuth v = some (u, p)} :=
  ⟨basicAuthHeader u p, basic_auth_header u p h⟩

/-- The text of a URL within the length limit, with the proof that it parses
back to the URL. -/
def URL.toCheckedString (u : URL) : Option {s : String // URL.parse s = .ok u} :=
  if h : u.toString.length ≤ URLParse.maxUrlLength then some ⟨u.toString, url_parse_print_ext u h⟩ else none

end LeanHttpx
