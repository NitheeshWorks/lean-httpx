import LeanHttpx.Proofs.H1
import LeanHttpx.Proofs.Auth
import LeanHttpx.Proofs.URL
import LeanHttpx.Proofs.H2
import LeanHttpx.Proofs.Hpack
import LeanHttpx.Specifications.H2

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

/-- Chunk-encode non-empty chunks, each below `maxChunkSize`. -/
def encodeChunks (cs : List ByteArray) :
    Option {b : ByteArray // ∀ rest, decodeChunked (b ++ rest) = some (cs, rest)} :=
  if h : ∀ c ∈ cs, 0 < c.size ∧ c.size < maxChunkSize then some ⟨encodeChunked cs, chunked_decode_encode cs h⟩ else none

end H1

namespace H2

/-- Print a frame, if it is valid and its payload fits `max` (below 2^24):
the bytes parse back to it whatever follows them. -/
def encodeFrame (max : Nat) (f : Frame) :
    Option {b : ByteArray // ∀ rest, parseFrame max (b ++ rest) = .done f rest} :=
  if h : f.ok = true ∧ f.toRaw.payload.size ≤ max ∧ max < 2 ^ 24 then
    some ⟨printFrame f, h2_frame_parse_print_ext max f h.1 h.2.1 h.2.2⟩
  else none

end H2

namespace Hpack

/-- An encoder and the peer's decoder, in step (`Spec.InStep`). -/
structure Synced where
  enc : Encoder
  dec : Decoder
  inStep : Spec.InStep enc dec

/-- Both sides new: empty tables of 4096 bytes. -/
def Synced.new : Synced := ⟨{}, {}, rfl, ⟨by decide, by decide⟩, by decide, by simp⟩

/-- Encode a header list, if its fields fit and it is within the decoder's
header-list limit: the block, the sides after it, still in step, and the
proof that the decoder reads the block back to the list. -/
def Synced.encode (s : Synced) (fs : List HeaderField) :
    Option {p : ByteArray × Synced // s.dec.decode p.1 = .ok (fs, p.2.dec)} :=
  if h : Spec.FieldsFit fs ∧ listSize fs ≤ s.dec.maxHeaderListSize then
    let r := s.enc.encode fs
    have hst := s.inStep
    some ⟨(r.1, ⟨r.2, { s.dec with table := r.2.table }, rfl,
        wf_encode s.enc fs hst.2.1 (fun n hn => by have := hst.2.2.2 n hn; have := hst.2.2.1; omega) h.1,
        hst.2.2.1, by simp [r, encode_pending]⟩),
      hpack_decode_encode s.enc s.dec fs hst.1 hst.2.1 hst.2.2.1 hst.2.2.2 h.1 h.2⟩
  else none

/-- Encode without the dynamic table, if the fields fit and the list is
within the decoder's limit: a block the decoder reads back, unchanged. -/
def encodeStaticChecked (d : Decoder) (fs : List HeaderField) :
    Option {b : ByteArray // d.decode b = .ok (fs, d)} :=
  if h : Spec.FieldsFit fs ∧ listSize fs ≤ d.maxHeaderListSize then
    some ⟨encodeStatic fs, hpack_decode_encode_static d fs h.1 h.2⟩
  else none

end Hpack

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
