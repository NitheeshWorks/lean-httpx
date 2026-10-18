import LeanHttpx.Proofs.URL
import LeanHttpx.Proofs.H1
import LeanHttpx.Specifications.URL
import LeanHttpx.Specifications.H1

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` bundles a layer's headline specifications with a proof
term for each. A specification with no proof is a compile error the moment
it needs a field here: you cannot construct a `Verified<Layer>` value without
every proof in hand. If a stated specification turns out false, its slot's
type flips to a refutation rather than being dropped, so this file stays an
honest map of what is verified.
-/

namespace LeanHttpx

open Spec

/-- URLs (RFC 3986, `httpx/_urlparse.py`). -/
structure VerifiedURL where
  /-- `url_parse_print_ext`: parse after print is the identity. -/
  parsePrint : URLParsePrint

/-- HTTP/1.1 messages (RFC 9112). -/
structure VerifiedH1 where
  /-- `h1_request_print_parse`. -/
  requestPrintParse : RequestPrintParse
  /-- `h1_response_parse_print_ext`. -/
  responseParsePrint : ResponseParsePrint
  /-- `chunked_decode_encode`. -/
  chunkedDecodeEncode : ChunkedDecodeEncode

def theVerifiedURL : VerifiedURL where
  parsePrint u h := url_parse_print_ext u h

def theVerifiedH1 : VerifiedH1 where
  requestPrintParse r rest h := H1.h1_request_print_parse r h rest
  responseParsePrint m r rest h := H1.h1_response_parse_print_ext m r h rest
  chunkedDecodeEncode cs rest h := H1.chunked_decode_encode cs h rest

end LeanHttpx
