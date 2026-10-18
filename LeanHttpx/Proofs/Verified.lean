import LeanHttpx.Proofs.URL
import LeanHttpx.Proofs.H1
import LeanHttpx.Specifications.URL
import LeanHttpx.Specifications.H1
import LeanHttpx.Specifications.Client
import LeanHttpx.Proofs.Headers
import LeanHttpx.Proofs.Cookies
import LeanHttpx.Proofs.Redirects
import LeanHttpx.Proofs.Auth
import LeanHttpx.Proofs.URLJoin

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
structure VerifiedURL : Prop where
  /-- `url_parse_print_ext`: parse after print is the identity. -/
  parsePrint : URLParsePrint
  /-- `url_join_rfc3986`: every RFC 3986 section 5.4 example resolves as the RFC says. -/
  joinRfc3986 : rfc3986Examples.all (fun e => joinsTo "http://a/b/c/d;p?q" e.1 e.2) = true

/-- HTTP/1.1 messages (RFC 9112). -/
structure VerifiedH1 : Prop where
  /-- `h1_request_print_parse`. -/
  requestPrintParse : RequestPrintParse
  /-- `h1_response_parse_print_ext`. -/
  responseParsePrint : ResponseParsePrint
  /-- `chunked_decode_encode`. -/
  chunkedDecodeEncode : ChunkedDecodeEncode
  /-- `readResponse_eq_parseResponse`: what `HTTPTransport` decodes with. -/
  readerIsCodec : ReaderIsCodec

/-- The client layer: headers, cookies, redirects, authentication. -/
structure VerifiedClient : Prop where
  /-- `headers_merge_precedence`. -/
  headersMerge : HeadersMergePrecedence
  /-- `cookie_match_domain_path`. -/
  cookieMatch : CookieMatch
  /-- `cookie_jar_set_get`. -/
  cookieSetGet : CookieSetGet
  /-- `redirect_method_rewrite`. -/
  redirectMethod : RedirectMethodRewrite
  /-- `redirect_bounded`. -/
  redirectBounded : RedirectBounded
  /-- `redirect_bounded_satisfiable`: its hypothesis holds of a real server. -/
  redirectBoundedSatisfiable : RedirectBoundedSatisfiable
  /-- `basic_auth_header`. -/
  basicAuth : BasicAuthHeader

theorem theVerifiedURL : VerifiedURL where
  parsePrint u h := url_parse_print_ext u h
  joinRfc3986 := url_join_rfc3986

theorem theVerifiedClient : VerifiedClient where
  headersMerge := Headers.headers_merge_precedence
  cookieMatch j url now ck := cookie_match_domain_path j url now ck
  cookieSetGet := cookie_jar_set_get
  redirectMethod := redirect_method_rewrite
  redirectBounded send hs jar m q := redirect_bounded send hs jar m q
  basicAuth u p h := basic_auth_header u p h
  redirectBoundedSatisfiable := redirect_bounded_satisfiable

theorem theVerifiedH1 : VerifiedH1 where
  requestPrintParse r rest h := H1.h1_request_print_parse r h rest
  responseParsePrint m r rest h := H1.h1_response_parse_print_ext m r h rest
  chunkedDecodeEncode cs rest h := H1.chunked_decode_encode cs h rest
  readerIsCodec := H1.readResponse_eq_parseResponse

end LeanHttpx
