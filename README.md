# lean-httpx

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [httpx and httpcore](https://github.com/encode/httpx) to Lean 4: an
HTTP client whose logic is pure functions over a transport, with the URL parser, the
HTTP/1.1 codec, cookie matching, redirects and Basic credentials proved.

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo with its proofs. This one depends on
[lean-json](https://github.com/NitheeshWorks/lean-json) and the shared theories of
[lean-keel](https://github.com/NitheeshWorks/lean-keel) (`Keel.Parse`, `Keel.Codec`).

## Quickstart

httpx's own quickstart, translated:

```python
>>> import httpx
>>> r = httpx.get('https://www.example.org/')
>>> r
<Response [200 OK]>
>>> r.status_code
200
>>> r.headers['content-type']
'text/html; charset=UTF-8'
>>> r.text
'<!doctype html>\n<html>\n<head>\n<title>Example Domain</title>...'
```

```lean
import LeanHttpx
open LeanHttpx LeanJson

def main : IO Unit := do
  let r ← LeanHttpx.get "http://www.example.org/"
  IO.println (reprStr r)              -- <Response [200 OK]>
  IO.println r.statusCode             -- 200
  IO.println r.headers["content-type"]!
  IO.println r.text
```

A client, as in httpx's docs (`docs/advanced/clients.md`, `docs/advanced/transports.md`):

```lean
def handler (request : Request) : Response :=
  Response.new 200 (json := json% {"text": "Hello, world!"})

def demo : IO Unit := do
  let client ← Client.new (transport := MockTransport handler) (headers := [("X-Auth", "from-client")])
  let r ← client.get "https://example.org/" (params := [("q", "search")])
  let data ← r.json                   -- {"text": "Hello, world!"}
  let r ← client.post "https://example.org/" (json := json% {"key": "value"})
  let r ← r.raiseForStatus
  let r ← client.get "https://example.org/old" (followRedirects := true)
  let r ← client.get "https://example.org/" (auth := ("user", "pass"))
  pure ()
```

| httpx | lean-httpx |
|---|---|
| `httpx.get(url, params=..., headers=...)` | `LeanHttpx.get url (params := …) (headers := …)` |
| `httpx.Client(base_url=..., follow_redirects=True)` | `Client.new (baseUrl := …) (followRedirects := true)` |
| `client.post(url, json=..., data=..., content=...)` | `client.post url (json := …) (data := …) (content := …)` |
| `response.status_code`, `.text`, `.json()`, `.raise_for_status()` | `r.statusCode`, `r.text`, `r.json`, `r.raiseForStatus` |
| `httpx.URL(s)`, `url.join(r)`, `url.copy_with(...)` | `URL.parse s`, `u.join r`, `u.copyWith …` |
| `httpx.Headers`, `httpx.QueryParams`, `httpx.Cookies` | `Headers`, `QueryParams`, `Cookies` |
| `httpx.BasicAuth`, `httpx.DigestAuth`, `auth=("u", "p")`, `auth=func` | `BasicAuth u p`, `← DigestAuth u p`, `some ("u", "p")`, `FunctionAuth f` |
| `httpx.MockTransport(handler)`, `httpx.ASGITransport(app)`, `httpx.HTTPTransport()` | `MockTransport handler`, `ASGITransport.mk app …`, `HTTPTransport` |
| `httpx.HTTPStatusError`, `httpx.TooManyRedirects`, ... | `HTTPError.httpStatusError`, `.tooManyRedirects`, ... |

Errors: in `IO`, an httpx exception is an `IO.userError` with the exception's name and
message (`TooManyRedirects: Exceeded maximum allowed redirects.`); the pure functions
return `Except HTTPError`, which lifts into `IO` automatically.

### For in-process test clients

lean-starlette's `TestClient` is a `Client` over a `Transport`:

```lean
structure Transport where
  handleRequest : Request → IO Response
  close : IO Unit := pure ()
```

`ASGITransport` (`LeanHttpx.RepoImpl.Transports`) is the reference: it builds an
`ASGIScope` from the request, gives the body to the app's `receive`, and collects
`ASGIMessage.httpResponseStart` / `httpResponseBody` from `send`. A transport returns
the raw body in `Response.stream`; the client decodes it (`Content-Encoding`), runs the
cookie jar, redirects and auth.

## What is proved

Every theorem below is checked by Lean with no axioms beyond `propext`, `Quot.sound` and
`Classical.choice`; each has a slot in `LeanHttpx/Proofs/Verified.lean`.

* **URL round trip** (`url_parse_print_ext`): every URL within httpx's length limit
  prints to text that parses back to it.
  `URL.parse u.toString = .ok u` given `u.toString.length ≤ 65536`.
* **Reference resolution** (`url_join_rfc3986`): `URL.join` gives RFC 3986's answer on
  all 42 examples of section 5.4.
* **HTTP/1.1 codecs** (`h1_request_print_parse`, `h1_response_parse_print_ext`): a valid
  message parses back from its bytes on any continuation:
  `parseResponse m (printResponse m r ++ rest) = some (r, rest)`. The codecs are built from
  `Keel.Codec` combinators, so the law is the combinators' law.
* **The transport decodes with the codec** (`readResponse_eq_parseResponse`): the reader
  `HTTPTransport` uses, which copies a `Content-Length` body as one slice, is
  `parseResponse`.
* **Chunked coding** (`chunked_decode_encode`): `decodeChunked (encodeChunked cs ++ rest) =
  some (cs, rest)` for non-empty chunks below 2^80 bytes (h11's 20 hex digits).
* **Header precedence** (`headers_merge_precedence`): after merging, a name has the
  request's values if it has any, else the client's.
* **Cookie matching** (`cookie_match_domain_path`): a request carries exactly the stored
  cookies whose domain matches, whose path path-matches (RFC 6265 section 5.1.4) and that
  are not expired or secure-only over plain HTTP.
* **Cookie jar** (`cookie_jar_set_get`): `(jar.set n v d p).get? n d p = .ok (some v)`.
* **Redirect method** (`redirect_method_rewrite`): 302/303 become `GET` (except `HEAD`),
  301 `POST` becomes `GET`, everything else keeps its method; 307/308 keep the body.
* **Redirect bound** (`redirect_bounded`): a response's redirect history has at most
  `max_redirects` entries (its type), and a server that always redirects ends in
  `TooManyRedirects`; such a server exists (`redirect_bounded_satisfiable`).
* **Basic credentials** (`basic_auth_header`): `parseBasicAuth (basicAuthHeader u p) =
  some (u, p)` when the user-id has no colon; from `Base64.decode_encode`.

Tested rather than proved: Digest auth and the hash functions (RFC vectors), inflate,
`Set-Cookie` parsing, query strings, the chunked fast path, and `HTTPTransport` itself
against a hostile server (head limit 100 KiB, framing, error classes, numbers bounded before
conversion, a 200 MiB body within twice upstream's time and memory). See [CONTRIBUTING.md](CONTRIBUTING.md#tested-not-proved).

## Getting started

```
lake build            # library, proofs, and both test executables
lake exe props        # property tests (seeded; `lake exe props 42`)
lake exe conformance  # cases re-expressed from the upstream test suites
scripts/bench.sh      # HTTPTransport against a hostile local server, and the benchmark
scripts/check.sh      # the whole CI gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`; `elan` installs it).

## Status

Milestone 8a: the HTTP/1.1 client. HTTP/2 is milestone 8b.

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
