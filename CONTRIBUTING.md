# Contributing to lean-httpx

`README.md` covers usage. This file covers the architecture, the verification
rules, the repository layout and the conventions, and is the document to keep
current when the code changes.

## Architecture

`LeanHttpx/` is layered bottom-up; each layer imports only the ones below it, so a
proof at one layer rewrites with lemmas from beneath it instead of unfolding
to bytes:

| Directory | Holds | Proved? |
|---|---|---|
| `DataTypes/` | structures and inductives; invariants are fields | n/a |
| `RepoImpl/` | executable definitions; total, structural recursion | subject of proofs |
| `Specifications/` | the properties, in `Prop` | the contract |
| `Proofs/` | theorems; `Proofs/Verified.lean` bundles one `Verified<Layer>` per layer | yes |
| `APIs/` | the public surface, returning refinements | by construction |
| `Transport.lean` | `HTTPTransport`, the only module doing network I/O | no; tested |

Module map: `RepoImpl/URL.lean` (parser and printer), `URLOps.lean` (properties,
`copyWith`, `join`), `Headers.lean` (`Headers`, `QueryParams`), `Cookies.lean`
(the `http.cookiejar` default policy), `Models.lean` (`Request.new`, `Response.new`
and properties), `Auth.lean`, `Redirects.lean` (pure redirect logic and the bounded
loop over any monad), `Client.lean`, `Transports.lean` (`Transport`, `MockTransport`,
`ASGITransport`), `H1.lean`/`H1Body.lean` (the HTTP/1.1 codecs, built from
`Keel.Codec`), `Codec.lean` (three combinators added to `Keel.Codec`: `guard`,
`fail`, `bytesN`), `Decoders.lean` (inflate, gzip, zlib), `Base64.lean`, `Hash.lean`,
`Text.lean`. `scripts/gen-aggregators.py` regenerates the layer aggregator modules.

**Stack depth.** Every parser of network input is iterative: `Keel.Parser.many`,
`takeBytes` (a loop into a `ByteArray`), or a bounded `for` loop. There is no
`Parser.fix` (so no need for `fixDepth`) and no recursion per byte; a 5 MB body,
20000 header lines and a 60000-character URL parse in constant stack.

Everything except the transport module is a pure function. This is
load-bearing: a round-trip property of a function is an equation that
`omega` and `simp` attack directly; the same property of a procedure would
be a Hoare triple over a heap.

## Verification <a name="verification"></a>

* **Weak preconditions, strong postconditions.** A public function takes the
  minimal hypothesis its body needs (usually none; the refinement lives in the
  input type) and returns the strongest useful statement, typically a round
  trip or a membership, as `{r // Post r}` or `Except Err {r // Post r}`.
* **Refinement types are subtypes with `Decidable` predicates**, so the same
  predicate is checked at runtime (`if h : P x`) and used in proofs.
* **Totality.** No `partial def` or `unsafe` under `LeanHttpx/`, and
  `scripts/gate-allow.txt` is empty. Parsers are `Keel.Parse` parsers (total by
  construction, well-founded on the input left); loops over sockets and bits are
  `for` loops over bounded ranges.
* **`_ext` lemmas.** A decoder lemma holds on any continuation of the buffer and
  reports the final position, so field lemmas compose. Do not add a lemma that
  only holds at the end of a buffer; it is unusable one field later.
* **Numbers.** `Nat`/`Int`/decimal-as-rational in proofs. `Float` only at the
  boundary via `Float.toBits`. Never `bv_decide` or `native_decide`.
* **The gate.** `scripts/check.sh` runs what CI runs: build, `sorry` grep,
  `scripts/Axioms.lean` (every theorem under `LeanHttpx` reaches only `propext`,
  `Quot.sound`, `Classical.choice`), `lake exe props`, `lake exe conformance`,
  the traceability check.

### Tested, not proved <a name="tested-not-proved"></a>

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`.

* **Digest authentication and the hash functions** (MD5, SHA-1, SHA-256,
  SHA-512): tested against the RFC 7616 and FIPS vectors. Proving a hash
  function is out of scope; the kernel cannot evaluate them for a `decide`
  proof of the vectors (they use `ByteArray` primitives).
* **Inflate, gzip and zlib decoding**: tested on upstream's cases and for
  totality on random input. A proof would need a model of DEFLATE.
* **`Set-Cookie` parsing and `set_ok`** (`http.cookiejar` semantics, including
  `http2time` dates): tested on upstream's cases. What a jar sends is proved
  (`cookie_match_domain_path`).
* **Query strings** (`parse_qs`/`urlencode`): tested as a round trip on random
  keys and values.
* **`URL.parse` reaches canonical form**: `build` checks `ParseResult.Canonical`
  at run time; that the check never fails on any input is tested on random
  URL-like strings (it is what makes `URL` carry its invariant).

### Deviations from upstream

Each is a row with `status = "deviation"` in `docs/traceability.toml`. Upstream
defects found while porting are recorded as UP-035 to UP-041 (see
`upstream-spec/findings.jsonl`).

* URL normal form, to make `url_parse_print_ext` true: host percent-escapes keep
  their case (UP-035); a path starting with `//` without an authority is invalid
  (UP-036); a relative path whose first segment reads as a scheme is invalid
  (UP-037); ports are digits only (UP-038); the default port is compared with the
  lower-cased scheme (UP-039). `URL.join` keeps empty path segments (RFC 3986,
  UP-040).
* IDNA host names are rejected (`Invalid IDNA hostname`); IPv6 zone indices are
  limited to unreserved characters.
* The `Port` cookie attribute is ignored; `response.cookies` evaluates expiry at
  time 0 (the client's jar uses the real clock).
* Text decoding knows UTF-8, ASCII and ISO-8859-1; other charsets fall back to
  the default encoding. Brotli and zstd are not decoded.
* No streaming responses, multipart `files=`, WSGI, proxies or environment
  configuration. `AsyncClient` is the same client in `IO`.
* `HTTPTransport` sends one request per connection with `Connection: close`;
  there is no TLS (`https` is `UnsupportedProtocol`) and no connection pool.
* The default `User-Agent` is `lean-httpx/0.1.0`.
* An authentication flow sends at most 32 requests (upstream's generators are
  unbounded; Basic and Digest send at most two).

## Tests

* `tests/Props.lean`: seeded property tests, no dependencies, under a second.
* `tests/Conformance.lean`: cases re-expressed from the upstream suite; each
  names the upstream test (`tests/test_x.py::test_y`).
* `tests/pbt/`: a separate Lake package, the one place an external dependency
  (`plausible`) is taken.

## Traceability

`docs/traceability.toml` links upstream behaviour to the Lean symbol, theorem
and test that realise it. Add a row when behaviour is newly implemented,
tested-only, excluded, or deviates. CI fails if a registered symbol does not
resolve.

## Conventions

* Lean 4 `leanprover/lean4:v4.35.0`; no Mathlib; the core library depends only on Lean
  core and the sibling `lean-*` repos listed in `lakefile.toml`, pinned by
  commit in `lake-manifest.json`.
* Choose the definition that suits the automation over a prettier one with a
  harder proof.
* No upstream code is copied; the upstream test suite and docs are the spec.
