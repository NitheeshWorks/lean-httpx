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
| `Transport.lean` | `HTTPTransport`, network I/O for HTTP/1.1 | no; tested |
| `Transport2.lean` | `HTTP2Transport`, network I/O for HTTP/2: a pool of multiplexed connections | no; tested |

**HTTP/2 concurrency.** Many tasks share one HTTP/2 connection, and no
lock is held across a socket operation or a wait: a `Std.Mutex` holds the
connection state only while it is updated. One reader per connection, on
its own thread, does every read while a stream is open (and stops when none
is, so an idle client holds no thread); a task waiting for its response or
for a free stream leaves an `IO.Promise` and waits on it with its timeout,
and the reader resolves the promises after every change; whoever has
output writes it and any that arrives meanwhile. A blocking lock held
across a read parks the runtime's worker threads, which the socket and
timer continuations need: that deadlocked six concurrent requests at the
default four threads. `tests/NativeH2.lean` runs 64 concurrent requests on
one client and a stalled stream beside a busy one, under one and two Lean
threads (`scripts/bench.sh`). The read timeout is per stream, counted from
that stream's last progress; a stream that times out is reset.

Module map: `RepoImpl/URL.lean` (parser and printer), `URLOps.lean` (properties,
`copyWith`, `join`), `Headers.lean` (`Headers`, `QueryParams`), `Cookies.lean`
(the `http.cookiejar` default policy), `Models.lean` (`Request.new`, `Response.new`
and properties), `Auth.lean`, `Redirects.lean` (pure redirect logic and the bounded
loop over any monad), `Client.lean`, `Transports.lean` (`Transport`, `MockTransport`,
`ASGITransport`), `H1.lean`/`H1Body.lean` (the HTTP/1.1 codecs, built from
`Keel.Codec`, and `readResponse`, the transport's reader, proved equal to the
response codec), `H1Stream.lean` (where a response ends on a stream: the
head's blank line, the last chunk, and h11's limits), `Codec.lean` (three combinators added to `Keel.Codec`: `guard`,
`fail`, `bytesN`), `Decoders.lean` (inflate, gzip, zlib), `Base64.lean`, `Hash.lean`,
`Text.lean`. HTTP/2: `DataTypes/H2.lean` (frames, error codes, settings),
`RepoImpl/Bytes.lean` (big-endian readers and their lemmas), `H2Request.lean`
(a request's fields as h2 sends them), `H2Frame.lean`
(the frame codec), `Huffman.lean` (the RFC 7541 code, canonical from its
code lengths), `Hpack.lean` (integers, strings, tables, the encoder and
decoder), `H2Conn.lean` (the sans-I/O client connection: streams, flow
control, settings, limits). `scripts/gen-aggregators.py` regenerates the layer aggregator modules.

**Stack depth.** Every parser of network input is iterative: `Keel.Parser.many`,
`takeBytes` (a loop into a `ByteArray`), or a bounded `for` loop. There is no
`Parser.fix` (so no need for `fixDepth`) and no recursion per byte; a 5 MB body,
20000 header lines and a 60000-character URL parse in constant stack.

**Hostile input.** `HTTPTransport` reads as httpcore does: the head first,
at most 100 KiB of it (httpcore's `MAX_INCOMPLETE_EVENT_SIZE`; "Receive
buffer too long"), then exactly what the head's framing says (`Content-Length`
bytes, chunks to the last one, or to the end of the connection), every read
under the read timeout. Every number read from input is length-checked
before it is converted, since converting `n` digits costs time quadratic in
`n`: `Content-Length`, ports and cookie `Max-Age` and date fields at most
`maxIntDigits` (4300, Python's `int()` limit), chunk sizes at most 20 hex
digits (h11), status codes 3 digits. `tests/Native.lean` (`scripts/bench.sh`,
run in CI) checks all of this against a hostile server in the test process,
and bounds a 200 MiB body to twice upstream's time and memory. Errors keep
their httpx class (`ReadTimeout`, `RemoteProtocolError`, ...): a transport
raises them as `"Name: message"` and `Client.sendSingle` reads the class
back (`HTTPError.ofString?`); any other exception propagates unchanged.

**Hostile HTTP/2 peers.** `H2.Conn` is a pure state machine over bytes, and
every resource a peer can make it hold is bounded by `H2.Limits`: a frame
longer than `SETTINGS_MAX_FRAME_SIZE` (16384) is refused from its header,
before its payload is read, so the input buffer never holds more than one
frame; the HPACK dynamic table is within the size we advertised and a size
update above it is refused; the header list (65536, h2's
`max_header_list_size`) is checked field by field as it decodes, so a small
block cannot expand into a large list; a header block may span at most 64
CONTINUATION frames (h2's `CONTINUATION_BACKLOG`) and 256 KiB; at most 100
streams are open (our `MAX_CONCURRENT_STREAMS`, or fewer if the peer says
so); 10000 frames in a row that make no progress on a request (PING,
SETTINGS, PRIORITY, RST_STREAM, WINDOW_UPDATE, empty DATA, unknown types) end
the connection with ENHANCE_YOUR_CALM, which bounds PING and SETTINGS floods
and rapid reset; and queued output (acknowledgements the peer does not read)
is at most 1 MiB. `tests/NativeH2.lean` runs each attack against the client
from a hostile server in the test process, next to what httpx 0.28.1 does
on the same server, and bounds a 200 MiB body to twice upstream's time and
memory.

Everything except the transport modules is a pure function. This is
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
* **`H1.readChunked` and `H1.scanChunks`**: the transport copies a chunked
  body slice by slice (`readChunked`, which runs the codec's own size-line and
  last-chunk parsers) rather than through `takeBytes`, which reads byte by byte
  and is too slow for a large chunk; that it agrees with the chunked codec,
  and that `scanChunks` stops exactly where the codec ends, is tested on
  intact and damaged bodies. A `Content-Length` body needs no test: the
  transport's reader is the codec (`readResponse_eq_parseResponse`).
* **`HTTPTransport`** (time, memory, limits and error classes): native checks
  against a hostile local server and a benchmark, `tests/Native.lean`.
* **The Huffman code** (`Huffman.encode`, `decode`): tested against hpack's
  encodings (`tests/upstream/h2_golden.py`) and as a round trip on random
  bytes. The encoder sends a Huffman string only after checking it decodes
  back (`huffmanForm`), so the HPACK theorems hold without a proof of the
  code; a property shows the check never fails, so the encoder's blocks are
  hpack's default encoder's, byte for byte.
* **`H2.Conn`** (the connection state machine) and **`HTTP2Transport`**:
  conformance cases from httpcore's and h2's tests, properties (the same
  response however the bytes are split; bounded buffers on random bytes),
  and the native hostile-server checks and benchmark in `tests/NativeH2.lean`.
  The codecs underneath are proved (`h2_frame_parse_print_ext`,
  `hpack_decode_encode`, `hpack_decode_encode_seq`).
* **`URL.parse` reaches canonical form**: `build` checks `ParseResult.Canonical`
  at run time; that the check never fails on any input is tested on random
  URL-like strings (it is what makes `URL` carry its invariant).

### Deviations from upstream

Each is a row with `status = "deviation"` in `docs/traceability.toml`. Upstream
defects found while porting are recorded as UP-035 to UP-041, UP-056 and UP-057 (see
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
  A head is limited to 100 KiB in all, where h11 counts only what is buffered
  while incomplete; error messages say the same thing in different words
  where h11 includes the offending bytes.
* Numbers past `maxIntDigits` digits: a port is invalid and a cookie
  `Max-Age` drops the cookie, as upstream (`int()` raises); a cookie date
  field that long makes the date invalid (a session cookie), where
  `http.cookiejar` catches the exception and drops every cookie of the
  response. A chunk size of more than 20 hex digits is refused (h11's limit),
  so `chunked_decode_encode` is stated for chunks below 2^80 bytes.
* HTTP/2 is with prior knowledge over TCP (`Client.new (http1 := false)
  (http2 := true)`): no TLS, so no ALPN, and no `Upgrade: h2c`. With both
  `http1` and `http2` the client uses HTTP/1.1, as httpx does without TLS.
* HTTP/2 protocol errors the server causes are `RemoteProtocolError`;
  httpcore raises them as `LocalProtocolError` (UP-056). The messages keep
  h2's wording where there is one, prefixed by the error code.
* The HPACK encoder Huffman-codes every literal, as hpack's default encoder
  does (even where raw is shorter); a table size the peer lowers is applied
  up to 4096. One difference: a never-indexed field that equals a static
  table entry (`authorization`, `proxy-authorization` or `cookie` with an
  empty value) stays a never-indexed literal, where hpack sends the index
  and so drops the marking (RFC 7541 section 7.1.3); this keeps
  `hpack_decode_encode` exact. Received fields are validated as h2 does, but
  an invalid response head resets its stream (an RFC 9113 stream error),
  where h2 ends the connection.
* A request's `te` other than `trailers` is dropped, with the other
  connection-specific fields (`h2_request_fields_clean`); h2 refuses to send
  it (`ProtocolError`, which httpcore raises as `LocalProtocolError`).
* h2 has no limit on PING, SETTINGS or other frames that make no progress,
  nor on the output its acknowledgements queue; ours has (see "Hostile HTTP/2
  peers"). A WINDOW_UPDATE of 0 is refused by the connection, where
  hyperframe refuses it while parsing the frame. A frame of unknown type is
  printed with its length (hyperframe's `ExtensionFrame` built with a body
  prints length 0, UP-057).
* The default `User-Agent` is `lean-httpx/0.1.0`.
* An authentication flow sends at most 32 requests (upstream's generators are
  unbounded; Basic and Digest send at most two).

## Tests

* `tests/Props.lean`: seeded property tests, no dependencies, under a second.
* `tests/Conformance.lean`: cases re-expressed from the upstream suite; each
  names the upstream test (`tests/test_x.py::test_y`).
* `tests/Native.lean`: `HTTPTransport` against a hostile server in the same
  process (`lake exe native`), and the 200 MiB benchmark (`scripts/bench.sh`).
  `lake exe native serve` runs only the server, to run upstream httpx against.
* `tests/NativeH2.lean`: the same for HTTP/2 (`lake exe native2`, `lake exe
  native2 bench`, `lake exe native2 serve`).
* `tests/upstream/h2_golden.py` writes `tests/upstream/h2_golden.txt`, the
  outcomes of h2's codecs (hyperframe, hpack) that the conformance cases
  "h2 golden" compare with; rerun it with
  `upstream-spec/.venv/bin/python -I tests/upstream/h2_golden.py > tests/upstream/h2_golden.txt`.
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
