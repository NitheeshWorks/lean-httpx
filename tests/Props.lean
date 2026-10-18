import LeanHttpx

/-!
# Property tests: fast feedback where there is no proof

Generates values with a seeded generator and checks the properties that are
tested rather than proved (CONTRIBUTING lists them, with the reason), plus
smoke tests of proved theorems on the executable code paths (`ByteArray`
rather than lists).

Run with `lake exe props`, or a different seed with `lake exe props 12345`.
A failure prints the seed and the value, so it reproduces exactly.
-/

open LeanHttpx

/-- xorshift64*: four lines, no dependency, deterministic from the seed. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { s := x })

def Rng.nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if bound == 0 then 0 else v.toNat % bound, r)

/-- A property: a name and a check that, given a generator, either passes or
returns a description of the failing value. -/
structure Property where
  name : String
  check : Rng → Option String × Rng

/-- A random string over an alphabet. -/
def Rng.string (r : Rng) (alphabet : List Char) (maxLen : Nat) : String × Rng := Id.run do
  let (n, r) := r.nat (maxLen + 1)
  let mut r := r
  let mut out := ""
  for _ in [0:n] do
    let (i, r') := r.nat alphabet.length
    r := r'
    out := out.push (alphabet.getD i 'a')
  return (out, r)

def Rng.bytes (r : Rng) (maxLen : Nat) : ByteArray × Rng := Id.run do
  let (n, r) := r.nat (maxLen + 1)
  let mut r := r
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (b, r') := r.nat 256
    r := r'
    out := out.push b.toUInt8
  return (out, r)

/-- A random chunked body, sometimes damaged: chunks of random sizes with
upper- or lower-case hex, optional extensions, optional trailers, then
(sometimes) one byte overwritten, or the end cut off. -/
def Rng.chunked (r : Rng) : ByteArray × Rng := Id.run do
  let (n, r) := r.nat 4
  let mut r := r
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (d, r1) := r.bytes 20
    let (upper, r2) := r1.nat 2
    let (ext, r3) := r2.nat 3
    r := r3
    let d := d.push 13
    let hex := String.ofList (Nat.toDigits 16 d.size)
    let hex := if upper == 1 then hex.toUpper else hex
    out := out ++ s!"{hex}{if ext == 0 then ";a=b" else ""}\r\n".toUTF8 ++ d ++ "\r\n".toUTF8
  let (tr, r4) := r.nat 3
  out := out ++ (if tr == 0 then "0\r\nX-T: v\r\n\r\n" else "0\r\n\r\n").toUTF8
  let (damage, r5) := r4.nat 4
  let (pos, r6) := r5.nat (out.size + 1)
  let (byte, r7) := r6.nat 256
  r := r7
  if damage == 0 && pos < out.size then out := out.set! pos byte.toUInt8
  if damage == 1 then out := out.extract 0 pos
  let (tail, r8) := r.bytes 4
  return (out ++ tail, r8)

/-- Characters URLs are made of, including the awkward ones. -/
def urlChars : List Char :=
  "abcXYZ019:/?#[]@!$&'()*+,;=%-._~ \"<>\\^`{|}é☃\t".toList

def urlParts : List String :=
  ["http://", "https://", "HTTP://", "//", "/", "a:", "user:pw@", "[::1]", "1.2.3.4", ":80", ":8080",
   "?q=1", "#f", "..", ".", "%41", "%zz", "example.com", "x", "/a/../b", ""]

def Rng.urlString (r : Rng) : String × Rng := Id.run do
  let (n, r) := r.nat 6
  let mut r := r
  let mut out := ""
  for _ in [0:n] do
    let (k, r') := r.nat 2
    r := r'
    if k == 0 then
      let (i, r'') := r.nat urlParts.length
      r := r''; out := out ++ urlParts.getD i ""
    else
      let (s, r'') := r.string urlChars 4
      r := r''; out := out ++ s
  return (out, r)

/-! ## HTTP/2 -/

def h2Field (r : Rng) : Hpack.HeaderField × Rng :=
  let (n, r) := r.string "abcxyz-".toList 6
  let (v, r) := r.bytes 12
  let (sens, r) := r.nat 4
  (⟨("x-" ++ n).toUTF8, v, sens == 0⟩, r)

def h2Fields' (r : Rng) (maxN : Nat) : List Hpack.HeaderField × Rng := Id.run do
  let (n, r) := r.nat (maxN + 1)
  let mut r := r
  let mut out := #[]
  for _ in [0:n] do
    let (f, r') := h2Field r
    r := r'
    out := out.push (if n % 3 == 0 && out.size > 0 then out[0]! else f)
  return (out.toList, r)

def frameBytes (fs : List H2.Frame) : ByteArray := fs.foldl (fun b f => b ++ H2.printFrame f) .empty

/-- A server's answer to stream 1: SETTINGS, PING, a response head, DATA in
pieces, the last ending the stream. -/
def serverAnswer (r : Rng) : ByteArray × ByteArray × Rng := Id.run do
  -- field values valid in a response (no control bytes, no surrounding space)
  let (fs, r) := h2Fields' r 3
  let fs := fs.map fun f => { f with value := (Hash.hex f.value).toUTF8 }
  let head := (({} : Hpack.Encoder).encode (⟨":status".toUTF8, "200".toUTF8, false⟩ :: fs)).1
  let (n, r) := r.nat 5
  let mut r := r
  let mut body := ByteArray.empty
  let mut frames : Array H2.Frame := #[.settings false [(H2.settingsMaxConcurrentStreams, 10)], .ping false "abcdefgh".toUTF8,
    .headers 1 head false true none none]
  for i in [0:n + 1] do
    let (d, r') := r.bytes 40
    r := r'
    body := body ++ d
    frames := frames.push (.data 1 d (i == n) none)
  return (frameBytes frames.toList, body, r)

/-- Split bytes at random points. -/
def splitRandom (r : Rng) (b : ByteArray) : List ByteArray × Rng := Id.run do
  let mut r := r
  let mut pos := 0
  let mut out := #[]
  for _ in [0:b.size + 1] do
    if pos ≥ b.size then break
    let (k, r') := r.nat 20
    r := r'
    let e := min b.size (pos + k + 1)
    out := out.push (b.extract pos e)
    pos := e
  return (out.toList, r)

def started1 : H2.Conn :=
  match (H2.Conn.new).startRequest [⟨":method".toUTF8, "GET".toUTF8, false⟩] .empty with
  | .ok (c, _) => c
  | .error _ => H2.Conn.new

def outcomeStr (c : H2.Conn) : String := match c.outcome 1 with
  | none => "pending"
  | some (.error m) => s!"error {m}"
  | some (.ok (st, hs, b)) => s!"{st} {hs.length} {Hash.hex b}"


def properties : List Property := [
  ⟨"HPACK API: chained Synced.encode blocks decode, the sides in step", fun r => Id.run do
    let mut r := r
    let mut s := Hpack.Synced.new
    for _ in [0:4] do
      let (fs, r') := h2Fields' r 6
      r := r'
      match s.encode fs with
      | none => return (some "refused", r)
      | some ⟨(b, s'), _⟩ =>
        match s.dec.decode b with
        | .ok (fs', d) => if fs' != fs || d.table.entries != s'.enc.table.entries then return (some "mismatch", r)
        | .error e => return (some e.message, r)
        s := s'
    return (none, r)⟩,
  ⟨"Frame API: encodeFrame bytes parse back, refused past the maximum size", fun r =>
    let (d, r) := r.bytes 64
    let (sid, r) := r.nat 5
    let f := H2.Frame.data (sid + 1) d true none
    let ok := match H2.encodeFrame 32 f with
      | some ⟨b, _⟩ => d.size ≤ 32 && match H2.parseFrame 32 b with | .done _ rest => rest.size == 0 | _ => false
      | none => d.size > 32
    (if ok then none else some s!"{d.size}", r)⟩,
  ⟨"Huffman: decode (encode b) = b", fun r =>
    let (b, r) := r.bytes 64
    (if Huffman.decode (Huffman.encode b) == some b then none else some s!"{b.toList}", r)⟩,
  ⟨"Huffman: an encoding's padding is under a byte of ones", fun r =>
    let (b, r) := r.bytes 32
    let e := Huffman.encode b
    let bits := (b.toList.map fun x => Huffman.codeLengths[x.toNat]!).sum
    (if e.size == (bits + 7) / 8 then none else some s!"{b.toList}", r)⟩,
  ⟨"HPACK: a sequence of blocks decodes on the executable path, any table size", fun r => Id.run do
    let (sz, r) := r.nat 300
    let mut r := r
    let mut e : Hpack.Encoder := ({} : Hpack.Encoder).setMaxSize sz
    let mut d : Hpack.Decoder := {}
    for _ in [0:4] do
      let (fs, r') := h2Fields' r 6
      r := r'
      let (b, e') := e.encode fs
      e := e'
      match d.decode b with
      | .ok (fs', d') =>
        if fs' != fs then return (some s!"size {sz}: {fs.length} fields", r)
        d := d'
      | .error err => return (some s!"size {sz}: {err.message}", r)
    return (none, r)⟩,
  ⟨"HPACK: random bytes are refused or decoded, the table within its limit", fun r =>
    let (b, r) := r.bytes 40
    let d : Hpack.Decoder := { table := { maxSize := 256 }, maxTableSize := 256, maxHeaderListSize := 512 }
    match d.decode b with
    | .ok (fs, d') =>
      (if d'.table.size ≤ d'.table.maxSize && d'.table.maxSize ≤ 256 && (fs.map Hpack.fieldSize).sum ≤ 512 then none
       else some s!"{b.toList}", r)
    | .error _ => (none, r)⟩,
  ⟨"HTTP/2: a response is the same however the bytes arrive", fun r =>
    let (wire, body, r) := serverAnswer r
    let (pieces, r) := splitRandom r wire
    let whole := started1.receive wire
    let split := pieces.foldl (fun c p => c.receive p) started1
    let ok := outcomeStr whole == outcomeStr split && (outcomeStr whole).endsWith (Hash.hex body)
      && (outcomeStr whole).startsWith "200"
    (if ok then none else some s!"{outcomeStr whole} vs {outcomeStr split}", r)⟩,
  ⟨"HTTP/2: on random bytes the buffers stay bounded", fun r =>
    let (b, r) := r.bytes 200
    let (pieces, r) := splitRandom r b
    let c := pieces.foldl (fun c p => c.receive p) started1
    let ok := c.inbuf.size ≤ 9 + c.limits.maxFrameSize && c.out.size ≤ c.limits.maxPendingOutput + 9 + 16384
      && c.streams.length ≤ 1
    (if ok then none else some s!"{b.toList}", r)⟩,
  ⟨"HTTP/2: request fields are pseudo-headers then lower-case fields, credentials never indexed", fun r =>
    let (k, r) := r.string "aAbB-".toList 5
    let (v, r) := r.string "xy".toList 4
    let hs : List (String × String) := [("Host", "example.org"), ("Authorization", "Basic x"), ("X-" ++ k, v),
      ("Transfer-Encoding", "chunked")]
    match URL.parse "http://example.com/p?q=1" >>= fun u => Request.new "GET" u (headers := hs) with
    | .error _ => (some "request", r)
    | .ok req =>
      let fs := h2Fields req
      let names := fs.map fun f => String.fromUTF8! f.name
      let ok := names.take 4 == [":method", ":authority", ":scheme", ":path"]
        && (fs.getD 1 default).value == "example.org".toUTF8
        && (fs.drop 4).all (fun f => (String.fromUTF8! f.name) == asciiLower (String.fromUTF8! f.name))
        && !names.contains "host" && !names.contains "transfer-encoding"
        && fs.all (fun f => f.sensitive == (f.name == "authorization".toUTF8))
      (if ok then none else some s!"{names}", r)⟩,
  ⟨"URL.parse never reaches its internal canonical-form check", fun r =>
    let (s, r) := r.urlString
    match URL.parse s with
    | .error e => (if e.message.startsWith "Internal" then some s!"{repr s}: {e.message}" else none, r)
    | .ok _ => (none, r)⟩,
  ⟨"URL.parse (toString (URL.parse s)) is URL.parse s (theorem url_parse_print_ext, on text)", fun r =>
    let (s, r) := r.urlString
    match URL.parse s with
    | .ok u => match URL.parse u.toString with
      | .ok v => (if u == v then none else some s!"{repr s} -> {u} -> {v}", r)
      | .error e => (some s!"{repr s} -> {u} -> error {e.message}", r)
    | .error _ => (none, r)⟩,
  ⟨"join gives a URL that parses back", fun r =>
    let (s, r) := r.urlString
    match (URL.parse "http://a/b/c/d;p?q").toOption.bind (fun u => (u.join s).toOption) with
    | some v => (if (URL.parse v.toString).toOption.map (· == v) == some true then none else some s!"{repr s}", r)
    | none => (none, r)⟩,
  ⟨"QueryParams.parse (toString q) has the same items", fun r =>
    let (n, r) := r.nat 4
    let (pairs, r) := (List.range n).foldl (fun (acc : List (String × String) × Rng) _ =>
      let (k, r) := acc.2.string "ab =&+%é".toList 3
      let (v, r) := r.string "ab =&+%é#".toList 3
      (acc.1 ++ [(if k.isEmpty then "k" else k, v)], r)) ([], r)
    let q := QueryParams.ofList pairs
    (if (QueryParams.parse (toString q)).equiv q then none else some s!"{pairs} -> {q}", r)⟩,
  ⟨"Text.unquote inverts percent-encoding of UTF-8 text", fun r =>
    let (s, r) := r.string "ab /%é☃?#".toList 8
    let q := String.ofList (Chars.quote (fun c => Chars.isUnreserved c) s.toList)
    (if Text.unquote q == s then none else some s!"{repr s} -> {repr q} -> {repr (Text.unquote q)}", r)⟩,
  ⟨"utf8DecodeReplace agrees with String.fromUTF8? on valid UTF-8", fun r =>
    let (s, r) := r.string "aé☃🌟z".toList 8
    (if Text.utf8DecodeReplace s.toUTF8 == s then none else some s, r)⟩,
  ⟨"utf8DecodeReplace is total on random bytes", fun r =>
    let (b, r) := r.bytes 16
    let _ := Text.utf8DecodeReplace b
    (none, r)⟩,
  ⟨"Base64.decode (encode b) = b on ByteArray (theorem decode_encode)", fun r =>
    let (b, r) := r.bytes 40
    (if Base64.decode (Base64.encode b) == some b then none else some s!"{b.toList}", r)⟩,
  ⟨"chunked coding round trip on ByteArray (theorem chunked_decode_encode)", fun r =>
    let (n, r) := r.nat 4
    let (cs, r) := (List.range n).foldl (fun (acc : List ByteArray × Rng) _ =>
      let (b, r) := acc.2.bytes 20
      (acc.1 ++ [b.push 1], r)) ([], r)
    let (tail, r) := r.bytes 5
    match H1.decodeChunked (H1.encodeChunked cs ++ tail) with
    | some (cs', rest) => (if cs' == cs && rest == tail then none else some s!"{cs.map (·.toList)}", r)
    | none => (some s!"none for {cs.map (·.toList)}", r)⟩,
  ⟨"a chunked body split at random chunk boundaries decodes to the same bytes", fun r =>
    let (body, r) := r.bytes 60
    let (k, r) := r.nat 5
    let size := body.size / (k + 1) + 1
    let cs := (List.range (body.size / size + 1)).filterMap fun i =>
      let c := body.extract (i * size) ((i + 1) * size)
      if c.isEmpty then none else some c
    match H1.decodeChunked (H1.encodeChunked cs) with
    | some (cs', _) => (if H1.concatChunks cs' == body then none else some s!"{body.toList}", r)
    | none => (some "none", r)⟩,
  ⟨"H1.readChunked (slices) agrees with the chunked codec on damaged and intact bodies", fun r =>
    let (b, r) := r.chunked
    let fast := H1.readChunked b 0
    let slow := (H1.chunkedBody.decodeBytes b).map fun (d, rest) => (d, b.size - rest.size)
    (if fast == slow then none else s!"{b.toList}: {fast.map (·.2)} vs {slow.map (·.2)}", r)⟩,
  ⟨"H1.scanChunks stops where the chunked codec ends, and never early", fun r =>
    let (b, r) := r.chunked
    match H1.readChunked b 0, H1.scanChunks b 0 with
    | some (_, k), .done k' => (if k == k' then none else some s!"{b.toList}: {k} vs {k'}", r)
    | some _, s => (some s!"{b.toList}: codec ends, scan says {repr s}", r)
    | none, .done k =>
      -- the scan only finds the end; a damaged body is then refused by the codec
      (if (H1.readChunked (b.extract 0 k) 0).isNone then none else some s!"{b.toList}: scan {k}", r)
    | none, _ => (none, r)⟩,
  ⟨"an httpx error raised in IO reads back as the same class and message", fun r =>
    let (m, r) := r.string "ab: :x".toList 8
    let es := [HTTPError.readTimeout m, .remoteProtocolError m, .connectError m, .writeError m,
      .localProtocolError m, .unsupportedProtocol m, .decodingError m, .readError m]
    let bad := es.filter fun e => (HTTPError.ofString? (toString e)).map toString != some (toString e)
    (if bad.isEmpty then none else some s!"{bad.map toString}", r)⟩,
  ⟨"response round trip on ByteArray (theorem h1_response_parse_print_ext)", fun r =>
    let (body, r) := r.bytes 30
    let (code, r) := r.nat 500
    let status := 200 + code % 300
    let head : H1.ResponseHead := H1.ResponseHead.mk .http11 status (H1.ascii "OK")
      [⟨H1.ascii "Content-Length", H1.ascii (toString body.size)⟩]
    let resp : H1.Response := ⟨head, body⟩
    if !(resp.ok (H1.ascii "GET")) then (none, r) else
    match H1.parseResponse (H1.ascii "GET") (H1.printResponse (H1.ascii "GET") resp) with
    | some (resp', rest) => (if resp'.head == resp.head && resp'.body == body && rest.isEmpty then none
        else some s!"status {status}", r)
    | none => (some s!"none for status {status}", r)⟩,
  ⟨"H1.parseResponse is total on random bytes", fun r =>
    let (b, r) := r.bytes 60
    let _ := H1.parseResponse (H1.ascii "GET") (("HTTP/1.1 200 OK\r\n".toUTF8) ++ b)
    (none, r)⟩,
  ⟨"inflate is total on random bytes", fun r =>
    let (b, r) := r.bytes 40
    let _ := Decoders.decodeContent ["gzip"] b
    let _ := Decoders.decodeContent ["deflate"] b
    (none, r)⟩,
  ⟨"a cookie jar holds one cookie per key after any sequence of sets", fun r =>
    let (n, r) := r.nat 8
    let (jar, r) := (List.range n).foldl (fun (acc : Cookies × Rng) _ =>
      let (nm, r) := acc.2.string "ab".toList 1
      let (d, r) := r.string "xy".toList 1
      let (p, r) := r.string "/q".toList 2
      (acc.1.set nm "v" d p, r)) ({}, r)
    let keys := jar.toList.map (·.key)
    (if keys.eraseDups.length == keys.length then none else some s!"{keys}", r)⟩,
  ⟨"Cookie header carries only path-matching cookies", fun r =>
    let (p, r) := r.string "/ab".toList 4
    let u := (URL.parse "http://example.org/a/b").toOption.get!
    let j := ({} : Cookies).extract [s!"c=1; Path={if p.isEmpty then "/" else p}"] u 0 2026
    let carried := (j.cookieHeader u 0).isSome
    let expect := CookieJar.pathReturnOk (j.toList.head?.map (·.path) |>.getD "/") "/a/b"
    (if carried == expect then none else some s!"path {p}", r)⟩
]

def main (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 88172645463325252
  let cases := 200
  let mut rng : Rng := { s := UInt64.ofNat seed }
  let mut failures := 0
  for p in properties do
    let mut failed : Option String := none
    for _ in [0:cases] do
      if failed.isSome then break
      let (res, rng') := p.check rng
      rng := rng'
      failed := res
    match failed with
    | none => IO.println s!"ok    {p.name} ({cases} cases)"
    | some why =>
      failures := failures + 1
      IO.println s!"FAIL  {p.name}: {why}  (seed {seed})"
  IO.println s!"{properties.length} properties, {failures} failing (seed {seed})"
  return if failures == 0 then 0 else 1
