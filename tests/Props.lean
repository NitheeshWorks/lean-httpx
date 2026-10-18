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

def properties : List Property := [
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
