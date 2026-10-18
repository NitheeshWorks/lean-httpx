import LeanHttpx.RepoImpl.Models
import LeanHttpx.RepoImpl.Base64
import LeanHttpx.RepoImpl.Hash

/-!
# Authentication (`httpx/_auth.py`)

An `Auth` is httpx's `auth_flow` generator, as two functions: `start` gives
the first request to send, `next` answers each response with the next
request (`some`) or accepts it (`none`).

* `BasicAuth u p` sets `Authorization: Basic base64(u:p)`
  (`basic_auth_header` proves the credentials decode back).
* `DigestAuth u p` answers a `401` carrying a `Digest` challenge with the
  RFC 7616 response, and reuses the challenge on later requests, counting
  nonces as upstream does. The digest computation (`digestAuthorization`) is
  pure; the flow keeps its state in an `IO.Ref`.
* `FunctionAuth f` applies `f` to the request.
-/

namespace LeanHttpx

/-- An authentication flow (`httpx.Auth`). -/
structure Auth where
  /-- The first request (`next(auth_flow(request))`). -/
  start : Request → IO Request
  /-- The flow's answer to a response: send this request next, or (`none`)
  accept the response. -/
  next : Request → Response → IO (Option Request) := fun _ _ => pure none

namespace Auth

/-- `httpx.Auth()`: send the request as it is. -/
def none : Auth := { start := pure }

end Auth

/-! ## Basic -/

/-- The `Authorization` value for Basic credentials (`_build_auth_header`). -/
def basicAuthHeader (username password : String) : String :=
  "Basic " ++ Base64.encode (username.toUTF8 ++ ":".toUTF8 ++ password.toUTF8)

/-- Split bytes at the first colon. -/
def splitColon (b : List UInt8) : List UInt8 × List UInt8 :=
  (b.takeWhile (· != 58), (b.dropWhile (· != 58)).drop 1)

/-- Read Basic credentials back from an `Authorization` value: the inverse
of `basicAuthHeader` (what a server does with it). -/
def parseBasicAuth (header : String) : Option (String × String) := do
  let h := header.toList
  if h.take 6 != "Basic ".toList then none
  let bytes ← Base64.decode (String.ofList (h.drop 6))
  let (u, p) := splitColon bytes.data.toList
  let u ← String.fromUTF8? ⟨u.toArray⟩
  let p ← String.fromUTF8? ⟨p.toArray⟩
  pure (u, p)

/-- **`httpx.BasicAuth(username, password)`**. -/
def BasicAuth (username password : String) : Auth where
  start r := pure { r with headers := r.headers.set "Authorization" (basicAuthHeader username password) }

/-- `auth=("user", "pass")`. -/
instance : Coe (String × String) Auth := ⟨fun p => BasicAuth p.1 p.2⟩

/-- **`httpx.FunctionAuth(func)`**, or `auth=func`. -/
def FunctionAuth (f : Request → Request) : Auth where
  start r := pure (f r)

instance : Coe (Request → Request) Auth := ⟨FunctionAuth⟩

/-! ## Digest (RFC 7616) -/

/-- A `Digest` challenge (`_DigestAuthChallenge`). -/
structure DigestChallenge where
  realm : String
  nonce : String
  algorithm : String := "MD5"
  opaqueToken : Option String := none
  qop : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- `urllib.request.parse_http_list`: split at commas outside quoted
strings, keeping quotes and backslash escapes, and strip each item. -/
def parseHttpList (s : String) : List String := Id.run do
  let mut items : List String := []
  let mut cur : String := ""
  let mut quoted := false
  let mut escape := false
  for c in s.toList do
    if escape then
      cur := cur.push c; escape := false
    else if quoted then
      if c == '\\' then escape := true
      else if c == '"' then quoted := false
      cur := cur.push c
    else if c == ',' then
      items := items ++ [cur]; cur := ""
    else
      if c == '"' then quoted := true
      cur := cur.push c
  if !cur.isEmpty then items := items ++ [cur]
  return items.map fun x => x.trimAscii.toString

/-- httpx's `unquote`: strip one pair of surrounding double quotes. -/
def unquoteValue (v : String) : String :=
  if v.length ≥ 2 && v.startsWith "\"" && v.endsWith "\"" then ((v.drop 1).dropEnd 1).toString else v

/-- Parse a `Digest ...` challenge (`_parse_challenge`). -/
def parseDigestChallenge (header : String) : Except HTTPError DigestChallenge := do
  let fields := match header.splitOn " " with
    | _ :: rest => " ".intercalate rest
    | [] => ""
  let dict := (parseHttpList fields).filterMap fun f =>
    match f.trimAscii.toString.splitOn "=" with
    | k :: v :: vs => some (k, unquoteValue ("=".intercalate (v :: vs)))
    | _ => none
  let get (k : String) := (dict.find? (·.1 == k)).map (·.2)
  match get "realm", get "nonce" with
  | some realm, some nonce =>
    pure { realm, nonce, algorithm := (get "algorithm").getD "MD5", opaqueToken := get "opaque", qop := get "qop" }
  | _, _ => throw (.remoteProtocolError "Malformed Digest WWW-Authenticate header")

/-- The hash of an algorithm name, upper case (`_ALGORITHM_TO_HASH_FUNCTION`). -/
def digestHash (algorithm : String) : Option (ByteArray → ByteArray) :=
  match algorithm.toUpper with
  | "MD5" | "MD5-SESS" => some Hash.md5
  | "SHA" | "SHA-SESS" => some Hash.sha1
  | "SHA-256" | "SHA-256-SESS" => some Hash.sha256
  | "SHA-512" | "SHA-512-SESS" => some Hash.sha512
  | _ => none

/-- The qop to answer with (`_resolve_qop`): `auth` if offered. -/
def resolveQop (qop : Option String) : Except HTTPError (Option String) :=
  match qop with
  | none => pure none
  | some q =>
    let qops := (q.splitOn ",").map fun s => s.trimAscii.toString
    if qops.contains "auth" then pure (some "auth")
    else if qops == ["auth-int"] then throw (.remoteProtocolError "Digest auth-int support is not yet implemented")
    else throw (.remoteProtocolError s!"Unexpected qop value \"{q}\" in digest auth")

/-- The nonce count as 8 hex digits. -/
def ncValue (n : Nat) : String :=
  let h := (Nat.toDigits 16 n)
  String.ofList (List.replicate (8 - h.length) '0' ++ h)

/-- **The `Authorization` value for a Digest challenge**
(`_build_auth_header`), given the nonce count and client nonce. -/
def digestAuthorization (username password : String) (ch : DigestChallenge) (method uri : String)
    (nonceCount : Nat) (cnonce : String) : Except HTTPError String := do
  let some hash := digestHash ch.algorithm
    | throw (.remoteProtocolError s!"Unsupported digest algorithm {ch.algorithm}")
  let digest (s : String) : String := Hash.hex (hash s.toUTF8)
  let a1 := username ++ ":" ++ ch.realm ++ ":" ++ password
  let a2 := method ++ ":" ++ uri
  let ha2 := digest a2
  let nc := ncValue nonceCount
  let ha1 := digest a1
  let ha1 := if (asciiLower ch.algorithm).endsWith "-sess" then digest (ha1 ++ ":" ++ ch.nonce ++ ":" ++ cnonce) else ha1
  let qop ← resolveQop ch.qop
  let data := match qop with
    | none => [ha1, ch.nonce, ha2]
    | some q => [ha1, ch.nonce, nc, cnonce, q, ha2]
  let response := digest (":".intercalate data)
  let fields : List (String × String × Bool) :=
    [("username", username, true), ("realm", ch.realm, true), ("nonce", ch.nonce, true),
     ("uri", uri, true), ("response", response, true), ("algorithm", ch.algorithm, false)] ++
    (match ch.opaqueToken with | some o => if o.isEmpty then [] else [("opaque", o, true)] | none => []) ++
    (match qop with
      | some _ => [("qop", "auth", false), ("nc", nc, false), ("cnonce", cnonce, true)]
      | none => [])
  pure ("Digest " ++ ", ".intercalate (fields.map fun (k, v, q) => if q then s!"{k}=\"{v}\"" else s!"{k}={v}"))

/-- The state a `DigestAuth` keeps between requests. -/
structure DigestState where
  lastChallenge : Option DigestChallenge := none
  nonceCount : Nat := 1

/-- A client nonce (`_get_client_nonce`): 16 hex digits of SHA-1 over the
count, the nonce and random bytes. -/
def clientNonce (nonceCount : Nat) (nonce : String) : IO String := do
  let rnd ← IO.getRandomBytes 8
  let h := Hash.hex (Hash.sha1 ((toString nonceCount).toUTF8 ++ nonce.toUTF8 ++ rnd))
  pure (String.ofList (h.toList.take 16))

/-- **`httpx.DigestAuth(username, password)`**. -/
def DigestAuth (username password : String) : IO Auth := do
  let st ← IO.mkRef ({} : DigestState)
  let authorize (r : Request) (ch : DigestChallenge) : IO Request := do
    let s ← st.get
    let cnonce ← clientNonce s.nonceCount ch.nonce
    let h ← IO.ofExcept ((digestAuthorization username password ch r.method r.url.rawPath s.nonceCount cnonce).mapError toString)
    st.set { s with nonceCount := s.nonceCount + 1 }
    pure { r with headers := r.headers.set "Authorization" h }
  pure {
    start := fun r => do
      match (← st.get).lastChallenge with
      | some ch => authorize r ch
      | none => pure r
    next := fun r resp => do
      if resp.statusCode != 401 || !resp.headers.contains "www-authenticate" then return none
      let some header := (resp.headers.getList "www-authenticate").find? fun h =>
          (asciiLower h).startsWith "digest " | return none
      let ch ← IO.ofExcept ((parseDigestChallenge header).mapError toString)
      st.set { lastChallenge := some ch, nonceCount := 1 }
      let r ← authorize r ch
      let jar := resp.cookies
      let r := match jar.cookieHeader r.url 0 with
        | some v => { r with headers := r.headers.set "Cookie" v }
        | none => r
      return some r }

end LeanHttpx
