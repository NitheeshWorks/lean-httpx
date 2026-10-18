import LeanHttpx

/-!
# Conformance cases

Each case re-expresses one upstream test (httpx `tests/`, httpcore `tests/`)
in Lean and names it, so `docs/traceability.toml` can point at both. The
upstream suite is the behavioural specification; no upstream code is copied.
Cases whose upstream expectation this port deliberately does not meet are
not here; they are deviations in CONTRIBUTING.

Run with `lake exe conformance`.
-/

open LeanHttpx LeanJson

structure Case where
  /-- Upstream test this mirrors, e.g. `tests/test_path.py::test_int`. -/
  upstream : String
  name : String
  run : IO Bool

/-! ## Helpers -/

/-- Compare and report. -/
def eqv {α : Type} [BEq α] [ToString α] (what : String) (actual expected : α) : IO Bool := do
  if actual == expected then pure true
  else IO.println s!"      {what}: got {actual}, expected {expected}"; pure false

def allOk (xs : List (IO Bool)) : IO Bool := xs.foldlM (fun acc x => do pure (acc && (← x))) true

def url! (s : String) : IO URL := match URL.parse s with
  | .ok u => pure u
  | .error e => throw (IO.userError s!"InvalidURL {e.message}")

def urlErr (s : String) : IO String := match URL.parse s with
  | .ok u => pure s!"ok {u}"
  | .error e => pure e.message

def except! {α : Type} (x : Except InvalidURL α) : IO α := match x with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"InvalidURL {e.message}")

def str (b : ByteArray) : String := String.fromUTF8! b

def join (base ref : String) : IO String := do
  let u ← url! base
  pure (toString (← except! (u.join ref)))

/-- A client over a mock handler. -/
def mockClient (handler : Request → Response) (followRedirects := false) (baseUrl := "") :
    IO Client := Client.new (transport := MockTransport handler) (followRedirects := followRedirects)
      (baseUrl := baseUrl)

/-- Run an IO action that should fail, returning its message. -/
def failure {α : Type} (x : IO α) : IO String := do
  try let _ ← x; pure "no error" catch e => pure (toString e)

/-! ## URLs (`tests/models/test_url.py`) -/

def urlCases : List Case := [
  ⟨"tests/models/test_url.py::test_basic_url", "basic url", do
    let u ← url! "https://www.example.com/"
    allOk [eqv "scheme" u.scheme "https", eqv "userinfo" u.userinfo "", eqv "netloc" u.netloc "www.example.com",
      eqv "host" u.host "www.example.com", eqv "port" u.port none, eqv "path" u.path "/",
      eqv "query" u.query "", eqv "fragment" u.fragment "", eqv "str" (toString u) "https://www.example.com/",
      eqv "repr" (reprStr u) "URL('https://www.example.com/')"]⟩,
  ⟨"tests/models/test_url.py::test_complete_url", "complete url", do
    let u ← url! "https://example.org:123/path/to/somewhere?abc=123#anchor"
    allOk [eqv "scheme" u.scheme "https", eqv "host" u.host "example.org", eqv "port" u.port (some 123),
      eqv "path" u.path "/path/to/somewhere", eqv "query" u.query "abc=123",
      eqv "raw_path" u.rawPath "/path/to/somewhere?abc=123", eqv "fragment" u.fragment "anchor",
      eqv "str" (toString u) "https://example.org:123/path/to/somewhere?abc=123#anchor"]⟩,
  ⟨"tests/models/test_url.py::test_url_with_empty_query", "empty query", do
    let u ← url! "https://www.example.com/path"
    let v ← url! "https://www.example.com/path?"
    allOk [eqv "path" u.path "/path", eqv "query" u.query "", eqv "raw" u.rawPath "/path",
      eqv "path2" v.path "/path", eqv "query2" v.query "", eqv "raw2" v.rawPath "/path?"]⟩,
  ⟨"tests/models/test_url.py::test_url_no_scheme", "no scheme", do
    let u ← url! "://example.com"
    allOk [eqv "scheme" u.scheme "", eqv "host" u.host "example.com", eqv "path" u.path "/"]⟩,
  ⟨"tests/models/test_url.py::test_url_no_authority", "no authority", do
    let u ← url! "http://"
    allOk [eqv "scheme" u.scheme "http", eqv "host" u.host "", eqv "path" u.path "/"]⟩,
  ⟨"tests/models/test_url.py::test_path_query_fragment", "unescaped chars in path", do
    let u ← url! "https://example.com/!$&'()*+,;= abc ABC 123 :/[]@"
    allOk [eqv "raw" u.rawPath "/!$&'()*+,;=%20abc%20ABC%20123%20:/[]@",
      eqv "path" u.path "/!$&'()*+,;= abc ABC 123 :/[]@"]⟩,
  ⟨"tests/models/test_url.py::test_path_query_fragment", "escaped chars in path", do
    let u ← url! "https://example.com/!$&'()*+,;=%20abc%20ABC%20123%20:/[]@"
    allOk [eqv "raw" u.rawPath "/!$&'()*+,;=%20abc%20ABC%20123%20:/[]@",
      eqv "path" u.path "/!$&'()*+,;= abc ABC 123 :/[]@"]⟩,
  ⟨"tests/models/test_url.py::test_path_query_fragment", "mixed escapes in path", do
    let u ← url! "https://example.com/ %61%62%63"
    allOk [eqv "raw" u.rawPath "/%20%61%62%63", eqv "path" u.path "/ abc"]⟩,
  ⟨"tests/models/test_url.py::test_path_query_fragment", "unescaped chars in query", do
    let u ← url! "https://example.com/?!$&'()*+,;= abc ABC 123 :/[]@?"
    allOk [eqv "raw" u.rawPath "/?!$&'()*+,;=%20abc%20ABC%20123%20:/[]@?",
      eqv "query" u.query "!$&'()*+,;=%20abc%20ABC%20123%20:/[]@?"]⟩,
  ⟨"tests/models/test_url.py::test_path_query_fragment", "escaped chars in query", do
    let u ← url! "https://example.com/?!$&%27()*+,;=%20abc%20ABC%20123%20:%2F[]@?"
    allOk [eqv "query" u.query "!$&%27()*+,;=%20abc%20ABC%20123%20:%2F[]@?"]⟩,
  ⟨"tests/models/test_url.py::test_path_query_fragment", "mixed escapes in query", do
    let u ← url! "https://example.com/?%20%97%98%99"
    allOk [eqv "raw" u.rawPath "/?%20%97%98%99", eqv "query" u.query "%20%97%98%99"]⟩,
  ⟨"tests/models/test_url.py::test_path_query_fragment", "chars in fragment", do
    let u ← url! "https://example.com/#!$&'()*+,;= abc ABC 123 :/[]@?#"
    allOk [eqv "raw" u.rawPath "/", eqv "fragment" u.fragment "!$&'()*+,;= abc ABC 123 :/[]@?#"]⟩,
  ⟨"tests/models/test_url.py::test_url_query_encoding", "query encoding", do
    let u ← url! "https://www.example.com/?a=b c&d=e/f"
    let v ← except! ((← url! "https://www.example.com/").copyWith (params := some [("a", "b c"), ("d", "e/f")]))
    allOk [eqv "raw" u.rawPath "/?a=b%20c&d=e/f", eqv "params" v.rawPath "/?a=b+c&d=e%2Ff"]⟩,
  ⟨"tests/models/test_url.py::test_url_params", "url params", do
    let v ← except! ((← url! "https://example.org:123/path/to/somewhere").copyWith (params := some [("a", "123")]))
    allOk [eqv "str" (toString v) "https://example.org:123/path/to/somewhere?a=123",
      eqv "params" (v.params.equiv [("a", "123")]) true]⟩,
  ⟨"tests/models/test_url.py::test_url_username_and_password", "username and password", do
    let u ← url! "https://username:password@example.com"
    let v ← url! "https://username%40gmail.com:pa%20ssword@example.com"
    let w ← url! "https://username@gmail.com:pa ssword@example.com"
    let x ← url! "https://user name:p@ssword@example.com"
    allOk [eqv "ui" u.userinfo "username:password", eqv "user" u.username "username",
      eqv "pw" u.password "password", eqv "ui2" v.userinfo "username%40gmail.com:pa%20ssword",
      eqv "user2" v.username "username@gmail.com", eqv "pw2" v.password "pa ssword",
      eqv "ui3" w.userinfo "username%40gmail.com:pa%20ssword", eqv "ui4" x.userinfo "user%20name:p%40ssword",
      eqv "user4" x.username "user name", eqv "pw4" x.password "p@ssword"]⟩,
  ⟨"tests/models/test_url.py::test_url_normalized_host", "normalized host", do
    allOk [eqv "host" (← url! "https://EXAMPLE.com/").host "example.com"]⟩,
  ⟨"tests/models/test_url.py::test_url_percent_escape_host", "percent escape host", do
    allOk [eqv "host" (← url! "https://exam le.com/").host "exam%20le.com"]⟩,
  ⟨"tests/models/test_url.py::test_url_ipv4_like_host", "ipv4-like host", do
    allOk [eqv "host" (← url! "https://023b76x43144/").host "023b76x43144"]⟩,
  ⟨"tests/models/test_url.py::test_url_valid_port", "valid port", do
    allOk [eqv "port" (← url! "https://example.com:123/").port (some 123)]⟩,
  ⟨"tests/models/test_url.py::test_url_normalized_port", "normalized port", do
    allOk [eqv "port" (← url! "https://example.com:443/").port none]⟩,
  ⟨"tests/models/test_url.py::test_url_invalid_port", "invalid port", do
    allOk [eqv "err" (← urlErr "https://example.com:abc/") "Invalid port: 'abc'"]⟩,
  ⟨"httpx/_urlparse.py::normalize_port (int() refuses more than 4300 digits)", "port with 4301 digits", do
    let digits := String.ofList (List.replicate 4301 '1')
    allOk [eqv "err" (← urlErr s!"https://example.com:{digits}/") s!"Invalid port: '{digits}'",
      eqv "4300 digits parse" ((URL.parse s!"https://example.com:{String.ofList (List.replicate 4300 '1')}/").toOption.isSome) true]⟩,
  ⟨"http/cookiejar.py::_normalized_cookie_tuples (int(max-age) refuses more than 4300 digits)", "cookie max-age with 5000 digits", do
    let c ← mockClient fun _ => Response.new 200
      (headers := [("set-cookie", s!"a=b; Max-Age={String.ofList (List.replicate 5000 '1')}"), ("set-cookie", "c=d; Max-Age=60")])
    let _ ← c.get "http://example.org/"
    let j ← c.cookies
    allOk [eqv "dropped" ((j.get? "a").toOption.join).isNone true, eqv "kept" ((j.get? "c").toOption.join) (some "d")]⟩,
  ⟨"tests/models/test_url.py::test_url_normalized_path", "normalized path", do
    allOk [eqv "path" (← url! "https://example.com/abc/def/../ghi/./jkl").path "/abc/ghi/jkl"]⟩,
  ⟨"tests/models/test_url.py::test_url_escaped_path", "escaped path", do
    allOk [eqv "raw" (← url! "https://example.com/ /🌟/").rawPath "/%20/%F0%9F%8C%9F/"]⟩,
  ⟨"tests/models/test_url.py::test_url_leading_dot_prefix_on_absolute_url", "leading dot absolute", do
    allOk [eqv "path" (← url! "https://example.com/../abc").path "/abc"]⟩,
  ⟨"tests/models/test_url.py::test_url_leading_dot_prefix_on_relative_url", "leading dot relative", do
    allOk [eqv "path" (← url! "../abc").path "../abc"]⟩,
  ⟨"tests/models/test_url.py::test_param_with_space", "param with space", do
    let v ← except! ((← url! "http://webservice").copyWith (params := some [("u", "with spaces")]))
    eqv "str" (toString v) "http://webservice?u=with+spaces"⟩,
  ⟨"tests/models/test_url.py::test_param_requires_encoding", "param requires encoding", do
    let v ← except! ((← url! "http://webservice").copyWith (params := some [("u", "%")]))
    eqv "str" (toString v) "http://webservice?u=%25"⟩,
  ⟨"tests/models/test_url.py::test_param_with_percent_encoded", "param with percent-encoded", do
    let v ← except! ((← url! "http://webservice").copyWith (params := some [("u", "with%20spaces")]))
    eqv "str" (toString v) "http://webservice?u=with%2520spaces"⟩,
  ⟨"tests/models/test_url.py::test_param_with_existing_escape_requires_encoding", "param escape", do
    let v ← except! ((← url! "http://webservice").copyWith (params := some [("u", "http://example.com?q=foo%2Fa")]))
    eqv "str" (toString v) "http://webservice?u=http%3A%2F%2Fexample.com%3Fq%3Dfoo%252Fa"⟩,
  ⟨"tests/models/test_url.py::test_query_with_existing_percent_encoding", "query existing escapes", do
    eqv "str" (toString (← url! "http://webservice?u=phrase%20with%20spaces")) "http://webservice?u=phrase%20with%20spaces"⟩,
  ⟨"tests/models/test_url.py::test_query_requiring_percent_encoding", "query requires escapes", do
    eqv "str" (toString (← url! "http://webservice?u=phrase with spaces")) "http://webservice?u=phrase%20with%20spaces"⟩,
  ⟨"tests/models/test_url.py::test_query_with_mixed_percent_encoding", "query mixed escapes", do
    eqv "str" (toString (← url! "http://webservice?u=phrase%20with spaces")) "http://webservice?u=phrase%20with%20spaces"⟩,
  ⟨"tests/models/test_url.py::test_url_invalid_hostname", "invalid hostname", do
    eqv "err" ((← urlErr "https://😇/").startsWith "Invalid IDNA hostname") true⟩,
  ⟨"tests/models/test_url.py::test_url_excessively_long_url", "url too long", do
    eqv "err" (← urlErr ("https://www.example.com/" ++ String.ofList (List.replicate 100000 'x'))) "URL too long"⟩,
  ⟨"tests/models/test_url.py::test_url_excessively_long_component", "component too long", do
    let r := (← url! "https://www.example.com").copyWith (path := "/" ++ String.ofList (List.replicate 100000 'x'))
    eqv "err" (match r with | .ok _ => "ok" | .error e => e.message) "URL component 'path' too long"⟩,
  ⟨"tests/models/test_url.py::test_url_non_printing_character_in_url", "non-printing in url", do
    eqv "err" (← urlErr "https://www.example.com/\n") "Invalid non-printable ASCII character in URL, '\\n' at position 24."⟩,
  ⟨"tests/models/test_url.py::test_url_non_printing_character_in_component", "non-printing in component", do
    let r := (← url! "https://www.example.com").copyWith (path := "/\n")
    eqv "err" (match r with | .ok _ => "ok" | .error e => e.message)
      "Invalid non-printable ASCII character in URL path component, '\\n' at position 1."⟩,
  ⟨"tests/models/test_url.py::test_url_with_components", "url from components", do
    let u ← except! (URL.ofComponents (scheme := "https") (host := "www.example.com") (path := "/"))
    eqv "str" (toString u) "https://www.example.com/"⟩,
  ⟨"tests/models/test_url.py::test_urlparse_with_invalid_scheme", "invalid scheme component", do
    let r := URL.ofComponents (scheme := "~ttp") (host := "www.example.com") (path := "/")
    eqv "err" (match r with | .ok _ => "ok" | .error e => e.message) "Invalid URL component 'scheme'"⟩,
  ⟨"tests/models/test_url.py::test_urlparse_with_invalid_path", "invalid path components", do
    let e (r : Except InvalidURL URL) : String := match r with | .ok _ => "ok" | .error e => e.message
    allOk [eqv "abs" (e (URL.ofComponents (scheme := "https") (host := "www.example.com") (path := "abc")))
        "For absolute URLs, path must be empty or begin with '/'",
      eqv "slashes" (e (URL.ofComponents (path := "//abc"))) "Relative URLs cannot have a path starting with '//'",
      eqv "colon" (e (URL.ofComponents (path := ":abc"))) "Relative URLs cannot have a path starting with ':'"]⟩,
  ⟨"tests/models/test_url.py::test_url_with_relative_path", "relative path", do
    eqv "path" (← except! (URL.ofComponents (path := "abc"))).path "abc"⟩,
  ⟨"tests/models/test_url.py::test_url_join", "join", do
    let b := "https://example.org:123/path/to/somewhere"
    allOk [eqv "1" (← join b "/somewhere-else") "https://example.org:123/somewhere-else",
      eqv "2" (← join b "somewhere-else") "https://example.org:123/path/to/somewhere-else",
      eqv "3" (← join b "../somewhere-else") "https://example.org:123/path/somewhere-else",
      eqv "4" (← join b "../../somewhere-else") "https://example.org:123/somewhere-else"]⟩,
  ⟨"tests/models/test_url.py::test_relative_url_join", "relative join", do
    let b := "/path/to/somewhere"
    allOk [eqv "1" (← join b "/somewhere-else") "/somewhere-else",
      eqv "2" (← join b "somewhere-else") "/path/to/somewhere-else",
      eqv "3" (← join b "../somewhere-else") "/path/somewhere-else",
      eqv "4" (← join b "../../somewhere-else") "/somewhere-else"]⟩,
  ⟨"tests/models/test_url.py::test_url_join_rfc3986", "join rfc3986", do
    let b := "http://example.com/b/c/d;p?q"
    let cases := rfc3986Examples.drop 1 |>.filter (·.1 != "http:g") |>.map fun (r, t) =>
      (r, (t.replace "http://a/" "http://example.com/"))
    allOk (cases.map fun (r, t) => do eqv r (← join b r) t)⟩,
  ⟨"tests/models/test_url.py::test_resolution_error_1833", "join resolution #1833", do
    eqv "join" (← join "https://example.com/?[]" "/") "https://example.com/"⟩,
  ⟨"tests/models/test_url.py::test_copy_with", "copy_with", do
    let u ← url! "https://www.example.com/"
    let u ← except! (u.copyWith (scheme := "http"))
    let s1 := toString u
    let u ← except! (u.copyWith (netloc := some "example.com"))
    let s2 := toString u
    let u ← except! (u.copyWith (path := "/abc"))
    allOk [eqv "1" s1 "http://www.example.com/", eqv "2" s2 "http://example.com/",
      eqv "3" (toString u) "http://example.com/abc"]⟩,
  ⟨"tests/models/test_url.py::test_url_copywith_authority_subcomponents", "copy_with authority", do
    let u ← except! ((← url! "https://example.org").copyWith (username := some "username")
      (password := some "password") (port := some 444) (host := "example.net"))
    eqv "str" (toString u) "https://username:password@example.net:444"⟩,
  ⟨"tests/models/test_url.py::test_url_copywith_netloc", "copy_with netloc", do
    let u ← except! ((← url! "https://example.org").copyWith (netloc := some "example.net:444"))
    eqv "str" (toString u) "https://example.net:444"⟩,
  ⟨"tests/models/test_url.py::test_url_copywith_userinfo_subcomponents", "copy_with userinfo", do
    let u ← except! ((← url! "https://example.org").copyWith (username := some "tom@example.org")
      (password := some "abc123@ %"))
    allOk [eqv "str" (toString u) "https://tom%40example.org:abc123%40%20%@example.org",
      eqv "user" u.username "tom@example.org", eqv "pw" u.password "abc123@ %",
      eqv "ui" u.userinfo "tom%40example.org:abc123%40%20%"]⟩,
  ⟨"tests/models/test_url.py::test_url_copywith_urlencoded_path", "copy_with encoded path", do
    let u ← except! ((← url! "https://example.org").copyWith (path := "/path to somewhere"))
    allOk [eqv "path" u.path "/path to somewhere", eqv "query" u.query "", eqv "raw" u.rawPath "/path%20to%20somewhere"]⟩,
  ⟨"tests/models/test_url.py::test_url_copywith_query", "copy_with query", do
    let u ← except! ((← url! "https://example.org").copyWith (query := some "a=123"))
    allOk [eqv "path" u.path "/", eqv "query" u.query "a=123", eqv "raw" u.rawPath "/?a=123"]⟩,
  ⟨"tests/models/test_url.py::test_url_copywith_raw_path", "copy_with raw_path", do
    let a ← except! ((← url! "https://example.org").copyWith (rawPath := some "/some/path"))
    let b ← except! ((← url! "https://example.org").copyWith (rawPath := some "/some/path?"))
    let c ← except! ((← url! "https://example.org").copyWith (rawPath := some "/some/path?a=123"))
    allOk [eqv "a" a.rawPath "/some/path", eqv "b" b.rawPath "/some/path?", eqv "bq" b.query "",
      eqv "c" c.rawPath "/some/path?a=123", eqv "cq" c.query "a=123"]⟩,
  ⟨"tests/models/test_url.py::test_url_copywith_security", "copy_with security", do
    let bad := (← url! "https://example.com/path?t=w#tw").copyWith (scheme := "https://xxxx:xxxx@xxxxxxx/xxxxx/xxx?x=x#xxxxx")
    allOk [eqv "invalid host" ((← urlErr "https://u:p@[invalid!]//evilHost/path?t=w#tw").startsWith "Invalid IPv6") true,
      eqv "bad scheme" (match bad with | .ok _ => false | .error _ => true) true]⟩,
  ⟨"tests/models/test_url.py::test_url_set_param_manipulation", "copy_set_param", do
    eqv "s" (toString (← except! ((← url! "https://example.org:123/?a=123").copySetParam "a" "456")))
      "https://example.org:123/?a=456"⟩,
  ⟨"tests/models/test_url.py::test_url_add_param_manipulation", "copy_add_param", do
    eqv "s" (toString (← except! ((← url! "https://example.org:123/?a=123").copyAddParam "a" "456")))
      "https://example.org:123/?a=123&a=456"⟩,
  ⟨"tests/models/test_url.py::test_url_remove_param_manipulation", "copy_remove_param", do
    eqv "s" (toString (← except! ((← url! "https://example.org:123/?a=123").copyRemoveParam "a")))
      "https://example.org:123/"⟩,
  ⟨"tests/models/test_url.py::test_url_merge_params_manipulation", "copy_merge_params", do
    eqv "s" (toString (← except! ((← url! "https://example.org:123/?a=123").copyMergeParams [("b", "456")])))
      "https://example.org:123/?a=123&b=456"⟩,
  ⟨"tests/models/test_url.py::test_url_eq_str", "url equality", do
    let u ← url! "https://example.org:123/path/to/somewhere?abc=123#anchor"
    let v ← url! (toString u)
    eqv "eq" (u == v) true⟩,
  ⟨"tests/models/test_url.py::test_ipv6_url", "ipv6 url", do
    let u ← url! "http://[::ffff:192.168.0.1]:5678/"
    allOk [eqv "host" u.host "::ffff:192.168.0.1", eqv "netloc" u.netloc "[::ffff:192.168.0.1]:5678"]⟩,
  ⟨"tests/models/test_url.py::test_url_invalid_ipv4", "invalid ipv4", do
    eqv "err" (← urlErr "https://999.999.999.999/") "Invalid IPv4 address: '999.999.999.999'"⟩,
  ⟨"tests/models/test_url.py::test_url_invalid_ipv6", "invalid ipv6", do
    eqv "err" (← urlErr "https://[2001]/") "Invalid IPv6 address: '[2001]'"⟩
]

/-! ## Headers and query parameters -/

def headerCases : List Case := [
  ⟨"tests/models/test_headers.py::test_headers", "headers", do
    let h : Headers := [("a", "123"), ("a", "456"), ("b", "789")]
    allOk [eqv "in a" (h.contains "a") true, eqv "in A" (h.contains "A") true, eqv "in c" (h.contains "c") false,
      eqv "get" (h.get? "a") (some "123, 456"), eqv "nope" (h.get? "nope") none,
      eqv "get_list" (h.getList "a") ["123", "456"], eqv "keys" h.keys ["a", "b"],
      eqv "values" h.values ["123, 456", "789"], eqv "items" h.items [("a", "123, 456"), ("b", "789")],
      eqv "multi" h.multiItems [("a", "123"), ("a", "456"), ("b", "789")],
      eqv "repr" h.pyRepr "Headers([('a', '123'), ('a', '456'), ('b', '789')])",
      eqv "eq1" (h.equiv [("a", "123"), ("b", "789"), ("a", "456")]) true,
      eqv "eq2" (h.equiv [("a", "123"), ("A", "456"), ("b", "789")]) true,
      eqv "dict repr" (Headers.ofList [("a", "123"), ("b", "789")]).pyRepr "Headers({'a': '123', 'b': '789'})"]⟩,
  ⟨"tests/models/test_headers.py::test_header_mutations", "header mutations", do
    let h : Headers := {}
    let h := h.set "a" "1"
    let h1 := h.items
    let h := h.set "a" "2"
    let h2 := h.items
    let h := h.setdefault "a" "3"
    let h3 := h.items
    let h := h.setdefault "b" "4"
    let h4 := h.items
    let h := h.delete "a"
    allOk [eqv "1" h1 [("a", "1")], eqv "2" h2 [("a", "2")], eqv "3" h3 [("a", "2")],
      eqv "4" h4 [("a", "2"), ("b", "4")], eqv "5" h.raw [("b", "4")]]⟩,
  ⟨"tests/models/test_headers.py::test_headers_insert_retains_ordering", "insert keeps order", do
    eqv "v" (Headers.ofList [("a", "a"), ("b", "b"), ("c", "c")] |>.set "b" "123").values ["a", "123", "c"]⟩,
  ⟨"tests/models/test_headers.py::test_headers_insert_appends_if_new", "insert appends", do
    eqv "v" (Headers.ofList [("a", "a"), ("b", "b"), ("c", "c")] |>.set "d" "123").values ["a", "b", "c", "123"]⟩,
  ⟨"tests/models/test_headers.py::test_headers_insert_removes_all_existing", "insert replaces all", do
    eqv "v" (Headers.ofList [("a", "123"), ("a", "456")] |>.set "a" "789").items [("a", "789")]⟩,
  ⟨"tests/models/test_headers.py::test_headers_delete_removes_all_existing", "delete removes all", do
    eqv "v" (Headers.ofList [("a", "123"), ("a", "456")] |>.delete "a").items []⟩,
  ⟨"tests/models/test_headers.py::test_headers_list_repr", "list repr", do
    eqv "r" (Headers.ofList [("custom", "example 1"), ("custom", "example 2")]).pyRepr
      "Headers([('custom', 'example 1'), ('custom', 'example 2')])"⟩,
  ⟨"tests/models/test_headers.py::test_headers_decode_ascii", "decode ascii", do
    eqv "d" (Headers.ofList [("Custom", "Example")]).items [("custom", "Example")]⟩,
  ⟨"tests/models/test_headers.py::test_headers_decode_utf_8", "decode utf-8", do
    eqv "d" (Text.decodeHeader "Code point: ☃".toUTF8) "Code point: ☃"⟩,
  ⟨"tests/models/test_headers.py::test_headers_decode_iso_8859_1", "decode iso-8859-1", do
    eqv "d" (Text.decodeHeader (ByteArray.mk #[67, 111, 100, 101, 32, 112, 111, 105, 110, 116, 58, 32, 0xff]))
      "Code point: ÿ"⟩,
  ⟨"tests/models/test_headers.py::test_multiple_headers", "multiple headers", do
    allOk [eqv "set-cookie" ((Headers.ofList [("set-cookie", "a, b"), ("set-cookie", "c")]).getList "Set-Cookie")
        ["a, b", "c"],
      eqv "vary" ((Headers.ofList [("vary", "a, b"), ("vary", "c")]).getList "Vary" (splitCommas := true))
        ["a", "b", "c"]]⟩,
  ⟨"tests/models/test_headers.py::test_sensitive_headers", "sensitive headers", do
    allOk [eqv "auth" (Headers.ofList [("authorization", "s3kr3t")]).pyRepr "Headers({'authorization': '[secure]'})",
      eqv "proxy" (Headers.ofList [("proxy-authorization", "s3kr3t")]).pyRepr
        "Headers({'proxy-authorization': '[secure]'})"]⟩,
  ⟨"tests/models/test_headers.py::test_parse_header_links", "parse header links", do
    let links (v : String) := (Response.new 200 (headers := [("Link", v)])).links.map (·.2)
    allOk [eqv "1" (links "<http:/.../front.jpeg>; rel=front; type=\"image/jpeg\"")
        [[("url", "http:/.../front.jpeg"), ("rel", "front"), ("type", "image/jpeg")]],
      eqv "2" (links "<http:/.../front.jpeg>") [[("url", "http:/.../front.jpeg")]],
      eqv "3" (links "<http:/.../front.jpeg>;") [[("url", "http:/.../front.jpeg")]],
      eqv "4" (links "<http:/.../front.jpeg>; type=\"image/jpeg\",<http://.../back.jpeg>;")
        [[("url", "http:/.../front.jpeg"), ("type", "image/jpeg")], [("url", "http://.../back.jpeg")]],
      eqv "5" (links "") []]⟩,
  ⟨"tests/models/test_queryparams.py::test_queryparams", "queryparams", do
    let q := QueryParams.parse "a=123&a=456&b=789"
    let q2 : QueryParams := [("a", "123"), ("a", "456"), ("b", "789")]
    allOk [eqv "in a" (q.contains "a") true, eqv "in A" (q.contains "A") false, eqv "get" (q.get? "a") (some "123"),
      eqv "nope" (q.get? "nope") none, eqv "get_list" (q.getList "a") ["123", "456"],
      eqv "keys" q.keys ["a", "b"], eqv "values" q.values ["123", "789"],
      eqv "items" q.items [("a", "123"), ("b", "789")], eqv "len" q.size 2,
      eqv "str" (toString q) "a=123&a=456&b=789", eqv "repr" q.pyRepr "QueryParams('a=123&a=456&b=789')",
      eqv "eq" (q.equiv q2) true,
      eqv "eq2" (QueryParams.equiv [("a", "123"), ("b", "456")] (QueryParams.parse "a=123&b=456")) true,
      eqv "eq3" (QueryParams.equiv [("a", "123"), ("b", "456")] [("b", "456"), ("a", "123")]) true]⟩,
  ⟨"tests/models/test_queryparams.py::test_empty_query_params", "empty query params", do
    allOk [eqv "1" (toString (QueryParams.ofList [("a", "")])) "a=", eqv "2" (toString (QueryParams.parse "a=")) "a=",
      eqv "3" (toString (QueryParams.parse "a")) "a="]⟩,
  ⟨"tests/models/test_queryparams.py::test_queryparam_set", "set", do
    eqv "s" ((QueryParams.parse "a=123").set "a" "456" |>.equiv (QueryParams.parse "a=456")) true⟩,
  ⟨"tests/models/test_queryparams.py::test_queryparam_add", "add", do
    eqv "s" ((QueryParams.parse "a=123").add "a" "456" |>.equiv (QueryParams.parse "a=123&a=456")) true⟩,
  ⟨"tests/models/test_queryparams.py::test_queryparam_remove", "remove", do
    eqv "s" ((QueryParams.parse "a=123").remove "a" |>.equiv (QueryParams.parse "")) true⟩,
  ⟨"tests/models/test_queryparams.py::test_queryparam_merge", "merge", do
    let q := (QueryParams.parse "a=123").merge [("b", "456")]
    let q2 := q.merge [("a", "000"), ("c", "789")]
    allOk [eqv "1" (q.equiv (QueryParams.parse "a=123&b=456")) true,
      eqv "2" (q2.equiv (QueryParams.parse "a=000&b=456&c=789")) true]⟩
]

/-! ## Cookies (`tests/models/test_cookies.py`, `tests/client/test_cookies.py`) -/

def cookieCases : List Case := [
  ⟨"tests/models/test_cookies.py::test_cookies", "cookies", do
    let c : Cookies := [("name", "value")]
    let d := c.delete "name"
    allOk [eqv "get" (c.get? "name" |>.toOption |>.join) (some "value"), eqv "len" c.size 1,
      eqv "names" c.names ["name"], eqv "deleted" d.size 0]⟩,
  ⟨"tests/models/test_cookies.py::test_cookies_update", "update", do
    let more := ({} : Cookies).set "name" "value" (domain := "example.com")
    let c := ({} : Cookies).update more
    allOk [eqv "names" c.names ["name"],
      eqv "get" (c.get? "name" (domain := some "example.com") |>.toOption |>.join) (some "value")]⟩,
  ⟨"tests/models/test_cookies.py::test_cookies_with_domain", "with domain", do
    let c := ({} : Cookies).set "name" "value" (domain := "example.com") |>.set "name" "value" (domain := "example.org")
    let conflict := match c.get? "name" with | .error (.cookieConflict _) => true | _ => false
    allOk [eqv "conflict" conflict true, eqv "after clear" (c.clear (some "example.com")).size 1]⟩,
  ⟨"tests/models/test_cookies.py::test_cookies_with_domain_and_path", "with domain and path", do
    let c := ({} : Cookies).set "name" "value" "example.com" "/subpath/1" |>.set "name" "value" "example.com" "/subpath/2"
    let c := c.clear (some "example.com") (some "/subpath/1")
    let n1 := c.size
    let c := c.delete "name" (some "example.com") (some "/subpath/2")
    allOk [eqv "1" n1 1, eqv "0" c.size 0]⟩,
  ⟨"tests/models/test_cookies.py::test_multiple_set_cookie", "multiple set-cookie", do
    let u ← url! "https://www.example.org"
    let c := ({} : Cookies).extract
      ["1P_JAR=2020-08-09-18; expires=Tue, 08-Sep-2099 18:33:35 GMT; path=/; domain=.example.org; Secure",
       "NID=204=KWdXOuypc86YvRfBSiWoW1dEXfSl; expires=Mon, 08-Feb-2099 18:33:35 GMT; path=/; domain=.example.org; HttpOnly"]
      u 1700000000 2026
    eqv "len" c.size 2⟩,
  ⟨"tests/models/test_cookies.py::test_cookies_can_be_a_list_of_tuples", "list of tuples", do
    let c : Cookies := [("name1", "val1"), ("name2", "val2")]
    allOk [eqv "len" c.size 2, eqv "1" (c.get? "name1" |>.toOption |>.join) (some "val1"),
      eqv "2" (c.get? "name2" |>.toOption |>.join) (some "val2")]⟩,
  ⟨"tests/models/test_cookies.py::test_cookies_repr", "repr", do
    let c := ({} : Cookies).set "foo" "bar" (domain := "http://blah.com") |>.set "fizz" "buzz" (domain := "http://hello.com")
    eqv "r" c.pyRepr "<Cookies[<Cookie foo=bar for http://blah.com />, <Cookie fizz=buzz for http://hello.com />]>"⟩,
  ⟨"tests/client/test_cookies.py::test_set_cookie", "client sends cookies", do
    let c ← Client.new (cookies := [("example-name", "example-value")])
      (transport := MockTransport fun r => Response.new 200 (json := json% {"cookies": ((r.headers.get? "cookie").getD "")}))
    let r ← c.get "http://example.org/echo_cookies"
    eqv "body" r.text "{\"cookies\":\"example-name=example-value\"}"⟩,
  ⟨"tests/client/test_cookies.py::test_get_cookie", "client stores cookies", do
    let c ← mockClient fun _ => Response.new 200 (headers := [("set-cookie", "example-name=example-value")])
    let _ ← c.get "http://example.org/set_cookie"
    let j ← c.cookies
    eqv "cookie" (j.get? "example-name" |>.toOption |>.join) (some "example-value")⟩,
  ⟨"tests/client/test_cookies.py::test_cookie_persistence", "cookie persistence", do
    let c ← mockClient fun r =>
      if r.url.path == "/set_cookie" then Response.new 200 (headers := [("set-cookie", "example-name=example-value")])
      else Response.new 200 (json := json% {"cookies": ((r.headers.get? "cookie").getD "")})
    let r1 ← c.get "http://example.org/echo_cookies"
    let _ ← c.get "http://example.org/set_cookie"
    let r2 ← c.get "http://example.org/echo_cookies"
    allOk [eqv "before" r1.text "{\"cookies\":\"\"}", eqv "after" r2.text "{\"cookies\":\"example-name=example-value\"}"]⟩,
  ⟨"tests/client/test_cookies.py::test_setting_client_cookies_to_cookiejar", "cookie path and domain matching", do
    let u ← url! "http://example.org/foo/bar"
    let c := ({} : Cookies).extract ["a=1; Path=/foo", "b=2; Path=/other", "c=3"] u 0 2026
    allOk [eqv "header" (c.cookieHeader u 0) (some "a=1; c=3"),
      eqv "other host" (c.cookieHeader (← url! "http://example.com/foo") 0) none]⟩
]

/-! ## Requests and responses (`tests/models/test_requests.py`, `test_responses.py`) -/

def req! (method url : String) (headers : Headers := {}) (content : Option Content := none)
    (json : Option Json := none) (data : List (String × String) := []) : IO Request := do
  except! (Request.new method (← url! url) (headers := headers) (content := content) (json := json) (data := data))

def modelCases : List Case := [
  ⟨"tests/models/test_requests.py::test_request_repr", "request repr", do
    eqv "r" (reprStr (← req! "GET" "http://example.org")) "<Request('GET', 'http://example.org')>"⟩,
  ⟨"tests/models/test_requests.py::test_no_content", "no content", do
    eqv "cl" ((← req! "GET" "http://example.org").headers.contains "Content-Length") false⟩,
  ⟨"tests/models/test_requests.py::test_content_length_header", "content length", do
    eqv "cl" ((← req! "POST" "http://example.org" (content := "test 123")).headers.get? "Content-Length")
      (some "8")⟩,
  ⟨"tests/models/test_requests.py::test_json_encoded_data", "json body", do
    let r ← req! "POST" "http://example.org" (json := json% {"test": 123})
    allOk [eqv "ct" (r.headers.get? "Content-Type") (some "application/json"), eqv "body" (str r.content) "{\"test\":123}"]⟩,
  ⟨"tests/models/test_requests.py::test_url_encoded_data", "form body", do
    let r ← req! "POST" "http://example.org" (data := [("test", "123")])
    allOk [eqv "ct" (r.headers.get? "Content-Type") (some "application/x-www-form-urlencoded"),
      eqv "body" (str r.content) "test=123"]⟩,
  ⟨"tests/models/test_requests.py::test_override_host_header", "override host", do
    eqv "host" ((← req! "GET" "http://example.org" (headers := [("Host", "1.2.3.4:80")])).headers.get? "Host")
      (some "1.2.3.4:80")⟩,
  ⟨"tests/models/test_requests.py::test_override_content_length_header", "override content-length", do
    let r ← req! "POST" "http://example.org" (headers := [("Content-Length", "8")]) (content := "test 123")
    eqv "cl" (r.headers.getList "Content-Length") ["8"]⟩,
  ⟨"tests/models/test_requests.py::test_url", "request url", do
    let r ← req! "GET" "http://example.org"
    let s ← req! "GET" "https://example.org/abc?foo=bar"
    allOk [eqv "scheme" r.url.scheme "http", eqv "port" r.url.port none, eqv "path" r.url.path "/",
      eqv "raw" r.url.rawPath "/", eqv "s port" s.url.port none, eqv "s raw" s.url.rawPath "/abc?foo=bar"]⟩,
  ⟨"tests/models/test_requests.py::test_request_params", "request params", do
    let r ← except! (Request.new "GET" (← url! "http://example.com") (params := some [("a", "b")]))
    eqv "url" (toString r.url) "http://example.com?a=b"⟩,
  ⟨"tests/models/test_responses.py::test_response", "response", do
    let r := Response.new 200 (content := "Hello, world!")
    allOk [eqv "status" r.statusCode 200, eqv "reason" r.reasonPhrase "OK", eqv "text" r.text "Hello, world!"]⟩,
  ⟨"tests/models/test_responses.py::test_response_content", "response content", do
    let r := Response.new 200 (content := "Hello, world!")
    allOk [eqv "content" (str r.content) "Hello, world!", eqv "cl" (r.headers.get? "Content-Length") (some "13")]⟩,
  ⟨"tests/models/test_responses.py::test_response_text", "response text", do
    let r := Response.new 200 (text := "Hello, world!")
    allOk [eqv "text" r.text "Hello, world!", eqv "ct" (r.headers.get? "Content-Type") (some "text/plain; charset=utf-8")]⟩,
  ⟨"tests/models/test_responses.py::test_response_html", "response html", do
    let r := Response.new 200 (html := "<html><body>Hello, world!</html></body>")
    eqv "ct" (r.headers.get? "Content-Type") (some "text/html; charset=utf-8")⟩,
  ⟨"tests/models/test_responses.py::test_response_json", "response json", do
    let r := Response.new 200 (json := json% {"hello": "world"})
    allOk [eqv "text" r.text "{\"hello\":\"world\"}", eqv "ct" (r.headers.get? "Content-Type") (some "application/json"),
      eqv "json" (match r.json with | .ok j => toString j | .error _ => "error") "{\"hello\":\"world\"}"]⟩,
  ⟨"tests/models/test_responses.py::test_raise_for_status", "raise_for_status", do
    let req ← req! "GET" "https://example.org"
    let msg (code : Nat) (hs : Headers := {}) : String :=
      match (Response.new code (headers := hs) (request := some req)).raiseForStatus with
      | .ok _ => "ok" | .error e => e.message
    allOk [eqv "200" (msg 200) "ok",
      eqv "101" (msg 101) "Informational response '101 Switching Protocols' for url 'https://example.org'\nFor more information check: https://developer.mozilla.org/en-US/docs/Web/HTTP/Status/101",
      eqv "303" (msg 303 [("location", "https://other.org")]) "Redirect response '303 See Other' for url 'https://example.org'\nRedirect location: 'https://other.org'\nFor more information check: https://developer.mozilla.org/en-US/docs/Web/HTTP/Status/303",
      eqv "404" (msg 404) "Client error '404 Not Found' for url 'https://example.org'\nFor more information check: https://developer.mozilla.org/en-US/docs/Web/HTTP/Status/404",
      eqv "500" (msg 500) "Server error '500 Internal Server Error' for url 'https://example.org'\nFor more information check: https://developer.mozilla.org/en-US/docs/Web/HTTP/Status/500",
      eqv "600" (msg 600) "Invalid status code '600 ' for url 'https://example.org'\nFor more information check: https://developer.mozilla.org/en-US/docs/Web/HTTP/Status/600"]⟩,
  ⟨"tests/models/test_responses.py::test_response_default_text_encoding", "default text encoding", do
    let r := Response.new 200 (content := "Hello, world!") (headers := [("Content-Type", "text/plain")])
    allOk [eqv "text" r.text "Hello, world!", eqv "enc" r.encoding "utf-8"]⟩,
  ⟨"tests/models/test_responses.py::test_response_set_explicit_encoding", "latin-1 charset", do
    let r := Response.new 200 (content := Content.bytes "Latin 1: ÿ".toUTF8)
      (headers := [("Content-Type", "text-plain; charset=iso-8859-1")])
    allOk [eqv "enc" r.encoding "iso-8859-1", eqv "text" r.text "Latin 1: Ã¿"]⟩,
  ⟨"tests/models/test_responses.py::test_response_non_text_encoding", "non-text encoding", do
    let r := Response.new 200 (content := "xyz") (headers := [("Content-Type", "image/png")])
    allOk [eqv "text" r.text "xyz", eqv "enc" r.encoding "utf-8"]⟩,
  ⟨"tests/models/test_responses.py::test_response_force_encoding", "unknown charset falls back", do
    let r := Response.new 200 (content := "Hello") (headers := [("Content-Type", "text/plain; charset=invalid-codec-name")])
    eqv "enc" r.encoding "utf-8"⟩,
  ⟨"tests/models/test_responses.py::test_value_error_without_request", "properties", do
    let r := Response.new 404
    allOk [eqv "is_error" r.isError true, eqv "client" r.isClientError true, eqv "server" r.isServerError false,
      eqv "redirect" r.isRedirect false, eqv "success" r.isSuccess false]⟩,
  ⟨"tests/models/test_responses.py::test_response_repr", "response repr", do
    eqv "r" (reprStr (Response.new 200 (content := "Hello, world!"))) "<Response [200 OK]>"⟩,
  ⟨"tests/test_decoders.py::test_gzip", "gzip decoding", do
    -- gzip.compress(b"test 123", mtime=0)
    let gz := ByteArray.mk #[31, 139, 8, 0, 0, 0, 0, 0, 2, 255, 43, 73, 45, 46, 81, 48, 52, 50, 6, 0, 223, 15, 105, 194, 8, 0, 0, 0]
    let r : Response := { statusCode := 200, headers := [("Content-Encoding", "gzip")], stream := some gz }
    eqv "content" (match Client.read r with | .ok r => str r.content | .error e => toString e) "test 123"⟩,
  ⟨"tests/test_decoders.py::test_deflate", "deflate decoding", do
    -- zlib.compress(b"test 123")
    let z := ByteArray.mk #[0x78,0x9c,0x2b,0x49,0x2d,0x2e,0x51,0x30,0x34,0x32,0x06,0x00,0x0b,0xc5,0x02,0x59]
    let r : Response := { statusCode := 200, headers := [("Content-Encoding", "deflate")], stream := some z }
    eqv "content" (match Client.read r with | .ok r => str r.content | .error e => toString e) "test 123"⟩,
  ⟨"tests/test_decoders.py::test_zlib", "raw deflate decoding", do
    -- zlib.compress(b"test 123")[2:-4]
    let z := ByteArray.mk #[0x2b,0x49,0x2d,0x2e,0x51,0x30,0x34,0x32,0x06,0x00]
    let r : Response := { statusCode := 200, headers := [("Content-Encoding", "deflate")], stream := some z }
    eqv "content" (match Client.read r with | .ok r => str r.content | .error e => toString e) "test 123"⟩,
  ⟨"tests/test_decoders.py::test_multi", "gzip then deflate", do
    -- gzip.compress(zlib.compress(b"test 123"), mtime=0)
    let deflated := ByteArray.mk #[0x78,0x9c,0x2b,0x49,0x2d,0x2e,0x51,0x30,0x34,0x32,0x06,0x00,0x0b,0xc5,0x02,0x59]
    let r : Response := { statusCode := 200, headers := [("Content-Encoding", "deflate, identity")], stream := some deflated }
    eqv "content" (match Client.read r with | .ok r => str r.content | .error e => toString e) "test 123"⟩,
  ⟨"tests/test_decoders.py::test_decoding_errors", "decoding error", do
    let r : Response := { statusCode := 200, headers := [("Content-Encoding", "gzip")], stream := some "test 123".toUTF8 }
    eqv "err" (match Client.read r with | .ok _ => "ok" | .error e => e.name) "DecodingError"⟩
]

/-! ## The client (`tests/client/`) -/

def echo (r : Request) : Response :=
  Response.new 200 (json := json% {"method": (r.method), "url": (toString r.url),
    "headers": (Json.obj (r.headers.multiItems.map fun (k, v) => (k, Json.str v)).toArray), "body": (str r.content)})

def field (r : Response) (k : String) : String :=
  match r.json with
  | .ok j => match j.getObjVal? k with
    | some (.str s) => s
    | some v => toString v
    | none => ""
  | .error _ => ""

/-- The redirect app of `tests/client/test_redirects.py`. -/
def redirects (r : Request) : Response :=
  let p := r.url.path
  let loc (code : Nat) (l : String) := Response.new code (headers := [("location", l)])
  if p == "/redirect_301" then loc 301 "https://example.org/"
  else if p == "/redirect_302" then loc 302 "https://example.org/"
  else if p == "/redirect_303" then loc 303 "https://example.org/"
  else if p == "/relative_redirect" then loc 303 "/"
  else if p == "/malformed_redirect" then loc 303 "https://:443/"
  else if p == "/no_scheme_redirect" then loc 303 "//example.org/"
  else if p.startsWith "/multiple_redirects" then
    let count := ((r.url.params.get? "count").bind String.toNat?).getD 0
    if count > 0 then loc 303 (if count > 1 then s!"/multiple_redirects?count={count - 1}" else "/multiple_redirects")
    else Response.new 200
  else if p == "/redirect_loop" then loc 303 "/redirect_loop"
  else if p == "/cross_domain" then loc 303 "https://example.org/cross_domain_target"
  else if p == "/cross_domain_target" then echo r
  else if p == "/redirect_body" then loc 308 "/redirect_body_target"
  else if p == "/redirect_no_body" then loc 303 "/redirect_body_target"
  else if p == "/redirect_body_target" then echo r
  else if p == "/cross_subdomain" then
    if r.headers.get? "host" == some "example.org" then loc 301 "https://www.example.org/cross_subdomain" else Response.new 200 (text := "Hello, world!")
  else if p == "/redirect_custom_scheme" then loc 301 "market://details?id=42"
  else if r.method == "HEAD" then Response.new 200
  else Response.new 200 (html := "<html><body>Hello, world!</body></html>")

def clientCases : List Case := [
  ⟨"tests/client/test_client.py::test_get", "get", do
    let c ← mockClient echo
    let r ← c.get "http://example.org/"
    allOk [eqv "status" r.statusCode 200, eqv "reason" r.reasonPhrase "OK", eqv "url" (toString r.url) "http://example.org/",
      eqv "http_version" r.httpVersion "HTTP/1.1", eqv "repr" (reprStr r) "<Response [200 OK]>"]⟩,
  ⟨"tests/client/test_client.py::test_build_request", "build_request", do
    let c ← Client.new (transport := MockTransport echo)
    let req ← IO.ofExcept ((c.buildRequest "GET" "http://example.org/" (headers := [("Custom-header", "value")])).mapError toString)
    let r ← c.send req
    allOk [eqv "status" r.statusCode 200, eqv "header" ((field r "headers").contains "custom-header") true]⟩,
  ⟨"tests/client/test_client.py::test_post", "post", do
    let c ← mockClient echo
    let r ← c.post "http://example.org/" (content := "Hello, world!")
    allOk [eqv "status" r.statusCode 200, eqv "body" (field r "body") "Hello, world!"]⟩,
  ⟨"tests/client/test_client.py::test_post_json", "post json", do
    let c ← mockClient echo
    let r ← c.post "http://example.org/" (json := json% {"text": "Hello, world!"})
    eqv "body" (field r "body") "{\"text\":\"Hello, world!\"}"⟩,
  ⟨"tests/client/test_client.py::test_raise_for_status", "client raise_for_status", do
    let c ← mockClient fun r => Response.new (((r.url.path.drop 8).toString.toNat?).getD 200)
    let msgs ← [200, 400, 404, 500, 505].mapM fun code => do
      let r ← c.get s!"http://example.org/status/{code}"
      pure (match r.raiseForStatus with | .ok _ => "ok" | .error e => e.name)
    eqv "kinds" msgs ["ok", "HTTPStatusError", "HTTPStatusError", "HTTPStatusError", "HTTPStatusError"]⟩,
  ⟨"tests/client/test_client.py::test_head", "head", do
    let c ← mockClient echo
    eqv "status" (← c.head "http://example.org/").statusCode 200⟩,
  ⟨"tests/client/test_client.py::test_put", "put", do
    let c ← mockClient echo
    eqv "method" (field (← c.put "http://example.org/" (content := "x")) "method") "PUT"⟩,
  ⟨"tests/client/test_client.py::test_patch", "patch", do
    let c ← mockClient echo
    eqv "method" (field (← c.patch "http://example.org/" (content := "x")) "method") "PATCH"⟩,
  ⟨"tests/client/test_client.py::test_delete", "delete", do
    let c ← mockClient echo
    eqv "method" (field (← c.delete "http://example.org/") "method") "DELETE"⟩,
  ⟨"tests/client/test_client.py::test_options", "options", do
    let c ← mockClient echo
    eqv "method" (field (← c.options "http://example.org/") "method") "OPTIONS"⟩,
  ⟨"tests/client/test_client.py::test_base_url", "base_url", do
    let c ← mockClient echo (baseUrl := "http://example.org")
    let r ← c.get "/"
    allOk [eqv "base" (toString c.baseUrl) "http://example.org", eqv "url" (toString r.url) "http://example.org/"]⟩,
  ⟨"tests/client/test_client.py::test_merge_absolute_url", "merge absolute url", do
    let c ← mockClient echo (baseUrl := "https://www.example.com/")
    let req ← IO.ofExcept ((c.buildRequest "GET" "http://www.example.com/").mapError toString)
    eqv "url" (toString req.url) "http://www.example.com/"⟩,
  ⟨"tests/client/test_client.py::test_merge_relative_url", "merge relative url", do
    let c ← mockClient echo (baseUrl := "https://www.example.com/")
    let req ← IO.ofExcept ((c.buildRequest "GET" "/testing/123").mapError toString)
    eqv "url" (toString req.url) "https://www.example.com/testing/123"⟩,
  ⟨"tests/client/test_client.py::test_merge_relative_url_with_path", "merge relative url with path", do
    let c ← mockClient echo (baseUrl := "https://www.example.com/some/path")
    let req ← IO.ofExcept ((c.buildRequest "GET" "/testing/123").mapError toString)
    eqv "url" (toString req.url) "https://www.example.com/some/path/testing/123"⟩,
  ⟨"tests/client/test_client.py::test_merge_relative_url_with_dotted_path", "merge dotted path", do
    let c ← mockClient echo (baseUrl := "https://www.example.com/some/path")
    let req ← IO.ofExcept ((c.buildRequest "GET" "../testing/123").mapError toString)
    eqv "url" (toString req.url) "https://www.example.com/some/testing/123"⟩,
  ⟨"tests/client/test_client.py::test_merge_relative_url_with_encoded_slashes", "merge encoded slashes", do
    let c ← mockClient echo (baseUrl := "https://www.example.com/")
    let req ← IO.ofExcept ((c.buildRequest "GET" "/testing%2F123").mapError toString)
    eqv "url" (toString req.url) "https://www.example.com/testing%2F123"⟩,
  ⟨"tests/client/test_client.py::test_client_closed_state_using_implicit_open", "closed client", do
    let c ← mockClient echo
    c.close
    eqv "err" ((← failure (c.get "http://example.org")).contains "client has been closed") true⟩,
  ⟨"tests/client/test_headers.py::test_client_header", "client headers", do
    let c ← Client.new (headers := [("Example-Header", "example-value")]) (transport := MockTransport echo)
    let r ← c.get "http://example.org/echo_headers"
    eqv "headers" (field r "headers")
      "{\"host\":\"example.org\",\"accept\":\"*/*\",\"accept-encoding\":\"gzip, deflate\",\"connection\":\"keep-alive\",\"user-agent\":\"lean-httpx/0.1.0\",\"example-header\":\"example-value\"}"⟩,
  ⟨"tests/client/test_headers.py::test_header_merge", "header merge", do
    let c ← Client.new (headers := [("User-Agent", "python-myclient/0.2.1")]) (transport := MockTransport echo)
    let r ← c.get "http://example.org/echo_headers" (headers := [("X-Auth-Token", "FooBarBazToken")])
    allOk [eqv "ua" ((field r "headers").contains "\"user-agent\":\"python-myclient/0.2.1\"") true,
      eqv "tok" ((field r "headers").contains "\"x-auth-token\":\"FooBarBazToken\"") true]⟩,
  ⟨"tests/client/test_headers.py::test_header_does_not_exist", "header does not exist", do
    let c ← Client.new (headers := [("foo", "bar")]) (transport := MockTransport echo)
    eqv "nope" (c.headers.get? "nope") none⟩,
  ⟨"tests/client/test_headers.py::test_host_with_auth_and_port_in_url", "host with auth and port", do
    let c ← mockClient echo
    let r ← c.get "http://username:password@example.org:80/echo_headers"
    allOk [eqv "host" ((field r "headers").contains "\"host\":\"example.org\"") true,
      eqv "auth" ((field r "headers").contains "\"authorization\":\"Basic dXNlcm5hbWU6cGFzc3dvcmQ=\"") true]⟩,
  ⟨"tests/client/test_headers.py::test_host_with_non_default_port_in_url", "host with non-default port", do
    let c ← mockClient echo
    let r ← c.get "http://username:password@example.org:123/echo_headers"
    eqv "host" ((field r "headers").contains "\"host\":\"example.org:123\"") true⟩,
  ⟨"tests/client/test_queryparams.py::test_client_queryparams", "client params", do
    let c ← Client.new (params := [("a", "b")]) (transport := MockTransport echo)
    let r1 ← c.get "http://example.org/echo_queryparams"
    let r2 ← c.get "http://example.org/echo_queryparams" (params := [("c", "d")])
    allOk [eqv "1" (toString r1.url) "http://example.org/echo_queryparams?a=b",
      eqv "2" (toString r2.url) "http://example.org/echo_queryparams?a=b&c=d"]⟩,
  ⟨"tests/client/test_event_hooks.py::test_event_hooks", "event hooks", do
    let log ← IO.mkRef ([] : List String)
    let c ← Client.new (transport := MockTransport echo) (eventHooks := {
      request := [fun r => log.modify (· ++ [s!"request {r.method}"])],
      response := [fun r => log.modify (· ++ [s!"response {r.statusCode}"])] })
    let _ ← c.get "http://127.0.0.1:8000/"
    eqv "log" (← log.get) ["request GET", "response 200"]⟩,
  ⟨"tests/client/test_event_hooks.py::test_event_hooks_raising_exception", "hook raising", do
    let c ← Client.new (transport := MockTransport fun _ => Response.new 404) (eventHooks := {
      response := [fun r => match r.raiseForStatus with | .ok _ => pure () | .error e => throw (IO.userError (toString e))] })
    eqv "err" ((← failure (c.get "http://127.0.0.1:8000/")).startsWith "HTTPStatusError") true⟩,
  ⟨"tests/client/test_event_hooks.py::test_event_hooks_with_redirect", "hooks see redirects", do
    let log ← IO.mkRef ([] : List String)
    let c ← Client.new (transport := MockTransport redirects) (followRedirects := true) (eventHooks := {
      request := [fun r => log.modify (· ++ [s!"request {r.url}"])] })
    let _ ← c.get "http://example.org/redirect_303"
    eqv "log" (← log.get) ["request http://example.org/redirect_303", "request https://example.org/"]⟩
]

/-! ## Redirects (`tests/client/test_redirects.py`) -/

def redirectCases : List Case := [
  ⟨"tests/client/test_redirects.py::test_redirect_301", "301", do
    let c ← mockClient redirects
    let r ← c.post "https://example.org/redirect_301" (followRedirects := true)
    allOk [eqv "status" r.statusCode 200, eqv "url" (toString r.url) "https://example.org/", eqv "hist" r.history.length 1]⟩,
  ⟨"tests/client/test_redirects.py::test_redirect_302", "302", do
    let c ← mockClient redirects
    let r ← c.post "https://example.org/redirect_302" (followRedirects := true)
    allOk [eqv "status" r.statusCode 200, eqv "url" (toString r.url) "https://example.org/", eqv "hist" r.history.length 1]⟩,
  ⟨"tests/client/test_redirects.py::test_redirect_303", "303", do
    let c ← mockClient redirects
    let r ← c.get "https://example.org/redirect_303" (followRedirects := true)
    allOk [eqv "status" r.statusCode 200, eqv "url" (toString r.url) "https://example.org/", eqv "hist" r.history.length 1]⟩,
  ⟨"tests/client/test_redirects.py::test_next_request", "next_request", do
    let c ← mockClient redirects
    let r ← c.post "https://example.org/redirect_303"
    let next := r.nextRequest.getD default
    let r2 ← c.send next
    allOk [eqv "status" r.statusCode 303, eqv "next" (toString next.url) "https://example.org/", eqv "status2" r2.statusCode 200]⟩,
  ⟨"tests/client/test_redirects.py::test_head_redirect", "head redirect", do
    let c ← mockClient redirects
    let r ← c.head "https://example.org/redirect_302" (followRedirects := true)
    allOk [eqv "status" r.statusCode 200, eqv "url" (toString r.url) "https://example.org/",
      eqv "method" r.request.method "HEAD", eqv "hist" r.history.length 1, eqv "text" r.text ""]⟩,
  ⟨"tests/client/test_redirects.py::test_relative_redirect", "relative redirect", do
    let c ← mockClient redirects
    let r ← c.get "https://example.org/relative_redirect" (followRedirects := true)
    allOk [eqv "url" (toString r.url) "https://example.org/", eqv "hist" r.history.length 1]⟩,
  ⟨"tests/client/test_redirects.py::test_malformed_redirect", "malformed redirect", do
    let c ← mockClient redirects
    let r ← c.get "http://example.org/malformed_redirect" (followRedirects := true)
    allOk [eqv "url" (r.url == (← url! "https://example.org:443/")) true, eqv "hist" r.history.length 1]⟩,
  ⟨"tests/client/test_redirects.py::test_no_scheme_redirect", "no-scheme redirect", do
    let c ← mockClient redirects
    let r ← c.get "https://example.org/no_scheme_redirect" (followRedirects := true)
    allOk [eqv "url" (toString r.url) "https://example.org/", eqv "hist" r.history.length 1]⟩,
  ⟨"tests/client/test_redirects.py::test_fragment_redirect", "fragment kept", do
    let c ← mockClient redirects
    let r ← c.get "https://example.org/relative_redirect#fragment" (followRedirects := true)
    eqv "url" (toString r.url) "https://example.org/#fragment"⟩,
  ⟨"tests/client/test_redirects.py::test_multiple_redirects", "multiple redirects", do
    let c ← mockClient redirects
    let r ← c.get "https://example.org/multiple_redirects?count=20" (followRedirects := true)
    allOk [eqv "url" (toString r.url) "https://example.org/multiple_redirects", eqv "hist" r.history.length 20,
      eqv "first" (toString r.history.head!.url) "https://example.org/multiple_redirects?count=20",
      eqv "second" (toString (r.history.getD 1 default).url) "https://example.org/multiple_redirects?count=19",
      eqv "h0" r.history.head!.history.length 0, eqv "h1" (r.history.getD 1 default).history.length 1]⟩,
  ⟨"tests/client/test_redirects.py::test_too_many_redirects", "too many redirects", do
    let c ← mockClient redirects
    eqv "err" ((← failure (c.get "https://example.org/multiple_redirects?count=21" (followRedirects := true))).startsWith
      "TooManyRedirects") true⟩,
  ⟨"tests/client/test_redirects.py::test_redirect_loop", "redirect loop", do
    let c ← mockClient redirects
    eqv "err" ((← failure (c.get "https://example.org/redirect_loop" (followRedirects := true))).startsWith
      "TooManyRedirects") true⟩,
  ⟨"tests/client/test_redirects.py::test_cross_domain_redirect_with_auth_header", "cross-domain drops auth", do
    let c ← mockClient redirects
    let r ← c.get "https://example.com/cross_domain" (headers := [("Authorization", "abc")]) (followRedirects := true)
    allOk [eqv "url" (toString r.url) "https://example.org/cross_domain_target",
      eqv "auth" ((field r "headers").contains "authorization") false]⟩,
  ⟨"tests/client/test_redirects.py::test_same_domain_redirect", "same domain keeps auth", do
    let c ← mockClient redirects
    let r ← c.get "https://example.org/cross_domain" (headers := [("Authorization", "abc")]) (followRedirects := true)
    eqv "auth" ((field r "headers").contains "\"authorization\":\"abc\"") true⟩,
  ⟨"tests/client/test_redirects.py::test_body_redirect", "308 keeps body", do
    let c ← mockClient redirects
    let r ← c.post "https://example.org/redirect_body" (content := "Example request body")
      (followRedirects := true)
    allOk [eqv "url" (toString r.url) "https://example.org/redirect_body_target",
      eqv "body" (field r "body") "Example request body",
      eqv "cl" ((field r "headers").contains "\"content-length\":\"20\"") true]⟩,
  ⟨"tests/client/test_redirects.py::test_no_body_redirect", "303 drops body", do
    let c ← mockClient redirects
    let r ← c.post "https://example.org/redirect_no_body" (content := "Example request body")
      (followRedirects := true)
    allOk [eqv "body" (field r "body") "", eqv "cl" ((field r "headers").contains "content-length") false]⟩,
  ⟨"tests/client/test_redirects.py::test_cross_subdomain_redirect", "cross subdomain", do
    let c ← mockClient redirects
    let r ← c.get "https://example.org/cross_subdomain" (followRedirects := true)
    eqv "url" (toString r.url) "https://www.example.org/cross_subdomain"⟩,
  ⟨"tests/client/test_redirects.py::test_redirect_cookie_behavior", "redirect cookies", do
    let c ← mockClient (followRedirects := true) fun r =>
      if r.url.path == "/login" then Response.new 302 (headers := [("location", "/"), ("set-cookie", "session=eat_me")])
      else if r.url.path == "/logout" then Response.new 302 (headers := [("location", "/"), ("set-cookie", "session=null; max-age=0")])
      else Response.new 200 (text := if (r.headers.get? "cookie").isSome then "Logged in" else "Not logged in")
    let r1 ← c.get "https://example.com/"
    let r2 ← c.get "https://example.com/login"
    let r3 ← c.get "https://example.com/"
    let r4 ← c.get "https://example.com/logout"
    allOk [eqv "1" r1.text "Not logged in", eqv "2" r2.text "Logged in", eqv "3" r3.text "Logged in",
      eqv "4" r4.text "Not logged in"]⟩,
  ⟨"tests/client/test_redirects.py::test_redirect_301", "method rewrite table", do
    allOk [eqv "301 POST" (redirectMethod 301 "POST") "GET", eqv "301 PUT" (redirectMethod 301 "PUT") "PUT",
      eqv "302 POST" (redirectMethod 302 "POST") "GET", eqv "302 HEAD" (redirectMethod 302 "HEAD") "HEAD",
      eqv "303 PUT" (redirectMethod 303 "PUT") "GET", eqv "307 POST" (redirectMethod 307 "POST") "POST",
      eqv "308 POST" (redirectMethod 308 "POST") "POST"]⟩
]

/-! ## Authentication (`tests/client/test_auth.py`, `tests/test_auth.py`) -/

/-- The challenge of RFC 7616 section 3.9.1. -/
def rfcChallenge (alg : String) : DigestChallenge :=
  DigestChallenge.mk "http-auth@example.org" "7ypf/xlj9XXwfDPEoM4URrv/xwf94BcCAzFZH4GiTo0v" alg
    (some "FQhe/qaU925kfnzjCev0ciny7QMkPqMAFRtzCUYo5tdS") (some "auth, auth-int")

def authCases : List Case := [
  ⟨"tests/client/test_auth.py::test_basic_auth", "basic auth", do
    let c ← mockClient echo
    let r ← c.get "https://example.org/" (auth := ("user", "password123"))
    eqv "auth" ((field r "headers").contains "\"authorization\":\"Basic dXNlcjpwYXNzd29yZDEyMw==\"") true⟩,
  ⟨"tests/client/test_auth.py::test_basic_auth_with_stream", "basic auth header", do
    eqv "h" (basicAuthHeader "user" "password123") "Basic dXNlcjpwYXNzd29yZDEyMw=="⟩,
  ⟨"tests/client/test_auth.py::test_basic_auth_in_url", "basic auth in url", do
    let c ← mockClient echo
    let r ← c.get "https://user:password123@example.org/"
    eqv "auth" ((field r "headers").contains "\"authorization\":\"Basic dXNlcjpwYXNzd29yZDEyMw==\"") true⟩,
  ⟨"tests/client/test_auth.py::test_basic_auth_on_session", "basic auth on client", do
    let c ← Client.new (auth := ("user", "password123")) (transport := MockTransport echo)
    let r ← c.get "https://example.org/"
    eqv "auth" ((field r "headers").contains "Basic dXNlcjpwYXNzd29yZDEyMw==") true⟩,
  ⟨"tests/client/test_auth.py::test_custom_auth", "custom auth", do
    let c ← mockClient echo
    let auth : Auth := FunctionAuth fun r => { r with headers := r.headers.set "Authorization" "Token 123" }
    let r ← c.get "https://example.org/" (auth := auth)
    eqv "auth" ((field r "headers").contains "\"authorization\":\"Token 123\"") true⟩,
  ⟨"tests/client/test_auth.py::test_digest_auth_returns_no_auth_if_no_digest_header_in_response", "digest without challenge", do
    let auth ← DigestAuth "user" "password123"
    let c ← mockClient echo
    let r ← c.get "https://example.org/" (auth := auth)
    allOk [eqv "status" r.statusCode 200, eqv "auth" ((field r "headers").contains "authorization") false,
      eqv "hist" r.history.length 0]⟩,
  ⟨"tests/client/test_auth.py::test_digest_auth", "digest auth", do
    let auth ← DigestAuth "user" "password123"
    let c ← mockClient fun r =>
      if r.headers.contains "authorization" then echo r
      else Response.new 401 (headers := [("www-authenticate",
        "Digest realm=\"httpx@example.org\", qop=\"auth\", nonce=\"ee96edced2a0b43e4869e96ebe27563f369c1205a049d06419bb51d8aeddf3d3\", opaque=\"ee6378f3ee14ebfd2fff54b70a91a7c9390518047f242ab2271380db0e14bda1\", algorithm=MD5")])
    let r ← c.get "https://example.org/" (auth := auth)
    let h := field r "headers"
    allOk [eqv "status" r.statusCode 200, eqv "hist" r.history.length 1,
      eqv "digest" (h.contains "\"authorization\":\"Digest username=\\\"user\\\", realm=\\\"httpx@example.org\\\"") true,
      eqv "fields" ((h.contains "uri=\\\"/\\\"") && (h.contains "algorithm=MD5") && (h.contains "qop=auth") &&
        (h.contains "nc=00000001")) true]⟩,
  ⟨"tests/client/test_auth.py::test_digest_auth_unavailable_streaming_body", "digest malformed challenge", do
    eqv "err" (match parseDigestChallenge "Digest realm=\"x\"" with | .ok _ => "ok" | .error e => e.message)
      "Malformed Digest WWW-Authenticate header"⟩,
  ⟨"tests/test_auth.py::test_digest_auth_rfc_7616_md5", "digest RFC 7616 MD5 vector", do
    let ch := rfcChallenge "MD5"
    let h := digestAuthorization "Mufasa" "Circle of Life" ch "GET" "/dir/index.html" 1 "f2/wE4q74E6zIJEtWaHKaf5wv/H5QzzpXusqGemxURZJ"
    eqv "response" (match h with | .ok s => s.contains "response=\"8ca523f5e9506fed4657c9700eebdbec\"" | .error _ => false) true⟩,
  ⟨"tests/test_auth.py::test_digest_auth_rfc_7616_sha_256", "digest RFC 7616 SHA-256 vector", do
    let ch := rfcChallenge "SHA-256"
    let h := digestAuthorization "Mufasa" "Circle of Life" ch "GET" "/dir/index.html" 1 "f2/wE4q74E6zIJEtWaHKaf5wv/H5QzzpXusqGemxURZJ"
    eqv "response" (match h with | .ok s => s.contains "response=\"753927fa0e85d155564e2e272a28d1802ca10daf4496794697cf8db5856cb6c1\"" | .error _ => false) true⟩,
  ⟨"tests/test_auth.py::test_digest_auth_with_401", "hash vectors", do
    allOk [eqv "md5" (Hash.hex (Hash.md5 "abc".toUTF8)) "900150983cd24fb0d6963f7d28e17f72",
      eqv "sha1" (Hash.hex (Hash.sha1 "abc".toUTF8)) "a9993e364706816aba3e25717850c26c9cd0d89d",
      eqv "sha256" (Hash.hex (Hash.sha256 "abc".toUTF8)) "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
      eqv "sha512" (Hash.hex (Hash.sha512 "abc".toUTF8)).length 128]⟩
]

/-! ## ASGI (`tests/test_asgi.py`) -/

def helloApp : ASGIApp := fun _ _ send => do
  send (.httpResponseStart 200 [("content-type".toUTF8, "text/plain".toUTF8)])
  send (.httpResponseBody "Hello, World!".toUTF8)

def echoPathApp : ASGIApp := fun scope _ send => do
  send (.httpResponseStart 200 [("content-type".toUTF8, "application/json".toUTF8)])
  send (.httpResponseBody (json% {"path": (scope.path), "raw_path": (str scope.rawPath)}).compress.toUTF8)

def echoBodyApp : ASGIApp := fun _ receive send => do
  let mut body := ByteArray.empty
  for _ in [0:100] do
    match ← receive with
    | .httpRequest b more => body := body ++ b; if !more then break
    | _ => break
  send (.httpResponseStart 200 [("content-type".toUTF8, "text/plain".toUTF8)])
  send (.httpResponseBody body)

def raisingApp : ASGIApp := fun _ _ _ => throw (IO.userError "RuntimeError")

def asgiCases : List Case := [
  ⟨"tests/test_asgi.py::test_asgi", "asgi hello", do
    let c ← Client.new (transport := ASGITransport.mk helloApp true "" ("127.0.0.1", 123))
    let r ← c.get "http://www.example.org/"
    allOk [eqv "status" r.statusCode 200, eqv "text" r.text "Hello, World!"]⟩,
  ⟨"tests/test_asgi.py::test_asgi_urlencoded_path", "asgi urlencoded path", do
    let c ← Client.new (transport := ASGITransport.mk echoPathApp true "" ("127.0.0.1", 123))
    let r ← c.get "http://www.example.org/user@example.org"
    eqv "body" r.text "{\"path\":\"/user@example.org\",\"raw_path\":\"/user@example.org\"}"⟩,
  ⟨"tests/test_asgi.py::test_asgi_upload", "asgi upload", do
    let c ← Client.new (transport := ASGITransport.mk echoBodyApp true "" ("127.0.0.1", 123))
    let r ← c.post "http://www.example.org/" (content := "example")
    allOk [eqv "status" r.statusCode 200, eqv "text" r.text "example"]⟩,
  ⟨"tests/test_asgi.py::test_asgi_exc", "asgi exception", do
    let c ← Client.new (transport := ASGITransport.mk raisingApp true "" ("127.0.0.1", 123))
    eqv "err" ((← failure (c.get "http://www.example.org/")).contains "RuntimeError") true⟩,
  ⟨"tests/test_asgi.py::test_asgi_exc_no_raise", "asgi exception without raise", do
    let c ← Client.new (transport := ASGITransport.mk raisingApp false "" ("127.0.0.1", 123))
    eqv "status" (← c.get "http://www.example.org/").statusCode 500⟩,
  ⟨"tests/test_asgi.py::test_asgi_headers", "asgi scope", do
    let t : ASGITransport := { app := helloApp }
    let req ← req! "GET" "http://www.example.org:8000/path?q=1"
    let s := t.scope req
    allOk [eqv "method" s.method "GET", eqv "path" s.path "/path", eqv "query" (str s.queryString) "q=1",
      eqv "server" s.server ("www.example.org", some 8000), eqv "client" s.client ("127.0.0.1", 123),
      eqv "headers" (s.headers.map fun (k, _) => str k) ["host"]]⟩,
  ⟨"tests/test_asgi.py::test_asgi_head", "asgi head drops body", do
    let c ← Client.new (transport := ASGITransport.mk helloApp true "" ("127.0.0.1", 123))
    eqv "content" (← c.head "http://www.example.org/").content.size 0⟩
]

/-! ## HTTP/1.1 on the wire (httpcore `tests/_sync/test_http11.py`) -/

def wire (s : String) : ByteArray := s.toUTF8

def h1Cases : List Case := [
  ⟨"httpcore tests/_sync/test_http11.py::test_http11_connection", "plain response", do
    match H1.parseResponse (H1.ascii "GET") (wire "HTTP/1.1 200 OK\r\nContent-Type: plain/text\r\nContent-Length: 13\r\n\r\nHello, world!") with
    | some (r, rest) =>
      let resp := ofH1Response r
      allOk [eqv "status" resp.statusCode 200, eqv "body" (str r.body) "Hello, world!", eqv "rest" rest.size 0,
        eqv "headers" resp.headers.raw [("Content-Type", "plain/text"), ("Content-Length", "13")]]
    | none => pure false⟩,
  ⟨"httpcore tests/_sync/test_http11.py::test_http11_connection_unread_response", "pipelined responses", do
    let two := wire "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhiHTTP/1.1 204 No Content\r\n\r\n"
    match H1.parseResponse (H1.ascii "GET") two with
    | some (r1, rest) => match H1.parseResponse (H1.ascii "GET") rest with
      | some (r2, rest2) => allOk [eqv "1" (str r1.body) "hi", eqv "2" r2.head.status 204, eqv "rest" rest2.size 0]
      | none => pure false
    | none => pure false⟩,
  ⟨"httpcore tests/_sync/test_http11.py::test_http11_connection_with_remote_protocol_error", "malformed response", do
    eqv "none" (H1.parseResponse (H1.ascii "GET") (wire "Wait, this isn't valid HTTP!")).isNone true⟩,
  ⟨"httpcore tests/_sync/test_http11.py::test_http11_connection_with_incomplete_response", "incomplete response", do
    eqv "none" (H1.parseResponse (H1.ascii "GET") (wire "HTTP/1.1 200 OK\r\nContent-Type: plain/text\r\nContent-Length: 13\r\n\r\nHello, wor")).isNone true⟩,
  ⟨"httpcore tests/_sync/test_http11.py::test_http11_early_hints", "chunked with trailers", do
    match H1.parseResponse (H1.ascii "GET") (wire "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nHello\r\n8;ext=1\r\n, world!\r\n0\r\nX-Trailer: yes\r\n\r\n") with
    | some (r, _) => eqv "body" (str r.body) "Hello, world!"
    | none => pure false⟩,
  ⟨"httpcore tests/_sync/test_http11.py::test_http11_header_sub_100kb", "large header", do
    let v := String.ofList (List.replicate 100000 'x')
    match H1.parseResponse (H1.ascii "GET") (wire s!"HTTP/1.1 200 OK\r\nContent-Length: 0\r\nX-Big: {v}\r\n\r\n") with
    | some (r, _) => eqv "len" ((r.head.fields.getD 1 default).value.length) 100000
    | none => pure false⟩,
  ⟨"httpcore tests/_sync/test_http11.py::test_http11_request_to_incorrect_origin", "request printing", do
    let req ← req! "GET" "http://example.com/path?q=1"
    match toH1Request req with
    | .ok w => eqv "wire" (str (H1.printRequest w)) "GET /path?q=1 HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"
    | .error _ => pure false⟩,
  ⟨"httpcore tests/_sync/test_http11.py::test_http11_connection_with_local_protocol_error", "illegal header value", do
    let req ← req! "GET" "http://example.com/" (headers := [("Host", "\x00")])
    eqv "err" (match toH1Request req with | .ok _ => "ok" | .error e => e.name) "LocalProtocolError"⟩,
  ⟨"httpcore tests/_sync/test_http11.py::test_http11_connection", "head response has no body", do
    match H1.parseResponse (H1.ascii "HEAD") (wire "HTTP/1.1 200 OK\r\nContent-Length: 13\r\n\r\n") with
    | some (r, rest) => allOk [eqv "body" r.body.size 0, eqv "rest" rest.size 0]
    | none => pure false⟩,
  ⟨"httpcore tests/_sync/test_http11.py::test_http11_connection", "close-delimited body", do
    match H1.parseResponse (H1.ascii "GET") (wire "HTTP/1.0 200 OK\r\n\r\nto the end") with
    | some (r, _) => allOk [eqv "body" (str r.body) "to the end", eqv "version" r.head.version.toString "HTTP/1.0"]
    | none => pure false⟩
]

/-! ## h2 golden fixtures

Each line of `tests/upstream/h2_golden.txt` is an outcome of h2's codecs
(hyperframe 6.1.0, hpack 4.2.0, as h2 4.4.1 pins them), produced by
`tests/upstream/h2_golden.py`. Frames hyperframe prints are parsed and
printed back to the same bytes; frames it refuses are refused; hpack's
blocks decode to its header lists and, where hpack sends no Huffman, our
encoder prints the same block; hpack's Huffman codes match ours. -/

def unhex (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    out := out.push (Chars.hexValue cs[2*i]! * 16 + Chars.hexValue cs[2*i+1]!).toUInt8
  return out

def hexOf (b : ByteArray) : String := Hash.hex b

def fieldsLine (fs : List Hpack.HeaderField) : String :=
  ";".intercalate (fs.map fun f => s!"{if f.sensitive then "!" else ""}{hexOf f.name}={hexOf f.value}")

def parseFields (s : String) : List Hpack.HeaderField :=
  if s.isEmpty then [] else (s.splitOn ";").map fun p =>
    let (sens, p) := if p.startsWith "!" then (true, p.drop 1 |>.toString) else (false, p)
    match p.splitOn "=" with
    | [n, v] => ⟨unhex n, unhex v, sens⟩
    | _ => ⟨unhex p, .empty, sens⟩

def goldenPath : System.FilePath := "tests/upstream/h2_golden.txt"

def goldenCase (kind name : String) (run : IO Bool) : Case :=
  { upstream := s!"h2 4.4.1 {kind} (tests/upstream/h2_golden.py)", name := s!"h2 golden {kind}: {name}", run }

def frameGolden (name wire : String) : Case := goldenCase "frame" name do
  let b := unhex wire
  match H2.parseFrame H2.defaultMaxFrameSize b with
  | .done f rest => allOk [eqv "rest" rest.size 0, eqv "printed" (hexOf (H2.printFrame f)) wire]
  | .more => IO.println "      incomplete"; pure false
  | .fail e => IO.println s!"      {e.message}"; pure false

/-- Refused when parsed, or (a zero WINDOW_UPDATE increment, which RFC 9113
6.9 makes a protocol error rather than a malformed frame) by the connection
it arrives on, after the server's SETTINGS. -/
def badFrameGolden (name wire cls : String) : Case := goldenCase "frame" s!"{name} refused ({cls})" do
  match H2.parseFrame H2.defaultMaxFrameSize (unhex wire) with
  | .fail _ => pure true
  | _ =>
    let c := (H2.Conn.new).receive (H2.printFrame (.settings false []) ++ unhex wire)
    if c.error.isSome then pure true else IO.println "      accepted"; pure false

/-- The blocks of one hpack case, decoded in sequence with one decoder and,
without Huffman, encoded in sequence with one encoder. -/
def hpackGolden (name : String) (size : Nat) (huffman : Bool) (blocks : List (String × String)) : Case :=
  goldenCase "hpack" name do
    let mut d : Hpack.Decoder := {}
    let mut e : Hpack.Encoder := if size == 4096 then {} else ({} : Hpack.Encoder).setMaxSize size
    let mut ok := true
    for (block, fields) in blocks do
      match d.decode (unhex block) with
      | .error err => IO.println s!"      {err.message}"; ok := false
      | .ok (fs, d') =>
        d := d'
        ok := (← eqv "fields" (fieldsLine fs) fields) && ok
        let (ours, e') := e.encode (parseFields fields)
        e := e'
        unless huffman do ok := (← eqv "block" (hexOf ours) block) && ok
    pure ok

def badHpackGolden (name maxList block cls : String) : Case := goldenCase "hpack" s!"{name} refused ({cls})" do
  let d : Hpack.Decoder := { maxHeaderListSize := maxList.toNat! }
  match d.decode (unhex block) with
  | .error _ => pure true
  | .ok _ => IO.println "      accepted"; pure false

def huffGolden (input encoded : String) : Case := goldenCase "huffman" s!"{input.take 24}" do
  allOk [eqv "encoded" (hexOf (Huffman.encode (unhex input))) encoded,
    eqv "decoded" ((Huffman.decode (unhex encoded)).map hexOf) (some input)]

def badHuffGolden (encoded outcome : String) : Case := goldenCase "huffman" s!"{encoded} {outcome}" do
  eqv "decoded" (Huffman.decode (unhex encoded)).isSome (outcome == "accepted")

/-- The cases of the fixture file, an hpack case's lines grouped in order. -/
def h2GoldenCases : IO (List Case) := do
  let lines := (← IO.FS.readFile goldenPath).splitOn "\n" |>.filter (!·.isEmpty)
  let mut out : Array Case := #[]
  let mut hp : Option (String × Nat × Bool × Array (String × String)) := none
  for l in lines do
    let fs := l.splitOn "|"
    if let some (n, sz, hf, bs) := hp then
      unless fs[0]! == "hpack" && fs[1]! == n do
        out := out.push (hpackGolden n sz hf bs.toList); hp := none
    match fs with
    | ["frame", n, w] => out := out.push (frameGolden n w)
    | ["badframe", n, w, c] => out := out.push (badFrameGolden n w c)
    | ["hpack", n, sz, hf, b, f] =>
      hp := match hp with
        | some (n', sz', hf', bs) => some (n', sz', hf', bs.push (b, f))
        | none => some (n, sz.toNat!, hf == "1", #[(b, f)])
    | ["badhpack", n, m, b, c] => out := out.push (badHpackGolden n m b c)
    | ["huff", i, e] => out := out.push (huffGolden i e)
    | ["badhuff", e, o] => out := out.push (badHuffGolden e o)
    | _ => throw (IO.userError s!"bad fixture line: {l}")
  if let some (n, sz, hf, bs) := hp then out := out.push (hpackGolden n sz hf bs.toList)
  return out.toList

/-! ## HTTP/2 connection (httpcore `tests/_sync/test_http2.py`, h2 `tests/`)

The sans-I/O connection fed the frames each upstream test sends. A request
that fails is an outcome `error …`; a connection error is `Conn.error`. -/

def hf (n v : String) : Hpack.HeaderField := ⟨n.toUTF8, v.toUTF8, false⟩
def getFields : List Hpack.HeaderField :=
  [hf ":method" "GET", hf ":authority" "example.com", hf ":scheme" "https", hf ":path" "/"]
/-- A block as a fresh `hpack.Encoder()` encodes it. -/
def block (fs : List (String × String)) : ByteArray := (({} : Hpack.Encoder).encode (fs.map fun (n, v) => hf n v)).1
def okHead : List (String × String) := [(":status", "200"), ("content-type", "plain/text")]
def respHeaders (sid : Nat) (fs : List (String × String) := okHead) (endStream := false) : H2.Frame :=
  .headers sid (block fs) endStream true none none
def dataFrame (sid : Nat) (d : String) (endStream := true) : H2.Frame := .data sid d.toUTF8 endStream none
def frames (fs : List H2.Frame) : ByteArray := fs.foldl (fun b f => b ++ H2.printFrame f) .empty
def srvSettings (ps : List (Nat × Nat) := []) : H2.Frame := .settings false ps

def start (c : H2.Conn) (body : ByteArray := .empty) : IO (H2.Conn × Nat) :=
  match c.startRequest getFields body with
  | .ok r => pure r
  | .error e => throw (IO.userError e.message)

def outcomeLine (c : H2.Conn) (sid : Nat) : String := match c.outcome sid with
  | none => "pending"
  | some (.error m) => s!"error {m}"
  | some (.ok (st, _, b)) => s!"{st} {str b}"

def connError (c : H2.Conn) : String := match c.error with
  | some e => s!"{e.code.name}: {e.message}"
  | none => "none"

def errCode (c : H2.Conn) : String := match c.error with
  | some e => e.code.name
  | none => "none"

/-- The frames the client sent, after the preface. -/
def sent (c : H2.Conn) : List H2.Frame := Id.run do
  let mut b := c.out.extract H2.preface.size c.out.size
  let mut out := #[]
  for _ in [0:b.size / 9 + 1] do
    match H2.parseFrame H2.maxFrameSizeLimit b with
    | .done f rest => out := out.push f; b := rest
    | _ => break
  return out.toList

def sentData (c : H2.Conn) : Nat × Bool := (sent c).foldl (fun (n, e) f => match f with
  | .data _ d endStream _ => (n + d.size, e || endStream)
  | _ => (n, e)) (0, false)

/-- A response on stream 1 whose head has an invalid field, after `:status`. -/
def badResponse (field : String × String) : IO String := do
  let (c, sid) ← start H2.Conn.new
  let c := c.receive (frames [srvSettings, respHeaders sid ((":status", "200") :: [field]) true])
  pure (outcomeLine c sid)

def isError (s : String) : Bool := s.startsWith "error"

def h2Up (t : String) : String := s!"h2 tests/{t}"
def coreUp (t : String) : String := s!"httpcore tests/_sync/test_http2.py::{t}"

def h2ConnCases : List Case := [
  ⟨coreUp "test_http2_connection", "a response", do
    let (c, sid) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings, respHeaders sid, dataFrame sid "Hello, world!"])
    allOk [eqv "outcome" (outcomeLine c sid) "200 Hello, world!", eqv "error" (connError c) "none",
      eqv "available" (c.release sid).canStart true]⟩,
  ⟨coreUp "test_http2_connection_post_request", "a request body", do
    let (c, sid) ← start H2.Conn.new "{\"a\": 1}".toUTF8
    let c := c.receive (frames [srvSettings, respHeaders sid, dataFrame sid "Hello, world!"])
    allOk [eqv "sent" (sentData c) (8, true), eqv "outcome" (outcomeLine c sid) "200 Hello, world!"]⟩,
  ⟨coreUp "test_http2_connection_with_remote_protocol_error", "not HTTP/2", do
    let (c, sid) ← start H2.Conn.new
    let c := c.receive "Wait, this isn't valid HTTP!".toUTF8
    allOk [eqv "error" (errCode c) "FRAME_SIZE_ERROR", eqv "outcome" (isError (outcomeLine c sid)) true]⟩,
  ⟨coreUp "test_http2_connection_with_rst_stream", "reset stream, connection reusable", do
    let (c, s1) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings, respHeaders s1, .rstStream s1 8])
    let first := outcomeLine c s1
    let (c, s3) ← start (c.release s1)
    let c := c.receive (frames [respHeaders s3, dataFrame s3 "Hello, world!"])
    allOk [eqv "first" first "error Stream 1 was reset by the server: CANCEL",
      eqv "second" (outcomeLine c s3) "200 Hello, world!"]⟩,
  ⟨coreUp "test_http2_connection_with_goaway", "GOAWAY, connection not reusable", do
    let (c, s1) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings, respHeaders s1, .goaway 0 0 .empty])
    allOk [eqv "first" (outcomeLine c s1) "error Server sent GOAWAY (NO_ERROR); stream 1 was not processed",
      eqv "available" c.canStart false,
      eqv "second" (match c.startRequest getFields .empty with | .ok _ => "ok" | .error e => e.code.name) "REFUSED_STREAM"]⟩,
  ⟨coreUp "test_http2_connection_with_flow_control", "a body larger than the initial window", do
    let (c, sid) ← start H2.Conn.new (ByteArray.mk (Array.replicate 100000 120))
    let before := sentData c
    let ups := (List.range 4).flatMap fun _ => [H2.Frame.windowUpdate 0 10000, .windowUpdate sid 10000]
    let c := c.receive (frames ([srvSettings] ++ ups ++ [respHeaders sid, dataFrame sid "100,000 bytes received"]))
    allOk [eqv "before" before (65535, false), eqv "sent" (sentData c) (100000, true),
      eqv "outcome" (outcomeLine c sid) "200 100,000 bytes received"]⟩,
  ⟨coreUp "test_http2_remote_max_streams_update", "MAX_CONCURRENT_STREAMS updates", do
    let (c, sid) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings [(H2.settingsMaxConcurrentStreams, 1000)], respHeaders sid,
      dataFrame sid "Hello, world!" false])
    let first := (c.peer.maxConcurrentStreams, min c.peer.maxConcurrentStreams c.limits.maxConcurrentStreams)
    let c := c.receive (frames [srvSettings [(H2.settingsMaxConcurrentStreams, 50)], dataFrame sid "Hello, world...again!"])
    allOk [eqv "first" first (1000, 100), eqv "second" c.peer.maxConcurrentStreams 50,
      eqv "outcome" (outcomeLine c sid) "200 Hello, world!Hello, world...again!"]⟩,
  ⟨h2Up "test_invalid_frame_sequences.py::TestInvalidFrameSequences::test_reject_invalid_settings_values", "invalid SETTINGS values", do
    let codes := [(2, 5), (4, 2 ^ 31), (5, 5), (5, 2 ^ 24)].map fun (k, v) =>
      errCode ((H2.Conn.new).receive (frames [srvSettings [(k, v)]]))
    eqv "codes" codes ["PROTOCOL_ERROR", "FLOW_CONTROL_ERROR", "PROTOCOL_ERROR", "PROTOCOL_ERROR"]⟩,
  ⟨h2Up "test_invalid_frame_sequences.py::TestInvalidFrameSequences::test_reject_server_enable_push_updates", "server ENABLE_PUSH 1", do
    eqv "code" (errCode ((H2.Conn.new).receive (frames [srvSettings [(H2.settingsEnablePush, 1)]]))) "PROTOCOL_ERROR"⟩,
  ⟨h2Up "test_invalid_frame_sequences.py::TestInvalidFrameSequences::test_invalid_frame_headers_are_protocol_errors", "HEADERS on stream 0", do
    let (c, _) ← start H2.Conn.new
    let w := H2.printFrame (respHeaders 1)
    let w := ByteArray.mk ((w.extract 0 9).data.map fun b => if b == 1 then 0 else b) ++ w.extract 9 w.size
    eqv "code" (errCode (c.receive (frames [srvSettings] ++ w))) "PROTOCOL_ERROR"⟩,
  ⟨h2Up "test_invalid_frame_sequences.py::TestInvalidFrameSequences::test_data_before_headers", "DATA before HEADERS", do
    let (c, sid) ← start H2.Conn.new
    eqv "error" (connError (c.receive (frames [srvSettings, dataFrame sid "hello" false])))
      "PROTOCOL_ERROR: DATA before HEADERS"⟩,
  ⟨h2Up "test_invalid_frame_sequences.py::TestInvalidFrameSequences::test_prevent_continuation_dos", "CONTINUATION flood", do
    let (c, sid) ← start H2.Conn.new
    let conts := (List.range 70).map fun _ => H2.Frame.continuation sid (ByteArray.mk #[0x40, 1, 120, 1, 120]) false
    let c := c.receive (frames ([srvSettings, .headers sid (block [(":status", "200")]) false false none none] ++ conts))
    eqv "error" (connError c) "PROTOCOL_ERROR: Too many continuation frames received."⟩,
  ⟨h2Up "test_informational_responses.py::TestReceivingInformationalResponses::test_single_informational_response", "100 then 200", do
    let (c, sid) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings, respHeaders sid [(":status", "100")], respHeaders sid, dataFrame sid "ok"])
    eqv "outcome" (outcomeLine c sid) "200 ok"⟩,
  ⟨h2Up "test_informational_responses.py::TestReceivingInformationalResponses::test_receiving_multiple_informational_responses", "several 1xx", do
    let (c, sid) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings, respHeaders sid [(":status", "100")], respHeaders sid [(":status", "103")],
      respHeaders sid, dataFrame sid "ok"])
    eqv "outcome" (outcomeLine c sid) "200 ok"⟩,
  ⟨h2Up "test_informational_responses.py::TestReceivingInformationalResponses::test_receive_provisional_response_with_end_stream", "1xx with END_STREAM", do
    let (c, _) ← start H2.Conn.new
    eqv "code" (errCode (c.receive (frames [srvSettings, respHeaders 1 [(":status", "100")] true]))) "PROTOCOL_ERROR"⟩,
  ⟨h2Up "test_invalid_headers.py::TestInvalidFrameSequences::test_headers_event", "invalid response fields", do
    let bad := [("Uppercase", "name"), ("connection", "close"), ("proxy-connection", "close"),
      ("keep-alive", "close"), ("transfer-encoding", "gzip"), ("upgrade", "super-protocol/1.1"), ("te", "chunked"),
      (" name", "name with leading space"), ("name ", "name with trailing space"),
      ("name", " value with leading space"), ("name", "value with trailing space "),
      ("illegal:characters", "value"), ("illegal-\r-characters", "value"), ("illegal-\n-characters", "value"),
      ("illegal-\x00-characters", "value"), ("illegal-\x01-characters", "value"),
      ("illegal-characters", "some \r value"), ("illegal-characters", "some \n value"),
      ("illegal-characters", "some \x00 value"), (":status", "200"), ("", "empty name")]
    let outs ← bad.mapM badResponse
    let wrong := (bad.zip outs).filter fun (_, o) => !isError o
    eqv "accepted" (wrong.map (·.1.1)) []⟩,
  ⟨h2Up "test_invalid_headers.py::TestInvalidFrameSequences::test_headers_event", "late pseudo-header", do
    let (c, sid) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings, respHeaders sid [(":status", "200"), ("x", "1"), (":late", "pseudo-header")] true])
    eqv "outcome" (isError (outcomeLine c sid)) true⟩,
  ⟨h2Up "test_invalid_headers.py::TestInvalidFrameSequences::test_te_trailers_is_valid", "te: trailers", do
    let (c, sid) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings, respHeaders sid [(":status", "200"), ("te", "trailers")] true])
    eqv "outcome" (outcomeLine c sid) "200 "⟩,
  ⟨h2Up "test_invalid_headers.py::TestInvalidFrameSequences::test_pseudo_headers_rejected_in_trailer", "pseudo-header in trailers", do
    let (c, sid) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings, respHeaders sid, dataFrame sid "x" false,
      respHeaders sid [(":status", "200")] true])
    eqv "outcome" (isError (outcomeLine c sid)) true⟩,
  ⟨h2Up "test_invalid_headers.py::TestOversizedHeaders::test_hpack_bomb_response", "HPACK bomb", do
    let (c, sid) ← start H2.Conn.new
    let big := Hpack.encodeReps [.indexed 8, .literal .incremental (.lit "x-bomb".toUTF8) (ByteArray.mk (Array.replicate 4000 97))]
    let blk := (List.range 20).foldl (fun b _ => b ++ Hpack.encodeReps [.indexed 62]) big
    let c := c.receive (frames [srvSettings, .headers sid blk true true none none])
    eqv "code" (errCode c) "COMPRESSION_ERROR"⟩,
  ⟨h2Up "test_flow_control_window.py::TestFlowControl::test_reject_increasing_connection_window_too_far", "connection window overflow", do
    eqv "code" (errCode ((H2.Conn.new).receive (frames [srvSettings, .windowUpdate 0 (2 ^ 31 - 65535)]))) "FLOW_CONTROL_ERROR"⟩,
  ⟨h2Up "test_flow_control_window.py::TestFlowControl::test_reject_increasing_stream_window_too_far", "stream window overflow resets the stream", do
    let (c, sid) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings, .windowUpdate sid (2 ^ 31 - 65535)])
    let rst := (sent c).any fun f => match f with | .rstStream 1 3 => true | _ => false
    allOk [eqv "error" (connError c) "none", eqv "outcome" (isError (outcomeLine c sid)) true, eqv "rst" rst true]⟩,
  ⟨h2Up "test_flow_control_window.py::TestFlowControl::test_reject_overlarge_stream_window_settings", "SETTINGS overflows a stream window", do
    let (c, sid) ← start H2.Conn.new
    let c := c.receive (frames [srvSettings, .windowUpdate sid (2 ^ 31 - 1 - 65535), srvSettings [(H2.settingsInitialWindowSize, 65536)]])
    eqv "code" (errCode c) "FLOW_CONTROL_ERROR"⟩,
  ⟨h2Up "test_flow_control_window.py::TestFlowControl::test_reject_overlarge_conn_window_settings", "SETTINGS leaves the connection window", do
    let c := (H2.Conn.new).receive (frames [srvSettings, .windowUpdate 0 (2 ^ 31 - 1 - 65535), srvSettings [(H2.settingsInitialWindowSize, 65536)]])
    eqv "error" (connError c) "none"⟩,
  ⟨h2Up "test_basic_logic.py::TestBasicClient::test_receiving_ping_frame", "PING is acknowledged", do
    let c := (H2.Conn.new).receive (frames [srvSettings, .ping false "12345678".toUTF8])
    eqv "ack" ((sent c).any fun f => match f with | .ping true d => d == "12345678".toUTF8 | _ => false) true⟩,
  ⟨h2Up "test_basic_logic.py::TestBasicClient::test_acknowledging_settings", "SETTINGS is acknowledged", do
    let c := (H2.Conn.new).receive (frames [srvSettings [(H2.settingsMaxConcurrentStreams, 10)]])
    eqv "ack" ((sent c).any fun f => match f with | .settings true [] => true | _ => false) true⟩,
  ⟨h2Up "test_basic_logic.py::TestBasicClient::test_cannot_receive_pushed_stream_when_enable_push_is_0", "PUSH_PROMISE refused", do
    let (c, sid) ← start H2.Conn.new
    eqv "code" (errCode (c.receive (frames [srvSettings, .pushPromise sid 2 (block okHead) true none]))) "PROTOCOL_ERROR"⟩
]

def cases : List Case :=
  urlCases ++ headerCases ++ cookieCases ++ modelCases ++ clientCases ++ redirectCases ++ authCases ++ asgiCases ++ h1Cases ++ h2ConnCases

def main : IO UInt32 := do
  let cases := cases ++ (← h2GoldenCases)
  let mut failures := 0
  for c in cases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length} cases, {failures} failing"
  return if failures == 0 then 0 else 1
