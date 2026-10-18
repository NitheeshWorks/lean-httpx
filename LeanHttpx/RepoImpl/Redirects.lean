import LeanHttpx.RepoImpl.Models

/-!
# Redirects (`httpx/_client.py`, `BaseClient._build_redirect_request`)

The redirect logic as pure functions, and the redirect loop over any monad:

* `redirectMethod`: 303, and 302 for anything but `HEAD`, become `GET`; a
  301 `POST` becomes `GET`; 307 and 308 keep the method (RFC 9110 section
  15.4, with the browser behaviour httpx follows).
* `redirectUrl`: the `Location`, resolved against the request URL, keeping
  the request's fragment when the location has none.
* `redirectHeaders`: drop `Authorization` when the origin changes (unless it
  is an upgrade to `https` on the same host), re-point `Host`, drop the body
  headers when the method became `GET`, and always drop `Cookie` (the jar
  re-sets it for the new URL).
* `sendHandlingRedirects`: follow at most `maxRedirects` redirects; one
  more is `TooManyRedirects`. Its result type carries the bound.
-/

namespace LeanHttpx

/-- The port a URL connects to: explicit, or the scheme default. -/
def portOrDefault (u : URL) : Option Nat :=
  match u.port with
  | some p => some p
  | none => if u.scheme == "http" then some 80 else if u.scheme == "https" then some 443 else none

/-- Same scheme, host and port (`_same_origin`). -/
def sameOrigin (a b : URL) : Bool :=
  a.scheme == b.scheme && a.host == b.host && portOrDefault a == portOrDefault b

/-- `location` is the `https` upgrade of `url` on the same host
(`_is_https_redirect`). -/
def isHttpsRedirect (url location : URL) : Bool :=
  url.host == location.host && url.scheme == "http" && portOrDefault url == some 80 &&
    location.scheme == "https" && portOrDefault location == some 443

/-- **The method of a redirected request** (`_redirect_method`). -/
def redirectMethod (status : Nat) (method : String) : String :=
  if status == 303 && method != "HEAD" then "GET"
  else if status == 302 && method != "HEAD" then "GET"
  else if status == 301 && method == "POST" then "GET"
  else method

/-- The URL to follow (`_redirect_url`). -/
def redirectUrl (request : Request) (response : Response) : Except HTTPError URL := do
  let location := (response.headers.get? "Location").getD ""
  let url ← match URL.parse location with
    | .ok u => pure u
    | .error e => throw (.remoteProtocolError s!"Invalid URL in location header: {e.message}.")
  let url ← if !url.scheme.isEmpty && url.host.isEmpty then
      (url.copyWith (host := request.url.host)).mapError fun e => .invalidURL e.message
    else pure url
  let url ← if url.isRelativeUrl then
      (request.url.join url.toString).mapError fun e => .invalidURL e.message
    else pure url
  if !request.url.fragment.isEmpty && url.fragment.isEmpty then
    (url.copyWith (fragment := request.url.ref.fragment)).mapError fun e => .invalidURL e.message
  else pure url

/-- The headers of a redirected request (`_redirect_headers`). -/
def redirectHeaders (request : Request) (url : URL) (method : String) : Headers :=
  let h := request.headers
  let h := if !sameOrigin url request.url then
      let h := if !isHttpsRedirect request.url url then h.delete "Authorization" else h
      h.set "Host" url.netloc
    else h
  let h := if method != request.method && method == "GET" then
      (h.delete "Content-Length").delete "Transfer-Encoding" else h
  h.delete "Cookie"

/-- **The redirected request** (`_build_redirect_request`): new method, URL
and headers; the body is kept unless the method became `GET`; the client's
cookies for the new URL are attached. -/
def buildRedirectRequest (request : Request) (response : Response) (cookies : Cookies) (now : Int) :
    Except HTTPError Request := do
  let method := redirectMethod response.statusCode request.method
  let url ← redirectUrl request response
  let headers := redirectHeaders request url method
  let headers := match cookies.cookieHeader url now with
    | some v => if headers.contains "Cookie" then headers else headers.set "Cookie" v
    | none => headers
  let content := if method != request.method && method == "GET" then ByteArray.empty else request.content
  pure { method, url, headers, content, timeout := request.timeout }

/-- A response whose redirect history is within the limit. -/
abbrev Bounded (maxRedirects : Nat) := {r : Response // r.history.length ≤ maxRedirects}

/-- The redirect loop with `budget` requests left (`history.length + budget
= maxRedirects + 1`). -/
def redirectLoop {m : Type → Type} [Monad m] (send : Request → m (Except HTTPError Response))
    (jar : m (Cookies × Int)) (follow : Bool) (maxRedirects : Nat) :
    (budget : Nat) → (request : Request) → (history : List Response) →
    history.length + budget = maxRedirects + 1 → m (Except HTTPError (Bounded maxRedirects))
  | 0, request, _, _ => pure (.error (.tooManyRedirects "Exceeded maximum allowed redirects." request))
  | b + 1, request, history, h => do
    match ← send request with
    | .error e => pure (.error e)
    | .ok response =>
      let response := { response with history }
      if !response.hasRedirectLocation then
        pure (.ok ⟨response, by simp [response]; omega⟩)
      else
        let (cookies, now) ← jar
        match buildRedirectRequest request response cookies now with
        | .error e => pure (.error e)
        | .ok next =>
          if follow then
            redirectLoop send jar follow maxRedirects b next (history ++ [response]) (by simp; omega)
          else pure (.ok ⟨{ response with nextRequest := some next }, by simp [response]; omega⟩)

/-- **`_send_handling_redirects`**: send, and while the response redirects
(and `follow` is set) send the redirected request; more than
`maxRedirects` redirects is `TooManyRedirects`. `history` holds responses
already in the chain (from authentication), which count toward the limit.
`jar` reads the client's current cookies and clock. -/
def sendHandlingRedirects {m : Type → Type} [Monad m] (send : Request → m (Except HTTPError Response))
    (jar : m (Cookies × Int)) (follow : Bool) (maxRedirects : Nat) (request : Request)
    (history : List Response := []) : m (Except HTTPError (Bounded maxRedirects)) :=
  if h : history.length ≤ maxRedirects then
    redirectLoop send jar follow maxRedirects (maxRedirects + 1 - history.length) request history (by omega)
  else pure (.error (.tooManyRedirects "Exceeded maximum allowed redirects." request))

end LeanHttpx
