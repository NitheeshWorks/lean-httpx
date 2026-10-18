/-!
# Status codes (RFC 9110 section 15; `httpx.codes`)

The registered status codes with their reason phrases, as `httpx.codes`
lists them, and the class predicates of `Response`.
-/

namespace LeanHttpx

namespace codes

/-- `100 Continue`. -/
abbrev CONTINUE : Nat := 100
/-- `101 Switching Protocols`. -/
abbrev SWITCHING_PROTOCOLS : Nat := 101
/-- `102 Processing`. -/
abbrev PROCESSING : Nat := 102
/-- `103 Early Hints`. -/
abbrev EARLY_HINTS : Nat := 103
/-- `200 OK`. -/
abbrev OK : Nat := 200
/-- `201 Created`. -/
abbrev CREATED : Nat := 201
/-- `202 Accepted`. -/
abbrev ACCEPTED : Nat := 202
/-- `203 Non-Authoritative Information`. -/
abbrev NON_AUTHORITATIVE_INFORMATION : Nat := 203
/-- `204 No Content`. -/
abbrev NO_CONTENT : Nat := 204
/-- `205 Reset Content`. -/
abbrev RESET_CONTENT : Nat := 205
/-- `206 Partial Content`. -/
abbrev PARTIAL_CONTENT : Nat := 206
/-- `207 Multi-Status`. -/
abbrev MULTI_STATUS : Nat := 207
/-- `208 Already Reported`. -/
abbrev ALREADY_REPORTED : Nat := 208
/-- `226 IM Used`. -/
abbrev IM_USED : Nat := 226
/-- `300 Multiple Choices`. -/
abbrev MULTIPLE_CHOICES : Nat := 300
/-- `301 Moved Permanently`. -/
abbrev MOVED_PERMANENTLY : Nat := 301
/-- `302 Found`. -/
abbrev FOUND : Nat := 302
/-- `303 See Other`. -/
abbrev SEE_OTHER : Nat := 303
/-- `304 Not Modified`. -/
abbrev NOT_MODIFIED : Nat := 304
/-- `305 Use Proxy`. -/
abbrev USE_PROXY : Nat := 305
/-- `307 Temporary Redirect`. -/
abbrev TEMPORARY_REDIRECT : Nat := 307
/-- `308 Permanent Redirect`. -/
abbrev PERMANENT_REDIRECT : Nat := 308
/-- `400 Bad Request`. -/
abbrev BAD_REQUEST : Nat := 400
/-- `401 Unauthorized`. -/
abbrev UNAUTHORIZED : Nat := 401
/-- `402 Payment Required`. -/
abbrev PAYMENT_REQUIRED : Nat := 402
/-- `403 Forbidden`. -/
abbrev FORBIDDEN : Nat := 403
/-- `404 Not Found`. -/
abbrev NOT_FOUND : Nat := 404
/-- `405 Method Not Allowed`. -/
abbrev METHOD_NOT_ALLOWED : Nat := 405
/-- `406 Not Acceptable`. -/
abbrev NOT_ACCEPTABLE : Nat := 406
/-- `407 Proxy Authentication Required`. -/
abbrev PROXY_AUTHENTICATION_REQUIRED : Nat := 407
/-- `408 Request Timeout`. -/
abbrev REQUEST_TIMEOUT : Nat := 408
/-- `409 Conflict`. -/
abbrev CONFLICT : Nat := 409
/-- `410 Gone`. -/
abbrev GONE : Nat := 410
/-- `411 Length Required`. -/
abbrev LENGTH_REQUIRED : Nat := 411
/-- `412 Precondition Failed`. -/
abbrev PRECONDITION_FAILED : Nat := 412
/-- `413 Request Entity Too Large`. -/
abbrev REQUEST_ENTITY_TOO_LARGE : Nat := 413
/-- `414 Request-URI Too Long`. -/
abbrev REQUEST_URI_TOO_LONG : Nat := 414
/-- `415 Unsupported Media Type`. -/
abbrev UNSUPPORTED_MEDIA_TYPE : Nat := 415
/-- `416 Requested Range Not Satisfiable`. -/
abbrev REQUESTED_RANGE_NOT_SATISFIABLE : Nat := 416
/-- `417 Expectation Failed`. -/
abbrev EXPECTATION_FAILED : Nat := 417
/-- `418 I'm a teapot`. -/
abbrev IM_A_TEAPOT : Nat := 418
/-- `421 Misdirected Request`. -/
abbrev MISDIRECTED_REQUEST : Nat := 421
/-- `422 Unprocessable Entity`. -/
abbrev UNPROCESSABLE_ENTITY : Nat := 422
/-- `423 Locked`. -/
abbrev LOCKED : Nat := 423
/-- `424 Failed Dependency`. -/
abbrev FAILED_DEPENDENCY : Nat := 424
/-- `425 Too Early`. -/
abbrev TOO_EARLY : Nat := 425
/-- `426 Upgrade Required`. -/
abbrev UPGRADE_REQUIRED : Nat := 426
/-- `428 Precondition Required`. -/
abbrev PRECONDITION_REQUIRED : Nat := 428
/-- `429 Too Many Requests`. -/
abbrev TOO_MANY_REQUESTS : Nat := 429
/-- `431 Request Header Fields Too Large`. -/
abbrev REQUEST_HEADER_FIELDS_TOO_LARGE : Nat := 431
/-- `451 Unavailable For Legal Reasons`. -/
abbrev UNAVAILABLE_FOR_LEGAL_REASONS : Nat := 451
/-- `500 Internal Server Error`. -/
abbrev INTERNAL_SERVER_ERROR : Nat := 500
/-- `501 Not Implemented`. -/
abbrev NOT_IMPLEMENTED : Nat := 501
/-- `502 Bad Gateway`. -/
abbrev BAD_GATEWAY : Nat := 502
/-- `503 Service Unavailable`. -/
abbrev SERVICE_UNAVAILABLE : Nat := 503
/-- `504 Gateway Timeout`. -/
abbrev GATEWAY_TIMEOUT : Nat := 504
/-- `505 HTTP Version Not Supported`. -/
abbrev HTTP_VERSION_NOT_SUPPORTED : Nat := 505
/-- `506 Variant Also Negotiates`. -/
abbrev VARIANT_ALSO_NEGOTIATES : Nat := 506
/-- `507 Insufficient Storage`. -/
abbrev INSUFFICIENT_STORAGE : Nat := 507
/-- `508 Loop Detected`. -/
abbrev LOOP_DETECTED : Nat := 508
/-- `510 Not Extended`. -/
abbrev NOT_EXTENDED : Nat := 510
/-- `511 Network Authentication Required`. -/
abbrev NETWORK_AUTHENTICATION_REQUIRED : Nat := 511

/-- The registered codes and their phrases. -/
def table : List (Nat × String) := [
  (100, "Continue"),
  (101, "Switching Protocols"),
  (102, "Processing"),
  (103, "Early Hints"),
  (200, "OK"),
  (201, "Created"),
  (202, "Accepted"),
  (203, "Non-Authoritative Information"),
  (204, "No Content"),
  (205, "Reset Content"),
  (206, "Partial Content"),
  (207, "Multi-Status"),
  (208, "Already Reported"),
  (226, "IM Used"),
  (300, "Multiple Choices"),
  (301, "Moved Permanently"),
  (302, "Found"),
  (303, "See Other"),
  (304, "Not Modified"),
  (305, "Use Proxy"),
  (307, "Temporary Redirect"),
  (308, "Permanent Redirect"),
  (400, "Bad Request"),
  (401, "Unauthorized"),
  (402, "Payment Required"),
  (403, "Forbidden"),
  (404, "Not Found"),
  (405, "Method Not Allowed"),
  (406, "Not Acceptable"),
  (407, "Proxy Authentication Required"),
  (408, "Request Timeout"),
  (409, "Conflict"),
  (410, "Gone"),
  (411, "Length Required"),
  (412, "Precondition Failed"),
  (413, "Request Entity Too Large"),
  (414, "Request-URI Too Long"),
  (415, "Unsupported Media Type"),
  (416, "Requested Range Not Satisfiable"),
  (417, "Expectation Failed"),
  (418, "I'm a teapot"),
  (421, "Misdirected Request"),
  (422, "Unprocessable Entity"),
  (423, "Locked"),
  (424, "Failed Dependency"),
  (425, "Too Early"),
  (426, "Upgrade Required"),
  (428, "Precondition Required"),
  (429, "Too Many Requests"),
  (431, "Request Header Fields Too Large"),
  (451, "Unavailable For Legal Reasons"),
  (500, "Internal Server Error"),
  (501, "Not Implemented"),
  (502, "Bad Gateway"),
  (503, "Service Unavailable"),
  (504, "Gateway Timeout"),
  (505, "HTTP Version Not Supported"),
  (506, "Variant Also Negotiates"),
  (507, "Insufficient Storage"),
  (508, "Loop Detected"),
  (510, "Not Extended"),
  (511, "Network Authentication Required")
]

/-- The reason phrase of a code, `""` if it is not registered
(`codes.get_reason_phrase`). -/
def getReasonPhrase (code : Nat) : String :=
  match table.find? (·.1 == code) with
  | some (_, p) => p
  | none => ""

/-- 1xx. -/
def isInformational (c : Nat) : Bool := 100 ≤ c && c ≤ 199
/-- 2xx. -/
def isSuccess (c : Nat) : Bool := 200 ≤ c && c ≤ 299
/-- 3xx. -/
def isRedirect (c : Nat) : Bool := 300 ≤ c && c ≤ 399
/-- 4xx. -/
def isClientError (c : Nat) : Bool := 400 ≤ c && c ≤ 499
/-- 5xx. -/
def isServerError (c : Nat) : Bool := 500 ≤ c && c ≤ 599
/-- 4xx or 5xx. -/
def isError (c : Nat) : Bool := 400 ≤ c && c ≤ 599

end codes

end LeanHttpx
