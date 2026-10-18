import LeanHttpx.RepoImpl.H1Body

/-!
# Specifications: HTTP/1.1 messages

The wire round trips, stated in `Prop`, each on any continuation of the
buffer. Proved in `Proofs/H1.lean`.
-/

namespace LeanHttpx.Spec

open H1

/-- A valid request parses back from its bytes, leaving what follows. -/
def RequestPrintParse : Prop :=
  ∀ (r : H1.Request) (rest : ByteArray), r.ok = true → parseRequest (printRequest r ++ rest) = some (r, rest)

/-- A valid response parses back from its bytes, leaving what follows. -/
def ResponseParsePrint : Prop :=
  ∀ (m : List UInt8) (r : H1.Response) (rest : ByteArray), r.ok m = true →
    parseResponse m (printResponse m r ++ rest) = some (r, rest)

/-- Non-empty chunks decode back from their chunked coding. -/
def ChunkedDecodeEncode : Prop :=
  ∀ (cs : List ByteArray) (rest : ByteArray), (∀ c ∈ cs, 0 < c.size) →
    decodeChunked (encodeChunked cs ++ rest) = some (cs, rest)

end LeanHttpx.Spec
