import LeanHttpx.RepoImpl.H1
import LeanHttpx.RepoImpl.Lists

/-!
# Chunked bodies and the message codecs

The chunked coding as a lawful codec of chunk lists (`chunks`), and the
request and response codecs: a head, then the body codec its framing selects
(`Codec.sigma`).

The laws of the three hand-written chunk parsers are proved here from
`Keel.Parse` equations; everything else is a `Keel.Codec` combinator.
-/

namespace LeanHttpx

namespace H1

open Keel Keel.Parser

variable {ε : Type} [ParseError ε]

theorem crlf_stops_hex : StopsAt isHexByte (crlf ++ r) := stopsAt_cons (by decide)

theorem parse_chunkSizeLine (n : Nat) (hn : n < maxChunkSize) (r : List UInt8) :
    (chunkSizeLine : Parser UInt8 ε Nat).parse (hexDigits n ++ (crlf ++ r)) = .ok n r := by
  have hl : ¬ (hexDigits n).length > maxChunkDigits := by
    have := hexDigits_length_le 19 n hn; simp [maxChunkDigits]; omega
  have h1 := takeWhile_append_stop (hexDigits_isHex n) (crlf_stops_hex (r := r))
  have h2 := dropWhile_append_stop (hexDigits_isHex n) (crlf_stops_hex (r := r))
  have hne : (hexDigits n).isEmpty = false := by simpa using hexDigits_ne_nil n
  have h3 : (crlf ++ r).takeWhile (· != CR) = [] := by simp [crlf]
  have h4 : (crlf ++ r).dropWhile (· != CR) = crlf ++ r := by simp [crlf]
  simp only [chunkSizeLine, parse_bind, parse_takeWhile, h1, h2, Reply.bind_ok, hne, hl,
    decide_false, Bool.or_false,
    Bool.false_eq_true, ite_false, h3, h4, List.isEmpty_nil, Bool.true_or, ite_true,
    parse_seqRight, parse_lit, parse_pure, hexValue_hexDigits]

theorem parse_chunk (d : ByteArray) (hd : 0 < d.size) (hm : d.size < maxChunkSize) (r : List UInt8) :
    (chunk : Parser UInt8 ε ByteArray).parse (encodeChunk d ++ r) = .ok d r := by
  have hn : d.size ≠ 0 := by omega
  have e : encodeChunk d ++ r = hexDigits d.size ++ (crlf ++ (d.data.toList ++ (crlf ++ r))) := by
    simp [encodeChunk, List.append_assoc]
  rw [e]
  simp only [chunk, parse_attempt, parse_bind, parse_chunkSizeLine _ hm, Reply.bind_ok, hn,
    ite_false, parse_takeBytes, parse_seqRight, parse_lit, parse_pure]

theorem parse_chunk_last (r : List UInt8) :
    (chunk : Parser UInt8 ε ByteArray).parse (lastChunkBytes ++ r) =
      .error ParseError.unexpected (lastChunkBytes ++ r) := by
  have e : lastChunkBytes ++ r = hexDigits 0 ++ (crlf ++ (crlf ++ r)) := by
    simp [lastChunkBytes, List.append_assoc]
  rw [e]
  simp only [chunk, parse_attempt, parse_bind, parse_chunkSizeLine 0 (by decide), Reply.bind_ok, ite_true,
    parse_fail]

theorem parse_lastChunk (r : List UInt8) :
    (lastChunk : Parser UInt8 ε Unit).parse (lastChunkBytes ++ r) = .ok () r := by
  have e : lastChunkBytes ++ r = hexDigits 0 ++ (crlf ++ (crlf ++ r)) := by
    simp [lastChunkBytes, List.append_assoc]
  have hm : (Parser.many (notFollowedBy (Parser.lit crlf) *> field.parser) : Parser UInt8 ε (List Field)).parse
      (crlf ++ r) = .ok [] (crlf ++ r) := by
    rw [parse_many]
    simp [parse_notFollowedBy]
  rw [e]
  simp only [lastChunk, parse_bind, parse_chunkSizeLine 0 (by decide), Reply.bind_ok, ne_eq, not_true_eq_false,
    ite_false, hm, parse_lit]

/-- **Chunked transfer coding**: a list of non-empty chunks, then the last
chunk. The decoder also takes chunk extensions and trailer fields, which it
ignores (the encoder writes neither). -/
def chunks : Codec UInt8 (List ByteArray) where
  encode cs := cs.flatMap encodeChunk ++ lastChunkBytes
  parser := do
    let cs ← Parser.many chunk
    lastChunk
    pure cs
  valid cs := ∀ c ∈ cs, 0 < c.size ∧ c.size < maxChunkSize
  follow _ := True
  parse_encode := @fun ε _ cs r hv _ => by
    have hreads : ∀ xs : List ByteArray, (∀ c ∈ xs, 0 < c.size ∧ c.size < maxChunkSize) →
        (chunk : Parser UInt8 ε ByteArray).ReadsAll encodeChunk (lastChunkBytes ++ r) xs := by
      intro xs
      induction xs with
      | nil => intro _; simp [Parser.ReadsAll, parse_chunk_last, Reply.rest]
      | cons x xs ih =>
        intro h
        refine ⟨by simp [encodeChunk, crlf], ?_, ih fun c hc => h c (by simp [hc])⟩
        rw [← List.append_assoc, List.append_assoc (encodeChunk x)]
        exact parse_chunk x (h x (by simp)).1 (h x (by simp)).2 _
    rw [List.append_assoc, parse_bind, Parser.parse_many_flatMap _ _ _ cs (hreads cs hv)]
    simp [parse_lastChunk]

/-- Concatenate chunks. -/
def concatChunks (cs : List ByteArray) : ByteArray := cs.foldl (· ++ ·) ByteArray.empty

/-- A body as chunks: one chunk, or none for an empty body. -/
def toChunks (b : ByteArray) : List ByteArray := if b.size = 0 then [] else [b]

theorem concatChunks_toChunks (b : ByteArray) : concatChunks (toChunks b) = b := by
  unfold toChunks concatChunks
  split
  · rename_i h
    obtain ⟨d⟩ := b
    simp only [List.foldl_nil]
    have : d.size = 0 := h
    have : d = #[] := by simpa using this
    subst this; rfl
  · simp

/-- A chunked body: the chunks concatenated. -/
def chunkedBody : Codec UInt8 ByteArray := chunks.map concatChunks toChunks concatChunks_toChunks

/-- Read every remaining byte. -/
def takeRest : Parser UInt8 ε ByteArray where
  run s i := .ok (buildBytes (fun k => (Input.get? s (i + k)).getD 0) (Input.size s - i)) (i + (Input.size s - i))
  run_eq s i := by
    have hL : Input.size (Input.rest s i) - 0 = Input.size s - i := by
      rw [Input.size_list, Input.length_rest, Nat.sub_zero]
    have hf : (fun k => (Input.get? (Input.rest s i) (0 + k)).getD 0) =
        (fun k => (Input.get? s (i + k)).getD 0) := by
      funext k; rw [Nat.zero_add, Input.get?_list, Input.get?_rest]
    show Result.ok _ _ = Result.shift i (Result.ok _ _)
    rw [hL, hf]; simp [Nat.add_comm]
  pos_le l := by show Result.pos (Result.ok _ _) ≤ _; simp

/-- A body that runs to the end of the input. Decode only: no value is
printed this way (`valid` is `False`), since a printed message must say
where it ends. -/
def toEnd : Codec UInt8 ByteArray where
  encode _ := []
  parser := takeRest
  valid _ := False
  follow _ := True
  parse_encode _ _ hv _ := hv.elim

/-- The body codec a framing selects. -/
def bodyCodec : Framing → Codec UInt8 ByteArray
  | .none => Codec.pure ByteArray.empty
  | .length n => Codec.bytesN n
  | .chunked => chunkedBody
  | .close => toEnd
  | .invalid => Codec.fail

/-- **The request codec**: a head, then the body its framing selects. -/
def request : Codec UInt8 Request :=
  (Codec.sigma requestHead fun h => bodyCodec (requestFraming h)).map
    (fun p => ⟨p.1, p.2⟩) (fun r => ⟨r.head, r.body⟩) fun _ => rfl

/-- **The response codec**, for a request with the given method. -/
def response (requestMethod : List UInt8) : Codec UInt8 Response :=
  (Codec.sigma responseHead fun h => bodyCodec (responseFraming requestMethod h)).map
    (fun p => ⟨p.1, p.2⟩) (fun r => ⟨r.head, r.body⟩) fun _ => rfl

end H1

end LeanHttpx

namespace LeanHttpx

namespace H1

/-! ## The wire functions -/

/-- The bytes of a request message. -/
def printRequest (r : Request) : ByteArray := request.encodeBytes r

/-- Read a request message from the start of `b`: the message and the bytes
after it. -/
def parseRequest (b : ByteArray) : Option (Request × ByteArray) := request.decodeBytes b

/-- The bytes of a response message. -/
def printResponse (requestMethod : List UInt8) (r : Response) : ByteArray :=
  (response requestMethod).encodeBytes r

/-- Read a response message, to a request with the given method. -/
def parseResponse (requestMethod : List UInt8) (b : ByteArray) : Option (Response × ByteArray) :=
  (response requestMethod).decodeBytes b

/-- **Read a response from a buffer**, as `parseResponse` does, by the same
codecs and at the same positions, except that a `Content-Length` body is
taken as one slice of the buffer (`ByteArray.extract`, a copy of the bytes)
rather than byte by byte. `readResponse_eq_parseResponse` proves the two
are the same function; the transport uses this one. -/
def readResponse (requestMethod : List UInt8) (b : ByteArray) : Option (Response × ByteArray) :=
  match (responseHead.parser (ε := Unit)).run b 0 with
  | .ok h j =>
    match responseFraming requestMethod h with
    | .length n =>
      if b.size - j < n then none else some (⟨h, b.extract j (j + n)⟩, b.extract (j + n) b.size)
    | f =>
      match ((bodyCodec f).parser (ε := Unit)).run b j with
      | .ok body k => some (⟨h, body⟩, b.extract k b.size)
      | .error _ _ => none
  | .error _ _ => none

/-- **Read a chunked body from a buffer**, from position `pos`: the data
and the position after the last chunk. It runs the codec's own parsers for
each chunk-size line (`chunkSizeLine`) and for the last chunk and trailers
(`lastChunk`), and copies each chunk's data as one slice, where the codec
reads it byte by byte (`takeBytes`). It agrees with `chunkedBody` on every
input; that is property-tested (`tests/Props.lean`, `chunked_fast`), not
proved. -/
def readChunked (b : ByteArray) (pos : Nat) : Option (ByteArray × Nat) := Id.run do
  -- the data is shorter than the rest of the buffer: one allocation
  let mut out := ByteArray.emptyWithCapacity (b.size - pos)
  let mut pos := pos
  -- every chunk takes at least four bytes, so `b.size + 1` passes suffice
  for _ in [0:b.size + 1] do
    match (chunkSizeLine (ε := Unit)).run b pos with
    | .error _ _ => return none
    | .ok n j =>
      if n == 0 then
        match (lastChunk (ε := Unit)).run b pos with
        | .ok _ k => return some (out, k)
        | .error _ _ => return none
      if b.size < j + n + 2 then return none
      if b[j + n]! != CR || b[j + n + 1]! != LF then return none
      out := b.copySlice j out out.size n false
      pos := j + n + 2
  return none

/-- The chunked coding of a list of chunks. -/
def encodeChunked (cs : List ByteArray) : ByteArray := chunks.encodeBytes cs

/-- Read a chunked body: the chunks and the bytes after the last chunk. -/
def decodeChunked (b : ByteArray) : Option (List ByteArray × ByteArray) := chunks.decodeBytes b

/-- A body fits a framing: no body, exactly the length, any body below
`maxChunkSize` when chunked; a printed message never runs to the end or has invalid framing. -/
def bodyFits : Framing → ByteArray → Bool
  | .none, b => b.size == 0
  | .length n, b => b.size == n
  | .chunked, b => decide (b.size < maxChunkSize)
  | .close, _ => false
  | .invalid, _ => false

/-- A request the codec round-trips: a token method, a target, valid fields,
and a body that fits the framing its fields declare. -/
def Request.ok (r : Request) : Bool :=
  isToken r.head.method && isTarget r.head.target && r.head.fields.all Field.ok &&
    bodyFits (requestFraming r.head) r.body

/-- A response the codec round-trips: a status from 100 to 999, a reason
phrase, valid fields, and a body that fits its framing. -/
def Response.ok (requestMethod : List UInt8) (r : Response) : Bool :=
  (100 ≤ r.head.status && r.head.status ≤ 999) && reasonOk r.head.reason &&
    r.head.fields.all Field.ok && bodyFits (responseFraming requestMethod r.head) r.body

end H1

end LeanHttpx
