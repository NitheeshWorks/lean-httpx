import LeanHttpx.RepoImpl.Bytes
import LeanHttpx.RepoImpl.Huffman
import LeanHttpx.DataTypes.H2

/-!
# HPACK (RFC 7541), as h2's `hpack` does it

Two layers, as for frames.

* **Wire.** A header block is a sequence of representations (`Rep`): an
  indexed field, a literal (with incremental indexing, without indexing, or
  never indexed) whose name is an index or a string, or a dynamic table size
  update. Integers use the prefix coding of section 5.1, at most five
  continuation bytes as `hpack` allows (`VARINT_MAX_LENGTH`); strings are
  raw or Huffman-coded. `encodeReps` prints, `decodeReps` reads.
* **Tables.** The static table (Appendix A) and a dynamic table, newest
  entry first, evicted from the oldest end to its maximum size. A `Decoder`
  applies representations to its table; an `Encoder` chooses them (an index
  when the field or its name is in a table, otherwise a literal) and updates
  its own table the same way, so the two tables stay equal.

Limits, against a hostile peer: a table size update above the size this
side allowed (`SETTINGS_HEADER_TABLE_SIZE`) is an error, and so is one after
the first field of a block; the decoded header list is at most
`maxHeaderListSize` (h2's 65536, counting 32 octets per field as the RFC
does), checked field by field, so a few bytes that reference a large entry
many times stop as soon as the list is too large; a Huffman string expands
at most 8/5.

The encoder prints strings raw (h2 Huffman-codes a string when that is
shorter); the decoder reads both.
-/

namespace LeanHttpx

namespace Hpack

open Bytes H2

/-- A header field: name and value bytes. -/
abbrev Field := ByteArray × ByteArray

/-- A decoded field, with whether it was sent as never-indexed (h2's
`NeverIndexedHeaderTuple`). -/
structure HeaderField where
  name : ByteArray
  value : ByteArray
  sensitive : Bool := false
  deriving DecidableEq, Inhabited

/-- The static table (RFC 7541 Appendix A), entries 1 to 61. -/
def staticEntries : List (String × String) := [
  (":authority", ""), (":method", "GET"), (":method", "POST"), (":path", "/"),
  (":path", "/index.html"), (":scheme", "http"), (":scheme", "https"), (":status", "200"),
  (":status", "204"), (":status", "206"), (":status", "304"), (":status", "400"),
  (":status", "404"), (":status", "500"), ("accept-charset", ""), ("accept-encoding", "gzip, deflate"),
  ("accept-language", ""), ("accept-ranges", ""), ("accept", ""), ("access-control-allow-origin", ""),
  ("age", ""), ("allow", ""), ("authorization", ""), ("cache-control", ""),
  ("content-disposition", ""), ("content-encoding", ""), ("content-language", ""), ("content-length", ""),
  ("content-location", ""), ("content-range", ""), ("content-type", ""), ("cookie", ""),
  ("date", ""), ("etag", ""), ("expect", ""), ("expires", ""),
  ("from", ""), ("host", ""), ("if-match", ""), ("if-modified-since", ""),
  ("if-none-match", ""), ("if-range", ""), ("if-unmodified-since", ""), ("last-modified", ""),
  ("link", ""), ("location", ""), ("max-forwards", ""), ("proxy-authenticate", ""),
  ("proxy-authorization", ""), ("range", ""), ("referer", ""), ("refresh", ""),
  ("retry-after", ""), ("server", ""), ("set-cookie", ""), ("strict-transport-security", ""),
  ("transfer-encoding", ""), ("user-agent", ""), ("vary", ""), ("via", ""),
  ("www-authenticate", "")]

/-- The static table as fields. -/
def staticTable : List Field := staticEntries.map fun (n, v) => (n.toUTF8, v.toUTF8)

/-- The number of static entries. -/
def staticSize : Nat := 61

/-! ## The dynamic table -/

/-- The size of an entry: its octets plus 32 (section 4.1). -/
def entrySize (f : Field) : Nat := f.1.size + f.2.size + 32

/-- The newest entries whose sizes add up to at most `budget`: what is left
after evicting from the oldest end (section 4.4). -/
def fitPrefix : List Field → Nat → List Field
  | [], _ => []
  | e :: es, budget => if entrySize e ≤ budget then e :: fitPrefix es (budget - entrySize e) else []

/-- The dynamic table: entries, newest first, and its maximum size. -/
structure Table where
  entries : List Field := []
  maxSize : Nat := 4096
  deriving Inhabited

/-- The current size. -/
def Table.size (t : Table) : Nat := (t.entries.map entrySize).sum

/-- Add an entry, evicting as needed; an entry larger than the table empties
it and is not added. -/
def Table.add (t : Table) (f : Field) : Table := { t with entries := fitPrefix (f :: t.entries) t.maxSize }

/-- Change the maximum size, evicting as needed. -/
def Table.resize (t : Table) (n : Nat) : Table := { entries := fitPrefix t.entries n, maxSize := n }

/-- The entry at an index: static from 1 to 61, dynamic after. -/
def Table.get (t : Table) (i : Nat) : Option Field :=
  if i == 0 then none
  else if i ≤ staticSize then staticTable[i - 1]?
  else t.entries[i - staticSize - 1]?

/-- The index of a field in either table. -/
def Table.findField (t : Table) (f : Field) : Option Nat :=
  match staticTable.findIdx? (fun x => decide (x = f)) with
  | some j => some (j + 1)
  | none => (t.entries.findIdx? (fun x => decide (x = f))).map (· + staticSize + 1)

/-- The index of a name in either table. -/
def Table.findName (t : Table) (n : ByteArray) : Option Nat :=
  match staticTable.findIdx? (fun x => decide (x.1 = n)) with
  | some j => some (j + 1)
  | none => (t.entries.findIdx? (fun x => decide (x.1 = n))).map (· + staticSize + 1)

/-! ## Representations -/

/-- How a literal affects the table (section 6.2). -/
inductive LitKind where
  | incremental | withoutIndexing | neverIndexed
  deriving DecidableEq, Repr, Inhabited

/-- A literal's name: an index, or the name itself. -/
inductive NameRef where
  | idx (i : Nat)
  | lit (name : ByteArray)
  deriving DecidableEq, Inhabited

/-- One representation in a header block (section 6). -/
inductive Rep where
  | indexed (i : Nat)
  | literal (kind : LitKind) (name : NameRef) (value : ByteArray)
  | sizeUpdate (n : Nat)
  deriving DecidableEq, Inhabited

/-! ## Integers and strings on the wire -/

/-- Continuation bytes of an integer, seven bits each, least significant
first (section 5.1). -/
def contBytes (x : Nat) : ByteArray :=
  if x < 128 then beArr 1 x else beArr 1 (x % 128 + 128) ++ contBytes (x / 128)
termination_by x
decreasing_by omega

/-- An integer with an `n`-bit prefix, the bits above it being `flags`. -/
def encodeInt (n flags v : Nat) : ByteArray :=
  if v < 2 ^ n - 1 then beArr 1 (flags + v) else beArr 1 (flags + (2 ^ n - 1)) ++ contBytes (v - (2 ^ n - 1))

/-- A string, raw (not Huffman-coded). -/
def encodeStr (s : ByteArray) : ByteArray := encodeInt 7 0 s.size ++ s

/-- An HPACK decoding error (`COMPRESSION_ERROR`). -/
def err (msg : String) : Error := ⟨.compressionError, msg⟩

/-- The most continuation bytes of an integer (`hpack`'s `VARINT_MAX_LENGTH`
of five octets after the prefix). -/
def maxContBytes : Nat := 5

/-- Read continuation bytes: the value so far, its next shift, and how many
bytes may still follow. -/
def readCont (b : ByteArray) : Nat → Nat → Nat → Nat → Except Error (Nat × Nat)
  | 0, _, _, _ => .error (err "Variable integer representation is too long")
  | fuel + 1, acc, shift, i => do
    let (x, i) ← u8 b (err "Unable to decode HPACK integer representation") i
    if x ≥ 128 then readCont b fuel (acc + (x - 128) * 2 ^ shift) (shift + 7) i
    else pure (acc + x * 2 ^ shift, i)

/-- Read an integer with an `n`-bit prefix: the bits above the prefix, and
the value. -/
def readInt (b : ByteArray) (n : Nat) (i : Nat) : Except Error ((Nat × Nat) × Nat) := do
  let (x, i) ← u8 b (err "Unable to decode HPACK integer representation") i
  let v := x % 2 ^ n
  if v < 2 ^ n - 1 then pure ((x - v, v), i)
  else
    let (r, i) ← readCont b maxContBytes 0 0 i
    pure ((x - v, v + r), i)

/-- Read a string: its length, then the bytes, Huffman-decoded when the
`H` bit is set. -/
def readStr (b : ByteArray) (i : Nat) : Except Error (ByteArray × Nat) := do
  let ((h, len), i) ← readInt b 7 i
  let (s, i) ← slice b len (err "String literal is longer than the block") i
  if h ≥ 128 then
    match Huffman.decode s with
    | some d => pure (d, i)
    | none => .error (err "Invalid Huffman string")
  else pure (s, i)

/-- The prefix, and the bits above it, of each literal kind. -/
def LitKind.prefix : LitKind → Nat × Nat
  | .incremental => (6, 64)
  | .withoutIndexing => (4, 0)
  | .neverIndexed => (4, 16)

/-- The bytes of a representation. -/
def encodeRep : Rep → ByteArray
  | .indexed i => encodeInt 7 128 i
  | .literal k (.idx i) v => encodeInt k.prefix.1 k.prefix.2 i ++ encodeStr v
  | .literal k (.lit n) v => encodeInt k.prefix.1 k.prefix.2 0 ++ (encodeStr n ++ encodeStr v)
  | .sizeUpdate n => encodeInt 5 32 n

/-- The bytes of a block. -/
def encodeReps : List Rep → ByteArray
  | [] => .empty
  | r :: rs => encodeRep r ++ encodeReps rs

/-- The byte at a position, without moving. -/
def peek (b : ByteArray) (i : Nat) : Except Error Nat :=
  if h : i < b.size then .ok b[i].toNat else .error (err "Unexpected end of header block")

/-- Read a literal of a kind. -/
def readLiteral (b : ByteArray) (k : LitKind) (i : Nat) : Except Error (Rep × Nat) := do
  let ((_, idx), i) ← readInt b k.prefix.1 i
  if idx == 0 then
    let (n, i) ← readStr b i
    let (v, i) ← readStr b i
    pure (.literal k (.lit n) v, i)
  else
    let (v, i) ← readStr b i
    pure (.literal k (.idx idx) v, i)

/-- Read one representation, by the high bits of its first byte. -/
def readRep (b : ByteArray) (i : Nat) : Except Error (Rep × Nat) := do
  let x ← peek b i
  if x ≥ 128 then
    let ((_, idx), i) ← readInt b 7 i
    pure (.indexed idx, i)
  else if x ≥ 64 then readLiteral b .incremental i
  else if x ≥ 32 then
    let ((_, n), i) ← readInt b 5 i
    pure (.sizeUpdate n, i)
  else if x ≥ 16 then readLiteral b .neverIndexed i
  else readLiteral b .withoutIndexing i

/-- Read representations to the end of the block. Every representation
takes at least one byte, so `fuel = b.size - i` suffices. -/
def readReps (b : ByteArray) : Nat → Nat → Except Error (List Rep)
  | 0, i => if i ≥ b.size then .ok [] else .error (err "Header block too long")
  | fuel + 1, i =>
    if i ≥ b.size then .ok [] else do
    let (r, j) ← readRep b i
    if j ≤ i then .error (err "Header block did not advance") else
    let rs ← readReps b fuel j
    pure (r :: rs)

/-- **Read a header block's representations.** -/
def decodeReps (b : ByteArray) : Except Error (List Rep) := readReps b b.size 0

/-! ## Applying representations -/

/-- The name a literal refers to. -/
def Table.name (t : Table) : NameRef → Except Error ByteArray
  | .idx i => match t.get i with
    | some f => .ok f.1
    | none => .error (err s!"Invalid table index {i}")
  | .lit n => .ok n

/-- Apply one representation: the new table, and the field it carries. A
size update above `limit` is an error. -/
def apply (limit : Nat) (t : Table) : Rep → Except Error (Table × Option HeaderField)
  | .indexed i => match t.get i with
    | some f => .ok (t, some ⟨f.1, f.2, false⟩)
    | none => .error (err s!"Invalid table index {i}")
  | .literal k nr v => do
    let n ← t.name nr
    let t' := if k == .incremental then t.add (n, v) else t
    pure (t', some ⟨n, v, k == .neverIndexed⟩)
  | .sizeUpdate n =>
    if n > limit then .error (err s!"Dynamic table size update {n} above the allowed {limit}")
    else .ok (t.resize n, none)

/-- A dynamic table size update. -/
def Rep.isSizeUpdate : Rep → Bool
  | .sizeUpdate _ => true
  | _ => false

/-- The size a header list counts (section 4.1 of RFC 7540, as h2 counts it). -/
def fieldSize (f : HeaderField) : Nat := f.name.size + f.value.size + 32

/-- The size of a header list (RFC 7541 section 4.1 per field, as the
header-list limit counts it). -/
def listSize (fs : List HeaderField) : Nat := (fs.map fieldSize).sum

/-- A table within its maximum size, the maximum below `2 ^ 28` (so every
size update and index fits the integers this decoder reads). -/
def Table.Wf (t : Table) : Prop := t.size ≤ t.maxSize ∧ t.maxSize < 2 ^ 28

/-- The decoding side: its table, the table size this side allows, and the
largest header list it accepts. -/
structure Decoder where
  table : Table := {}
  maxTableSize : Nat := 4096
  maxHeaderListSize : Nat := 65536
  deriving Inhabited

/-- Apply a block's representations in order: size updates only before the
first field, the header list within its limit at every field. -/
def applyAll (limit maxList : Nat) : Table → List Rep → Bool → Nat → Except Error (List HeaderField × Table)
  | t, [], _, _ => .ok ([], t)
  | t, r :: rs, started, total => do
    if started && r.isSizeUpdate then
      throw (err "Dynamic table size update not at the start of the block")
    let (t, f) ← apply limit t r
    match f with
    | none => applyAll limit maxList t rs started total
    | some f =>
      let total := total + fieldSize f
      if total > maxList then throw (err s!"Header list too large: {total} > {maxList}")
      let (fs, t) ← applyAll limit maxList t rs true total
      pure (f :: fs, t)

/-- **Decode a header block.** -/
def Decoder.decode (d : Decoder) (b : ByteArray) : Except Error (List HeaderField × Decoder) := do
  let reps ← decodeReps b
  let (fs, t) ← applyAll d.maxTableSize d.maxHeaderListSize d.table reps false 0
  pure (fs, { d with table := t })

/-! ## Encoding -/

/-- The encoding side: its table, and a size update to send at the start of
the next block (after the peer's `SETTINGS_HEADER_TABLE_SIZE` changed). -/
structure Encoder where
  table : Table := {}
  pendingSize : Option Nat := none
  deriving Inhabited

/-- The name reference for a name. -/
def Table.nameRef (t : Table) (n : ByteArray) : NameRef :=
  match t.findName n with
  | some i => .idx i
  | none => .lit n

/-- The representation the encoder chooses for a field: never-indexed for a
sensitive field; the index when the field is in a table; else a literal
with incremental indexing. -/
def choose (t : Table) (f : HeaderField) : Rep :=
  if f.sensitive then .literal .neverIndexed (t.nameRef f.name) f.value
  else match t.findField (f.name, f.value) with
    | some i => .indexed i
    | none => .literal .incremental (t.nameRef f.name) f.value

/-- What a representation does to the table, when it applies. -/
def step (t : Table) : Rep → Table
  | .literal .incremental nr v => match t.name nr with
    | .ok n => t.add (n, v)
    | .error _ => t
  | .sizeUpdate n => t.resize n
  | _ => t

/-- Choose the representations of fields, updating the table as the
decoder will. -/
def chooseAll : Table → List HeaderField → List Rep × Table
  | t, [] => ([], t)
  | t, f :: fs =>
    let r := choose t f
    let (rs, t') := chooseAll (step t r) fs
    (r :: rs, t')

/-- **Encode a header block**: a pending size update, then each field. -/
def Encoder.encode (e : Encoder) (fs : List HeaderField) : ByteArray × Encoder :=
  let (pre, t) := match e.pendingSize with
    | some n => ([Rep.sizeUpdate n], e.table.resize n)
    | none => ([], e.table)
  let (rs, t) := chooseAll t fs
  (encodeReps (pre ++ rs), { table := t, pendingSize := none })

/-- Encode header lists in order, one block each, the table carried along. -/
def Encoder.encodeAll (e : Encoder) : List (List HeaderField) → List ByteArray × Encoder
  | [] => ([], e)
  | fs :: ls =>
    let (b, e') := e.encode fs
    let (bs, e'') := e'.encodeAll ls
    (b :: bs, e'')

/-- Decode blocks in order, the table carried along. -/
def Decoder.decodeAll (d : Decoder) : List ByteArray → Except Error (List (List HeaderField) × Decoder)
  | [] => .ok ([], d)
  | b :: bs => do
    let (fs, d') ← d.decode b
    let (ls, d'') ← d'.decodeAll bs
    pure (fs :: ls, d'')

/-- After the peer's `SETTINGS_HEADER_TABLE_SIZE`: use at most that size,
and say so at the start of the next block. -/
def Encoder.setMaxSize (e : Encoder) (n : Nat) : Encoder :=
  { e with pendingSize := some n }

/-- The static-only encoding (section 2.3, no dynamic table): an index for
a field of the static table, else a literal without indexing, its name an
index when the static table has it. -/
def chooseStatic (f : HeaderField) : Rep :=
  let t : Table := { maxSize := 0 }
  match staticTable.findIdx? (fun x => decide (x = (f.name, f.value))) with
  | some j => if f.sensitive then .literal .neverIndexed (t.nameRef f.name) f.value else .indexed (j + 1)
  | none => .literal (if f.sensitive then .neverIndexed else .withoutIndexing) (t.nameRef f.name) f.value

/-- **Encode without the dynamic table.** -/
def encodeStatic (fs : List HeaderField) : ByteArray := encodeReps (fs.map chooseStatic)

end Hpack

end LeanHttpx
