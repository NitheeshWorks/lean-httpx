import LeanHttpx.RepoImpl.Text

/-!
# Headers and query parameters (`httpx.Headers`, `httpx.QueryParams`)

`Headers` is httpx's case-insensitive multi-dict: an ordered list of raw
`(name, value)` pairs, looked up by the ASCII-lower-cased name. Every
operation is a list function, so its laws are list facts; `update` (the
operation behind the client's header merge) is `headers_merge_precedence`.

`QueryParams` is httpx's immutable multi-dict of query parameters: keys in
first-insertion order, each with its values in order, parsed with
`urllib.parse.parse_qs(keep_blank_values=True)` and printed with
`urlencode`.
-/

namespace LeanHttpx

/-- ASCII lower case (what `bytes.lower()` does to a header name). -/
def asciiLower (s : String) : String := String.ofList (s.toList.map Char.toLower)

/-- HTTP headers: raw `(name, value)` pairs in order (`httpx.Headers`). -/
structure Headers where
  raw : List (String × String) := []
  deriving DecidableEq, Repr, Inhabited


instance : Coe (List (String × String)) Headers := ⟨fun l => ⟨l⟩⟩

namespace Headers

variable (h : Headers)

/-- Build from pairs (`httpx.Headers([...])` or `httpx.Headers({...})`). -/
def ofList (l : List (String × String)) : Headers := ⟨l⟩

/-- The pairs whose lower-cased name is `k` (already lower-cased). -/
def matching (k : String) : List (String × String) := h.raw.filter fun p => asciiLower p.1 == k

/-- Every value for a name, in order (`get_list`). With `splitCommas`, each
value is split at commas and stripped. -/
def getList (key : String) (splitCommas : Bool := false) : List String :=
  let vs := (h.matching (asciiLower key)).map (·.2)
  if splitCommas then vs.flatMap fun v => (v.splitOn ",").map fun s => s.trimAscii.toString else vs

/-- The value for a name, several values joined with `", "`
(`headers[key]`, `headers.get(key)`). -/
def get? (key : String) : Option String :=
  match h.getList key with
  | [] => none
  | vs => some (", ".intercalate vs)

/-- `headers.get(key, default)`. -/
def getD (key : String) (default : String) : String := (h.get? key).getD default

/-- `key in headers`. -/
def contains (key : String) : Bool := h.raw.any fun p => asciiLower p.1 == asciiLower key

/-- Remove every pair with this name (`del headers[key]`, `pop`). -/
def delete (key : String) : Headers := ⟨h.raw.filter fun p => asciiLower p.1 != asciiLower key⟩

/-- Set a name to one value (`headers[key] = value`): the first pair with the
name is replaced in place, any others removed; a new name goes at the end. -/
def set (key value : String) : Headers :=
  let k := asciiLower key
  if h.contains key then
    let rec go : List (String × String) → Bool → List (String × String)
      | [], _ => []
      | p :: ps, seen =>
        if asciiLower p.1 == k then (if seen then go ps true else (key, value) :: go ps true)
        else p :: go ps seen
    ⟨go h.raw false⟩
  else ⟨h.raw ++ [(key, value)]⟩

/-- Set a value unless the name is present (`setdefault`). -/
def setdefault (key value : String) : Headers := if h.contains key then h else h.set key value

/-- Add a pair at the end, keeping any existing ones. -/
def append (key value : String) : Headers := ⟨h.raw ++ [(key, value)]⟩

/-- **`headers.update(other)`**: every name in `other` replaces all of its
pairs here; `other`'s pairs are appended. This is how a client merges its
default headers with a request's. -/
def update (other : Headers) : Headers :=
  ⟨(h.raw.filter fun p => !other.contains p.1) ++ other.raw⟩

/-- The distinct lower-cased names, in order (`keys()`). -/
def keys : List String :=
  (h.raw.map fun p => asciiLower p.1).foldl (fun acc k => if acc.contains k then acc else acc ++ [k]) []

/-- `(name, joined value)` per distinct name (`items()`). -/
def items : List (String × String) := h.keys.map fun k => (k, (h.get? k).getD "")

/-- The joined values per distinct name (`values()`). -/
def values : List String := h.items.map (·.2)

/-- The pairs with lower-cased names (`multi_items()`). -/
def multiItems : List (String × String) := h.raw.map fun p => (asciiLower p.1, p.2)

/-- The number of pairs (`len(headers)`). -/
def size : Nat := h.raw.length

/-- Equality as httpx compares headers: the same lower-cased pairs, in any
order. -/
def equiv (a b : Headers) : Bool := a.multiItems.isPerm b.multiItems

/-- `repr(headers)`: a dict when names are distinct, else a list;
`authorization` values hidden. -/
def pyRepr : String :=
  let items := h.multiItems.map fun (k, v) =>
    (k, if k == "authorization" || k == "proxy-authorization" then "[secure]" else v)
  let distinct := h.keys.length == items.length
  if distinct then
    "Headers({" ++ ", ".intercalate (items.map fun (k, v) => Text.pyRepr k ++ ": " ++ Text.pyRepr v) ++ "})"
  else
    "Headers([" ++ ", ".intercalate (items.map fun (k, v) => "(" ++ Text.pyRepr k ++ ", " ++ Text.pyRepr v ++ ")") ++ "])"

instance : GetElem? Headers String String (fun h k => (h.get? k).isSome) where
  getElem h k ok := (h.get? k).get ok
  getElem? h k := h.get? k

end Headers

/-- URL query parameters (`httpx.QueryParams`): each key once, in order of
first appearance, with its values in order. -/
structure QueryParams where
  dict : List (String × List String) := []
  deriving DecidableEq, Repr, Inhabited


namespace QueryParams

variable (q : QueryParams)

/-- Append a value for a key. -/
def addValue (key value : String) : QueryParams :=
  if q.dict.any (·.1 == key) then
    ⟨q.dict.map fun p => if p.1 == key then (p.1, p.2 ++ [value]) else p⟩
  else ⟨q.dict ++ [(key, [value])]⟩

/-- From `(key, value)` pairs, grouping repeated keys. -/
def ofList (l : List (String × String)) : QueryParams :=
  l.foldl (fun (q : QueryParams) (p : String × String) => q.addValue p.1 p.2) ⟨[]⟩

instance : Coe (List (String × String)) QueryParams := ⟨ofList⟩

/-- Parse a query string as `parse_qs(qs, keep_blank_values=True)` does:
split at `&`, skip empty fields, a field without `=` has an empty value,
`+` is a space and `%XX` escapes are decoded. -/
def parse (s : String) : QueryParams :=
  ofList <| (s.splitOn "&").filterMap fun field =>
    if field.isEmpty then none else
    match field.splitOn "=" with
    | [] => none
    | k :: rest => some (Text.unquotePlus k, Text.unquotePlus ("=".intercalate rest))

/-- `(key, value)` pairs, a key's values together (`multi_items()`). -/
def multiItems : List (String × String) := q.dict.flatMap fun p => p.2.map (p.1, ·)

/-- The keys (`keys()`). -/
def keys : List String := q.dict.map (·.1)

/-- The first value per key (`items()`). -/
def items : List (String × String) := q.dict.filterMap fun p => p.2.head?.map (p.1, ·)

/-- The first values (`values()`). -/
def values : List String := q.items.map (·.2)

/-- The first value of a key (`get`). -/
def get? (key : String) : Option String := (q.dict.find? (·.1 == key)).bind (·.2.head?)

/-- Every value of a key (`get_list`). -/
def getList (key : String) : List String := ((q.dict.find? (·.1 == key)).map (·.2)).getD []

/-- `key in params`. -/
def contains (key : String) : Bool := q.dict.any (·.1 == key)

/-- Set a key to one value (`set`). -/
def set (key value : String) : QueryParams :=
  if q.contains key then ⟨q.dict.map fun p => if p.1 == key then (key, [value]) else p⟩
  else ⟨q.dict ++ [(key, [value])]⟩

/-- Add a value for a key (`add`). -/
def add (key value : String) : QueryParams := q.addValue key value

/-- Remove a key (`remove`). -/
def remove (key : String) : QueryParams := ⟨q.dict.filter (·.1 != key)⟩

/-- `merge(other)`: `other`'s keys replace these keys' values; new keys
are added in `other`'s order. -/
def merge (other : QueryParams) : QueryParams :=
  other.dict.foldl (fun acc p => if acc.contains p.1 then
    ⟨acc.dict.map fun e => if e.1 == p.1 then p else e⟩ else ⟨acc.dict ++ [p]⟩) q

/-- The number of keys. -/
def size : Nat := q.dict.length

/-- Empty: no keys. -/
def isEmpty : Bool := q.dict.isEmpty

/-- `str(params)`: `urlencode` of the multi-items. -/
protected def toString : String :=
  "&".intercalate (q.multiItems.map fun p => Text.quotePlus p.1 ++ "=" ++ Text.quotePlus p.2)

instance : ToString QueryParams := ⟨QueryParams.toString⟩

/-- `repr(params)`. -/
def pyRepr : String := "QueryParams(" ++ Text.pyRepr (toString q) ++ ")"

/-- Equality as httpx compares: the same multi-items, in any order. -/
def equiv (a b : QueryParams) : Bool := a.multiItems.isPerm b.multiItems

end QueryParams

end LeanHttpx
