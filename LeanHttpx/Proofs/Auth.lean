import LeanHttpx.RepoImpl.Auth
import LeanHttpx.RepoImpl.Lists

/-!
# Basic credentials round trip

`basic_auth_header`: the `Authorization` value `BasicAuth u p` sends decodes
back to `(u, p)` whenever the user-id has no colon (RFC 7617 section 2
forbids one: the first colon separates user-id and password). It rests on
the base64 law `Base64.decode_encode` and on one UTF-8 fact: the byte `:`
appears in a character's encoding only for `:` itself.
-/

namespace LeanHttpx

/-- The byte `0x3A` occurs in the UTF-8 encoding of `c` only if `c` is `:`. -/
theorem colon_byte (c : Char) (h : (58 : UInt8) ∈ String.utf8EncodeChar c) : c = ':' := by
  unfold String.utf8EncodeChar at h
  dsimp only at h
  split at h
  · simp only [List.mem_singleton, ← UInt8.toNat_inj, UInt8.toNat_ofNat] at h
    apply Char.ext
    apply UInt32.toNat_inj.mp
    have : c.val.toNat % 256 = c.val.toNat := Nat.mod_eq_of_lt (by omega)
    show c.val.toNat = 58
    rw [UInt8.toNat_ofNat'] at h
    omega
  · split at h <;> (try split at h) <;> simp [← UInt8.toNat_inj, UInt8.toNat_ofNat] at h <;> omega

theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s := by
  simp [String.fromUTF8?, s.isValidUTF8]
  rfl

theorem no_colon_byte {s : String} (h : ':' ∉ s.toList) : ∀ b ∈ s.toByteArray.data.toList, (b != 58) = true := by
  intro b hb
  rw [← String.utf8Encode_toList] at hb
  simp only [List.utf8Encode, List.toList_data_toByteArray, List.mem_flatMap] at hb
  obtain ⟨c, hc, hbc⟩ := hb
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  exact h (colon_byte c hbc ▸ hc)

/-- **Basic credentials decode back** (card: `basic_auth_header`). -/
theorem basic_auth_header (u p : String) (h : ':' ∉ u.toList) :
    parseBasicAuth (basicAuthHeader u p) = some (u, p) := by
  have hb : (u.toUTF8 ++ ":".toUTF8 ++ p.toUTF8).data.toList =
      u.toByteArray.data.toList ++ (58 :: p.toByteArray.data.toList) := by
    simp only [ByteArray.data_append, Array.toList_append, String.toUTF8_eq_toByteArray]
    have : (":".toByteArray).data.toList = [58] := by decide
    rw [this]; simp
  have hs : splitColon (u.toByteArray.data.toList ++ (58 :: p.toByteArray.data.toList)) =
      (u.toByteArray.data.toList, p.toByteArray.data.toList) := by
    have hstop : StopsAt (· != (58 : UInt8)) (58 :: p.toByteArray.data.toList) := stopsAt_cons (by decide)
    simp [splitColon, takeWhile_append_stop (no_colon_byte h) hstop,
      dropWhile_append_stop (no_colon_byte h) hstop]
  have hpre : (basicAuthHeader u p).toList.take 6 = "Basic ".toList := by
    simp [basicAuthHeader]
  have hd : String.ofList ((basicAuthHeader u p).toList.drop 6) = Base64.encode (u.toUTF8 ++ ":".toUTF8 ++ p.toUTF8) := by
    simp [basicAuthHeader]
  have ha : ∀ s : String, (⟨s.toByteArray.data.toList.toArray⟩ : ByteArray) = s.toByteArray := by
    intro s; simp
  simp only [parseBasicAuth, hpre, bne_self_eq_false, Bool.false_eq_true, ite_false, hd,
    Base64.decode_encode]
  simp only [Option.bind_eq_bind, Option.bind, hb, hs, ha, fromUTF8?_toByteArray]
  rfl

end LeanHttpx
