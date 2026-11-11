module

public import ChaChaPoly.Spec.Symbolic

/-!
# Properties of the AEAD construction

* `aeadEncrypt_eq`, `aeadDecrypt_eq`: the RFC model is the generic construction at `rfcPrims`.
* `aead_roundtrip`: decryption inverts encryption, for the real primitives, on all inputs.
* `macData_injective`: the authenticated encoding of `(aad, ct)` is injective.
* `Aead.integrity`: under an ideal MAC, changing the ciphertext or the associated data makes
  decryption reject.
-/

@[expose] public section

namespace ChaChaPoly.Spec

theorem aeadEncrypt_eq (key nonce aad pt : Bytes) :
    aeadEncrypt key nonce aad pt = Aead.encrypt rfcPrims key nonce aad pt := rfl

theorem aeadDecrypt_eq (key nonce aad ct tag : Bytes) :
    aeadDecrypt key nonce aad ct tag = Aead.decrypt rfcPrims key nonce aad ct tag := rfl

/-! ## Little-endian encodings -/

@[simp] theorem natLe_length (len n : Nat) : (natLe len n).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih => simp [natLe, ih]

theorem leNat_natLe (len n : Nat) : leNat (natLe len n) = n % 256 ^ len := by
  induction len generalizing n with
  | zero => simp [natLe, leNat, Nat.mod_one]
  | succ len ih =>
    show (BitVec.ofNat 8 n).toNat + 256 * leNat (natLe len (n / 256)) = _
    rw [ih, BitVec.toNat_ofNat, show 256 ^ (len + 1) = 256 * 256 ^ len from Nat.pow_succ', Nat.mod_mul]

theorem natLe_injective {len a b : Nat} (ha : a < 256 ^ len) (hb : b < 256 ^ len)
    (h : natLe len a = natLe len b) : a = b := by
  have := congrArg leNat h
  rwa [leNat_natLe, leNat_natLe, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-! ## Injectivity of the authenticated encoding -/

@[simp] theorem pad16_length (d : Bytes) : (pad16 d).length = (16 - d.length % 16) % 16 := by
  simp [pad16]

theorem macData_injective {aad ct aad' ct' : Bytes}
    (h : LengthsOk aad ct) (h' : LengthsOk aad' ct')
    (heq : macData aad ct = macData aad' ct') : aad = aad' ∧ ct = ct' := by
  unfold macData at heq
  -- Peel the two 8-byte length fields off the end.
  obtain ⟨heq, hc⟩ := List.append_inj' heq (by simp)
  obtain ⟨heq, ha⟩ := List.append_inj' heq (by simp)
  have hla : aad.length = aad'.length := natLe_injective (by simpa using h.1) (by simpa using h'.1) ha
  have hlc : ct.length = ct'.length := natLe_injective (by simpa using h.2) (by simpa using h'.2) hc
  -- With equal lengths the remaining four pieces line up.
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at heq
  obtain ⟨haad, heq⟩ := List.append_inj heq hla
  obtain ⟨_, heq⟩ := List.append_inj heq (by simp [hla])
  obtain ⟨hct, _⟩ := List.append_inj heq hlc
  exact ⟨haad, hct⟩

/-! ## Symbolic integrity -/

namespace Aead

variable {Tag : Type} [DecidableEq Tag]

/-- Decryption accepts exactly the tags the MAC produces. -/
theorem decrypt_eq_some_iff (P : Prims Tag) (key nonce aad ct : Bytes) (tag : Tag) (pt : Bytes) :
    decrypt P key nonce aad ct tag = some pt ↔
      P.mac (P.macKey key nonce) (macData aad ct) = tag ∧ pt = P.stream key nonce ct := by
  unfold decrypt
  split <;> simp_all [eq_comm]

/-- **Symbolic integrity.** Let `(ct, tag)` be the encryption of some plaintext under
    `(key, nonce, aad)`. Under an ideal MAC, decryption under the same `(key, nonce)` rejects
    every `(aad', ct')` other than `(aad, ct)` that is presented with `tag`. -/
theorem integrity (P : Prims Tag) (hideal : P.IdealMac) {key nonce aad pt ct aad' ct' : Bytes}
    {tag : Tag} (henc : encrypt P key nonce aad pt = (ct, tag))
    (hlen : LengthsOk aad ct) (hlen' : LengthsOk aad' ct')
    (hne : (aad', ct') ≠ (aad, ct)) :
    decrypt P key nonce aad' ct' tag = none := by
  unfold encrypt at henc
  obtain ⟨hct, htag⟩ := Prod.mk.inj henc
  unfold decrypt
  split
  · rename_i hmac
    exfalso
    rw [← htag, hct] at hmac
    obtain ⟨ha, hc⟩ := macData_injective hlen' hlen (hideal _ _ _ hmac)
    exact hne (by rw [ha, hc])
  · rfl

/-- Decryption inverts encryption whenever the stream cipher is an involution. -/
theorem roundtrip (P : Prims Tag) (hinv : ∀ k n d, P.stream k n (P.stream k n d) = d)
    (key nonce aad pt : Bytes) :
    decrypt P key nonce aad (encrypt P key nonce aad pt).1 (encrypt P key nonce aad pt).2 =
      some pt := by
  simp [decrypt, encrypt, hinv]

end Aead

theorem idealPrims_idealMac (stream : Bytes → Bytes → Bytes → Bytes)
    (macKey : Bytes → Bytes → Bytes) : (idealPrims stream macKey).IdealMac := by
  intro k m m' h
  exact (Prod.mk.inj h).2

/-! ## ChaCha20 encryption is an involution -/

theorem xorBytes_xorBytes : ∀ (d ks : Bytes), d.length ≤ ks.length → xorBytes (xorBytes d ks) ks = d
  | [], _, _ => by simp [xorBytes]
  | _ :: _, [], h => by simp at h
  | a :: d, k :: ks, h => by
    have ih := xorBytes_xorBytes d ks (by simpa using h)
    simp only [xorBytes, List.zipWith_cons_cons] at ih ⊢
    rw [ih, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

@[simp] theorem xorBytes_length (d ks : Bytes) : (xorBytes d ks).length = min d.length ks.length := by
  simp [xorBytes]

@[simp] theorem chacha20Block_length (key : Bytes) (counter : BitVec 32) (nonce : Bytes) :
    (chacha20Block key counter nonce).length = 64 := by
  simp [chacha20Block, State.bytes, word32Bytes]

theorem chacha20Encrypt_short (key : Bytes) (counter : BitVec 32) (nonce data : Bytes)
    (h : data.length ≤ 64) :
    chacha20Encrypt key counter nonce data = xorBytes data (chacha20Block key counter nonce) := by
  rw [chacha20Encrypt]; split
  · rfl
  · contradiction

theorem chacha20Encrypt_long (key : Bytes) (counter : BitVec 32) (nonce data : Bytes)
    (h : ¬ data.length ≤ 64) :
    chacha20Encrypt key counter nonce data =
      xorBytes (data.take 64) (chacha20Block key counter nonce) ++
        chacha20Encrypt key (counter + 1) nonce (data.drop 64) := by
  rw [chacha20Encrypt]; split
  · contradiction
  · rfl

theorem chacha20Encrypt_length (key : Bytes) (nonce : Bytes) :
    ∀ (n : Nat) (counter : BitVec 32) (data : Bytes), data.length = n →
      (chacha20Encrypt key counter nonce data).length = data.length := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro counter data hn
    by_cases h : data.length ≤ 64
    · rw [chacha20Encrypt_short _ _ _ _ h]; simp; omega
    · rw [chacha20Encrypt_long _ _ _ _ h, List.length_append,
        ih (data.drop 64).length (by simp; omega) _ _ rfl]
      simp; omega

theorem chacha20Encrypt_involutive (key : Bytes) (nonce : Bytes) :
    ∀ (n : Nat) (counter : BitVec 32) (data : Bytes), data.length = n →
      chacha20Encrypt key counter nonce (chacha20Encrypt key counter nonce data) = data := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro counter data hn
    by_cases h : data.length ≤ 64
    · have hlen : (xorBytes data (chacha20Block key counter nonce)).length ≤ 64 := by simp; omega
      rw [chacha20Encrypt_short _ _ _ data h, chacha20Encrypt_short _ _ _ _ hlen]
      exact xorBytes_xorBytes _ _ (by simpa using h)
    · have h64 : (xorBytes (data.take 64) (chacha20Block key counter nonce)).length = 64 := by
        simp; omega
      rw [chacha20Encrypt_long _ _ _ data h]
      rw [chacha20Encrypt_long _ _ _ _ (by
        rw [List.length_append, chacha20Encrypt_length key nonce _ _ _ rfl]; simp; omega)]
      rw [List.take_left' h64, List.drop_left' h64,
        ih (data.drop 64).length (by simp; omega) _ _ rfl,
        xorBytes_xorBytes _ _ (by simp; omega), List.take_append_drop]

/-- **Round trip.** For the real primitives, AEAD decryption of an AEAD encryption returns the
    plaintext, for every key, nonce, associated data and plaintext. -/
theorem aead_roundtrip (key nonce aad pt : Bytes) :
    aeadDecrypt key nonce aad (aeadEncrypt key nonce aad pt).1 (aeadEncrypt key nonce aad pt).2 =
      some pt := by
  rw [aeadEncrypt_eq, aeadDecrypt_eq]
  exact Aead.roundtrip rfcPrims (fun k n d => chacha20Encrypt_involutive k n _ 1 d rfl) key nonce aad pt

/-! ## ChaCha20 encryption as a key stream from the initial state -/

theorem initState_advance (key : Bytes) (c : BitVec 32) (nonce : Bytes) :
    (initState key c nonce).advance 1 = initState key (c + 1) nonce := by
  simp [State.advance, initState]

theorem chacha20Encrypt_eq_streamXor (key nonce : Bytes) :
    ∀ (n : Nat) (counter : BitVec 32) (data : Bytes), data.length = n →
      chacha20Encrypt key counter nonce data = streamXor (initState key counter nonce) data := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro counter data hn
    by_cases h : data.length ≤ 64
    · rw [chacha20Encrypt_short _ _ _ _ h, streamXor, dif_pos h]; rfl
    · rw [chacha20Encrypt_long _ _ _ _ h, streamXor, dif_neg h,
        ih (data.drop 64).length (by simp; omega) _ _ rfl, initState_advance]
      rfl

end ChaChaPoly.Spec
