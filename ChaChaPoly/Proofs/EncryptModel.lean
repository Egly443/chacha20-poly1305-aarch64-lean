module

public import ChaChaPoly.Proofs.EncryptBytes

/-!
# `chachapoly_encrypt`: the RFC 8439 side

`chacha20Encrypt` is the key stream of an explicit state (`chacha20Encrypt_eq`), the Poly1305 key
is the first 32 bytes of block 0 of it (`keyGen_eq`), and the tag the code computes is the tag of
`aeadEncrypt` (`enc_tag`).
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 ProofLib ChaChaPoly ChaChaPoly.Spec

theorem initState_succ (key nonce : Bytes) (c : BitVec 32) :
    initState key (c + 1) nonce = (initState key c nonce).advance 1 := by
  simp [initState, Spec.State.advance]

theorem chacha20Encrypt_eq (key nonce : Bytes) (data : Bytes) (c : BitVec 32) :
    chacha20Encrypt key c nonce data = streamXor (initState key c nonce) data := by
  by_cases hs : data.length ≤ 64
  · rw [chacha20Encrypt, dif_pos hs, streamXor_short _ _ hs]; rfl
  · rw [chacha20Encrypt, dif_neg hs, streamXor_long _ _ hs,
      chacha20Encrypt_eq key nonce (data.drop 64) (c + 1), initState_succ]
    rfl
termination_by data.length
decreasing_by simp only [List.length_drop]; omega

theorem xorBytes_zeros (B : Bytes) (m : Nat) (h : m ≤ B.length) :
    xorBytes (List.replicate m 0#8) B = B.take m := by
  induction m generalizing B with
  | zero => simp [xorBytes]
  | succ m ih =>
    match B, h with
    | b :: B', h =>
      simp only [List.replicate_succ, xorBytes, List.zipWith_cons_cons, List.take_succ_cons]
      rw [← xorBytes, ih B' (by simp at h; omega)]
      simp

theorem keyGen_eq (k n : Bytes) :
    poly1305KeyGen k n = streamXor (initState k 0 n) (List.replicate 32 0#8) := by
  rw [streamXor_short _ _ (by simp), xorBytes_zeros _ _ (by simp [stateBlock_length])]
  rfl

theorem pad16_aligned (X : Bytes) : (X ++ pad16 X).length % 16 = 0 := by
  simp only [List.length_append, pad16, List.length_replicate]; omega

theorem natLe_mod (n x : Nat) : natLe n (x % 256 ^ n) = natLe n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [natLe]
    congr 1
    · apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat, Nat.pow_succ]
    · rw [← ih (x / 256)]; congr 1
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]


theorem enc_tag (k n a msg mk : Bytes) (w0 w1 w2 w3 t0 t1 t2 t3 : BitVec 32) (l3 : PolyLimbs)
    (hmk : mk = streamXor (initState k 0 n) (List.replicate 32 0#8))
    (hpw : words4Val w0 w1 w2 w3 = leNat (mk.drop 16))
    (hl3 : l3.Rep (clamp (leNat (mk.take 16)))
      ((polyBlocks (clamp (leNat (mk.take 16))) (polyBlocks (clamp (leNat (mk.take 16))) 0 (a ++ pad16 a))
          (streamXor (initState k 1 n) msg ++ pad16 (streamXor (initState k 1 n) msg)) +
        leNat (natLe 8 a.length ++ natLe 8 msg.length ++ [1])) * clamp (leNat (mk.take 16)) % p1305))
    (htg : words4Val t0 t1 t2 t3 =
      (limbVal l3.h0.toNat l3.h1.toNat l3.h2.toNat l3.h3.toNat l3.h4.toNat % p1305 +
        words4Val w0 w1 w2 w3) % 2 ^ 128) :
    natLe 16 (words4Val t0 t1 t2 t3) = (aeadEncrypt k n a msg).2 := by
  have hmkl : mk.length = 32 := by rw [hmk, streamXor_length _ _ _ rfl]; simp
  have hCl : (streamXor (initState k 1 n) msg).length = msg.length := streamXor_length _ _ _ rfl
  simp only [aeadEncrypt, poly1305Mac, macData, chacha20Encrypt_eq]
  rw [keyGen_eq, ← hmk]
  rw [show (mk.drop 16).take 16 = mk.drop 16 by rw [List.take_of_length_le]; simp [hmkl]]
  generalize hr : clamp (leNat (mk.take 16)) = r at *
  generalize hC : streamXor (initState k 1 n) msg = C at *
  have hlens : (natLe 8 a.length ++ natLe 8 C.length).length = 16 := by simp [natLe]
  rw [show a ++ pad16 a ++ C ++ pad16 C ++ natLe 8 a.length ++ natLe 8 C.length =
      (a ++ pad16 a) ++ ((C ++ pad16 C) ++ (natLe 8 a.length ++ natLe 8 C.length ++ [])) by simp,
    polyBlocks_append r ((a ++ pad16 a).length / 16) _ _ _ (by have := pad16_aligned a; omega),
    polyBlocks_append r ((C ++ pad16 C).length / 16) _ _ _ (by have := pad16_aligned C; omega),
    polyBlocks_block _ _ _ _ hlens, polyBlocks_nil, hCl]
  rw [htg, hl3.2.2.2, Nat.mod_mod, hpw, show (2 : Nat) ^ 128 = 256 ^ 16 by decide, natLe_mod]

end ChaChaPoly.Proofs
