module

public import ChaChaPoly.Proofs.Integrity
public import ChaChaPoly.Proofs.Code
public import ChaChaPoly.Spec.Contracts

/-!
# Symbolic integrity at the machine code

`decryptIntegrity_of_contract`: any code meeting `aeadDecryptContract` meets
`aeadDecryptIntegrityContract`. If decryption accepts a presented `(aad', ct')` with an honest tag
for a different `(aad, ct)`, the tag check passed, so Poly1305 under the one-time key maps the
two authenticated encodings (distinct, by `macData_injective`) to the same tag.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib
open ChaChaPoly ChaChaPoly.Spec

theorem decryptIntegrity_of_contract {prog : Program} {e sigma : BitVec 64}
    {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (h : subroutine_ok prog e (lib.withCodeLoaded mpl (aeadDecryptContract sigma))) :
    subroutine_ok prog e (lib.withCodeLoaded mpl (aeadDecryptIntegrityContract sigma)) := by
  refine subroutine_ok_of_ghost h ?_
  intro x R s0 hp
  obtain ⟨g, aad0, pt⟩ := x
  dsimp only [MultiPlacedLib.withCodeLoaded, aeadDecryptIntegrityContract] at hp
  simp only [sepConj_assoc] at hp
  rw [satisfies_pure_sepConj] at hp
  obtain ⟨⟨htag, hne, hlen0⟩, hp⟩ := hp
  have hpre := hp
  simp only [aeadDecryptContract, aeadPre, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, hal, hml⟩, _⟩ := hpre
  have hlen : LengthsOk g.a g.msg := ⟨by omega, by simp only [maxMsgLen] at hml; omega⟩
  refine ⟨g, emp, ?_, fun sf _ hq => ?_⟩
  · simp only [MultiPlacedLib.withCodeLoaded, emp_sepConj, sepConj_assoc]
    exact hp
  simp only [MultiPlacedLib.withCodeLoaded, aeadDecryptContract, emp_sepConj] at hq
  dsimp only [MultiPlacedLib.withCodeLoaded, aeadDecryptIntegrityContract]
  cases hd : aeadDecrypt g.k g.n g.a g.msg g.t with
  | none =>
    simp only [hd, sepConj_assoc, satisfies_pure_sepConj] at hq
    obtain ⟨hx0, hq⟩ := hq
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨Or.inl hx0, ?_⟩
    refine Satisfies.mono ?_ hq
    refine sepConj_mono_left ?_
    refine Entails.trans ?_ (Entails.sepExists_intro g.msg)
    rw [pure_sepConj_of_true (fun _ => rfl)]
    exact Entails.refl _
  | some p =>
    simp only [hd, sepConj_assoc, satisfies_pure_sepConj] at hq
    obtain ⟨hx0, hq⟩ := hq
    have hmac : poly1305Mac (poly1305KeyGen g.k g.n) (macData g.a g.msg) = g.t := by
      unfold aeadDecrypt at hd
      split at hd
      · assumption
      · exact absurd hd (by simp)
    have hcol : polyCollision (poly1305KeyGen g.k g.n) (macData g.a g.msg)
        (macData aad0 (aeadEncrypt g.k g.n aad0 pt).1) := by
      refine ⟨fun heq => hne ?_, ?_⟩
      · obtain ⟨h1, h2⟩ := macData_injective hlen hlen0 heq
        rw [h1, h2]
      · rw [hmac, ← htag]; rfl
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨Or.inr hcol, ?_⟩
    refine Satisfies.mono ?_ hq
    refine sepConj_mono_left ?_
    refine Entails.trans ?_ (Entails.sepExists_intro p)
    rw [pure_sepConj_of_true (fun h => by rw [hx0] at h; exact absurd h (by decide))]
    exact Entails.refl _

end ChaChaPoly.Proofs
