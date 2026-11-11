module

public import ChaChaPoly.Proofs.Poly1305Final

/-!
# The arithmetic of `Poly1305::finalize`

`fin_core`: the full carry, the trial subtraction of `p = 2^130 - 5` and the select leave limbs
whose value is the accumulator fully reduced modulo `p` (taken modulo `2^128`).
`fin_pack`: repacking into four 32-bit words and adding the pad `s` with carries computes the
sum modulo `2^128`.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open ChaChaPoly.Spec Arm64 ProofLib

theorem fin_core (h0 h1 h2 h3 h4 : Nat)
    (hh0 : h0 < 2 ^ 26) (hh1 : h1 < 2 ^ 26 + 64) (hh2 : h2 < 2 ^ 26) (hh3 : h3 < 2 ^ 26)
    (hh4 : h4 < 2 ^ 26)
    (T2 T3 T4 C4 T0 N0 N1 N2 N3 N4 M1 G0 G1 G2 G3 G4S F0 F1 F2 F3 F4 : Nat)
    (hT2 : T2 = h2 + h1 / 2 ^ 26) (hT3 : T3 = h3 + T2 / 2 ^ 26) (hT4 : T4 = h4 + T3 / 2 ^ 26)
    (hC4 : C4 = T4 / 2 ^ 26) (hT0 : T0 = 5 * C4 + h0)
    (hN0 : N0 = T0 % 2 ^ 26) (hN1 : N1 = h1 % 2 ^ 26) (hN2 : N2 = T2 % 2 ^ 26)
    (hN3 : N3 = T3 % 2 ^ 26) (hN4 : N4 = T4 % 2 ^ 26)
    (hM1 : M1 = N1 + T0 / 2 ^ 26)
    (hG0 : G0 = N0 + 5) (hG1 : G1 = M1 + G0 / 2 ^ 26) (hG2 : G2 = N2 + G1 / 2 ^ 26)
    (hG3 : G3 = N3 + G2 / 2 ^ 26) (hG4S : G4S = N4 + G3 / 2 ^ 26)
    (hsel : (G4S < 2 ^ 26 ∧ F0 = N0 ∧ F1 = M1 ∧ F2 = N2 ∧ F3 = N3 ∧ F4 = T4) ∨
      (2 ^ 26 ≤ G4S ∧ F0 = G0 % 2 ^ 26 ∧ F1 = G1 % 2 ^ 26 ∧ F2 = G2 % 2 ^ 26 ∧
        F3 = G3 % 2 ^ 26 ∧ F4 = G4S)) :
    (F0 < 2 ^ 26 ∧ F1 < 2 ^ 26 ∧ F2 < 2 ^ 26 ∧ F3 < 2 ^ 26) ∧
    F0 + 2 ^ 26 * F1 + 2 ^ 52 * F2 + 2 ^ 78 * F3 + 2 ^ 104 * (F4 % 2 ^ 24) =
      limbVal h0 h1 h2 h3 h4 % p1305 % 2 ^ 128 := by
  have hM1b : M1 < 2 ^ 26 := by omega
  have hv : N0 + 2 ^ 26 * M1 + 2 ^ 52 * N2 + 2 ^ 78 * N3 + 2 ^ 104 * N4 + p1305 * C4 =
      limbVal h0 h1 h2 h3 h4 := by
    simp only [limbVal, p1305]; omega
  have hg : G0 % 2 ^ 26 + 2 ^ 26 * (G1 % 2 ^ 26) + 2 ^ 52 * (G2 % 2 ^ 26) + 2 ^ 78 * (G3 % 2 ^ 26) +
      2 ^ 104 * G4S = N0 + 2 ^ 26 * M1 + 2 ^ 52 * N2 + 2 ^ 78 * N3 + 2 ^ 104 * N4 + 5 := by
    omega
  generalize hV : N0 + 2 ^ 26 * M1 + 2 ^ 52 * N2 + 2 ^ 78 * N3 + 2 ^ 104 * N4 = V at hv hg
  have hVb : V < 2 ^ 130 := by omega
  rcases hsel with ⟨hlt, e0, e1, e2, e3, e4⟩ | ⟨hge, e0, e1, e2, e3, e4⟩
  · have hVp : V < p1305 := by simp only [p1305]; omega
    have hmod : limbVal h0 h1 h2 h3 h4 % p1305 = V := by
      rw [← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hVp]
    rw [hmod]
    refine ⟨by omega, ?_⟩
    omega
  · have hVp : p1305 ≤ V := by simp only [p1305]; omega
    have hmod : limbVal h0 h1 h2 h3 h4 % p1305 = V - p1305 := by
      have e : limbVal h0 h1 h2 h3 h4 = (V - p1305) + p1305 * (C4 + 1) := by
        rw [← hv, Nat.mul_add, Nat.mul_one]; omega
      rw [e, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by simp only [p1305] at *; omega)]
    rw [hmod]
    refine ⟨by omega, ?_⟩
    simp only [p1305] at *
    omega

theorem fin_pack (F0 F1 F2 F3 F4 p0 p1 p2 p3 O0 O1 O2 O3 S1 S2 o0 o1 o2 o3 : Nat)
    (hF0 : F0 < 2 ^ 26) (hF1 : F1 < 2 ^ 26) (hF2 : F2 < 2 ^ 26) (hF3 : F3 < 2 ^ 26)
    (hp0 : p0 < 2 ^ 32) (hp1 : p1 < 2 ^ 32) (hp2 : p2 < 2 ^ 32) (hp3 : p3 < 2 ^ 32)
    (hO0 : O0 = F0 + 2 ^ 26 * (F1 % 2 ^ 6)) (hO1 : O1 = F1 / 2 ^ 6 + 2 ^ 20 * (F2 % 2 ^ 12))
    (hO2 : O2 = F2 / 2 ^ 12 + 2 ^ 14 * (F3 % 2 ^ 18))
    (hO3 : O3 = F3 / 2 ^ 18 + 2 ^ 8 * (F4 % 2 ^ 24))
    (ho0 : o0 = (O0 + p0) % 2 ^ 32) (hS1 : S1 = O1 + p1 + (O0 + p0) / 2 ^ 32)
    (ho1 : o1 = S1 % 2 ^ 32) (hS2 : S2 = O2 + p2 + S1 / 2 ^ 32) (ho2 : o2 = S2 % 2 ^ 32)
    (ho3 : o3 = ((O3 + p3) % 2 ^ 32 + S2 / 2 ^ 32) % 2 ^ 32) :
    o0 + 2 ^ 32 * o1 + 2 ^ 64 * o2 + 2 ^ 96 * o3 =
      (F0 + 2 ^ 26 * F1 + 2 ^ 52 * F2 + 2 ^ 78 * F3 + 2 ^ 104 * (F4 % 2 ^ 24) +
        (p0 + 2 ^ 32 * p1 + 2 ^ 64 * p2 + 2 ^ 96 * p3)) % 2 ^ 128 := by
  omega

end ChaChaPoly.Proofs
