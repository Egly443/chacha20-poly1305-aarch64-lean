module

public import ChaChaPoly.Proofs.Poly1305Final
public import ChaChaPoly.Proofs.Poly1305Block

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

/-! ## From the 32-bit expressions to the arithmetic -/

theorem toNat_sshr31 (x : BitVec 32) :
    (x.sshiftRight 31).toNat = if 2 ^ 31 ≤ x.toNat then 2 ^ 32 - 1 else 0 := by
  by_cases h : 2 ^ 31 ≤ x.toNat
  · have hm : x.msb = true := by rw [BitVec.msb_eq_decide]; simpa using h
    rw [BitVec.toNat_sshiftRight_of_msb_true hm, Nat.shiftRight_eq_div_pow]
    have := x.isLt
    simp only [h, ↓reduceIte]
    omega
  · have hm : x.msb = false := by rw [BitVec.msb_eq_decide]; simpa using h
    rw [BitVec.toNat_sshiftRight_of_msb_false hm, Nat.shiftRight_eq_div_pow]
    simp only [h, ↓reduceIte]
    omega



theorem carry32_iff (a b : BitVec 32) :
    (AddWithCarry32 a b false).snd.c = decide (2 ^ 32 ≤ a.toNat + b.toNat) := by
  simp only [AddWithCarry32, BitVec.msb_eq_decide, Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply propext
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.zeroExtend, BitVec.toNat_setWidth]
  have := a.isLt; have := b.isLt
  constructor <;> intro h <;> omega

theorem toNat_or_shl (x y : BitVec 32) (k : Nat) (hk : k < 32) (hx : x.toNat < 2 ^ k) :
    (x ||| y <<< k).toNat = x.toNat + 2 ^ k * (y.toNat % 2 ^ (32 - k)) := by
  have hy : (y <<< k).toNat = (y.toNat % 2 ^ (32 - k)) <<< k := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have e : (2 : Nat) ^ 32 = 2 ^ (32 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, Nat.mul_mod_mul_right]
  rw [BitVec.toNat_or, hy, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  rw [Nat.mul_comm]; omega



/-! ### The constant-time select, on variables -/

set_option maxRecDepth 200000

theorem selF0_keep (t g : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (-1#32 : BitVec 32) &&& (BitVec.zeroExtend 64 t &&& 67108863#64) ||| BitVec.zeroExtend 64 (BitVec.truncate 32 ((BitVec.zeroExtend 64 (0#32 : BitVec 32) &&& 67108863#64) &&& BitVec.zeroExtend 64 g))) = BitVec.truncate 32 (BitVec.zeroExtend 64 t &&& 67108863#64) := by bv_bits

theorem selF0_sub (t g : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (0#32 : BitVec 32) &&& (BitVec.zeroExtend 64 t &&& 67108863#64) ||| BitVec.zeroExtend 64 (BitVec.truncate 32 ((BitVec.zeroExtend 64 (-1#32 : BitVec 32) &&& 67108863#64) &&& BitVec.zeroExtend 64 g))) = BitVec.truncate 32 (BitVec.zeroExtend 64 g &&& 67108863#64) := by bv_bits

theorem selF1_keep (t g : BitVec 32) :
    BitVec.truncate 32 ((BitVec.zeroExtend 64 (0#32 : BitVec 32) &&& 67108863#64) &&& BitVec.zeroExtend 64 g) ||| (-1#32 : BitVec 32) &&& t = t := by bv_bits

theorem selF1_sub (t g : BitVec 32) :
    BitVec.truncate 32 ((BitVec.zeroExtend 64 (-1#32 : BitVec 32) &&& 67108863#64) &&& BitVec.zeroExtend 64 g) ||| (0#32 : BitVec 32) &&& t = BitVec.truncate 32 (BitVec.zeroExtend 64 g &&& 67108863#64) := by bv_bits

theorem selF2_keep (t g : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 ((BitVec.zeroExtend 64 (0#32 : BitVec 32) &&& 67108863#64) &&& BitVec.zeroExtend 64 g)) ||| BitVec.zeroExtend 64 (-1#32 : BitVec 32) &&& (BitVec.zeroExtend 64 t &&& 67108863#64)) = BitVec.truncate 32 (BitVec.zeroExtend 64 t &&& 67108863#64) := by bv_bits

theorem selF2_sub (t g : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 ((BitVec.zeroExtend 64 (-1#32 : BitVec 32) &&& 67108863#64) &&& BitVec.zeroExtend 64 g)) ||| BitVec.zeroExtend 64 (0#32 : BitVec 32) &&& (BitVec.zeroExtend 64 t &&& 67108863#64)) = BitVec.truncate 32 (BitVec.zeroExtend 64 g &&& 67108863#64) := by bv_bits

theorem selF4_keep (t g : BitVec 32) :
    (0#32 : BitVec 32) &&& g ||| (-1#32 : BitVec 32) &&& t = t := by bv_bits

theorem selF4_sub (t g : BitVec 32) :
    (-1#32 : BitVec 32) &&& g ||| (0#32 : BitVec 32) &&& t = g := by bv_bits

theorem toNat_m1 : (-1#32 : BitVec 32).toNat = 2 ^ 32 - 1 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- **`finalize` computes the Poly1305 tag.** For accumulator limbs within the representation
    bounds and any pad words `p`, the four output words (little-endian, as a 128-bit number)
    are `(acc mod (2^130 - 5) + s) mod 2^128`, where `acc` is the limbs' value and `s` the pad's. -/
theorem fin_correct (h0 h1 h2 h3 h4 p0 p1 p2 p3 : BitVec 32)
    (hh0 : h0.toNat < 2 ^ 26) (hh1 : h1.toNat < 2 ^ 26 + 64) (hh2 : h2.toNat < 2 ^ 26)
    (hh3 : h3.toNat < 2 ^ 26) (hh4 : h4.toNat < 2 ^ 26) :
    (finOut0 h0 h1 h2 h3 h4 p0).toNat + 2 ^ 32 * (finOut1 h0 h1 h2 h3 h4 p0 p1).toNat +
        2 ^ 64 * (finOut2 h0 h1 h2 h3 h4 p0 p1 p2).toNat + 2 ^ 96 * (finOut3 h0 h1 h2 h3 h4 p0 p1 p2 p3).toNat =
      (limbVal h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat % p1305 +
        (p0.toNat + 2 ^ 32 * p1.toNat + 2 ^ 64 * p2.toNat + 2 ^ 96 * p3.toNat)) % 2 ^ 128 := by
  -- Full carry.
  have eT2 : (finT2 h1 h2).toNat = h2.toNat + h1.toNat / 2 ^ 26 := by unfold finT2; bv_omega
  have eT3 : (finT3 h1 h2 h3).toNat = h3.toNat + (finT2 h1 h2).toNat / 2 ^ 26 := by
    unfold finT3; bv_omega
  have eT4 : (finT4 h1 h2 h3 h4).toNat = h4.toNat + (finT3 h1 h2 h3).toNat / 2 ^ 26 := by
    unfold finT4; bv_omega
  have eC4 : (finC4 h1 h2 h3 h4).toNat = (finT4 h1 h2 h3 h4).toNat / 2 ^ 26 := by
    unfold finC4; bv_omega
  have eT0 : (finT0 h0 h1 h2 h3 h4).toNat = 5 * (finC4 h1 h2 h3 h4).toNat + h0.toNat := by
    unfold finT0; bv_omega
  have eN0 : (finN0 h0 h1 h2 h3 h4).toNat = (finT0 h0 h1 h2 h3 h4).toNat % 2 ^ 26 := toNat_mask26' _
  have eN1 : (finN1 h1).toNat = h1.toNat % 2 ^ 26 := toNat_mask26' _
  have eN2 : (finN2 h1 h2).toNat = (finT2 h1 h2).toNat % 2 ^ 26 := toNat_mask26' _
  have eN3 : (finN3 h1 h2 h3).toNat = (finT3 h1 h2 h3).toNat % 2 ^ 26 := toNat_mask26' _
  have eN4 : (finN4 h1 h2 h3 h4).toNat = (finT4 h1 h2 h3 h4).toNat % 2 ^ 26 := toNat_mask26' _
  have eM1 : (finM1 h0 h1 h2 h3 h4).toNat = (finN1 h1).toNat + (finT0 h0 h1 h2 h3 h4).toNat / 2 ^ 26 := by
    unfold finM1; bv_omega
  -- Trial subtraction of p.
  have eG0 : (finG0 h0 h1 h2 h3 h4).toNat = (finN0 h0 h1 h2 h3 h4).toNat + 5 := by unfold finG0; bv_omega
  have eG1 : (finG1 h0 h1 h2 h3 h4).toNat = (finM1 h0 h1 h2 h3 h4).toNat + (finG0 h0 h1 h2 h3 h4).toNat / 2 ^ 26 := by
    unfold finG1; bv_omega
  have eG2 : (finG2 h0 h1 h2 h3 h4).toNat = (finN2 h1 h2).toNat + (finG1 h0 h1 h2 h3 h4).toNat / 2 ^ 26 := by
    unfold finG2; bv_omega
  have eG3 : (finG3 h0 h1 h2 h3 h4).toNat = (finN3 h1 h2 h3).toNat + (finG2 h0 h1 h2 h3 h4).toNat / 2 ^ 26 := by
    unfold finG3; bv_omega
  have eG4S : (finG4S h0 h1 h2 h3 h4).toNat = (finN4 h1 h2 h3 h4).toNat + (finG3 h0 h1 h2 h3 h4).toNat / 2 ^ 26 := by
    unfold finG4S; bv_omega
  have eG4 : (finG4 h0 h1 h2 h3 h4).toNat = ((finG4S h0 h1 h2 h3 h4).toNat + 4227858432) % 2 ^ 32 := by
    unfold finG4; bv_omega
  -- Constant-time select.
  obtain ⟨F0, F1, F2, F3, F4, eF0, eF1, eF2, eF3, eF4, hsel⟩ : ∃ F0 F1 F2 F3 F4 : Nat,
      (finF0 h0 h1 h2 h3 h4).toNat = F0 ∧ (finF1 h0 h1 h2 h3 h4).toNat = F1 ∧ (finF2 h0 h1 h2 h3 h4).toNat = F2 ∧
      (finF3 h0 h1 h2 h3 h4).toNat = F3 ∧ (finF4 h0 h1 h2 h3 h4).toNat = F4 ∧
      (((finG4S h0 h1 h2 h3 h4).toNat < 2 ^ 26 ∧ F0 = (finN0 h0 h1 h2 h3 h4).toNat ∧ F1 = (finM1 h0 h1 h2 h3 h4).toNat ∧
          F2 = (finN2 h1 h2).toNat ∧ F3 = (finN3 h1 h2 h3).toNat ∧ F4 = (finT4 h1 h2 h3 h4).toNat) ∨
        (2 ^ 26 ≤ (finG4S h0 h1 h2 h3 h4).toNat ∧ F0 = (finG0 h0 h1 h2 h3 h4).toNat % 2 ^ 26 ∧
          F1 = (finG1 h0 h1 h2 h3 h4).toNat % 2 ^ 26 ∧ F2 = (finG2 h0 h1 h2 h3 h4).toNat % 2 ^ 26 ∧
          F3 = (finG3 h0 h1 h2 h3 h4).toNat % 2 ^ 26 ∧ F4 = (finG4S h0 h1 h2 h3 h4).toNat)) := by
    have hG4Sb : (finG4S h0 h1 h2 h3 h4).toNat < 2 ^ 27 := by omega
    by_cases hc : (finG4S h0 h1 h2 h3 h4).toNat < 2 ^ 26
    · have hNM : finNM h0 h1 h2 h3 h4 = -1#32 := by
        apply BitVec.eq_of_toNat_eq
        rw [finNM, toNat_sshr31, toNat_m1, if_pos (by omega)]
      have hMK : finMK h0 h1 h2 h3 h4 = 0#32 := by unfold finMK; bv_omega
      refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hc, ?_, ?_, ?_, ?_, ?_⟩⟩
      · unfold finF0 finMKM finN0; rw [hNM, hMK]; exact congrArg BitVec.toNat (selF0_keep _ _)
      · unfold finF1 finMKM; rw [hNM, hMK]; exact congrArg BitVec.toNat (selF1_keep _ _)
      · unfold finF2 finMKM finN2; rw [hNM, hMK]; exact congrArg BitVec.toNat (selF2_keep _ _)
      · unfold finF3 finMKM finN3; rw [hNM, hMK]; exact congrArg BitVec.toNat (selF2_keep _ _)
      · unfold finF4; rw [hNM, hMK]; exact congrArg BitVec.toNat (selF4_keep _ _)
    · have hNM : finNM h0 h1 h2 h3 h4 = 0#32 := by
        apply BitVec.eq_of_toNat_eq
        rw [finNM, toNat_sshr31, if_neg (by omega)]; rfl
      have hMK : finMK h0 h1 h2 h3 h4 = -1#32 := by unfold finMK; bv_omega
      refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩⟩
      · unfold finF0 finMKM; rw [hNM, hMK]
        rw [← toNat_mask26' (finG0 h0 h1 h2 h3 h4)]; exact congrArg BitVec.toNat (selF0_sub _ _)
      · unfold finF1 finMKM; rw [hNM, hMK]
        rw [← toNat_mask26' (finG1 h0 h1 h2 h3 h4)]; exact congrArg BitVec.toNat (selF1_sub _ _)
      · unfold finF2 finMKM; rw [hNM, hMK]
        rw [← toNat_mask26' (finG2 h0 h1 h2 h3 h4)]; exact congrArg BitVec.toNat (selF2_sub _ _)
      · unfold finF3 finMKM; rw [hNM, hMK]
        rw [← toNat_mask26' (finG3 h0 h1 h2 h3 h4)]; exact congrArg BitVec.toNat (selF2_sub _ _)
      · unfold finF4; rw [hNM, hMK]; exact congrArg BitVec.toNat (selF4_sub _ _)
  obtain ⟨⟨bF0, bF1, bF2, bF3⟩, hcore⟩ := fin_core h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat
    hh0 hh1 hh2 hh3 hh4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 F1 F2 F3 F4
    eT2 eT3 eT4 eC4 eT0 eN0 eN1 eN2 eN3 eN4 eM1 eG0 eG1 eG2 eG3 eG4S hsel
  -- Repacking.
  have eO0 : (finO0 h0 h1 h2 h3 h4).toNat = F0 + 2 ^ 26 * (F1 % 2 ^ 6) := by
    unfold finO0; rw [toNat_or_shl _ _ 26 (by decide) (by omega), eF0, eF1]
  have eO1 : (finO1 h0 h1 h2 h3 h4).toNat = F1 / 2 ^ 6 + 2 ^ 20 * (F2 % 2 ^ 12) := by
    have e : (BitVec.truncate 32 (BitVec.zeroExtend 64 (finF1 h0 h1 h2 h3 h4) >>> 6)).toNat = F1 / 2 ^ 6 := by
      rw [← eF1]; bv_omega
    unfold finO1; rw [toNat_or_shl _ _ 20 (by decide) (by omega), e, eF2]
  have eO2 : (finO2 h0 h1 h2 h3 h4).toNat = F2 / 2 ^ 12 + 2 ^ 14 * (F3 % 2 ^ 18) := by
    have e : (BitVec.truncate 32 (BitVec.zeroExtend 64 (finF2 h0 h1 h2 h3 h4) >>> 12)).toNat = F2 / 2 ^ 12 := by
      rw [← eF2]; bv_omega
    unfold finO2; rw [toNat_or_shl _ _ 14 (by decide) (by omega), e, eF3]
  have eO3 : (finO3 h0 h1 h2 h3 h4).toNat = F3 / 2 ^ 18 + 2 ^ 8 * (F4 % 2 ^ 24) := by
    have e : (BitVec.truncate 32 (BitVec.zeroExtend 64 (finF3 h0 h1 h2 h3 h4) >>> 18)).toNat = F3 / 2 ^ 18 := by
      rw [← eF3]; bv_omega
    unfold finO3; rw [toNat_or_shl _ _ 8 (by decide) (by omega), e, eF4]
  -- Adding the pad.
  have eo0 : (finOut0 h0 h1 h2 h3 h4 p0).toNat = ((finO0 h0 h1 h2 h3 h4).toNat + p0.toNat) % 2 ^ 32 := by
    unfold finOut0; bv_omega
  have eS1 : (finS1 h0 h1 h2 h3 h4 p0 p1).toNat =
      (finO1 h0 h1 h2 h3 h4).toNat + p1.toNat + ((finO0 h0 h1 h2 h3 h4).toNat + p0.toNat) / 2 ^ 32 := by
    unfold finS1; rw [carry32_iff]
    have := (finO0 h0 h1 h2 h3 h4).isLt; have := p0.isLt
    split <;> rename_i hcy <;> simp only [decide_eq_true_eq] at hcy <;> bv_omega
  have eo1 : (finOut1 h0 h1 h2 h3 h4 p0 p1).toNat = (finS1 h0 h1 h2 h3 h4 p0 p1).toNat % 2 ^ 32 := by
    unfold finOut1; bv_omega
  have eS2 : (finS2 h0 h1 h2 h3 h4 p0 p1 p2).toNat =
      (finO2 h0 h1 h2 h3 h4).toNat + p2.toNat + (finS1 h0 h1 h2 h3 h4 p0 p1).toNat / 2 ^ 32 := by
    unfold finS2; bv_omega
  have eo2 : (finOut2 h0 h1 h2 h3 h4 p0 p1 p2).toNat = (finS2 h0 h1 h2 h3 h4 p0 p1 p2).toNat % 2 ^ 32 := by
    unfold finOut2; bv_omega
  have eo3 : (finOut3 h0 h1 h2 h3 h4 p0 p1 p2 p3).toNat =
      (((finO3 h0 h1 h2 h3 h4).toNat + p3.toNat) % 2 ^ 32 + (finS2 h0 h1 h2 h3 h4 p0 p1 p2).toNat / 2 ^ 32) % 2 ^ 32 := by
    unfold finOut3; bv_omega
  have hpack := fin_pack F0 F1 F2 F3 F4 p0.toNat p1.toNat p2.toNat p3.toNat _ _ _ _ _ _ _ _ _ _
    bF0 bF1 bF2 bF3 p0.isLt p1.isLt p2.isLt p3.isLt eO0 eO1 eO2 eO3 eo0 eS1 eo1 eS2 eo2 eo3
  rw [hpack, hcore]
  omega

/-- `finalize` satisfies its contract over the RFC model. -/
theorem polyFinalContract_ok [CpPlacement] :
    subroutine_ok cpProg8r cpPl8.base (chachapolyLib.withCodeLoaded cpMpl polyFinalContract) := by
  refine subroutine_ok_reghost (C := fun s0 => chachapolyLib.CodeLoaded cpMpl s0.mem)
    (pre₁ := polyFinalSpec.pre) (post₁ := polyFinalSpec.post) polyFinal_ok ?_
  intro a R s0 hpre
  simp only [polyFinalContract] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hh0, hh1, hh2, hh3, hh4⟩, hm⟩ := hpre
  refine ⟨⟨a.st, a.out, a.s0, a.s1, a.s2, a.s3, a.h0, a.h1, a.h2, a.h3, a.h4, a.o0, a.o1, a.o2, a.o3⟩, ?_, ?_⟩
  · simp only [polyFinalSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8⟩, hm⟩
  · intro sf hq
    simp only [polyFinalSpec] at hq
    have hv := fin_correct a.h0 a.h1 a.h2 a.h3 a.h4 a.s0 a.s1 a.s2 a.s3 hh0 hh1 hh2 hh3 hh4
    rw [sepConj_assoc, sepConj_assoc] at hq ⊢
    refine Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (Entails.sepExists_intro (P := fun t : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 =>
        ⌜words4Val t.1 t.2.1 t.2.2.1 t.2.2.2 =
          (limbVal a.h0.toNat a.h1.toNat a.h2.toNat a.h3.toNat a.h4.toNat % p1305 +
            words4Val a.s0 a.s1 a.s2 a.s3) % 2 ^ 128⌝ ∗
        words4At a.out t.1 t.2.1 t.2.2.1 t.2.2.2)
        (finOut0 a.h0 a.h1 a.h2 a.h3 a.h4 a.s0, finOut1 a.h0 a.h1 a.h2 a.h3 a.h4 a.s0 a.s1, finOut2 a.h0 a.h1 a.h2 a.h3 a.h4 a.s0 a.s1 a.s2,
          finOut3 a.h0 a.h1 a.h2 a.h3 a.h4 a.s0 a.s1 a.s2 a.s3))))) ?_
    rw [← sepConj_assoc, ← sepConj_assoc] at hq ⊢
    rw [sepConj_comm (words4At a.st _ _ _ _ ∗ _), sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj]
    rw [sepConj_comm (words4At a.st _ _ _ _ ∗ _), sepConj_assoc] at hq
    exact ⟨by simp only [words4Val]; exact hv, hq⟩

end ChaChaPoly.Proofs
