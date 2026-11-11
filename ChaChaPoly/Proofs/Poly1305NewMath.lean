module

public import ChaChaPoly.Proofs.Poly1305New
public import ChaChaPoly.Proofs.Poly1305FinalMath

/-!
# The arithmetic of `Poly1305::new`

`new_clamp`: the five limbs the code computes are below `2^26` and have value
`clamp (leNat key[0..16])` (RFC 8439 §2.5.1). The clamp identity is decided bit by bit by the
kernel-checked ROBDD procedure `bv_robdd`. `new_pad`: the pad words are key bytes 16..31.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 ProofLib ChaChaPoly.Spec

set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

theorem clampsum (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (BitVec.zeroExtend 128 (BitVec.truncate 32 (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) &&& 67108863#64)) <<< 0) + (BitVec.zeroExtend 128 (BitVec.truncate 32 (67108611#64 &&& BitVec.zeroExtend 64 (pack32 b3 b4 b5 b6) >>> 2)) <<< 26) + (BitVec.zeroExtend 128 (BitVec.truncate 32 (67092735#64 &&& BitVec.zeroExtend 64 (pack32 b6 b7 b8 b9) >>> 4)) <<< 52) + (BitVec.zeroExtend 128 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (pack32 b9 b10 b11 b12) >>> 6)) &&& 4293935103#64)) <<< 78) + (BitVec.zeroExtend 128 (BitVec.truncate 32 (BitVec.zeroExtend 64 (pack32 b12 b13 b14 b15) >>> 8 &&& 1048575#64)) <<< 104) =
    (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) &&& 0x0ffffffc0ffffffc0ffffffc0fffffff#128 := by
  simp only [pack32]
  bv_robdd

theorem toNat_zx_shl (l : BitVec 32) (k : Nat) (hb : l.toNat * 2 ^ k < 2 ^ 128) :
    (BitVec.zeroExtend 128 l <<< k).toNat = l.toNat * 2 ^ k := by
  have hl := l.isLt
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hl (by decide)), Nat.mod_eq_of_lt hb]

theorem sum_toNat (l0 l1 l2 l3 l4 : BitVec 32) (h0 : l0.toNat < 2 ^ 26) (h1 : l1.toNat < 2 ^ 26)
    (h2 : l2.toNat < 2 ^ 26) (h3 : l3.toNat < 2 ^ 26) (h4 : l4.toNat < 2 ^ 24) :
    ((BitVec.zeroExtend 128 l0 <<< 0) + (BitVec.zeroExtend 128 l1 <<< 26) +
      (BitVec.zeroExtend 128 l2 <<< 52) + (BitVec.zeroExtend 128 l3 <<< 78) +
      (BitVec.zeroExtend 128 l4 <<< 104)).toNat =
    l0.toNat + 2 ^ 26 * l1.toNat + 2 ^ 52 * l2.toNat + 2 ^ 78 * l3.toNat + 2 ^ 104 * l4.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add,
    toNat_zx_shl _ _ (by omega), toNat_zx_shl _ _ (by omega), toNat_zx_shl _ _ (by omega),
    toNat_zx_shl _ _ (by omega), toNat_zx_shl _ _ (by omega)]
  omega

theorem toNat_append' {m n : Nat} (a : BitVec m) (x : BitVec n) :
    (a ++ x).toNat = 2 ^ n * a.toNat + x.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq, Nat.mul_comm]

theorem shr26_bound (x : BitVec 32) (h : x >>> 26 = 0#32) : x.toNat < 2 ^ 26 := by bv_omega
theorem shr24_bound (x : BitVec 32) (h : x >>> 24 = 0#32) : x.toNat < 2 ^ 24 := by bv_omega

theorem new_clamp (kb : Bytes) (hlen : kb.length = 32) :
    ((newL0 kb).toNat < 2 ^ 26 ∧ (newL1 kb).toNat < 2 ^ 26 ∧ (newL2 kb).toNat < 2 ^ 26 ∧
      (newL3 kb).toNat < 2 ^ 26 ∧ (newL4 kb).toNat < 2 ^ 26) ∧
    limbVal (newL0 kb).toNat (newL1 kb).toNat (newL2 kb).toNat (newL3 kb).toNat (newL4 kb).toNat =
      clamp (leNat (kb.take 16)) := by
  match kb, hlen with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], _ =>
    simp only [newL0, newL1, newL2, newL3, newL4, kw, List.getD_cons_zero, List.getD_cons_succ]
    have e0 := shr26_bound _ (by simp only [pack32]; bv_robdd : BitVec.truncate 32 (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) &&& 67108863#64) >>> 26 = 0#32)
    have e1 := shr26_bound _ (by simp only [pack32]; bv_robdd : BitVec.truncate 32 (67108611#64 &&& BitVec.zeroExtend 64 (pack32 b3 b4 b5 b6) >>> 2) >>> 26 = 0#32)
    have e2 := shr26_bound _ (by simp only [pack32]; bv_robdd : BitVec.truncate 32 (67092735#64 &&& BitVec.zeroExtend 64 (pack32 b6 b7 b8 b9) >>> 4) >>> 26 = 0#32)
    have e3 := shr26_bound _ (by simp only [pack32]; bv_robdd : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (pack32 b9 b10 b11 b12) >>> 6)) &&& 4293935103#64) >>> 26 = 0#32)
    have e4 := shr24_bound _ (by simp only [pack32]; bv_robdd : BitVec.truncate 32 (BitVec.zeroExtend 64 (pack32 b12 b13 b14 b15) >>> 8 &&& 1048575#64) >>> 24 = 0#32)
    refine ⟨⟨e0, e1, e2, e3, by omega⟩, ?_⟩
    have hs := congrArg BitVec.toNat (clampsum b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
    rw [sum_toNat _ _ _ _ _ e0 e1 e2 e3 e4] at hs
    rw [limbVal, hs, BitVec.toNat_and, BitVec.toNat_ofNat]
    have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt; have := b4.isLt
    have := b5.isLt; have := b6.isLt; have := b7.isLt; have := b8.isLt; have := b9.isLt
    have := b10.isLt; have := b11.isLt; have := b12.isLt; have := b13.isLt; have := b14.isLt
    have := b15.isLt
    have hX : (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).toNat = leNat ([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31].take 16) := by
      simp only [toNat_append', leNat, List.take_succ_cons, List.take_zero]
      omega
    have hC : 0x0ffffffc0ffffffc0ffffffc0fffffff % 2 ^ 128 = 0x0ffffffc0ffffffc0ffffffc0fffffff := by
      decide
    rw [hX, hC]
    rfl

theorem readLE8_lo (kb : Bytes) (o : Nat) :
    (ByteSlice.readLE kb o 8).extractLsb' 0 32 = kw kb o := by
  simp only [ByteSlice.readLE, kw, pack32, Nat.add_zero]
  bv_robdd

theorem readLE8_hi (kb : Bytes) (o : Nat) :
    (ByteSlice.readLE kb o 8).extractLsb' 32 32 = kw kb (o + 4) := by
  simp only [ByteSlice.readLE, kw, pack32, Nat.add_zero, Nat.add_assoc]
  bv_robdd

theorem new_pad (kb : Bytes) (hlen : kb.length = 32) :
    words4Val (kw kb 16) (kw kb 20) (kw kb 24) (kw kb 28) = leNat (kb.drop 16) := by
  match kb, hlen with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], _ =>
    simp only [words4Val, kw, toNat_pack32, List.getD_cons_zero, List.getD_cons_succ, leNat,
      List.drop_succ_cons, List.drop_zero]
    omega

set_option maxHeartbeats 4000000 in
/-- `new` satisfies its contract over the RFC model. -/
theorem polyNewContract_ok [CpPlacement] :
    subroutine_ok cpProg10r cpPl10.base (chachapolyLib.withCodeLoaded cpMpl polyNewContract) := by
  refine subroutine_ok_reghost (C := fun s0 => chachapolyLib.CodeLoaded cpMpl s0.mem)
    (pre₁ := polyNewSpec.pre) (post₁ := polyNewSpec.post) polyNew_ok ?_
  rintro ⟨k, out, kb⟩ R s0 hpre
  simp only [polyNewContract] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hlen⟩, hm⟩ := hpre
  rw [memRegion_partition out 56 [8, 16, 20, 24, 28, 32, 36, 44, 52]] at hm
  simp only [memRegion_four, memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists] at hm
  obtain ⟨c7, a6, a5, c4, c3, c2, c1, c0, a1, a0, hm⟩ := hm
  refine ⟨⟨k, out, kb, a0, a1, a5, a6, c0, c1, c2, c3, c4, c7⟩, ?_, ?_⟩
  · simp only [polyNewSpec, newOutCells]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, hlen⟩, hm⟩
  · intro sf hq
    simp only [polyNewSpec] at hq
    obtain ⟨⟨r0b, r1b, r2b, r3b, r4b⟩, hrv⟩ := new_clamp kb hlen
    refine Satisfies.of_entails hq (sepConj_mono_left (sepConj_mono_right ?_))
    refine Entails.trans ?_ (Entails.sepExists_intro (kw kb 16, kw kb 20, kw kb 24, kw kb 28))
    refine Entails.trans ?_ (Entails.sepExists_intro
      (⟨newL0 kb, newL1 kb, newL2 kb, newL3 kb, newL4 kb, 0#32, 0#32, 0#32, 0#32, 0#32⟩ : PolyLimbs))
    rw [pure_sepConj_of_true ⟨new_pad kb hlen, ⟨r0b, r1b, r2b, r3b, r4b⟩, hrv,
      ⟨by simp, by simp, by simp, by simp, by simp⟩, by simp [limbVal]⟩]
    simp only [newOutCells, words4At, polyLimbsAt, limbsAt, pointsTo64_split32, readLE8_lo,
      readLE8_hi, BitVec.add_assoc]
    sep_entail

end ChaChaPoly.Proofs
