module

public import ChaChaPoly.Proofs.ApplyKeystream7

/-!
# `apply_keystream` (block 4), part 8: the tail loop

At offset `0x43c` the last `t < 64` data bytes are XORed in place with the key-stream buffer.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
arm64_proof_prelude

/-- `T` with its first `i` bytes XORed with `kb`. -/
def tailPrefix (T kb : Bytes) (i : Nat) : Bytes := (xorBytes T kb).take i ++ T.drop i

theorem tailPrefix_length (T kb : Bytes) (i : Nat) (hk : T.length ≤ kb.length) (hi : i ≤ T.length) :
    (tailPrefix T kb i).length = T.length := by
  simp [tailPrefix, xorBytes]; omega

theorem tailPrefix_getD (T kb : Bytes) (i : Nat) (hk : T.length ≤ kb.length) (hi : i < T.length) :
    (tailPrefix T kb i).getD i 0#8 = T.getD i 0#8 := by
  have hl : (xorBytes T kb).length = T.length := by simp [xorBytes]; omega
  simp only [tailPrefix, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_take, hl,
    Nat.min_eq_left (Nat.le_of_lt hi), List.getElem?_drop]
  simp

theorem tailPrefix_step (T kb : Bytes) (i : Nat) (hk : T.length ≤ kb.length) (hi : i < T.length) :
    ByteSlice.write8 (tailPrefix T kb i) i (kb.getD i 0#8 ^^^ T.getD i 0#8) = tailPrefix T kb (i + 1) := by
  have hl : (xorBytes T kb).length = T.length := by simp [xorBytes]; omega
  apply List.ext_getElem
  · rw [ByteSlice.write8_length _ _ _ (by rw [tailPrefix_length _ _ _ hk (by omega)]; omega),
      tailPrefix_length _ _ _ hk (by omega), tailPrefix_length _ _ _ hk (by omega)]
  · intro j h1 h2
    rw [List.getElem_eq_getD 0#8, List.getElem_eq_getD 0#8,
      ByteSlice.getD_write8 _ _ _ _ _ (by rw [tailPrefix_length _ _ _ hk (by omega)]; omega)]
    simp only [tailPrefix, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_take,
      List.length_take, List.getElem?_drop, hl]
    rw [Nat.min_eq_left (show i ≤ T.length by omega), Nat.min_eq_left (show i + 1 ≤ T.length by omega)]
    by_cases hj : j = i
    · subst hj
      simp [xorBytes, List.getElem?_zipWith, List.getElem?_eq_getElem (show j < T.length by omega),
        List.getElem?_eq_getElem (show j < kb.length by omega), BitVec.xor_comm]
    · rw [if_neg hj]
      by_cases hlt : j < i
      · simp [hlt, show j < i + 1 by omega]
      · rw [if_neg hlt, if_neg (by omega), show i + (j - i) = j by omega,
          show i + 1 + (j - (i + 1)) = j by omega]

theorem tailPrefix_full (T kb : Bytes) (hk : T.length ≤ kb.length) :
    tailPrefix T kb T.length = xorBytes T kb := by
  have hl : (xorBytes T kb).length = T.length := by simp [xorBytes]; omega
  rw [tailPrefix, List.drop_of_length_le (by omega), List.append_nil, List.take_of_length_le (by omega)]

/-- Registers the tail loop leaves alone. -/
def tailKeeps (sm st : Arm64.State) : Prop :=
  st.sp = sm.sp ∧ st.readReg64 .x21 = sm.readReg64 .x21 ∧ st.readReg64 .x22 = sm.readReg64 .x22 ∧
  st.readReg64 .x29 = sm.readReg64 .x29 ∧ calleeSavedVRegs st = calleeSavedVRegs sm

theorem tailLoop_ok [CpPlacement] (sm : Arm64.State) (D B : BitVec 64) (T kb : Bytes) (P : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x43c#64) (hrun : sm.status = .Running)
    (hT0 : 0 < T.length) (hT : T.length < 64) (hkb : kb.length = 64)
    (h19 : sm.readReg64 .x19 = D) (h20 : sm.readReg64 .x20 = B)
    (h8 : sm.readReg64 .x8 = BitVec.ofNat 64 T.length) :
    SepWP cpProg4r (cpPl4.base + 0x454#64) sm ((D ↦ₛ T) ∗ (B ↦ₛ kb) ∗ P)
      (sepPostState (fun st => tailKeeps sm st)
        (fun _ => (D ↦ₛ xorBytes T kb) ∗ (B ↦ₛ kb) ∗ P)) := by
  wp_loop_measure (T.length - 1) (fun m st =>
    m ≤ T.length - 1 ∧ st.readReg64 .x19 = D + BitVec.ofNat 64 (T.length - 1 - m) ∧
      st.readReg64 .x20 = B + BitVec.ofNat 64 (T.length - 1 - m) ∧
      st.readReg64 .x8 = BitVec.ofNat 64 (m + 1) ∧ tailKeeps sm st)
    (fun m _ => (D ↦ₛ tailPrefix T kb (T.length - 1 - m)) ∗ (B ↦ₛ kb) ∗ P)
  all_goals first
    | (simp [tailPrefix, tailKeeps, h19, h20, wp_norm, arm64_norm]; done)
    | (simp only [Nat.sub_self, Nat.sub_zero]; first | (simp [h8]; congr 1; omega) | skip)
    | skip
  case init => simp [tailPrefix]; exact Entails.refl _
  case base =>
    simp only [Nat.sub_zero, tailKeeps] at *
    have hl := tailPrefix_length T kb (T.length - 1) (by omega) (by omega)
    have hg := tailPrefix_getD T kb (T.length - 1) (by omega) (by omega)
    wp_steps
    rw [tailPrefix_step T kb _ (by omega) (by omega), show T.length - 1 + 1 = T.length by omega,
      tailPrefix_full T kb (by omega)]
    wp_done
  case step =>
    right
    simp only [tailKeeps] at *
    have hl := tailPrefix_length T kb (T.length - 1 - (m' + 1)) (by omega) (by omega)
    have hg := tailPrefix_getD T kb (T.length - 1 - (m' + 1)) (by omega) (by omega)
    have hne : BitVec.ofNat 64 (m' + 1 + 1) - 1#64 ≠ 0#64 := by bv_omega
    wp_steps
    rw [tailPrefix_step T kb _ (by omega) (by omega),
      show T.length - 1 - (m' + 1) + 1 = T.length - 1 - m' by omega]
    wp_done

end ChaChaPoly.Proofs
