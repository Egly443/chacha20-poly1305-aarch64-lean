module

public import ChaChaPoly.Proofs.ApplyKeystream1

/-!
# `apply_keystream` (block 4), part 2: the 64-byte XOR loop

At offset `0x3cc` the full-block path XORs a copy of the data block (at `x22`) with the key-stream
block (at `x23`) into an output block (at `x24`), one byte per iteration.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
arm64_proof_prelude

/-- `ob` with its first `i` bytes replaced by `da[j] ^^^ ks[j]`. -/
def xorPrefix (ob da ks : Bytes) (i : Nat) : Bytes := (xorBytes da ks).take i ++ ob.drop i

theorem xorPrefix_length (ob da ks : Bytes) (i : Nat) (hob : ob.length = 64) (hda : da.length = 64)
    (hks : ks.length = 64) (hi : i ≤ 64) : (xorPrefix ob da ks i).length = 64 := by
  simp [xorPrefix, xorBytes, hob, hda, hks]; omega

theorem xorPrefix_step (ob da ks : Bytes) (i : Nat) (hob : ob.length = 64) (hda : da.length = 64)
    (hks : ks.length = 64) (hi : i < 64) :
    ByteSlice.write8 (xorPrefix ob da ks i) i (ks.getD i 0#8 ^^^ da.getD i 0#8) =
      xorPrefix ob da ks (i + 1) := by
  apply List.ext_getElem
  · rw [ByteSlice.write8_length _ _ _ (by rw [xorPrefix_length _ _ _ _ hob hda hks (by omega)]; omega),
      xorPrefix_length _ _ _ _ hob hda hks (by omega), xorPrefix_length _ _ _ _ hob hda hks (by omega)]
  · intro j h1 h2
    rw [List.getElem_eq_getD 0#8, List.getElem_eq_getD 0#8,
      ByteSlice.getD_write8 _ _ _ _ _ (by rw [xorPrefix_length _ _ _ _ hob hda hks (by omega)]; omega)]
    have hl : (xorBytes da ks).length = 64 := by simp [xorBytes, hda, hks]
    simp only [xorPrefix, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_take,
      List.length_take, List.getElem?_drop, hl]
    rw [Nat.min_eq_left (show i ≤ 64 by omega), Nat.min_eq_left (show i + 1 ≤ 64 by omega)]
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl, if_pos (by omega)]
      simp [xorBytes, List.getElem?_zipWith, List.getElem?_eq_getElem (show j < da.length by omega),
        List.getElem?_eq_getElem (show j < ks.length by omega), BitVec.xor_comm]
    · rw [if_neg hj]
      by_cases hlt : j < i
      · simp [hlt, show j < i + 1 by omega]
      · rw [if_neg hlt, if_neg (by omega), show i + (j - i) = j by omega,
          show i + 1 + (j - (i + 1)) = j by omega]

theorem xorPrefix_full (ob da ks : Bytes) (hob : ob.length = 64) (hda : da.length = 64)
    (hks : ks.length = 64) : xorPrefix ob da ks 64 = xorBytes da ks := by
  have hl : (xorBytes da ks).length = 64 := by simp [xorBytes, hda, hks]
  rw [xorPrefix, List.drop_of_length_le (by omega), List.append_nil, List.take_of_length_le (by omega)]

/-- Registers the XOR loop leaves alone (it writes only `x8`, `x9`, `x12`, `x25`). -/
def xorKeeps (sm st : Arm64.State) : Prop :=
  st.sp = sm.sp ∧ st.readReg64 .x0 = sm.readReg64 .x0 ∧
  st.readReg64 .x1 = sm.readReg64 .x1 ∧
  st.readReg64 .x2 = sm.readReg64 .x2 ∧
  st.readReg64 .x3 = sm.readReg64 .x3 ∧
  st.readReg64 .x4 = sm.readReg64 .x4 ∧
  st.readReg64 .x5 = sm.readReg64 .x5 ∧
  st.readReg64 .x6 = sm.readReg64 .x6 ∧
  st.readReg64 .x7 = sm.readReg64 .x7 ∧
  st.readReg64 .x10 = sm.readReg64 .x10 ∧
  st.readReg64 .x11 = sm.readReg64 .x11 ∧
  st.readReg64 .x13 = sm.readReg64 .x13 ∧
  st.readReg64 .x14 = sm.readReg64 .x14 ∧
  st.readReg64 .x15 = sm.readReg64 .x15 ∧
  st.readReg64 .x16 = sm.readReg64 .x16 ∧
  st.readReg64 .x17 = sm.readReg64 .x17 ∧
  st.readReg64 .x18 = sm.readReg64 .x18 ∧
  st.readReg64 .x19 = sm.readReg64 .x19 ∧
  st.readReg64 .x20 = sm.readReg64 .x20 ∧
  st.readReg64 .x21 = sm.readReg64 .x21 ∧
  st.readReg64 .x22 = sm.readReg64 .x22 ∧
  st.readReg64 .x23 = sm.readReg64 .x23 ∧
  st.readReg64 .x24 = sm.readReg64 .x24 ∧
  st.readReg64 .x26 = sm.readReg64 .x26 ∧
  st.readReg64 .x27 = sm.readReg64 .x27 ∧
  st.readReg64 .x28 = sm.readReg64 .x28 ∧
  st.readReg64 .x29 = sm.readReg64 .x29 ∧
  st.readReg64 .x30 = sm.readReg64 .x30 ∧
  st.readVReg128 0#5 = sm.readVReg128 0#5 ∧ calleeSavedVRegs st = calleeSavedVRegs sm

theorem xorLoop_ok [CpPlacement] (sm : Arm64.State) (A K O : BitVec 64) (da ks ob : Bytes) (P : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x3cc#64) (hrun : sm.status = .Running)
    (hda : da.length = 64) (hks : ks.length = 64) (hob : ob.length = 64)
    (h22 : sm.readReg64 .x22 = A) (h23 : sm.readReg64 .x23 = K) (h24 : sm.readReg64 .x24 = O)
    (h25 : sm.readReg64 .x25 = 0#64) :
    SepWP cpProg4r (cpPl4.base + 0x3ec#64) sm ((A ↦ₛ da) ∗ (K ↦ₛ ks) ∗ (O ↦ₛ ob) ∗ P)
      (sepPostState (fun st => st.readReg64 .x25 = 64#64 ∧ xorKeeps sm st)
        (fun _ => (A ↦ₛ da) ∗ (K ↦ₛ ks) ∗ (O ↦ₛ xorBytes da ks) ∗ P)) := by
  wp_loop_measure 63 (fun m st =>
    m ≤ 63 ∧ st.readReg64 .x25 = BitVec.ofNat 64 (63 - m) ∧ xorKeeps sm st)
    (fun m _ => (A ↦ₛ da) ∗ (K ↦ₛ ks) ∗ (O ↦ₛ xorPrefix ob da ks (63 - m)) ∗ P)
  case base =>
    simp only [Nat.sub_zero, xorKeeps] at *
    have hl : (xorPrefix ob da ks 63).length = 64 := xorPrefix_length _ _ _ _ hob hda hks (by omega)
    wp_steps
    rw [xorPrefix_step _ _ _ _ hob hda hks (by omega), xorPrefix_full _ _ _ hob hda hks]
    wp_done
  case step =>
    right
    simp only [xorKeeps] at *
    rw [show 63 - (m' + 1) = 62 - m' by omega] at *
    have hl : (xorPrefix ob da ks (62 - m')).length = 64 :=
      xorPrefix_length _ _ _ _ hob hda hks (by omega)
    have hne : BitVec.ofNat 64 (62 - m') + 1#64 ≠ 64#64 := by bv_omega
    wp_steps
    rw [xorPrefix_step _ _ _ _ hob hda hks (by omega)]
    rw [show 62 - m' + 1 = 63 - m' by omega]
    have h25' : BitVec.ofNat 64 (62 - m') + 1#64 = BitVec.ofNat 64 (63 - m') := by bv_omega
    wp_done

end ChaChaPoly.Proofs
