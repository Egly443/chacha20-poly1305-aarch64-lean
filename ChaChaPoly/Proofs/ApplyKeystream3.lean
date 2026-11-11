module

public import ChaChaPoly.Proofs.ApplyKeystream2

/-!
# `apply_keystream` (block 4), part 3: words↔bytes, and the outer-loop head to the end of the
# inlined rounds (segment A)
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
arm64_proof_prelude

theorem word32Bytes_eq (w : BitVec 32) :
    word32Bytes w = [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8] := rfl

theorem pointsTo32_eq_word32Bytes (a : BitVec 64) (w : BitVec 32) : (a ↦₃₂ w) = (a ↦ₛ word32Bytes w) := by
  rw [pointsTo32_eq_pointsToBytes]; rfl

theorem stateAt_eq_bytes (p : BitVec 64) (s : Spec.State) : stateAt p s = (p ↦ₛ s.bytes) := by
  have hb : ∀ w : BitVec 32, (word32Bytes w).length = 4 := fun _ => rfl
  simp only [Spec.State.bytes, pointsToBytes_append, List.length_append, hb]
  simp only [stateAt, pointsTo32_eq_word32Bytes, sepConj_assoc]

/-- Registers at the outer-loop head: the sixteen state words (words 0..2 in `x2, x6, x7`). -/
def regsO (sm : Arm64.State) (c : Spec.State) : Prop :=
  sm.readReg64 .x2 = BitVec.zeroExtend 64 c.x0 ∧ sm.readReg64 .x6 = BitVec.zeroExtend 64 c.x1 ∧
  sm.readReg64 .x7 = BitVec.zeroExtend 64 c.x2 ∧ sm.readReg64 .x14 = BitVec.zeroExtend 64 c.x3 ∧
  sm.readReg64 .x15 = BitVec.zeroExtend 64 c.x4 ∧ sm.readReg64 .x16 = BitVec.zeroExtend 64 c.x5 ∧
  sm.readReg64 .x17 = BitVec.zeroExtend 64 c.x6 ∧ sm.readReg64 .x18 = BitVec.zeroExtend 64 c.x7 ∧
  sm.readReg64 .x0 = BitVec.zeroExtend 64 c.x8 ∧ sm.readReg64 .x3 = BitVec.zeroExtend 64 c.x9 ∧
  sm.readReg64 .x4 = BitVec.zeroExtend 64 c.x10 ∧ sm.readReg64 .x5 = BitVec.zeroExtend 64 c.x11 ∧
  sm.readReg64 .x27 = BitVec.zeroExtend 64 c.x12 ∧ sm.readReg64 .x30 = BitVec.zeroExtend 64 c.x13 ∧
  sm.readReg64 .x28 = BitVec.zeroExtend 64 c.x14 ∧ sm.readReg64 .x26 = BitVec.zeroExtend 64 c.x15

theorem halfKeepsK_trans {a b c : Arm64.State} (h1 : halfKeepsK a b) (h2 : halfKeepsK b c) :
    halfKeepsK a c := by
  unfold halfKeepsK at *; obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
    b8.trans a8⟩

theorem halfKeepsK_setPC {a b : Arm64.State} (p : BitVec 64) (h : halfKeepsK a b) :
    halfKeepsK a (b.setPC p) := by
  unfold halfKeepsK at *; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using h

theorem segA_ok [CpPlacement] (sm : Arm64.State) (c : Spec.State) (old : BitVec 32) (F : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x144#64) (hrun : sm.status = .Running) (hsp : (sm.sp &&& 15#64 == 0#64) = true) (hregs : regsO sm c) :
    SepWP cpProg4r (cpPl4.base + 0x2e0#64) sm (((sm.sp + 0x6c#64) ↦₃₂ old) ∗ F)
      (fun sm' P' => (regsK sm' (iter doubleRound 10 c) ∧ halfKeepsK sm sm' ∧
          sm'.readReg64 .x25 = 0#64) ∧
        (P' ⊢ ((sm.sp + 0x6c#64) ↦₃₂ c.x12) ∗ F)) := by
  unfold regsO at hregs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hregs
  wp_steps 5
  wp_loop_measure 9 (fun k st =>
    k ≤ 9 ∧ st.readReg64 .x25 = BitVec.ofNat 64 (k + 1) ∧ halfKeepsK sm st ∧
    regsK st (iter doubleRound (9 - k) c))
  all_goals first
    | (simp [regsK, iter, halfKeepsK, calleeSavedVRegs, wp_norm, arm64_norm, h0, h1, h2, h3, h4, h5,
        h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]; done)
    | skip
  case base =>
    have hlast : iter doubleRound 10 c = doubleRound (iter doubleRound 9 c) := iter_succ' _ _ _
    refine SepWP.seq_entails_emp (bodyK_ok st _ _ _ hpc_st hrun_st hinv_st (by assumption)) ?_
    intro s2 hpc2 hrun2 ⟨hr2, hk2, h252, hps2⟩
    rw [← hlast] at hr2
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2]) ?_
    refine ⟨⟨by simpa using hr2, halfKeepsK_setPC _ (halfKeepsK_trans ‹halfKeepsK sm st› hk2), ?_⟩,
      Entails.refl _⟩
    simp [wp_norm, arm64_norm, h252, ‹st.readReg64 .x25 = _›]
  case step =>
    right
    have hnext : iter doubleRound (9 - m') c = doubleRound (iter doubleRound (8 - m') c) := by
      rw [show 9 - m' = (8 - m') + 1 by omega, iter_succ']
    refine SepWP.seq_entails_emp (bodyK_ok st _ _ _ hpc_st hrun_st hinv_st (by assumption)) ?_
    intro s2 hpc2 hrun2 ⟨hr2, hk2, h252, hps2⟩
    rw [← hnext] at hr2
    have hk_nz : BitVec.ofNat 64 (m' + 1 + 1) ≠ 1#64 := by bv_omega
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2]) ?_
    refine ⟨⟨by omega, ?_, halfKeepsK_setPC _ (halfKeepsK_trans ‹halfKeepsK sm st› hk2),
      by simpa using hr2⟩, Entails.refl _⟩
    simp [wp_norm, arm64_norm, h252, ‹st.readReg64 .x25 = _›]
    bv_omega

end ChaChaPoly.Proofs
