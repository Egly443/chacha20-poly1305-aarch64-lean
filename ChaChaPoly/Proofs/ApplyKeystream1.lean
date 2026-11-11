module

public import ChaChaPoly.Proofs.ChaChaBlock

/-!
# `StreamCipherCoreWrapper::apply_keystream` (block 4), part 1: the inlined double round

The full-block path of `apply_keystream` inlines the ChaCha20 block function. Its 10-iteration
double-round loop (head at offset `0x158`) keeps the sixteen state words in the registers of
`regsK`; after the column half (offset `0x21c`) they are in the registers of `regsKM`. Both
mappings were derived from the code and are checked here by the kernel.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
arm64_proof_prelude

/-- State words at the inner loop head. -/
def regsK (sm : Arm64.State) (c : Spec.State) : Prop :=
  sm.readReg64 .x13 = BitVec.zeroExtend 64 c.x0 ∧
  sm.readReg64 .x12 = BitVec.zeroExtend 64 c.x1 ∧
  sm.readReg64 .x11 = BitVec.zeroExtend 64 c.x2 ∧
  sm.readReg64 .x14 = BitVec.zeroExtend 64 c.x3 ∧
  sm.readReg64 .x15 = BitVec.zeroExtend 64 c.x4 ∧
  sm.readReg64 .x16 = BitVec.zeroExtend 64 c.x5 ∧
  sm.readReg64 .x17 = BitVec.zeroExtend 64 c.x6 ∧
  sm.readReg64 .x18 = BitVec.zeroExtend 64 c.x7 ∧
  sm.readReg64 .x0 = BitVec.zeroExtend 64 c.x8 ∧
  sm.readReg64 .x3 = BitVec.zeroExtend 64 c.x9 ∧
  sm.readReg64 .x4 = BitVec.zeroExtend 64 c.x10 ∧
  sm.readReg64 .x5 = BitVec.zeroExtend 64 c.x11 ∧
  sm.readReg64 .x27 = BitVec.zeroExtend 64 c.x12 ∧
  sm.readReg64 .x30 = BitVec.zeroExtend 64 c.x13 ∧
  sm.readReg64 .x28 = BitVec.zeroExtend 64 c.x14 ∧
  sm.readReg64 .x26 = BitVec.zeroExtend 64 c.x15

/-- State words after the column half round. -/
def regsKM (sm : Arm64.State) (c : Spec.State) : Prop :=
  sm.readReg64 .x6 = BitVec.zeroExtend 64 c.x0 ∧
  sm.readReg64 .x7 = BitVec.zeroExtend 64 c.x1 ∧
  sm.readReg64 .x21 = BitVec.zeroExtend 64 c.x2 ∧
  sm.readReg64 .x13 = BitVec.zeroExtend 64 c.x3 ∧
  sm.readReg64 .x15 = BitVec.zeroExtend 64 c.x4 ∧
  sm.readReg64 .x3 = BitVec.zeroExtend 64 c.x5 ∧
  sm.readReg64 .x4 = BitVec.zeroExtend 64 c.x6 ∧
  sm.readReg64 .x26 = BitVec.zeroExtend 64 c.x7 ∧
  sm.readReg64 .x12 = BitVec.zeroExtend 64 c.x8 ∧
  sm.readReg64 .x11 = BitVec.zeroExtend 64 c.x9 ∧
  sm.readReg64 .x18 = BitVec.zeroExtend 64 c.x10 ∧
  sm.readReg64 .x5 = BitVec.zeroExtend 64 c.x11 ∧
  sm.readReg64 .x16 = BitVec.zeroExtend 64 c.x12 ∧
  sm.readReg64 .x0 = BitVec.zeroExtend 64 c.x13 ∧
  sm.readReg64 .x17 = BitVec.zeroExtend 64 c.x14 ∧
  sm.readReg64 .x27 = BitVec.zeroExtend 64 c.x15

@[simp, wp_norm, arm64_norm] theorem regsK_setPC (sm : Arm64.State) (p : BitVec 64) (c : Spec.State) :
    regsK (sm.setPC p) c = regsK sm c := by
  simp only [regsK, wp_norm, arm64_norm]

attribute [irreducible] regsK regsKM

/-- What a half round of the inlined loop leaves alone: the stack pointer, frame pointer, the
    block index and the three buffer pointers. -/
def halfKeepsK (sm sm' : Arm64.State) : Prop :=
  sm'.sp = sm.sp ∧ sm'.readReg64 .x29 = sm.readReg64 .x29 ∧ sm'.readReg64 .x10 = sm.readReg64 .x10 ∧
  sm'.readReg64 .x22 = sm.readReg64 .x22 ∧ sm'.readReg64 .x23 = sm.readReg64 .x23 ∧
  sm'.readReg64 .x24 = sm.readReg64 .x24 ∧ calleeSavedVRegs sm' = calleeSavedVRegs sm ∧
  sm'.readVReg128 0#5 = sm.readVReg128 0#5

theorem colHalfK_ok [CpPlacement] (sm : Arm64.State) (c : Spec.State) (n : BitVec 64) (P : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x158#64) (hrun : sm.status = .Running)
    (hregs : regsK sm c) (h25 : sm.readReg64 .x25 = n) :
    SepWP cpProg4r (cpPl4.base + 0x21c#64) sm P
      (fun sm' P' => (regsKM sm' (colRound c) ∧ halfKeepsK sm sm' ∧
        sm'.readReg64 .x25 = n - 1#64 ∧ sm'.pstate = subsPState64 n 1#64) ∧ (P' ⊢ P)) := by
  unfold regsK at hregs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hregs
  wp_steps 49
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨?_, Entails.refl _⟩
  simp only [regsKM, halfKeepsK, colRound, qrA, qrB, qrC, qrD, wp_norm, arm64_norm]
  and_intros
  all_goals first | assumption | ac_rfl | trace_state

theorem diagHalfK_ok [CpPlacement] (sm : Arm64.State) (c : Spec.State) (P : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x21c#64) (hrun : sm.status = .Running)
    (hregs : regsKM sm c) :
    SepWP cpProg4r (cpPl4.base + 0x2dc#64) sm P
      (fun sm' P' => (regsK sm' (diagRound c) ∧ halfKeepsK sm sm' ∧
        sm'.readReg64 .x25 = sm.readReg64 .x25 ∧ sm'.pstate = sm.pstate) ∧ (P' ⊢ P)) := by
  unfold regsKM at hregs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hregs
  wp_steps 48
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨?_, Entails.refl _⟩
  simp only [regsK, halfKeepsK, diagRound, qrA, qrB, qrC, qrD, wp_norm, arm64_norm]
  and_intros
  all_goals first | assumption | ac_rfl | trace_state

/-- One double round of the inlined loop, up to (not including) the closing `b.ne`. -/
theorem bodyK_ok [CpPlacement] (sm : Arm64.State) (c : Spec.State) (n : BitVec 64) (P : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x158#64) (hrun : sm.status = .Running)
    (hregs : regsK sm c) (h25 : sm.readReg64 .x25 = n) :
    SepWP cpProg4r (cpPl4.base + 0x2dc#64) sm P
      (fun sm' P' => (regsK sm' (doubleRound c) ∧ halfKeepsK sm sm' ∧
        sm'.readReg64 .x25 = n - 1#64 ∧ sm'.pstate = subsPState64 n 1#64) ∧ (P' ⊢ P)) := by
  refine SepWP.seq_entails_emp (colHalfK_ok sm c n P hpc hrun hregs h25) ?_
  intro s1 hpc1 hrun1 ⟨hr1, hk1, h251, hps1⟩
  refine SepWP.mono (diagHalfK_ok s1 (colRound c) P hpc1 hrun1 hr1) ?_
  intro s2 P2 _ _ ⟨⟨hr2, hk2, h252, hps2⟩, hent⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hent⟩
  · rw [doubleRound_eq]; exact hr2
  · unfold halfKeepsK at *; simp_all
  · rw [h252, h251]
  · rw [hps2, hps1]

end ChaChaPoly.Proofs
