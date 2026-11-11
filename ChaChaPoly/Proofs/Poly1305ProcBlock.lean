module

public import ChaChaPoly.Proofs.Poly1305Block

/-!
# `proc_block` (block 9): `mov w2, #0; b compute_block`

The wrapper sets `partial = false` and tail-calls `compute_block` in block 7, so its contract
follows from `polyBlockContract_ok`.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
arm64_proof_prelude

theorem polyProcBlockContract_ok [CpPlacement] :
    subroutine_ok cpProg9r cpPl9.base (chachapolyLib.withCodeLoaded cpMpl polyProcBlockContract) := by
  have h7 := @polyBlockContract_ok _
  dsimp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract]
  wp_entry "<poly1305::backend::soft::State as universal_hash::UhfBackend>::proc_block" g s0
  obtain ⟨st, blk, bs, r, acc⟩ := g
  wp_steps
  have hpc7 : cpPl9.base + 4#64 + (cpPl9.ρ "<poly1305::backend::soft::State>::compute_block" - cpPl9.base - 4#64) =
      cpPl7.base := by
    have h : Obj.lookupBlockSym "<poly1305::backend::soft::State>::compute_block" chachapolyLib.blocks =
        some (7, 0) := by decide +kernel
    have hr : cpPl9.ρ "<poly1305::backend::soft::State>::compute_block" = cpPl7.base := by
      simp [cpPl9, cpPl7, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]
    rw [hr]; bv_omega
  rw [hpc7]
  refine MultiPlacedLib.sepWP_of_other_block (j := 7) (by decide) h ?_
  have h7' : subroutine_ok (chachapolyLib.blockProgram cpMpl 7) cpPl7.base
      (chachapolyLib.withCodeLoaded cpMpl polyBlockContract) := h7
  refine SepWP.call_subroutine_frame h7' (x := (st, blk, bs, r, acc)) (F := emp)
    (ret_pc := s0.readReg64 Reg.lr) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, State.spAligned, hsp_align])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  · intro R' hm
    simp only [MultiPlacedLib.withCodeLoaded, polyBlockContract, emp_sepConj]
    rw [sepConj_assoc, sepConj_comm ⌜_⌝ R', ← sepConj_assoc, sepConj_comm _ ⌜_⌝,
      satisfies_pure_sepConj]
    refine ⟨by simpa [wp_norm, arm64_norm] using h, ?_⟩
    refine Satisfies.of_entails hm (sepConj_mono_left ?_)
    refine Entails.trans ?_ (Entails.sepExists_intro v_stk)
    rw [pure_sepConj_of_true ⟨⟨by simp [wp_norm, arm64_norm, h_3], by simp [wp_norm, arm64_norm, h_4],
      by simp [wp_norm, arm64_norm], h_2⟩, h_1⟩]
    exact Entails.refl _
  · intro sf hpcf hrunf hspf hcsf
    refine SepWP.done hpcf hrunf ?_
    refine ⟨fun hm => ?_, ?_, ?_⟩
    · simpa [MultiPlacedLib.withCodeLoaded, polyBlockContract, sepConj_emp] using hm
    · simpa [wp_norm, arm64_norm] using hspf
    · refine CalleeSavedPreserved.trans ?_ hcsf
      unfold CalleeSavedPreserved
      simp [wp_norm, arm64_norm]

end ChaChaPoly.Proofs
