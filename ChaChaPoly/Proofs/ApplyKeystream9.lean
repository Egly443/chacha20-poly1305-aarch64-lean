module

public import ChaChaPoly.Proofs.ApplyKeystream8

/-!
# `apply_keystream` (block 4), part 9: the tail segment

From offset `0x420`, with `t = len mod 64 > 0` bytes left: compute the tail address
`buf + (len & !63)`, call `write_keystream_block` (block 3) on the cipher state, then XOR the
`t` bytes with the fresh key-stream block (`tailLoop_ok`).
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
arm64_proof_prelude

theorem mask_eq (y : BitVec 64) (h : y.ult 0x8000000000000000#64 = true) :
    y &&& 0x7fffffffffffffc0#64 = y >>> 6 <<< 6 := by
  revert h; bv_robdd
theorem mask_val (nb t : Nat) (ht : t < 64) (hL : 64 * nb + t < 2 ^ 63) :
    BitVec.ofNat 64 (64 * nb + t) &&& 0x7fffffffffffffc0#64 = BitVec.ofNat 64 (64 * nb) := by
  rw [mask_eq _ (by simp [BitVec.ult]; omega)]
  bv_omega

theorem chachaBlock_blk_ok [CpPlacement] :
    subroutine_ok (chachapolyLib.blockProgram cpMpl 3) cpPl3.base
      (chachapolyLib.withCodeLoaded cpMpl chachaBlockSpec) := chachaBlock_ok

theorem tailSeg_ok [CpPlacement] (sm : Arm64.State) (c bufp : BitVec 64) (s buf : Spec.State)
    (nb : Nat) (T : Bytes) (F : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x420#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true) (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (h21 : sm.readReg64 .x21 = c) (h1 : sm.readReg64 .x1 = bufp)
    (h2 : sm.readReg64 .x2 = BitVec.ofNat 64 (64 * nb + T.length))
    (h22 : sm.readReg64 .x22 = BitVec.ofNat 64 T.length)
    (hT0 : 0 < T.length) (hT : T.length < 64) (hL : 64 * nb + T.length < 2 ^ 63) :
    SepWP cpProg4r (cpPl4.base + 0x454#64) sm
      (stateAt c s ∗ stateAt (c + 0x40#64) buf ∗ ((bufp + BitVec.ofNat 64 (64 * nb)) ↦ₛ T) ∗
        memRegion (sm.sp - 0x90#64) 0x90 ∗ F)
      (sepPost (fun sm' => sm'.sp = sm.sp ∧ sm'.readReg64 .x21 = c ∧
          sm'.readReg64 .x22 = BitVec.ofNat 64 T.length)
        (stateAt c { s with x12 := s.x12 + 1 } ∗ stateAt (c + 0x40#64) ((iter doubleRound 10 s).add s) ∗
          ((bufp + BitVec.ofNat 64 (64 * nb)) ↦ₛ xorBytes T (stateBlock s)) ∗
          memRegion (sm.sp - 0x90#64) 0x90 ∗ F)) := by
  have hm := mask_val nb T.length hT hL
  have hr : cpPl4.ρ "<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>> as cipher::stream_core::StreamCipherCore>::write_keystream_block" = cpPl3.base := by
    have h : Obj.lookupBlockSym "<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>> as cipher::stream_core::StreamCipherCore>::write_keystream_block" chachapolyLib.blocks = some (3, 0) := by decide +kernel
    simp [cpPl4, cpPl3, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]
  wp_steps 6
  rw [show cpPl4.base + 1076#64 + (cpPl3.base - cpPl4.base - 1076#64) = cpPl3.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 4) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 3) (by decide) chachaBlock_blk_ok
    (x := (c, c + 0x40#64, s, buf)) (ret_pc := cpPl4.base + 0x438#64) (F := ((bufp + BitVec.ofNat 64 (64 * nb)) ↦ₛ T) ∗ F)
    (by simpa [wp_norm, arm64_norm] using hcl) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, State.spAligned, hsp])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, chachaBlockSpec, stackFrame]
    simp only [wp_norm, arm64_norm, hcl, and_self, pure_true_sepConj, sepConj_pure_true]
    exact Satisfies.of_entails hm (by sep_entail)
  · intro sf hpcf hrunf hspf hcsf
    simp only [MultiPlacedLib.withCodeLoaded, chachaBlockSpec, stackFrame, wp_norm, arm64_norm] at hspf ⊢
    obtain ⟨c19, c20, c21, c22, -⟩ := hcsf
    simp only [wp_norm, arm64_norm] at c19 c20 c21 c22
    show SepWP cpProg4r _ _ _ _ _
    wp_step
    rw [stateAt_eq_bytes (c + 64#64)]
    refine SepWP.mono (SepWP.weaken_pre (by unfold stateBlock; sep_entail) (tailLoop_ok
      ((sf.writeReg64 (Reg.gpr 8#5) (BitVec.ofNat 64 T.length)).setPC (cpPl4.base + 1084#64))
      (bufp + BitVec.ofNat 64 (64 * nb)) (c + 64#64) T
      (stateBlock s) (stateAt c { s with x12 := s.x12 + 1 } ∗ memRegion (sm.sp - 144#64) 144 ∗ F)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf]) hT0 hT (stateBlock_length s)
      (by simp [wp_norm, arm64_norm, c19]) (by simp [wp_norm, arm64_norm, c20])
      (by simp [wp_norm, arm64_norm]))) ?_
    intro st Pf _ _ hst
    simp only [sepPostState, sepPost] at hst ⊢
    obtain ⟨hk, hm'⟩ := hst
    simp only [tailKeeps, wp_norm, arm64_norm] at hk
    refine ⟨⟨by rw [hk.1, hspf], by rw [hk.2.1, c21, h21], by rw [hk.2.2.1, c22, h22]⟩,
      Entails.trans hm' (by unfold stateBlock; sep_entail)⟩

end ChaChaPoly.Proofs
