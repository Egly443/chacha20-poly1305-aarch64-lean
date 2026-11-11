module

public import ChaChaPoly.Proofs.ApplyKeystream6

/-!
# `apply_keystream` (block 4), part 7: the full-block loop

`outerLoop_ok`: from the loop head with no block done, after the loop exits (`0x410`) the first
`nb` blocks of the data are XORed with the key stream of `s` and the counter register holds
`(s.advance nb).x12`.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
arm64_proof_prelude

/-- The scratch area of the full-block loop with unspecified contents. -/
def akScratch (sp : BitVec 64) (tail len c : BitVec 64) (s : Spec.State) (n bufp : BitVec 64) : SepProp :=
  ∃∗ ctr : BitVec 32, ∃∗ ks : Spec.State, ∃∗ cpb : Bytes, ∃∗ ob : Bytes,
    ⌜cpb.length = 64 ∧ ob.length = 64⌝ ∗
    akSlots sp tail len c s n bufp ctr ∗ stateAt (sp + 0x70#64) ks ∗ ((sp + 0xb0#64) ↦ₛ cpb) ∗
    ((sp + 0xf0#64) ↦ₛ ob)

theorem akScratch_open {prog : Program} {t : BitVec 64} {st : Arm64.State} {post : Arm64.State → SepProp → Prop}
    {oom : Arm64.State → SepProp} (sp tail len c : BitVec 64) (s : Spec.State) (n bufp : BitVec 64)
    (R : SepProp)
    (h : ∀ ctr ks cpb ob, cpb.length = 64 → ob.length = 64 →
      SepWP prog t st ((akSlots sp tail len c s n bufp ctr ∗ stateAt (sp + 0x70#64) ks ∗
        ((sp + 0xb0#64) ↦ₛ cpb) ∗ ((sp + 0xf0#64) ↦ₛ ob)) ∗ R) post oom) :
    SepWP prog t st (akScratch sp tail len c s n bufp ∗ R) post oom := by
  unfold akScratch
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun ctr => SepWP.exists_elim fun ks => SepWP.exists_elim fun cpb =>
    SepWP.exists_elim fun ob => ?_
  rw [sepConj_assoc]
  exact SepWP.pure_elim fun ⟨h1, h2⟩ => h ctr ks cpb ob h1 h2

theorem akScratch_close (sp tail len c : BitVec 64) (s : Spec.State) (n bufp : BitVec 64)
    (ctr : BitVec 32) (ks : Spec.State) (cpb ob : Bytes) (h1 : cpb.length = 64) (h2 : ob.length = 64) :
    (akSlots sp tail len c s n bufp ctr ∗ stateAt (sp + 0x70#64) ks ∗
        ((sp + 0xb0#64) ↦ₛ cpb) ∗ ((sp + 0xf0#64) ↦ₛ ob)) ⊢ akScratch sp tail len c s n bufp := by
  unfold akScratch
  refine Entails.trans ?_ (Entails.sepExists_intro ctr)
  refine Entails.trans ?_ (Entails.sepExists_intro ks)
  refine Entails.trans ?_ (Entails.sepExists_intro cpb)
  refine Entails.trans ?_ (Entails.sepExists_intro ob)
  rw [pure_sepConj_of_true ⟨h1, h2⟩]
  exact Entails.refl _

theorem regsO_setPC (sm : Arm64.State) (p : BitVec 64) (c : Spec.State) :
    regsO (sm.setPC p) c = regsO sm c := by
  simp only [regsO, wp_norm, arm64_norm]

attribute [local irreducible] regsO
attribute [irreducible] akScratch

theorem outerLoop_ok [CpPlacement] (sm : Arm64.State) (s : Spec.State) (tail len c bufp : BitVec 64)
    (nb : Nat) (data : Bytes) (F : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x144#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true)
    (hregs : regsO sm s) (h10 : sm.readReg64 .x10 = 0#64)
    (h29 : sm.readReg64 .x29 = sm.sp + 0x140#64) (h22 : sm.readReg64 .x22 = sm.sp + 0xb0#64)
    (h23 : sm.readReg64 .x23 = sm.sp + 0x70#64) (h24 : sm.readReg64 .x24 = sm.sp + 0xf0#64)
    (hv0 : sm.readVReg128 0#5 = 0#128)
    (hnb : 0 < nb) (hk : 64 * nb ≤ data.length) (hL : data.length < 2 ^ 63) :
    SepWP cpProg4r (cpPl4.base + 0x410#64) sm
      (akScratch sm.sp tail len c s (BitVec.ofNat 64 nb) bufp ∗ (bufp ↦ₛ data) ∗ F)
      (sepPost (fun sm' => sm'.readReg64 .x27 = BitVec.zeroExtend 64 (s.advance nb).x12 ∧
          sm'.sp = sm.sp ∧ sm'.readReg64 .x29 = sm.readReg64 .x29)
        (akScratch sm.sp tail len c s (BitVec.ofNat 64 nb) bufp ∗ (bufp ↦ₛ akCur s data nb) ∗ F)) := by
  have hcur0 : akCur s data 0 = data := by simp [akCur, streamXor_nil]
  refine SepWP.weaken_pre (P' := akScratch sm.sp tail len c s (BitVec.ofNat 64 nb) bufp ∗
    (bufp ↦ₛ akCur s data 0) ∗ F) (by rw [hcur0]; exact Entails.refl _) ?_
  wp_loop_measure (nb - 1) (fun m st =>
    m ≤ nb - 1 ∧ regsO st (s.advance (nb - 1 - m)) ∧ st.sp = sm.sp ∧
      st.readReg64 .x10 = BitVec.ofNat 64 (nb - 1 - m) ∧ st.readReg64 .x29 = sm.readReg64 .x29 ∧
      st.readReg64 .x22 = sm.readReg64 .x22 ∧ st.readReg64 .x23 = sm.readReg64 .x23 ∧
      st.readReg64 .x24 = sm.readReg64 .x24 ∧ st.readVReg128 0#5 = 0#128)
    (fun m _ => akScratch sm.sp tail len c s (BitVec.ofNat 64 nb) bufp ∗
      (bufp ↦ₛ akCur s data (nb - 1 - m)) ∗ F)
  all_goals first
    | (simp only [Nat.sub_self, State.advance_zero]; first | assumption | simp [h10, hv0])
    | skip
  case base =>
    simp only [Nat.sub_zero] at *
    refine akScratch_open _ _ _ _ _ _ _ _ (fun ctr ks cpb ob h1 h2 => ?_)
    have hst : st.sp = sm.sp := by assumption
    have e29 : st.readReg64 .x29 = sm.readReg64 .x29 := by assumption
    have e22 : st.readReg64 .x22 = sm.readReg64 .x22 := by assumption
    have e23 : st.readReg64 .x23 = sm.readReg64 .x23 := by assumption
    have e24 : st.readReg64 .x24 = sm.readReg64 .x24 := by assumption
    have hO := outerStep_ok st s tail len c (BitVec.ofNat 64 nb) bufp (nb - 1) data ctr ks cpb ob F
      hpc_st hrun_st (by rw [hst]; exact hsp) (by assumption) (by assumption)
      (by rw [e29, h29, hst]) (by rw [e22, h22, hst]) (by rw [e23, h23, hst])
      (by rw [e24, h24, hst]) (by assumption) (by omega) hL h1 h2
    rw [hst] at hO
    simp only [sepConj_assoc]
    refine SepWP.seq hO ?_
    intro s1 Pm hpc1 hrun1 ⟨⟨hr1, h1sp, h129, h110, h18, h1ps, h122, h123, h124, h1v0⟩, hent⟩
    refine SepWP.weaken_pre hent ?_
    have hnb1 : BitVec.ofNat 64 (nb - 1) + 1#64 = BitVec.ofNat 64 nb := by bv_omega
    rw [hnb1] at h1ps
    rw [show nb - 1 + 1 = nb by omega] at hr1 ⊢
    wp_steps
    have hblk := blockOf_length data (64 * (nb - 1)) (by omega)
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) ?_
    refine ⟨⟨?_, by simpa [wp_norm, arm64_norm] using h1sp,
      by simpa [wp_norm, arm64_norm] using h129.trans e29⟩, ?_⟩
    · unfold regsO at hr1; simpa [wp_norm, arm64_norm] using hr1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · have hxl : (xorBytes (blockOf data (64 * (nb - 1))) (stateBlock (s.advance (nb - 1)))).length = 64 := by
        simp [xorBytes, hblk]
      have hc := akScratch_close sm.sp tail len c s (BitVec.ofNat 64 nb) bufp (s.advance (nb - 1)).x12
        ((iter doubleRound 10 (s.advance (nb - 1))).add (s.advance (nb - 1))) _ _ hblk hxl
      refine Entails.trans ?_ (sepConj_mono_left hc)
      exact Entails.of_eq_explicit (by simp only [sepConj_assoc])
  case step =>
    right
    refine akScratch_open _ _ _ _ _ _ _ _ (fun ctr ks cpb ob h1 h2 => ?_)
    have hst : st.sp = sm.sp := by assumption
    have e29 : st.readReg64 .x29 = sm.readReg64 .x29 := by assumption
    have e22 : st.readReg64 .x22 = sm.readReg64 .x22 := by assumption
    have e23 : st.readReg64 .x23 = sm.readReg64 .x23 := by assumption
    have e24 : st.readReg64 .x24 = sm.readReg64 .x24 := by assumption
    have hm : m' + 1 ≤ nb - 1 := by assumption
    have hO := outerStep_ok st s tail len c (BitVec.ofNat 64 nb) bufp (nb - 1 - (m' + 1)) data ctr ks cpb ob F
      hpc_st hrun_st (by rw [hst]; exact hsp) (by assumption) (by assumption)
      (by rw [e29, h29, hst]) (by rw [e22, h22, hst]) (by rw [e23, h23, hst])
      (by rw [e24, h24, hst]) (by assumption) (by omega) hL h1 h2
    rw [hst] at hO
    simp only [sepConj_assoc]
    refine SepWP.seq hO ?_
    intro s1 Pm hpc1 hrun1 ⟨⟨hr1, h1sp, h129, h110, h18, h1ps, h122, h123, h124, h1v0⟩, hent⟩
    refine SepWP.weaken_pre hent ?_
    have hk1 : (nb - 1 - (m' + 1)) + 1 = nb - 1 - m' := by omega
    have hnb1 : BitVec.ofNat 64 (nb - 1 - (m' + 1)) + 1#64 = BitVec.ofNat 64 (nb - 1 - m') := by bv_omega
    have hne : BitVec.ofNat 64 nb ≠ BitVec.ofNat 64 (nb - 1 - m') := by bv_omega
    rw [hnb1] at h1ps h110
    rw [hk1] at hr1 ⊢
    wp_steps
    have hblk := blockOf_length data (64 * (nb - 1 - (m' + 1))) (by omega)
    have hxl : (xorBytes (blockOf data (64 * (nb - 1 - (m' + 1)))) (stateBlock (s.advance (nb - 1 - (m' + 1))))).length = 64 := by
      simp [xorBytes, hblk]
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) ?_
    refine ⟨⟨by omega, by simp only [regsO_setPC]; exact hr1, by simpa [wp_norm, arm64_norm] using h1sp,
      by simpa [wp_norm, arm64_norm] using h110, by simpa [wp_norm, arm64_norm] using h129.trans e29,
      by simpa [wp_norm, arm64_norm] using h122.trans e22, by simpa [wp_norm, arm64_norm] using h123.trans e23,
      by simpa [wp_norm, arm64_norm] using h124.trans e24, by simpa [wp_norm, arm64_norm] using h1v0⟩, ?_⟩
    have hc := akScratch_close sm.sp tail len c s (BitVec.ofNat 64 nb) bufp (s.advance (nb - 1 - (m' + 1))).x12
      ((iter doubleRound 10 (s.advance (nb - 1 - (m' + 1)))).add (s.advance (nb - 1 - (m' + 1)))) _ _ hblk hxl
    refine Entails.trans ?_ (sepConj_mono_left hc)
    exact Entails.of_eq_explicit (by simp only [sepConj_assoc])

end ChaChaPoly.Proofs
