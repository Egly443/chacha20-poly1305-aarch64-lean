module

public import ChaChaPoly.Proofs.DecryptMac
public import ChaChaPoly.Proofs.Helpers

/-!
# `chachapoly_decrypt` (block 5): the constant-time tag comparison

`0x3fc`–`0x594`: the sixteen bytes of the computed tag (at `x29 - 0x30`) are compared with the
received tag (at `x21`), each result passed through `subtle::black_box` (block 0), and the
conjunction passed through `black_box` once more. `dcmp_ok` shows the result is
`1` iff the two tags are equal.
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

theorem rho5_blackBox [CpPlacement] : cpPl5.ρ blackBoxSym = cpPl0.base := by
  have h : Obj.lookupBlockSym blackBoxSym chachapolyLib.blocks = some (0, 0) := by decide +kernel
  simp [cpPl5, cpPl0, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]

theorem bb_blk_ok [CpPlacement] :
    subroutine_ok (chachapolyLib.blockProgram cpMpl 0) cpPl0.base
      (chachapolyLib.withCodeLoaded cpMpl blackBoxContract) := blackBox_ok

theorem cset_eqb (x y : BitVec 8) :
    (if (BitVec.zeroExtend 32 x != BitVec.zeroExtend 32 y) = true then 0#64 else 1#64).truncate 8 =
      (BitVec.ofBool (x == y)).zeroExtend 8 := by
  by_cases h : x = y
  · subst h; simp
  · have : BitVec.zeroExtend 32 x ≠ BitVec.zeroExtend 32 y := by
      intro h'; apply h; bv_omega
    have hb : (x == y) = false := by simpa using h
    simp [hb, this]

theorem list_beq16 (T t : Bytes) (hT : T.length = 16) (ht : t.length = 16) :
    (T == t) = ((T.getD 0 0 == t.getD 0 0) && (T.getD 1 0 == t.getD 1 0) && (T.getD 2 0 == t.getD 2 0) && (T.getD 3 0 == t.getD 3 0) && (T.getD 4 0 == t.getD 4 0) && (T.getD 5 0 == t.getD 5 0) && (T.getD 6 0 == t.getD 6 0) && (T.getD 7 0 == t.getD 7 0) && (T.getD 8 0 == t.getD 8 0) && (T.getD 9 0 == t.getD 9 0) && (T.getD 10 0 == t.getD 10 0) && (T.getD 11 0 == t.getD 11 0) && (T.getD 12 0 == t.getD 12 0) && (T.getD 13 0 == t.getD 13 0) && (T.getD 14 0 == t.getD 14 0) && (T.getD 15 0 == t.getD 15 0)) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, Bool.and_eq_true]
  constructor
  · intro h; subst h; simp
  · intro h
    apply List.ext_getElem (by omega)
    intro i hi1 hi2
    have e1 : T[i] = T.getD i 0 := by simp [List.getD_eq_getElem?_getD, hi1]
    have e2 : t[i] = t.getD i 0 := by simp [List.getD_eq_getElem?_getD, hi2]
    rw [e1, e2]
    have hi : i < 16 := by omega
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := h
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
    | 8, _ => exact h8
    | 9, _ => exact h9
    | 10, _ => exact h10
    | 11, _ => exact h11
    | 12, _ => exact h12
    | 13, _ => exact h13
    | 14, _ => exact h14
    | 15, _ => exact h15
    | n + 16, h => omega

/-! Normal forms of the comparison's AND chain over the `0`/`1` bytes `black_box` returns. -/

theorem bb_and (p q : Bool) :
    (BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool p)) &&&
      BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool q))) =
      BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool (p && q))) := by
  cases p <;> cases q <;> rfl

theorem bb_and32 (p q : Bool) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool p))) &&&
      BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool q)))) =
      BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool (p && q)))) := by
  cases p <;> cases q <;> rfl

theorem bb_trunc (p : Bool) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool p)))) =
      BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool p)) := by
  cases p <;> rfl

theorem bb_one (p : Bool) :
    (BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool p)) &&& 1#64) =
      BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool p)) := by
  cases p <;> rfl

theorem bb_t8 (p : Bool) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool p))) =
      BitVec.zeroExtend 8 (BitVec.ofBool p) := by
  cases p <;> rfl

/-- What decrypt's tag comparison (`0x3fc`–`0x594`) leaves unchanged, and its result in `x0`. -/
def dcmpPost (sm sf : Arm64.State) (fp : BitVec 64) (T t : Bytes) : Prop :=
  sf.sp = sm.sp ∧ sf.readReg64 .x19 = sm.readReg64 .x19 ∧ sf.readReg64 .x23 = sm.readReg64 .x23 ∧
  sf.readReg64 .x24 = sm.readReg64 .x24 ∧ sf.readReg64 .x25 = sm.readReg64 .x25 ∧
  sf.readReg64 .x26 = sm.readReg64 .x26 ∧ sf.readReg64 .x27 = sm.readReg64 .x27 ∧
  sf.readReg64 .x28 = sm.readReg64 .x28 ∧ sf.readReg64 .x29 = fp ∧
  calleeSavedVRegs sf = calleeSavedVRegs sm ∧
  sf.readReg64 .x0 = BitVec.zeroExtend 64 (BitVec.zeroExtend 8 (BitVec.ofBool (T == t)))

/-- Decrypt's constant-time tag comparison: sixteen byte comparisons, each passed through
    `subtle::black_box`, AND-ed together and passed through `black_box` once more. The result
    in `x0` is `1` iff the computed tag `T` equals the received tag `t`. -/
theorem dcmp_ok [CpPlacement] (F : SepProp) (sm : Arm64.State) (tg fp : BitVec 64) (h29 : sm.readReg64 .x29 = fp) (T t : Bytes)
    (hpc : sm.pc = cpPl5.base + 0x3fc#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true) (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (h21 : sm.readReg64 .x21 = tg) (hT : T.length = 16) (ht : t.length = 16) :
    SepWP cpProg5r (cpPl5.base + 0x594#64) sm
      (((fp - 0x30#64) ↦ₛ T) ∗ (tg ↦ₛ t) ∗ memRegion (sm.sp - 16#64) 16 ∗ F)
      (sepPost (fun sf => dcmpPost sm sf fp T t)
        (((fp - 0x30#64) ↦ₛ T) ∗ (tg ↦ₛ t) ∗ memRegion (sm.sp - 16#64) 16 ∗ F)) := by
  have hρ := rho5_blackBox
  simp only [blackBoxSym] at hρ
  have hT' := hT
  have ht' := ht
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1040#64) hcl ?_
  wp_steps 5
  rw [show cpPl5.base + 1036#64 + (cpPl0.base - cpPl5.base - 1036#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 0 0 == t.getD 0 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1040#64) (F := ?F0)
    (by simpa [wp_norm, arm64_norm] using hcl) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s1 s1pc s1run s1sp s1cs
  obtain ⟨s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v⟩ := s1cs
  simp only [wp_norm, arm64_norm] at s1_19 s1_20 s1_21 s1_22 s1_23 s1_24 s1_25 s1_26 s1_27 s1_28 s1_29 s1_v s1sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s1pc]) s1run ?_
  intro hcl1
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s1_x0 => ?_
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1064#64) hcl1 ?_
  wp_steps 6
  rw [show cpPl5.base + 1060#64 + (cpPl0.base - cpPl5.base - 1060#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 1 0 == t.getD 1 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1064#64) (F := ?F1)
    (by simpa [wp_norm, arm64_norm] using hcl1) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl1 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl1⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s2 s2pc s2run s2sp s2cs
  obtain ⟨s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v⟩ := s2cs
  simp only [wp_norm, arm64_norm] at s2_19 s2_20 s2_21 s2_22 s2_23 s2_24 s2_25 s2_26 s2_27 s2_28 s2_29 s2_v s2sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s2pc]) s2run ?_
  intro hcl2
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s2_x0 => ?_
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_19
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_20
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_21
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_22
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_23
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_24
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_25
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_26
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_27
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_28
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_29
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2_v
  try simp only [wp_norm, arm64_norm, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_v, s1sp, s1_x0] at s2sp
  clear s1_19 s1_20 s1_21 s1_22 s1_23 s1_24 s1_25 s1_26 s1_27 s1_28 s1_29 s1_v s1sp s1_x0 s1pc s1run hcl1
  clear s1
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1088#64) hcl2 ?_
  wp_steps 6
  rw [show cpPl5.base + 1084#64 + (cpPl0.base - cpPl5.base - 1084#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 2 0 == t.getD 2 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1088#64) (F := ?F2)
    (by simpa [wp_norm, arm64_norm] using hcl2) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl2 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl2⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s3 s3pc s3run s3sp s3cs
  obtain ⟨s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v⟩ := s3cs
  simp only [wp_norm, arm64_norm] at s3_19 s3_20 s3_21 s3_22 s3_23 s3_24 s3_25 s3_26 s3_27 s3_28 s3_29 s3_v s3sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s3pc]) s3run ?_
  intro hcl3
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s3_x0 => ?_
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_19
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_20
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_21
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_22
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_23
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_24
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_25
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_26
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_27
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_28
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_29
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3_v
  try simp only [wp_norm, arm64_norm, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27, s2_28, s2_29, s2_v, s2sp, s2_x0] at s3sp
  clear s2_19 s2_20 s2_21 s2_22 s2_23 s2_24 s2_25 s2_26 s2_27 s2_28 s2_29 s2_v s2sp s2_x0 s2pc s2run hcl2
  clear s2
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1112#64) hcl3 ?_
  wp_steps 6
  rw [show cpPl5.base + 1108#64 + (cpPl0.base - cpPl5.base - 1108#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 3 0 == t.getD 3 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1112#64) (F := ?F3)
    (by simpa [wp_norm, arm64_norm] using hcl3) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl3 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl3⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s4 s4pc s4run s4sp s4cs
  obtain ⟨s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v⟩ := s4cs
  simp only [wp_norm, arm64_norm] at s4_19 s4_20 s4_21 s4_22 s4_23 s4_24 s4_25 s4_26 s4_27 s4_28 s4_29 s4_v s4sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s4pc]) s4run ?_
  intro hcl4
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s4_x0 => ?_
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_19
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_20
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_21
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_22
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_23
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_24
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_25
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_26
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_27
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_28
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_29
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4_v
  try simp only [wp_norm, arm64_norm, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27, s3_28, s3_29, s3_v, s3sp, s3_x0] at s4sp
  clear s3_19 s3_20 s3_21 s3_22 s3_23 s3_24 s3_25 s3_26 s3_27 s3_28 s3_29 s3_v s3sp s3_x0 s3pc s3run hcl3
  clear s3
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1140#64) hcl4 ?_
  wp_steps 7
  rw [show cpPl5.base + 1136#64 + (cpPl0.base - cpPl5.base - 1136#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 4 0 == t.getD 4 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1140#64) (F := ?F4)
    (by simpa [wp_norm, arm64_norm] using hcl4) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl4 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl4⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s5 s5pc s5run s5sp s5cs
  obtain ⟨s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v⟩ := s5cs
  simp only [wp_norm, arm64_norm] at s5_19 s5_20 s5_21 s5_22 s5_23 s5_24 s5_25 s5_26 s5_27 s5_28 s5_29 s5_v s5sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s5pc]) s5run ?_
  intro hcl5
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s5_x0 => ?_
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_19
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_20
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_21
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_22
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_23
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_24
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_25
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_26
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_27
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_28
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_29
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5_v
  try simp only [wp_norm, arm64_norm, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27, s4_28, s4_29, s4_v, s4sp, s4_x0] at s5sp
  clear s4_19 s4_20 s4_21 s4_22 s4_23 s4_24 s4_25 s4_26 s4_27 s4_28 s4_29 s4_v s4sp s4_x0 s4pc s4run hcl4
  clear s4
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1164#64) hcl5 ?_
  wp_steps 6
  rw [show cpPl5.base + 1160#64 + (cpPl0.base - cpPl5.base - 1160#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 5 0 == t.getD 5 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1164#64) (F := ?F5)
    (by simpa [wp_norm, arm64_norm] using hcl5) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl5 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl5⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s6 s6pc s6run s6sp s6cs
  obtain ⟨s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v⟩ := s6cs
  simp only [wp_norm, arm64_norm] at s6_19 s6_20 s6_21 s6_22 s6_23 s6_24 s6_25 s6_26 s6_27 s6_28 s6_29 s6_v s6sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s6pc]) s6run ?_
  intro hcl6
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s6_x0 => ?_
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_19
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_20
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_21
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_22
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_23
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_24
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_25
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_26
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_27
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_28
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_29
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6_v
  try simp only [wp_norm, arm64_norm, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27, s5_28, s5_29, s5_v, s5sp, s5_x0] at s6sp
  clear s5_19 s5_20 s5_21 s5_22 s5_23 s5_24 s5_25 s5_26 s5_27 s5_28 s5_29 s5_v s5sp s5_x0 s5pc s5run hcl5
  clear s5
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1188#64) hcl6 ?_
  wp_steps 6
  rw [show cpPl5.base + 1184#64 + (cpPl0.base - cpPl5.base - 1184#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 6 0 == t.getD 6 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1188#64) (F := ?F6)
    (by simpa [wp_norm, arm64_norm] using hcl6) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl6 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl6⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s7 s7pc s7run s7sp s7cs
  obtain ⟨s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v⟩ := s7cs
  simp only [wp_norm, arm64_norm] at s7_19 s7_20 s7_21 s7_22 s7_23 s7_24 s7_25 s7_26 s7_27 s7_28 s7_29 s7_v s7sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s7pc]) s7run ?_
  intro hcl7
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s7_x0 => ?_
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_19
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_20
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_21
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_22
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_23
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_24
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_25
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_26
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_27
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_28
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_29
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7_v
  try simp only [wp_norm, arm64_norm, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27, s6_28, s6_29, s6_v, s6sp, s6_x0] at s7sp
  clear s6_19 s6_20 s6_21 s6_22 s6_23 s6_24 s6_25 s6_26 s6_27 s6_28 s6_29 s6_v s6sp s6_x0 s6pc s6run hcl6
  clear s6
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1216#64) hcl7 ?_
  wp_steps 7
  rw [show cpPl5.base + 1212#64 + (cpPl0.base - cpPl5.base - 1212#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 7 0 == t.getD 7 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1216#64) (F := ?F7)
    (by simpa [wp_norm, arm64_norm] using hcl7) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl7 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl7⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s8 s8pc s8run s8sp s8cs
  obtain ⟨s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v⟩ := s8cs
  simp only [wp_norm, arm64_norm] at s8_19 s8_20 s8_21 s8_22 s8_23 s8_24 s8_25 s8_26 s8_27 s8_28 s8_29 s8_v s8sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s8pc]) s8run ?_
  intro hcl8
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s8_x0 => ?_
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_19
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_20
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_21
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_22
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_23
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_24
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_25
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_26
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_27
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_28
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_29
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8_v
  try simp only [wp_norm, arm64_norm, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27, s7_28, s7_29, s7_v, s7sp, s7_x0] at s8sp
  clear s7_19 s7_20 s7_21 s7_22 s7_23 s7_24 s7_25 s7_26 s7_27 s7_28 s7_29 s7_v s7sp s7_x0 s7pc s7run hcl7
  clear s7
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1240#64) hcl8 ?_
  wp_steps 6
  rw [show cpPl5.base + 1236#64 + (cpPl0.base - cpPl5.base - 1236#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 8 0 == t.getD 8 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1240#64) (F := ?F8)
    (by simpa [wp_norm, arm64_norm] using hcl8) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl8 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl8⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s9 s9pc s9run s9sp s9cs
  obtain ⟨s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v⟩ := s9cs
  simp only [wp_norm, arm64_norm] at s9_19 s9_20 s9_21 s9_22 s9_23 s9_24 s9_25 s9_26 s9_27 s9_28 s9_29 s9_v s9sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s9pc]) s9run ?_
  intro hcl9
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s9_x0 => ?_
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_19
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_20
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_21
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_22
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_23
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_24
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_25
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_26
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_27
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_28
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_29
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9_v
  try simp only [wp_norm, arm64_norm, s8_19, s8_20, s8_21, s8_22, s8_23, s8_24, s8_25, s8_26, s8_27, s8_28, s8_29, s8_v, s8sp, s8_x0] at s9sp
  clear s8_19 s8_20 s8_21 s8_22 s8_23 s8_24 s8_25 s8_26 s8_27 s8_28 s8_29 s8_v s8sp s8_x0 s8pc s8run hcl8
  clear s8
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1264#64) hcl9 ?_
  wp_steps 6
  rw [show cpPl5.base + 1260#64 + (cpPl0.base - cpPl5.base - 1260#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 9 0 == t.getD 9 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1264#64) (F := ?F9)
    (by simpa [wp_norm, arm64_norm] using hcl9) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl9 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl9⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s10 s10pc s10run s10sp s10cs
  obtain ⟨s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v⟩ := s10cs
  simp only [wp_norm, arm64_norm] at s10_19 s10_20 s10_21 s10_22 s10_23 s10_24 s10_25 s10_26 s10_27 s10_28 s10_29 s10_v s10sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s10pc]) s10run ?_
  intro hcl10
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s10_x0 => ?_
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_19
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_20
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_21
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_22
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_23
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_24
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_25
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_26
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_27
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_28
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_29
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10_v
  try simp only [wp_norm, arm64_norm, s9_19, s9_20, s9_21, s9_22, s9_23, s9_24, s9_25, s9_26, s9_27, s9_28, s9_29, s9_v, s9sp, s9_x0] at s10sp
  clear s9_19 s9_20 s9_21 s9_22 s9_23 s9_24 s9_25 s9_26 s9_27 s9_28 s9_29 s9_v s9sp s9_x0 s9pc s9run hcl9
  clear s9
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1288#64) hcl10 ?_
  wp_steps 6
  rw [show cpPl5.base + 1284#64 + (cpPl0.base - cpPl5.base - 1284#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 10 0 == t.getD 10 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1288#64) (F := ?F10)
    (by simpa [wp_norm, arm64_norm] using hcl10) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl10 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl10⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s11 s11pc s11run s11sp s11cs
  obtain ⟨s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v⟩ := s11cs
  simp only [wp_norm, arm64_norm] at s11_19 s11_20 s11_21 s11_22 s11_23 s11_24 s11_25 s11_26 s11_27 s11_28 s11_29 s11_v s11sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s11pc]) s11run ?_
  intro hcl11
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s11_x0 => ?_
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_19
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_20
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_21
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_22
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_23
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_24
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_25
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_26
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_27
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_28
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_29
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11_v
  try simp only [wp_norm, arm64_norm, s10_19, s10_20, s10_21, s10_22, s10_23, s10_24, s10_25, s10_26, s10_27, s10_28, s10_29, s10_v, s10sp, s10_x0] at s11sp
  clear s10_19 s10_20 s10_21 s10_22 s10_23 s10_24 s10_25 s10_26 s10_27 s10_28 s10_29 s10_v s10sp s10_x0 s10pc s10run hcl10
  clear s10
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1316#64) hcl11 ?_
  wp_steps 7
  rw [show cpPl5.base + 1312#64 + (cpPl0.base - cpPl5.base - 1312#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 11 0 == t.getD 11 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1316#64) (F := ?F11)
    (by simpa [wp_norm, arm64_norm] using hcl11) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl11 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl11⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s12 s12pc s12run s12sp s12cs
  obtain ⟨s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v⟩ := s12cs
  simp only [wp_norm, arm64_norm] at s12_19 s12_20 s12_21 s12_22 s12_23 s12_24 s12_25 s12_26 s12_27 s12_28 s12_29 s12_v s12sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s12pc]) s12run ?_
  intro hcl12
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s12_x0 => ?_
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_19
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_20
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_21
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_22
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_23
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_24
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_25
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_26
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_27
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_28
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_29
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12_v
  try simp only [wp_norm, arm64_norm, s11_19, s11_20, s11_21, s11_22, s11_23, s11_24, s11_25, s11_26, s11_27, s11_28, s11_29, s11_v, s11sp, s11_x0] at s12sp
  clear s11_19 s11_20 s11_21 s11_22 s11_23 s11_24 s11_25 s11_26 s11_27 s11_28 s11_29 s11_v s11sp s11_x0 s11pc s11run hcl11
  clear s11
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1340#64) hcl12 ?_
  wp_steps 6
  rw [show cpPl5.base + 1336#64 + (cpPl0.base - cpPl5.base - 1336#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 12 0 == t.getD 12 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1340#64) (F := ?F12)
    (by simpa [wp_norm, arm64_norm] using hcl12) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl12 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl12⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s13 s13pc s13run s13sp s13cs
  obtain ⟨s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v⟩ := s13cs
  simp only [wp_norm, arm64_norm] at s13_19 s13_20 s13_21 s13_22 s13_23 s13_24 s13_25 s13_26 s13_27 s13_28 s13_29 s13_v s13sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s13pc]) s13run ?_
  intro hcl13
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s13_x0 => ?_
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_19
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_20
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_21
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_22
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_23
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_24
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_25
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_26
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_27
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_28
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_29
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13_v
  try simp only [wp_norm, arm64_norm, s12_19, s12_20, s12_21, s12_22, s12_23, s12_24, s12_25, s12_26, s12_27, s12_28, s12_29, s12_v, s12sp, s12_x0] at s13sp
  clear s12_19 s12_20 s12_21 s12_22 s12_23 s12_24 s12_25 s12_26 s12_27 s12_28 s12_29 s12_v s12sp s12_x0 s12pc s12run hcl12
  clear s12
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1364#64) hcl13 ?_
  wp_steps 6
  rw [show cpPl5.base + 1360#64 + (cpPl0.base - cpPl5.base - 1360#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 13 0 == t.getD 13 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1364#64) (F := ?F13)
    (by simpa [wp_norm, arm64_norm] using hcl13) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl13 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl13⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s14 s14pc s14run s14sp s14cs
  obtain ⟨s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v⟩ := s14cs
  simp only [wp_norm, arm64_norm] at s14_19 s14_20 s14_21 s14_22 s14_23 s14_24 s14_25 s14_26 s14_27 s14_28 s14_29 s14_v s14sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s14pc]) s14run ?_
  intro hcl14
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s14_x0 => ?_
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_19
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_20
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_21
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_22
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_23
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_24
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_25
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_26
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_27
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_28
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_29
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14_v
  try simp only [wp_norm, arm64_norm, s13_19, s13_20, s13_21, s13_22, s13_23, s13_24, s13_25, s13_26, s13_27, s13_28, s13_29, s13_v, s13sp, s13_x0] at s14sp
  clear s13_19 s13_20 s13_21 s13_22 s13_23 s13_24 s13_25 s13_26 s13_27 s13_28 s13_29 s13_v s13sp s13_x0 s13pc s13run hcl13
  clear s13
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1388#64) hcl14 ?_
  wp_steps 6
  rw [show cpPl5.base + 1384#64 + (cpPl0.base - cpPl5.base - 1384#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 14 0 == t.getD 14 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1388#64) (F := ?F14)
    (by simpa [wp_norm, arm64_norm] using hcl14) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl14 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl14⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s15 s15pc s15run s15sp s15cs
  obtain ⟨s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v⟩ := s15cs
  simp only [wp_norm, arm64_norm] at s15_19 s15_20 s15_21 s15_22 s15_23 s15_24 s15_25 s15_26 s15_27 s15_28 s15_29 s15_v s15sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s15pc]) s15run ?_
  intro hcl15
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s15_x0 => ?_
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_19
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_20
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_21
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_22
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_23
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_24
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_25
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_26
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_27
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_28
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_29
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15_v
  try simp only [wp_norm, arm64_norm, s14_19, s14_20, s14_21, s14_22, s14_23, s14_24, s14_25, s14_26, s14_27, s14_28, s14_29, s14_v, s14sp, s14_x0] at s15sp
  clear s14_19 s14_20 s14_21 s14_22 s14_23 s14_24 s14_25 s14_26 s14_27 s14_28 s14_29 s14_v s14sp s14_x0 s14pc s14run hcl14
  clear s14
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1412#64) hcl15 ?_
  wp_steps 6
  rw [show cpPl5.base + 1408#64 + (cpPl0.base - cpPl5.base - 1408#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T.getD 15 0 == t.getD 15 0)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1412#64) (F := ?F15)
    (by simpa [wp_norm, arm64_norm] using hcl15) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl15 ⊢
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], hcl15⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s16 s16pc s16run s16sp s16cs
  obtain ⟨s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v⟩ := s16cs
  simp only [wp_norm, arm64_norm] at s16_19 s16_20 s16_21 s16_22 s16_23 s16_24 s16_25 s16_26 s16_27 s16_28 s16_29 s16_v s16sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s16pc]) s16run ?_
  intro hcl16
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s16_x0 => ?_
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_19
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_20
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_21
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_22
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_23
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_24
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_25
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_26
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_27
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_28
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_29
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16_v
  try simp only [wp_norm, arm64_norm, s15_19, s15_20, s15_21, s15_22, s15_23, s15_24, s15_25, s15_26, s15_27, s15_28, s15_29, s15_v, s15sp, s15_x0] at s16sp
  clear s15_19 s15_20 s15_21 s15_22 s15_23 s15_24 s15_25 s15_26 s15_27 s15_28 s15_29 s15_v s15sp s15_x0 s15pc s15run hcl15
  clear s15
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 1428#64) hcl16 ?_
  wp_steps 4
  rw [show cpPl5.base + 1424#64 + (cpPl0.base - cpPl5.base - 1424#64) = cpPl0.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 0) (by decide) bb_blk_ok
    (x := (BitVec.ofBool (T == t)).zeroExtend 8)
    (ret_pc := cpPl5.base + 1428#64) (F := ?F16)
    (by simpa [wp_norm, arm64_norm] using hcl16) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm, State.spAligned, *])
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, cset_eqb, stackFrame] at hm hcl16 ⊢
    refine ⟨⟨by (try simp only [wp_norm, arm64_norm, *]); rw [list_beq16 T t hT ht]; generalize (T.getD 0 0 == t.getD 0 0) = b0; generalize (T.getD 1 0 == t.getD 1 0) = b1; generalize (T.getD 2 0 == t.getD 2 0) = b2; generalize (T.getD 3 0 == t.getD 3 0) = b3; generalize (T.getD 4 0 == t.getD 4 0) = b4; generalize (T.getD 5 0 == t.getD 5 0) = b5; generalize (T.getD 6 0 == t.getD 6 0) = b6; generalize (T.getD 7 0 == t.getD 7 0) = b7; generalize (T.getD 8 0 == t.getD 8 0) = b8; generalize (T.getD 9 0 == t.getD 9 0) = b9; generalize (T.getD 10 0 == t.getD 10 0) = b10; generalize (T.getD 11 0 == t.getD 11 0) = b11; generalize (T.getD 12 0 == t.getD 12 0) = b12; generalize (T.getD 13 0 == t.getD 13 0) = b13; generalize (T.getD 14 0 == t.getD 14 0) = b14; generalize (T.getD 15 0 == t.getD 15 0) = b15; simp only [bb_and, bb_and32, bb_trunc, bb_one, bb_t8, Bool.and_assoc], hcl16⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  intro s17 s17pc s17run s17sp s17cs
  obtain ⟨s17_19, s17_20, s17_21, s17_22, s17_23, s17_24, s17_25, s17_26, s17_27, s17_28, s17_29, s17_v⟩ := s17cs
  simp only [wp_norm, arm64_norm] at s17_19 s17_20 s17_21 s17_22 s17_23 s17_24 s17_25 s17_26 s17_27 s17_28 s17_29 s17_v s17sp
  simp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  refine SepWP.done (by simp [wp_norm, arm64_norm, s17pc]) s17run ?_
  intro hcl17
  show SepWP cpProg5r _ _ _ _ _
  simp only [stackFrame, wp_norm, arm64_norm, *]
  refine SepWP.pure_elim fun s17_x0 => ?_
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_19
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_20
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_21
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_22
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_23
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_24
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_25
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_26
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_27
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_28
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_29
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17_v
  try simp only [wp_norm, arm64_norm, s16_19, s16_20, s16_21, s16_22, s16_23, s16_24, s16_25, s16_26, s16_27, s16_28, s16_29, s16_v, s16sp, s16_x0] at s17sp
  clear s16_19 s16_20 s16_21 s16_22 s16_23 s16_24 s16_25 s16_26 s16_27 s16_28 s16_29 s16_v s16sp s16_x0 s16pc s16run hcl16
  clear s16
  refine SepWP.done (by simp [wp_norm, arm64_norm, s17pc]) s17run ?_
  refine ⟨by simp only [dcmpPost, wp_norm, arm64_norm, *], ?_⟩
  sep_entail

end ChaChaPoly.Proofs
