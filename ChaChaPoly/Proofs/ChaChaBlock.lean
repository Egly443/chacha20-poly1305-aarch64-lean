module

public import ChaChaPoly.Proofs.Code
public import ChaChaPoly.Spec.Contracts

/-!
# The ChaCha20 block function (`write_keystream_block`, block 3)

Machine-code proof that RustCrypto's `ChaChaCore::write_keystream_block` writes
`(doubleRound^10 s) + s` for the state `s` it is given and increments the block counter.
The loop body is cut at the column/diagonal boundary so that every proof obligation is one
quarter round deep.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
arm64_proof_prelude

theorem _root_.Arm64.SepWP.rw_pre {prog : Program} {t : BitVec 64} {s : Arm64.State} {P P' : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (h : P = P') (hwp : SepWP prog t s P' post oom) : SepWP prog t s P post oom := h ▸ hwp

theorem rotl32_eq (x : BitVec 32) (r l : Nat)
    (hl : l < 32 := by decide) (hrl : r + l = 32 := by rfl) :
    x.rotateLeft l = BitVec.truncate 32 ((x ++ x) >>> r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
      BitVec.getLsbD_rotateLeft_of_le hl]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hlt : i < l
  · have hlt2 : r + i < 32 := by omega
    simp only [hlt, hlt2, ↓reduceIte]
    congr 1
    omega
  · have hlt2 : ¬(r + i < 32) := by omega
    simp only [hlt, hlt2, ↓reduceIte]
    congr 1
    omega

theorem iter_succ' {α : Type} (f : α → α) (n : Nat) (a : α) : iter f (n + 1) a = f (iter f n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [iter, ih]; rfl

/-- The quarter round with rotations in the machine's form. -/
def qrA (a b c d : BitVec 32) : BitVec 32 :=
  let a1 := a + b; let d1 := BitVec.truncate 32 (((d ^^^ a1) ++ (d ^^^ a1)) >>> 16)
  let c1 := c + d1; let b1 := BitVec.truncate 32 (((b ^^^ c1) ++ (b ^^^ c1)) >>> 20)
  a1 + b1
def qrD (a b c d : BitVec 32) : BitVec 32 :=
  let a1 := a + b; let d1 := BitVec.truncate 32 (((d ^^^ a1) ++ (d ^^^ a1)) >>> 16)
  let c1 := c + d1; let b1 := BitVec.truncate 32 (((b ^^^ c1) ++ (b ^^^ c1)) >>> 20)
  let a2 := a1 + b1; BitVec.truncate 32 (((d1 ^^^ a2) ++ (d1 ^^^ a2)) >>> 24)
def qrC (a b c d : BitVec 32) : BitVec 32 :=
  let a1 := a + b; let d1 := BitVec.truncate 32 (((d ^^^ a1) ++ (d ^^^ a1)) >>> 16)
  let c1 := c + d1
  c1 + qrD a b c d
def qrB (a b c d : BitVec 32) : BitVec 32 :=
  let a1 := a + b; let d1 := BitVec.truncate 32 (((d ^^^ a1) ++ (d ^^^ a1)) >>> 16)
  let c1 := c + d1; let b1 := BitVec.truncate 32 (((b ^^^ c1) ++ (b ^^^ c1)) >>> 20)
  BitVec.truncate 32 (((b1 ^^^ qrC a b c d) ++ (b1 ^^^ qrC a b c d)) >>> 25)

theorem quarterRound_eq (a b c d : BitVec 32) :
    quarterRound a b c d = (qrA a b c d, qrB a b c d, qrC a b c d, qrD a b c d) := by
  simp only [quarterRound, qrA, qrB, qrC, qrD, rotl32_eq _ 16 16, rotl32_eq _ 20 12,
    rotl32_eq _ 24 8, rotl32_eq _ 25 7]

/-- The column round. -/
def colRound (s : Spec.State) : Spec.State :=
  ⟨qrA s.x0 s.x4 s.x8 s.x12, qrA s.x1 s.x5 s.x9 s.x13, qrA s.x2 s.x6 s.x10 s.x14, qrA s.x3 s.x7 s.x11 s.x15,
   qrB s.x0 s.x4 s.x8 s.x12, qrB s.x1 s.x5 s.x9 s.x13, qrB s.x2 s.x6 s.x10 s.x14, qrB s.x3 s.x7 s.x11 s.x15,
   qrC s.x0 s.x4 s.x8 s.x12, qrC s.x1 s.x5 s.x9 s.x13, qrC s.x2 s.x6 s.x10 s.x14, qrC s.x3 s.x7 s.x11 s.x15,
   qrD s.x0 s.x4 s.x8 s.x12, qrD s.x1 s.x5 s.x9 s.x13, qrD s.x2 s.x6 s.x10 s.x14, qrD s.x3 s.x7 s.x11 s.x15⟩

/-- The diagonal round. -/
def diagRound (s : Spec.State) : Spec.State :=
  ⟨qrA s.x0 s.x5 s.x10 s.x15, qrA s.x1 s.x6 s.x11 s.x12, qrA s.x2 s.x7 s.x8 s.x13, qrA s.x3 s.x4 s.x9 s.x14,
   qrB s.x3 s.x4 s.x9 s.x14, qrB s.x0 s.x5 s.x10 s.x15, qrB s.x1 s.x6 s.x11 s.x12, qrB s.x2 s.x7 s.x8 s.x13,
   qrC s.x2 s.x7 s.x8 s.x13, qrC s.x3 s.x4 s.x9 s.x14, qrC s.x0 s.x5 s.x10 s.x15, qrC s.x1 s.x6 s.x11 s.x12,
   qrD s.x1 s.x6 s.x11 s.x12, qrD s.x2 s.x7 s.x8 s.x13, qrD s.x3 s.x4 s.x9 s.x14, qrD s.x0 s.x5 s.x10 s.x15⟩

theorem doubleRound_eq (s : Spec.State) : doubleRound s = diagRound (colRound s) := by
  simp only [doubleRound, quarterRound_eq, colRound, diagRound]

/-- Register assignment of the sixteen ChaCha words. -/
def regsH (sm : Arm64.State) (c : Spec.State) : Prop :=
  sm.readReg64 .x16 = BitVec.zeroExtend 64 c.x0 ∧
  sm.readReg64 .x18 = BitVec.zeroExtend 64 c.x1 ∧
  sm.readReg64 .x8 = BitVec.zeroExtend 64 c.x2 ∧
  sm.readReg64 .x9 = BitVec.zeroExtend 64 c.x3 ∧
  sm.readReg64 .x27 = BitVec.zeroExtend 64 c.x4 ∧
  sm.readReg64 .x28 = BitVec.zeroExtend 64 c.x5 ∧
  sm.readReg64 .x30 = BitVec.zeroExtend 64 c.x6 ∧
  sm.readReg64 .x13 = BitVec.zeroExtend 64 c.x7 ∧
  sm.readReg64 .x22 = BitVec.zeroExtend 64 c.x8 ∧
  sm.readReg64 .x26 = BitVec.zeroExtend 64 c.x9 ∧
  sm.readReg64 .x25 = BitVec.zeroExtend 64 c.x10 ∧
  sm.readReg64 .x24 = BitVec.zeroExtend 64 c.x11 ∧
  sm.readReg64 .x19 = BitVec.zeroExtend 64 c.x12 ∧
  sm.readReg64 .x21 = BitVec.zeroExtend 64 c.x13 ∧
  sm.readReg64 .x23 = BitVec.zeroExtend 64 c.x14 ∧
  sm.readReg64 .x20 = BitVec.zeroExtend 64 c.x15

/-- Register assignment of the sixteen ChaCha words. -/
def regsM (sm : Arm64.State) (c : Spec.State) : Prop :=
  sm.readReg64 .x16 = BitVec.zeroExtend 64 c.x0 ∧
  sm.readReg64 .x11 = BitVec.zeroExtend 64 c.x1 ∧
  sm.readReg64 .x2 = BitVec.zeroExtend 64 c.x2 ∧
  sm.readReg64 .x13 = BitVec.zeroExtend 64 c.x3 ∧
  sm.readReg64 .x18 = BitVec.zeroExtend 64 c.x4 ∧
  sm.readReg64 .x23 = BitVec.zeroExtend 64 c.x5 ∧
  sm.readReg64 .x24 = BitVec.zeroExtend 64 c.x6 ∧
  sm.readReg64 .x26 = BitVec.zeroExtend 64 c.x7 ∧
  sm.readReg64 .x9 = BitVec.zeroExtend 64 c.x8 ∧
  sm.readReg64 .x8 = BitVec.zeroExtend 64 c.x9 ∧
  sm.readReg64 .x21 = BitVec.zeroExtend 64 c.x10 ∧
  sm.readReg64 .x25 = BitVec.zeroExtend 64 c.x11 ∧
  sm.readReg64 .x19 = BitVec.zeroExtend 64 c.x12 ∧
  sm.readReg64 .x22 = BitVec.zeroExtend 64 c.x13 ∧
  sm.readReg64 .x20 = BitVec.zeroExtend 64 c.x14 ∧
  sm.readReg64 .x27 = BitVec.zeroExtend 64 c.x15

@[simp, wp_norm, arm64_norm] theorem regsH_setPC (sm : Arm64.State) (p : BitVec 64) (c : Spec.State) :
    regsH (sm.setPC p) c = regsH sm c := by
  simp only [regsH, wp_norm, arm64_norm]

attribute [irreducible] regsH regsM

/-- Registers and flags that a half round leaves alone. -/
def halfKeeps (sm sm' : Arm64.State) : Prop :=
  sm'.sp = sm.sp ∧ sm'.readReg64 .x0 = sm.readReg64 .x0 ∧ sm'.readReg64 .x1 = sm.readReg64 .x1 ∧
  sm'.readReg64 .x14 = sm.readReg64 .x14 ∧ sm'.readReg64 .x6 = sm.readReg64 .x6 ∧
  sm'.readReg64 .x7 = sm.readReg64 .x7 ∧ sm'.readReg64 .x29 = sm.readReg64 .x29 ∧
  calleeSavedVRegs sm' = calleeSavedVRegs sm

theorem colHalf_ok [CpPlacement] (sm : Arm64.State) (c : Spec.State) (n : BitVec 64) (P : SepProp)
    (hpc : sm.pc = cpPl3.base + 108#64) (hrun : sm.status = .Running)
    (hregs : regsH sm c) (h17 : sm.readReg64 .x17 = n) :
    SepWP cpProg3r (cpPl3.base + 304#64) sm P
      (fun sm' P' => (regsM sm' (colRound c) ∧ halfKeeps sm sm' ∧
        sm'.readReg64 .x17 = n - 1#64 ∧ sm'.pstate = subsPState64 n 1#64) ∧ (P' ⊢ P)) := by
  unfold regsH at hregs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hregs
  wp_steps 49
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨?_, Entails.refl _⟩
  simp only [regsM, halfKeeps, colRound, qrA, qrB, qrC, qrD, wp_norm, arm64_norm]
  and_intros
  all_goals first | assumption | ac_rfl | trace_state

theorem diagHalf_ok [CpPlacement] (sm : Arm64.State) (c : Spec.State) (P : SepProp)
    (hpc : sm.pc = cpPl3.base + 304#64) (hrun : sm.status = .Running)
    (hregs : regsM sm c) :
    SepWP cpProg3r (cpPl3.base + 496#64) sm P
      (fun sm' P' => (regsH sm' (diagRound c) ∧ halfKeeps sm sm' ∧
        sm'.readReg64 .x17 = sm.readReg64 .x17 ∧ sm'.pstate = sm.pstate) ∧ (P' ⊢ P)) := by
  unfold regsM at hregs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hregs
  wp_steps 48
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨?_, Entails.refl _⟩
  simp only [regsH, halfKeeps, diagRound, qrA, qrB, qrC, qrD, wp_norm, arm64_norm]
  and_intros
  all_goals first | assumption | ac_rfl | trace_state

/-- One full loop body up to (not including) the closing `b.ne`. -/
theorem body_ok [CpPlacement] (sm : Arm64.State) (c : Spec.State) (n : BitVec 64) (P : SepProp)
    (hpc : sm.pc = cpPl3.base + 108#64) (hrun : sm.status = .Running)
    (hregs : regsH sm c) (h17 : sm.readReg64 .x17 = n) :
    SepWP cpProg3r (cpPl3.base + 496#64) sm P
      (fun sm' P' => (regsH sm' (doubleRound c) ∧ halfKeeps sm sm' ∧
        sm'.readReg64 .x17 = n - 1#64 ∧ sm'.pstate = subsPState64 n 1#64) ∧ (P' ⊢ P)) := by
  refine SepWP.seq_entails_emp (colHalf_ok sm c n P hpc hrun hregs h17) ?_
  intro s1 hpc1 hrun1 ⟨hr1, hk1, h171, hps1⟩
  refine SepWP.mono (diagHalf_ok s1 (colRound c) P hpc1 hrun1 hr1) ?_
  intro s2 P2 _ _ ⟨⟨hr2, hk2, h172, hps2⟩, hent⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hent⟩
  · rw [doubleRound_eq]; exact hr2
  · unfold halfKeeps at *; simp_all
  · rw [h172, h171]
  · rw [hps2, hps1]

/-- Open a `144`-byte stack frame into the typed cells the function uses. -/
theorem SepWP.frame144 {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    (hf : P = memRegion b 144 ∗ F := by sep_focus)
    (h : ∀ (v0 : BitVec 32) (v1 : BitVec 32) (v2 : BitVec 32) (v3 : BitVec 32) (v4 : BitVec 32) (v5 : BitVec 32) (v6 : BitVec 32) (v7 : BitVec 32) (v8 : BitVec 32) (v9 : BitVec 32) (v10 : BitVec 32) (v11 : BitVec 32) (v12 : BitVec 64) (v13 : BitVec 32) (v14 : BitVec 32) (v15 : BitVec 64) (v16 : BitVec 64) (v17 : BitVec 64) (v18 : BitVec 64) (v19 : BitVec 64) (v20 : BitVec 64) (v21 : BitVec 64) (v22 : BitVec 64) (v23 : BitVec 64) (v24 : BitVec 64), SepWP prog t s
      (((b ↦₃₂ v0) ∗
      ((b + 4#64) ↦₃₂ v1) ∗
      ((b + 8#64) ↦₃₂ v2) ∗
      ((b + 12#64) ↦₃₂ v3) ∗
      ((b + 16#64) ↦₃₂ v4) ∗
      ((b + 20#64) ↦₃₂ v5) ∗
      ((b + 24#64) ↦₃₂ v6) ∗
      ((b + 28#64) ↦₃₂ v7) ∗
      ((b + 32#64) ↦₃₂ v8) ∗
      ((b + 36#64) ↦₃₂ v9) ∗
      ((b + 40#64) ↦₃₂ v10) ∗
      ((b + 44#64) ↦₃₂ v11) ∗
      ((b + 48#64) ↦₆₄ v12) ∗
      ((b + 56#64) ↦₃₂ v13) ∗
      ((b + 60#64) ↦₃₂ v14) ∗
      ((b + 64#64) ↦₆₄ v15) ∗
      ((b + 72#64) ↦₆₄ v16) ∗
      ((b + 80#64) ↦₆₄ v17) ∗
      ((b + 88#64) ↦₆₄ v18) ∗
      ((b + 96#64) ↦₆₄ v19) ∗
      ((b + 104#64) ↦₆₄ v20) ∗
      ((b + 112#64) ↦₆₄ v21) ∗
      ((b + 120#64) ↦₆₄ v22) ∗
      ((b + 128#64) ↦₆₄ v23) ∗
      ((b + 136#64) ↦₆₄ v24)) ∗ F) post oom) :
    SepWP prog t s P post oom := by
  subst hf
  rw [memRegion_partition b 144 [4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 56, 60, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136]]
  simp only [memRegion_four, memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  exact h ..

theorem frame144_fold (b : BitVec 64) (v0 : BitVec 32) (v1 : BitVec 32) (v2 : BitVec 32) (v3 : BitVec 32) (v4 : BitVec 32) (v5 : BitVec 32) (v6 : BitVec 32) (v7 : BitVec 32) (v8 : BitVec 32) (v9 : BitVec 32) (v10 : BitVec 32) (v11 : BitVec 32) (v12 : BitVec 64) (v13 : BitVec 32) (v14 : BitVec 32) (v15 : BitVec 64) (v16 : BitVec 64) (v17 : BitVec 64) (v18 : BitVec 64) (v19 : BitVec 64) (v20 : BitVec 64) (v21 : BitVec 64) (v22 : BitVec 64) (v23 : BitVec 64) (v24 : BitVec 64) :
    ((b ↦₃₂ v0) ∗
      ((b + 4#64) ↦₃₂ v1) ∗
      ((b + 8#64) ↦₃₂ v2) ∗
      ((b + 12#64) ↦₃₂ v3) ∗
      ((b + 16#64) ↦₃₂ v4) ∗
      ((b + 20#64) ↦₃₂ v5) ∗
      ((b + 24#64) ↦₃₂ v6) ∗
      ((b + 28#64) ↦₃₂ v7) ∗
      ((b + 32#64) ↦₃₂ v8) ∗
      ((b + 36#64) ↦₃₂ v9) ∗
      ((b + 40#64) ↦₃₂ v10) ∗
      ((b + 44#64) ↦₃₂ v11) ∗
      ((b + 48#64) ↦₆₄ v12) ∗
      ((b + 56#64) ↦₃₂ v13) ∗
      ((b + 60#64) ↦₃₂ v14) ∗
      ((b + 64#64) ↦₆₄ v15) ∗
      ((b + 72#64) ↦₆₄ v16) ∗
      ((b + 80#64) ↦₆₄ v17) ∗
      ((b + 88#64) ↦₆₄ v18) ∗
      ((b + 96#64) ↦₆₄ v19) ∗
      ((b + 104#64) ↦₆₄ v20) ∗
      ((b + 112#64) ↦₆₄ v21) ∗
      ((b + 120#64) ↦₆₄ v22) ∗
      ((b + 128#64) ↦₆₄ v23) ∗
      ((b + 136#64) ↦₆₄ v24)) ⊢ memRegion b 144 := by
  rw [memRegion_partition b 144 [4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 56, 60, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136]]
  simp only [memRegion_four, memRegion_eight]
  repeat (first | exact Entails.sepExists_intro _ | refine Entails.sepExists_intro_frame _ (sepConj_mono_right ?_))

/-- Fold the typed cells of a `144`-byte stack frame back into one region. -/
theorem SepWP.frame144_close {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    {v0 : BitVec 32} {v1 : BitVec 32} {v2 : BitVec 32} {v3 : BitVec 32} {v4 : BitVec 32} {v5 : BitVec 32} {v6 : BitVec 32} {v7 : BitVec 32} {v8 : BitVec 32} {v9 : BitVec 32} {v10 : BitVec 32} {v11 : BitVec 32} {v12 : BitVec 64} {v13 : BitVec 32} {v14 : BitVec 32} {v15 : BitVec 64} {v16 : BitVec 64} {v17 : BitVec 64} {v18 : BitVec 64} {v19 : BitVec 64} {v20 : BitVec 64} {v21 : BitVec 64} {v22 : BitVec 64} {v23 : BitVec 64} {v24 : BitVec 64}
    (hf : P ⊢ ((b ↦₃₂ v0) ∗
      ((b + 4#64) ↦₃₂ v1) ∗
      ((b + 8#64) ↦₃₂ v2) ∗
      ((b + 12#64) ↦₃₂ v3) ∗
      ((b + 16#64) ↦₃₂ v4) ∗
      ((b + 20#64) ↦₃₂ v5) ∗
      ((b + 24#64) ↦₃₂ v6) ∗
      ((b + 28#64) ↦₃₂ v7) ∗
      ((b + 32#64) ↦₃₂ v8) ∗
      ((b + 36#64) ↦₃₂ v9) ∗
      ((b + 40#64) ↦₃₂ v10) ∗
      ((b + 44#64) ↦₃₂ v11) ∗
      ((b + 48#64) ↦₆₄ v12) ∗
      ((b + 56#64) ↦₃₂ v13) ∗
      ((b + 60#64) ↦₃₂ v14) ∗
      ((b + 64#64) ↦₆₄ v15) ∗
      ((b + 72#64) ↦₆₄ v16) ∗
      ((b + 80#64) ↦₆₄ v17) ∗
      ((b + 88#64) ↦₆₄ v18) ∗
      ((b + 96#64) ↦₆₄ v19) ∗
      ((b + 104#64) ↦₆₄ v20) ∗
      ((b + 112#64) ↦₆₄ v21) ∗
      ((b + 120#64) ↦₆₄ v22) ∗
      ((b + 128#64) ↦₆₄ v23) ∗
      ((b + 136#64) ↦₆₄ v24)) ∗ F)
    (h : SepWP prog t s (memRegion b 144 ∗ F) post oom) :
    SepWP prog t s P post oom :=
  SepWP.weaken_pre (Entails.trans hf (sepConj_mono_left (frame144_fold b ..))) h

theorem chachaBlock_ok [CpPlacement] :
    subroutine_ok cpProg3r cpPl3.base (chachapolyLib.withCodeLoaded cpMpl chachaBlockSpec) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, chachaBlockSpec, stateAt, cpProg3r, State.add]
  wp_entry "<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>> as cipher::stream_core::StreamCipherCore>::write_keystream_block" g s0
  refine SepWP.frame144 (s0.sp - 144#64) (by sep_focus) ?_
  intro v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24
  wp_steps 27
  obtain ⟨st, out, s, o⟩ := g
  simp only at *
  wp_loop_measure 9 (fun k sm =>
    k ≤ 9 ∧ sm.readReg64 .x17 = BitVec.ofNat 64 (k + 1) ∧ sm.sp = s0.sp - 144#64 ∧
    sm.readReg64 .x0 = st ∧ sm.readReg64 .x1 = out ∧
    sm.readReg64 .x14 = BitVec.zeroExtend 64 s.x12 ∧
    sm.readReg64 .x6 = BitVec.zeroExtend 64 s.x8 ∧
    sm.readReg64 .x7 = BitVec.zeroExtend 64 s.x10 ∧
    sm.readReg64 .x29 = s0.readReg64 .x29 ∧
    calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
    regsH sm (iter doubleRound (9 - k) s))
  case init =>
    simp [regsH, iter, wp_norm, arm64_norm]
  case base =>
    have hlast : iter doubleRound 10 s = doubleRound (iter doubleRound 9 s) := iter_succ' _ _ _
    refine SepWP.seq_entails_emp (body_ok st_1 _ _ _ hpc_st hrun_st hinv_st (by assumption)) ?_
    intro s2 hpc2 hrun2 ⟨hr2, hk2, h172, hps2⟩
    unfold halfKeeps at hk2
    obtain ⟨hk_sp, hk_0, hk_1, hk_14, hk_6, hk_7, hk_29, hk_v⟩ := hk2
    rw [← hlast] at hr2
    unfold regsH at hr2
    obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩ := hr2
    generalize iter doubleRound 10 s = f at *
    wp_steps
    wp_done
  case step =>
    right
    have hnext : iter doubleRound (9 - m') s = doubleRound (iter doubleRound (8 - m') s) := by
      rw [show 9 - m' = (8 - m') + 1 by omega, iter_succ']
    refine SepWP.seq_entails_emp (body_ok st_1 _ _ _ hpc_st hrun_st hinv_st (by assumption)) ?_
    intro s2 hpc2 hrun2 ⟨hr2, hk2, h172, hps2⟩
    unfold halfKeeps at hk2
    obtain ⟨hk_sp, hk_0, hk_1, hk_14, hk_6, hk_7, hk_29, hk_v⟩ := hk2
    have hk_nz : BitVec.ofNat 64 (m' + 1 + 1) ≠ 1#64 := by bv_omega
    wp_steps
    wp_done

/-- Any single block's rebased program is the library's block program. -/
theorem cpBlockProg_rebase [CpPlacement] (i : Nat) :
    ((chachapolyLib.blockLib i).program (chachapolyLib.blockPlacement cpMpl i)).rebase
        (chachapolyLib.blockPlacement cpMpl i).base (fun _ => none) =
      chachapolyLib.blockProgram cpMpl i := rfl

end ChaChaPoly.Proofs
