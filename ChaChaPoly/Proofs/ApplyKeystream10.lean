module

public import ChaChaPoly.Proofs.ApplyKeystream9

/-!
# `apply_keystream` (block 4), part 10: the whole function

Frame lemmas for the 560-byte stack frame, the `len ≥ 64` path (`akBlocks_ok`), the three-way
dispatch (`akDispatch_ok`) and the top-level contract proof `applyKeystream_ok`.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
arm64_proof_prelude

/-- Open the 560-byte frame (callee area, locals, saved registers) of `apply_keystream`. -/
theorem SepWP.akTop {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    (hf : P = memRegion b 560 ∗ F := by sep_focus)
    (h : ∀ (v2 : BitVec 64) (v3 : BitVec 64) (v4 : BitVec 64) (v5 : BitVec 64) (v6 : BitVec 64) (v7 : BitVec 64) (v8 : BitVec 64) (v9 : BitVec 64) (v10 : BitVec 64) (v11 : BitVec 64) (v12 : BitVec 64) (v13 : BitVec 64), SepWP prog t s
      ((memRegion b 144 ∗
      memRegion (b + 144#64) 320 ∗
      ((b + 464#64) ↦₆₄ v2) ∗
      ((b + 472#64) ↦₆₄ v3) ∗
      ((b + 480#64) ↦₆₄ v4) ∗
      ((b + 488#64) ↦₆₄ v5) ∗
      ((b + 496#64) ↦₆₄ v6) ∗
      ((b + 504#64) ↦₆₄ v7) ∗
      ((b + 512#64) ↦₆₄ v8) ∗
      ((b + 520#64) ↦₆₄ v9) ∗
      ((b + 528#64) ↦₆₄ v10) ∗
      ((b + 536#64) ↦₆₄ v11) ∗
      ((b + 544#64) ↦₆₄ v12) ∗
      ((b + 552#64) ↦₆₄ v13)) ∗ F) post oom) :
    SepWP prog t s P post oom := by
  subst hf
  rw [memRegion_partition b 560 [144, 464, 472, 480, 488, 496, 504, 512, 520, 528, 536, 544, 552]]
  simp (maxSteps := 50000000) only [memRegion_one, memRegion_four, memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  exact h ..

theorem akTop_fold (b : BitVec 64) (v2 : BitVec 64) (v3 : BitVec 64) (v4 : BitVec 64) (v5 : BitVec 64) (v6 : BitVec 64) (v7 : BitVec 64) (v8 : BitVec 64) (v9 : BitVec 64) (v10 : BitVec 64) (v11 : BitVec 64) (v12 : BitVec 64) (v13 : BitVec 64) :
    (memRegion b 144 ∗
      memRegion (b + 144#64) 320 ∗
      ((b + 464#64) ↦₆₄ v2) ∗
      ((b + 472#64) ↦₆₄ v3) ∗
      ((b + 480#64) ↦₆₄ v4) ∗
      ((b + 488#64) ↦₆₄ v5) ∗
      ((b + 496#64) ↦₆₄ v6) ∗
      ((b + 504#64) ↦₆₄ v7) ∗
      ((b + 512#64) ↦₆₄ v8) ∗
      ((b + 520#64) ↦₆₄ v9) ∗
      ((b + 528#64) ↦₆₄ v10) ∗
      ((b + 536#64) ↦₆₄ v11) ∗
      ((b + 544#64) ↦₆₄ v12) ∗
      ((b + 552#64) ↦₆₄ v13)) ⊢ memRegion b 560 := by
  rw [memRegion_partition b 560 [144, 464, 472, 480, 488, 496, 504, 512, 520, 528, 536, 544, 552]]
  repeat' (first
    | exact Entails.refl _
    | exact pointsTo64_entails_memRegion _ _
    | exact pointsTo32_entails_memRegion _ _
    | exact pointsTo8_entails_memRegion _ _
    | refine sepConj_mono ?_ ?_)

/-- Fold the typed cells of a `560`-byte stack frame back into one region. -/
theorem SepWP.akTop_close {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    {v2 : BitVec 64} {v3 : BitVec 64} {v4 : BitVec 64} {v5 : BitVec 64} {v6 : BitVec 64} {v7 : BitVec 64} {v8 : BitVec 64} {v9 : BitVec 64} {v10 : BitVec 64} {v11 : BitVec 64} {v12 : BitVec 64} {v13 : BitVec 64}
    (hf : P ⊢ (memRegion b 144 ∗
      memRegion (b + 144#64) 320 ∗
      ((b + 464#64) ↦₆₄ v2) ∗
      ((b + 472#64) ↦₆₄ v3) ∗
      ((b + 480#64) ↦₆₄ v4) ∗
      ((b + 488#64) ↦₆₄ v5) ∗
      ((b + 496#64) ↦₆₄ v6) ∗
      ((b + 504#64) ↦₆₄ v7) ∗
      ((b + 512#64) ↦₆₄ v8) ∗
      ((b + 520#64) ↦₆₄ v9) ∗
      ((b + 528#64) ↦₆₄ v10) ∗
      ((b + 536#64) ↦₆₄ v11) ∗
      ((b + 544#64) ↦₆₄ v12) ∗
      ((b + 552#64) ↦₆₄ v13)) ∗ F)
    (h : SepWP prog t s (memRegion b 560 ∗ F) post oom) :
    SepWP prog t s P post oom :=
  SepWP.weaken_pre (Entails.trans hf (sepConj_mono_left (akTop_fold b ..))) h

/-- Open the 320-byte locals area of `apply_keystream` into the slots the block loop uses. -/
theorem SepWP.akLoc {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    (hf : P = memRegion b 320 ∗ F := by sep_focus)
    (h : ∀ (v0 : BitVec 64) (v1 : BitVec 64) (v2 : BitVec 64) (v3 : BitVec 32) (v4 : BitVec 32) (v5 : BitVec 32) (v6 : BitVec 32) (v7 : BitVec 32) (v8 : BitVec 32) (v9 : BitVec 32) (v10 : BitVec 32) (v11 : BitVec 32) (v12 : BitVec 32) (v13 : BitVec 32) (v14 : BitVec 32) (v15 : BitVec 32) (v16 : BitVec 32) (v17 : BitVec 32) (v18 : BitVec 32) (v19 : BitVec 64) (v20 : BitVec 64) (v21 : BitVec 32) (v22 : BitVec 32) (v23 : BitVec 32) (v24 : BitVec 32) (v25 : BitVec 32) (v26 : BitVec 32) (v27 : BitVec 32) (v28 : BitVec 32) (v29 : BitVec 32) (v30 : BitVec 32) (v31 : BitVec 32) (v32 : BitVec 32) (v33 : BitVec 32) (v34 : BitVec 32) (v35 : BitVec 32) (v36 : BitVec 32) (v37 : BitVec 32) (v38 : BitVec 32) (v41 : BitVec 64) (v42 : BitVec 64), SepWP prog t s
      (((b ↦₆₄ v0) ∗
      ((b + 8#64) ↦₆₄ v1) ∗
      ((b + 16#64) ↦₆₄ v2) ∗
      ((b + 24#64) ↦₃₂ v3) ∗
      ((b + 28#64) ↦₃₂ v4) ∗
      ((b + 32#64) ↦₃₂ v5) ∗
      ((b + 36#64) ↦₃₂ v6) ∗
      ((b + 40#64) ↦₃₂ v7) ∗
      ((b + 44#64) ↦₃₂ v8) ∗
      ((b + 48#64) ↦₃₂ v9) ∗
      ((b + 52#64) ↦₃₂ v10) ∗
      ((b + 56#64) ↦₃₂ v11) ∗
      ((b + 60#64) ↦₃₂ v12) ∗
      ((b + 64#64) ↦₃₂ v13) ∗
      ((b + 68#64) ↦₃₂ v14) ∗
      ((b + 72#64) ↦₃₂ v15) ∗
      ((b + 76#64) ↦₃₂ v16) ∗
      ((b + 80#64) ↦₃₂ v17) ∗
      ((b + 84#64) ↦₃₂ v18) ∗
      ((b + 88#64) ↦₆₄ v19) ∗
      ((b + 96#64) ↦₆₄ v20) ∗
      ((b + 104#64) ↦₃₂ v21) ∗
      ((b + 108#64) ↦₃₂ v22) ∗
      ((b + 112#64) ↦₃₂ v23) ∗
      ((b + 116#64) ↦₃₂ v24) ∗
      ((b + 120#64) ↦₃₂ v25) ∗
      ((b + 124#64) ↦₃₂ v26) ∗
      ((b + 128#64) ↦₃₂ v27) ∗
      ((b + 132#64) ↦₃₂ v28) ∗
      ((b + 136#64) ↦₃₂ v29) ∗
      ((b + 140#64) ↦₃₂ v30) ∗
      ((b + 144#64) ↦₃₂ v31) ∗
      ((b + 148#64) ↦₃₂ v32) ∗
      ((b + 152#64) ↦₃₂ v33) ∗
      ((b + 156#64) ↦₃₂ v34) ∗
      ((b + 160#64) ↦₃₂ v35) ∗
      ((b + 164#64) ↦₃₂ v36) ∗
      ((b + 168#64) ↦₃₂ v37) ∗
      ((b + 172#64) ↦₃₂ v38) ∗
      memRegion (b + 176#64) 64 ∗
      memRegion (b + 240#64) 64 ∗
      ((b + 304#64) ↦₆₄ v41) ∗
      ((b + 312#64) ↦₆₄ v42)) ∗ F) post oom) :
    SepWP prog t s P post oom := by
  subst hf
  rw [memRegion_partition b 320 [8, 16, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 96, 104, 108, 112, 116, 120, 124, 128, 132, 136, 140, 144, 148, 152, 156, 160, 164, 168, 172, 176, 240, 304, 312]]
  simp (maxSteps := 50000000) only [memRegion_one, memRegion_four, memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  exact h ..

theorem akLoc_fold (b : BitVec 64) (v0 : BitVec 64) (v1 : BitVec 64) (v2 : BitVec 64) (v3 : BitVec 32) (v4 : BitVec 32) (v5 : BitVec 32) (v6 : BitVec 32) (v7 : BitVec 32) (v8 : BitVec 32) (v9 : BitVec 32) (v10 : BitVec 32) (v11 : BitVec 32) (v12 : BitVec 32) (v13 : BitVec 32) (v14 : BitVec 32) (v15 : BitVec 32) (v16 : BitVec 32) (v17 : BitVec 32) (v18 : BitVec 32) (v19 : BitVec 64) (v20 : BitVec 64) (v21 : BitVec 32) (v22 : BitVec 32) (v23 : BitVec 32) (v24 : BitVec 32) (v25 : BitVec 32) (v26 : BitVec 32) (v27 : BitVec 32) (v28 : BitVec 32) (v29 : BitVec 32) (v30 : BitVec 32) (v31 : BitVec 32) (v32 : BitVec 32) (v33 : BitVec 32) (v34 : BitVec 32) (v35 : BitVec 32) (v36 : BitVec 32) (v37 : BitVec 32) (v38 : BitVec 32) (v41 : BitVec 64) (v42 : BitVec 64) :
    ((b ↦₆₄ v0) ∗
      ((b + 8#64) ↦₆₄ v1) ∗
      ((b + 16#64) ↦₆₄ v2) ∗
      ((b + 24#64) ↦₃₂ v3) ∗
      ((b + 28#64) ↦₃₂ v4) ∗
      ((b + 32#64) ↦₃₂ v5) ∗
      ((b + 36#64) ↦₃₂ v6) ∗
      ((b + 40#64) ↦₃₂ v7) ∗
      ((b + 44#64) ↦₃₂ v8) ∗
      ((b + 48#64) ↦₃₂ v9) ∗
      ((b + 52#64) ↦₃₂ v10) ∗
      ((b + 56#64) ↦₃₂ v11) ∗
      ((b + 60#64) ↦₃₂ v12) ∗
      ((b + 64#64) ↦₃₂ v13) ∗
      ((b + 68#64) ↦₃₂ v14) ∗
      ((b + 72#64) ↦₃₂ v15) ∗
      ((b + 76#64) ↦₃₂ v16) ∗
      ((b + 80#64) ↦₃₂ v17) ∗
      ((b + 84#64) ↦₃₂ v18) ∗
      ((b + 88#64) ↦₆₄ v19) ∗
      ((b + 96#64) ↦₆₄ v20) ∗
      ((b + 104#64) ↦₃₂ v21) ∗
      ((b + 108#64) ↦₃₂ v22) ∗
      ((b + 112#64) ↦₃₂ v23) ∗
      ((b + 116#64) ↦₃₂ v24) ∗
      ((b + 120#64) ↦₃₂ v25) ∗
      ((b + 124#64) ↦₃₂ v26) ∗
      ((b + 128#64) ↦₃₂ v27) ∗
      ((b + 132#64) ↦₃₂ v28) ∗
      ((b + 136#64) ↦₃₂ v29) ∗
      ((b + 140#64) ↦₃₂ v30) ∗
      ((b + 144#64) ↦₃₂ v31) ∗
      ((b + 148#64) ↦₃₂ v32) ∗
      ((b + 152#64) ↦₃₂ v33) ∗
      ((b + 156#64) ↦₃₂ v34) ∗
      ((b + 160#64) ↦₃₂ v35) ∗
      ((b + 164#64) ↦₃₂ v36) ∗
      ((b + 168#64) ↦₃₂ v37) ∗
      ((b + 172#64) ↦₃₂ v38) ∗
      memRegion (b + 176#64) 64 ∗
      memRegion (b + 240#64) 64 ∗
      ((b + 304#64) ↦₆₄ v41) ∗
      ((b + 312#64) ↦₆₄ v42)) ⊢ memRegion b 320 := by
  rw [memRegion_partition b 320 [8, 16, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 96, 104, 108, 112, 116, 120, 124, 128, 132, 136, 140, 144, 148, 152, 156, 160, 164, 168, 172, 176, 240, 304, 312]]
  repeat' (first
    | exact Entails.refl _
    | exact pointsTo64_entails_memRegion _ _
    | exact pointsTo32_entails_memRegion _ _
    | exact pointsTo8_entails_memRegion _ _
    | refine sepConj_mono ?_ ?_)

/-- Fold the typed cells of a `320`-byte stack frame back into one region. -/
theorem SepWP.akLoc_close {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    {v0 : BitVec 64} {v1 : BitVec 64} {v2 : BitVec 64} {v3 : BitVec 32} {v4 : BitVec 32} {v5 : BitVec 32} {v6 : BitVec 32} {v7 : BitVec 32} {v8 : BitVec 32} {v9 : BitVec 32} {v10 : BitVec 32} {v11 : BitVec 32} {v12 : BitVec 32} {v13 : BitVec 32} {v14 : BitVec 32} {v15 : BitVec 32} {v16 : BitVec 32} {v17 : BitVec 32} {v18 : BitVec 32} {v19 : BitVec 64} {v20 : BitVec 64} {v21 : BitVec 32} {v22 : BitVec 32} {v23 : BitVec 32} {v24 : BitVec 32} {v25 : BitVec 32} {v26 : BitVec 32} {v27 : BitVec 32} {v28 : BitVec 32} {v29 : BitVec 32} {v30 : BitVec 32} {v31 : BitVec 32} {v32 : BitVec 32} {v33 : BitVec 32} {v34 : BitVec 32} {v35 : BitVec 32} {v36 : BitVec 32} {v37 : BitVec 32} {v38 : BitVec 32} {v41 : BitVec 64} {v42 : BitVec 64}
    (hf : P ⊢ ((b ↦₆₄ v0) ∗
      ((b + 8#64) ↦₆₄ v1) ∗
      ((b + 16#64) ↦₆₄ v2) ∗
      ((b + 24#64) ↦₃₂ v3) ∗
      ((b + 28#64) ↦₃₂ v4) ∗
      ((b + 32#64) ↦₃₂ v5) ∗
      ((b + 36#64) ↦₃₂ v6) ∗
      ((b + 40#64) ↦₃₂ v7) ∗
      ((b + 44#64) ↦₃₂ v8) ∗
      ((b + 48#64) ↦₃₂ v9) ∗
      ((b + 52#64) ↦₃₂ v10) ∗
      ((b + 56#64) ↦₃₂ v11) ∗
      ((b + 60#64) ↦₃₂ v12) ∗
      ((b + 64#64) ↦₃₂ v13) ∗
      ((b + 68#64) ↦₃₂ v14) ∗
      ((b + 72#64) ↦₃₂ v15) ∗
      ((b + 76#64) ↦₃₂ v16) ∗
      ((b + 80#64) ↦₃₂ v17) ∗
      ((b + 84#64) ↦₃₂ v18) ∗
      ((b + 88#64) ↦₆₄ v19) ∗
      ((b + 96#64) ↦₆₄ v20) ∗
      ((b + 104#64) ↦₃₂ v21) ∗
      ((b + 108#64) ↦₃₂ v22) ∗
      ((b + 112#64) ↦₃₂ v23) ∗
      ((b + 116#64) ↦₃₂ v24) ∗
      ((b + 120#64) ↦₃₂ v25) ∗
      ((b + 124#64) ↦₃₂ v26) ∗
      ((b + 128#64) ↦₃₂ v27) ∗
      ((b + 132#64) ↦₃₂ v28) ∗
      ((b + 136#64) ↦₃₂ v29) ∗
      ((b + 140#64) ↦₃₂ v30) ∗
      ((b + 144#64) ↦₃₂ v31) ∗
      ((b + 148#64) ↦₃₂ v32) ∗
      ((b + 152#64) ↦₃₂ v33) ∗
      ((b + 156#64) ↦₃₂ v34) ∗
      ((b + 160#64) ↦₃₂ v35) ∗
      ((b + 164#64) ↦₃₂ v36) ∗
      ((b + 168#64) ↦₃₂ v37) ∗
      ((b + 172#64) ↦₃₂ v38) ∗
      memRegion (b + 176#64) 64 ∗
      memRegion (b + 240#64) 64 ∗
      ((b + 304#64) ↦₆₄ v41) ∗
      ((b + 312#64) ↦₆₄ v42)) ∗ F)
    (h : SepWP prog t s (memRegion b 320 ∗ F) post oom) :
    SepWP prog t s P post oom :=
  SepWP.weaken_pre (Entails.trans hf (sepConj_mono_left (akLoc_fold b ..))) h

theorem SepWP.memRegion_bytes {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (a : BitVec 64) (n : Nat)
    (hn : n ≤ 2 ^ 64) (hf : P = memRegion a n ∗ F := by sep_focus)
    (h : ∀ bs : Bytes, bs.length = n → SepWP prog t s ((a ↦ₛ bs) ∗ F) post oom) :
    SepWP prog t s P post oom := by
  subst hf
  rw [memRegion_eq_exists_bytes a n hn, sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  exact SepWP.pure_elim fun hl => h bs hl

theorem SepWP.bytes_region {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (a : BitVec 64) (bs : Bytes)
    (n : Nat) (hl : bs.length = n) (hf : P = (a ↦ₛ bs) ∗ F := by sep_focus)
    (h : SepWP prog t s (memRegion a n ∗ F) post oom) : SepWP prog t s P post oom := by
  subst hf; subst hl
  exact SepWP.weaken_pre (sepConj_mono_left (pointsToBytes_entails_memRegion a bs)) h

/-- From the block-loop setup (`0xe4`, `n = len / 64 > 0`) to the epilogue (`0x454`): the
    outer loop, the counter write-back and, when `len mod 64 > 0`, the tail segment. -/
theorem akBlocks_ok [CpPlacement] (sm : Arm64.State) (c bufp : BitVec 64) (s buf : Spec.State)
    (data : Bytes) (nb : Nat) (F : SepProp)
    (hpc : sm.pc = cpPl4.base + 0xe4#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true) (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (h21 : sm.readReg64 .x21 = c) (h1 : sm.readReg64 .x1 = bufp)
    (h2 : sm.readReg64 .x2 = BitVec.ofNat 64 data.length)
    (h8 : sm.readReg64 .x8 = BitVec.ofNat 64 nb)
    (h22 : sm.readReg64 .x22 = BitVec.ofNat 64 (data.length % 64))
    (h27 : sm.readReg64 .x27 = BitVec.zeroExtend 64 s.x12)
    (h29 : sm.readReg64 .x29 = sm.sp + 0x140#64)
    (hnb : nb = data.length / 64) (hnb0 : 0 < nb) (hL : data.length < 2 ^ 63) :
    SepWP cpProg4r (cpPl4.base + 0x454#64) sm
      (stateAt c s ∗ stateAt (c + 0x40#64) buf ∗ (bufp ↦ₛ data) ∗
        memRegion (sm.sp - 0x90#64) 0x90 ∗ memRegion sm.sp 0x140 ∗ F)
      (sepPost (fun sm' => sm'.sp = sm.sp ∧ sm'.readReg64 .x21 = c ∧
          sm'.readReg64 .x22 = BitVec.ofNat 64 (data.length % 64) ∧
          calleeSavedVRegs sm' = calleeSavedVRegs sm)
        (stateAt c (s.advance ((data.length + 63) / 64)) ∗ (∃∗ b, stateAt (c + 0x40#64) b) ∗
          (bufp ↦ₛ streamXor s data) ∗ memRegion (sm.sp - 0x90#64) 0x90 ∗ memRegion sm.sp 0x140 ∗ F)) := by
  subst hnb
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl4.base + 0x41c#64) hcl ?_
  refine SepWP.akLoc sm.sp (by sep_focus) ?_
  intro v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v41 v42
  simp only [stateAt] at *
  wp_steps 24
  refine SepWP.memRegion_bytes (sm.sp + 176#64) 64 (by decide) (by sep_focus) fun cpb hcpb => ?_
  refine SepWP.memRegion_bytes (sm.sp + 240#64) 64 (by decide) (by sep_focus) fun ob hob => ?_
  refine SepWP.seq (SepWP.weaken_pre ?_ (outerLoop_ok _ s (BitVec.ofNat 64 (data.length % 64))
    (BitVec.ofNat 64 data.length) c bufp (data.length / 64) data
    (((sm.sp + 24#64) ↦₃₂ v3) ∗ ((sm.sp + 104#64) ↦₃₂ v21) ∗ ((sm.sp + 304#64) ↦₆₄ v41) ∗
      ((sm.sp + 312#64) ↦₆₄ v42) ∗ stateAt c s ∗ stateAt (c + 64#64) buf ∗
      memRegion (sm.sp - 144#64) 144 ∗ F)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simp [regsO, wp_norm, arm64_norm, h27]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, h29]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by omega) (by omega) hL)) ?_
  · simp only [wp_norm, arm64_norm]
    refine Entails.trans ?_ (sepConj_mono_left (akScratch_close _ _ _ _ s _ _ v22
      ⟨v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38⟩ cpb ob hcpb hob))
    simp only [akSlots, stateAt]
    sep_entail
  intro st Pm hpcl hrunl ⟨⟨h27l, hspl, h29l, h1l, hvl⟩, hentl⟩
  refine SepWP.weaken_pre hentl ?_
  simp only [wp_norm, arm64_norm] at hspl h27l h1l hvl ⊢
  refine akScratch_open _ _ _ _ _ _ _ _ (fun ctr ks cpb' ob' hc' ho' => ?_)
  simp only [akSlots, stateAt]
  wp_steps 3
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunl]) ?_
  intro hcl'
  refine SepWP.bytes_region (sm.sp + 176#64) cpb' 64 hc' (by sep_focus) ?_
  refine SepWP.bytes_region (sm.sp + 240#64) ob' 64 ho' (by sep_focus) ?_
  refine SepWP.akLoc_close sm.sp (by sep_frame) ?_
  wp_step
  simp only [wp_norm, arm64_norm] at hcl'
  by_cases ht : data.length % 64 = 0
  · have hc : (BitVec.ofNat 64 (data.length % 64) == 0#64) = true := by simp [ht]
    simp only [hc, ite_true]
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunl]) ?_
    refine ⟨⟨by simp [wp_norm, arm64_norm, hspl], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simpa [wp_norm, arm64_norm] using hvl⟩, ?_⟩
    have h63 : (data.length + 63) / 64 = data.length / 64 := by omega
    have hcur : akCur s data (data.length / 64) = streamXor s data := by
      rw [akCur, show 64 * (data.length / 64) = data.length by omega, List.take_length,
        List.drop_length, List.append_nil]
    rw [h63, hcur]
    refine Entails.trans ?_ (Entails.sepExists_intro buf)
    simp only [Spec.State.advance]
    sep_entail
  · have hne : BitVec.ofNat 64 (data.length % 64) ≠ 0#64 := by
      intro h; apply ht; have := congrArg BitVec.toNat h; simp at this; omega
    rw [if_neg (by simpa using hne)]
    have hA : (streamXor s (data.take (64 * (data.length / 64)))).length = 64 * (data.length / 64) := by
      rw [streamXor_length s _ _ rfl]; simp; omega
    have hTl : (data.drop (64 * (data.length / 64))).length = data.length % 64 := by simp; omega
    rw [akCur, pointsToBytes_append, hA]
    refine SepWP.mono (SepWP.weaken_pre ?_ (tailSeg_ok _ c bufp (s.advance (data.length / 64)) buf
      (data.length / 64) (data.drop (64 * (data.length / 64)))
      (memRegion sm.sp 320 ∗ (bufp ↦ₛ streamXor s (data.take (64 * (data.length / 64)))) ∗ F)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunl])
      (by simp [wp_norm, arm64_norm, hspl, hsp]) hcl' (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, h1l])
      (by simp [wp_norm, arm64_norm, hTl]; congr 1; omega)
      (by simp [wp_norm, arm64_norm, hTl]) (by omega) (by omega) (by omega))) ?_
    · simp only [wp_norm, arm64_norm, hspl, stateAt]
      sep_entail
    intro sf Pf _ _ ⟨⟨fsp, f21, f22, fv⟩, hQ⟩
    simp only [wp_norm, arm64_norm, hspl] at fsp fv
    refine ⟨⟨fsp, f21, by rw [f22, hTl], by rw [fv, hvl]⟩, Entails.trans hQ ?_⟩
    have h63 : (data.length + 63) / 64 = data.length / 64 + 1 := by omega
    have hsx : streamXor s data = streamXor s (data.take (64 * (data.length / 64))) ++
        xorBytes (data.drop (64 * (data.length / 64))) (stateBlock (s.advance (data.length / 64))) := by
      have e := congrArg (streamXor s) (List.take_append_drop (64 * (data.length / 64)) data)
      rw [← e, streamXor_append s (data.length / 64) _ _ (by simp; omega),
        streamXor_short (s.advance (data.length / 64)) (data.drop (64 * (data.length / 64))) (by rw [hTl]; omega)]
    rw [h63, hsx, pointsToBytes_append, hA]
    refine Entails.trans ?_ (Entails.sepExists_intro ((iter doubleRound 10 (s.advance (data.length / 64))).add
      (s.advance (data.length / 64))))
    have hadv : { s.advance (data.length / 64) with x12 := (s.advance (data.length / 64)).x12 + 1 } =
        s.advance (data.length / 64 + 1) := by
      simp [Spec.State.advance, BitVec.add_assoc, BitVec.ofNat_add]
    rw [hadv]
    simp only [stateAt, BitVec.add_assoc, BitVec.reduceAdd, wp_norm, arm64_norm, hspl]
    sep_entail

/-- From the dispatch at `0xa4` to the epilogue: `len = 0`, `0 < len < 64` (tail only) and
    `len ≥ 64` (`akBlocks_ok`). -/
theorem akDispatch_ok [CpPlacement] (sm : Arm64.State) (c bufp : BitVec 64) (s buf : Spec.State)
    (data : Bytes) (F : SepProp)
    (hpc : sm.pc = cpPl4.base + 0xa4#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true) (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (h21 : sm.readReg64 .x21 = c) (h1 : sm.readReg64 .x1 = bufp)
    (h2 : sm.readReg64 .x2 = BitVec.ofNat 64 data.length)
    (h8 : sm.readReg64 .x8 = BitVec.ofNat 64 (data.length / 64))
    (h22 : sm.readReg64 .x22 = BitVec.ofNat 64 (data.length % 64))
    (h27 : sm.readReg64 .x27 = BitVec.zeroExtend 64 s.x12)
    (h29 : sm.readReg64 .x29 = sm.sp + 0x140#64)
    (hL : data.length < 2 ^ 63) :
    SepWP cpProg4r (cpPl4.base + 0x454#64) sm
      (stateAt c s ∗ stateAt (c + 0x40#64) buf ∗ (bufp ↦ₛ data) ∗
        memRegion (sm.sp - 0x90#64) 0x90 ∗ memRegion sm.sp 0x140 ∗ F)
      (sepPost (fun sm' => sm'.sp = sm.sp ∧ sm'.readReg64 .x21 = c ∧
          sm'.readReg64 .x22 = BitVec.ofNat 64 (data.length % 64) ∧
          calleeSavedVRegs sm' = calleeSavedVRegs sm)
        (stateAt c (s.advance ((data.length + 63) / 64)) ∗ (∃∗ b, stateAt (c + 0x40#64) b) ∗
          (bufp ↦ₛ streamXor s data) ∗ memRegion (sm.sp - 0x90#64) 0x90 ∗ memRegion sm.sp 0x140 ∗ F)) := by
  by_cases hnb : data.length / 64 = 0
  · have hz : (BitVec.ofNat 64 (data.length / 64) == 0#64) = true := by simp [hnb]
    wp_step
    simp only [h8, hz, Bool.not_true, ite_false, ite_true, Bool.false_eq_true, not_true_eq_false,
      not_false_eq_true] at *
    by_cases ht : data.length % 64 = 0
    · have hd : data = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hd
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
      refine ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, h21],
        by simp [wp_norm, arm64_norm, h22], by simp [wp_norm, arm64_norm]⟩, ?_⟩
      simp only [List.length_nil, show (0 + 63) / 64 = 0 from rfl, State.advance_zero, streamXor_nil]
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro buf)))
      simp only [wp_norm, arm64_norm]
      exact Entails.refl _
    · have hnz : (BitVec.ofNat 64 (data.length % 64) == 0#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h; apply ht; have := congrArg BitVec.toNat h; simp at this; omega
      wp_step
      simp only [wp_norm, arm64_norm, h22, hnz, Bool.not_false, ite_true, ite_false,
        Bool.false_eq_true, not_true_eq_false, not_false_eq_true]
      have hl : data.length < 64 := by omega
      have h0 : BitVec.ofNat 64 (64 * 0) = 0#64 := rfl
      refine SepWP.mono (SepWP.weaken_pre ?_ (tailSeg_ok _ c bufp s buf 0 data
        (memRegion sm.sp 320 ∗ F) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp]) (by simpa [wp_norm, arm64_norm] using hcl)
        (by simp [wp_norm, arm64_norm, h21]) (by simp [wp_norm, arm64_norm, h1])
        (by simp [wp_norm, arm64_norm, h2]) (by simp [wp_norm, arm64_norm, h22, Nat.mod_eq_of_lt hl])
        (by omega) hl (by omega))) ?_
      · simp only [wp_norm, arm64_norm, h0, BitVec.add_zero]
        sep_entail
      intro sf Pf _ _ ⟨⟨fsp, f21, f22, fv⟩, hQ⟩
      simp only [wp_norm, arm64_norm] at fsp fv
      refine ⟨⟨fsp, f21, by rw [f22, Nat.mod_eq_of_lt hl], fv⟩, Entails.trans hQ ?_⟩
      have h63 : (data.length + 63) / 64 = 1 := by omega
      have hadv : { s with x12 := s.x12 + 1 } = s.advance 1 := by simp [Spec.State.advance]
      rw [h63, ← hadv, streamXor_short s data (by omega)]
      refine Entails.trans ?_ (Entails.sepExists_intro ((iter doubleRound 10 s).add s))
      simp only [wp_norm, arm64_norm, h0, BitVec.add_zero]
      sep_entail
  · have hnz : (BitVec.ofNat 64 (data.length / 64) == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h; apply hnb; have := congrArg BitVec.toNat h; simp at this; omega
    wp_step
    try simp only [wp_norm, arm64_norm, h8, hnz, Bool.not_false, ite_true]
    have hB := akBlocks_ok (sm.setPC (cpPl4.base + 0xe4#64)) c bufp s buf data (data.length / 64) F (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simpa [wp_norm, arm64_norm] using hsp)
      (by simpa [wp_norm, arm64_norm] using hcl) (by simpa [wp_norm, arm64_norm] using h21)
      (by simpa [wp_norm, arm64_norm] using h1) (by simpa [wp_norm, arm64_norm] using h2)
      (by simpa [wp_norm, arm64_norm] using h8) (by simpa [wp_norm, arm64_norm] using h22)
      (by simpa [wp_norm, arm64_norm] using h27) (by simpa [wp_norm, arm64_norm] using h29)
      rfl (by omega) hL
    simp only [wp_norm, arm64_norm] at hB
    exact hB

set_option maxRecDepth 400000 in
/-- `apply_keystream` meets `applyKeystreamContract` (key-stream position 0 on entry). -/
theorem applyKeystream_ok [CpPlacement] :
    subroutine_ok cpProg4r cpPl4.base (chachapolyLib.withCodeLoaded cpMpl applyKeystreamContract) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, applyKeystreamContract]
  wp_entry "<cipher::stream_wrapper::StreamCipherCoreWrapper<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>>> as cipher::stream::StreamCipher>::apply_keystream" a s0
  obtain ⟨c, bufp, data, s, buf⟩ := a
  simp only at *
  refine SepWP.akTop (s0.sp - 0x230#64) (by sep_focus) ?_
  intro v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  simp only [stateAt] at *
  have hnp : (BitVec.zeroExtend 64 (BitVec.truncate 32 (~~~BitVec.zeroExtend 64 s.x12))).ult
      (if (BitVec.ofNat 64 (List.length data) &&& 63#64 == 0#64) = true then
        BitVec.ofNat 64 (List.length data) >>> 6
      else BitVec.ofNat 64 (List.length data) >>> 6 + 1#64) = false := by
    have hx := s.x12.isLt
    have hn : (BitVec.zeroExtend 64 (BitVec.truncate 32 (~~~BitVec.zeroExtend 64 s.x12))) =
        BitVec.ofNat 64 (2 ^ 32 - 1 - s.x12.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_not,
        BitVec.toNat_ofNat]
      omega
    have hand : (BitVec.ofNat 64 (List.length data) &&& 63#64).toNat = data.length % 64 := by
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show 63 % 2 ^ 64 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have hb : (if (BitVec.ofNat 64 (List.length data) &&& 63#64 == 0#64) = true then
        BitVec.ofNat 64 (List.length data) >>> 6
      else BitVec.ofNat 64 (List.length data) >>> 6 + 1#64) = BitVec.ofNat 64 ((data.length + 63) / 64) := by
      split <;> rename_i hc
      · have : data.length % 64 = 0 := by
          simp only [beq_iff_eq] at hc; rw [← hand, hc]; rfl
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
        omega
      · have : data.length % 64 ≠ 0 := by
          intro h0; apply hc; simp only [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [hand, h0]; rfl
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
        omega
    rw [hn, hb]
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_lt]
    omega
  have hal : ((s0.sp - 416#64) &&& 15#64 == 0#64) = true := by
    simp only [beq_iff_eq] at hsp_align ⊢
    have h16 := congrArg BitVec.toNat hsp_align
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod] at h16 ⊢
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat] at h16 ⊢
    omega
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl4.base + 0xa4#64) h ?_
  wp_steps
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  intro hcl
  have hx8 : BitVec.ofNat 64 data.length >>> 6 = BitVec.ofNat 64 (data.length / 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have hx22 : BitVec.ofNat 64 data.length &&& 63#64 = BitVec.ofNat 64 (data.length % 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show 63 % 2 ^ 64 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    omega
  simp only [hx8, hx22] at hcl ⊢
  refine SepWP.seq (SepWP.weaken_pre ?_ (akDispatch_ok _ c bufp s buf data
    (((c + 128#64) ↦₈ 0#8) ∗
        ((s0.sp - 560#64 + 464#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 560#64 + 472#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 560#64 + 480#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
        ((s0.sp - 560#64 + 488#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
        ((s0.sp - 560#64 + 496#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 560#64 + 504#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 560#64 + 512#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 560#64 + 520#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 560#64 + 528#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 560#64 + 536#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 560#64 + 544#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 560#64 + 552#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h_5)) ?_
  · have e1 : s0.sp - 416#64 - 144#64 = s0.sp - 560#64 := by bv_omega
    have e2 : s0.sp - 416#64 = s0.sp - 560#64 + 144#64 := by bv_omega
    simp only [wp_norm, arm64_norm, stateAt]
    try rw [e1]
    sep_entail
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm, hrun]
  · simpa [wp_norm, arm64_norm] using hal
  · simpa [wp_norm, arm64_norm] using hcl
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm, h_3]
  · simp [wp_norm, arm64_norm, h_4]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · first | (simp [wp_norm, arm64_norm]; done) | (simp [wp_norm, arm64_norm]; bv_omega)
  intro sf Pf hpcf hrunf ⟨⟨fsp, f21, f22, fv⟩, hQ⟩
  refine SepWP.weaken_pre hQ ?_
  simp only [wp_norm, arm64_norm] at fsp fv
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun b => ?_
  simp only [stateAt]
  wp_steps
  wp_done

end ChaChaPoly.Proofs
