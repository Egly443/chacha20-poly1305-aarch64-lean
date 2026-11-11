module

public import ChaChaPoly.Proofs.Code
public import ChaChaPoly.Spec.Contracts

/-!
# `subtle::black_box::<u8>` (block 0) and the `Cipher` drop glue (block 1)
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
arm64_proof_prelude


theorem blackBox_ok [CpPlacement] :
    subroutine_ok cpProg0r cpPl0.base (chachapolyLib.withCodeLoaded cpMpl blackBoxContract) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, blackBoxContract]
  wp_entry "subtle::black_box::<u8>" b s0
  refine SepWP.memRegion_bytes (s0.sp - 16#64) 16 (by decide) (by sep_focus) ?_
  intro stk hstk
  wp_steps
  refine SepWP.bytes_memRegion (s0.sp - 16#64) 16 ?_
  have hb : (ByteSlice.write8 stk 12 b).getD 12 0#8 = b := by
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega)]; simp
  wp_done

/-- Open a `129`-byte stack frame into the typed cells the function uses. -/
theorem SepWP.frame129 {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    (hf : P = memRegion b 129 ∗ F := by sep_focus)
    (h : ∀ (v0 : BitVec 32) (v1 : BitVec 32) (v2 : BitVec 32) (v3 : BitVec 32) (v4 : BitVec 32) (v5 : BitVec 32) (v6 : BitVec 32) (v7 : BitVec 32) (v8 : BitVec 32) (v9 : BitVec 32) (v10 : BitVec 32) (v11 : BitVec 32) (v12 : BitVec 32) (v13 : BitVec 32) (v14 : BitVec 32) (v15 : BitVec 32) (v16 : BitVec 8) (v17 : BitVec 8) (v18 : BitVec 8) (v19 : BitVec 8) (v20 : BitVec 8) (v21 : BitVec 8) (v22 : BitVec 8) (v23 : BitVec 8) (v24 : BitVec 8) (v25 : BitVec 8) (v26 : BitVec 8) (v27 : BitVec 8) (v28 : BitVec 8) (v29 : BitVec 8) (v30 : BitVec 8) (v31 : BitVec 8) (v32 : BitVec 8) (v33 : BitVec 8) (v34 : BitVec 8) (v35 : BitVec 8) (v36 : BitVec 8) (v37 : BitVec 8) (v38 : BitVec 8) (v39 : BitVec 8) (v40 : BitVec 8) (v41 : BitVec 8) (v42 : BitVec 8) (v43 : BitVec 8) (v44 : BitVec 8) (v45 : BitVec 8) (v46 : BitVec 8) (v47 : BitVec 8) (v48 : BitVec 8) (v49 : BitVec 8) (v50 : BitVec 8) (v51 : BitVec 8) (v52 : BitVec 8) (v53 : BitVec 8) (v54 : BitVec 8) (v55 : BitVec 8) (v56 : BitVec 8) (v57 : BitVec 8) (v58 : BitVec 8) (v59 : BitVec 8) (v60 : BitVec 8) (v61 : BitVec 8) (v62 : BitVec 8) (v63 : BitVec 8) (v64 : BitVec 8) (v65 : BitVec 8) (v66 : BitVec 8) (v67 : BitVec 8) (v68 : BitVec 8) (v69 : BitVec 8) (v70 : BitVec 8) (v71 : BitVec 8) (v72 : BitVec 8) (v73 : BitVec 8) (v74 : BitVec 8) (v75 : BitVec 8) (v76 : BitVec 8) (v77 : BitVec 8) (v78 : BitVec 8) (v79 : BitVec 8) (v80 : BitVec 8), SepWP prog t s
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
      ((b + 48#64) ↦₃₂ v12) ∗
      ((b + 52#64) ↦₃₂ v13) ∗
      ((b + 56#64) ↦₃₂ v14) ∗
      ((b + 60#64) ↦₃₂ v15) ∗
      ((b + 64#64) ↦₈ v16) ∗
      ((b + 65#64) ↦₈ v17) ∗
      ((b + 66#64) ↦₈ v18) ∗
      ((b + 67#64) ↦₈ v19) ∗
      ((b + 68#64) ↦₈ v20) ∗
      ((b + 69#64) ↦₈ v21) ∗
      ((b + 70#64) ↦₈ v22) ∗
      ((b + 71#64) ↦₈ v23) ∗
      ((b + 72#64) ↦₈ v24) ∗
      ((b + 73#64) ↦₈ v25) ∗
      ((b + 74#64) ↦₈ v26) ∗
      ((b + 75#64) ↦₈ v27) ∗
      ((b + 76#64) ↦₈ v28) ∗
      ((b + 77#64) ↦₈ v29) ∗
      ((b + 78#64) ↦₈ v30) ∗
      ((b + 79#64) ↦₈ v31) ∗
      ((b + 80#64) ↦₈ v32) ∗
      ((b + 81#64) ↦₈ v33) ∗
      ((b + 82#64) ↦₈ v34) ∗
      ((b + 83#64) ↦₈ v35) ∗
      ((b + 84#64) ↦₈ v36) ∗
      ((b + 85#64) ↦₈ v37) ∗
      ((b + 86#64) ↦₈ v38) ∗
      ((b + 87#64) ↦₈ v39) ∗
      ((b + 88#64) ↦₈ v40) ∗
      ((b + 89#64) ↦₈ v41) ∗
      ((b + 90#64) ↦₈ v42) ∗
      ((b + 91#64) ↦₈ v43) ∗
      ((b + 92#64) ↦₈ v44) ∗
      ((b + 93#64) ↦₈ v45) ∗
      ((b + 94#64) ↦₈ v46) ∗
      ((b + 95#64) ↦₈ v47) ∗
      ((b + 96#64) ↦₈ v48) ∗
      ((b + 97#64) ↦₈ v49) ∗
      ((b + 98#64) ↦₈ v50) ∗
      ((b + 99#64) ↦₈ v51) ∗
      ((b + 100#64) ↦₈ v52) ∗
      ((b + 101#64) ↦₈ v53) ∗
      ((b + 102#64) ↦₈ v54) ∗
      ((b + 103#64) ↦₈ v55) ∗
      ((b + 104#64) ↦₈ v56) ∗
      ((b + 105#64) ↦₈ v57) ∗
      ((b + 106#64) ↦₈ v58) ∗
      ((b + 107#64) ↦₈ v59) ∗
      ((b + 108#64) ↦₈ v60) ∗
      ((b + 109#64) ↦₈ v61) ∗
      ((b + 110#64) ↦₈ v62) ∗
      ((b + 111#64) ↦₈ v63) ∗
      ((b + 112#64) ↦₈ v64) ∗
      ((b + 113#64) ↦₈ v65) ∗
      ((b + 114#64) ↦₈ v66) ∗
      ((b + 115#64) ↦₈ v67) ∗
      ((b + 116#64) ↦₈ v68) ∗
      ((b + 117#64) ↦₈ v69) ∗
      ((b + 118#64) ↦₈ v70) ∗
      ((b + 119#64) ↦₈ v71) ∗
      ((b + 120#64) ↦₈ v72) ∗
      ((b + 121#64) ↦₈ v73) ∗
      ((b + 122#64) ↦₈ v74) ∗
      ((b + 123#64) ↦₈ v75) ∗
      ((b + 124#64) ↦₈ v76) ∗
      ((b + 125#64) ↦₈ v77) ∗
      ((b + 126#64) ↦₈ v78) ∗
      ((b + 127#64) ↦₈ v79) ∗
      ((b + 128#64) ↦₈ v80)) ∗ F) post oom) :
    SepWP prog t s P post oom := by
  subst hf
  rw [memRegion_partition b 129 [4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]]
  simp (maxSteps := 50000000) only [memRegion_one, memRegion_four, memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  exact h ..

theorem frame129_fold (b : BitVec 64) (v0 : BitVec 32) (v1 : BitVec 32) (v2 : BitVec 32) (v3 : BitVec 32) (v4 : BitVec 32) (v5 : BitVec 32) (v6 : BitVec 32) (v7 : BitVec 32) (v8 : BitVec 32) (v9 : BitVec 32) (v10 : BitVec 32) (v11 : BitVec 32) (v12 : BitVec 32) (v13 : BitVec 32) (v14 : BitVec 32) (v15 : BitVec 32) (v16 : BitVec 8) (v17 : BitVec 8) (v18 : BitVec 8) (v19 : BitVec 8) (v20 : BitVec 8) (v21 : BitVec 8) (v22 : BitVec 8) (v23 : BitVec 8) (v24 : BitVec 8) (v25 : BitVec 8) (v26 : BitVec 8) (v27 : BitVec 8) (v28 : BitVec 8) (v29 : BitVec 8) (v30 : BitVec 8) (v31 : BitVec 8) (v32 : BitVec 8) (v33 : BitVec 8) (v34 : BitVec 8) (v35 : BitVec 8) (v36 : BitVec 8) (v37 : BitVec 8) (v38 : BitVec 8) (v39 : BitVec 8) (v40 : BitVec 8) (v41 : BitVec 8) (v42 : BitVec 8) (v43 : BitVec 8) (v44 : BitVec 8) (v45 : BitVec 8) (v46 : BitVec 8) (v47 : BitVec 8) (v48 : BitVec 8) (v49 : BitVec 8) (v50 : BitVec 8) (v51 : BitVec 8) (v52 : BitVec 8) (v53 : BitVec 8) (v54 : BitVec 8) (v55 : BitVec 8) (v56 : BitVec 8) (v57 : BitVec 8) (v58 : BitVec 8) (v59 : BitVec 8) (v60 : BitVec 8) (v61 : BitVec 8) (v62 : BitVec 8) (v63 : BitVec 8) (v64 : BitVec 8) (v65 : BitVec 8) (v66 : BitVec 8) (v67 : BitVec 8) (v68 : BitVec 8) (v69 : BitVec 8) (v70 : BitVec 8) (v71 : BitVec 8) (v72 : BitVec 8) (v73 : BitVec 8) (v74 : BitVec 8) (v75 : BitVec 8) (v76 : BitVec 8) (v77 : BitVec 8) (v78 : BitVec 8) (v79 : BitVec 8) (v80 : BitVec 8) :
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
      ((b + 48#64) ↦₃₂ v12) ∗
      ((b + 52#64) ↦₃₂ v13) ∗
      ((b + 56#64) ↦₃₂ v14) ∗
      ((b + 60#64) ↦₃₂ v15) ∗
      ((b + 64#64) ↦₈ v16) ∗
      ((b + 65#64) ↦₈ v17) ∗
      ((b + 66#64) ↦₈ v18) ∗
      ((b + 67#64) ↦₈ v19) ∗
      ((b + 68#64) ↦₈ v20) ∗
      ((b + 69#64) ↦₈ v21) ∗
      ((b + 70#64) ↦₈ v22) ∗
      ((b + 71#64) ↦₈ v23) ∗
      ((b + 72#64) ↦₈ v24) ∗
      ((b + 73#64) ↦₈ v25) ∗
      ((b + 74#64) ↦₈ v26) ∗
      ((b + 75#64) ↦₈ v27) ∗
      ((b + 76#64) ↦₈ v28) ∗
      ((b + 77#64) ↦₈ v29) ∗
      ((b + 78#64) ↦₈ v30) ∗
      ((b + 79#64) ↦₈ v31) ∗
      ((b + 80#64) ↦₈ v32) ∗
      ((b + 81#64) ↦₈ v33) ∗
      ((b + 82#64) ↦₈ v34) ∗
      ((b + 83#64) ↦₈ v35) ∗
      ((b + 84#64) ↦₈ v36) ∗
      ((b + 85#64) ↦₈ v37) ∗
      ((b + 86#64) ↦₈ v38) ∗
      ((b + 87#64) ↦₈ v39) ∗
      ((b + 88#64) ↦₈ v40) ∗
      ((b + 89#64) ↦₈ v41) ∗
      ((b + 90#64) ↦₈ v42) ∗
      ((b + 91#64) ↦₈ v43) ∗
      ((b + 92#64) ↦₈ v44) ∗
      ((b + 93#64) ↦₈ v45) ∗
      ((b + 94#64) ↦₈ v46) ∗
      ((b + 95#64) ↦₈ v47) ∗
      ((b + 96#64) ↦₈ v48) ∗
      ((b + 97#64) ↦₈ v49) ∗
      ((b + 98#64) ↦₈ v50) ∗
      ((b + 99#64) ↦₈ v51) ∗
      ((b + 100#64) ↦₈ v52) ∗
      ((b + 101#64) ↦₈ v53) ∗
      ((b + 102#64) ↦₈ v54) ∗
      ((b + 103#64) ↦₈ v55) ∗
      ((b + 104#64) ↦₈ v56) ∗
      ((b + 105#64) ↦₈ v57) ∗
      ((b + 106#64) ↦₈ v58) ∗
      ((b + 107#64) ↦₈ v59) ∗
      ((b + 108#64) ↦₈ v60) ∗
      ((b + 109#64) ↦₈ v61) ∗
      ((b + 110#64) ↦₈ v62) ∗
      ((b + 111#64) ↦₈ v63) ∗
      ((b + 112#64) ↦₈ v64) ∗
      ((b + 113#64) ↦₈ v65) ∗
      ((b + 114#64) ↦₈ v66) ∗
      ((b + 115#64) ↦₈ v67) ∗
      ((b + 116#64) ↦₈ v68) ∗
      ((b + 117#64) ↦₈ v69) ∗
      ((b + 118#64) ↦₈ v70) ∗
      ((b + 119#64) ↦₈ v71) ∗
      ((b + 120#64) ↦₈ v72) ∗
      ((b + 121#64) ↦₈ v73) ∗
      ((b + 122#64) ↦₈ v74) ∗
      ((b + 123#64) ↦₈ v75) ∗
      ((b + 124#64) ↦₈ v76) ∗
      ((b + 125#64) ↦₈ v77) ∗
      ((b + 126#64) ↦₈ v78) ∗
      ((b + 127#64) ↦₈ v79) ∗
      ((b + 128#64) ↦₈ v80)) ⊢ memRegion b 129 := by
  rw [memRegion_partition b 129 [4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]]
  simp only [memRegion_one, memRegion_four, memRegion_eight]
  repeat (first | exact Entails.sepExists_intro _ | refine Entails.sepExists_intro_frame _ (sepConj_mono_right ?_))

/-- Fold the typed cells of a `129`-byte stack frame back into one region. -/
theorem SepWP.frame129_close {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    {v0 : BitVec 32} {v1 : BitVec 32} {v2 : BitVec 32} {v3 : BitVec 32} {v4 : BitVec 32} {v5 : BitVec 32} {v6 : BitVec 32} {v7 : BitVec 32} {v8 : BitVec 32} {v9 : BitVec 32} {v10 : BitVec 32} {v11 : BitVec 32} {v12 : BitVec 32} {v13 : BitVec 32} {v14 : BitVec 32} {v15 : BitVec 32} {v16 : BitVec 8} {v17 : BitVec 8} {v18 : BitVec 8} {v19 : BitVec 8} {v20 : BitVec 8} {v21 : BitVec 8} {v22 : BitVec 8} {v23 : BitVec 8} {v24 : BitVec 8} {v25 : BitVec 8} {v26 : BitVec 8} {v27 : BitVec 8} {v28 : BitVec 8} {v29 : BitVec 8} {v30 : BitVec 8} {v31 : BitVec 8} {v32 : BitVec 8} {v33 : BitVec 8} {v34 : BitVec 8} {v35 : BitVec 8} {v36 : BitVec 8} {v37 : BitVec 8} {v38 : BitVec 8} {v39 : BitVec 8} {v40 : BitVec 8} {v41 : BitVec 8} {v42 : BitVec 8} {v43 : BitVec 8} {v44 : BitVec 8} {v45 : BitVec 8} {v46 : BitVec 8} {v47 : BitVec 8} {v48 : BitVec 8} {v49 : BitVec 8} {v50 : BitVec 8} {v51 : BitVec 8} {v52 : BitVec 8} {v53 : BitVec 8} {v54 : BitVec 8} {v55 : BitVec 8} {v56 : BitVec 8} {v57 : BitVec 8} {v58 : BitVec 8} {v59 : BitVec 8} {v60 : BitVec 8} {v61 : BitVec 8} {v62 : BitVec 8} {v63 : BitVec 8} {v64 : BitVec 8} {v65 : BitVec 8} {v66 : BitVec 8} {v67 : BitVec 8} {v68 : BitVec 8} {v69 : BitVec 8} {v70 : BitVec 8} {v71 : BitVec 8} {v72 : BitVec 8} {v73 : BitVec 8} {v74 : BitVec 8} {v75 : BitVec 8} {v76 : BitVec 8} {v77 : BitVec 8} {v78 : BitVec 8} {v79 : BitVec 8} {v80 : BitVec 8}
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
      ((b + 48#64) ↦₃₂ v12) ∗
      ((b + 52#64) ↦₃₂ v13) ∗
      ((b + 56#64) ↦₃₂ v14) ∗
      ((b + 60#64) ↦₃₂ v15) ∗
      ((b + 64#64) ↦₈ v16) ∗
      ((b + 65#64) ↦₈ v17) ∗
      ((b + 66#64) ↦₈ v18) ∗
      ((b + 67#64) ↦₈ v19) ∗
      ((b + 68#64) ↦₈ v20) ∗
      ((b + 69#64) ↦₈ v21) ∗
      ((b + 70#64) ↦₈ v22) ∗
      ((b + 71#64) ↦₈ v23) ∗
      ((b + 72#64) ↦₈ v24) ∗
      ((b + 73#64) ↦₈ v25) ∗
      ((b + 74#64) ↦₈ v26) ∗
      ((b + 75#64) ↦₈ v27) ∗
      ((b + 76#64) ↦₈ v28) ∗
      ((b + 77#64) ↦₈ v29) ∗
      ((b + 78#64) ↦₈ v30) ∗
      ((b + 79#64) ↦₈ v31) ∗
      ((b + 80#64) ↦₈ v32) ∗
      ((b + 81#64) ↦₈ v33) ∗
      ((b + 82#64) ↦₈ v34) ∗
      ((b + 83#64) ↦₈ v35) ∗
      ((b + 84#64) ↦₈ v36) ∗
      ((b + 85#64) ↦₈ v37) ∗
      ((b + 86#64) ↦₈ v38) ∗
      ((b + 87#64) ↦₈ v39) ∗
      ((b + 88#64) ↦₈ v40) ∗
      ((b + 89#64) ↦₈ v41) ∗
      ((b + 90#64) ↦₈ v42) ∗
      ((b + 91#64) ↦₈ v43) ∗
      ((b + 92#64) ↦₈ v44) ∗
      ((b + 93#64) ↦₈ v45) ∗
      ((b + 94#64) ↦₈ v46) ∗
      ((b + 95#64) ↦₈ v47) ∗
      ((b + 96#64) ↦₈ v48) ∗
      ((b + 97#64) ↦₈ v49) ∗
      ((b + 98#64) ↦₈ v50) ∗
      ((b + 99#64) ↦₈ v51) ∗
      ((b + 100#64) ↦₈ v52) ∗
      ((b + 101#64) ↦₈ v53) ∗
      ((b + 102#64) ↦₈ v54) ∗
      ((b + 103#64) ↦₈ v55) ∗
      ((b + 104#64) ↦₈ v56) ∗
      ((b + 105#64) ↦₈ v57) ∗
      ((b + 106#64) ↦₈ v58) ∗
      ((b + 107#64) ↦₈ v59) ∗
      ((b + 108#64) ↦₈ v60) ∗
      ((b + 109#64) ↦₈ v61) ∗
      ((b + 110#64) ↦₈ v62) ∗
      ((b + 111#64) ↦₈ v63) ∗
      ((b + 112#64) ↦₈ v64) ∗
      ((b + 113#64) ↦₈ v65) ∗
      ((b + 114#64) ↦₈ v66) ∗
      ((b + 115#64) ↦₈ v67) ∗
      ((b + 116#64) ↦₈ v68) ∗
      ((b + 117#64) ↦₈ v69) ∗
      ((b + 118#64) ↦₈ v70) ∗
      ((b + 119#64) ↦₈ v71) ∗
      ((b + 120#64) ↦₈ v72) ∗
      ((b + 121#64) ↦₈ v73) ∗
      ((b + 122#64) ↦₈ v74) ∗
      ((b + 123#64) ↦₈ v75) ∗
      ((b + 124#64) ↦₈ v76) ∗
      ((b + 125#64) ↦₈ v77) ∗
      ((b + 126#64) ↦₈ v78) ∗
      ((b + 127#64) ↦₈ v79) ∗
      ((b + 128#64) ↦₈ v80)) ∗ F)
    (h : SepWP prog t s (memRegion b 129 ∗ F) post oom) :
    SepWP prog t s P post oom :=
  SepWP.weaken_pre (Entails.trans hf (sepConj_mono_left (frame129_fold b ..))) h

theorem cipherDrop_ok [CpPlacement] :
    subroutine_ok cpProg1r cpPl1.base (chachapolyLib.withCodeLoaded cpMpl cipherDropContract) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, cipherDropContract]
  wp_entry "core::ptr::drop_glue::<chacha20poly1305::cipher::Cipher<cipher::stream_wrapper::StreamCipherCoreWrapper<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>>>>>" c s0
  refine SepWP.frame129 (c + 56#64) (by sep_focus) ?_
  intro v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80
  simp only [BitVec.add_assoc] at *
  wp_steps
  refine SepWP.frame129_close (c + 56#64) (by simp only [BitVec.add_assoc]; sep_frame) ?_
  wp_done

end ChaChaPoly.Proofs
