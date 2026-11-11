import ChaChaPoly.Proofs
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec ChaChaPoly.Proofs
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
arm64_proof_prelude

/-- Open a `1168`-byte stack frame into the typed cells the function uses. -/
theorem SepWP.decFrame {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    (hf : P = memRegion b 1168 ∗ F := by sep_focus)
    (h : ∀ (v1 : BitVec 32) (v2 : BitVec 8) (v4 : BitVec 8) (v6 : BitVec 8) (v8 : BitVec 8) (v10 : BitVec 8) (v12 : BitVec 8) (v14 : BitVec 8) (v16 : BitVec 8) (v18 : BitVec 8) (v20 : BitVec 8) (v22 : BitVec 8) (v24 : BitVec 8) (v26 : BitVec 8) (v28 : BitVec 8) (v30 : BitVec 8) (v32 : BitVec 8) (v34 : BitVec 8) (v36 : BitVec 8) (v38 : BitVec 8) (v40 : BitVec 8) (v42 : BitVec 8) (v44 : BitVec 8) (v46 : BitVec 8) (v48 : BitVec 8) (v50 : BitVec 8) (v52 : BitVec 8) (v54 : BitVec 8) (v56 : BitVec 8) (v58 : BitVec 8) (v60 : BitVec 8) (v62 : BitVec 8) (v64 : BitVec 8) (v70 : BitVec 8) (v71 : BitVec 8) (v72 : BitVec 8) (v73 : BitVec 8) (v74 : BitVec 8) (v75 : BitVec 8) (v76 : BitVec 8) (v77 : BitVec 8) (v78 : BitVec 8) (v79 : BitVec 8) (v80 : BitVec 8) (v81 : BitVec 8) (v82 : BitVec 8) (v83 : BitVec 8) (v84 : BitVec 8) (v85 : BitVec 8) (v86 : BitVec 8) (v87 : BitVec 8) (v88 : BitVec 8) (v89 : BitVec 8) (v90 : BitVec 8) (v91 : BitVec 8) (v92 : BitVec 8) (v93 : BitVec 8) (v94 : BitVec 8) (v95 : BitVec 8) (v96 : BitVec 8) (v97 : BitVec 8) (v98 : BitVec 8) (v99 : BitVec 8) (v100 : BitVec 8) (v101 : BitVec 8) (v102 : BitVec 32) (v103 : BitVec 64) (v104 : BitVec 32) (v106 : BitVec 8) (v110 : BitVec 64) (v111 : BitVec 64) (v112 : BitVec 64) (v113 : BitVec 64) (v114 : BitVec 64) (v115 : BitVec 64) (v116 : BitVec 64) (v117 : BitVec 64) (v118 : BitVec 64) (v119 : BitVec 64) (v120 : BitVec 64) (v121 : BitVec 64), SepWP prog t s
      ((memRegion b 560 ∗
      ((b + 560#64) ↦₃₂ v1) ∗
      ((b + 564#64) ↦₈ v2) ∗
      memRegion (b + 565#64) 3 ∗
      ((b + 568#64) ↦₈ v4) ∗
      memRegion (b + 569#64) 3 ∗
      ((b + 572#64) ↦₈ v6) ∗
      memRegion (b + 573#64) 3 ∗
      ((b + 576#64) ↦₈ v8) ∗
      memRegion (b + 577#64) 3 ∗
      ((b + 580#64) ↦₈ v10) ∗
      memRegion (b + 581#64) 3 ∗
      ((b + 584#64) ↦₈ v12) ∗
      memRegion (b + 585#64) 3 ∗
      ((b + 588#64) ↦₈ v14) ∗
      memRegion (b + 589#64) 3 ∗
      ((b + 592#64) ↦₈ v16) ∗
      memRegion (b + 593#64) 3 ∗
      ((b + 596#64) ↦₈ v18) ∗
      memRegion (b + 597#64) 3 ∗
      ((b + 600#64) ↦₈ v20) ∗
      memRegion (b + 601#64) 3 ∗
      ((b + 604#64) ↦₈ v22) ∗
      memRegion (b + 605#64) 3 ∗
      ((b + 608#64) ↦₈ v24) ∗
      memRegion (b + 609#64) 3 ∗
      ((b + 612#64) ↦₈ v26) ∗
      memRegion (b + 613#64) 3 ∗
      ((b + 616#64) ↦₈ v28) ∗
      memRegion (b + 617#64) 3 ∗
      ((b + 620#64) ↦₈ v30) ∗
      memRegion (b + 621#64) 3 ∗
      ((b + 624#64) ↦₈ v32) ∗
      memRegion (b + 625#64) 3 ∗
      ((b + 628#64) ↦₈ v34) ∗
      memRegion (b + 629#64) 3 ∗
      ((b + 632#64) ↦₈ v36) ∗
      memRegion (b + 633#64) 3 ∗
      ((b + 636#64) ↦₈ v38) ∗
      memRegion (b + 637#64) 3 ∗
      ((b + 640#64) ↦₈ v40) ∗
      memRegion (b + 641#64) 3 ∗
      ((b + 644#64) ↦₈ v42) ∗
      memRegion (b + 645#64) 3 ∗
      ((b + 648#64) ↦₈ v44) ∗
      memRegion (b + 649#64) 3 ∗
      ((b + 652#64) ↦₈ v46) ∗
      memRegion (b + 653#64) 3 ∗
      ((b + 656#64) ↦₈ v48) ∗
      memRegion (b + 657#64) 3 ∗
      ((b + 660#64) ↦₈ v50) ∗
      memRegion (b + 661#64) 3 ∗
      ((b + 664#64) ↦₈ v52) ∗
      memRegion (b + 665#64) 3 ∗
      ((b + 668#64) ↦₈ v54) ∗
      memRegion (b + 669#64) 3 ∗
      ((b + 672#64) ↦₈ v56) ∗
      memRegion (b + 673#64) 3 ∗
      ((b + 676#64) ↦₈ v58) ∗
      memRegion (b + 677#64) 3 ∗
      ((b + 680#64) ↦₈ v60) ∗
      memRegion (b + 681#64) 3 ∗
      ((b + 684#64) ↦₈ v62) ∗
      memRegion (b + 685#64) 3 ∗
      ((b + 688#64) ↦₈ v64) ∗
      memRegion (b + 689#64) 3 ∗
      memRegion (b + 692#64) 56 ∗
      memRegion (b + 748#64) 129 ∗
      memRegion (b + 877#64) 3 ∗
      memRegion (b + 880#64) 16 ∗
      ((b + 896#64) ↦₈ v70) ∗
      ((b + 897#64) ↦₈ v71) ∗
      ((b + 898#64) ↦₈ v72) ∗
      ((b + 899#64) ↦₈ v73) ∗
      ((b + 900#64) ↦₈ v74) ∗
      ((b + 901#64) ↦₈ v75) ∗
      ((b + 902#64) ↦₈ v76) ∗
      ((b + 903#64) ↦₈ v77) ∗
      ((b + 904#64) ↦₈ v78) ∗
      ((b + 905#64) ↦₈ v79) ∗
      ((b + 906#64) ↦₈ v80) ∗
      ((b + 907#64) ↦₈ v81) ∗
      ((b + 908#64) ↦₈ v82) ∗
      ((b + 909#64) ↦₈ v83) ∗
      ((b + 910#64) ↦₈ v84) ∗
      ((b + 911#64) ↦₈ v85) ∗
      ((b + 912#64) ↦₈ v86) ∗
      ((b + 913#64) ↦₈ v87) ∗
      ((b + 914#64) ↦₈ v88) ∗
      ((b + 915#64) ↦₈ v89) ∗
      ((b + 916#64) ↦₈ v90) ∗
      ((b + 917#64) ↦₈ v91) ∗
      ((b + 918#64) ↦₈ v92) ∗
      ((b + 919#64) ↦₈ v93) ∗
      ((b + 920#64) ↦₈ v94) ∗
      ((b + 921#64) ↦₈ v95) ∗
      ((b + 922#64) ↦₈ v96) ∗
      ((b + 923#64) ↦₈ v97) ∗
      ((b + 924#64) ↦₈ v98) ∗
      ((b + 925#64) ↦₈ v99) ∗
      ((b + 926#64) ↦₈ v100) ∗
      ((b + 927#64) ↦₈ v101) ∗
      ((b + 928#64) ↦₃₂ v102) ∗
      ((b + 932#64) ↦₆₄ v103) ∗
      ((b + 940#64) ↦₃₂ v104) ∗
      memRegion (b + 944#64) 64 ∗
      ((b + 1008#64) ↦₈ v106) ∗
      memRegion (b + 1009#64) 15 ∗
      memRegion (b + 1024#64) 32 ∗
      memRegion (b + 1056#64) 16 ∗
      ((b + 1072#64) ↦₆₄ v110) ∗
      ((b + 1080#64) ↦₆₄ v111) ∗
      ((b + 1088#64) ↦₆₄ v112) ∗
      ((b + 1096#64) ↦₆₄ v113) ∗
      ((b + 1104#64) ↦₆₄ v114) ∗
      ((b + 1112#64) ↦₆₄ v115) ∗
      ((b + 1120#64) ↦₆₄ v116) ∗
      ((b + 1128#64) ↦₆₄ v117) ∗
      ((b + 1136#64) ↦₆₄ v118) ∗
      ((b + 1144#64) ↦₆₄ v119) ∗
      ((b + 1152#64) ↦₆₄ v120) ∗
      ((b + 1160#64) ↦₆₄ v121)) ∗ F) post oom) :
    SepWP prog t s P post oom := by
  subst hf
  rw [memRegion_partition b 1168 [560, 564, 565, 568, 569, 572, 573, 576, 577, 580, 581, 584, 585, 588, 589, 592, 593, 596, 597, 600, 601, 604, 605, 608, 609, 612, 613, 616, 617, 620, 621, 624, 625, 628, 629, 632, 633, 636, 637, 640, 641, 644, 645, 648, 649, 652, 653, 656, 657, 660, 661, 664, 665, 668, 669, 672, 673, 676, 677, 680, 681, 684, 685, 688, 689, 692, 748, 877, 880, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 932, 940, 944, 1008, 1009, 1024, 1056, 1072, 1080, 1088, 1096, 1104, 1112, 1120, 1128, 1136, 1144, 1152, 1160]]
  simp (maxSteps := 50000000) only [memRegion_one, memRegion_four, memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  exact h ..

theorem decFrame_fold (b : BitVec 64) (v1 : BitVec 32) (v2 : BitVec 8) (v4 : BitVec 8) (v6 : BitVec 8) (v8 : BitVec 8) (v10 : BitVec 8) (v12 : BitVec 8) (v14 : BitVec 8) (v16 : BitVec 8) (v18 : BitVec 8) (v20 : BitVec 8) (v22 : BitVec 8) (v24 : BitVec 8) (v26 : BitVec 8) (v28 : BitVec 8) (v30 : BitVec 8) (v32 : BitVec 8) (v34 : BitVec 8) (v36 : BitVec 8) (v38 : BitVec 8) (v40 : BitVec 8) (v42 : BitVec 8) (v44 : BitVec 8) (v46 : BitVec 8) (v48 : BitVec 8) (v50 : BitVec 8) (v52 : BitVec 8) (v54 : BitVec 8) (v56 : BitVec 8) (v58 : BitVec 8) (v60 : BitVec 8) (v62 : BitVec 8) (v64 : BitVec 8) (v70 : BitVec 8) (v71 : BitVec 8) (v72 : BitVec 8) (v73 : BitVec 8) (v74 : BitVec 8) (v75 : BitVec 8) (v76 : BitVec 8) (v77 : BitVec 8) (v78 : BitVec 8) (v79 : BitVec 8) (v80 : BitVec 8) (v81 : BitVec 8) (v82 : BitVec 8) (v83 : BitVec 8) (v84 : BitVec 8) (v85 : BitVec 8) (v86 : BitVec 8) (v87 : BitVec 8) (v88 : BitVec 8) (v89 : BitVec 8) (v90 : BitVec 8) (v91 : BitVec 8) (v92 : BitVec 8) (v93 : BitVec 8) (v94 : BitVec 8) (v95 : BitVec 8) (v96 : BitVec 8) (v97 : BitVec 8) (v98 : BitVec 8) (v99 : BitVec 8) (v100 : BitVec 8) (v101 : BitVec 8) (v102 : BitVec 32) (v103 : BitVec 64) (v104 : BitVec 32) (v106 : BitVec 8) (v110 : BitVec 64) (v111 : BitVec 64) (v112 : BitVec 64) (v113 : BitVec 64) (v114 : BitVec 64) (v115 : BitVec 64) (v116 : BitVec 64) (v117 : BitVec 64) (v118 : BitVec 64) (v119 : BitVec 64) (v120 : BitVec 64) (v121 : BitVec 64) :
    (memRegion b 560 ∗
      ((b + 560#64) ↦₃₂ v1) ∗
      ((b + 564#64) ↦₈ v2) ∗
      memRegion (b + 565#64) 3 ∗
      ((b + 568#64) ↦₈ v4) ∗
      memRegion (b + 569#64) 3 ∗
      ((b + 572#64) ↦₈ v6) ∗
      memRegion (b + 573#64) 3 ∗
      ((b + 576#64) ↦₈ v8) ∗
      memRegion (b + 577#64) 3 ∗
      ((b + 580#64) ↦₈ v10) ∗
      memRegion (b + 581#64) 3 ∗
      ((b + 584#64) ↦₈ v12) ∗
      memRegion (b + 585#64) 3 ∗
      ((b + 588#64) ↦₈ v14) ∗
      memRegion (b + 589#64) 3 ∗
      ((b + 592#64) ↦₈ v16) ∗
      memRegion (b + 593#64) 3 ∗
      ((b + 596#64) ↦₈ v18) ∗
      memRegion (b + 597#64) 3 ∗
      ((b + 600#64) ↦₈ v20) ∗
      memRegion (b + 601#64) 3 ∗
      ((b + 604#64) ↦₈ v22) ∗
      memRegion (b + 605#64) 3 ∗
      ((b + 608#64) ↦₈ v24) ∗
      memRegion (b + 609#64) 3 ∗
      ((b + 612#64) ↦₈ v26) ∗
      memRegion (b + 613#64) 3 ∗
      ((b + 616#64) ↦₈ v28) ∗
      memRegion (b + 617#64) 3 ∗
      ((b + 620#64) ↦₈ v30) ∗
      memRegion (b + 621#64) 3 ∗
      ((b + 624#64) ↦₈ v32) ∗
      memRegion (b + 625#64) 3 ∗
      ((b + 628#64) ↦₈ v34) ∗
      memRegion (b + 629#64) 3 ∗
      ((b + 632#64) ↦₈ v36) ∗
      memRegion (b + 633#64) 3 ∗
      ((b + 636#64) ↦₈ v38) ∗
      memRegion (b + 637#64) 3 ∗
      ((b + 640#64) ↦₈ v40) ∗
      memRegion (b + 641#64) 3 ∗
      ((b + 644#64) ↦₈ v42) ∗
      memRegion (b + 645#64) 3 ∗
      ((b + 648#64) ↦₈ v44) ∗
      memRegion (b + 649#64) 3 ∗
      ((b + 652#64) ↦₈ v46) ∗
      memRegion (b + 653#64) 3 ∗
      ((b + 656#64) ↦₈ v48) ∗
      memRegion (b + 657#64) 3 ∗
      ((b + 660#64) ↦₈ v50) ∗
      memRegion (b + 661#64) 3 ∗
      ((b + 664#64) ↦₈ v52) ∗
      memRegion (b + 665#64) 3 ∗
      ((b + 668#64) ↦₈ v54) ∗
      memRegion (b + 669#64) 3 ∗
      ((b + 672#64) ↦₈ v56) ∗
      memRegion (b + 673#64) 3 ∗
      ((b + 676#64) ↦₈ v58) ∗
      memRegion (b + 677#64) 3 ∗
      ((b + 680#64) ↦₈ v60) ∗
      memRegion (b + 681#64) 3 ∗
      ((b + 684#64) ↦₈ v62) ∗
      memRegion (b + 685#64) 3 ∗
      ((b + 688#64) ↦₈ v64) ∗
      memRegion (b + 689#64) 3 ∗
      memRegion (b + 692#64) 56 ∗
      memRegion (b + 748#64) 129 ∗
      memRegion (b + 877#64) 3 ∗
      memRegion (b + 880#64) 16 ∗
      ((b + 896#64) ↦₈ v70) ∗
      ((b + 897#64) ↦₈ v71) ∗
      ((b + 898#64) ↦₈ v72) ∗
      ((b + 899#64) ↦₈ v73) ∗
      ((b + 900#64) ↦₈ v74) ∗
      ((b + 901#64) ↦₈ v75) ∗
      ((b + 902#64) ↦₈ v76) ∗
      ((b + 903#64) ↦₈ v77) ∗
      ((b + 904#64) ↦₈ v78) ∗
      ((b + 905#64) ↦₈ v79) ∗
      ((b + 906#64) ↦₈ v80) ∗
      ((b + 907#64) ↦₈ v81) ∗
      ((b + 908#64) ↦₈ v82) ∗
      ((b + 909#64) ↦₈ v83) ∗
      ((b + 910#64) ↦₈ v84) ∗
      ((b + 911#64) ↦₈ v85) ∗
      ((b + 912#64) ↦₈ v86) ∗
      ((b + 913#64) ↦₈ v87) ∗
      ((b + 914#64) ↦₈ v88) ∗
      ((b + 915#64) ↦₈ v89) ∗
      ((b + 916#64) ↦₈ v90) ∗
      ((b + 917#64) ↦₈ v91) ∗
      ((b + 918#64) ↦₈ v92) ∗
      ((b + 919#64) ↦₈ v93) ∗
      ((b + 920#64) ↦₈ v94) ∗
      ((b + 921#64) ↦₈ v95) ∗
      ((b + 922#64) ↦₈ v96) ∗
      ((b + 923#64) ↦₈ v97) ∗
      ((b + 924#64) ↦₈ v98) ∗
      ((b + 925#64) ↦₈ v99) ∗
      ((b + 926#64) ↦₈ v100) ∗
      ((b + 927#64) ↦₈ v101) ∗
      ((b + 928#64) ↦₃₂ v102) ∗
      ((b + 932#64) ↦₆₄ v103) ∗
      ((b + 940#64) ↦₃₂ v104) ∗
      memRegion (b + 944#64) 64 ∗
      ((b + 1008#64) ↦₈ v106) ∗
      memRegion (b + 1009#64) 15 ∗
      memRegion (b + 1024#64) 32 ∗
      memRegion (b + 1056#64) 16 ∗
      ((b + 1072#64) ↦₆₄ v110) ∗
      ((b + 1080#64) ↦₆₄ v111) ∗
      ((b + 1088#64) ↦₆₄ v112) ∗
      ((b + 1096#64) ↦₆₄ v113) ∗
      ((b + 1104#64) ↦₆₄ v114) ∗
      ((b + 1112#64) ↦₆₄ v115) ∗
      ((b + 1120#64) ↦₆₄ v116) ∗
      ((b + 1128#64) ↦₆₄ v117) ∗
      ((b + 1136#64) ↦₆₄ v118) ∗
      ((b + 1144#64) ↦₆₄ v119) ∗
      ((b + 1152#64) ↦₆₄ v120) ∗
      ((b + 1160#64) ↦₆₄ v121)) ⊢ memRegion b 1168 := by
  rw [memRegion_partition b 1168 [560, 564, 565, 568, 569, 572, 573, 576, 577, 580, 581, 584, 585, 588, 589, 592, 593, 596, 597, 600, 601, 604, 605, 608, 609, 612, 613, 616, 617, 620, 621, 624, 625, 628, 629, 632, 633, 636, 637, 640, 641, 644, 645, 648, 649, 652, 653, 656, 657, 660, 661, 664, 665, 668, 669, 672, 673, 676, 677, 680, 681, 684, 685, 688, 689, 692, 748, 877, 880, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 932, 940, 944, 1008, 1009, 1024, 1056, 1072, 1080, 1088, 1096, 1104, 1112, 1120, 1128, 1136, 1144, 1152, 1160]]
  repeat' (first
    | exact Entails.refl _
    | exact pointsTo64_entails_memRegion _ _
    | exact pointsTo32_entails_memRegion _ _
    | exact pointsTo8_entails_memRegion _ _
    | refine sepConj_mono ?_ ?_)

/-- Fold the typed cells of a `1168`-byte stack frame back into one region. -/
theorem SepWP.decFrame_close {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    {v1 : BitVec 32} {v2 : BitVec 8} {v4 : BitVec 8} {v6 : BitVec 8} {v8 : BitVec 8} {v10 : BitVec 8} {v12 : BitVec 8} {v14 : BitVec 8} {v16 : BitVec 8} {v18 : BitVec 8} {v20 : BitVec 8} {v22 : BitVec 8} {v24 : BitVec 8} {v26 : BitVec 8} {v28 : BitVec 8} {v30 : BitVec 8} {v32 : BitVec 8} {v34 : BitVec 8} {v36 : BitVec 8} {v38 : BitVec 8} {v40 : BitVec 8} {v42 : BitVec 8} {v44 : BitVec 8} {v46 : BitVec 8} {v48 : BitVec 8} {v50 : BitVec 8} {v52 : BitVec 8} {v54 : BitVec 8} {v56 : BitVec 8} {v58 : BitVec 8} {v60 : BitVec 8} {v62 : BitVec 8} {v64 : BitVec 8} {v70 : BitVec 8} {v71 : BitVec 8} {v72 : BitVec 8} {v73 : BitVec 8} {v74 : BitVec 8} {v75 : BitVec 8} {v76 : BitVec 8} {v77 : BitVec 8} {v78 : BitVec 8} {v79 : BitVec 8} {v80 : BitVec 8} {v81 : BitVec 8} {v82 : BitVec 8} {v83 : BitVec 8} {v84 : BitVec 8} {v85 : BitVec 8} {v86 : BitVec 8} {v87 : BitVec 8} {v88 : BitVec 8} {v89 : BitVec 8} {v90 : BitVec 8} {v91 : BitVec 8} {v92 : BitVec 8} {v93 : BitVec 8} {v94 : BitVec 8} {v95 : BitVec 8} {v96 : BitVec 8} {v97 : BitVec 8} {v98 : BitVec 8} {v99 : BitVec 8} {v100 : BitVec 8} {v101 : BitVec 8} {v102 : BitVec 32} {v103 : BitVec 64} {v104 : BitVec 32} {v106 : BitVec 8} {v110 : BitVec 64} {v111 : BitVec 64} {v112 : BitVec 64} {v113 : BitVec 64} {v114 : BitVec 64} {v115 : BitVec 64} {v116 : BitVec 64} {v117 : BitVec 64} {v118 : BitVec 64} {v119 : BitVec 64} {v120 : BitVec 64} {v121 : BitVec 64}
    (hf : P ⊢ (memRegion b 560 ∗
      ((b + 560#64) ↦₃₂ v1) ∗
      ((b + 564#64) ↦₈ v2) ∗
      memRegion (b + 565#64) 3 ∗
      ((b + 568#64) ↦₈ v4) ∗
      memRegion (b + 569#64) 3 ∗
      ((b + 572#64) ↦₈ v6) ∗
      memRegion (b + 573#64) 3 ∗
      ((b + 576#64) ↦₈ v8) ∗
      memRegion (b + 577#64) 3 ∗
      ((b + 580#64) ↦₈ v10) ∗
      memRegion (b + 581#64) 3 ∗
      ((b + 584#64) ↦₈ v12) ∗
      memRegion (b + 585#64) 3 ∗
      ((b + 588#64) ↦₈ v14) ∗
      memRegion (b + 589#64) 3 ∗
      ((b + 592#64) ↦₈ v16) ∗
      memRegion (b + 593#64) 3 ∗
      ((b + 596#64) ↦₈ v18) ∗
      memRegion (b + 597#64) 3 ∗
      ((b + 600#64) ↦₈ v20) ∗
      memRegion (b + 601#64) 3 ∗
      ((b + 604#64) ↦₈ v22) ∗
      memRegion (b + 605#64) 3 ∗
      ((b + 608#64) ↦₈ v24) ∗
      memRegion (b + 609#64) 3 ∗
      ((b + 612#64) ↦₈ v26) ∗
      memRegion (b + 613#64) 3 ∗
      ((b + 616#64) ↦₈ v28) ∗
      memRegion (b + 617#64) 3 ∗
      ((b + 620#64) ↦₈ v30) ∗
      memRegion (b + 621#64) 3 ∗
      ((b + 624#64) ↦₈ v32) ∗
      memRegion (b + 625#64) 3 ∗
      ((b + 628#64) ↦₈ v34) ∗
      memRegion (b + 629#64) 3 ∗
      ((b + 632#64) ↦₈ v36) ∗
      memRegion (b + 633#64) 3 ∗
      ((b + 636#64) ↦₈ v38) ∗
      memRegion (b + 637#64) 3 ∗
      ((b + 640#64) ↦₈ v40) ∗
      memRegion (b + 641#64) 3 ∗
      ((b + 644#64) ↦₈ v42) ∗
      memRegion (b + 645#64) 3 ∗
      ((b + 648#64) ↦₈ v44) ∗
      memRegion (b + 649#64) 3 ∗
      ((b + 652#64) ↦₈ v46) ∗
      memRegion (b + 653#64) 3 ∗
      ((b + 656#64) ↦₈ v48) ∗
      memRegion (b + 657#64) 3 ∗
      ((b + 660#64) ↦₈ v50) ∗
      memRegion (b + 661#64) 3 ∗
      ((b + 664#64) ↦₈ v52) ∗
      memRegion (b + 665#64) 3 ∗
      ((b + 668#64) ↦₈ v54) ∗
      memRegion (b + 669#64) 3 ∗
      ((b + 672#64) ↦₈ v56) ∗
      memRegion (b + 673#64) 3 ∗
      ((b + 676#64) ↦₈ v58) ∗
      memRegion (b + 677#64) 3 ∗
      ((b + 680#64) ↦₈ v60) ∗
      memRegion (b + 681#64) 3 ∗
      ((b + 684#64) ↦₈ v62) ∗
      memRegion (b + 685#64) 3 ∗
      ((b + 688#64) ↦₈ v64) ∗
      memRegion (b + 689#64) 3 ∗
      memRegion (b + 692#64) 56 ∗
      memRegion (b + 748#64) 129 ∗
      memRegion (b + 877#64) 3 ∗
      memRegion (b + 880#64) 16 ∗
      ((b + 896#64) ↦₈ v70) ∗
      ((b + 897#64) ↦₈ v71) ∗
      ((b + 898#64) ↦₈ v72) ∗
      ((b + 899#64) ↦₈ v73) ∗
      ((b + 900#64) ↦₈ v74) ∗
      ((b + 901#64) ↦₈ v75) ∗
      ((b + 902#64) ↦₈ v76) ∗
      ((b + 903#64) ↦₈ v77) ∗
      ((b + 904#64) ↦₈ v78) ∗
      ((b + 905#64) ↦₈ v79) ∗
      ((b + 906#64) ↦₈ v80) ∗
      ((b + 907#64) ↦₈ v81) ∗
      ((b + 908#64) ↦₈ v82) ∗
      ((b + 909#64) ↦₈ v83) ∗
      ((b + 910#64) ↦₈ v84) ∗
      ((b + 911#64) ↦₈ v85) ∗
      ((b + 912#64) ↦₈ v86) ∗
      ((b + 913#64) ↦₈ v87) ∗
      ((b + 914#64) ↦₈ v88) ∗
      ((b + 915#64) ↦₈ v89) ∗
      ((b + 916#64) ↦₈ v90) ∗
      ((b + 917#64) ↦₈ v91) ∗
      ((b + 918#64) ↦₈ v92) ∗
      ((b + 919#64) ↦₈ v93) ∗
      ((b + 920#64) ↦₈ v94) ∗
      ((b + 921#64) ↦₈ v95) ∗
      ((b + 922#64) ↦₈ v96) ∗
      ((b + 923#64) ↦₈ v97) ∗
      ((b + 924#64) ↦₈ v98) ∗
      ((b + 925#64) ↦₈ v99) ∗
      ((b + 926#64) ↦₈ v100) ∗
      ((b + 927#64) ↦₈ v101) ∗
      ((b + 928#64) ↦₃₂ v102) ∗
      ((b + 932#64) ↦₆₄ v103) ∗
      ((b + 940#64) ↦₃₂ v104) ∗
      memRegion (b + 944#64) 64 ∗
      ((b + 1008#64) ↦₈ v106) ∗
      memRegion (b + 1009#64) 15 ∗
      memRegion (b + 1024#64) 32 ∗
      memRegion (b + 1056#64) 16 ∗
      ((b + 1072#64) ↦₆₄ v110) ∗
      ((b + 1080#64) ↦₆₄ v111) ∗
      ((b + 1088#64) ↦₆₄ v112) ∗
      ((b + 1096#64) ↦₆₄ v113) ∗
      ((b + 1104#64) ↦₆₄ v114) ∗
      ((b + 1112#64) ↦₆₄ v115) ∗
      ((b + 1120#64) ↦₆₄ v116) ∗
      ((b + 1128#64) ↦₆₄ v117) ∗
      ((b + 1136#64) ↦₆₄ v118) ∗
      ((b + 1144#64) ↦₆₄ v119) ∗
      ((b + 1152#64) ↦₆₄ v120) ∗
      ((b + 1160#64) ↦₆₄ v121)) ∗ F)
    (h : SepWP prog t s (memRegion b 1168 ∗ F) post oom) :
    SepWP prog t s P post oom :=
  SepWP.weaken_pre (Entails.trans hf (sepConj_mono_left (decFrame_fold b ..))) h

set_option maxRecDepth 400000 in
theorem decrypt_draft [CpPlacement] :
    subroutine_ok cpProg5r cpPl5.base
      (chachapolyLib.withCodeLoaded cpMpl (aeadDecryptContract (cpMpl.ρ sigmaSym))) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, aeadDecryptContract, aeadPre]
  wp_entry "chachapoly_decrypt" g s0
  obtain ⟨key, nonce, aad, buf, tag, k, n, a, msg, t⟩ := g
  simp only at *
  refine SepWP.decFrame (s0.sp - 0x490#64) (by sep_focus) ?_
  intros
  have hρ : cpPl5.ρ "chachapoly_verified:.rodata.cst16+0x0" = cpMpl.ρ sigmaSym := by
    have h : Obj.lookupBlockSym "chachapoly_verified:.rodata.cst16+0x0" chachapolyLib.blocks = none := by
      decide +kernel
    simp [cpPl5, sigmaSym, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x204#64) h ?_
  refine Proofs.SepWP.memRegion_bytes (s0.sp - 1168#64 + 880#64) 16 (by decide) (by sep_focus) fun cs0 hcs0 => ?_
  refine Proofs.SepWP.memRegion_bytes (s0.sp - 1168#64 + 944#64) 64 (by decide) (by sep_focus) fun cb0 hcb0 => ?_
  refine Proofs.SepWP.memRegion_bytes (s0.sp - 1168#64 + 1024#64) 32 (by decide) (by sep_focus) fun mk0 hmk0 => ?_
  wp_steps 129
  refine Proofs.SepWP.foldPart (encState_fold (s0.sp - 288#64) k n cs0 cb0 (by assumption) (by assumption)
    hcs0 hcb0) (by sep_focus) ?_
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  intro hcl
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x210#64) hcl ?_
  rw [zero_chain32 mk0 hmk0]
  have hal := aligned_sub hsp_align 608 (by decide) (by decide)
  wp_step
  have hr : cpPl5.ρ "<cipher::stream_wrapper::StreamCipherCoreWrapper<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>>> as cipher::stream::StreamCipher>::apply_keystream" = cpPl4.base := by
    have h : Obj.lookupBlockSym "<cipher::stream_wrapper::StreamCipherCoreWrapper<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>>> as cipher::stream::StreamCipher>::apply_keystream" chachapolyLib.blocks = some (4, 0) := by decide +kernel
    simp [cpPl5, cpPl4, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]
  rw [hr, show cpPl5.base + 516#64 + (cpPl4.base - cpPl5.base - 516#64) = cpPl4.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 4) (by decide) ak_blk_ok
    (x := ⟨s0.sp - 288#64, s0.sp - 144#64, List.replicate 32 0#8, initState k 0 n, zeroState⟩)
    (ret_pc := cpPl5.base + 520#64) (F := ?F)
    (by simpa [wp_norm, arm64_norm] using hcl) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, State.spAligned]; simpa using hsp_align)
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, applyKeystreamContract, stackFrame]
    simp only [wp_norm, arm64_norm, hcl, and_self, pure_true_sepConj, sepConj_pure_true] at hm hcl ⊢
    refine ⟨⟨⟨by simp, by simp [initState]⟩, hcl⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  · intro sf hpcf hrunf hspf hcsf
    show SepWP cpProg5r _ _ _ _ _
    simp only [MultiPlacedLib.withCodeLoaded, applyKeystreamContract, stackFrame, wp_norm,
      arm64_norm] at hspf hcsf ⊢
    obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcsf
    simp only [wp_norm, arm64_norm] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 cv hspf
    wp_steps 2
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf]) ?_
    intro hcl2
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x2e4#64) hcl2 ?_
    refine SepWP.exists_elim fun kb => ?_
    wp_step
    have hr2 : cpPl5.ρ "<poly1305::Poly1305 as crypto_common::KeyInit>::new" = cpPl10.base := by
      have h : Obj.lookupBlockSym "<poly1305::Poly1305 as crypto_common::KeyInit>::new" chachapolyLib.blocks = some (10, 0) := by decide +kernel
      simp [cpPl5, cpPl10, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]
    rw [hr2, show cpPl5.base + 528#64 + (cpPl10.base - cpPl5.base - 528#64) = cpPl10.base by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
    refine MultiPlacedLib.sepWP_call_block (j := 10) (by decide) pn_blk_ok
      (x := (s0.sp - 144#64, s0.sp - 476#64, streamXor (initState k 0 n) (List.replicate 32 0#8)))
      (ret_pc := cpPl5.base + 532#64) (F := ?F2)
      (by simpa [wp_norm, arm64_norm] using hcl2) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrunf]) (by simp [wp_norm, arm64_norm, State.spAligned, hspf]; simpa using hsp_align)
      (by simp [wp_norm, arm64_norm]) ?_
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
    rotate_left
    · intro R hm
      simp only [MultiPlacedLib.withCodeLoaded, polyNewContract]
      simp only [wp_norm, arm64_norm, hcl2, and_self, pure_true_sepConj, sepConj_pure_true, c29] at hm hcl2 ⊢
      refine ⟨⟨by rw [streamXor_length _ _ _ rfl]; simp, hcl2⟩, ?_⟩
      simp only [← sepConj_assoc] at hm ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      simp only [sepConj_assoc]
      sep_frame
    · intro sf2 hpcf2 hrunf2 hspf2 hcsf2
      show SepWP cpProg5r _ _ _ _ _
      simp only [MultiPlacedLib.withCodeLoaded, polyNewContract, wp_norm, arm64_norm] at hspf2 hcsf2 ⊢
      obtain ⟨d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, dv⟩ := hcsf2
      simp only [wp_norm, arm64_norm, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv, hspf] at d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 dv hspf2
      refine SepWP.exists_elim fun pw => SepWP.exists_elim fun pl => ?_
      refine SepWP.pure_elim fun ⟨hpw, hpl⟩ => ?_
      rw [stateAt_eq_bytes (s0.sp - 288#64), stateAt_eq_bytes (s0.sp - 224#64)]
      refine Proofs.SepWP.foldPart (Entails.of_eq_explicit (SepFrameInfer.memRegion_merge (s0.sp - 420#64)
        (s0.sp - 291#64) 129 3 132 (by bv_omega) rfl (by decide))) (by sep_focus) ?_
      refine Proofs.SepWP.foldPart (Entails.of_eq_explicit (memRegion_partition (s0.sp - 420#64) 132
        [16, 32, 48, 64, 80, 96, 112, 128])) (by sep_focus) ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 420#64 + 0#64) 16 (by decide) (by sep_focus) fun q0 hq0 => ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 420#64 + 16#64) 16 (by decide) (by sep_focus) fun q1 hq1 => ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 420#64 + 32#64) 16 (by decide) (by sep_focus) fun q2 hq2 => ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 420#64 + 48#64) 16 (by decide) (by sep_focus) fun q3 hq3 => ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 420#64 + 64#64) 16 (by decide) (by sep_focus) fun q4 hq4 => ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 420#64 + 80#64) 16 (by decide) (by sep_focus) fun q5 hq5 => ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 420#64 + 96#64) 16 (by decide) (by sep_focus) fun q6 hq6 => ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 420#64 + 112#64) 16 (by decide) (by sep_focus) fun q7 hq7 => ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 420#64 + 128#64) 4 (by decide) (by sep_focus) fun qp hqp => ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 159#64) 15 (by decide) (by sep_focus) fun pr hpr => ?_
      refine Proofs.SepWP.foldPart (Entails.of_eq_explicit (pointsToBytes_cons (s0.sp - 160#64) 32#8 pr).symm)
        (by sep_focus) ?_
      have hmkl : (streamXor (initState k 0 n) (List.replicate 32 0#8)).length = 32 := by
        rw [streamXor_length _ _ _ rfl]; simp
      have hkbl : kb.bytes.length = 64 := by simp [Spec.State.bytes, word32Bytes]
      have hsl : ((initState k 0 n).advance (((List.replicate 32 0#8).length + 63) / 64)).bytes.length = 64 := by
        simp [Spec.State.bytes, word32Bytes]
      have h1blk : ((List.replicate 32 0#8).length + 63) / 64 = 1 := by simp
      simp only [h1blk] at hsl ⊢
      generalize hmkeq : streamXor (initState k 0 n) (List.replicate 32 0#8) = mk at *
      generalize hkbeq : kb.bytes = kbb at *
      generalize hsbeq : ((initState k 0 n).advance 1).bytes = sb at *
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf2]) ?_
      intro hcl3
      have hml : msg.length ≤ maxMsgLen := by assumption
      have hhi : (274877906879#64).ult (BitVec.ofNat 64 msg.length) = false := by
        simp only [maxMsgLen] at hml; simp [BitVec.ult]; omega
      wp_step
      refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x358#64) (by simpa [wp_norm, arm64_norm] using hcl3) ?_
      have hsbl : (ByteSlice.write32 sb 48 1#32).length = 64 := by simp [hsl]
      rw [show ((s0.sp - 288#64) ↦ₛ ByteSlice.write32 sb 48 1#32) =
          ((s0.sp - 288#64) ↦ₛ (ByteSlice.write32 sb 48 1#32).take 16) ∗
          ((s0.sp - 288#64 + 16#64) ↦ₛ (ByteSlice.write32 sb 48 1#32).drop 16) by
        conv => lhs; rw [← List.take_append_drop 16 (ByteSlice.write32 sb 48 1#32)]
        rw [pointsToBytes_append, show ((ByteSlice.write32 sb 48 1#32).take 16).length = 16 by simp; omega]]
      refine SepWP.mono (SepWP.weaken_pre ?_ (dmacAad_ok ?FA _ aad (s0.sp - 288#64) a
        ((ByteSlice.write32 sb 48 1#32).take 16) (clamp (leNat (mk.take 16))) 0 pl
        (by simp [wp_norm, arm64_norm, hhi]) (by simp [wp_norm, arm64_norm, hrunf2])
        (by simp [wp_norm, arm64_norm, hspf2]; simpa using hsp_align)
        (by simpa [wp_norm, arm64_norm] using hcl3)
        (by simp [wp_norm, arm64_norm, d27]) (by simp [wp_norm, arm64_norm, d23])
        (by simp [wp_norm, arm64_norm, d29]; try bv_omega) (by assumption) (by simp; omega) hpl)) ?_
      · try simp only [wp_norm, arm64_norm, hspf2]
        simp only [← sepConj_assoc]
        sep_frame
      intro sf3 Pf3 hpc3 hrun3 ⟨hk3, hQ3⟩ hcl4
      refine SepWP.weaken_pre hQ3 ?_
      refine SepWP.exists_elim fun l1 => SepWP.exists_elim fun blk1 => ?_
      refine SepWP.pure_elim fun ⟨hl1, hblk1⟩ => ?_
      obtain ⟨k1s, k19, k21, k22, k23, k25, k29, kv⟩ := hk3
      simp only [wp_norm, arm64_norm] at k1s k19 k21 k22 k23 k25 k29 kv
      refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x3c4#64) hcl4 ?_
      refine SepWP.mono (SepWP.weaken_pre ?_ (dmacCt_ok ?FC _ buf (s0.sp - 288#64)
        msg blk1 (clamp (leNat (mk.take 16)))
        (polyBlocks (clamp (leNat (mk.take 16))) 0 (a ++ pad16 a)) l1
        hpc3 hrun3
        (by simp [wp_norm, arm64_norm, k1s, hspf2]; simpa using hsp_align) hcl4
        (by simp [wp_norm, arm64_norm, k19, d19])
        (by simp [wp_norm, arm64_norm, k22, d20])
        (by simp [wp_norm, arm64_norm, k29, d29]; try bv_omega)
        (by simp only [maxMsgLen] at hml; omega) hblk1 hl1)) ?_
      · try simp only [wp_norm, arm64_norm, k1s, hspf2]
        simp only [← sepConj_assoc]
        sep_frame
      intro sf5 Pf5 hpc5 hrun5 ⟨hk5, hQ5⟩ hcl6
      refine SepWP.weaken_pre hQ5 ?_
      refine SepWP.exists_elim fun l2 => SepWP.exists_elim fun blk2 => ?_
      refine SepWP.pure_elim fun ⟨hl2, hblk2⟩ => ?_
      obtain ⟨g1, g19, g21, g22, g24, g25, g29, gv⟩ := hk5
      simp only [wp_norm, arm64_norm] at g1 g19 g21 g22 g24 g25 g29 gv
      trace_state
      sorry
