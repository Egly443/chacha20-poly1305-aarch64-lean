import ChaChaPoly.Proofs
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec ChaChaPoly.Proofs
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
arm64_proof_prelude
open ChaChaPoly.Spec

open ChaChaPoly.Spec
theorem sigma_chain (bs : List (BitVec 8)) (h : bs.length = 16) :
    ByteSlice.write64 (ByteSlice.write64 bs 0 3684054920433006693#64) 8 7719281312240119090#64 = sigmaBytes := by
  match bs, h with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: [], _ => rfl

theorem zero_chain64 (bs : List (BitVec 8)) (h : bs.length = 64) :
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 bs 0 0#64) 8 0#64) 16 0#64) 24 0#64) 32 0#64) 40 0#64) 48 0#64) 56 0#64) = List.replicate 64 0#8 := by
  match bs, h with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: a20 :: a21 :: a22 :: a23 :: a24 :: a25 :: a26 :: a27 :: a28 :: a29 :: a30 :: a31 :: a32 :: a33 :: a34 :: a35 :: a36 :: a37 :: a38 :: a39 :: a40 :: a41 :: a42 :: a43 :: a44 :: a45 :: a46 :: a47 :: a48 :: a49 :: a50 :: a51 :: a52 :: a53 :: a54 :: a55 :: a56 :: a57 :: a58 :: a59 :: a60 :: a61 :: a62 :: a63 :: [], _ => rfl

theorem zero_chain32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 bs 0 0#64) 8 0#64) 16 0#64) 24 0#64) = List.replicate 32 0#8 := by
  match bs, h with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: a20 :: a21 :: a22 :: a23 :: a24 :: a25 :: a26 :: a27 :: a28 :: a29 :: a30 :: a31 :: [], _ => rfl

/-- The all-zero ChaCha state (the fresh key-stream buffer). -/
def zeroState : Spec.State := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

theorem unpack64_readLE_nonce (n : Bytes) (hn : n.length = 12) :
    unpack64 (ByteSlice.readLE n 0 8) = n.take 8 := by
  have h : unpack64 (ByteSlice.readLE n 0 8) = ByteSlice.unpackLE 8 (ByteSlice.readLE n 0 8) := rfl
  rw [h, ByteSlice.unpackLE_readLE n 0 8 (by omega)]
  rfl

/-- The cells the encrypt prologue writes at `c` (constant, key bytes, counter 0, nonce, zeroed
    key-stream buffer) form the RFC 8439 initial state for counter 0 and an empty buffer. -/
theorem encState_fold (c : BitVec 64) (k n cs0 cb0 : Bytes) (hk : k.length = 32)
    (hn : n.length = 12) (hcs : cs0.length = 16) (hcb : cb0.length = 64) :
    ((c ↦ₛ ByteSlice.write64 (ByteSlice.write64 cs0 0 3684054920433006693#64) 8
        7719281312240119090#64) ∗
    ((c + 16#64) ↦₈ k.getD 0 0#8) ∗
    ((c + 17#64) ↦₈ k.getD 1 0#8) ∗
    ((c + 18#64) ↦₈ k.getD 2 0#8) ∗
    ((c + 19#64) ↦₈ k.getD 3 0#8) ∗
    ((c + 20#64) ↦₈ k.getD 4 0#8) ∗
    ((c + 21#64) ↦₈ k.getD 5 0#8) ∗
    ((c + 22#64) ↦₈ k.getD 6 0#8) ∗
    ((c + 23#64) ↦₈ k.getD 7 0#8) ∗
    ((c + 24#64) ↦₈ k.getD 8 0#8) ∗
    ((c + 25#64) ↦₈ k.getD 9 0#8) ∗
    ((c + 26#64) ↦₈ k.getD 10 0#8) ∗
    ((c + 27#64) ↦₈ k.getD 11 0#8) ∗
    ((c + 28#64) ↦₈ k.getD 12 0#8) ∗
    ((c + 29#64) ↦₈ k.getD 13 0#8) ∗
    ((c + 30#64) ↦₈ k.getD 14 0#8) ∗
    ((c + 31#64) ↦₈ k.getD 15 0#8) ∗
    ((c + 32#64) ↦₈ k.getD 16 0#8) ∗
    ((c + 33#64) ↦₈ k.getD 17 0#8) ∗
    ((c + 34#64) ↦₈ k.getD 18 0#8) ∗
    ((c + 35#64) ↦₈ k.getD 19 0#8) ∗
    ((c + 36#64) ↦₈ k.getD 20 0#8) ∗
    ((c + 37#64) ↦₈ k.getD 21 0#8) ∗
    ((c + 38#64) ↦₈ k.getD 22 0#8) ∗
    ((c + 39#64) ↦₈ k.getD 23 0#8) ∗
    ((c + 40#64) ↦₈ k.getD 24 0#8) ∗
    ((c + 41#64) ↦₈ k.getD 25 0#8) ∗
    ((c + 42#64) ↦₈ k.getD 26 0#8) ∗
    ((c + 43#64) ↦₈ k.getD 27 0#8) ∗
    ((c + 44#64) ↦₈ k.getD 28 0#8) ∗
    ((c + 45#64) ↦₈ k.getD 29 0#8) ∗
    ((c + 46#64) ↦₈ k.getD 30 0#8) ∗
    ((c + 47#64) ↦₈ k.getD 31 0#8) ∗
    ((c + 48#64) ↦₃₂ 0#32) ∗ ((c + 52#64) ↦₆₄ ByteSlice.readLE n 0 8) ∗
    ((c + 60#64) ↦₃₂ pack32 (n.getD 8 0#8) (n.getD 9 0#8) (n.getD 10 0#8) (n.getD 11 0#8)) ∗
    ((c + 64#64) ↦ₛ (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 cb0 0 0#64) 8 0#64) 16 0#64) 24 0#64) 32 0#64) 40 0#64) 48 0#64) 56 0#64))) ⊢
    stateAt c (initState k 0 n) ∗ stateAt (c + 64#64) zeroState := by
  rw [sigma_chain cs0 hcs, zero_chain64 cb0 hcb, stateAt_eq_bytes (c + 64#64),
    show zeroState.bytes = List.replicate 64 0#8 from rfl,
    pointsTo64_eq_pointsToBytes, unpack64_readLE_nonce n hn]
  have hσ : sigmaBytes = word32Bytes 0x61707865#32 ++ (word32Bytes 0x3320646e#32 ++
      (word32Bytes 0x79622d32#32 ++ word32Bytes 0x6b206574#32)) := by decide
  have hl : ∀ w : BitVec 32, (word32Bytes w).length = 4 := fun _ => rfl
  rw [hσ]
  simp only [pointsToBytes_append, hl, List.length_append, BitVec.add_assoc]
  match k, hk, n, hn with
  | k0 :: k1 :: k2 :: k3 :: k4 :: k5 :: k6 :: k7 :: k8 :: k9 :: k10 :: k11 :: k12 :: k13 :: k14 :: k15 :: k16 :: k17 :: k18 :: k19 :: k20 :: k21 :: k22 :: k23 :: k24 :: k25 :: k26 :: k27 :: k28 :: k29 :: k30 :: k31 :: [], _, n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: [], _ =>
    simp only [stateAt, initState, word32At, byteAt, List.getD_cons_succ, List.getD_cons_zero,
      List.take, pack32, ← pointsTo32_eq_word32Bytes, ← pointsToBytes4_eq_pointsTo32,
      pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    sep_entail



/-- Open a `1184`-byte stack frame into the typed cells the function uses. -/
theorem SepWP.encFrame {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    (hf : P = memRegion b 1184 ∗ F := by sep_focus)
    (h : ∀ (v1 : BitVec 64) (v2 : BitVec 64) (v3 : BitVec 32) (v4 : BitVec 8) (v6 : BitVec 8) (v8 : BitVec 8) (v10 : BitVec 8) (v12 : BitVec 8) (v14 : BitVec 8) (v16 : BitVec 8) (v18 : BitVec 8) (v20 : BitVec 8) (v22 : BitVec 8) (v24 : BitVec 8) (v26 : BitVec 8) (v28 : BitVec 8) (v30 : BitVec 8) (v32 : BitVec 8) (v34 : BitVec 8) (v36 : BitVec 8) (v38 : BitVec 8) (v40 : BitVec 8) (v42 : BitVec 8) (v44 : BitVec 8) (v46 : BitVec 8) (v48 : BitVec 8) (v50 : BitVec 8) (v52 : BitVec 8) (v54 : BitVec 8) (v56 : BitVec 8) (v58 : BitVec 8) (v60 : BitVec 8) (v62 : BitVec 8) (v64 : BitVec 8) (v66 : BitVec 8) (v72 : BitVec 8) (v73 : BitVec 8) (v74 : BitVec 8) (v75 : BitVec 8) (v76 : BitVec 8) (v77 : BitVec 8) (v78 : BitVec 8) (v79 : BitVec 8) (v80 : BitVec 8) (v81 : BitVec 8) (v82 : BitVec 8) (v83 : BitVec 8) (v84 : BitVec 8) (v85 : BitVec 8) (v86 : BitVec 8) (v87 : BitVec 8) (v88 : BitVec 8) (v89 : BitVec 8) (v90 : BitVec 8) (v91 : BitVec 8) (v92 : BitVec 8) (v93 : BitVec 8) (v94 : BitVec 8) (v95 : BitVec 8) (v96 : BitVec 8) (v97 : BitVec 8) (v98 : BitVec 8) (v99 : BitVec 8) (v100 : BitVec 8) (v101 : BitVec 8) (v102 : BitVec 8) (v103 : BitVec 8) (v104 : BitVec 32) (v105 : BitVec 64) (v106 : BitVec 32) (v108 : BitVec 8) (v112 : BitVec 64) (v113 : BitVec 64) (v114 : BitVec 64) (v115 : BitVec 64) (v116 : BitVec 64) (v117 : BitVec 64) (v118 : BitVec 64) (v119 : BitVec 64) (v120 : BitVec 64) (v121 : BitVec 64) (v122 : BitVec 64) (v123 : BitVec 64), SepWP prog t s
      ((memRegion b 560 ∗
      ((b + 560#64) ↦₆₄ v1) ∗
      ((b + 568#64) ↦₆₄ v2) ∗
      ((b + 576#64) ↦₃₂ v3) ∗
      ((b + 580#64) ↦₈ v4) ∗
      memRegion (b + 581#64) 3 ∗
      ((b + 584#64) ↦₈ v6) ∗
      memRegion (b + 585#64) 3 ∗
      ((b + 588#64) ↦₈ v8) ∗
      memRegion (b + 589#64) 3 ∗
      ((b + 592#64) ↦₈ v10) ∗
      memRegion (b + 593#64) 3 ∗
      ((b + 596#64) ↦₈ v12) ∗
      memRegion (b + 597#64) 3 ∗
      ((b + 600#64) ↦₈ v14) ∗
      memRegion (b + 601#64) 3 ∗
      ((b + 604#64) ↦₈ v16) ∗
      memRegion (b + 605#64) 3 ∗
      ((b + 608#64) ↦₈ v18) ∗
      memRegion (b + 609#64) 3 ∗
      ((b + 612#64) ↦₈ v20) ∗
      memRegion (b + 613#64) 3 ∗
      ((b + 616#64) ↦₈ v22) ∗
      memRegion (b + 617#64) 3 ∗
      ((b + 620#64) ↦₈ v24) ∗
      memRegion (b + 621#64) 3 ∗
      ((b + 624#64) ↦₈ v26) ∗
      memRegion (b + 625#64) 3 ∗
      ((b + 628#64) ↦₈ v28) ∗
      memRegion (b + 629#64) 3 ∗
      ((b + 632#64) ↦₈ v30) ∗
      memRegion (b + 633#64) 3 ∗
      ((b + 636#64) ↦₈ v32) ∗
      memRegion (b + 637#64) 3 ∗
      ((b + 640#64) ↦₈ v34) ∗
      memRegion (b + 641#64) 3 ∗
      ((b + 644#64) ↦₈ v36) ∗
      memRegion (b + 645#64) 3 ∗
      ((b + 648#64) ↦₈ v38) ∗
      memRegion (b + 649#64) 3 ∗
      ((b + 652#64) ↦₈ v40) ∗
      memRegion (b + 653#64) 3 ∗
      ((b + 656#64) ↦₈ v42) ∗
      memRegion (b + 657#64) 3 ∗
      ((b + 660#64) ↦₈ v44) ∗
      memRegion (b + 661#64) 3 ∗
      ((b + 664#64) ↦₈ v46) ∗
      memRegion (b + 665#64) 3 ∗
      ((b + 668#64) ↦₈ v48) ∗
      memRegion (b + 669#64) 3 ∗
      ((b + 672#64) ↦₈ v50) ∗
      memRegion (b + 673#64) 3 ∗
      ((b + 676#64) ↦₈ v52) ∗
      memRegion (b + 677#64) 3 ∗
      ((b + 680#64) ↦₈ v54) ∗
      memRegion (b + 681#64) 3 ∗
      ((b + 684#64) ↦₈ v56) ∗
      memRegion (b + 685#64) 3 ∗
      ((b + 688#64) ↦₈ v58) ∗
      memRegion (b + 689#64) 3 ∗
      ((b + 692#64) ↦₈ v60) ∗
      memRegion (b + 693#64) 3 ∗
      ((b + 696#64) ↦₈ v62) ∗
      memRegion (b + 697#64) 3 ∗
      ((b + 700#64) ↦₈ v64) ∗
      memRegion (b + 701#64) 3 ∗
      ((b + 704#64) ↦₈ v66) ∗
      memRegion (b + 705#64) 3 ∗
      memRegion (b + 708#64) 56 ∗
      memRegion (b + 764#64) 129 ∗
      memRegion (b + 893#64) 3 ∗
      memRegion (b + 896#64) 16 ∗
      ((b + 912#64) ↦₈ v72) ∗
      ((b + 913#64) ↦₈ v73) ∗
      ((b + 914#64) ↦₈ v74) ∗
      ((b + 915#64) ↦₈ v75) ∗
      ((b + 916#64) ↦₈ v76) ∗
      ((b + 917#64) ↦₈ v77) ∗
      ((b + 918#64) ↦₈ v78) ∗
      ((b + 919#64) ↦₈ v79) ∗
      ((b + 920#64) ↦₈ v80) ∗
      ((b + 921#64) ↦₈ v81) ∗
      ((b + 922#64) ↦₈ v82) ∗
      ((b + 923#64) ↦₈ v83) ∗
      ((b + 924#64) ↦₈ v84) ∗
      ((b + 925#64) ↦₈ v85) ∗
      ((b + 926#64) ↦₈ v86) ∗
      ((b + 927#64) ↦₈ v87) ∗
      ((b + 928#64) ↦₈ v88) ∗
      ((b + 929#64) ↦₈ v89) ∗
      ((b + 930#64) ↦₈ v90) ∗
      ((b + 931#64) ↦₈ v91) ∗
      ((b + 932#64) ↦₈ v92) ∗
      ((b + 933#64) ↦₈ v93) ∗
      ((b + 934#64) ↦₈ v94) ∗
      ((b + 935#64) ↦₈ v95) ∗
      ((b + 936#64) ↦₈ v96) ∗
      ((b + 937#64) ↦₈ v97) ∗
      ((b + 938#64) ↦₈ v98) ∗
      ((b + 939#64) ↦₈ v99) ∗
      ((b + 940#64) ↦₈ v100) ∗
      ((b + 941#64) ↦₈ v101) ∗
      ((b + 942#64) ↦₈ v102) ∗
      ((b + 943#64) ↦₈ v103) ∗
      ((b + 944#64) ↦₃₂ v104) ∗
      ((b + 948#64) ↦₆₄ v105) ∗
      ((b + 956#64) ↦₃₂ v106) ∗
      memRegion (b + 960#64) 64 ∗
      ((b + 1024#64) ↦₈ v108) ∗
      memRegion (b + 1025#64) 15 ∗
      memRegion (b + 1040#64) 32 ∗
      memRegion (b + 1072#64) 16 ∗
      ((b + 1088#64) ↦₆₄ v112) ∗
      ((b + 1096#64) ↦₆₄ v113) ∗
      ((b + 1104#64) ↦₆₄ v114) ∗
      ((b + 1112#64) ↦₆₄ v115) ∗
      ((b + 1120#64) ↦₆₄ v116) ∗
      ((b + 1128#64) ↦₆₄ v117) ∗
      ((b + 1136#64) ↦₆₄ v118) ∗
      ((b + 1144#64) ↦₆₄ v119) ∗
      ((b + 1152#64) ↦₆₄ v120) ∗
      ((b + 1160#64) ↦₆₄ v121) ∗
      ((b + 1168#64) ↦₆₄ v122) ∗
      ((b + 1176#64) ↦₆₄ v123)) ∗ F) post oom) :
    SepWP prog t s P post oom := by
  subst hf
  rw [memRegion_partition b 1184 [560, 568, 576, 580, 581, 584, 585, 588, 589, 592, 593, 596, 597, 600, 601, 604, 605, 608, 609, 612, 613, 616, 617, 620, 621, 624, 625, 628, 629, 632, 633, 636, 637, 640, 641, 644, 645, 648, 649, 652, 653, 656, 657, 660, 661, 664, 665, 668, 669, 672, 673, 676, 677, 680, 681, 684, 685, 688, 689, 692, 693, 696, 697, 700, 701, 704, 705, 708, 764, 893, 896, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 948, 956, 960, 1024, 1025, 1040, 1072, 1088, 1096, 1104, 1112, 1120, 1128, 1136, 1144, 1152, 1160, 1168, 1176]]
  simp (maxSteps := 50000000) only [memRegion_one, memRegion_four, memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  exact h ..

theorem encFrame_fold (b : BitVec 64) (v1 : BitVec 64) (v2 : BitVec 64) (v3 : BitVec 32) (v4 : BitVec 8) (v6 : BitVec 8) (v8 : BitVec 8) (v10 : BitVec 8) (v12 : BitVec 8) (v14 : BitVec 8) (v16 : BitVec 8) (v18 : BitVec 8) (v20 : BitVec 8) (v22 : BitVec 8) (v24 : BitVec 8) (v26 : BitVec 8) (v28 : BitVec 8) (v30 : BitVec 8) (v32 : BitVec 8) (v34 : BitVec 8) (v36 : BitVec 8) (v38 : BitVec 8) (v40 : BitVec 8) (v42 : BitVec 8) (v44 : BitVec 8) (v46 : BitVec 8) (v48 : BitVec 8) (v50 : BitVec 8) (v52 : BitVec 8) (v54 : BitVec 8) (v56 : BitVec 8) (v58 : BitVec 8) (v60 : BitVec 8) (v62 : BitVec 8) (v64 : BitVec 8) (v66 : BitVec 8) (v72 : BitVec 8) (v73 : BitVec 8) (v74 : BitVec 8) (v75 : BitVec 8) (v76 : BitVec 8) (v77 : BitVec 8) (v78 : BitVec 8) (v79 : BitVec 8) (v80 : BitVec 8) (v81 : BitVec 8) (v82 : BitVec 8) (v83 : BitVec 8) (v84 : BitVec 8) (v85 : BitVec 8) (v86 : BitVec 8) (v87 : BitVec 8) (v88 : BitVec 8) (v89 : BitVec 8) (v90 : BitVec 8) (v91 : BitVec 8) (v92 : BitVec 8) (v93 : BitVec 8) (v94 : BitVec 8) (v95 : BitVec 8) (v96 : BitVec 8) (v97 : BitVec 8) (v98 : BitVec 8) (v99 : BitVec 8) (v100 : BitVec 8) (v101 : BitVec 8) (v102 : BitVec 8) (v103 : BitVec 8) (v104 : BitVec 32) (v105 : BitVec 64) (v106 : BitVec 32) (v108 : BitVec 8) (v112 : BitVec 64) (v113 : BitVec 64) (v114 : BitVec 64) (v115 : BitVec 64) (v116 : BitVec 64) (v117 : BitVec 64) (v118 : BitVec 64) (v119 : BitVec 64) (v120 : BitVec 64) (v121 : BitVec 64) (v122 : BitVec 64) (v123 : BitVec 64) :
    (memRegion b 560 ∗
      ((b + 560#64) ↦₆₄ v1) ∗
      ((b + 568#64) ↦₆₄ v2) ∗
      ((b + 576#64) ↦₃₂ v3) ∗
      ((b + 580#64) ↦₈ v4) ∗
      memRegion (b + 581#64) 3 ∗
      ((b + 584#64) ↦₈ v6) ∗
      memRegion (b + 585#64) 3 ∗
      ((b + 588#64) ↦₈ v8) ∗
      memRegion (b + 589#64) 3 ∗
      ((b + 592#64) ↦₈ v10) ∗
      memRegion (b + 593#64) 3 ∗
      ((b + 596#64) ↦₈ v12) ∗
      memRegion (b + 597#64) 3 ∗
      ((b + 600#64) ↦₈ v14) ∗
      memRegion (b + 601#64) 3 ∗
      ((b + 604#64) ↦₈ v16) ∗
      memRegion (b + 605#64) 3 ∗
      ((b + 608#64) ↦₈ v18) ∗
      memRegion (b + 609#64) 3 ∗
      ((b + 612#64) ↦₈ v20) ∗
      memRegion (b + 613#64) 3 ∗
      ((b + 616#64) ↦₈ v22) ∗
      memRegion (b + 617#64) 3 ∗
      ((b + 620#64) ↦₈ v24) ∗
      memRegion (b + 621#64) 3 ∗
      ((b + 624#64) ↦₈ v26) ∗
      memRegion (b + 625#64) 3 ∗
      ((b + 628#64) ↦₈ v28) ∗
      memRegion (b + 629#64) 3 ∗
      ((b + 632#64) ↦₈ v30) ∗
      memRegion (b + 633#64) 3 ∗
      ((b + 636#64) ↦₈ v32) ∗
      memRegion (b + 637#64) 3 ∗
      ((b + 640#64) ↦₈ v34) ∗
      memRegion (b + 641#64) 3 ∗
      ((b + 644#64) ↦₈ v36) ∗
      memRegion (b + 645#64) 3 ∗
      ((b + 648#64) ↦₈ v38) ∗
      memRegion (b + 649#64) 3 ∗
      ((b + 652#64) ↦₈ v40) ∗
      memRegion (b + 653#64) 3 ∗
      ((b + 656#64) ↦₈ v42) ∗
      memRegion (b + 657#64) 3 ∗
      ((b + 660#64) ↦₈ v44) ∗
      memRegion (b + 661#64) 3 ∗
      ((b + 664#64) ↦₈ v46) ∗
      memRegion (b + 665#64) 3 ∗
      ((b + 668#64) ↦₈ v48) ∗
      memRegion (b + 669#64) 3 ∗
      ((b + 672#64) ↦₈ v50) ∗
      memRegion (b + 673#64) 3 ∗
      ((b + 676#64) ↦₈ v52) ∗
      memRegion (b + 677#64) 3 ∗
      ((b + 680#64) ↦₈ v54) ∗
      memRegion (b + 681#64) 3 ∗
      ((b + 684#64) ↦₈ v56) ∗
      memRegion (b + 685#64) 3 ∗
      ((b + 688#64) ↦₈ v58) ∗
      memRegion (b + 689#64) 3 ∗
      ((b + 692#64) ↦₈ v60) ∗
      memRegion (b + 693#64) 3 ∗
      ((b + 696#64) ↦₈ v62) ∗
      memRegion (b + 697#64) 3 ∗
      ((b + 700#64) ↦₈ v64) ∗
      memRegion (b + 701#64) 3 ∗
      ((b + 704#64) ↦₈ v66) ∗
      memRegion (b + 705#64) 3 ∗
      memRegion (b + 708#64) 56 ∗
      memRegion (b + 764#64) 129 ∗
      memRegion (b + 893#64) 3 ∗
      memRegion (b + 896#64) 16 ∗
      ((b + 912#64) ↦₈ v72) ∗
      ((b + 913#64) ↦₈ v73) ∗
      ((b + 914#64) ↦₈ v74) ∗
      ((b + 915#64) ↦₈ v75) ∗
      ((b + 916#64) ↦₈ v76) ∗
      ((b + 917#64) ↦₈ v77) ∗
      ((b + 918#64) ↦₈ v78) ∗
      ((b + 919#64) ↦₈ v79) ∗
      ((b + 920#64) ↦₈ v80) ∗
      ((b + 921#64) ↦₈ v81) ∗
      ((b + 922#64) ↦₈ v82) ∗
      ((b + 923#64) ↦₈ v83) ∗
      ((b + 924#64) ↦₈ v84) ∗
      ((b + 925#64) ↦₈ v85) ∗
      ((b + 926#64) ↦₈ v86) ∗
      ((b + 927#64) ↦₈ v87) ∗
      ((b + 928#64) ↦₈ v88) ∗
      ((b + 929#64) ↦₈ v89) ∗
      ((b + 930#64) ↦₈ v90) ∗
      ((b + 931#64) ↦₈ v91) ∗
      ((b + 932#64) ↦₈ v92) ∗
      ((b + 933#64) ↦₈ v93) ∗
      ((b + 934#64) ↦₈ v94) ∗
      ((b + 935#64) ↦₈ v95) ∗
      ((b + 936#64) ↦₈ v96) ∗
      ((b + 937#64) ↦₈ v97) ∗
      ((b + 938#64) ↦₈ v98) ∗
      ((b + 939#64) ↦₈ v99) ∗
      ((b + 940#64) ↦₈ v100) ∗
      ((b + 941#64) ↦₈ v101) ∗
      ((b + 942#64) ↦₈ v102) ∗
      ((b + 943#64) ↦₈ v103) ∗
      ((b + 944#64) ↦₃₂ v104) ∗
      ((b + 948#64) ↦₆₄ v105) ∗
      ((b + 956#64) ↦₃₂ v106) ∗
      memRegion (b + 960#64) 64 ∗
      ((b + 1024#64) ↦₈ v108) ∗
      memRegion (b + 1025#64) 15 ∗
      memRegion (b + 1040#64) 32 ∗
      memRegion (b + 1072#64) 16 ∗
      ((b + 1088#64) ↦₆₄ v112) ∗
      ((b + 1096#64) ↦₆₄ v113) ∗
      ((b + 1104#64) ↦₆₄ v114) ∗
      ((b + 1112#64) ↦₆₄ v115) ∗
      ((b + 1120#64) ↦₆₄ v116) ∗
      ((b + 1128#64) ↦₆₄ v117) ∗
      ((b + 1136#64) ↦₆₄ v118) ∗
      ((b + 1144#64) ↦₆₄ v119) ∗
      ((b + 1152#64) ↦₆₄ v120) ∗
      ((b + 1160#64) ↦₆₄ v121) ∗
      ((b + 1168#64) ↦₆₄ v122) ∗
      ((b + 1176#64) ↦₆₄ v123)) ⊢ memRegion b 1184 := by
  rw [memRegion_partition b 1184 [560, 568, 576, 580, 581, 584, 585, 588, 589, 592, 593, 596, 597, 600, 601, 604, 605, 608, 609, 612, 613, 616, 617, 620, 621, 624, 625, 628, 629, 632, 633, 636, 637, 640, 641, 644, 645, 648, 649, 652, 653, 656, 657, 660, 661, 664, 665, 668, 669, 672, 673, 676, 677, 680, 681, 684, 685, 688, 689, 692, 693, 696, 697, 700, 701, 704, 705, 708, 764, 893, 896, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 948, 956, 960, 1024, 1025, 1040, 1072, 1088, 1096, 1104, 1112, 1120, 1128, 1136, 1144, 1152, 1160, 1168, 1176]]
  repeat' (first
    | exact Entails.refl _
    | exact pointsTo64_entails_memRegion _ _
    | exact pointsTo32_entails_memRegion _ _
    | exact pointsTo8_entails_memRegion _ _
    | refine sepConj_mono ?_ ?_)

/-- Fold the typed cells of a `1184`-byte stack frame back into one region. -/
theorem SepWP.encFrame_close {prog : Program} {t : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} (b : BitVec 64)
    {v1 : BitVec 64} {v2 : BitVec 64} {v3 : BitVec 32} {v4 : BitVec 8} {v6 : BitVec 8} {v8 : BitVec 8} {v10 : BitVec 8} {v12 : BitVec 8} {v14 : BitVec 8} {v16 : BitVec 8} {v18 : BitVec 8} {v20 : BitVec 8} {v22 : BitVec 8} {v24 : BitVec 8} {v26 : BitVec 8} {v28 : BitVec 8} {v30 : BitVec 8} {v32 : BitVec 8} {v34 : BitVec 8} {v36 : BitVec 8} {v38 : BitVec 8} {v40 : BitVec 8} {v42 : BitVec 8} {v44 : BitVec 8} {v46 : BitVec 8} {v48 : BitVec 8} {v50 : BitVec 8} {v52 : BitVec 8} {v54 : BitVec 8} {v56 : BitVec 8} {v58 : BitVec 8} {v60 : BitVec 8} {v62 : BitVec 8} {v64 : BitVec 8} {v66 : BitVec 8} {v72 : BitVec 8} {v73 : BitVec 8} {v74 : BitVec 8} {v75 : BitVec 8} {v76 : BitVec 8} {v77 : BitVec 8} {v78 : BitVec 8} {v79 : BitVec 8} {v80 : BitVec 8} {v81 : BitVec 8} {v82 : BitVec 8} {v83 : BitVec 8} {v84 : BitVec 8} {v85 : BitVec 8} {v86 : BitVec 8} {v87 : BitVec 8} {v88 : BitVec 8} {v89 : BitVec 8} {v90 : BitVec 8} {v91 : BitVec 8} {v92 : BitVec 8} {v93 : BitVec 8} {v94 : BitVec 8} {v95 : BitVec 8} {v96 : BitVec 8} {v97 : BitVec 8} {v98 : BitVec 8} {v99 : BitVec 8} {v100 : BitVec 8} {v101 : BitVec 8} {v102 : BitVec 8} {v103 : BitVec 8} {v104 : BitVec 32} {v105 : BitVec 64} {v106 : BitVec 32} {v108 : BitVec 8} {v112 : BitVec 64} {v113 : BitVec 64} {v114 : BitVec 64} {v115 : BitVec 64} {v116 : BitVec 64} {v117 : BitVec 64} {v118 : BitVec 64} {v119 : BitVec 64} {v120 : BitVec 64} {v121 : BitVec 64} {v122 : BitVec 64} {v123 : BitVec 64}
    (hf : P ⊢ (memRegion b 560 ∗
      ((b + 560#64) ↦₆₄ v1) ∗
      ((b + 568#64) ↦₆₄ v2) ∗
      ((b + 576#64) ↦₃₂ v3) ∗
      ((b + 580#64) ↦₈ v4) ∗
      memRegion (b + 581#64) 3 ∗
      ((b + 584#64) ↦₈ v6) ∗
      memRegion (b + 585#64) 3 ∗
      ((b + 588#64) ↦₈ v8) ∗
      memRegion (b + 589#64) 3 ∗
      ((b + 592#64) ↦₈ v10) ∗
      memRegion (b + 593#64) 3 ∗
      ((b + 596#64) ↦₈ v12) ∗
      memRegion (b + 597#64) 3 ∗
      ((b + 600#64) ↦₈ v14) ∗
      memRegion (b + 601#64) 3 ∗
      ((b + 604#64) ↦₈ v16) ∗
      memRegion (b + 605#64) 3 ∗
      ((b + 608#64) ↦₈ v18) ∗
      memRegion (b + 609#64) 3 ∗
      ((b + 612#64) ↦₈ v20) ∗
      memRegion (b + 613#64) 3 ∗
      ((b + 616#64) ↦₈ v22) ∗
      memRegion (b + 617#64) 3 ∗
      ((b + 620#64) ↦₈ v24) ∗
      memRegion (b + 621#64) 3 ∗
      ((b + 624#64) ↦₈ v26) ∗
      memRegion (b + 625#64) 3 ∗
      ((b + 628#64) ↦₈ v28) ∗
      memRegion (b + 629#64) 3 ∗
      ((b + 632#64) ↦₈ v30) ∗
      memRegion (b + 633#64) 3 ∗
      ((b + 636#64) ↦₈ v32) ∗
      memRegion (b + 637#64) 3 ∗
      ((b + 640#64) ↦₈ v34) ∗
      memRegion (b + 641#64) 3 ∗
      ((b + 644#64) ↦₈ v36) ∗
      memRegion (b + 645#64) 3 ∗
      ((b + 648#64) ↦₈ v38) ∗
      memRegion (b + 649#64) 3 ∗
      ((b + 652#64) ↦₈ v40) ∗
      memRegion (b + 653#64) 3 ∗
      ((b + 656#64) ↦₈ v42) ∗
      memRegion (b + 657#64) 3 ∗
      ((b + 660#64) ↦₈ v44) ∗
      memRegion (b + 661#64) 3 ∗
      ((b + 664#64) ↦₈ v46) ∗
      memRegion (b + 665#64) 3 ∗
      ((b + 668#64) ↦₈ v48) ∗
      memRegion (b + 669#64) 3 ∗
      ((b + 672#64) ↦₈ v50) ∗
      memRegion (b + 673#64) 3 ∗
      ((b + 676#64) ↦₈ v52) ∗
      memRegion (b + 677#64) 3 ∗
      ((b + 680#64) ↦₈ v54) ∗
      memRegion (b + 681#64) 3 ∗
      ((b + 684#64) ↦₈ v56) ∗
      memRegion (b + 685#64) 3 ∗
      ((b + 688#64) ↦₈ v58) ∗
      memRegion (b + 689#64) 3 ∗
      ((b + 692#64) ↦₈ v60) ∗
      memRegion (b + 693#64) 3 ∗
      ((b + 696#64) ↦₈ v62) ∗
      memRegion (b + 697#64) 3 ∗
      ((b + 700#64) ↦₈ v64) ∗
      memRegion (b + 701#64) 3 ∗
      ((b + 704#64) ↦₈ v66) ∗
      memRegion (b + 705#64) 3 ∗
      memRegion (b + 708#64) 56 ∗
      memRegion (b + 764#64) 129 ∗
      memRegion (b + 893#64) 3 ∗
      memRegion (b + 896#64) 16 ∗
      ((b + 912#64) ↦₈ v72) ∗
      ((b + 913#64) ↦₈ v73) ∗
      ((b + 914#64) ↦₈ v74) ∗
      ((b + 915#64) ↦₈ v75) ∗
      ((b + 916#64) ↦₈ v76) ∗
      ((b + 917#64) ↦₈ v77) ∗
      ((b + 918#64) ↦₈ v78) ∗
      ((b + 919#64) ↦₈ v79) ∗
      ((b + 920#64) ↦₈ v80) ∗
      ((b + 921#64) ↦₈ v81) ∗
      ((b + 922#64) ↦₈ v82) ∗
      ((b + 923#64) ↦₈ v83) ∗
      ((b + 924#64) ↦₈ v84) ∗
      ((b + 925#64) ↦₈ v85) ∗
      ((b + 926#64) ↦₈ v86) ∗
      ((b + 927#64) ↦₈ v87) ∗
      ((b + 928#64) ↦₈ v88) ∗
      ((b + 929#64) ↦₈ v89) ∗
      ((b + 930#64) ↦₈ v90) ∗
      ((b + 931#64) ↦₈ v91) ∗
      ((b + 932#64) ↦₈ v92) ∗
      ((b + 933#64) ↦₈ v93) ∗
      ((b + 934#64) ↦₈ v94) ∗
      ((b + 935#64) ↦₈ v95) ∗
      ((b + 936#64) ↦₈ v96) ∗
      ((b + 937#64) ↦₈ v97) ∗
      ((b + 938#64) ↦₈ v98) ∗
      ((b + 939#64) ↦₈ v99) ∗
      ((b + 940#64) ↦₈ v100) ∗
      ((b + 941#64) ↦₈ v101) ∗
      ((b + 942#64) ↦₈ v102) ∗
      ((b + 943#64) ↦₈ v103) ∗
      ((b + 944#64) ↦₃₂ v104) ∗
      ((b + 948#64) ↦₆₄ v105) ∗
      ((b + 956#64) ↦₃₂ v106) ∗
      memRegion (b + 960#64) 64 ∗
      ((b + 1024#64) ↦₈ v108) ∗
      memRegion (b + 1025#64) 15 ∗
      memRegion (b + 1040#64) 32 ∗
      memRegion (b + 1072#64) 16 ∗
      ((b + 1088#64) ↦₆₄ v112) ∗
      ((b + 1096#64) ↦₆₄ v113) ∗
      ((b + 1104#64) ↦₆₄ v114) ∗
      ((b + 1112#64) ↦₆₄ v115) ∗
      ((b + 1120#64) ↦₆₄ v116) ∗
      ((b + 1128#64) ↦₆₄ v117) ∗
      ((b + 1136#64) ↦₆₄ v118) ∗
      ((b + 1144#64) ↦₆₄ v119) ∗
      ((b + 1152#64) ↦₆₄ v120) ∗
      ((b + 1160#64) ↦₆₄ v121) ∗
      ((b + 1168#64) ↦₆₄ v122) ∗
      ((b + 1176#64) ↦₆₄ v123)) ∗ F)
    (h : SepWP prog t s (memRegion b 1184 ∗ F) post oom) :
    SepWP prog t s P post oom :=
  SepWP.weaken_pre (Entails.trans hf (sepConj_mono_left (encFrame_fold b ..))) h

theorem SepWP.foldPart {prog : Program} {t : BitVec 64} {s : Arm64.State} {P T T' F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hent : T ⊢ T') (hf : P = T ∗ F) (h : SepWP prog t s (T' ∗ F) post oom) :
    SepWP prog t s P post oom :=
  SepWP.weaken_pre (hf ▸ sepConj_mono_left hent) h

theorem aligned_sub {x : BitVec 64} (h : (x &&& 15#64 == 0#64) = true) (k : Nat)
    (hk : k % 16 = 0) (hk2 : k < 2 ^ 64) : ((x - BitVec.ofNat 64 k) &&& 15#64 == 0#64) = true := by
  simp only [beq_iff_eq] at h ⊢
  have h16 := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod] at h16 ⊢
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat] at h16 ⊢
  omega

theorem ak_blk_ok [CpPlacement] :
    subroutine_ok (chachapolyLib.blockProgram cpMpl 4) cpPl4.base
      (chachapolyLib.withCodeLoaded cpMpl applyKeystreamContract) := applyKeystream_ok

theorem pn_blk_ok [CpPlacement] :
    subroutine_ok (chachapolyLib.blockProgram cpMpl 10) cpPl10.base
      (chachapolyLib.withCodeLoaded cpMpl polyNewContract) := polyNewContract_ok

def sigmaSym : String := "chachapoly_verified:.rodata.cst16+0x0"

set_option maxRecDepth 400000 in
theorem encrypt_draft [CpPlacement] :
    subroutine_ok cpProg6r cpPl6.base
      (chachapolyLib.withCodeLoaded cpMpl (aeadEncryptContract (cpMpl.ρ sigmaSym))) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, aeadEncryptContract, aeadPre]
  wp_entry "chachapoly_encrypt" g s0
  obtain ⟨key, nonce, aad, buf, tag, k, n, a, msg, t⟩ := g
  simp only at *
  refine SepWP.encFrame (s0.sp - 0x4a0#64) (by sep_focus) ?_
  intros
  have hρ : cpPl6.ρ "chachapoly_verified:.rodata.cst16+0x0" = cpMpl.ρ sigmaSym := by
    have h : Obj.lookupBlockSym "chachapoly_verified:.rodata.cst16+0x0" chachapolyLib.blocks = none := by
      decide +kernel
    simp [cpPl6, sigmaSym, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl6.base + 0x204#64) h ?_
  refine Proofs.SepWP.memRegion_bytes (s0.sp - 1184#64 + 896#64) 16 (by decide) (by sep_focus) fun cs0 hcs0 => ?_
  refine Proofs.SepWP.memRegion_bytes (s0.sp - 1184#64 + 960#64) 64 (by decide) (by sep_focus) fun cb0 hcb0 => ?_
  refine Proofs.SepWP.memRegion_bytes (s0.sp - 1184#64 + 1040#64) 32 (by decide) (by sep_focus) fun mk0 hmk0 => ?_
  wp_steps 129
  refine SepWP.foldPart (encState_fold (s0.sp - 288#64) k n cs0 cb0 (by assumption) (by assumption)
    hcs0 hcb0) (by sep_focus) ?_
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  intro hcl
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl6.base + 0x210#64) hcl ?_
  rw [zero_chain32 mk0 hmk0]
  have hal := aligned_sub hsp_align 624 (by decide) (by decide)
  wp_step
  have hr : cpPl6.ρ "<cipher::stream_wrapper::StreamCipherCoreWrapper<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>>> as cipher::stream::StreamCipher>::apply_keystream" = cpPl4.base := by
    have h : Obj.lookupBlockSym "<cipher::stream_wrapper::StreamCipherCoreWrapper<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>>> as cipher::stream::StreamCipher>::apply_keystream" chachapolyLib.blocks = some (4, 0) := by decide +kernel
    simp [cpPl6, cpPl4, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]
  rw [hr, show cpPl6.base + 516#64 + (cpPl4.base - cpPl6.base - 516#64) = cpPl4.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 6) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 4) (by decide) ak_blk_ok
    (x := ⟨s0.sp - 288#64, s0.sp - 144#64, List.replicate 32 0#8, initState k 0 n, zeroState⟩)
    (ret_pc := cpPl6.base + 520#64) (F := ?F)
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
    show SepWP cpProg6r _ _ _ _ _
    simp only [MultiPlacedLib.withCodeLoaded, applyKeystreamContract, stackFrame, wp_norm,
      arm64_norm] at hspf hcsf ⊢
    obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcsf
    simp only [wp_norm, arm64_norm] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 cv hspf
    wp_steps 2
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf]) ?_
    intro hcl2
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl6.base + 0x2e0#64) hcl2 ?_
    refine SepWP.exists_elim fun kb => ?_
    wp_step
    have hr2 : cpPl6.ρ "<poly1305::Poly1305 as crypto_common::KeyInit>::new" = cpPl10.base := by
      have h : Obj.lookupBlockSym "<poly1305::Poly1305 as crypto_common::KeyInit>::new" chachapolyLib.blocks = some (10, 0) := by decide +kernel
      simp [cpPl6, cpPl10, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]
    rw [hr2, show cpPl6.base + 528#64 + (cpPl10.base - cpPl6.base - 528#64) = cpPl10.base by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 6) _ _ _ _ _
    refine MultiPlacedLib.sepWP_call_block (j := 10) (by decide) pn_blk_ok
      (x := (s0.sp - 144#64, s0.sp - 476#64, streamXor (initState k 0 n) (List.replicate 32 0#8)))
      (ret_pc := cpPl6.base + 532#64) (F := ?F2)
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
      show SepWP cpProg6r _ _ _ _ _
      simp only [MultiPlacedLib.withCodeLoaded, polyNewContract, wp_norm, arm64_norm] at hspf2 hcsf2 ⊢
      obtain ⟨d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, dv⟩ := hcsf2
      simp only [wp_norm, arm64_norm, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv, hspf] at d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 dv hspf2
      refine SepWP.exists_elim fun pw => SepWP.exists_elim fun pl => ?_
      refine SepWP.pure_elim fun ⟨hpw, hpl⟩ => ?_
      rw [stateAt_eq_bytes (s0.sp - 288#64), stateAt_eq_bytes (s0.sp - 224#64)]
      refine SepWP.foldPart (Entails.of_eq_explicit (SepFrameInfer.memRegion_merge (s0.sp - 420#64)
        (s0.sp - 291#64) 129 3 132 (by bv_omega) rfl (by decide))) (by sep_focus) ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 420#64) 132 (by decide) (by sep_focus) fun cc0 hcc0 => ?_
      refine Proofs.SepWP.memRegion_bytes (s0.sp - 159#64) 15 (by decide) (by sep_focus) fun pr hpr => ?_
      refine SepWP.foldPart (Entails.of_eq_explicit (pointsToBytes_cons (s0.sp - 160#64) 32#8 pr).symm)
        (by sep_focus) ?_
      have hmkl : (streamXor (initState k 0 n) (List.replicate 32 0#8)).length = 32 := by
        rw [streamXor_length _ _ _ rfl]; simp
      have hkbl : kb.bytes.length = 64 := by simp [Spec.State.bytes, word32Bytes]
      have hsl : ((initState k 0 n).advance (((List.replicate 32 0#8).length + 63) / 64)).bytes.length = 64 := by
        simp [Spec.State.bytes, word32Bytes]
      generalize streamXor (initState k 0 n) (List.replicate 32 0#8) = mk at *
      generalize kb.bytes = kbb at *
      generalize ((initState k 0 n).advance (((List.replicate 32 0#8).length + 63) / 64)).bytes = sb at *
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf2]) ?_
      intro hcl3
      have hml : msg.length ≤ maxMsgLen := by assumption
      have hlo : (BitVec.ofNat 64 msg.length).ult 274877906880#64 = true := by
        simp only [maxMsgLen] at hml; simp [BitVec.ult]; omega
      wp_steps 3
      trace_state
      sorry
