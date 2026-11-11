module

public import ChaChaPoly.Proofs.DecryptCmp
public import ChaChaPoly.Proofs.Encrypt

/-!
# `chachapoly_decrypt` (block 5)
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

/-- The tag decrypt computes is the RFC 8439 tag of `(aad, ciphertext)`. -/
theorem dec_tag (k n a msg mk : Bytes) (w0 w1 w2 w3 t0 t1 t2 t3 : BitVec 32) (l3 : PolyLimbs)
    (hmk : mk = streamXor (initState k 0 n) (List.replicate 32 0#8))
    (hpw : words4Val w0 w1 w2 w3 = leNat (mk.drop 16))
    (hl3 : l3.Rep (clamp (leNat (mk.take 16)))
      ((polyBlocks (clamp (leNat (mk.take 16))) (polyBlocks (clamp (leNat (mk.take 16))) 0 (a ++ pad16 a))
          (msg ++ pad16 msg) +
        leNat (natLe 8 a.length ++ natLe 8 msg.length ++ [1])) * clamp (leNat (mk.take 16)) % p1305))
    (htg : words4Val t0 t1 t2 t3 =
      (limbVal l3.h0.toNat l3.h1.toNat l3.h2.toNat l3.h3.toNat l3.h4.toNat % p1305 +
        words4Val w0 w1 w2 w3) % 2 ^ 128) :
    natLe 16 (words4Val t0 t1 t2 t3) = poly1305Mac (poly1305KeyGen k n) (macData a msg) := by
  have hmkl : mk.length = 32 := by rw [hmk, streamXor_length _ _ _ rfl]; simp
  simp only [poly1305Mac, macData]
  rw [keyGen_eq, ← hmk]
  rw [show (mk.drop 16).take 16 = mk.drop 16 by rw [List.take_of_length_le]; simp [hmkl]]
  generalize hr : clamp (leNat (mk.take 16)) = r at *
  have hlens : (natLe 8 a.length ++ natLe 8 msg.length).length = 16 := by simp [natLe]
  rw [show a ++ pad16 a ++ msg ++ pad16 msg ++ natLe 8 a.length ++ natLe 8 msg.length =
      (a ++ pad16 a) ++ ((msg ++ pad16 msg) ++ (natLe 8 a.length ++ natLe 8 msg.length ++ [])) by simp,
    polyBlocks_append r ((a ++ pad16 a).length / 16) _ _ _ (by have := pad16_aligned a; omega),
    polyBlocks_append r ((msg ++ pad16 msg).length / 16) _ _ _ (by have := pad16_aligned msg; omega),
    polyBlocks_block _ _ _ _ hlens, polyBlocks_nil]
  rw [htg, hl3.2.2.2, Nat.mod_mod, hpw, show (2 : Nat) ^ 128 = 256 ^ 16 by decide, natLe_mod]

/-- `aeadDecrypt` in terms of the computed tag and the key stream. -/
theorem aeadDecrypt_eq (k n a msg t T : Bytes) (hT : T = poly1305Mac (poly1305KeyGen k n) (macData a msg)) :
    aeadDecrypt k n a msg t = if T = t then some (streamXor (initState k 1 n) msg) else none := by
  simp [aeadDecrypt, hT, chacha20Encrypt_eq]

theorem rho5_ak [CpPlacement] : cpPl5.ρ applyKeystreamSym = cpPl4.base := by
  have h : Obj.lookupBlockSym applyKeystreamSym chachapolyLib.blocks = some (4, 0) := by decide +kernel
  simp [cpPl5, cpPl4, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]

theorem region_join (p : BitVec 64) (m n : Nat) (h : m ≤ n) (hn : n ≤ 2 ^ 64) :
    (memRegion p m ∗ memRegion (p + BitVec.ofNat 64 m) (n - m)) ⊢ memRegion p n := by
  rw [memRegion_split_le p m n h hn]; exact Entails.refl _

theorem decClose_fold (b : BitVec 64) (v1 : BitVec 32) (v11 : BitVec 64) (v12 : BitVec 64) (v13 : BitVec 64) (v14 : BitVec 64) (v15 : BitVec 64) (v16 : BitVec 64) (v17 : BitVec 64) (v18 : BitVec 64) (v19 : BitVec 64) (v20 : BitVec 64) (v21 : BitVec 64) (v22 : BitVec 64) :
    (memRegion b 560 ∗
      ((b + 560#64) ↦₃₂ v1) ∗
      memRegion (b + 564#64) 128 ∗
      memRegion (b + 692#64) 56 ∗
      memRegion (b + 748#64) 129 ∗
      memRegion (b + 877#64) 3 ∗
      memRegion (b + 880#64) 64 ∗
      memRegion (b + 944#64) 64 ∗
      memRegion (b + 1008#64) 16 ∗
      memRegion (b + 1024#64) 32 ∗
      memRegion (b + 1056#64) 16 ∗
      ((b + 1072#64) ↦₆₄ v11) ∗
      ((b + 1080#64) ↦₆₄ v12) ∗
      ((b + 1088#64) ↦₆₄ v13) ∗
      ((b + 1096#64) ↦₆₄ v14) ∗
      ((b + 1104#64) ↦₆₄ v15) ∗
      ((b + 1112#64) ↦₆₄ v16) ∗
      ((b + 1120#64) ↦₆₄ v17) ∗
      ((b + 1128#64) ↦₆₄ v18) ∗
      ((b + 1136#64) ↦₆₄ v19) ∗
      ((b + 1144#64) ↦₆₄ v20) ∗
      ((b + 1152#64) ↦₆₄ v21) ∗
      ((b + 1160#64) ↦₆₄ v22)) ⊢ memRegion b 1168 := by
  rw [memRegion_partition b 1168 [560, 564, 692, 748, 877, 880, 944, 1008, 1024, 1056, 1072, 1080, 1088, 1096, 1104, 1112, 1120, 1128, 1136, 1144, 1152, 1160]]
  repeat' (first
    | exact Entails.refl _
    | exact pointsTo64_entails_memRegion _ _
    | exact pointsTo32_entails_memRegion _ _
    | exact pointsTo8_entails_memRegion _ _
    | refine sepConj_mono ?_ ?_)


theorem rho5_drop [CpPlacement] : cpPl5.ρ cipherDropSym = cpPl1.base := by
  have h : Obj.lookupBlockSym cipherDropSym chachapolyLib.blocks = some (1, 0) := by decide +kernel
  simp [cpPl5, cpPl1, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]

/-- `0x5bc` to the return: the cipher's drop glue, the zeroisation of the key copy, the epilogue. -/
theorem decEnd_ok [CpPlacement] (s0 sm : Arm64.State) (R : SepProp)
    (k n a t B : Bytes) (key nonce aad buf tag : BitVec 64) (v1 w : BitVec 32)
    (hpc : sm.pc = cpPl5.base + 0x5bc#64) (hrun : sm.status = .Running)
    (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (hsp : sm.sp = s0.sp - 608#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (h19 : (sm.readReg64 .x19).truncate 32 = w)
    (hv : calleeSavedVRegs sm = calleeSavedVRegs s0) :
    SepWP cpProg5r (s0.readReg64 (Reg.gpr 30#5)) sm
      (memRegion (s0.sp - 1168#64) 560 ∗
        (buf ↦ₛ B) ∗
        (aad ↦ₛ a) ∗
        memRegion (s0.sp - 476#64) 56 ∗
        memRegion (s0.sp - 420#64) 129 ∗
        memRegion (s0.sp - 291#64) 3 ∗
        memRegion (s0.sp - 288#64) 64 ∗
        memRegion (s0.sp - 224#64) 64 ∗
        memRegion (s0.sp - 160#64) 16 ∗
        memRegion (s0.sp - 144#64) 32 ∗
        (s0.sp - 608#64) ↦₃₂ v1 ∗
        (s0.sp - 604#64) ↦₈ List.getD k 31 0#8 ∗
        memRegion (s0.sp - 603#64) 3 ∗
        (s0.sp - 600#64) ↦₈ List.getD k 30 0#8 ∗
        memRegion (s0.sp - 599#64) 3 ∗
        (s0.sp - 596#64) ↦₈ List.getD k 29 0#8 ∗
        memRegion (s0.sp - 595#64) 3 ∗
        (s0.sp - 592#64) ↦₈ List.getD k 28 0#8 ∗
        memRegion (s0.sp - 591#64) 3 ∗
        (s0.sp - 588#64) ↦₈ List.getD k 27 0#8 ∗
        memRegion (s0.sp - 587#64) 3 ∗
        (s0.sp - 584#64) ↦₈ List.getD k 26 0#8 ∗
        memRegion (s0.sp - 583#64) 3 ∗
        (s0.sp - 580#64) ↦₈ List.getD k 25 0#8 ∗
        memRegion (s0.sp - 579#64) 3 ∗
        (s0.sp - 576#64) ↦₈ List.getD k 24 0#8 ∗
        memRegion (s0.sp - 575#64) 3 ∗
        (s0.sp - 572#64) ↦₈ List.getD k 23 0#8 ∗
        memRegion (s0.sp - 571#64) 3 ∗
        (s0.sp - 568#64) ↦₈ List.getD k 22 0#8 ∗
        memRegion (s0.sp - 567#64) 3 ∗
        (s0.sp - 564#64) ↦₈ List.getD k 21 0#8 ∗
        memRegion (s0.sp - 563#64) 3 ∗
        (s0.sp - 560#64) ↦₈ List.getD k 20 0#8 ∗
        memRegion (s0.sp - 559#64) 3 ∗
        (s0.sp - 556#64) ↦₈ List.getD k 19 0#8 ∗
        memRegion (s0.sp - 555#64) 3 ∗
        (s0.sp - 552#64) ↦₈ List.getD k 18 0#8 ∗
        memRegion (s0.sp - 551#64) 3 ∗
        (s0.sp - 548#64) ↦₈ List.getD k 17 0#8 ∗
        memRegion (s0.sp - 547#64) 3 ∗
        (s0.sp - 544#64) ↦₈ List.getD k 16 0#8 ∗
        memRegion (s0.sp - 543#64) 3 ∗
        (s0.sp - 540#64) ↦₈ List.getD k 15 0#8 ∗
        memRegion (s0.sp - 539#64) 3 ∗
        (s0.sp - 536#64) ↦₈ List.getD k 14 0#8 ∗
        memRegion (s0.sp - 535#64) 3 ∗
        (s0.sp - 532#64) ↦₈ List.getD k 13 0#8 ∗
        memRegion (s0.sp - 531#64) 3 ∗
        (s0.sp - 528#64) ↦₈ List.getD k 12 0#8 ∗
        memRegion (s0.sp - 527#64) 3 ∗
        (s0.sp - 524#64) ↦₈ List.getD k 11 0#8 ∗
        memRegion (s0.sp - 523#64) 3 ∗
        (s0.sp - 520#64) ↦₈ List.getD k 10 0#8 ∗
        memRegion (s0.sp - 519#64) 3 ∗
        (s0.sp - 516#64) ↦₈ List.getD k 9 0#8 ∗
        memRegion (s0.sp - 515#64) 3 ∗
        (s0.sp - 512#64) ↦₈ List.getD k 8 0#8 ∗
        memRegion (s0.sp - 511#64) 3 ∗
        (s0.sp - 508#64) ↦₈ List.getD k 7 0#8 ∗
        memRegion (s0.sp - 507#64) 3 ∗
        (s0.sp - 504#64) ↦₈ List.getD k 6 0#8 ∗
        memRegion (s0.sp - 503#64) 3 ∗
        (s0.sp - 500#64) ↦₈ List.getD k 5 0#8 ∗
        memRegion (s0.sp - 499#64) 3 ∗
        (s0.sp - 496#64) ↦₈ List.getD k 4 0#8 ∗
        memRegion (s0.sp - 495#64) 3 ∗
        (s0.sp - 492#64) ↦₈ List.getD k 3 0#8 ∗
        memRegion (s0.sp - 491#64) 3 ∗
        (s0.sp - 488#64) ↦₈ List.getD k 2 0#8 ∗
        memRegion (s0.sp - 487#64) 3 ∗
        (s0.sp - 484#64) ↦₈ List.getD k 1 0#8 ∗
        memRegion (s0.sp - 483#64) 3 ∗
        (s0.sp - 480#64) ↦₈ List.getD k 0 0#8 ∗
        memRegion (s0.sp - 479#64) 3 ∗
        memRegion (s0.sp - 112#64) 16 ∗
        (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
        (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
        key ↦ₛ k ∗
        nonce ↦ₛ n ∗
        tag ↦ₛ t ∗
        cpMpl.ρ sigmaSym ↦ᵣ sigmaBytes)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜BitVec.truncate 32 (sf.readReg64 (Reg.gpr 0#5)) = w⌝ ∗ buf ↦ₛ B) ∗ key ↦ₛ k ∗ nonce ↦ₛ n ∗ aad ↦ₛ a ∗ tag ↦ₛ t ∗ cpMpl.ρ sigmaSym ↦ᵣ sigmaBytes ∗ memRegion (s0.sp - 1168#64) 1168 ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hρd := rho5_drop
  simp only [cipherDropSym] at hρd
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x5c4#64) hcl ?_
  wp_steps 2
  rw [show cpPl5.base + 1472#64 + (cpPl1.base - cpPl5.base - 1472#64) = cpPl1.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  refine MultiPlacedLib.sepWP_call_block (j := 1) (by decide) cd_blk_ok
    (x := s0.sp - 476#64) (ret_pc := cpPl5.base + 1476#64) (F := ?F6)
    (by simpa [wp_norm, arm64_norm] using hcl) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, State.spAligned, hsp]; simpa using hsp_align)
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, cipherDropContract]
    simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, hsp] at hm hcl ⊢
    refine ⟨hcl, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  · intro sf8 hpcf8 hrunf8 hspf8 hcsf8
    obtain ⟨o19, o20, o21, o22, o23, o24, o25, o26, o27, o28, o29, ov⟩ := hcsf8
    simp only [wp_norm, arm64_norm] at o19 o20 o21 o22 o23 o24 o25 o26 o27 o28 o29 ov hspf8
    simp only [MultiPlacedLib.withCodeLoaded, cipherDropContract]
    refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf8]) hrunf8 ?_
    intro hcl11
    show SepWP cpProg5r _ _ _ _ _
    wp_steps
    refine Proofs.SepWP.foldPart (spill128_fold (s0.sp - 604#64) 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8) (by sep_focus) ?_
    refine Proofs.SepWP.foldPart (decClose_fold (s0.sp - 1168#64) _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    wp_done

theorem decTail_ok [CpPlacement] (s0 sm : Arm64.State) (R : SepProp)
    (k n a msg t mk pr blk2 : Bytes) (key nonce aad buf tag : BitVec 64)
    (pw : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) (kb : Spec.State) (l2 : PolyLimbs) (v1 : BitVec 32)
    (hpc : sm.pc = cpPl5.base + 0x3c4#64) (hrun : sm.status = .Running)
    (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (hsp : sm.sp = s0.sp - 608#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (h19 : sm.readReg64 .x19 = BitVec.ofNat 64 msg.length) (h21 : sm.readReg64 .x21 = tag)
    (h23 : sm.readReg64 .x23 = buf) (h24 : sm.readReg64 .x24 = BitVec.ofNat 64 a.length)
    (h25 : sm.readReg64 .x25 = s0.sp - 288#64) (h29 : sm.readReg64 .x29 = s0.sp - 96#64)
    (hv : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hkl : k.length = 32) (hnl : n.length = 12) (htl : t.length = 16) (hal : a.length < 2 ^ 63)
    (hml : msg.length ≤ maxMsgLen) (hmkl : mk.length = 32) (hpr : pr.length = 15) (hblk2 : blk2.length = 16)
    (hmk : streamXor (initState k 0 n) (List.replicate 32 0#8) = mk)
    (hpw : words4Val pw.1 pw.2.1 pw.2.2.1 pw.2.2.2 = leNat (mk.drop 16))
    (hl2 : l2.Rep (clamp (leNat (mk.take 16))) (polyBlocks (clamp (leNat (mk.take 16))) (polyBlocks (clamp (leNat (mk.take 16))) 0 (a ++ pad16 a)) (msg ++ pad16 msg))) :
    SepWP cpProg5r (s0.readReg64 (Reg.gpr 30#5)) sm
      ((stateAt (s0.sp - 356#64) kb ∗ stateAt (s0.sp - 420#64) (initState k 1 n) ∗ buf ↦ₛ msg ∗ (s0.sp - 288#64) ↦ₛ blk2 ∗ polyLimbsAt (s0.sp - 476#64) l2 ∗ aad ↦ₛ a ∗ ((s0.sp - 160#64) ↦₈ 0#8 ∗ (s0.sp - 160#64 + 1#64) ↦ₛ pr) ∗ (s0.sp - 292#64) ↦ₛ [0#8, List.getD pr 0 0#8, List.getD pr 1 0#8, List.getD pr 2 0#8] ∗ (s0.sp - 144#64) ↦ₛ ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 mk 0 0#8) 1 0#8) 2 0#8) 3 0#8) 4 0#8) 5 0#8) 6 0#8) 7 0#8) 8 0#8) 9 0#8) 10 0#8) 11 0#8) 12 0#8) 13 0#8) 14 0#8) 15 0#8) 16 0#8) 17 0#8) 18 0#8) 19 0#8) 20 0#8) 21 0#8) 22 0#8) 23 0#8) 24 0#8) 25 0#8) 26 0#8) 27 0#8) 28 0#8) 29 0#8) 30 0#8) 31 0#8 ∗ words4At (s0.sp - 476#64) pw.fst pw.snd.fst pw.snd.snd.fst pw.snd.snd.snd ∗ (s0.sp - 272#64) ↦ₛ List.drop 16 (initState k 1 n).bytes ∗ (s0.sp - 224#64) ↦ₛ kb.bytes ∗ memRegion (s0.sp - 1168#64) 560 ∗ (s0.sp - 608#64) ↦₃₂ v1 ∗ (s0.sp - 604#64) ↦₈ List.getD k 31 0#8 ∗ memRegion (s0.sp - 603#64) 3 ∗ (s0.sp - 600#64) ↦₈ List.getD k 30 0#8 ∗ memRegion (s0.sp - 599#64) 3 ∗ (s0.sp - 596#64) ↦₈ List.getD k 29 0#8 ∗ memRegion (s0.sp - 595#64) 3 ∗ (s0.sp - 592#64) ↦₈ List.getD k 28 0#8 ∗ memRegion (s0.sp - 591#64) 3 ∗ (s0.sp - 588#64) ↦₈ List.getD k 27 0#8 ∗ memRegion (s0.sp - 587#64) 3 ∗ (s0.sp - 584#64) ↦₈ List.getD k 26 0#8 ∗ memRegion (s0.sp - 583#64) 3 ∗ (s0.sp - 580#64) ↦₈ List.getD k 25 0#8 ∗ memRegion (s0.sp - 579#64) 3 ∗ (s0.sp - 576#64) ↦₈ List.getD k 24 0#8 ∗ memRegion (s0.sp - 575#64) 3 ∗ (s0.sp - 572#64) ↦₈ List.getD k 23 0#8 ∗ memRegion (s0.sp - 571#64) 3 ∗ (s0.sp - 568#64) ↦₈ List.getD k 22 0#8 ∗ memRegion (s0.sp - 567#64) 3 ∗ (s0.sp - 564#64) ↦₈ List.getD k 21 0#8 ∗ memRegion (s0.sp - 563#64) 3 ∗ (s0.sp - 560#64) ↦₈ List.getD k 20 0#8 ∗ memRegion (s0.sp - 559#64) 3 ∗ (s0.sp - 556#64) ↦₈ List.getD k 19 0#8 ∗ memRegion (s0.sp - 555#64) 3 ∗ (s0.sp - 552#64) ↦₈ List.getD k 18 0#8 ∗ memRegion (s0.sp - 551#64) 3 ∗ (s0.sp - 548#64) ↦₈ List.getD k 17 0#8 ∗ memRegion (s0.sp - 547#64) 3 ∗ (s0.sp - 544#64) ↦₈ List.getD k 16 0#8 ∗ memRegion (s0.sp - 543#64) 3 ∗ (s0.sp - 540#64) ↦₈ List.getD k 15 0#8 ∗ memRegion (s0.sp - 539#64) 3 ∗ (s0.sp - 536#64) ↦₈ List.getD k 14 0#8 ∗ memRegion (s0.sp - 535#64) 3 ∗ (s0.sp - 532#64) ↦₈ List.getD k 13 0#8 ∗ memRegion (s0.sp - 531#64) 3 ∗ (s0.sp - 528#64) ↦₈ List.getD k 12 0#8 ∗ memRegion (s0.sp - 527#64) 3 ∗ (s0.sp - 524#64) ↦₈ List.getD k 11 0#8 ∗ memRegion (s0.sp - 523#64) 3 ∗ (s0.sp - 520#64) ↦₈ List.getD k 10 0#8 ∗ memRegion (s0.sp - 519#64) 3 ∗ (s0.sp - 516#64) ↦₈ List.getD k 9 0#8 ∗ memRegion (s0.sp - 515#64) 3 ∗ (s0.sp - 512#64) ↦₈ List.getD k 8 0#8 ∗ memRegion (s0.sp - 511#64) 3 ∗ (s0.sp - 508#64) ↦₈ List.getD k 7 0#8 ∗ memRegion (s0.sp - 507#64) 3 ∗ (s0.sp - 504#64) ↦₈ List.getD k 6 0#8 ∗ memRegion (s0.sp - 503#64) 3 ∗ (s0.sp - 500#64) ↦₈ List.getD k 5 0#8 ∗ memRegion (s0.sp - 499#64) 3 ∗ (s0.sp - 496#64) ↦₈ List.getD k 4 0#8 ∗ memRegion (s0.sp - 495#64) 3 ∗ (s0.sp - 492#64) ↦₈ List.getD k 3 0#8 ∗ memRegion (s0.sp - 491#64) 3 ∗ (s0.sp - 488#64) ↦₈ List.getD k 2 0#8 ∗ memRegion (s0.sp - 487#64) 3 ∗ (s0.sp - 484#64) ↦₈ List.getD k 1 0#8 ∗ memRegion (s0.sp - 483#64) 3 ∗ (s0.sp - 480#64) ↦₈ List.getD k 0 0#8 ∗ memRegion (s0.sp - 479#64) 3 ∗ memRegion (s0.sp - 112#64) 16 ∗ (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗ (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗ (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗ (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗ (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗ (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗ key ↦ₛ k ∗ nonce ↦ₛ n ∗ tag ↦ₛ t ∗ cpMpl.ρ sigmaSym ↦ᵣ sigmaBytes))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (match aeadDecrypt k n a msg t with | some p => ⌜BitVec.truncate 32 (sf.readReg64 (Reg.gpr 0#5)) = 0#32⌝ ∗ buf ↦ₛ p | none => ⌜BitVec.truncate 32 (sf.readReg64 (Reg.gpr 0#5)) = 4294967295#32⌝ ∗ buf ↦ₛ msg) ∗ key ↦ₛ k ∗ nonce ↦ₛ n ∗ aad ↦ₛ a ∗ tag ↦ₛ t ∗ cpMpl.ρ sigmaSym ↦ᵣ sigmaBytes ∗ memRegion (s0.sp - 1168#64) 1168 ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x3d0#64) hcl ?_
  wp_steps 3
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  intro hcl7
  refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x3d4#64) hcl7 ?_
  wp_step
  rw [write64_pair _ _ _ hblk2, unpackLE_ofNat_natLe, unpackLE_ofNat_natLe]
  rw [rho5_procBlock, show cpPl5.base + 976#64 + (cpPl9.base - cpPl5.base - 976#64) = cpPl9.base by bv_omega]
  show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
  have hlens : (natLe 8 a.length ++ natLe 8 msg.length).length = 16 := by simp [natLe]
  refine MultiPlacedLib.sepWP_call_block (j := 9) (by decide) pb_blk_ok
    (x := (s0.sp - 476#64, s0.sp - 288#64, natLe 8 a.length ++ natLe 8 msg.length,
      clamp (leNat (mk.take 16)),
      polyBlocks (clamp (leNat (mk.take 16))) (polyBlocks (clamp (leNat (mk.take 16))) 0 (a ++ pad16 a))
        (msg ++ pad16 msg)))
    (ret_pc := cpPl5.base + 980#64) (F := ?F4)
    (by simpa [wp_norm, arm64_norm] using hcl7) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, State.spAligned, hsp]; simpa using hsp_align)
    (by simp [wp_norm, arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  rotate_left
  · intro R hm
    simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract]
    simp only [wp_norm, arm64_norm, hcl7, sepExists_sepConj_left, satisfies_sepExists, hsp] at hm hcl7 ⊢
    refine ⟨l2, ⟨⟨hlens, hl2⟩, hcl7⟩, ?_⟩
    simp only [← sepConj_assoc] at hm ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [sepConj_assoc]
    sep_frame
  · intro sf6 hpcf6 hrunf6 hspf6 hcsf6
    obtain ⟨i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, iv⟩ := hcsf6
    simp only [wp_norm, arm64_norm] at i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 iv hspf6
    simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract, polyBlockContract]
    refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf6]) hrunf6 ?_
    intro hcl8
    show SepWP cpProg5r _ _ _ _ _
    rw [sepExists_sepConj_left]
    refine SepWP.exists_elim fun l3 => ?_
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun hl3 => ?_
    refine Proofs.SepWP.foldPart (Entails.of_eq_explicit (polyState_bytes (s0.sp - 476#64) pw.1 pw.2.1
      pw.2.2.1 pw.2.2.2 l3)) (by sep_focus) ?_
    have hlens : (natLe 8 a.length ++ natLe 8 msg.length).length = 16 := by simp [natLe]
    refine Proofs.SepWP.foldPart (Entails.of_eq_explicit (pointsToBytes_append (s0.sp - 288#64)
      (natLe 8 a.length ++ natLe 8 msg.length) (List.drop 16 (initState k 1 n).bytes)).symm)
      (by sep_focus) ?_
    have hscl : (natLe 8 a.length ++ natLe 8 msg.length ++ List.drop 16 (initState k 1 n).bytes).length = 64 := by
      simp [natLe, Spec.State.bytes, word32Bytes]
    have hpBl := polyBytes_length pw.1 pw.2.1 pw.2.2.1 pw.2.2.2 l3
    generalize hscr : natLe 8 a.length ++ natLe 8 msg.length ++ List.drop 16 (initState k 1 n).bytes = scr64 at *
    generalize hpB : polyBytes pw.1 pw.2.1 pw.2.2.1 pw.2.2.2 l3 = pB at *
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x3f8#64) (by simpa [wp_norm, arm64_norm] using hcl8) ?_
    wp_steps 9
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf6]) ?_
    intro hcl9
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x3fc#64) hcl9 ?_
    rw [copy56 scr64 pB hscl hpBl, zero_chain8 mk hmkl]
    have hd8 : (scr64.drop 56).length = 8 := by simp [hscl]
    rw [pointsToBytes_append, hpBl, ← hpB, ← polyState_bytes]
    have hz : List.replicate 32 (0#8) = List.replicate 16 0#8 ++ List.replicate 16 0#8 := rfl
    rw [hz, pointsToBytes_append, bytes16_words _ (List.replicate 16 0#8) (by simp)]
    simp only [polyLimbsAt]
    have hρf : cpPl5.ρ "<poly1305::Poly1305 as universal_hash::UniversalHash>::finalize" = cpPl8.base := by
      have h : Obj.lookupBlockSym "<poly1305::Poly1305 as universal_hash::UniversalHash>::finalize"
          chachapolyLib.blocks = some (8, 0) := by decide +kernel
      simp [cpPl5, cpPl8, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]
    wp_step
    rw [show cpPl5.base + 1016#64 + (cpPl8.base - cpPl5.base - 1016#64) = cpPl8.base by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
    have hb := hl3.2.2.1
    refine MultiPlacedLib.sepWP_call_block (j := 8) (by decide) polyFinalContract_ok
      (x := ⟨s0.sp - 288#64, s0.sp - 144#64, pw.1, pw.2.1, pw.2.2.1, pw.2.2.2, l3.h0, l3.h1, l3.h2, l3.h3,
        l3.h4, word32At (List.replicate 16 0#8) 0, word32At (List.replicate 16 0#8) 4,
        word32At (List.replicate 16 0#8) 8, word32At (List.replicate 16 0#8) 12⟩)
      (ret_pc := cpPl5.base + 1020#64) (F := ?F5)
      (by simpa [wp_norm, arm64_norm] using hcl9) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrunf6])
      (by simp [wp_norm, arm64_norm, State.spAligned, hspf6, hsp]; simpa using hsp_align)
      (by simp [wp_norm, arm64_norm]) ?_
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
    rotate_left
    · intro R hm
      simp only [MultiPlacedLib.withCodeLoaded, polyFinalContract]
      simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj] at hm hcl9 ⊢
      refine ⟨⟨⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2⟩, hcl9⟩, ?_⟩
      simp only [← sepConj_assoc] at hm ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      simp only [sepConj_assoc]
      sep_frame
    · intro sf7 hpcf7 hrunf7 hspf7 hcsf7
      obtain ⟨j19, j20, j21, j22, j23, j24, j25, j26, j27, j28, j29, jv⟩ := hcsf7
      simp only [wp_norm, arm64_norm] at j19 j20 j21 j22 j23 j24 j25 j26 j27 j28 j29 jv hspf7
      simp only [MultiPlacedLib.withCodeLoaded, polyFinalContract]
      refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf7]) hrunf7 ?_
      intro hcl10
      show SepWP cpProg5r _ _ _ _ _
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun tg => ?_
      refine sepwp_pure_out (by sep_focus) fun htg => ?_
      rw [words4_bytes (s0.sp - 144#64), words4_natLe]
      have hTl : (natLe 16 (words4Val tg.1 tg.2.1 tg.2.2.1 tg.2.2.2)).length = 16 := by simp [natLe]
      have htag := dec_tag k n a msg mk pw.1 pw.2.1 pw.2.2.1 pw.2.2.2 tg.1 tg.2.1 tg.2.2.1 tg.2.2.2
        l3 hmk.symm hpw hl3 htg
      generalize hT : natLe 16 (words4Val tg.1 tg.2.1 tg.2.2.1 tg.2.2.2) = T at hTl htag ⊢
      rw [memRegion_split_le (s0.sp - 1168#64) 544 560 (by omega) (by omega),
        show s0.sp - 1168#64 + BitVec.ofNat 64 544 = s0.sp - 624#64 by bv_omega]
      refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x594#64) hcl10 ?_
      refine SepWP.mono (SepWP.weaken_pre ?_ (dcmp_ok ?FD _ tag (s0.sp - 96#64)
        (by simp [wp_norm, arm64_norm, j29, i29, h29]) T t
        (by simp [wp_norm, arm64_norm, hpcf7]) hrunf7
        (by simp [wp_norm, arm64_norm, hspf7, hspf6, hsp]; simpa using hsp_align)
        hcl10 (by simp [wp_norm, arm64_norm, j21, i21, h21]) hTl htl)) ?_
      · simp only [wp_norm, arm64_norm, hspf7, hspf6, hsp]
        simp only [← sepConj_assoc]
        sep_frame
      intro sf8 Pf8 hpc8 hrun8 ⟨hk8, hQ8⟩ hcl11
      refine SepWP.weaken_pre hQ8 ?_
      obtain ⟨c1, c19, c23, c24, c25, c26, c27, c28, c29, cv, c0⟩ := hk8
      simp only [wp_norm, arm64_norm, hspf7, hspf6, hsp, j19, j23, j29, i19, i23, i29, h19, h23, h29] at c1 c19 c23 c29 c0
      simp only [hspf7, hspf6, hsp, show s0.sp - 96#64 - 48#64 = s0.sp - 144#64 by bv_omega]
      refine Proofs.SepWP.foldPart (region_join (s0.sp - 1168#64) 544 560 (by omega) (by omega)) (by sep_focus) ?_
      have hρak := rho5_ak
      simp only [applyKeystreamSym] at hρak
      by_cases hTt : T = t
      · have hb : (T == t) = true := by simp [hTt]
        rw [hb] at c0
        refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x5b0#64) hcl11 ?_
        wp_steps 7
        rw [show cpPl5.base + 1452#64 + (cpPl4.base - cpPl5.base - 1452#64) = cpPl4.base by bv_omega]
        show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
        have hml' : msg.length ≤ maxMsgLen := hml
        simp only [maxMsgLen] at hml'
        refine MultiPlacedLib.sepWP_call_block (j := 4) (by decide) ak_blk_ok
          (x := ⟨s0.sp - 420#64, buf, msg, initState k 1 n, kb⟩)
          (ret_pc := cpPl5.base + 1456#64) (F := ?FK)
          (by simpa [wp_norm, arm64_norm] using hcl11) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun8]) (by simp [wp_norm, arm64_norm, State.spAligned, c1]; simpa using hsp_align)
          (by simp [wp_norm, arm64_norm]) ?_
          (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
        rotate_left
        · intro R hm
          simp only [MultiPlacedLib.withCodeLoaded, applyKeystreamContract, stackFrame]
          simp only [wp_norm, arm64_norm, and_self, pure_true_sepConj, sepConj_pure_true, c1] at hm hcl11 ⊢
          refine ⟨⟨⟨by omega, by simp [initState]; omega⟩, hcl11⟩, ?_⟩
          simp only [← sepConj_assoc] at hm ⊢
          refine Satisfies.mono (sepConj_mono_left ?_) hm
          simp only [sepConj_assoc]
          sep_frame
        · intro sf9 hpcf9 hrunf9 hspf9 hcsf9
          show SepWP cpProg5r _ _ _ _ _
          simp only [MultiPlacedLib.withCodeLoaded, applyKeystreamContract, stackFrame, wp_norm,
            arm64_norm] at hspf9 hcsf9 ⊢
          obtain ⟨f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, fv⟩ := hcsf9
          simp only [wp_norm, arm64_norm] at f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 fv hspf9
          refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf9]) hrunf9 ?_
          intro hcl12
          refine SepWP.exists_elim fun kb2 => ?_
          refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x5bc#64) hcl12 ?_
          wp_steps
          refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf9]) ?_
          intro hcl13
          refine Proofs.SepWP.foldPart (cipher129_entails (s0.sp - 420#64) _ _ _) (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (cells3_fold (s0.sp - 291#64) _ _ _) (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (slice_region (s0.sp - 476#64) _ 56 (polyBytes_length _ _ _ _ _))
            (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (words4_region (s0.sp - 288#64) _ _ _ _) (by sep_focus) ?_
          unfold limbsAt
          refine Proofs.SepWP.foldPart (limbs20_fold (s0.sp - 272#64) l3.r0 l3.r1 l3.r2 l3.r3 l3.r4)
            (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (limbs20_fold (s0.sp - 252#64) l3.h0 l3.h1 l3.h2 l3.h3 l3.h4)
            (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (slice_region (s0.sp - 232#64) (scr64.drop 56) 8 (by simp [hscl]))
            (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (carea64_fold (s0.sp - 288#64)) (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (slice_region (s0.sp - 224#64) kb.bytes 64
            (by simp [Spec.State.bytes, word32Bytes])) (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (slice_region (s0.sp - 159#64) pr 15 hpr) (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (pos16_fold (s0.sp - 160#64) 0#8) (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (slice_region (s0.sp - 144#64) T 16 hTl) (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (slice_region (s0.sp - 128#64) (List.replicate 16 0#8) 16 (by simp))
            (by sep_focus) ?_
          refine Proofs.SepWP.foldPart (region_join (s0.sp - 144#64) 16 32 (by omega) (by omega)) (by sep_focus) ?_
          rw [aeadDecrypt_eq k n a msg t T htag, if_pos hTt]
          refine SepWP.weaken_pre ?_ (decEnd_ok s0 _ R k n a t (streamXor (initState k 1 n) msg) key nonce aad buf tag
            v1 0#32 (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf9]) hcl13
            (by simp [wp_norm, arm64_norm, hspf9, c1]) hsp_align (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, fv, cv, jv, iv, hv]))
          try simp only [wp_norm, arm64_norm, hspf9, c1]
          sep_entail
      · have hb : (T == t) = false := by simp [hTt]
        rw [hb] at c0
        refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x5bc#64) hcl11 ?_
        wp_steps
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun8]) ?_
        intro hcl13
        refine Proofs.SepWP.foldPart (cipher129_entails (s0.sp - 420#64) _ _ _) (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (cells3_fold (s0.sp - 291#64) _ _ _) (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (slice_region (s0.sp - 476#64) _ 56 (polyBytes_length _ _ _ _ _))
          (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (words4_region (s0.sp - 288#64) _ _ _ _) (by sep_focus) ?_
        unfold limbsAt
        refine Proofs.SepWP.foldPart (limbs20_fold (s0.sp - 272#64) l3.r0 l3.r1 l3.r2 l3.r3 l3.r4)
          (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (limbs20_fold (s0.sp - 252#64) l3.h0 l3.h1 l3.h2 l3.h3 l3.h4)
          (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (slice_region (s0.sp - 232#64) (scr64.drop 56) 8 (by simp [hscl]))
          (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (carea64_fold (s0.sp - 288#64)) (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (slice_region (s0.sp - 224#64) kb.bytes 64
          (by simp [Spec.State.bytes, word32Bytes])) (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (slice_region (s0.sp - 159#64) pr 15 hpr) (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (pos16_fold (s0.sp - 160#64) 0#8) (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (slice_region (s0.sp - 144#64) T 16 hTl) (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (slice_region (s0.sp - 128#64) (List.replicate 16 0#8) 16 (by simp))
          (by sep_focus) ?_
        refine Proofs.SepWP.foldPart (region_join (s0.sp - 144#64) 16 32 (by omega) (by omega)) (by sep_focus) ?_
        rw [aeadDecrypt_eq k n a msg t T htag, if_neg hTt]
        refine SepWP.weaken_pre ?_ (decEnd_ok s0 _ R k n a t msg key nonce aad buf tag
          v1 4294967295#32 (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun8]) hcl13
          (by simp [wp_norm, arm64_norm, c1]) hsp_align (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, cv, jv, iv, hv]))
        try simp only [wp_norm, arm64_norm, c1]
        sep_entail

end ChaChaPoly.Proofs
