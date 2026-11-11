module

public import ChaChaPoly.Proofs.EncryptMac

/-!
# `chachapoly_decrypt` (block 5): the two Poly1305 passes

The same code shape as `chachapoly_encrypt`'s passes (`EncryptMac.lean`) with decrypt's register
allocation and offsets: AAD pass `0x2e8`–`0x358`, ciphertext pass `0x358`–`0x3c4`.
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

theorem rho5_procBlock [CpPlacement] :
    cpPl5.ρ "<poly1305::backend::soft::State as universal_hash::UhfBackend>::proc_block" = cpPl9.base := by
  have h : Obj.lookupBlockSym "<poly1305::backend::soft::State as universal_hash::UhfBackend>::proc_block"
      chachapolyLib.blocks = some (9, 0) := by decide +kernel
  simp [cpPl5, cpPl9, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]

theorem musl_blk_rho5 [CpPlacement] :
    cpPl5.ρ "memset" = cpMpl.base 12 ∧ cpPl5.ρ "memcpy" = cpMpl.base 11 := by
  have h1 : Obj.lookupBlockSym "memset" chachapolyLib.blocks = some (12, 0) := by decide +kernel
  have h2 : Obj.lookupBlockSym "memcpy" chachapolyLib.blocks = some (11, 0) := by decide +kernel
  simp [cpPl5, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h1, h2]

/-- Registers decrypt's AAD loop leaves unchanged (`x20` is its scratch register). -/
def dmacKeeps (sm st : Arm64.State) : Prop :=
  st.sp = sm.sp ∧ st.readReg64 .x19 = sm.readReg64 .x19 ∧ st.readReg64 .x21 = sm.readReg64 .x21 ∧
  st.readReg64 .x22 = sm.readReg64 .x22 ∧ st.readReg64 .x23 = sm.readReg64 .x23 ∧
  st.readReg64 .x24 = sm.readReg64 .x24 ∧ st.readReg64 .x25 = sm.readReg64 .x25 ∧
  st.readReg64 .x26 = sm.readReg64 .x26 ∧ st.readReg64 .x27 = sm.readReg64 .x27 ∧
  st.readReg64 .x29 = sm.readReg64 .x29 ∧ calleeSavedVRegs st = calleeSavedVRegs sm

theorem daadLoop_ok [CpPlacement] (r : Nat) :
    ∀ (j : Nat) (F : SepProp) (sm : Arm64.State) (ptr : BitVec 64) (D : Bytes) (acc : Nat) (l : PolyLimbs),
    sm.pc = cpPl5.base + 0x308#64 → sm.status = .Running → (sm.sp &&& 15#64 == 0#64) = true →
    chachapolyLib.CodeLoaded cpMpl sm.mem →
    sm.readReg64 .x28 = BitVec.ofNat 64 (16 * (j + 1)) → sm.readReg64 .x1 = ptr →
    D.length = 16 * (j + 1) → 16 * (j + 1) < 2 ^ 63 → l.Rep r acc →
    SepWP cpProg5r (cpPl5.base + 0x320#64) sm ((ptr ↦ₛ D) ∗ polyLimbsAt (sm.sp + 0x84#64) l ∗ F)
      (sepPost (fun sm' => dmacKeeps sm sm')
        (∃∗ l' : PolyLimbs, ⌜l'.Rep r (polyBlocks r acc D)⌝ ∗ (ptr ↦ₛ D) ∗
          polyLimbsAt (sm.sp + 0x84#64) l' ∗ F)) := by
  intro j
  induction j with
  | zero =>
    intro F sm ptr D acc l hpc hrun hsp hcl h28 h1 hD hlen hl
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x314#64) hcl ?_
    wp_steps 3
    rw [rho5_procBlock, show cpPl5.base + 784#64 + (cpPl9.base - cpPl5.base - 784#64) = cpPl9.base by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
    refine MultiPlacedLib.sepWP_call_block (j := 9) (by decide) pb_blk_ok
      (x := (sm.sp + 0x84#64, ptr, D, r, acc))
      (ret_pc := cpPl5.base + 788#64) (F := F)
      (by simpa [wp_norm, arm64_norm] using hcl) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, State.spAligned, hsp])
      (by simp [wp_norm, arm64_norm]) ?_
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
    · intro R hm
      simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract]
      simp only [wp_norm, arm64_norm, hcl, sepExists_sepConj_left, satisfies_sepExists] at hm ⊢
      exact ⟨l, ⟨⟨h1, by omega⟩, hl⟩, hm⟩
    · intro sf hpcf hrunf hspf hcsf
      obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcsf
      simp only [wp_norm, arm64_norm] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 cv hspf
      simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract, polyBlockContract]
      refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf]) hrunf ?_
      intro hcl2
      show SepWP cpProg5r _ _ _ _ _
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf]) ?_
      refine ⟨by simp [dmacKeeps, wp_norm, arm64_norm, hspf, c19, c21, c22, c23, c24, c25, c26, c27, c29, cv], ?_⟩
      have hp : polyBlocks r acc D = (acc + leNat (D ++ [1])) * r % p1305 := by
        have := polyBlocks_block r acc D [] (by omega)
        rw [List.append_nil] at this; rw [this, polyBlocks_nil]
      rw [hp, sepExists_sepConj_left]
      exact Entails.sepExists_elim fun l' => Entails.trans (by simp only [sepConj_assoc]; exact Entails.refl _)
        (Entails.sepExists_intro l')
  | succ j ih =>
    intro F sm ptr D acc l hpc hrun hsp hcl h28 h1 hD hlen hl
    have hB : (D.take 16).length = 16 := by simp; omega
    have hD' : (D.drop 16).length = 16 * (j + 1) := by simp; omega
    rw [show (ptr ↦ₛ D) = (ptr ↦ₛ (D.take 16 ++ D.drop 16)) by rw [List.take_append_drop],
      pointsToBytes_append, hB]
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x314#64) hcl ?_
    wp_steps 3
    rw [rho5_procBlock, show cpPl5.base + 784#64 + (cpPl9.base - cpPl5.base - 784#64) = cpPl9.base by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
    refine MultiPlacedLib.sepWP_call_block (j := 9) (by decide) pb_blk_ok
      (x := (sm.sp + 0x84#64, ptr, D.take 16, r, acc))
      (ret_pc := cpPl5.base + 788#64) (F := ((ptr + 16#64) ↦ₛ D.drop 16) ∗ F)
      (by simpa [wp_norm, arm64_norm] using hcl) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, State.spAligned, hsp])
      (by simp [wp_norm, arm64_norm]) ?_
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
    · intro R hm
      simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract]
      simp only [wp_norm, arm64_norm, hcl, sepExists_sepConj_left, satisfies_sepExists] at hm ⊢
      refine ⟨l, ⟨⟨h1, hB⟩, hl⟩, ?_⟩
      exact Satisfies.of_entails hm (by sep_entail)
    · intro sf hpcf hrunf hspf hcsf
      obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcsf
      simp only [wp_norm, arm64_norm] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 cv hspf
      simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract, polyBlockContract]
      refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf]) hrunf ?_
      intro hcl2
      show SepWP cpProg5r _ _ _ _ _
      have hsub : BitVec.ofNat 64 (16 * (j + 1 + 1)) - 16#64 = BitVec.ofNat 64 (16 * (j + 1)) := by
        bv_omega
      have hnz : BitVec.ofNat 64 (16 * (j + 1)) ≠ 0#64 := by bv_omega
      have hne16 : ¬BitVec.ofNat 64 (16 * (j + 1 + 1)) = 16#64 := by bv_omega
      wp_steps 3
      rw [sepExists_sepConj_left]
      refine SepWP.exists_elim fun l2 => ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim fun hl2 => ?_
      refine SepWP.mono (SepWP.weaken_pre ?_ (ih ((ptr ↦ₛ D.take 16) ∗ F) _ (ptr + 16#64) (D.drop 16) _ l2
        (by simp [wp_norm, arm64_norm, hne16]) (by simp [wp_norm, arm64_norm, hrunf])
        (by simp [wp_norm, arm64_norm, hspf, hsp]) (by simpa [wp_norm, arm64_norm] using hcl2)
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) hD' (by omega) hl2)) ?_
      · simp only [wp_norm, arm64_norm, hspf]
        sep_entail
      intro sf2 Pf _ _ ⟨hk2, hQ⟩
      refine ⟨?_, Entails.trans hQ ?_⟩
      · simp only [dmacKeeps, wp_norm, arm64_norm, hspf] at hk2 ⊢
        obtain ⟨k1, k20, k21, k22, k23, k24, k25, k26, k27, k29, kv⟩ := hk2
        exact ⟨k1, k20.trans c19, k21.trans c21, k22.trans c22, k23.trans c23, k24.trans c24,
          k25.trans c25, k26.trans c26, k27.trans c27, k29.trans c29, kv.trans cv⟩
      · have hp : polyBlocks r acc D =
            polyBlocks r ((acc + leNat (D.take 16 ++ [1])) * r % p1305) (D.drop 16) := by
          conv => lhs; rw [← List.take_append_drop 16 D]
          exact polyBlocks_block r acc _ _ hB
        simp only [wp_norm, arm64_norm, hspf, hp, sepExists_sepConj_left]
        exact Entails.sepExists_elim fun l3 => Entails.trans (by sep_entail)
          (Entails.sepExists_intro l3)

theorem daadTail_ok [CpPlacement] (F : SepProp) (sm : Arm64.State) (aad scr : BitVec 64)
    (T blk : Bytes) (full r acc : Nat) (l : PolyLimbs)
    (hpc : sm.pc = cpPl5.base + 0x320#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true) (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (h27 : sm.readReg64 .x27 = BitVec.ofNat 64 T.length) (h26 : sm.readReg64 .x26 = BitVec.ofNat 64 full)
    (h21 : sm.readReg64 .x24 = BitVec.ofNat 64 (full + T.length)) (h23 : sm.readReg64 .x23 = aad)
    (h29 : sm.readReg64 .x29 = scr + 0xc0#64)
    (hT : T.length < 16) (hblk : blk.length = 16) (hf16 : full % 16 = 0) (hfull : full + T.length < 2 ^ 63)
    (hl : l.Rep r acc) :
    SepWP cpProg5r (cpPl5.base + 0x358#64) sm
      (((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ (scr ↦ₛ blk) ∗ polyLimbsAt (sm.sp + 0x84#64) l ∗ F)
      (sepPost (fun sm' => dmacKeeps sm sm')
        (∃∗ l' : PolyLimbs, ∃∗ blk' : Bytes,
          ⌜l'.Rep r (polyBlocks r acc (T ++ pad16 T)) ∧ blk'.length = 16⌝ ∗
          ((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ (scr ↦ₛ blk') ∗ polyLimbsAt (sm.sp + 0x84#64) l' ∗ F)) := by
  by_cases ht : T.length = 0
  · have hT0 : T = [] := List.eq_nil_of_length_eq_zero ht
    subst hT0
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp [dmacKeeps, wp_norm, arm64_norm], ?_⟩
    rw [pad16_nil, List.append_nil, polyBlocks_nil]
    refine Entails.trans ?_ (Entails.sepExists_intro l)
    refine Entails.trans ?_ (Entails.sepExists_intro blk)
    rw [pure_sepConj_of_true ⟨hl, hblk⟩]
    sep_entail
  · have hnz : BitVec.ofNat 64 T.length ≠ 0#64 := by
      intro h; apply ht; have := congrArg BitVec.toNat h; simp at this; omega
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x33c#64) hcl ?_
    have htk : (blk.take T.length).length = T.length := by simp; omega
    have hdl : (blk.drop T.length).length = 16 - T.length := by simp; omega
    rw [show (scr ↦ₛ blk) = (scr ↦ₛ (blk.take T.length ++ blk.drop T.length)) by rw [List.take_append_drop],
      pointsToBytes_append, htk]
    refine SepWP.foldPart (pointsToBytes_entails_memRegion (scr + BitVec.ofNat 64 T.length) (blk.drop T.length)) (by sep_focus) ?_
    rw [hdl]
    wp_steps 7
    rw [musl_blk_rho5.1, show cpPl5.base + 824#64 + (cpMpl.base 12 - cpPl5.base - 824#64) = cpMpl.base 12 by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
    have hn16 : (16#64 - BitVec.ofNat 64 T.length).toNat = 16 - T.length := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
    refine MultiPlacedLib.sepWP_call_block (j := 12) (by decide) memset_blk_ok
      (x := (scr + BitVec.ofNat 64 T.length, 0#32, 16#64 - BitVec.ofNat 64 T.length))
      (ret_pc := cpPl5.base + 828#64)
      (F := ((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ (scr ↦ₛ blk.take T.length) ∗
        polyLimbsAt (sm.sp + 0x84#64) l ∗ F)
      (by simpa [wp_norm, arm64_norm] using hcl) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, State.spAligned, hsp])
      (by simp [wp_norm, arm64_norm]) ?_
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
    · intro R hm
      simp only [VerifiedLibraries.Musl.memsetSymSpec, CType.U32, CType.SizeT, hn16]
      simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      refine ⟨by simp [CType.SemType.valWf], ?_⟩
      exact Satisfies.of_entails hm (by sep_entail)
    · intro sf hpcf hrunf hspf hcsf
      obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcsf
      simp only [wp_norm, arm64_norm] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 cv hspf
      simp only [VerifiedLibraries.Musl.memsetSymSpec, CType.MutSlice8, CType.Bytes,
        CType.SemType.interp, hn16, sepConj_assoc]
      simp only [show BitVec.setWidth 8 0#32 = 0#8 from rfl]
      refine SepWP.pure_elim fun _ => ?_
      refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf]) hrunf ?_
      intro hcl2
      show SepWP cpProg5r _ _ _ _ _
      refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x34c#64) hcl2 ?_
      refine SepWP.foldPart (pointsToBytes_entails_memRegion scr (blk.take T.length)) (by sep_focus) ?_
      rw [htk]
      have hm15 := mask15_val full T.length hf16 hT hfull
      wp_steps 4
      rw [musl_blk_rho5.2, show cpPl5.base + 840#64 + (cpMpl.base 11 - cpPl5.base - 840#64) = cpMpl.base 11 by bv_omega]
      show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
      refine MultiPlacedLib.sepWP_call_block (j := 11) (by decide) memcpy_blk_ok
        (x := (scr, aad + BitVec.ofNat 64 full, T))
        (ret_pc := cpPl5.base + 844#64)
        (F := ((scr + BitVec.ofNat 64 T.length) ↦ₛ List.replicate (16 - T.length) 0#8) ∗
          polyLimbsAt (sm.sp + 0x84#64) l ∗ F)
        (by simpa [wp_norm, arm64_norm] using hcl2) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrunf]) (by simp [wp_norm, arm64_norm, State.spAligned, hspf, hsp])
        (by simp [wp_norm, arm64_norm]) ?_
        (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
      · intro R hm
        simp only [muslMemcpySpec]
        simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, c21, c23, c24, c26, c29,
          h21, h23, h26, h29, hm15] at hm ⊢
        refine ⟨by omega, ?_⟩
        exact Satisfies.of_entails hm (by sep_entail)
      · intro sf2 hpcf2 hrunf2 hspf2 hcsf2
        obtain ⟨d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, dv⟩ := hcsf2
        simp only [wp_norm, arm64_norm] at d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 dv hspf2
        simp only [muslMemcpySpec, sepConj_assoc]
        refine SepWP.pure_elim fun _ => ?_
        refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf2]) hrunf2 ?_
        intro hcl3
        show SepWP cpProg5r _ _ _ _ _
        have hblk' : (T ++ List.replicate (16 - T.length) 0#8).length = 16 := by simp; omega
        refine SepWP.foldPart (Entails.of_eq_explicit (pointsToBytes_append scr T
          (List.replicate (16 - T.length) 0#8)).symm) (by sep_focus) ?_
        wp_steps 3
        rw [rho5_procBlock, show cpPl5.base + 852#64 + (cpPl9.base - cpPl5.base - 852#64) = cpPl9.base by bv_omega]
        show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
        refine MultiPlacedLib.sepWP_call_block (j := 9) (by decide) pb_blk_ok
          (x := (sm.sp + 0x84#64, scr, T ++ List.replicate (16 - T.length) 0#8, r, acc))
          (ret_pc := cpPl5.base + 856#64) (F := ((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ F)
          (by simpa [wp_norm, arm64_norm] using hcl3) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrunf2])
          (by simp [wp_norm, arm64_norm, State.spAligned, hspf2, hspf, hsp])
          (by simp [wp_norm, arm64_norm]) ?_
          (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
        · intro R hm
          simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract]
          simp only [wp_norm, arm64_norm, hcl3, sepExists_sepConj_left, satisfies_sepExists, d29, c29, h29,
            hspf2, hspf] at hm ⊢
          refine ⟨l, ⟨?_, hl⟩, ?_⟩
          · first | exact hblk' | exact ⟨by bv_omega, hblk'⟩ | (simp_all; done)
          exact Satisfies.of_entails hm (by sep_entail)
        · intro sf3 hpcf3 hrunf3 hspf3 hcsf3
          obtain ⟨e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, ev⟩ := hcsf3
          simp only [wp_norm, arm64_norm] at e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 ev hspf3
          simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract, polyBlockContract]
          refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf3]) hrunf3 ?_
          refine ⟨by simp only [dmacKeeps, wp_norm, arm64_norm, hspf3, hspf2, hspf, e19, e20, e21, e22, e23, e24,
            e25, e26, e27, e29, ev, d19, d20, d21, d22, d23, d24, d25, d26, d27, d29, dv, c19, c20, c21, c22, c23, c24,
            c25, c26, c27, c29, cv], ?_⟩
          have hpad : pad16 T = List.replicate (16 - T.length) 0#8 := by
            simp only [pad16]; congr 1; omega
          have hp : polyBlocks r acc (T ++ pad16 T) =
              (acc + leNat (T ++ List.replicate (16 - T.length) 0#8 ++ [1])) * r % p1305 := by
            have h1 := polyBlocks_block r acc (T ++ List.replicate (16 - T.length) 0#8) [] hblk'
            simp only [List.append_nil] at h1
            rw [hpad, h1, polyBlocks_nil]
          rw [hp]
          simp only [wp_norm, arm64_norm, hspf3, hspf2, hspf, sepExists_sepConj_left]
          refine Entails.sepExists_elim fun l' => ?_
          refine Entails.trans ?_ (Entails.sepExists_intro l')
          refine Entails.trans ?_ (Entails.sepExists_intro (T ++ List.replicate (16 - T.length) 0#8))
          refine Entails.pure_left fun hl' => ?_
          rw [pure_sepConj_of_true ⟨hl', hblk'⟩]
          sep_entail

/-- Registers decrypt's AAD pass leaves unchanged, and the buffer pointer it copies to `x22`. -/
def dmacKeepsA (sm st : Arm64.State) : Prop :=
  st.sp = sm.sp ∧ st.readReg64 .x19 = sm.readReg64 .x19 ∧ st.readReg64 .x21 = sm.readReg64 .x21 ∧
  st.readReg64 .x22 = sm.readReg64 .x20 ∧ st.readReg64 .x23 = sm.readReg64 .x23 ∧
  st.readReg64 .x25 = sm.readReg64 .x25 ∧ st.readReg64 .x29 = sm.readReg64 .x29 ∧
  calleeSavedVRegs st = calleeSavedVRegs sm

theorem dmacAad_ok [CpPlacement] (F : SepProp) (sm : Arm64.State) (aad scr : BitVec 64)
    (A blk : Bytes) (r acc : Nat) (l : PolyLimbs)
    (hpc : sm.pc = cpPl5.base + 0x2e8#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true) (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (h21 : sm.readReg64 .x27 = BitVec.ofNat 64 A.length) (h23 : sm.readReg64 .x23 = aad)
    (h29 : sm.readReg64 .x29 = scr + 0xc0#64)
    (hA : A.length < 2 ^ 63) (hblk : blk.length = 16) (hl : l.Rep r acc) :
    SepWP cpProg5r (cpPl5.base + 0x358#64) sm
      ((aad ↦ₛ A) ∗ (scr ↦ₛ blk) ∗ polyLimbsAt (sm.sp + 0x84#64) l ∗ F)
      (sepPost (fun sm' => dmacKeepsA sm sm')
        (∃∗ l' : PolyLimbs, ∃∗ blk' : Bytes,
          ⌜l'.Rep r (polyBlocks r acc (A ++ pad16 A)) ∧ blk'.length = 16⌝ ∗
          (aad ↦ₛ A) ∗ (scr ↦ₛ blk') ∗ polyLimbsAt (sm.sp + 0x84#64) l' ∗ F)) := by
  have hfm := mask16_val A.length hA
  have htm := mask15_val (16 * (A.length / 16)) (A.length % 16) (by omega) (by omega) (by omega)
  rw [show 16 * (A.length / 16) + A.length % 16 = A.length by omega] at htm
  have hT : (A.drop (16 * (A.length / 16))).length = A.length % 16 := by simp; omega
  have hsplit : A ++ pad16 A = A.take (16 * (A.length / 16)) ++
      (A.drop (16 * (A.length / 16)) ++ pad16 (A.drop (16 * (A.length / 16)))) := by
    rw [← List.append_assoc, List.take_append_drop, ← pad16_drop]
  rw [hsplit, polyBlocks_append r (A.length / 16) _ _ _ (by simp; omega)]
  clear hsplit
  by_cases hsm : A.length < 16
  · have h0 : A.length / 16 = 0 := by omega
    simp only [h0, Nat.mul_zero, List.take_zero, polyBlocks_nil, List.drop_zero] at hT htm hfm ⊢
    have hlo : (BitVec.ofNat 64 A.length).ult 16#64 = true := by simp [BitVec.ult]; omega
    clear hT
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x320#64) hcl ?_
    wp_steps 6
    refine SepWP.done (by simp [wp_norm, arm64_norm, hlo]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    intro hcl1
    refine SepWP.mono (SepWP.weaken_pre ?_ (daadTail_ok F _ aad scr A
      blk 0 r acc l (by simp [wp_norm, arm64_norm, hlo]) (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [wp_norm, arm64_norm] using hsp) (by simpa [wp_norm, arm64_norm] using hcl1)
      (by simp [wp_norm, arm64_norm, Nat.mod_eq_of_lt hsm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, h21]) (by simp [wp_norm, arm64_norm, h23])
      (by simp [wp_norm, arm64_norm, h29]) hsm hblk (by decide) (by omega) hl)) ?_
    · simp only [wp_norm, arm64_norm, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      sep_entail
    intro sf Pf _ _ ⟨hk, hQ⟩
    simp only [dmacKeeps, wp_norm, arm64_norm] at hk
    refine ⟨?_, Entails.trans hQ ?_⟩
    · obtain ⟨k1, k19, k21, k22, k23, k24, k25, k26, k27, k29, kv⟩ := hk
      exact ⟨k1, k19, k21, k22, k23, k25, k29, kv⟩
    · simp only [wp_norm, arm64_norm, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      exact Entails.refl _
  · obtain ⟨j, hj⟩ : ∃ j, A.length / 16 = j + 1 := ⟨A.length / 16 - 1, by omega⟩
    have hlo : (BitVec.ofNat 64 A.length).ult 16#64 = false := by simp [BitVec.ult]; omega
    have htl : (A.take (16 * (A.length / 16))).length = 16 * (A.length / 16) := by simp; omega
    have hAs : (aad ↦ₛ A) = (aad ↦ₛ A.take (16 * (A.length / 16))) ∗
        ((aad + BitVec.ofNat 64 (16 * (A.length / 16))) ↦ₛ A.drop (16 * (A.length / 16))) := by
      conv => lhs; rw [← List.take_append_drop (16 * (A.length / 16)) A]
      rw [pointsToBytes_append, htl]
    rw [hAs]
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x308#64) hcl ?_
    wp_steps 8
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    intro hclm
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x320#64) hclm ?_
    rw [hj] at htl hT ⊢
    have hfl : 16 * (j + 1) + A.length % 16 = A.length := by omega
    refine SepWP.mono (SepWP.weaken_pre ?_ (daadLoop_ok r j
      (((aad + BitVec.ofNat 64 (16 * (j + 1))) ↦ₛ A.drop (16 * (j + 1))) ∗ (scr ↦ₛ blk) ∗ F) _ aad (A.take (16 * (j + 1))) acc l
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [wp_norm, arm64_norm] using hsp) (by simpa [wp_norm, arm64_norm] using hclm)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) htl (by omega) hl)) ?_
    · simp only [wp_norm, arm64_norm]
      sep_entail
    intro s1 P1 hpc1 hrun1 ⟨hk1, hQ1⟩ hcl1
    simp only [dmacKeeps, wp_norm, arm64_norm] at hk1
    obtain ⟨k1, k19, k21, k22, k23, k24, k25, k26, k27, k29, kv⟩ := hk1
    refine SepWP.weaken_pre hQ1 ?_
    refine SepWP.exists_elim fun l1 => ?_
    refine SepWP.pure_elim fun hl1 => ?_
    refine SepWP.mono (SepWP.weaken_pre ?_ (daadTail_ok
      ((aad ↦ₛ A.take (16 * (j + 1))) ∗ F) s1 aad scr
      (A.drop (16 * (j + 1))) blk (16 * (j + 1)) r _ l1 hpc1 hrun1
      (by rw [k1]; simpa [wp_norm, arm64_norm] using hsp) hcl1
      (by rw [k27, hT]) (by rw [k26]) (by rw [k24]; (try rw [h21]); rw [hT, hfl]) (by rw [k23, h23])
      (by rw [k29, h29]) (by rw [hT]; omega) hblk (by omega) (by rw [hT]; omega) hl1)) ?_
    · simp only [k1]
      sep_entail
    intro sf Pf _ _ ⟨hk, hQ⟩
    simp only [dmacKeeps] at hk
    obtain ⟨g1, g19, g21, g22, g23, g24, g25, g26, g27, g29, gv⟩ := hk
    refine ⟨⟨by rw [g1, k1], by rw [g19, k19], by rw [g21, k21], by rw [g22, k22], by rw [g23, k23],
      by rw [g25, k25], by rw [g29, k29], by rw [gv, kv]⟩, Entails.trans hQ ?_⟩
    simp only [k1]
    refine Entails.sepExists_elim fun l' => Entails.sepExists_elim fun b' => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro l')
    refine Entails.trans ?_ (Entails.sepExists_intro b')
    sep_entail

/-- Registers decrypt's ciphertext loop and tail leave unchanged (`x20`, `x27` are scratch). -/
def dmacKeepsC (sm st : Arm64.State) : Prop :=
  st.sp = sm.sp ∧ st.readReg64 .x19 = sm.readReg64 .x19 ∧ st.readReg64 .x21 = sm.readReg64 .x21 ∧
  st.readReg64 .x22 = sm.readReg64 .x22 ∧ st.readReg64 .x23 = sm.readReg64 .x23 ∧
  st.readReg64 .x24 = sm.readReg64 .x24 ∧ st.readReg64 .x25 = sm.readReg64 .x25 ∧
  st.readReg64 .x26 = sm.readReg64 .x26 ∧ st.readReg64 .x28 = sm.readReg64 .x28 ∧
  st.readReg64 .x29 = sm.readReg64 .x29 ∧ calleeSavedVRegs st = calleeSavedVRegs sm

theorem dctLoop_ok [CpPlacement] (r : Nat) :
    ∀ (j : Nat) (F : SepProp) (sm : Arm64.State) (ptr : BitVec 64) (D : Bytes) (acc : Nat) (l : PolyLimbs),
    sm.pc = cpPl5.base + 0x374#64 → sm.status = .Running → (sm.sp &&& 15#64 == 0#64) = true →
    chachapolyLib.CodeLoaded cpMpl sm.mem →
    sm.readReg64 .x27 = BitVec.ofNat 64 (16 * (j + 1)) → sm.readReg64 .x1 = ptr →
    D.length = 16 * (j + 1) → 16 * (j + 1) < 2 ^ 63 → l.Rep r acc →
    SepWP cpProg5r (cpPl5.base + 0x38c#64) sm ((ptr ↦ₛ D) ∗ polyLimbsAt (sm.sp + 0x84#64) l ∗ F)
      (sepPost (fun sm' => dmacKeepsC sm sm')
        (∃∗ l' : PolyLimbs, ⌜l'.Rep r (polyBlocks r acc D)⌝ ∗ (ptr ↦ₛ D) ∗
          polyLimbsAt (sm.sp + 0x84#64) l' ∗ F)) := by
  intro j
  induction j with
  | zero =>
    intro F sm ptr D acc l hpc hrun hsp hcl h28 h1 hD hlen hl
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x380#64) hcl ?_
    wp_steps 3
    rw [rho5_procBlock, show cpPl5.base + 892#64 + (cpPl9.base - cpPl5.base - 892#64) = cpPl9.base by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
    refine MultiPlacedLib.sepWP_call_block (j := 9) (by decide) pb_blk_ok
      (x := (sm.sp + 0x84#64, ptr, D, r, acc))
      (ret_pc := cpPl5.base + 896#64) (F := F)
      (by simpa [wp_norm, arm64_norm] using hcl) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, State.spAligned, hsp])
      (by simp [wp_norm, arm64_norm]) ?_
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
    · intro R hm
      simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract]
      simp only [wp_norm, arm64_norm, hcl, sepExists_sepConj_left, satisfies_sepExists] at hm ⊢
      exact ⟨l, ⟨⟨h1, by omega⟩, hl⟩, hm⟩
    · intro sf hpcf hrunf hspf hcsf
      obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcsf
      simp only [wp_norm, arm64_norm] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 cv hspf
      simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract, polyBlockContract]
      refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf]) hrunf ?_
      intro hcl2
      show SepWP cpProg5r _ _ _ _ _
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf]) ?_
      refine ⟨by simp [dmacKeepsC, wp_norm, arm64_norm, hspf, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv], ?_⟩
      have hp : polyBlocks r acc D = (acc + leNat (D ++ [1])) * r % p1305 := by
        have := polyBlocks_block r acc D [] (by omega)
        rw [List.append_nil] at this; rw [this, polyBlocks_nil]
      rw [hp, sepExists_sepConj_left]
      exact Entails.sepExists_elim fun l' => Entails.trans (by simp only [sepConj_assoc]; exact Entails.refl _)
        (Entails.sepExists_intro l')
  | succ j ih =>
    intro F sm ptr D acc l hpc hrun hsp hcl h28 h1 hD hlen hl
    have hB : (D.take 16).length = 16 := by simp; omega
    have hD' : (D.drop 16).length = 16 * (j + 1) := by simp; omega
    rw [show (ptr ↦ₛ D) = (ptr ↦ₛ (D.take 16 ++ D.drop 16)) by rw [List.take_append_drop],
      pointsToBytes_append, hB]
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x380#64) hcl ?_
    wp_steps 3
    rw [rho5_procBlock, show cpPl5.base + 892#64 + (cpPl9.base - cpPl5.base - 892#64) = cpPl9.base by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
    refine MultiPlacedLib.sepWP_call_block (j := 9) (by decide) pb_blk_ok
      (x := (sm.sp + 0x84#64, ptr, D.take 16, r, acc))
      (ret_pc := cpPl5.base + 896#64) (F := ((ptr + 16#64) ↦ₛ D.drop 16) ∗ F)
      (by simpa [wp_norm, arm64_norm] using hcl) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, State.spAligned, hsp])
      (by simp [wp_norm, arm64_norm]) ?_
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
    · intro R hm
      simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract]
      simp only [wp_norm, arm64_norm, hcl, sepExists_sepConj_left, satisfies_sepExists] at hm ⊢
      refine ⟨l, ⟨⟨h1, hB⟩, hl⟩, ?_⟩
      exact Satisfies.of_entails hm (by sep_entail)
    · intro sf hpcf hrunf hspf hcsf
      obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcsf
      simp only [wp_norm, arm64_norm] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 cv hspf
      simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract, polyBlockContract]
      refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf]) hrunf ?_
      intro hcl2
      show SepWP cpProg5r _ _ _ _ _
      have hsub : BitVec.ofNat 64 (16 * (j + 1 + 1)) - 16#64 = BitVec.ofNat 64 (16 * (j + 1)) := by
        bv_omega
      have hnz : BitVec.ofNat 64 (16 * (j + 1)) ≠ 0#64 := by bv_omega
      have hne16 : ¬BitVec.ofNat 64 (16 * (j + 1 + 1)) = 16#64 := by bv_omega
      wp_steps 3
      rw [sepExists_sepConj_left]
      refine SepWP.exists_elim fun l2 => ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim fun hl2 => ?_
      refine SepWP.mono (SepWP.weaken_pre ?_ (ih ((ptr ↦ₛ D.take 16) ∗ F) _ (ptr + 16#64) (D.drop 16) _ l2
        (by simp [wp_norm, arm64_norm, hne16]) (by simp [wp_norm, arm64_norm, hrunf])
        (by simp [wp_norm, arm64_norm, hspf, hsp]) (by simpa [wp_norm, arm64_norm] using hcl2)
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) hD' (by omega) hl2)) ?_
      · simp only [wp_norm, arm64_norm, hspf]
        sep_entail
      intro sf2 Pf _ _ ⟨hk2, hQ⟩
      refine ⟨?_, Entails.trans hQ ?_⟩
      · simp only [dmacKeepsC, wp_norm, arm64_norm, hspf] at hk2 ⊢
        obtain ⟨k1, k20, k21, k22, k23, k24, k25, k27, k28, k29, kv⟩ := hk2
        exact ⟨k1, k20.trans c19, k21.trans c21, k22.trans c22, k23.trans c23, k24.trans c24,
          k25.trans c25, k27.trans c26, k28.trans c28, k29.trans c29, kv.trans cv⟩
      · have hp : polyBlocks r acc D =
            polyBlocks r ((acc + leNat (D.take 16 ++ [1])) * r % p1305) (D.drop 16) := by
          conv => lhs; rw [← List.take_append_drop 16 D]
          exact polyBlocks_block r acc _ _ hB
        simp only [wp_norm, arm64_norm, hspf, hp, sepExists_sepConj_left]
        exact Entails.sepExists_elim fun l3 => Entails.trans (by sep_entail)
          (Entails.sepExists_intro l3)

theorem dctTail_ok [CpPlacement] (F : SepProp) (sm : Arm64.State) (aad scr : BitVec 64)
    (T blk : Bytes) (full r acc : Nat) (l : PolyLimbs)
    (hpc : sm.pc = cpPl5.base + 0x38c#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true) (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (h24x : sm.readReg64 .x26 = BitVec.ofNat 64 T.length) (h23x : sm.readReg64 .x28 = BitVec.ofNat 64 full)
    (h20x : sm.readReg64 .x19 = BitVec.ofNat 64 (full + T.length)) (h22x : sm.readReg64 .x23 = aad)
    (h29 : sm.readReg64 .x29 = scr + 0xc0#64)
    (hT : T.length < 16) (hblk : blk.length = 16) (hf16 : full % 16 = 0) (hfull : full + T.length < 2 ^ 63)
    (hl : l.Rep r acc) :
    SepWP cpProg5r (cpPl5.base + 0x3c4#64) sm
      (((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ (scr ↦ₛ blk) ∗ polyLimbsAt (sm.sp + 0x84#64) l ∗ F)
      (sepPost (fun sm' => dmacKeepsC sm sm')
        (∃∗ l' : PolyLimbs, ∃∗ blk' : Bytes,
          ⌜l'.Rep r (polyBlocks r acc (T ++ pad16 T)) ∧ blk'.length = 16⌝ ∗
          ((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ (scr ↦ₛ blk') ∗ polyLimbsAt (sm.sp + 0x84#64) l' ∗ F)) := by
  by_cases ht : T.length = 0
  · have hT0 : T = [] := List.eq_nil_of_length_eq_zero ht
    subst hT0
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp [dmacKeepsC, wp_norm, arm64_norm], ?_⟩
    rw [pad16_nil, List.append_nil, polyBlocks_nil]
    refine Entails.trans ?_ (Entails.sepExists_intro l)
    refine Entails.trans ?_ (Entails.sepExists_intro blk)
    rw [pure_sepConj_of_true ⟨hl, hblk⟩]
    sep_entail
  · have hnz : BitVec.ofNat 64 T.length ≠ 0#64 := by
      intro h; apply ht; have := congrArg BitVec.toNat h; simp at this; omega
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x3a8#64) hcl ?_
    have htk : (blk.take T.length).length = T.length := by simp; omega
    have hdl : (blk.drop T.length).length = 16 - T.length := by simp; omega
    rw [show (scr ↦ₛ blk) = (scr ↦ₛ (blk.take T.length ++ blk.drop T.length)) by rw [List.take_append_drop],
      pointsToBytes_append, htk]
    refine SepWP.foldPart (pointsToBytes_entails_memRegion (scr + BitVec.ofNat 64 T.length) (blk.drop T.length)) (by sep_focus) ?_
    rw [hdl]
    wp_steps 7
    rw [musl_blk_rho5.1, show cpPl5.base + 932#64 + (cpMpl.base 12 - cpPl5.base - 932#64) = cpMpl.base 12 by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
    have hn16 : (16#64 - BitVec.ofNat 64 T.length).toNat = 16 - T.length := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
    refine MultiPlacedLib.sepWP_call_block (j := 12) (by decide) memset_blk_ok
      (x := (scr + BitVec.ofNat 64 T.length, 0#32, 16#64 - BitVec.ofNat 64 T.length))
      (ret_pc := cpPl5.base + 936#64)
      (F := ((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ (scr ↦ₛ blk.take T.length) ∗
        polyLimbsAt (sm.sp + 0x84#64) l ∗ F)
      (by simpa [wp_norm, arm64_norm] using hcl) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, State.spAligned, hsp])
      (by simp [wp_norm, arm64_norm]) ?_
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
    · intro R hm
      simp only [VerifiedLibraries.Musl.memsetSymSpec, CType.U32, CType.SizeT, hn16]
      simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      refine ⟨by simp [CType.SemType.valWf], ?_⟩
      exact Satisfies.of_entails hm (by sep_entail)
    · intro sf hpcf hrunf hspf hcsf
      obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcsf
      simp only [wp_norm, arm64_norm] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 cv hspf
      simp only [VerifiedLibraries.Musl.memsetSymSpec, CType.MutSlice8, CType.Bytes,
        CType.SemType.interp, hn16, sepConj_assoc]
      simp only [show BitVec.setWidth 8 0#32 = 0#8 from rfl]
      refine SepWP.pure_elim fun _ => ?_
      refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf]) hrunf ?_
      intro hcl2
      show SepWP cpProg5r _ _ _ _ _
      refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x3b8#64) hcl2 ?_
      refine SepWP.foldPart (pointsToBytes_entails_memRegion scr (blk.take T.length)) (by sep_focus) ?_
      rw [htk]
      have hm15 := mask15_val full T.length hf16 hT hfull
      wp_steps 4
      rw [musl_blk_rho5.2, show cpPl5.base + 948#64 + (cpMpl.base 11 - cpPl5.base - 948#64) = cpMpl.base 11 by bv_omega]
      show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
      refine MultiPlacedLib.sepWP_call_block (j := 11) (by decide) memcpy_blk_ok
        (x := (scr, aad + BitVec.ofNat 64 full, T))
        (ret_pc := cpPl5.base + 952#64)
        (F := ((scr + BitVec.ofNat 64 T.length) ↦ₛ List.replicate (16 - T.length) 0#8) ∗
          polyLimbsAt (sm.sp + 0x84#64) l ∗ F)
        (by simpa [wp_norm, arm64_norm] using hcl2) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrunf]) (by simp [wp_norm, arm64_norm, State.spAligned, hspf, hsp])
        (by simp [wp_norm, arm64_norm]) ?_
        (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
      · intro R hm
        simp only [muslMemcpySpec]
        simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, c20, c21, c22, c23, c24,
          c19, c26, c28, c29, h20x, h22x, h23x, h29, hm15] at hm ⊢
        refine ⟨by omega, ?_⟩
        exact Satisfies.of_entails hm (by sep_entail)
      · intro sf2 hpcf2 hrunf2 hspf2 hcsf2
        obtain ⟨d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, dv⟩ := hcsf2
        simp only [wp_norm, arm64_norm] at d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 dv hspf2
        simp only [muslMemcpySpec, sepConj_assoc]
        refine SepWP.pure_elim fun _ => ?_
        refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf2]) hrunf2 ?_
        intro hcl3
        show SepWP cpProg5r _ _ _ _ _
        have hblk' : (T ++ List.replicate (16 - T.length) 0#8).length = 16 := by simp; omega
        refine SepWP.foldPart (Entails.of_eq_explicit (pointsToBytes_append scr T
          (List.replicate (16 - T.length) 0#8)).symm) (by sep_focus) ?_
        wp_steps 3
        rw [rho5_procBlock, show cpPl5.base + 960#64 + (cpPl9.base - cpPl5.base - 960#64) = cpPl9.base by bv_omega]
        show SepWP (chachapolyLib.blockProgram cpMpl 5) _ _ _ _ _
        refine MultiPlacedLib.sepWP_call_block (j := 9) (by decide) pb_blk_ok
          (x := (sm.sp + 0x84#64, scr, T ++ List.replicate (16 - T.length) 0#8, r, acc))
          (ret_pc := cpPl5.base + 964#64) (F := ((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ F)
          (by simpa [wp_norm, arm64_norm] using hcl3) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrunf2])
          (by simp [wp_norm, arm64_norm, State.spAligned, hspf2, hspf, hsp])
          (by simp [wp_norm, arm64_norm]) ?_
          (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
        · intro R hm
          simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract]
          simp only [wp_norm, arm64_norm, hcl3, sepExists_sepConj_left, satisfies_sepExists, d29, c29, h29,
            hspf2, hspf] at hm ⊢
          refine ⟨l, ⟨?_, hl⟩, ?_⟩
          · first | exact hblk' | exact ⟨by bv_omega, hblk'⟩ | (simp_all; done)
          exact Satisfies.of_entails hm (by sep_entail)
        · intro sf3 hpcf3 hrunf3 hspf3 hcsf3
          obtain ⟨e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, ev⟩ := hcsf3
          simp only [wp_norm, arm64_norm] at e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 ev hspf3
          simp only [MultiPlacedLib.withCodeLoaded, polyProcBlockContract, polyBlockContract]
          refine SepWP.done (by simp [wp_norm, arm64_norm, hpcf3]) hrunf3 ?_
          refine ⟨by simp only [dmacKeepsC, wp_norm, arm64_norm, hspf3, hspf2, hspf, e20, e21, e22, e23, e24,
            e25, e26, e27, e28, e29, e19, ev, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, dv, c19, c20, c21, c22, c23,
            c24, c25, c26, c27, c28, c29, cv], ?_⟩
          have hpad : pad16 T = List.replicate (16 - T.length) 0#8 := by
            simp only [pad16]; congr 1; omega
          have hp : polyBlocks r acc (T ++ pad16 T) =
              (acc + leNat (T ++ List.replicate (16 - T.length) 0#8 ++ [1])) * r % p1305 := by
            have h1 := polyBlocks_block r acc (T ++ List.replicate (16 - T.length) 0#8) [] hblk'
            simp only [List.append_nil] at h1
            rw [hpad, h1, polyBlocks_nil]
          rw [hp]
          simp only [wp_norm, arm64_norm, hspf3, hspf2, hspf, sepExists_sepConj_left]
          refine Entails.sepExists_elim fun l' => ?_
          refine Entails.trans ?_ (Entails.sepExists_intro l')
          refine Entails.trans ?_ (Entails.sepExists_intro (T ++ List.replicate (16 - T.length) 0#8))
          refine Entails.pure_left fun hl' => ?_
          rw [pure_sepConj_of_true ⟨hl', hblk'⟩]
          sep_entail

/-- Registers decrypt's ciphertext pass leaves unchanged (`x24` still holds the AAD length). -/
def dmacKeepsT (sm st : Arm64.State) : Prop :=
  st.sp = sm.sp ∧ st.readReg64 .x19 = sm.readReg64 .x19 ∧ st.readReg64 .x21 = sm.readReg64 .x21 ∧
  st.readReg64 .x22 = sm.readReg64 .x22 ∧ st.readReg64 .x24 = sm.readReg64 .x24 ∧
  st.readReg64 .x25 = sm.readReg64 .x25 ∧ st.readReg64 .x29 = sm.readReg64 .x29 ∧
  calleeSavedVRegs st = calleeSavedVRegs sm

theorem dmacCt_ok [CpPlacement] (F : SepProp) (sm : Arm64.State) (aad scr : BitVec 64)
    (A blk : Bytes) (r acc : Nat) (l : PolyLimbs)
    (hpc : sm.pc = cpPl5.base + 0x358#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true) (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (h21 : sm.readReg64 .x19 = BitVec.ofNat 64 A.length) (h23 : sm.readReg64 .x22 = aad)
    (h29 : sm.readReg64 .x29 = scr + 0xc0#64)
    (hA : A.length < 2 ^ 38) (hblk : blk.length = 16) (hl : l.Rep r acc) :
    SepWP cpProg5r (cpPl5.base + 0x3c4#64) sm
      ((aad ↦ₛ A) ∗ (scr ↦ₛ blk) ∗ polyLimbsAt (sm.sp + 0x84#64) l ∗ F)
      (sepPost (fun sm' => dmacKeepsT sm sm')
        (∃∗ l' : PolyLimbs, ∃∗ blk' : Bytes,
          ⌜l'.Rep r (polyBlocks r acc (A ++ pad16 A)) ∧ blk'.length = 16⌝ ∗
          (aad ↦ₛ A) ∗ (scr ↦ₛ blk') ∗ polyLimbsAt (sm.sp + 0x84#64) l' ∗ F)) := by
  have hfm := mask38_val A.length hA
  have htm := mask15_val (16 * (A.length / 16)) (A.length % 16) (by omega) (by omega) (by omega)
  rw [show 16 * (A.length / 16) + A.length % 16 = A.length by omega] at htm
  have hT : (A.drop (16 * (A.length / 16))).length = A.length % 16 := by simp; omega
  have hsplit : A ++ pad16 A = A.take (16 * (A.length / 16)) ++
      (A.drop (16 * (A.length / 16)) ++ pad16 (A.drop (16 * (A.length / 16)))) := by
    rw [← List.append_assoc, List.take_append_drop, ← pad16_drop]
  rw [hsplit, polyBlocks_append r (A.length / 16) _ _ _ (by simp; omega)]
  clear hsplit
  by_cases hsm : A.length < 16
  · have h0 : A.length / 16 = 0 := by omega
    simp only [h0, Nat.mul_zero, List.take_zero, polyBlocks_nil, List.drop_zero] at hT htm hfm ⊢
    have hlo : (BitVec.ofNat 64 A.length).ult 16#64 = true := by simp [BitVec.ult]; omega
    clear hT
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x38c#64) hcl ?_
    wp_steps 5
    refine SepWP.done (by simp [wp_norm, arm64_norm, hlo]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    intro hcl1
    refine SepWP.mono (SepWP.weaken_pre ?_ (dctTail_ok F _ aad scr A
      blk 0 r acc l (by simp [wp_norm, arm64_norm, hlo]) (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [wp_norm, arm64_norm] using hsp) (by simpa [wp_norm, arm64_norm] using hcl1)
      (by simp [wp_norm, arm64_norm, Nat.mod_eq_of_lt hsm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, h21]) (by simp [wp_norm, arm64_norm, h23])
      (by simp [wp_norm, arm64_norm, h29]) hsm hblk (by decide) (by omega) hl)) ?_
    · simp only [wp_norm, arm64_norm, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      sep_entail
    intro sf Pf _ _ ⟨hk, hQ⟩
    simp only [dmacKeepsC, wp_norm, arm64_norm] at hk
    refine ⟨?_, Entails.trans hQ ?_⟩
    · obtain ⟨k1, k19, k21, k22, k23, k24, k25, k26, k28, k29, kv⟩ := hk
      exact ⟨k1, k19, k21, k22, k24, k25, k29, kv⟩
    · simp only [wp_norm, arm64_norm, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      exact Entails.refl _
  · obtain ⟨j, hj⟩ : ∃ j, A.length / 16 = j + 1 := ⟨A.length / 16 - 1, by omega⟩
    have hlo : (BitVec.ofNat 64 A.length).ult 16#64 = false := by simp [BitVec.ult]; omega
    have htl : (A.take (16 * (A.length / 16))).length = 16 * (A.length / 16) := by simp; omega
    have hAs : (aad ↦ₛ A) = (aad ↦ₛ A.take (16 * (A.length / 16))) ∗
        ((aad + BitVec.ofNat 64 (16 * (A.length / 16))) ↦ₛ A.drop (16 * (A.length / 16))) := by
      conv => lhs; rw [← List.take_append_drop (16 * (A.length / 16)) A]
      rw [pointsToBytes_append, htl]
    rw [hAs]
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x374#64) hcl ?_
    wp_steps 7
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    intro hclm
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl5.base + 0x38c#64) hclm ?_
    rw [hj] at htl hT ⊢
    have hfl : 16 * (j + 1) + A.length % 16 = A.length := by omega
    refine SepWP.mono (SepWP.weaken_pre ?_ (dctLoop_ok r j
      (((aad + BitVec.ofNat 64 (16 * (j + 1))) ↦ₛ A.drop (16 * (j + 1))) ∗ (scr ↦ₛ blk) ∗
        F) _ aad (A.take (16 * (j + 1))) acc l
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [wp_norm, arm64_norm] using hsp) (by simpa [wp_norm, arm64_norm] using hclm)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) htl (by omega) hl)) ?_
    · simp only [wp_norm, arm64_norm]
      sep_entail
    intro s1 P1 hpc1 hrun1 ⟨hk1, hQ1⟩ hcl1
    simp only [dmacKeepsC, wp_norm, arm64_norm] at hk1
    obtain ⟨k1, k19, k21, k22, k23, k24, k25, k26, k28, k29, kv⟩ := hk1
    refine SepWP.weaken_pre hQ1 ?_
    refine SepWP.exists_elim fun l1 => ?_
    refine SepWP.pure_elim fun hl1 => ?_
    refine SepWP.mono (SepWP.weaken_pre ?_ (dctTail_ok
      ((aad ↦ₛ A.take (16 * (j + 1))) ∗ F) s1 aad scr
      (A.drop (16 * (j + 1))) blk (16 * (j + 1)) r _ l1 hpc1 hrun1
      (by rw [k1]; simpa [wp_norm, arm64_norm] using hsp) hcl1
      (by rw [k26, hT]) (by rw [k28]) (by rw [k19]; (try rw [h21]); rw [hT, hfl]) (by rw [k23]; (try rw [h23]))
      (by rw [k29, h29]) (by rw [hT]; omega) hblk (by omega) (by rw [hT]; omega) hl1)) ?_
    · simp only [k1]
      sep_entail
    intro sf Pf _ _ ⟨hk, hQ⟩
    simp only [dmacKeepsC] at hk
    obtain ⟨g1, g19, g21, g22, g23, g24, g25, g26, g28, g29, gv⟩ := hk
    refine ⟨⟨by rw [g1, k1], by rw [g19, k19], by rw [g21, k21], by rw [g22, k22], by rw [g24, k24],
      by rw [g25, k25], by rw [g29, k29], by rw [gv, kv]⟩, Entails.trans hQ ?_⟩
    simp only [k1]
    refine Entails.sepExists_elim fun l' => Entails.sepExists_elim fun b' => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro l')
    refine Entails.trans ?_ (Entails.sepExists_intro b')
    sep_entail

end ChaChaPoly.Proofs
