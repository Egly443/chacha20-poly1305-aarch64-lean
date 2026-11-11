import ChaChaPoly.Proofs
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec ChaChaPoly.Proofs
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
arm64_proof_prelude

theorem SepWP.foldPart {prog : Program} {t : BitVec 64} {s : Arm64.State} {P T T' F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hent : T ⊢ T') (hf : P = T ∗ F) (h : SepWP prog t s (T' ∗ F) post oom) :
    SepWP prog t s P post oom :=
  SepWP.weaken_pre (hf ▸ sepConj_mono_left hent) h

theorem polyBlocks_block (r acc : Nat) (B Y : Bytes) (hB : B.length = 16) :
    polyBlocks r acc (B ++ Y) = polyBlocks r ((acc + leNat (B ++ [1])) * r % p1305) Y := by
  rw [polyBlocks]
  have hne : B ++ Y ≠ [] := by intro h; have := congrArg List.length h; simp only [List.length_append, List.length_nil] at this; omega
  simp only [hne, dite_false, List.take_left' hB, List.drop_left' hB]

theorem polyBlocks_nil (r acc : Nat) : polyBlocks r acc [] = acc := by
  rw [polyBlocks]; simp

#print axioms polyBlocks_block

theorem pb_blk_ok [CpPlacement] :
    subroutine_ok (chachapolyLib.blockProgram cpMpl 9) cpPl9.base
      (chachapolyLib.withCodeLoaded cpMpl polyProcBlockContract) := polyProcBlockContract_ok

theorem rho6_procBlock [CpPlacement] :
    cpPl6.ρ "<poly1305::backend::soft::State as universal_hash::UhfBackend>::proc_block" = cpPl9.base := by
  have h : Obj.lookupBlockSym "<poly1305::backend::soft::State as universal_hash::UhfBackend>::proc_block"
      chachapolyLib.blocks = some (9, 0) := by decide +kernel
  simp [cpPl6, cpPl9, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]

/-- Registers the MAC loops leave unchanged. -/
def macKeeps (sm st : Arm64.State) : Prop :=
  st.sp = sm.sp ∧ st.readReg64 .x20 = sm.readReg64 .x20 ∧ st.readReg64 .x21 = sm.readReg64 .x21 ∧
  st.readReg64 .x22 = sm.readReg64 .x22 ∧ st.readReg64 .x23 = sm.readReg64 .x23 ∧
  st.readReg64 .x24 = sm.readReg64 .x24 ∧ st.readReg64 .x25 = sm.readReg64 .x25 ∧
  st.readReg64 .x26 = sm.readReg64 .x26 ∧ st.readReg64 .x27 = sm.readReg64 .x27 ∧
  st.readReg64 .x29 = sm.readReg64 .x29 ∧ calleeSavedVRegs st = calleeSavedVRegs sm

theorem aadLoop_ok [CpPlacement] (r : Nat) :
    ∀ (j : Nat) (F : SepProp) (sm : Arm64.State) (ptr : BitVec 64) (D : Bytes) (acc : Nat) (l : PolyLimbs),
    sm.pc = cpPl6.base + 0x310#64 → sm.status = .Running → (sm.sp &&& 15#64 == 0#64) = true →
    chachapolyLib.CodeLoaded cpMpl sm.mem →
    sm.readReg64 .x28 = BitVec.ofNat 64 (16 * (j + 1)) → sm.readReg64 .x1 = ptr →
    D.length = 16 * (j + 1) → 16 * (j + 1) < 2 ^ 63 → l.Rep r acc →
    SepWP cpProg6r (cpPl6.base + 0x328#64) sm ((ptr ↦ₛ D) ∗ polyLimbsAt (sm.sp + 0x94#64) l ∗ F)
      (sepPost (fun sm' => macKeeps sm sm')
        (∃∗ l' : PolyLimbs, ⌜l'.Rep r (polyBlocks r acc D)⌝ ∗ (ptr ↦ₛ D) ∗
          polyLimbsAt (sm.sp + 0x94#64) l' ∗ F)) := by
  intro j
  induction j with
  | zero =>
    intro F sm ptr D acc l hpc hrun hsp hcl h28 h1 hD hlen hl
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl6.base + 0x31c#64) hcl ?_
    wp_steps 3
    rw [rho6_procBlock, show cpPl6.base + 792#64 + (cpPl9.base - cpPl6.base - 792#64) = cpPl9.base by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 6) _ _ _ _ _
    refine MultiPlacedLib.sepWP_call_block (j := 9) (by decide) pb_blk_ok
      (x := (sm.sp + 0x94#64, ptr, D, r, acc))
      (ret_pc := cpPl6.base + 796#64) (F := F)
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
      show SepWP cpProg6r _ _ _ _ _
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunf]) ?_
      refine ⟨by simp [macKeeps, wp_norm, arm64_norm, hspf, c20, c21, c22, c23, c24, c25, c26, c27, c29, cv], ?_⟩
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
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl6.base + 0x31c#64) hcl ?_
    wp_steps 3
    rw [rho6_procBlock, show cpPl6.base + 792#64 + (cpPl9.base - cpPl6.base - 792#64) = cpPl9.base by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 6) _ _ _ _ _
    refine MultiPlacedLib.sepWP_call_block (j := 9) (by decide) pb_blk_ok
      (x := (sm.sp + 0x94#64, ptr, D.take 16, r, acc))
      (ret_pc := cpPl6.base + 796#64) (F := ((ptr + 16#64) ↦ₛ D.drop 16) ∗ F)
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
      show SepWP cpProg6r _ _ _ _ _
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
      · simp only [macKeeps, wp_norm, arm64_norm, hspf] at hk2 ⊢
        obtain ⟨k1, k20, k21, k22, k23, k24, k25, k26, k27, k29, kv⟩ := hk2
        exact ⟨k1, k20.trans c20, k21.trans c21, k22.trans c22, k23.trans c23, k24.trans c24,
          k25.trans c25, k26.trans c26, k27.trans c27, k29.trans c29, kv.trans cv⟩
      · have hp : polyBlocks r acc D =
            polyBlocks r ((acc + leNat (D.take 16 ++ [1])) * r % p1305) (D.drop 16) := by
          conv => lhs; rw [← List.take_append_drop 16 D]
          exact polyBlocks_block r acc _ _ hB
        simp only [wp_norm, arm64_norm, hspf, hp, sepExists_sepConj_left]
        exact Entails.sepExists_elim fun l3 => Entails.trans (by sep_entail)
          (Entails.sepExists_intro l3)


theorem musl_blk_rho [CpPlacement] :
    cpPl6.ρ "memset" = cpMpl.base 12 ∧ cpPl6.ρ "memcpy" = cpMpl.base 11 := by
  have h1 : Obj.lookupBlockSym "memset" chachapolyLib.blocks = some (12, 0) := by decide +kernel
  have h2 : Obj.lookupBlockSym "memcpy" chachapolyLib.blocks = some (11, 0) := by decide +kernel
  simp [cpPl6, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h1, h2]

theorem mask15_val (full t : Nat) (hf16 : full % 16 = 0) (ht : t < 16) (hfull : full + 16 < 2 ^ 63) :
    BitVec.ofNat 64 (full + t) &&& 15#64 = BitVec.ofNat 64 t := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (15 : Nat) % 2 ^ 64 = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem pad16_nil : pad16 [] = [] := rfl

theorem aadTail_ok [CpPlacement] (F : SepProp) (sm : Arm64.State) (aad scr : BitVec 64)
    (T blk : Bytes) (full r acc : Nat) (l : PolyLimbs)
    (hpc : sm.pc = cpPl6.base + 0x328#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true) (hcl : chachapolyLib.CodeLoaded cpMpl sm.mem)
    (h27 : sm.readReg64 .x27 = BitVec.ofNat 64 T.length) (h26 : sm.readReg64 .x26 = BitVec.ofNat 64 full)
    (h21 : sm.readReg64 .x21 = BitVec.ofNat 64 (full + T.length)) (h23 : sm.readReg64 .x23 = aad)
    (h29 : sm.readReg64 .x29 = scr + 0xc0#64)
    (hT : T.length < 16) (hblk : blk.length = 16) (hf16 : full % 16 = 0) (hfull : full + 16 < 2 ^ 63)
    (hl : l.Rep r acc) :
    SepWP cpProg6r (cpPl6.base + 0x360#64) sm
      (((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ (scr ↦ₛ blk) ∗ polyLimbsAt (sm.sp + 0x94#64) l ∗ F)
      (sepPost (fun sm' => macKeeps sm sm')
        (∃∗ l' : PolyLimbs, ∃∗ blk' : Bytes,
          ⌜l'.Rep r (polyBlocks r acc (T ++ pad16 T)) ∧ blk'.length = 16⌝ ∗
          ((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ (scr ↦ₛ blk') ∗ polyLimbsAt (sm.sp + 0x94#64) l' ∗ F)) := by
  by_cases ht : T.length = 0
  · have hT0 : T = [] := List.eq_nil_of_length_eq_zero ht
    subst hT0
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp [macKeeps, wp_norm, arm64_norm], ?_⟩
    rw [pad16_nil, List.append_nil, polyBlocks_nil]
    refine Entails.trans ?_ (Entails.sepExists_intro l)
    refine Entails.trans ?_ (Entails.sepExists_intro blk)
    rw [pure_sepConj_of_true ⟨hl, hblk⟩]
    sep_entail
  · have hnz : BitVec.ofNat 64 T.length ≠ 0#64 := by
      intro h; apply ht; have := congrArg BitVec.toNat h; simp at this; omega
    refine MultiPlacedLib.seq_codeLoaded (mid := cpPl6.base + 0x344#64) hcl ?_
    have htk : (blk.take T.length).length = T.length := by simp; omega
    have hdl : (blk.drop T.length).length = 16 - T.length := by simp; omega
    rw [show (scr ↦ₛ blk) = (scr ↦ₛ (blk.take T.length ++ blk.drop T.length)) by rw [List.take_append_drop],
      pointsToBytes_append, htk]
    refine SepWP.foldPart (pointsToBytes_entails_memRegion (scr + BitVec.ofNat 64 T.length) (blk.drop T.length)) (by sep_focus) ?_
    rw [hdl]
    wp_steps 7
    rw [musl_blk_rho.1, show cpPl6.base + 832#64 + (cpMpl.base 12 - cpPl6.base - 832#64) = cpMpl.base 12 by bv_omega]
    show SepWP (chachapolyLib.blockProgram cpMpl 6) _ _ _ _ _
    have hn16 : (16#64 - BitVec.ofNat 64 T.length).toNat = 16 - T.length := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
    refine MultiPlacedLib.sepWP_call_block (j := 12) (by decide) memset_blk_ok
      (x := (scr + BitVec.ofNat 64 T.length, 0#32, 16#64 - BitVec.ofNat 64 T.length))
      (ret_pc := cpPl6.base + 836#64)
      (F := ((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ (scr ↦ₛ blk.take T.length) ∗
        polyLimbsAt (sm.sp + 0x94#64) l ∗ F)
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
      show SepWP cpProg6r _ _ _ _ _
      refine MultiPlacedLib.seq_codeLoaded (mid := cpPl6.base + 0x354#64) hcl2 ?_
      refine SepWP.foldPart (pointsToBytes_entails_memRegion scr (blk.take T.length)) (by sep_focus) ?_
      rw [htk]
      have hm15 := mask15_val full T.length hf16 hT hfull
      wp_steps 4
      rw [musl_blk_rho.2, show cpPl6.base + 848#64 + (cpMpl.base 11 - cpPl6.base - 848#64) = cpMpl.base 11 by bv_omega]
      show SepWP (chachapolyLib.blockProgram cpMpl 6) _ _ _ _ _
      refine MultiPlacedLib.sepWP_call_block (j := 11) (by decide) memcpy_blk_ok
        (x := (scr, aad + BitVec.ofNat 64 full, T))
        (ret_pc := cpPl6.base + 852#64)
        (F := ((scr + BitVec.ofNat 64 T.length) ↦ₛ List.replicate (16 - T.length) 0#8) ∗
          polyLimbsAt (sm.sp + 0x94#64) l ∗ F)
        (by simpa [wp_norm, arm64_norm] using hcl2) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrunf]) (by simp [wp_norm, arm64_norm, State.spAligned, hspf, hsp])
        (by simp [wp_norm, arm64_norm]) ?_
        (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
      · intro R hm
        simp only [muslMemcpySpec]
        simp only [wp_norm, arm64_norm, sepConj_assoc, satisfies_pure_sepConj, c21, c23, c26, c29,
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
        show SepWP cpProg6r _ _ _ _ _
        have hblk' : (T ++ List.replicate (16 - T.length) 0#8).length = 16 := by simp; omega
        refine SepWP.foldPart (Entails.of_eq_explicit (pointsToBytes_append scr T
          (List.replicate (16 - T.length) 0#8)).symm) (by sep_focus) ?_
        wp_steps 3
        rw [rho6_procBlock, show cpPl6.base + 860#64 + (cpPl9.base - cpPl6.base - 860#64) = cpPl9.base by bv_omega]
        show SepWP (chachapolyLib.blockProgram cpMpl 6) _ _ _ _ _
        refine MultiPlacedLib.sepWP_call_block (j := 9) (by decide) pb_blk_ok
          (x := (sm.sp + 0x94#64, scr, T ++ List.replicate (16 - T.length) 0#8, r, acc))
          (ret_pc := cpPl6.base + 864#64) (F := ((aad + BitVec.ofNat 64 full) ↦ₛ T) ∗ F)
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
          refine ⟨by simp only [macKeeps, wp_norm, arm64_norm, hspf3, hspf2, hspf, e20, e21, e22, e23, e24,
            e25, e26, e27, e29, ev, d20, d21, d22, d23, d24, d25, d26, d27, d29, dv, c20, c21, c22, c23, c24,
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

#print axioms aadTail_ok
