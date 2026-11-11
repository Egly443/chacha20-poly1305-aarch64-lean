module

public import ChaChaPoly.Proofs.ApplyKeystream5

/-!
# `apply_keystream` (block 4), part 6: one block of the full-block loop

`outerStep_ok` composes segment A (inlined rounds), segment B (key-stream block and data copy),
the XOR loop and segment C (copy-back): from the loop head with `k` blocks done, block `k` of the
data is XORed with `stateBlock (s.advance k)` and the counter advances.
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

/-- `akSlots` without the counter slot. -/
def akSlotsBase (sp : BitVec 64) (tail len c : BitVec 64) (s : Spec.State) (n bufp : BitVec 64) :
    SepProp :=
  (sp ↦₆₄ tail) ∗ ((sp + 8#64) ↦₆₄ len) ∗ ((sp + 16#64) ↦₆₄ c) ∗
  ((sp + 0x1c#64) ↦₃₂ s.x15) ∗ ((sp + 0x20#64) ↦₃₂ s.x14) ∗ ((sp + 0x24#64) ↦₃₂ s.x13) ∗
  ((sp + 0x28#64) ↦₃₂ s.x11) ∗ ((sp + 0x2c#64) ↦₃₂ s.x10) ∗ ((sp + 0x30#64) ↦₃₂ s.x9) ∗
  ((sp + 0x34#64) ↦₃₂ s.x8) ∗ ((sp + 0x38#64) ↦₃₂ s.x7) ∗ ((sp + 0x3c#64) ↦₃₂ s.x6) ∗
  ((sp + 0x40#64) ↦₃₂ s.x5) ∗ ((sp + 0x44#64) ↦₃₂ s.x4) ∗ ((sp + 0x48#64) ↦₃₂ s.x3) ∗
  ((sp + 0x4c#64) ↦₃₂ s.x2) ∗ ((sp + 0x50#64) ↦₃₂ s.x1) ∗ ((sp + 0x54#64) ↦₃₂ s.x0) ∗
  ((sp + 0x58#64) ↦₆₄ n) ∗ ((sp + 0x60#64) ↦₆₄ bufp)

theorem akSlots_split (sp tail len c : BitVec 64) (s : Spec.State) (n bufp : BitVec 64) (ctr : BitVec 32) :
    akSlots sp tail len c s n bufp ctr = akSlotsBase sp tail len c s n bufp ∗ ((sp + 0x6c#64) ↦₃₂ ctr) := by
  simp only [akSlots, akSlotsBase, sepConj_assoc]

theorem akSlotsBase_advance (sp tail len c : BitVec 64) (s : Spec.State) (n bufp : BitVec 64) (k : Nat) :
    akSlotsBase sp tail len c (s.advance k) n bufp = akSlotsBase sp tail len c s n bufp := rfl

/-- `akSlots` without the block-count slot `n`. -/
def akRest (sp : BitVec 64) (tail len c : BitVec 64) (s : Spec.State) (bufp : BitVec 64)
    (ctr : BitVec 32) : SepProp :=
  (sp ↦₆₄ tail) ∗ ((sp + 8#64) ↦₆₄ len) ∗ ((sp + 16#64) ↦₆₄ c) ∗
  ((sp + 0x1c#64) ↦₃₂ s.x15) ∗ ((sp + 0x20#64) ↦₃₂ s.x14) ∗ ((sp + 0x24#64) ↦₃₂ s.x13) ∗
  ((sp + 0x28#64) ↦₃₂ s.x11) ∗ ((sp + 0x2c#64) ↦₃₂ s.x10) ∗ ((sp + 0x30#64) ↦₃₂ s.x9) ∗
  ((sp + 0x34#64) ↦₃₂ s.x8) ∗ ((sp + 0x38#64) ↦₃₂ s.x7) ∗ ((sp + 0x3c#64) ↦₃₂ s.x6) ∗
  ((sp + 0x40#64) ↦₃₂ s.x5) ∗ ((sp + 0x44#64) ↦₃₂ s.x4) ∗ ((sp + 0x48#64) ↦₃₂ s.x3) ∗
  ((sp + 0x4c#64) ↦₃₂ s.x2) ∗ ((sp + 0x50#64) ↦₃₂ s.x1) ∗ ((sp + 0x54#64) ↦₃₂ s.x0) ∗
  ((sp + 0x60#64) ↦₆₄ bufp) ∗ ((sp + 0x6c#64) ↦₃₂ ctr)

theorem akSlots_n (sp tail len c : BitVec 64) (s : Spec.State) (n bufp : BitVec 64) (ctr : BitVec 32) :
    akSlots sp tail len c s n bufp ctr = ((sp + 0x58#64) ↦₆₄ n) ∗ akRest sp tail len c s bufp ctr := by
  simp only [akSlots, akRest]; sep_eq

theorem akRest_advance (sp tail len c : BitVec 64) (s : Spec.State) (bufp : BitVec 64) (ctr : BitVec 32)
    (k : Nat) : akRest sp tail len c (s.advance k) bufp ctr = akRest sp tail len c s bufp ctr := rfl

theorem pointsToBytes_three (p : BitVec 64) (T X D : Bytes) (t : Nat) (hT : T.length = t)
    (hX : X.length = 64) (ht : t < 2 ^ 63) :
    (p ↦ₛ (T ++ (X ++ D))) =
      (p ↦ₛ T) ∗ ((p + BitVec.ofNat 64 t) ↦ₛ X) ∗ ((p + BitVec.ofNat 64 (t + 64)) ↦ₛ D) := by
  rw [pointsToBytes_append, pointsToBytes_append, hT, hX, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem advance_succ_x12 (s : Spec.State) (k : Nat) :
    (s.advance (k + 1)).x12 = (s.advance k).x12 + 1#32 := by
  simp [Spec.State.advance, BitVec.add_assoc, BitVec.ofNat_add]

/-- One block of the outer loop, from its head (`0x144`) to the closing `b.ne` (`0x40c`). -/
theorem outerStep_ok [CpPlacement] (sm : Arm64.State) (s : Spec.State) (tail len c n bufp : BitVec 64)
    (k : Nat) (data : Bytes) (ctr0 : BitVec 32) (ks0 : Spec.State) (cpb ob : Bytes) (F : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x144#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true)
    (hregs : regsO sm (s.advance k)) (h10 : sm.readReg64 .x10 = BitVec.ofNat 64 k)
    (h29 : sm.readReg64 .x29 = sm.sp + 0x140#64) (h22 : sm.readReg64 .x22 = sm.sp + 0xb0#64)
    (h23 : sm.readReg64 .x23 = sm.sp + 0x70#64) (h24 : sm.readReg64 .x24 = sm.sp + 0xf0#64)
    (hv0 : sm.readVReg128 0#5 = 0#128)
    (hk : 64 * k + 64 ≤ data.length) (hL : data.length < 2 ^ 63)
    (hcp : cpb.length = 64) (hob : ob.length = 64) :
    SepWP cpProg4r (cpPl4.base + 0x40c#64) sm
      (akSlots sm.sp tail len c s n bufp ctr0 ∗ stateAt (sm.sp + 0x70#64) ks0 ∗
        ((sm.sp + 0xb0#64) ↦ₛ cpb) ∗ ((sm.sp + 0xf0#64) ↦ₛ ob) ∗ (bufp ↦ₛ akCur s data k) ∗ F)
      (sepPost (fun sm' => regsO sm' (s.advance (k + 1)) ∧ sm'.sp = sm.sp ∧
          sm'.readReg64 .x29 = sm.readReg64 .x29 ∧
          sm'.readReg64 .x10 = BitVec.ofNat 64 k + 1#64 ∧ sm'.readReg64 .x8 = n ∧
          sm'.pstate = subsPState64 n (BitVec.ofNat 64 k + 1#64) ∧
          sm'.readReg64 .x22 = sm.readReg64 .x22 ∧ sm'.readReg64 .x23 = sm.readReg64 .x23 ∧
          sm'.readReg64 .x24 = sm.readReg64 .x24 ∧ sm'.readVReg128 0#5 = 0#128)
        (akSlots sm.sp tail len c s n bufp (s.advance k).x12 ∗
          stateAt (sm.sp + 0x70#64) ((iter doubleRound 10 (s.advance k)).add (s.advance k)) ∗
          ((sm.sp + 0xb0#64) ↦ₛ blockOf data (64 * k)) ∗
          ((sm.sp + 0xf0#64) ↦ₛ xorBytes (blockOf data (64 * k)) (stateBlock (s.advance k))) ∗
          (bufp ↦ₛ akCur s data (k + 1)) ∗ F)) := by
  -- Segment A: the inlined rounds.
  refine SepWP.weaken_pre (P' := ((sm.sp + 0x6c#64) ↦₃₂ ctr0) ∗
      (akSlotsBase sm.sp tail len c s n bufp ∗ stateAt (sm.sp + 0x70#64) ks0 ∗
        ((sm.sp + 0xb0#64) ↦ₛ cpb) ∗ ((sm.sp + 0xf0#64) ↦ₛ ob) ∗ (bufp ↦ₛ akCur s data k) ∗ F))
    (by rw [akSlots_split]; sep_entail) ?_
  refine SepWP.seq_entails_emp (segA_ok sm (s.advance k) ctr0 _ hpc hrun hsp hregs) ?_
  intro sm1 hpc1 hrun1 ⟨hr1, hk1, h251⟩
  obtain ⟨k1sp, k129, k110, k122, k123, k124, k1v, k1v0⟩ := hk1
  -- Segment B: key-stream block, data-block copy, register restore.
  have hcl := akCur_length s data k (by omega)
  refine SepWP.weaken_pre (P' := akSlots sm1.sp tail len c (s.advance k) n bufp (s.advance k).x12 ∗
      stateAt (sm1.sp + 0x70#64) ks0 ∗ ((sm1.sp + 0xb0#64) ↦ₛ cpb) ∗ ((sm1.sp + 0xf0#64) ↦ₛ ob) ∗
      (bufp ↦ₛ akCur s data k) ∗ F)
    (by rw [k1sp, akSlots_split, akSlotsBase_advance]; sep_entail) ?_
  refine SepWP.seq_entails_emp (segB_ok sm1 (s.advance k) tail len c n bufp k (akCur s data k) cpb ob
    ks0 F hpc1 hrun1 (by rw [k1sp]; exact hsp) hr1 (by rw [k110, h10])
    (by rw [k129, h29, k1sp]) h251 (by rw [k1v0, hv0]) (by omega) (by omega) hcp hob) ?_
  intro sm2 hpc2 hrun2 ⟨hr2, h2sp, h229, h210, h222, h223, h224, h225, h21, h211, h2v0, h2v⟩
  rw [k1sp] at *
  rw [blockOf_akCur s data k (by omega)]
  have hblk := blockOf_length data (64 * k) hk
  -- The XOR loop.
  refine SepWP.weaken_pre (P' := ((sm.sp + 0xb0#64) ↦ₛ blockOf data (64 * k)) ∗
      ((sm.sp + 0x70#64) ↦ₛ stateBlock (s.advance k)) ∗ ((sm.sp + 0xf0#64) ↦ₛ zero64Chain ob) ∗
      (akSlots sm.sp tail len c (s.advance k) n bufp (s.advance k).x12 ∗ (bufp ↦ₛ akCur s data k) ∗ F))
    (by rw [stateAt_eq_bytes]; exact Entails.of_eq_explicit (by simp only [stateBlock]; sep_eq)) ?_
  refine SepWP.seq (xorLoop_ok sm2 _ _ _ _ _ _ _ hpc2 hrun2 hblk (stateBlock_length _)
    (zero64Chain_length ob hob) (by rw [h222, k122, h22]) (by rw [h223, k123, h23])
    (by rw [h224, k124, h24]) h225) ?_
  intro sm3 Pm hpc3 hrun3 ⟨⟨h325, hxk⟩, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  simp only [xorKeeps] at hxk
  obtain ⟨x3sp, x30, x31, x32, x33, x34, x35, x36, x37, x310, x311, x313, x314, x315, x316, x317,
    x318, x319, x320, x321, x322, x323, x324, x326, x327, x328, x329, x330, x3v0, x3v⟩ := hxk
  -- Segment C: copy back over data block `k`.
  rw [pointsToBytes_split3 bufp (akCur s data k) (64 * k) 64 (by omega)]
  have hb2 : ((akCur s data k).drop (64 * k)).take 64 = blockOf data (64 * k) :=
    blockOf_akCur s data k (by omega)
  rw [hb2]
  have hxb : (xorBytes (blockOf data (64 * k)) (stateBlock (s.advance k))).length = 64 := by
    simp [xorBytes, hblk]
  refine SepWP.weaken_pre (P' := ((sm.sp + 0x58#64) ↦₆₄ n) ∗
      ((sm.sp + 0xf0#64) ↦ₛ xorBytes (blockOf data (64 * k)) (stateBlock (s.advance k))) ∗
      ((bufp + BitVec.ofNat 64 (64 * k)) ↦ₛ blockOf data (64 * k)) ∗
      (akRest sm.sp tail len c (s.advance k) bufp (s.advance k).x12 ∗ ((sm.sp + 0xb0#64) ↦ₛ blockOf data (64 * k)) ∗
        ((sm.sp + 0x70#64) ↦ₛ stateBlock (s.advance k)) ∗ (bufp ↦ₛ (akCur s data k).take (64 * k)) ∗
        ((bufp + BitVec.ofNat 64 (64 * k + 64)) ↦ₛ (akCur s data k).drop (64 * k + 64)) ∗ F)) ?_ ?_
  · rw [akSlots_n]; sep_entail
  have e3 : sm3.sp = sm.sp := by rw [x3sp, h2sp]
  unfold regsO at hr2
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩ := hr2
  have hC := segC_ok sm3 (bufp + BitVec.ofNat 64 (64 * k)) n k (s.advance k).x12
    (blockOf data (64 * k)) (xorBytes (blockOf data (64 * k)) (stateBlock (s.advance k)))
    (akRest sm.sp tail len c (s.advance k) bufp (s.advance k).x12 ∗
        ((sm.sp + 0xb0#64) ↦ₛ blockOf data (64 * k)) ∗
        ((sm.sp + 0x70#64) ↦ₛ stateBlock (s.advance k)) ∗ (bufp ↦ₛ (akCur s data k).take (64 * k)) ∗
        ((bufp + BitVec.ofNat 64 (64 * k + 64)) ↦ₛ (akCur s data k).drop (64 * k + 64)) ∗ F)
    hpc3 hrun3 (by rw [e3]; exact hsp) (by rw [x310, h210, k110, h10])
    (by rw [x329, h229, k129, h29, e3]) (by rw [x311, h211]) (by rw [x327, r12]) hblk hxb
  rw [e3] at hC
  refine SepWP.mono hC ?_
  intro sf Pf _ _ ⟨⟨fsp, f29, f10, f27, f8, f11, fps, f0, f1, f2, f3, f4, f5, f6, f7, f14, f15, f16, f17,
    f18, f22, f23, f24, f25, f26, f28, f30, fv0, fv⟩, hQ⟩
  refine ⟨⟨?_, fsp, by rw [f29, x329, h229, k129], f10, f8, fps,
    by rw [f22, x322, h222, k122], by rw [f23, x323, h223, k123], by rw [f24, x324, h224, k124],
    by rw [fv0, x3v0, h2v0]⟩, ?_⟩
  · unfold regsO
    rw [f0, f2, f6, f7, f14, f15, f16, f17, f18, f3, f4, f5, f27, f30, f28, f26, x30, x32, x36, x37,
      x314, x315, x316, x317, x318, x33, x34, x35, x330, x328, x326, r0, r1, r2, r3, r4, r5, r6, r7,
      r8, r9, r10, r11, r13, r14, r15, advance_succ_x12]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine Entails.trans hQ ?_
    have hT : ((akCur s data k).take (64 * k)).length = 64 * k := by simp [hcl]; omega
    rw [akSlots_n, ← akRest_advance _ _ _ _ s _ _ k, stateAt_eq_bytes, ← akCur_succ s data k hk,
      pointsToBytes_three bufp _ _ _ (64 * k) hT hxb (by omega)]
    simp only [stateBlock]
    sep_entail

end ChaChaPoly.Proofs
