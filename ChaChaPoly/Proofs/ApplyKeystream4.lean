module

public import ChaChaPoly.Proofs.ApplyKeystream3

/-!
# `apply_keystream` (block 4), part 4: segment B (`0x2e0` to the XOR loop at `0x3cc`)

Adds the input state to the rounds' output (the key-stream block, as 16 words on the stack),
zeroes the output block, copies data block `k` to the stack with 128-bit loads/stores, and
restores the state registers for the next block.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
arm64_proof_prelude

/-- The spilled loop state of `apply_keystream`'s full-block path, at `sp`. -/
def akSlots (sp : BitVec 64) (tail len c : BitVec 64) (s : Spec.State) (n bufp : BitVec 64)
    (ctr : BitVec 32) : SepProp :=
  (sp ↦₆₄ tail) ∗ ((sp + 8#64) ↦₆₄ len) ∗ ((sp + 16#64) ↦₆₄ c) ∗
  ((sp + 0x1c#64) ↦₃₂ s.x15) ∗ ((sp + 0x20#64) ↦₃₂ s.x14) ∗ ((sp + 0x24#64) ↦₃₂ s.x13) ∗
  ((sp + 0x28#64) ↦₃₂ s.x11) ∗ ((sp + 0x2c#64) ↦₃₂ s.x10) ∗ ((sp + 0x30#64) ↦₃₂ s.x9) ∗
  ((sp + 0x34#64) ↦₃₂ s.x8) ∗ ((sp + 0x38#64) ↦₃₂ s.x7) ∗ ((sp + 0x3c#64) ↦₃₂ s.x6) ∗
  ((sp + 0x40#64) ↦₃₂ s.x5) ∗ ((sp + 0x44#64) ↦₃₂ s.x4) ∗ ((sp + 0x48#64) ↦₃₂ s.x3) ∗
  ((sp + 0x4c#64) ↦₃₂ s.x2) ∗ ((sp + 0x50#64) ↦₃₂ s.x1) ∗ ((sp + 0x54#64) ↦₃₂ s.x0) ∗
  ((sp + 0x58#64) ↦₆₄ n) ∗ ((sp + 0x60#64) ↦₆₄ bufp) ∗ ((sp + 0x6c#64) ↦₃₂ ctr)

/-- Block `b..b+64` of `data`. -/
def blockOf (data : Bytes) (b : Nat) : Bytes := (data.drop b).take 64

theorem readLE_blockOf (data : Bytes) (b o : Nat) :
    ∀ n, o + n ≤ 64 → ByteSlice.readLE data (b + o) n = ByteSlice.readLE (blockOf data b) o n
  | 0, _ => rfl
  | n + 1, h => by
    rw [ByteSlice.readLE_succ, ByteSlice.readLE_succ, readLE_blockOf data b o n (by omega)]
    congr 3
    simp only [blockOf, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [if_pos (by omega), show b + (o + n) = b + o + n by omega]

theorem readLE_blockOf0 (data : Bytes) (b : Nat) (n : Nat) (h : n ≤ 64) :
    ByteSlice.readLE data b n = ByteSlice.readLE (blockOf data b) 0 n := by
  simpa using readLE_blockOf data b 0 n (by omega)

theorem blockOf_length (data : Bytes) (b : Nat) (h : b + 64 ≤ data.length) :
    (blockOf data b).length = 64 := by simp [blockOf]; omega

/-- The output block after the code zeroes it with eight 64-bit stores. -/
def zero64Chain (ob : Bytes) : Bytes :=
  ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 ob 0 0#64) 8 0#64) 16 0#64) 24 0#64)
    32 0#64) 40 0#64) 48 0#64) 56 0#64

theorem zero64Chain_length (ob : Bytes) (h : ob.length = 64) : (zero64Chain ob).length = 64 := by
  unfold zero64Chain; byte_region_len

theorem segB_ok [CpPlacement] (sm : Arm64.State) (c' : Spec.State) (tail len cp n bufp : BitVec 64)
    (k : Nat) (data cpb ob : Bytes) (ks0 : Spec.State) (F : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x2e0#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true)
    (hregs : regsK sm (iter doubleRound 10 c'))
    (h10 : sm.readReg64 .x10 = BitVec.ofNat 64 k) (h29 : sm.readReg64 .x29 = sm.sp + 0x140#64)
    (h25 : sm.readReg64 .x25 = 0#64) (hv0 : sm.readVReg128 0#5 = 0#128)
    (hk : 64 * k + 64 ≤ data.length) (hL : data.length < 2 ^ 63)
    (hcp : cpb.length = 64) (hob : ob.length = 64) :
    SepWP cpProg4r (cpPl4.base + 0x3cc#64) sm
      (akSlots sm.sp tail len cp c' n bufp c'.x12 ∗ stateAt (sm.sp + 0x70#64) ks0 ∗
        ((sm.sp + 0xb0#64) ↦ₛ cpb) ∗ ((sm.sp + 0xf0#64) ↦ₛ ob) ∗ (bufp ↦ₛ data) ∗ F)
      (sepPost (fun sm' => regsO sm' c' ∧ sm'.sp = sm.sp ∧
          sm'.readReg64 .x29 = sm.readReg64 .x29 ∧ sm'.readReg64 .x10 = sm.readReg64 .x10 ∧
          sm'.readReg64 .x22 = sm.readReg64 .x22 ∧ sm'.readReg64 .x23 = sm.readReg64 .x23 ∧
          sm'.readReg64 .x24 = sm.readReg64 .x24 ∧ sm'.readReg64 .x25 = 0#64 ∧
          sm'.readReg64 .x1 = bufp ∧ sm'.readReg64 .x11 = bufp + BitVec.ofNat 64 (64 * k) ∧
          sm'.readVReg128 0#5 = 0#128 ∧ calleeSavedVRegs sm' = calleeSavedVRegs sm)
        (akSlots sm.sp tail len cp c' n bufp c'.x12 ∗
          stateAt (sm.sp + 0x70#64) ((iter doubleRound 10 c').add c') ∗
          ((sm.sp + 0xb0#64) ↦ₛ blockOf data (64 * k)) ∗ ((sm.sp + 0xf0#64) ↦ₛ zero64Chain ob) ∗
          (bufp ↦ₛ data) ∗ F)) := by
  unfold regsK at hregs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10', h11, h12, h13, h14, h15⟩ := hregs
  simp only [akSlots, stateAt] at *
  have hshl : BitVec.ofNat 64 k <<< 6 = BitVec.ofNat 64 (64 * k) := by bv_omega
  wp_steps
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨?_, ?_⟩
  · simp only [regsO, calleeSavedVRegs, wp_norm, arm64_norm]
    exact ⟨h25, hv0⟩
  · have hb := blockOf_length data (64 * k) hk
    rw [readLE_blockOf0 data (64 * k) 8 (by omega)]
    rw [readLE_blockOf data (64 * k) 8 8 (by omega), readLE_blockOf data (64 * k) 16 8 (by omega),
      readLE_blockOf data (64 * k) 24 8 (by omega), readLE_blockOf data (64 * k) 32 8 (by omega),
      readLE_blockOf data (64 * k) 40 8 (by omega), readLE_blockOf data (64 * k) 48 8 (by omega),
      readLE_blockOf data (64 * k) 56 8 (by omega)]
    rw [← ByteSlice.copyPrefix_zero cpb (blockOf data (64 * k))]
    rw [ByteSlice.write64_copyPrefix_readLE _ _ 0 (by omega),
      ByteSlice.write64_copyPrefix_readLE _ _ 8 (by omega),
      ByteSlice.write64_copyPrefix_readLE _ _ 16 (by omega),
      ByteSlice.write64_copyPrefix_readLE _ _ 24 (by omega),
      ByteSlice.write64_copyPrefix_readLE _ _ 32 (by omega),
      ByteSlice.write64_copyPrefix_readLE _ _ 40 (by omega),
      ByteSlice.write64_copyPrefix_readLE _ _ 48 (by omega),
      ByteSlice.write64_copyPrefix_readLE _ _ 56 (by omega),
      ByteSlice.copyPrefix_full hcp hb]
    simp only [Spec.State.add, zero64Chain]
    exact Entails.refl _

end ChaChaPoly.Proofs
