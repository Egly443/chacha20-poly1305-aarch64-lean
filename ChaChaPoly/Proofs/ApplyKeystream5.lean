module

public import ChaChaPoly.Proofs.ApplyKeystream4
public import ChaChaPoly.Proofs.Integrity

/-!
# `apply_keystream` (block 4), part 5: segment C (copy-back) and the outer-loop model

`segC_ok`: after the XOR loop the output block is copied back over data block `k` and the
block index and counter are incremented. `akCur s data k` is the data after `k` full blocks;
`akCur_succ` is the model step one block performs.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
arm64_proof_prelude

@[simp] theorem stateBlock_length (s : Spec.State) : (stateBlock s).length = 64 := by
  simp [stateBlock, Spec.State.bytes, word32Bytes]

theorem streamXor_short (s : Spec.State) (data : Bytes) (h : data.length ≤ 64) :
    streamXor s data = xorBytes data (stateBlock s) := by
  rw [streamXor]; split
  · rfl
  · contradiction

theorem streamXor_long (s : Spec.State) (data : Bytes) (h : ¬ data.length ≤ 64) :
    streamXor s data = xorBytes (data.take 64) (stateBlock s) ++ streamXor (s.advance 1) (data.drop 64) := by
  rw [streamXor]; split
  · contradiction
  · rfl

theorem streamXor_length (s : Spec.State) :
    ∀ (n : Nat) (data : Bytes), data.length = n → (streamXor s data).length = data.length := by
  intro n
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    intro data hn
    by_cases h : data.length ≤ 64
    · rw [streamXor_short _ _ h, xorBytes_length, stateBlock_length]; omega
    · rw [streamXor_long _ _ h, List.length_append, ih (data.drop 64).length (by simp; omega) _ _ rfl,
        xorBytes_length, stateBlock_length]
      simp; omega

theorem State.advance_zero (s : Spec.State) : s.advance 0 = s := by
  simp [Spec.State.advance]

theorem State.advance_advance (s : Spec.State) (a b : Nat) :
    (s.advance a).advance b = s.advance (a + b) := by
  simp [Spec.State.advance, BitVec.add_assoc, BitVec.ofNat_add]

theorem streamXor_nil (s : Spec.State) : streamXor s [] = [] := by
  rw [streamXor_short _ _ (by simp)]; rfl

theorem streamXor_append (s : Spec.State) :
    ∀ (j : Nat) (A B : Bytes), A.length = 64 * j →
      streamXor s (A ++ B) = streamXor s A ++ streamXor (s.advance j) B := by
  intro j
  induction j generalizing s with
  | zero =>
    intro A B hA
    have : A = [] := List.eq_nil_of_length_eq_zero (by simpa using hA)
    subst this
    rw [State.advance_zero, streamXor_nil]; rfl
  | succ j ih =>
    intro A B hA
    by_cases hj : j = 0
    · subst hj
      by_cases hB : B = []
      · subst hB; rw [List.append_nil, streamXor_nil, List.append_nil]
      · have hBl : 0 < B.length := List.length_pos_iff.mpr hB
        rw [streamXor_long _ _ (by simp; omega), streamXor_short _ A (by omega)]
        rw [List.take_left' (by omega), List.drop_left' (by omega)]
    · rw [streamXor_long _ _ (by simp; omega), streamXor_long _ A (by omega)]
      rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
        ih (s.advance 1) (A.drop 64) B (by simp; omega), State.advance_advance,
        List.append_assoc, show 1 + j = j + 1 by omega]

/-- The data after `k` full blocks of the outer loop. -/
def akCur (s : Spec.State) (data : Bytes) (k : Nat) : Bytes :=
  streamXor s (data.take (64 * k)) ++ data.drop (64 * k)

theorem akCur_length (s : Spec.State) (data : Bytes) (k : Nat) (h : 64 * k ≤ data.length) :
    (akCur s data k).length = data.length := by
  simp only [akCur, List.length_append, streamXor_length s _ _ rfl, List.length_take,
    List.length_drop]; omega

theorem akCur_take (s : Spec.State) (data : Bytes) (k : Nat) (h : 64 * k ≤ data.length) :
    (akCur s data k).take (64 * k) = streamXor s (data.take (64 * k)) := by
  rw [akCur, List.take_left' (by rw [streamXor_length s _ _ rfl]; simp; omega)]

theorem akCur_drop (s : Spec.State) (data : Bytes) (k m : Nat) (h : 64 * k ≤ data.length) :
    (akCur s data k).drop (64 * k + m) = data.drop (64 * k + m) := by
  have hl : (streamXor s (data.take (64 * k))).length = 64 * k := by
    rw [streamXor_length s _ _ rfl]; simp; omega
  rw [akCur, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hl, List.drop_drop]
  congr 1; omega

theorem blockOf_akCur (s : Spec.State) (data : Bytes) (k : Nat) (h : 64 * k ≤ data.length) :
    blockOf (akCur s data k) (64 * k) = blockOf data (64 * k) := by
  have := akCur_drop s data k 0 h
  simp only [Nat.add_zero] at this
  simp only [blockOf, this]

theorem akCur_succ (s : Spec.State) (data : Bytes) (k : Nat) (h : 64 * k + 64 ≤ data.length) :
    (akCur s data k).take (64 * k) ++
        (xorBytes (blockOf data (64 * k)) (stateBlock (s.advance k)) ++
          (akCur s data k).drop (64 * k + 64)) =
      akCur s data (k + 1) := by
  rw [akCur_take s data k (by omega), akCur_drop s data k 64 (by omega), akCur]
  have ht : data.take (64 * (k + 1)) = data.take (64 * k) ++ blockOf data (64 * k) := by
    rw [blockOf, show 64 * (k + 1) = 64 * k + 64 by omega, List.take_add]
  rw [ht, streamXor_append s k _ _ (by simp; omega),
    streamXor_short (s.advance k) (blockOf data (64 * k)) (by rw [blockOf_length data _ h]; exact Nat.le_refl 64), show 64 * (k + 1) = 64 * k + 64 by omega,
    List.append_assoc]

theorem segC_ok [CpPlacement] (sm : Arm64.State) (X n : BitVec 64) (k : Nat) (w : BitVec 32)
    (blk ob : Bytes) (F : SepProp)
    (hpc : sm.pc = cpPl4.base + 0x3ec#64) (hrun : sm.status = .Running)
    (hsp : (sm.sp &&& 15#64 == 0#64) = true)
    (h10 : sm.readReg64 .x10 = BitVec.ofNat 64 k) (h29 : sm.readReg64 .x29 = sm.sp + 0x140#64)
    (h11 : sm.readReg64 .x11 = X) (h27 : sm.readReg64 .x27 = BitVec.zeroExtend 64 w)
    (hblk : blk.length = 64) (hob : ob.length = 64) :
    SepWP cpProg4r (cpPl4.base + 0x40c#64) sm
      (((sm.sp + 0x58#64) ↦₆₄ n) ∗ ((sm.sp + 0xf0#64) ↦ₛ ob) ∗ (X ↦ₛ blk) ∗ F)
      (sepPost (fun sm' => sm'.sp = sm.sp ∧ sm'.readReg64 .x29 = sm.readReg64 .x29 ∧
          sm'.readReg64 .x10 = BitVec.ofNat 64 k + 1#64 ∧
          sm'.readReg64 .x27 = BitVec.zeroExtend 64 (w + 1#32) ∧ sm'.readReg64 .x8 = n ∧
          sm'.readReg64 .x11 = X ∧
          sm'.pstate = subsPState64 n (BitVec.ofNat 64 k + 1#64) ∧
          sm'.readReg64 .x0 = sm.readReg64 .x0 ∧
          sm'.readReg64 .x1 = sm.readReg64 .x1 ∧
          sm'.readReg64 .x2 = sm.readReg64 .x2 ∧
          sm'.readReg64 .x3 = sm.readReg64 .x3 ∧
          sm'.readReg64 .x4 = sm.readReg64 .x4 ∧
          sm'.readReg64 .x5 = sm.readReg64 .x5 ∧
          sm'.readReg64 .x6 = sm.readReg64 .x6 ∧
          sm'.readReg64 .x7 = sm.readReg64 .x7 ∧
          sm'.readReg64 .x14 = sm.readReg64 .x14 ∧
          sm'.readReg64 .x15 = sm.readReg64 .x15 ∧
          sm'.readReg64 .x16 = sm.readReg64 .x16 ∧
          sm'.readReg64 .x17 = sm.readReg64 .x17 ∧
          sm'.readReg64 .x18 = sm.readReg64 .x18 ∧
          sm'.readReg64 .x22 = sm.readReg64 .x22 ∧
          sm'.readReg64 .x23 = sm.readReg64 .x23 ∧
          sm'.readReg64 .x24 = sm.readReg64 .x24 ∧
          sm'.readReg64 .x25 = sm.readReg64 .x25 ∧
          sm'.readReg64 .x26 = sm.readReg64 .x26 ∧
          sm'.readReg64 .x28 = sm.readReg64 .x28 ∧
          sm'.readReg64 .x30 = sm.readReg64 .x30 ∧
          sm'.readVReg128 0#5 = sm.readVReg128 0#5 ∧ calleeSavedVRegs sm' = calleeSavedVRegs sm)
        (((sm.sp + 0x58#64) ↦₆₄ n) ∗ ((sm.sp + 0xf0#64) ↦ₛ ob) ∗ (X ↦ₛ ob) ∗ F)) := by
  wp_steps
  rw [← ByteSlice.copyPrefix_zero blk ob]
  rw [ByteSlice.write64_copyPrefix_readLE _ _ 0 (by omega),
    ByteSlice.write64_copyPrefix_readLE _ _ 8 (by omega),
    ByteSlice.write64_copyPrefix_readLE _ _ 16 (by omega),
    ByteSlice.write64_copyPrefix_readLE _ _ 24 (by omega),
    ByteSlice.write64_copyPrefix_readLE _ _ 32 (by omega),
    ByteSlice.write64_copyPrefix_readLE _ _ 40 (by omega),
    ByteSlice.write64_copyPrefix_readLE _ _ 48 (by omega),
    ByteSlice.write64_copyPrefix_readLE _ _ 56 (by omega),
    ByteSlice.copyPrefix_full hblk hob]
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨?_, Entails.refl _⟩
  simp [calleeSavedVRegs, wp_norm, arm64_norm, h10, h27, h11]

end ChaChaPoly.Proofs
