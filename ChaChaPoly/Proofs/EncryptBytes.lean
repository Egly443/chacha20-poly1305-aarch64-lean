module

public import ChaChaPoly.Proofs.EncryptMac

/-!
# `chachapoly_encrypt` (block 6): byte-slice identities

The encrypt prologue copies the ChaCha state and key-stream buffer into the cipher struct with
pairs of 64-bit loads and stores (`pair_copy`) and one 32-bit store (`quad_pack`); the counter
word it writes is the one already there (`advance1_bytes`).
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 ProofLib ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 400000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem write64_readLE (dst src : List (BitVec 8)) (o o' : Nat) (h : o' + 8 ≤ src.length) :
    ByteSlice.write64 dst o (ByteSlice.readLE src o' 8) = ProofLib.ByteSlice.write dst o (ProofLib.ByteSlice.slice src o' 8) := by
  rw [ByteSlice.write64_eq_writeLE, ByteSlice.writeLE, ByteSlice.unpackLE_readLE src o' 8 h]

theorem write32_pack32 (dst : List (BitVec 8)) (o : Nat) (b0 b1 b2 b3 : BitVec 8) :
    ByteSlice.write32 dst o (pack32 b0 b1 b2 b3) = ProofLib.ByteSlice.write dst o [b0, b1, b2, b3] := by
  rw [ByteSlice.write32_eq_writeLE, ByteSlice.writeLE]
  congr 1
  exact unpack32_pack32 b0 b1 b2 b3

theorem pair_copy (D src : List (BitVec 8)) (o o' : Nat) (ho : o' = o + 8) (hD : D.length = 16)
    (h : o + 16 ≤ src.length) :
    ByteSlice.write64 (ByteSlice.write64 D 0 (ByteSlice.readLE src o 8)) 8 (ByteSlice.readLE src o' 8) =
      ProofLib.ByteSlice.slice src o 16 := by
  subst ho
  rw [write64_readLE _ _ _ _ (by omega), write64_readLE _ _ _ _ (by omega)]
  apply List.ext_getElem
  · simp [ProofLib.ByteSlice.write, ProofLib.ByteSlice.slice]; omega
  · intro i h1 h2
    have hi : i < 16 := by simp [ProofLib.ByteSlice.slice] at h2; omega
    simp only [ProofLib.ByteSlice.write, ProofLib.ByteSlice.slice, List.getElem_append, List.getElem_take,
      List.getElem_drop, List.length_append, List.length_take, List.length_drop]
    have hm : min 8 (src.length - o) = 8 := by omega
    have hm2 : min 8 (src.length - (o + 8)) = 8 := by omega
    simp only [hm, hm2, hD, Nat.min_def, Nat.zero_le, ite_true] at h1 h2 ⊢
    repeat' split
    all_goals first | omega | (congr 1; omega) | (simp_all; done) | skip

theorem quad_pack (D : List (BitVec 8)) (b0 b1 b2 b3 : BitVec 8) (hD : D.length = 4) :
    ByteSlice.write32 D 0 (pack32 b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  rw [write32_pack32]
  match D, hD with
  | _ :: _ :: _ :: _ :: [], _ => rfl


theorem slices4 (X : List (BitVec 8)) (hX : X.length = 64) :
    X = ProofLib.ByteSlice.slice X 0 16 ++ (ProofLib.ByteSlice.slice X 16 16 ++
      (ProofLib.ByteSlice.slice X 32 16 ++ ProofLib.ByteSlice.slice X 48 16)) := by
  apply List.ext_getElem
  · simp [ProofLib.ByteSlice.slice]; omega
  · intro i h1 h2
    simp only [ProofLib.ByteSlice.slice, List.getElem_append, List.getElem_take, List.getElem_drop,
      List.length_append, List.length_take, List.length_drop, hX]
    repeat' split
    all_goals first | omega | (congr 1; omega) | (simp_all; done) | skip

theorem four_slices (c : BitVec 64) (X : List (BitVec 8)) (hX : X.length = 64) :
    ((c ↦ₛ ProofLib.ByteSlice.slice X 0 16) ∗ ((c + 16#64) ↦ₛ ProofLib.ByteSlice.slice X 16 16) ∗
      ((c + 32#64) ↦ₛ ProofLib.ByteSlice.slice X 32 16) ∗ ((c + 48#64) ↦ₛ ProofLib.ByteSlice.slice X 48 16)) =
    (c ↦ₛ X) := by
  have hl : ∀ o, o + 16 ≤ 64 → (ProofLib.ByteSlice.slice X o 16).length = 16 := by
    intro o ho; simp [ProofLib.ByteSlice.slice]; omega
  conv => rhs; rw [slices4 X hX]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, hl 0 (by omega), hl 16 (by omega),
    hl 32 (by omega), BitVec.add_assoc, BitVec.add_assoc]
  rfl

theorem advance1_bytes (k n : Bytes) :
    ByteSlice.write32 ((initState k 0 n).advance 1).bytes 48 1#32 = (initState k 1 n).bytes := by
  simp only [Spec.State.advance, initState, Spec.State.bytes, ByteSlice.write32_eq_writeLE,
    ByteSlice.writeLE, ProofLib.ByteSlice.write]
  rfl

theorem slice_write32_lo (sb : List (BitVec 8)) (o : Nat) (h : o + 16 ≤ 48) (hs : sb.length = 64) :
    ProofLib.ByteSlice.slice (ByteSlice.write32 sb 48 1#32) o 16 = ProofLib.ByteSlice.slice sb o 16 := by
  have hu : (ByteSlice.unpackLE 4 1#32).length = 4 := by simp
  apply List.ext_getElem
  · simp [ProofLib.ByteSlice.slice, ByteSlice.write32_eq_writeLE, ByteSlice.writeLE, ProofLib.ByteSlice.write]
    omega
  · intro i h1 h2
    have hi : i < 16 := by simp [ProofLib.ByteSlice.slice] at h2; omega
    simp only [ProofLib.ByteSlice.slice, ByteSlice.write32_eq_writeLE, ByteSlice.writeLE,
      ProofLib.ByteSlice.write, List.getElem_append, List.getElem_take, List.getElem_drop,
      List.length_take, List.length_append, List.length_drop, hu, hs]
    repeat' split
    all_goals first | omega | (congr 1; omega) | (simp_all; done) | skip

theorem unpackLE_ofNat_natLe (x : Nat) :
    ByteSlice.unpackLE 8 (BitVec.ofNat 64 x) = natLe 8 x := by
  simp only [ByteSlice.unpackLE, natLe, List.range, List.range.loop, List.map]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩⟩⟩⟩⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega

theorem write64_pair (D : List (BitVec 8)) (v1 v2 : BitVec 64) (hD : D.length = 16) :
    ByteSlice.write64 (ByteSlice.write64 D 0 v1) 8 v2 = ByteSlice.unpackLE 8 v1 ++ ByteSlice.unpackLE 8 v2 := by
  match D, hD with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [], _ => rfl

/-- The 56 bytes of a Poly1305 state: pad words, then `r` and `h` limbs. -/
def polyBytes (w0 w1 w2 w3 : BitVec 32) (l : PolyLimbs) : Bytes :=
  word32Bytes w0 ++ word32Bytes w1 ++ word32Bytes w2 ++ word32Bytes w3 ++
  word32Bytes l.r0 ++ word32Bytes l.r1 ++ word32Bytes l.r2 ++ word32Bytes l.r3 ++ word32Bytes l.r4 ++
  word32Bytes l.h0 ++ word32Bytes l.h1 ++ word32Bytes l.h2 ++ word32Bytes l.h3 ++ word32Bytes l.h4

theorem polyBytes_length (w0 w1 w2 w3 : BitVec 32) (l : PolyLimbs) : (polyBytes w0 w1 w2 w3 l).length = 56 := rfl

theorem polyState_bytes (st : BitVec 64) (w0 w1 w2 w3 : BitVec 32) (l : PolyLimbs) :
    (words4At st w0 w1 w2 w3 ∗ polyLimbsAt st l) = (st ↦ₛ polyBytes w0 w1 w2 w3 l) := by
  have hl : ∀ w : BitVec 32, (word32Bytes w).length = 4 := fun _ => rfl
  simp only [polyBytes, List.append_assoc, pointsToBytes_append, hl, List.length_append]
  simp only [words4At, polyLimbsAt, limbsAt, pointsTo32_eq_word32Bytes]
  apply sepProp_ext <;> sep_entail

theorem bytes16_words (p : BitVec 64) (X : Bytes) (hX : X.length = 16) :
    (p ↦ₛ X) = words4At p (word32At X 0) (word32At X 4) (word32At X 8) (word32At X 12) := by
  match X, hX with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: [], _ =>
    simp only [words4At, word32At, byteAt, List.getD_cons_succ, List.getD_cons_zero,
      ← pointsToBytes4_eq_pointsTo32, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    apply sepProp_ext <;> sep_entail


theorem words4_natLe (t0 t1 t2 t3 : BitVec 32) :
    word32Bytes t0 ++ word32Bytes t1 ++ word32Bytes t2 ++ word32Bytes t3 =
      natLe 16 (words4Val t0 t1 t2 t3) := by
  have b0 := t0.isLt; have b1 := t1.isLt; have b2 := t2.isLt; have b3 := t3.isLt
  simp only [word32Bytes, natLe, words4Val, List.cons_append, List.nil_append]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega

theorem copy56 (D pB : List (BitVec 8)) (hD : D.length = 64) (hp : pB.length = 56) :
    ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 D 48 (ByteSlice.readLE pB 48 8)) 0 (ByteSlice.readLE pB 0 8)) 8
      (ByteSlice.readLE pB 8 8)) 16 (ByteSlice.readLE pB 16 8)) 24 (ByteSlice.readLE pB 24 8)) 32
      (ByteSlice.readLE pB 32 8)) 40 (ByteSlice.readLE pB 40 8) = pB ++ D.drop 56 := by
  rw [← ByteSlice.copySet_false D pB]
  simp (disch := omega) only [ByteSlice.write64_copySet_readLE]
  apply ByteSlice.ext_getD (by simp; omega)
  intro i hi
  simp only [ByteSlice.copySet_length] at hi
  rw [ByteSlice.getD_copySet]
  by_cases h56 : i < 56
  · have hc : ((false || decide (48 ≤ i) && decide (i < 48 + 8) || decide (0 ≤ i) && decide (i < 0 + 8) ||
        decide (8 ≤ i) && decide (i < 8 + 8) || decide (16 ≤ i) && decide (i < 16 + 8) ||
        decide (24 ≤ i) && decide (i < 24 + 8) || decide (32 ≤ i) && decide (i < 32 + 8) ||
        decide (40 ≤ i) && decide (i < 40 + 8)) && decide (i < D.length)) = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, false_or]
      omega
    rw [if_pos hc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  · have hc : ((false || decide (48 ≤ i) && decide (i < 48 + 8) || decide (0 ≤ i) && decide (i < 0 + 8) ||
        decide (8 ≤ i) && decide (i < 8 + 8) || decide (16 ≤ i) && decide (i < 16 + 8) ||
        decide (24 ≤ i) && decide (i < 24 + 8) || decide (32 ≤ i) && decide (i < 32 + 8) ||
        decide (40 ≤ i) && decide (i < 40 + 8)) && decide (i < D.length)) = false := by
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.false_eq_true,
        true_and, Bool.or_false, Bool.false_or]
      omega
    rw [if_neg (by rw [hc]; exact Bool.false_ne_true), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_drop, hp]
    rw [ByteSlice.copySet_false, show 56 + (i - 56) = i by omega]


theorem zero_chain8 (mk : List (BitVec 8)) (h : mk.length = 32) :
    ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 mk 0 0#8) 1 0#8) 2 0#8) 3 0#8) 4 0#8) 5 0#8) 6 0#8) 7 0#8) 8 0#8) 9 0#8) 10 0#8) 11 0#8) 12 0#8) 13 0#8) 14 0#8) 15 0#8) 16 0#8) 17 0#8) 18 0#8) 19 0#8) 20 0#8) 21 0#8) 22 0#8) 23 0#8) 24 0#8) 25 0#8) 26 0#8) 27 0#8) 28 0#8) 29 0#8) 30 0#8) 31 0#8 = List.replicate 32 0#8 := by
  rw [← ByteSlice.fillPrefix_zero mk 0#8]
  simp (disch := omega) only [ByteSlice.write8_fillPrefix]
  exact ByteSlice.fillPrefix_full h

theorem cipher129_entails (c : BitVec 64) (s b : Spec.State) (v : BitVec 8) :
    (stateAt c s ∗ stateAt (c + 64#64) b ∗ ((c + 128#64) ↦₈ v)) ⊢ memRegion c 129 := by
  have hs : s.bytes.length = 64 := by simp [Spec.State.bytes, word32Bytes]
  have hb : b.bytes.length = 64 := by simp [Spec.State.bytes, word32Bytes]
  rw [stateAt_eq_bytes, stateAt_eq_bytes, ← pointsToBytes_singleton]
  have e : (c ↦ₛ (s.bytes ++ (b.bytes ++ [v]))) =
      (c ↦ₛ s.bytes) ∗ ((c + 64#64) ↦ₛ b.bytes) ∗ ((c + 128#64) ↦ₛ [v]) := by
    rw [pointsToBytes_append, pointsToBytes_append, hs, hb, BitVec.add_assoc]; rfl
  rw [← e]
  have hl : (s.bytes ++ (b.bytes ++ [v])).length = 129 := by simp [hs, hb]
  exact hl ▸ pointsToBytes_entails_memRegion c _

theorem words4_bytes (p : BitVec 64) (t0 t1 t2 t3 : BitVec 32) :
    words4At p t0 t1 t2 t3 = (p ↦ₛ (word32Bytes t0 ++ word32Bytes t1 ++ word32Bytes t2 ++ word32Bytes t3)) := by
  have hl : ∀ w : BitVec 32, (word32Bytes w).length = 4 := fun _ => rfl
  simp only [words4At, List.append_assoc, pointsToBytes_append, hl, pointsTo32_eq_word32Bytes]
  apply sepProp_ext <;> sep_entail

end ChaChaPoly.Proofs
