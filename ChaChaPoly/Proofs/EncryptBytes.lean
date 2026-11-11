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

end ChaChaPoly.Proofs
