module

public import ChaChaPoly.Proofs.Code
public import ChaChaPoly.Proofs.Poly1305Block

/-!
# `<Poly1305 as KeyInit>::new` (block 10)

The compiled `new` reads the 32-byte one-time key at `x0` and writes the 56-byte state at `x8`:
the pad (key bytes 16..31) at offset 0, the clamped multiplier `r` as five 26-bit limbs at
offset 16, and a zero accumulator at offset 36. `polyNew_ok` proves the machine code computes
the expressions `newL0 … newL4`; `Poly1305NewMath.lean` relates them to RFC 8439's `clamp`.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
arm64_proof_prelude

section Model
variable (kb : Bytes)

/-- The 32-bit little-endian word of `kb` at byte offset `o`. -/
def kw (o : Nat) : BitVec 32 := pack32 (kb.getD o 0) (kb.getD (o + 1) 0) (kb.getD (o + 2) 0) (kb.getD (o + 3) 0)

def newL0 : BitVec 32 := BitVec.truncate 32 (BitVec.zeroExtend 64 (kw kb 0) &&& 67108863#64)
def newL1 : BitVec 32 := BitVec.truncate 32 (67108611#64 &&& BitVec.zeroExtend 64 (kw kb 3) >>> 2)
def newL2 : BitVec 32 := BitVec.truncate 32 (67092735#64 &&& BitVec.zeroExtend 64 (kw kb 6) >>> 4)
def newL3 : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (kw kb 9) >>> 6)) &&&
    4293935103#64)
def newL4 : BitVec 32 := BitVec.truncate 32 (BitVec.zeroExtend 64 (kw kb 12) >>> 8 &&& 1048575#64)

end Model

structure PolyNewGhost where
  k : BitVec 64
  out : BitVec 64
  kb : Bytes
  (a0 a1 a5 a6 : BitVec 64)
  (c0 c1 c2 c3 c4 c7 : BitVec 32)

/-- The output region as the cells the code stores to. -/
def newOutCells (out a0 a1 : BitVec 64) (c0 c1 c2 c3 c4 : BitVec 32) (a5 a6 : BitVec 64)
    (c7 : BitVec 32) : SepProp :=
  (out ↦₆₄ a0) ∗ ((out + 8#64) ↦₆₄ a1) ∗
  ((out + 16#64) ↦₃₂ c0) ∗ ((out + 20#64) ↦₃₂ c1) ∗ ((out + 24#64) ↦₃₂ c2) ∗
  ((out + 28#64) ↦₃₂ c3) ∗ ((out + 32#64) ↦₃₂ c4) ∗
  ((out + 36#64) ↦₆₄ a5) ∗ ((out + 44#64) ↦₆₄ a6) ∗ ((out + 52#64) ↦₃₂ c7)

def polyNewSpec : Spec PolyNewGhost where
  pre := fun g s0 =>
    ⌜s0.readReg64 .x0 = g.k ∧ s0.readReg64 .x8 = g.out ∧ g.kb.length = 32⌝ ∗
    (g.k ↦ₛ g.kb) ∗ newOutCells g.out g.a0 g.a1 g.c0 g.c1 g.c2 g.c3 g.c4 g.a5 g.a6 g.c7
  post := fun g _ _ =>
    (g.k ↦ₛ g.kb) ∗
    newOutCells g.out (ByteSlice.readLE g.kb 16 8) (ByteSlice.readLE g.kb 24 8)
      (newL0 g.kb) (newL1 g.kb) (newL2 g.kb) (newL3 g.kb) (newL4 g.kb) 0#64 0#64 0#32

theorem polyNew_ok [CpPlacement] :
    subroutine_ok cpProg10r cpPl10.base (chachapolyLib.withCodeLoaded cpMpl polyNewSpec) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, polyNewSpec, newOutCells, newL0, newL1, newL2,
    newL3, newL4, kw]
  wp_entry "<poly1305::Poly1305 as crypto_common::KeyInit>::new" g s0
  obtain ⟨k, out, kb, a0, a1, a5, a6, c0, c1, c2, c3, c4, c7⟩ := g
  simp only at *
  wp_steps
  wp_done

end ChaChaPoly.Proofs
