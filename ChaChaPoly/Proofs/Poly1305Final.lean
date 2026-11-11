module

public import ChaChaPoly.Proofs.Code
public import ChaChaPoly.Proofs.Poly1305Math

/-!
# `Poly1305::finalize` (block 8)

`fin*` are the expressions the compiled `finalize` computes, named after the steps of the Rust
source: full carry (`T*`, `N*`), the trial subtraction of `p = 2^130 - 5` (`G*`), the
constant-time select (`NM`, `MK`, `F*`), repacking into four 32-bit words (`O*`) and the
addition of the pad `s` with carries (`S*`). `finalize_ok` proves the machine code writes
`finOut0 … finOut3`; the arithmetic meaning is established in `Poly1305FinalMath.lean`.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
arm64_proof_prelude

section Model
variable (h0 h1 h2 h3 h4 p0 p1 p2 p3 : BitVec 32)

def finT2 : BitVec 32 := h2 + h1 >>> 26
def finT3 : BitVec 32 := h3 + finT2 h1 h2 >>> 26
def finT4 : BitVec 32 := h4 + finT3 h1 h2 h3 >>> 26
def finN1 : BitVec 32 := BitVec.truncate 32 (BitVec.zeroExtend 64 h1 &&& 67108863#64)
def finN2 : BitVec 32 := BitVec.truncate 32 (BitVec.zeroExtend 64 (finT2 h1 h2) &&& 67108863#64)
def finN3 : BitVec 32 := BitVec.truncate 32 (BitVec.zeroExtend 64 (finT3 h1 h2 h3) &&& 67108863#64)
def finN4 : BitVec 32 := BitVec.truncate 32 (BitVec.zeroExtend 64 (finT4 h1 h2 h3 h4) &&& 67108863#64)
def finC4 : BitVec 32 := BitVec.truncate 32 (BitVec.zeroExtend 64 (finT4 h1 h2 h3 h4) >>> 26)
def finT0 : BitVec 32 := finC4 h1 h2 h3 h4 + finC4 h1 h2 h3 h4 <<< 2 + h0
def finN0 : BitVec 32 := BitVec.truncate 32 (BitVec.zeroExtend 64 (finT0 h0 h1 h2 h3 h4) &&& 67108863#64)
def finM1 : BitVec 32 := finN1 h1 + finT0 h0 h1 h2 h3 h4 >>> 26
def finG0 : BitVec 32 := finN0 h0 h1 h2 h3 h4 + 5#32
def finG1 : BitVec 32 := finM1 h0 h1 h2 h3 h4 + finG0 h0 h1 h2 h3 h4 >>> 26
def finG2 : BitVec 32 := finN2 h1 h2 + finG1 h0 h1 h2 h3 h4 >>> 26
def finG3 : BitVec 32 := finN3 h1 h2 h3 + finG2 h0 h1 h2 h3 h4 >>> 26
def finG4S : BitVec 32 := finN4 h1 h2 h3 h4 + finG3 h0 h1 h2 h3 h4 >>> 26
def finG4 : BitVec 32 := finG4S h0 h1 h2 h3 h4 + 4227858432#32
def finNM : BitVec 32 := (finG4 h0 h1 h2 h3 h4).sshiftRight 31
def finMK : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (finG4 h0 h1 h2 h3 h4) >>> 31) - 1#32
def finMKM : BitVec 64 := BitVec.zeroExtend 64 (finMK h0 h1 h2 h3 h4) &&& 67108863#64
def finF0 : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (finNM h0 h1 h2 h3 h4) &&&
      (BitVec.zeroExtend 64 (finT0 h0 h1 h2 h3 h4) &&& 67108863#64) |||
    BitVec.zeroExtend 64 (BitVec.truncate 32 (finMKM h0 h1 h2 h3 h4 &&&
      BitVec.zeroExtend 64 (finG0 h0 h1 h2 h3 h4))))
def finF1 : BitVec 32 :=
  BitVec.truncate 32 (finMKM h0 h1 h2 h3 h4 &&& BitVec.zeroExtend 64 (finG1 h0 h1 h2 h3 h4)) |||
    finNM h0 h1 h2 h3 h4 &&& finM1 h0 h1 h2 h3 h4
def finF2 : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (finMKM h0 h1 h2 h3 h4 &&&
      BitVec.zeroExtend 64 (finG2 h0 h1 h2 h3 h4))) |||
    BitVec.zeroExtend 64 (finNM h0 h1 h2 h3 h4) &&&
      (BitVec.zeroExtend 64 (finT2 h1 h2) &&& 67108863#64))
def finF3 : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (finMKM h0 h1 h2 h3 h4 &&&
      BitVec.zeroExtend 64 (finG3 h0 h1 h2 h3 h4))) |||
    BitVec.zeroExtend 64 (finNM h0 h1 h2 h3 h4) &&&
      (BitVec.zeroExtend 64 (finT3 h1 h2 h3) &&& 67108863#64))
def finF4 : BitVec 32 :=
  finMK h0 h1 h2 h3 h4 &&& finG4S h0 h1 h2 h3 h4 ||| finNM h0 h1 h2 h3 h4 &&& finT4 h1 h2 h3 h4
def finO0 : BitVec 32 := finF0 h0 h1 h2 h3 h4 ||| finF1 h0 h1 h2 h3 h4 <<< 26
def finO1 : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (finF1 h0 h1 h2 h3 h4) >>> 6) |||
    finF2 h0 h1 h2 h3 h4 <<< 20
def finO2 : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (finF2 h0 h1 h2 h3 h4) >>> 12) |||
    finF3 h0 h1 h2 h3 h4 <<< 14
def finO3 : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (finF3 h0 h1 h2 h3 h4) >>> 18) |||
    finF4 h0 h1 h2 h3 h4 <<< 8
def finOut0 : BitVec 32 := finO0 h0 h1 h2 h3 h4 + p0
def finS1 : BitVec 64 :=
  BitVec.zeroExtend 64 (finO1 h0 h1 h2 h3 h4) + BitVec.zeroExtend 64 p1 +
    if (AddWithCarry32 (finO0 h0 h1 h2 h3 h4) p0 false).snd.c = true then 1#64 else 0#64
def finOut1 : BitVec 32 := BitVec.truncate 32 (finS1 h0 h1 h2 h3 h4 p0 p1)
def finS2 : BitVec 64 :=
  BitVec.zeroExtend 64 (finO2 h0 h1 h2 h3 h4) + BitVec.zeroExtend 64 p2 +
    finS1 h0 h1 h2 h3 h4 p0 p1 >>> 32
def finOut2 : BitVec 32 := BitVec.truncate 32 (finS2 h0 h1 h2 h3 h4 p0 p1 p2)
def finOut3 : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (finO3 h0 h1 h2 h3 h4 + p3) +
    finS2 h0 h1 h2 h3 h4 p0 p1 p2 >>> 32)

end Model

/-- Four little-endian 32-bit words at `p`. -/
def words4At (p : BitVec 64) (w0 w1 w2 w3 : BitVec 32) : SepProp :=
  (p ↦₃₂ w0) ∗ ((p + 4#64) ↦₃₂ w1) ∗ ((p + 8#64) ↦₃₂ w2) ∗ ((p + 12#64) ↦₃₂ w3)

structure PolyFinalGhost where
  st : BitVec 64
  out : BitVec 64
  (p0 p1 p2 p3 h0 h1 h2 h3 h4 o0 o1 o2 o3 : BitVec 32)

def polyFinalSpec : Spec PolyFinalGhost where
  pre := fun g s0 =>
    ⌜s0.readReg64 .x0 = g.st ∧ s0.readReg64 .x8 = g.out⌝ ∗
    words4At g.st g.p0 g.p1 g.p2 g.p3 ∗ limbsAt (g.st + 36#64) g.h0 g.h1 g.h2 g.h3 g.h4 ∗
    words4At g.out g.o0 g.o1 g.o2 g.o3
  post := fun g _ _ =>
    words4At g.st g.p0 g.p1 g.p2 g.p3 ∗ limbsAt (g.st + 36#64) g.h0 g.h1 g.h2 g.h3 g.h4 ∗
    words4At g.out (finOut0 g.h0 g.h1 g.h2 g.h3 g.h4 g.p0)
      (finOut1 g.h0 g.h1 g.h2 g.h3 g.h4 g.p0 g.p1)
      (finOut2 g.h0 g.h1 g.h2 g.h3 g.h4 g.p0 g.p1 g.p2)
      (finOut3 g.h0 g.h1 g.h2 g.h3 g.h4 g.p0 g.p1 g.p2 g.p3)

theorem polyFinal_ok [CpPlacement] :
    subroutine_ok cpProg8r cpPl8.base (chachapolyLib.withCodeLoaded cpMpl polyFinalSpec) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, polyFinalSpec, limbsAt, words4At]
  wp_entry "<poly1305::Poly1305 as universal_hash::UniversalHash>::finalize" g s0
  obtain ⟨st, out, p0, p1, p2, p3, h0, h1, h2, h3, h4, o0, o1, o2, o3⟩ := g
  simp only at *
  wp_steps
  -- Fold the computed words back into the named model expressions (definitional).
  refine SepWP.weaken_pre (P' :=
    (st ↦₃₂ p0) ∗ ((st + 4#64) ↦₃₂ p1) ∗ ((st + 8#64) ↦₃₂ p2) ∗ ((st + 12#64) ↦₃₂ p3) ∗
    ((st + 36#64) ↦₃₂ h0) ∗ ((st + 40#64) ↦₃₂ h1) ∗ ((st + 44#64) ↦₃₂ h2) ∗
    ((st + 48#64) ↦₃₂ h3) ∗ ((st + 52#64) ↦₃₂ h4) ∗
    (out ↦₃₂ finOut0 h0 h1 h2 h3 h4 p0) ∗ ((out + 4#64) ↦₃₂ finOut1 h0 h1 h2 h3 h4 p0 p1) ∗
    ((out + 8#64) ↦₃₂ finOut2 h0 h1 h2 h3 h4 p0 p1 p2) ∗
    ((out + 12#64) ↦₃₂ finOut3 h0 h1 h2 h3 h4 p0 p1 p2 p3)) (Entails.refl _) ?_
  wp_done

end ChaChaPoly.Proofs
