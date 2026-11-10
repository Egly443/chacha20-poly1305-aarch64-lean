module

public import ProofLib
public import ChaChaPoly.Spec.Contracts

/-!
# Poly1305 in five 26-bit limbs: the arithmetic behind `State::compute_block`

`cbH0 … cbH4` are the 32/64-bit expressions the machine code of RustCrypto's
`poly1305::backend::soft::State::compute_block` computes (in the operand order of the compiled
code). `cb_correct` shows that, on limbs within the representation bounds, they compute
`(h + m) * r mod 2^130 - 5` and re-establish the bounds.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace ChaChaPoly.Proofs

open ChaChaPoly.Spec Arm64 ProofLib

/-! ## Width bookkeeping -/

theorem toNat_times5 (r : BitVec 32) (h : r.toNat < 2 ^ 26) : (r + r <<< 2).toNat = 5 * r.toNat := by
  bv_omega

theorem toNat_zx_mul (a b : BitVec 32) :
    (BitVec.zeroExtend 64 a * BitVec.zeroExtend 64 b).toNat = a.toNat * b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have : a.toNat * b.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by decide)
  simp only [BitVec.toNat_mul, BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt this]

theorem toNat_carry (d : BitVec 64) (h : d.toNat < 2 ^ 58) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (d >>> 26))).toNat = d.toNat / 2 ^ 26 := by
  bv_omega

theorem toNat_carry32 (d : BitVec 64) (h : d.toNat < 2 ^ 58) :
    (BitVec.truncate 32 (d >>> 26)).toNat = d.toNat / 2 ^ 26 := by
  bv_omega

theorem toNat_mask26 (d : BitVec 64) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 d) &&& 67108863#64)).toNat =
      d.toNat % 2 ^ 26 := by
  have h : (67108863 : Nat) = 2 ^ 26 - 1 := by decide
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_and,
    BitVec.toNat_ofNat]
  rw [show 67108863 % 2 ^ 64 = 2 ^ 26 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_mask26' (x : BitVec 32) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 x &&& 67108863#64)).toNat = x.toNat % 2 ^ 26 := by
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_and,
    BitVec.toNat_ofNat]
  rw [show 67108863 % 2 ^ 64 = 2 ^ 26 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-! ## The limb product -/

theorem limb_mul_identity (A0 A1 A2 A3 A4 R0 R1 R2 R3 R4 : Nat) :
    limbVal A0 A1 A2 A3 A4 * limbVal R0 R1 R2 R3 R4
      + 5 * (A1 * R4 + A2 * R3 + A3 * R2 + A4 * R1 + 2 ^ 26 * (A2 * R4 + A3 * R3 + A4 * R2)
          + 2 ^ 52 * (A3 * R4 + A4 * R3) + 2 ^ 78 * (A4 * R4))
    = (A0 * R0 + 5 * (A1 * R4) + 5 * (A2 * R3) + 5 * (A3 * R2) + 5 * (A4 * R1))
      + 2 ^ 26 * (A0 * R1 + A1 * R0 + 5 * (A2 * R4) + 5 * (A3 * R3) + 5 * (A4 * R2))
      + 2 ^ 52 * (A0 * R2 + A1 * R1 + A2 * R0 + 5 * (A3 * R4) + 5 * (A4 * R3))
      + 2 ^ 78 * (A0 * R3 + A1 * R2 + A2 * R1 + A3 * R0 + 5 * (A4 * R4))
      + 2 ^ 104 * (A0 * R4 + A1 * R3 + A2 * R2 + A3 * R1 + A4 * R0)
      + 2 ^ 130 * (A1 * R4 + A2 * R3 + A3 * R2 + A4 * R1 + 2 ^ 26 * (A2 * R4 + A3 * R3 + A4 * R2)
          + 2 ^ 52 * (A3 * R4 + A4 * R3) + 2 ^ 78 * (A4 * R4)) := by
  simp only [limbVal]
  grind

/-- One multiply-and-reduce step on natural-number limbs: no intermediate overflows 58 bits,
    the final carry times five fits 32 bits, the result limbs are within the representation
    bounds, and the result is congruent to the product modulo `2^130 - 5`. -/
theorem cb_core (R0 R1 R2 R3 R4 A0 A1 A2 A3 A4 : Nat)
    (hR0 : R0 < 2 ^ 26) (hR1 : R1 < 2 ^ 26) (hR2 : R2 < 2 ^ 26) (hR3 : R3 < 2 ^ 26) (hR4 : R4 < 2 ^ 26)
    (hA0 : A0 < 2 ^ 27 + 64) (hA1 : A1 < 2 ^ 27 + 64) (hA2 : A2 < 2 ^ 27 + 64) (hA3 : A3 < 2 ^ 27 + 64) (hA4 : A4 < 2 ^ 27 + 64)
    (D0 D1 D2 D3 D4 : Nat)
    (hD0 : D0 = A0 * R0 + 5 * (A1 * R4) + 5 * (A2 * R3) + 5 * (A3 * R2) + 5 * (A4 * R1))
    (hD1 : D1 = A0 * R1 + A1 * R0 + 5 * (A2 * R4) + 5 * (A3 * R3) + 5 * (A4 * R2) + D0 / 2 ^ 26)
    (hD2 : D2 = A0 * R2 + A1 * R1 + A2 * R0 + 5 * (A3 * R4) + 5 * (A4 * R3) + D1 / 2 ^ 26)
    (hD3 : D3 = A0 * R3 + A1 * R2 + A2 * R1 + A3 * R0 + 5 * (A4 * R4) + D2 / 2 ^ 26)
    (hD4 : D4 = A0 * R4 + A1 * R3 + A2 * R2 + A3 * R1 + A4 * R0 + D3 / 2 ^ 26)
    (T0 : Nat) (hT0 : T0 = D4 / 2 ^ 26 + 4 * (D4 / 2 ^ 26) + D0 % 2 ^ 26) :
    (D0 < 2 ^ 58 ∧ D1 < 2 ^ 58 ∧ D2 < 2 ^ 58 ∧ D3 < 2 ^ 58 ∧ D4 < 2 ^ 58 ∧ T0 < 2 ^ 32) ∧
    T0 / 2 ^ 26 < 64 ∧
    limbVal (T0 % 2 ^ 26) (D1 % 2 ^ 26 + T0 / 2 ^ 26) (D2 % 2 ^ 26) (D3 % 2 ^ 26) (D4 % 2 ^ 26) % p1305 =
      limbVal A0 A1 A2 A3 A4 * limbVal R0 R1 R2 R3 R4 % p1305 := by
  have hpoly := limb_mul_identity A0 A1 A2 A3 A4 R0 R1 R2 R3 R4
  have b00 : A0 * R0 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b01 : A0 * R1 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b02 : A0 * R2 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b03 : A0 * R3 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b04 : A0 * R4 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b10 : A1 * R0 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b11 : A1 * R1 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b12 : A1 * R2 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b13 : A1 * R3 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b14 : A1 * R4 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b20 : A2 * R0 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b21 : A2 * R1 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b22 : A2 * R2 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b23 : A2 * R3 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b24 : A2 * R4 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b30 : A3 * R0 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b31 : A3 * R1 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b32 : A3 * R2 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b33 : A3 * R3 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b34 : A3 * R4 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b40 : A4 * R0 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b41 : A4 * R1 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b42 : A4 * R2 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b43 : A4 * R3 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b44 : A4 * R4 ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  generalize limbVal A0 A1 A2 A3 A4 * limbVal R0 R1 R2 R3 R4 = V at *
  generalize A0 * R0 = m00 at *
  generalize A0 * R1 = m01 at *
  generalize A0 * R2 = m02 at *
  generalize A0 * R3 = m03 at *
  generalize A0 * R4 = m04 at *
  generalize A1 * R0 = m10 at *
  generalize A1 * R1 = m11 at *
  generalize A1 * R2 = m12 at *
  generalize A1 * R3 = m13 at *
  generalize A1 * R4 = m14 at *
  generalize A2 * R0 = m20 at *
  generalize A2 * R1 = m21 at *
  generalize A2 * R2 = m22 at *
  generalize A2 * R3 = m23 at *
  generalize A2 * R4 = m24 at *
  generalize A3 * R0 = m30 at *
  generalize A3 * R1 = m31 at *
  generalize A3 * R2 = m32 at *
  generalize A3 * R3 = m33 at *
  generalize A3 * R4 = m34 at *
  generalize A4 * R0 = m40 at *
  generalize A4 * R1 = m41 at *
  generalize A4 * R2 = m42 at *
  generalize A4 * R3 = m43 at *
  generalize A4 * R4 = m44 at *
  refine ⟨by omega, by omega, ?_⟩
  have key : limbVal (T0 % 2 ^ 26) (D1 % 2 ^ 26 + T0 / 2 ^ 26) (D2 % 2 ^ 26) (D3 % 2 ^ 26) (D4 % 2 ^ 26)
      + p1305 * (D4 / 2 ^ 26 + (m14 + m23 + m32 + m41 + 2 ^ 26 * (m24 + m33 + m42)
          + 2 ^ 52 * (m34 + m43) + 2 ^ 78 * m44)) = V := by
    simp only [limbVal, p1305]
    omega
  rw [← key, Nat.add_mul_mod_self_left]

/-! ## The machine's expressions -/

/-- `5 * r` as the code computes it. -/
def cbS (r : BitVec 32) : BitVec 32 := r + r <<< 2

def cbD0 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 64 :=
  BitVec.zeroExtend 64 r0 * BitVec.zeroExtend 64 a0 + BitVec.zeroExtend 64 a1 * BitVec.zeroExtend 64 (cbS r4) + BitVec.zeroExtend 64 a2 * BitVec.zeroExtend 64 (cbS r3) + BitVec.zeroExtend 64 a3 * BitVec.zeroExtend 64 (cbS r2) + BitVec.zeroExtend 64 a4 * BitVec.zeroExtend 64 (cbS r1)

def cbD1 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 64 :=
  BitVec.zeroExtend 64 r1 * BitVec.zeroExtend 64 a0 + BitVec.zeroExtend 64 r0 * BitVec.zeroExtend 64 a1 + BitVec.zeroExtend 64 a2 * BitVec.zeroExtend 64 (cbS r4) + BitVec.zeroExtend 64 a3 * BitVec.zeroExtend 64 (cbS r3) + BitVec.zeroExtend 64 a4 * BitVec.zeroExtend 64 (cbS r2) +
    BitVec.zeroExtend 64 (BitVec.truncate 32 (cbD0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 >>> 26))

def cbD2 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 64 :=
  BitVec.zeroExtend 64 r2 * BitVec.zeroExtend 64 a0 + BitVec.zeroExtend 64 r1 * BitVec.zeroExtend 64 a1 + BitVec.zeroExtend 64 r0 * BitVec.zeroExtend 64 a2 + BitVec.zeroExtend 64 a3 * BitVec.zeroExtend 64 (cbS r4) + BitVec.zeroExtend 64 a4 * BitVec.zeroExtend 64 (cbS r3) +
    BitVec.zeroExtend 64 (BitVec.truncate 32 (cbD1 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 >>> 26))

def cbD3 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 64 :=
  BitVec.zeroExtend 64 r3 * BitVec.zeroExtend 64 a0 + BitVec.zeroExtend 64 r2 * BitVec.zeroExtend 64 a1 + BitVec.zeroExtend 64 r1 * BitVec.zeroExtend 64 a2 + BitVec.zeroExtend 64 r0 * BitVec.zeroExtend 64 a3 + BitVec.zeroExtend 64 a4 * BitVec.zeroExtend 64 (cbS r4) +
    BitVec.zeroExtend 64 (BitVec.truncate 32 (cbD2 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 >>> 26))

def cbD4 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 64 :=
  BitVec.zeroExtend 64 r4 * BitVec.zeroExtend 64 a0 + BitVec.zeroExtend 64 r3 * BitVec.zeroExtend 64 a1 + BitVec.zeroExtend 64 r2 * BitVec.zeroExtend 64 a2 + BitVec.zeroExtend 64 r1 * BitVec.zeroExtend 64 a3 + BitVec.zeroExtend 64 r0 * BitVec.zeroExtend 64 a4 +
    BitVec.zeroExtend 64 (BitVec.truncate 32 (cbD3 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 >>> 26))

def cbT0 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 32 :=
  BitVec.truncate 32 (cbD4 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 >>> 26) + BitVec.truncate 32 (cbD4 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 >>> 26) <<< 2 +
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (cbD0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4)) &&& 67108863#64)

def cbH0 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (cbT0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4) &&& 67108863#64)
def cbH1 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (cbD1 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4)) &&& 67108863#64) +
    cbT0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 >>> 26
def cbH2 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (cbD2 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4)) &&& 67108863#64)
def cbH3 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (cbD3 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4)) &&& 67108863#64)
def cbH4 (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32) : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (cbD4 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4)) &&& 67108863#64)

/-- The machine's expressions compute one Poly1305 multiply-and-reduce step: for clamped-size
    `r` limbs (`< 2^26`) and message-added accumulator limbs `a` (`< 2^27 + 64`), the result limbs are
    within the representation bounds and their value is `a * r` modulo `2^130 - 5`. -/
theorem cb_correct (r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 : BitVec 32)
    (hr0 : r0.toNat < 2 ^ 26) (hr1 : r1.toNat < 2 ^ 26) (hr2 : r2.toNat < 2 ^ 26)
    (hr3 : r3.toNat < 2 ^ 26) (hr4 : r4.toNat < 2 ^ 26)
    (ha0 : a0.toNat < 2 ^ 27 + 64) (ha1 : a1.toNat < 2 ^ 27 + 64) (ha2 : a2.toNat < 2 ^ 27 + 64)
    (ha3 : a3.toNat < 2 ^ 27 + 64) (ha4 : a4.toNat < 2 ^ 27 + 64) :
    ((cbH0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat < 2 ^ 26 ∧ (cbH1 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat < 2 ^ 26 + 64 ∧
      (cbH2 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat < 2 ^ 26 ∧ (cbH3 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat < 2 ^ 26 ∧ (cbH4 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat < 2 ^ 26) ∧
    limbVal (cbH0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat (cbH1 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat (cbH2 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat (cbH3 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat
        (cbH4 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat % p1305 =
      limbVal a0.toNat a1.toNat a2.toNat a3.toNat a4.toNat *
        limbVal r0.toNat r1.toNat r2.toNat r3.toNat r4.toNat % p1305 := by
  have hS1 := toNat_times5 r1 hr1
  have hS2 := toNat_times5 r2 hr2
  have hS3 := toNat_times5 r3 hr3
  have hS4 := toNat_times5 r4 hr4
  have b00 : a0.toNat * r0.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b01 : a0.toNat * r1.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b02 : a0.toNat * r2.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b03 : a0.toNat * r3.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b04 : a0.toNat * r4.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b10 : a1.toNat * r0.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b11 : a1.toNat * r1.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b12 : a1.toNat * r2.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b13 : a1.toNat * r3.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b14 : a1.toNat * r4.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b20 : a2.toNat * r0.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b21 : a2.toNat * r1.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b22 : a2.toNat * r2.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b23 : a2.toNat * r3.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b24 : a2.toNat * r4.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b30 : a3.toNat * r0.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b31 : a3.toNat * r1.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b32 : a3.toNat * r2.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b33 : a3.toNat * r3.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b34 : a3.toNat * r4.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b40 : a4.toNat * r0.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b41 : a4.toNat * r1.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b42 : a4.toNat * r2.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b43 : a4.toNat * r3.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have b44 : a4.toNat * r4.toNat ≤ (2 ^ 27 + 63) * (2 ^ 26 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have c00 : r0.toNat * a0.toNat = a0.toNat * r0.toNat := Nat.mul_comm _ _
  have c01 : r1.toNat * a0.toNat = a0.toNat * r1.toNat := Nat.mul_comm _ _
  have c02 : r2.toNat * a0.toNat = a0.toNat * r2.toNat := Nat.mul_comm _ _
  have c03 : r3.toNat * a0.toNat = a0.toNat * r3.toNat := Nat.mul_comm _ _
  have c04 : r4.toNat * a0.toNat = a0.toNat * r4.toNat := Nat.mul_comm _ _
  have c10 : r0.toNat * a1.toNat = a1.toNat * r0.toNat := Nat.mul_comm _ _
  have c11 : r1.toNat * a1.toNat = a1.toNat * r1.toNat := Nat.mul_comm _ _
  have c12 : r2.toNat * a1.toNat = a1.toNat * r2.toNat := Nat.mul_comm _ _
  have c13 : r3.toNat * a1.toNat = a1.toNat * r3.toNat := Nat.mul_comm _ _
  have c14 : r4.toNat * a1.toNat = a1.toNat * r4.toNat := Nat.mul_comm _ _
  have c20 : r0.toNat * a2.toNat = a2.toNat * r0.toNat := Nat.mul_comm _ _
  have c21 : r1.toNat * a2.toNat = a2.toNat * r1.toNat := Nat.mul_comm _ _
  have c22 : r2.toNat * a2.toNat = a2.toNat * r2.toNat := Nat.mul_comm _ _
  have c23 : r3.toNat * a2.toNat = a2.toNat * r3.toNat := Nat.mul_comm _ _
  have c24 : r4.toNat * a2.toNat = a2.toNat * r4.toNat := Nat.mul_comm _ _
  have c30 : r0.toNat * a3.toNat = a3.toNat * r0.toNat := Nat.mul_comm _ _
  have c31 : r1.toNat * a3.toNat = a3.toNat * r1.toNat := Nat.mul_comm _ _
  have c32 : r2.toNat * a3.toNat = a3.toNat * r2.toNat := Nat.mul_comm _ _
  have c33 : r3.toNat * a3.toNat = a3.toNat * r3.toNat := Nat.mul_comm _ _
  have c34 : r4.toNat * a3.toNat = a3.toNat * r4.toNat := Nat.mul_comm _ _
  have c40 : r0.toNat * a4.toNat = a4.toNat * r0.toNat := Nat.mul_comm _ _
  have c41 : r1.toNat * a4.toNat = a4.toNat * r1.toNat := Nat.mul_comm _ _
  have c42 : r2.toNat * a4.toNat = a4.toNat * r2.toNat := Nat.mul_comm _ _
  have c43 : r3.toNat * a4.toNat = a4.toNat * r3.toNat := Nat.mul_comm _ _
  have c44 : r4.toNat * a4.toNat = a4.toNat * r4.toNat := Nat.mul_comm _ _
  have l11 : a1.toNat * (5 * r1.toNat) = 5 * (a1.toNat * r1.toNat) := Nat.mul_left_comm _ _ _
  have l12 : a1.toNat * (5 * r2.toNat) = 5 * (a1.toNat * r2.toNat) := Nat.mul_left_comm _ _ _
  have l13 : a1.toNat * (5 * r3.toNat) = 5 * (a1.toNat * r3.toNat) := Nat.mul_left_comm _ _ _
  have l14 : a1.toNat * (5 * r4.toNat) = 5 * (a1.toNat * r4.toNat) := Nat.mul_left_comm _ _ _
  have l21 : a2.toNat * (5 * r1.toNat) = 5 * (a2.toNat * r1.toNat) := Nat.mul_left_comm _ _ _
  have l22 : a2.toNat * (5 * r2.toNat) = 5 * (a2.toNat * r2.toNat) := Nat.mul_left_comm _ _ _
  have l23 : a2.toNat * (5 * r3.toNat) = 5 * (a2.toNat * r3.toNat) := Nat.mul_left_comm _ _ _
  have l24 : a2.toNat * (5 * r4.toNat) = 5 * (a2.toNat * r4.toNat) := Nat.mul_left_comm _ _ _
  have l31 : a3.toNat * (5 * r1.toNat) = 5 * (a3.toNat * r1.toNat) := Nat.mul_left_comm _ _ _
  have l32 : a3.toNat * (5 * r2.toNat) = 5 * (a3.toNat * r2.toNat) := Nat.mul_left_comm _ _ _
  have l33 : a3.toNat * (5 * r3.toNat) = 5 * (a3.toNat * r3.toNat) := Nat.mul_left_comm _ _ _
  have l34 : a3.toNat * (5 * r4.toNat) = 5 * (a3.toNat * r4.toNat) := Nat.mul_left_comm _ _ _
  have l41 : a4.toNat * (5 * r1.toNat) = 5 * (a4.toNat * r1.toNat) := Nat.mul_left_comm _ _ _
  have l42 : a4.toNat * (5 * r2.toNat) = 5 * (a4.toNat * r2.toNat) := Nat.mul_left_comm _ _ _
  have l43 : a4.toNat * (5 * r3.toNat) = 5 * (a4.toNat * r3.toNat) := Nat.mul_left_comm _ _ _
  have l44 : a4.toNat * (5 * r4.toNat) = 5 * (a4.toNat * r4.toNat) := Nat.mul_left_comm _ _ _
  obtain ⟨⟨hb0, hb1, hb2, hb3, hb4, hbT⟩, hT64, hval⟩ :=
    cb_core r0.toNat r1.toNat r2.toNat r3.toNat r4.toNat a0.toNat a1.toNat a2.toNat a3.toNat a4.toNat
      hr0 hr1 hr2 hr3 hr4 ha0 ha1 ha2 ha3 ha4 _ _ _ _ _ rfl rfl rfl rfl rfl _ rfl
  have hD0 : (cbD0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = a0.toNat * r0.toNat + 5 * (a1.toNat * r4.toNat) + 5 * (a2.toNat * r3.toNat) + 5 * (a3.toNat * r2.toNat) + 5 * (a4.toNat * r1.toNat) := by
    simp only [cbD0, cbS, BitVec.toNat_add, toNat_zx_mul, hS1, hS2, hS3, hS4]
    omega
  rw [← hD0] at hb0 hb1 hb2 hb3 hb4 hbT hT64 hval
  have hD1 : (cbD1 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = a0.toNat * r1.toNat + a1.toNat * r0.toNat + 5 * (a2.toNat * r4.toNat) + 5 * (a3.toNat * r3.toNat) + 5 * (a4.toNat * r2.toNat) + (cbD0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat / 2 ^ 26 := by
    simp only [cbD1, cbS, BitVec.toNat_add, toNat_zx_mul, hS1, hS2, hS3, hS4, toNat_carry _ hb0]
    omega
  rw [← hD1] at hb1 hb2 hb3 hb4 hbT hT64 hval
  have hD2 : (cbD2 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = a0.toNat * r2.toNat + a1.toNat * r1.toNat + a2.toNat * r0.toNat + 5 * (a3.toNat * r4.toNat) + 5 * (a4.toNat * r3.toNat) + (cbD1 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat / 2 ^ 26 := by
    simp only [cbD2, cbS, BitVec.toNat_add, toNat_zx_mul, hS1, hS2, hS3, hS4, toNat_carry _ hb1]
    omega
  rw [← hD2] at hb2 hb3 hb4 hbT hT64 hval
  have hD3 : (cbD3 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = a0.toNat * r3.toNat + a1.toNat * r2.toNat + a2.toNat * r1.toNat + a3.toNat * r0.toNat + 5 * (a4.toNat * r4.toNat) + (cbD2 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat / 2 ^ 26 := by
    simp only [cbD3, cbS, BitVec.toNat_add, toNat_zx_mul, hS1, hS2, hS3, hS4, toNat_carry _ hb2]
    omega
  rw [← hD3] at hb3 hb4 hbT hT64 hval
  have hD4 : (cbD4 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = a0.toNat * r4.toNat + a1.toNat * r3.toNat + a2.toNat * r2.toNat + a3.toNat * r1.toNat + a4.toNat * r0.toNat + (cbD3 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat / 2 ^ 26 := by
    simp only [cbD4, cbS, BitVec.toNat_add, toNat_zx_mul, hS1, hS2, hS3, hS4, toNat_carry _ hb3]
    omega
  rw [← hD4] at hb4 hbT hT64 hval
  have hT0 : (cbT0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = (cbD4 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat / 2 ^ 26 + 4 * ((cbD4 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat / 2 ^ 26) +
      (cbD0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat % 2 ^ 26 := by
    have hc := toNat_carry32 _ hb4
    have hm := toNat_mask26 (cbD0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4)
    simp only [cbT0, BitVec.toNat_add, BitVec.toNat_shiftLeft, hc, hm]
    omega
  rw [← hT0] at hbT hT64 hval
  have hH0 : (cbH0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = (cbT0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat % 2 ^ 26 := toNat_mask26' _
  have hH1 : (cbH1 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = (cbD1 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat % 2 ^ 26 + (cbT0 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat / 2 ^ 26 := by
    have hm := toNat_mask26 (cbD1 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4)
    simp only [cbH1, BitVec.toNat_add, BitVec.toNat_ushiftRight, hm, Nat.shiftRight_eq_div_pow]
    omega
  have hH2 : (cbH2 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = (cbD2 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat % 2 ^ 26 := toNat_mask26 _
  have hH3 : (cbH3 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = (cbD3 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat % 2 ^ 26 := toNat_mask26 _
  have hH4 : (cbH4 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat = (cbD4 r0 r1 r2 r3 r4 a0 a1 a2 a3 a4).toNat % 2 ^ 26 := toNat_mask26 _
  rw [hH0, hH1, hH2, hH3, hH4]
  exact ⟨by omega, hval⟩

/-! ## Adding a 16-byte block to the accumulator -/

def cbA0 (h0 : BitVec 32) (bs : Bytes) : BitVec 32 :=
  h0 + BitVec.truncate 32 (BitVec.zeroExtend 64 (pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)) &&& 67108863#64)
def cbA1 (h1 : BitVec 32) (bs : Bytes) : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (pack32 (bs.getD 3 0#8) (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8)) >>> 2 &&& 67108863#64) + h1
def cbA2 (h2 : BitVec 32) (bs : Bytes) : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 (pack32 (bs.getD 6 0#8) (bs.getD 7 0#8) (bs.getD 8 0#8) (bs.getD 9 0#8)) >>> 4 &&& 67108863#64) + h2
def cbA3 (h3 : BitVec 32) (bs : Bytes) : BitVec 32 :=
  h3 + (pack32 (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8)) >>> 6
def cbA4 (h4 : BitVec 32) (bs : Bytes) : BitVec 32 :=
  h4 + 16777216#32 + (pack32 (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8) (bs.getD 15 0#8)) >>> 8

theorem toNat_pack32 (b0 b1 b2 b3 : BitVec 8) :
    (pack32 b0 b1 b2 b3).toNat = b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
  have e0 := b0.isLt; have e1 := b1.isLt; have e2 := b2.isLt
  unfold pack32
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt e0, ← Nat.shiftLeft_add_eq_or_of_lt e1,
    ← Nat.shiftLeft_add_eq_or_of_lt e2]
  simp only [Nat.shiftLeft_eq]
  omega

theorem toNat_shr_mask26 (x : BitVec 32) (k : Nat) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 x >>> k &&& 67108863#64)).toNat =
      x.toNat / 2 ^ k % 2 ^ 26 := by
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_and,
    BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [show 67108863 % 2 ^ 64 = 2 ^ 26 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  have := x.isLt
  have h1 : x.toNat % 2 ^ 64 = x.toNat := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have h2 : x.toNat / 2 ^ k % 2 ^ 26 < 2 ^ 26 := Nat.mod_lt _ (by decide)
  omega

theorem toNat_a4 (h4 w : BitVec 32) (hh : h4.toNat < 2 ^ 26) :
    (h4 + 16777216#32 + w >>> 8).toNat = h4.toNat + 16777216 + w.toNat / 2 ^ 8 := by
  bv_omega

/-- Adding a full 16-byte block (with the `2^128` bit of RFC 8439 §2.5.1) to accumulator limbs
    within the representation bounds: no limb exceeds 27 bits, and the value is the sum. -/
theorem msg_correct (h0 h1 h2 h3 h4 : BitVec 32) (bs : Bytes) (hlen : bs.length = 16)
    (hh0 : h0.toNat < 2 ^ 26) (hh1 : h1.toNat < 2 ^ 26 + 64) (hh2 : h2.toNat < 2 ^ 26)
    (hh3 : h3.toNat < 2 ^ 26) (hh4 : h4.toNat < 2 ^ 26) :
    ((cbA0 h0 bs).toNat < 2 ^ 27 + 64 ∧ (cbA1 h1 bs).toNat < 2 ^ 27 + 64 ∧ (cbA2 h2 bs).toNat < 2 ^ 27 + 64 ∧
      (cbA3 h3 bs).toNat < 2 ^ 27 + 64 ∧ (cbA4 h4 bs).toNat < 2 ^ 27 + 64) ∧
    limbVal (cbA0 h0 bs).toNat (cbA1 h1 bs).toNat (cbA2 h2 bs).toNat (cbA3 h3 bs).toNat
        (cbA4 h4 bs).toNat =
      limbVal h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat + leNat (bs ++ [1]) := by
  match bs, hlen with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15], _ =>
    have e0 := b0.isLt; have e1 := b1.isLt; have e2 := b2.isLt; have e3 := b3.isLt
    have e4 := b4.isLt; have e5 := b5.isLt; have e6 := b6.isLt; have e7 := b7.isLt
    have e8 := b8.isLt; have e9 := b9.isLt; have e10 := b10.isLt; have e11 := b11.isLt
    have e12 := b12.isLt; have e13 := b13.isLt; have e14 := b14.isLt; have e15 := b15.isLt
    have hA0 : (cbA0 h0 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).toNat =
        h0.toNat + (pack32 b0 b1 b2 b3).toNat % 2 ^ 26 := by
      simp only [cbA0, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_add, toNat_mask26']
      omega
    have hA1 : (cbA1 h1 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).toNat =
        (pack32 b3 b4 b5 b6).toNat / 2 ^ 2 % 2 ^ 26 + h1.toNat := by
      simp only [cbA1, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_add, toNat_shr_mask26]
      omega
    have hA2 : (cbA2 h2 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).toNat =
        (pack32 b6 b7 b8 b9).toNat / 2 ^ 4 % 2 ^ 26 + h2.toNat := by
      simp only [cbA2, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_add, toNat_shr_mask26]
      omega
    have hA3 : (cbA3 h3 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).toNat =
        h3.toNat + (pack32 b9 b10 b11 b12).toNat / 2 ^ 6 := by
      have := (pack32 b9 b10 b11 b12).isLt
      simp only [cbA3, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_add,
        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    have hA4 : (cbA4 h4 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).toNat =
        h4.toNat + 16777216 + (pack32 b12 b13 b14 b15).toNat / 2 ^ 8 := by
      simp only [cbA4, List.getD_cons_zero, List.getD_cons_succ]
      exact toNat_a4 _ _ hh4
    rw [hA0, hA1, hA2, hA3, hA4]
    have hone : (1 : BitVec 8).toNat = 1 := by decide
    simp only [toNat_pack32, limbVal, leNat, List.cons_append, List.nil_append, hone]
    have m0 : (BitVec.toNat b0 + 256 * BitVec.toNat b1 + 65536 * BitVec.toNat b2 + 16777216 * BitVec.toNat b3) % 2 ^ 26 = BitVec.toNat b0 + 256 * BitVec.toNat b1 + 65536 * BitVec.toNat b2 + 16777216 * (BitVec.toNat b3 % 4) := by omega
    have m1 : (BitVec.toNat b3 + 256 * BitVec.toNat b4 + 65536 * BitVec.toNat b5 + 16777216 * BitVec.toNat b6) / 2 ^ 2 % 2 ^ 26 = BitVec.toNat b3 / 4 + 64 * BitVec.toNat b4 + 16384 * BitVec.toNat b5 + 4194304 * (BitVec.toNat b6 % 16) := by omega
    have m2 : (BitVec.toNat b6 + 256 * BitVec.toNat b7 + 65536 * BitVec.toNat b8 + 16777216 * BitVec.toNat b9) / 2 ^ 4 % 2 ^ 26 = BitVec.toNat b6 / 16 + 16 * BitVec.toNat b7 + 4096 * BitVec.toNat b8 + 1048576 * (BitVec.toNat b9 % 64) := by omega
    have m3 : (BitVec.toNat b9 + 256 * BitVec.toNat b10 + 65536 * BitVec.toNat b11 + 16777216 * BitVec.toNat b12) / 2 ^ 6 = BitVec.toNat b9 / 64 + 4 * BitVec.toNat b10 + 1024 * BitVec.toNat b11 + 262144 * BitVec.toNat b12 := by omega
    have m4 : (BitVec.toNat b12 + 256 * BitVec.toNat b13 + 65536 * BitVec.toNat b14 + 16777216 * BitVec.toNat b15) / 2 ^ 8 = BitVec.toNat b13 + 256 * BitVec.toNat b14 + 65536 * BitVec.toNat b15 := by omega
    rw [m0, m1, m2, m3, m4]
    clear m0 m1 m2 m3 m4 hA0 hA1 hA2 hA3 hA4
    have d3 : BitVec.toNat b3 = 4 * (BitVec.toNat b3 / 4) + BitVec.toNat b3 % 4 := by omega
    have u3 : BitVec.toNat b3 % 4 < 4 := Nat.mod_lt _ (by decide)
    generalize BitVec.toNat b3 / 4 = q3 at *
    generalize BitVec.toNat b3 % 4 = l3 at *
    have d6 : BitVec.toNat b6 = 16 * (BitVec.toNat b6 / 16) + BitVec.toNat b6 % 16 := by omega
    have u6 : BitVec.toNat b6 % 16 < 16 := Nat.mod_lt _ (by decide)
    generalize BitVec.toNat b6 / 16 = q6 at *
    generalize BitVec.toNat b6 % 16 = l6 at *
    have d9 : BitVec.toNat b9 = 64 * (BitVec.toNat b9 / 64) + BitVec.toNat b9 % 64 := by omega
    have u9 : BitVec.toNat b9 % 64 < 64 := Nat.mod_lt _ (by decide)
    generalize BitVec.toNat b9 / 64 = q9 at *
    generalize BitVec.toNat b9 % 64 = l9 at *
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega

end ChaChaPoly.Proofs
