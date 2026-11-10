module

public import ChaChaPoly.Proofs.Code
public import ProofLib.Hoare.Model
public import ProofLib.Hoare.SubroutineOk
public import ChaChaPoly.Proofs.Poly1305Math

/-!
# `poly1305::backend::soft::State::compute_block` (block 7)

Machine-code proof that the compiled `compute_block`, called with `partial = false`, replaces
the accumulator limbs `h` by the expressions `cbH0 … cbH4` of `Poly1305Math.lean` applied to the
message-added limbs `cbA0 … cbA4`. Together with `cb_correct` and `msg_correct` this is one
Poly1305 block step, `h ← (h + block + 2^128) * r mod 2^130 - 5`.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open ChaChaPoly ChaChaPoly.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
arm64_proof_prelude

/-- Ghost state of a `compute_block` call: state pointer, block pointer, block bytes, `r`, `h`. -/
structure PolyBlockGhost where
  st : BitVec 64
  blk : BitVec 64
  bs : Bytes
  (r0 r1 r2 r3 r4 h0 h1 h2 h3 h4 : BitVec 32)

def polyBlockSpec : Spec PolyBlockGhost where
  pre := fun g s0 =>
    ⌜s0.readReg64 .x0 = g.st ∧ s0.readReg64 .x1 = g.blk ∧ s0.readReg64 .x2 = 0#64 ∧
      g.bs.length = 16⌝ ∗
    (g.blk ↦ₛ g.bs) ∗ limbsAt (g.st + 16#64) g.r0 g.r1 g.r2 g.r3 g.r4 ∗
    limbsAt (g.st + 36#64) g.h0 g.h1 g.h2 g.h3 g.h4
  post := fun g _ _ =>
    (g.blk ↦ₛ g.bs) ∗ limbsAt (g.st + 16#64) g.r0 g.r1 g.r2 g.r3 g.r4 ∗
    limbsAt (g.st + 36#64)
      (cbH0 g.r0 g.r1 g.r2 g.r3 g.r4 (cbA0 g.h0 g.bs) (cbA1 g.h1 g.bs) (cbA2 g.h2 g.bs) (cbA3 g.h3 g.bs) (cbA4 g.h4 g.bs))
      (cbH1 g.r0 g.r1 g.r2 g.r3 g.r4 (cbA0 g.h0 g.bs) (cbA1 g.h1 g.bs) (cbA2 g.h2 g.bs) (cbA3 g.h3 g.bs) (cbA4 g.h4 g.bs))
      (cbH2 g.r0 g.r1 g.r2 g.r3 g.r4 (cbA0 g.h0 g.bs) (cbA1 g.h1 g.bs) (cbA2 g.h2 g.bs) (cbA3 g.h3 g.bs) (cbA4 g.h4 g.bs))
      (cbH3 g.r0 g.r1 g.r2 g.r3 g.r4 (cbA0 g.h0 g.bs) (cbA1 g.h1 g.bs) (cbA2 g.h2 g.bs) (cbA3 g.h3 g.bs) (cbA4 g.h4 g.bs))
      (cbH4 g.r0 g.r1 g.r2 g.r3 g.r4 (cbA0 g.h0 g.bs) (cbA1 g.h1 g.bs) (cbA2 g.h2 g.bs) (cbA3 g.h3 g.bs) (cbA4 g.h4 g.bs))

theorem polyBlock_ok [CpPlacement] :
    subroutine_ok cpProg7r cpPl7.base (chachapolyLib.withCodeLoaded cpMpl polyBlockSpec) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, polyBlockSpec, limbsAt, cbH0, cbH1, cbH2, cbH3, cbH4,
    cbT0, cbD0, cbD1, cbD2, cbD3, cbD4, cbS, cbA0, cbA1, cbA2, cbA3, cbA4]
  wp_entry "<poly1305::backend::soft::State>::compute_block" g s0
  obtain ⟨st, blk, bs, r0, r1, r2, r3, r4, h0, h1, h2, h3, h4⟩ := g
  simp only at *
  wp_steps
  wp_done

/-- Change of ghost state for contracts with default failure clauses, under an extra pure
    fact `C` about the entry state (as added by `MultiPlacedLib.withCodeLoaded`). -/
theorem subroutine_ok_reghost {α β : Type} {prog : Program} {pc : BitVec 64}
    {pre₁ : α → Arm64.State → SepProp} {post₁ : α → Arm64.State → Arm64.State → SepProp}
    {pre₂ : β → Arm64.State → SepProp} {post₂ : β → Arm64.State → Arm64.State → SepProp}
    {C : Arm64.State → Prop}
    (h : subroutine_ok prog pc
      ({ pre := fun x s0 => pre₁ x s0 ∗ ⌜C s0⌝, post := post₁ } : Arm64.Spec α))
    (hc : ∀ y R s0, (s0.mem ⊨ pre₂ y s0 ∗ R) → ∃ x, (s0.mem ⊨ pre₁ x s0 ∗ R) ∧
      ∀ sf, (sf.mem ⊨ post₁ x s0 sf ∗ R) → (sf.mem ⊨ post₂ y s0 sf ∗ R)) :
    subroutine_ok prog pc
      ({ pre := fun y s0 => pre₂ y s0 ∗ ⌜C s0⌝, post := post₂ } : Arm64.Spec β) := by
  rw [subroutine_ok_iff]
  intro y R s0 hpc hrun hpre hsp
  rw [sepConj_assoc, sepConj_comm ⌜C s0⌝ R, ← sepConj_assoc] at hpre
  have hC : C s0 := by
    rw [sepConj_comm, satisfies_pure_sepConj] at hpre
    exact hpre.1
  rw [sepConj_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨x, hx, hpost⟩ := hc y R s0 hpre.2
  refine h.mono_outcome x R s0 hpc hrun ?_ hsp (fun sf ho => ?_)
  · rw [sepConj_assoc, sepConj_comm ⌜C s0⌝ R, ← sepConj_assoc, sepConj_comm, satisfies_pure_sepConj]
    exact ⟨hC, hx⟩
  · rcases ho with ⟨hret, hcc, hq⟩ | ho
    · exact Or.inl ⟨hret, hcc, hpost sf hq⟩
    · exact Or.inr ho

private theorem mod_step {a b m r p : Nat} (h : a % p = b % p) :
    (a + m) * r % p = (b + m) * r % p % p := by
  rw [Nat.mod_mod, Nat.mul_mod, Nat.add_mod, h, ← Nat.add_mod, ← Nat.mul_mod]

/-- One Poly1305 block step, as a contract over the RFC model. -/
theorem polyBlockContract_ok [CpPlacement] :
    subroutine_ok cpProg7r cpPl7.base (chachapolyLib.withCodeLoaded cpMpl polyBlockContract) := by
  refine subroutine_ok_reghost (C := fun s0 => chachapolyLib.CodeLoaded cpMpl s0.mem)
    (pre₁ := polyBlockSpec.pre) (post₁ := polyBlockSpec.post) polyBlock_ok ?_
  rintro ⟨st, blk, bs, r, acc⟩ R s0 hpre
  simp only [polyBlockContract] at hpre ⊢
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpre
  obtain ⟨l, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨⟨hx0, hx1, hx2, hlen⟩, ⟨hr0, hr1, hr2, hr3, hr4⟩, hrv, ⟨hh0, hh1, hh2, hh3, hh4⟩, hhv⟩, hm⟩ := hpre
  refine ⟨⟨st, blk, bs, l.r0, l.r1, l.r2, l.r3, l.r4, l.h0, l.h1, l.h2, l.h3, l.h4⟩, ?_, ?_⟩
  · simp only [polyBlockSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen⟩, hm⟩
  · intro sf hq
    simp only [polyBlockSpec] at hq
    obtain ⟨⟨ha0, ha1, ha2, ha3, ha4⟩, hav⟩ := msg_correct l.h0 l.h1 l.h2 l.h3 l.h4 bs hlen hh0 hh1 hh2 hh3 hh4
    obtain ⟨hb, hv⟩ := cb_correct l.r0 l.r1 l.r2 l.r3 l.r4 _ _ _ _ _ hr0 hr1 hr2 hr3 hr4 ha0 ha1 ha2 ha3 ha4
    refine Satisfies.sepExists_intro ⟨l.r0, l.r1, l.r2, l.r3, l.r4,
      (cbH0 l.r0 l.r1 l.r2 l.r3 l.r4 (cbA0 l.h0 bs) (cbA1 l.h1 bs) (cbA2 l.h2 bs) (cbA3 l.h3 bs) (cbA4 l.h4 bs)),
      (cbH1 l.r0 l.r1 l.r2 l.r3 l.r4 (cbA0 l.h0 bs) (cbA1 l.h1 bs) (cbA2 l.h2 bs) (cbA3 l.h3 bs) (cbA4 l.h4 bs)),
      (cbH2 l.r0 l.r1 l.r2 l.r3 l.r4 (cbA0 l.h0 bs) (cbA1 l.h1 bs) (cbA2 l.h2 bs) (cbA3 l.h3 bs) (cbA4 l.h4 bs)),
      (cbH3 l.r0 l.r1 l.r2 l.r3 l.r4 (cbA0 l.h0 bs) (cbA1 l.h1 bs) (cbA2 l.h2 bs) (cbA3 l.h3 bs) (cbA4 l.h4 bs)),
      (cbH4 l.r0 l.r1 l.r2 l.r3 l.r4 (cbA0 l.h0 bs) (cbA1 l.h1 bs) (cbA2 l.h2 bs) (cbA3 l.h3 bs) (cbA4 l.h4 bs))⟩ ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨⟨hr0, hr1, hr2, hr3, hr4⟩, hrv, hb, ?_⟩, hq⟩
    rw [hv, hav, hrv]
    exact mod_step hhv

end ChaChaPoly.Proofs
