module

public import ChaChaPoly.Proofs.Code
public import VerifiedLibraries.Musl.Proofs.MemcpySym
public import VerifiedLibraries.Musl.Proofs.MemsetSym

/-!
# musl `memcpy` and `memset` (blocks 11 and 12)

The library contains musl's AArch64 `memcpy` and `memset` from the toolchain's self-contained
`libc.a` (the objects the linker put in the ELF; see `scripts/extract`). Their code is word for
word the code that upstream `VerifiedLibraries.Musl` verifies (`memcpySymWords`,
`memsetWordsSym`, checked here by the kernel), so upstream's proofs give their full C contracts
for every placement: `memsetSymSpec` directly, and for `memcpy` the contract `muslMemcpySpec`
below, obtained from upstream's symbolic-execution theorem `memcpy_sepwp` (upstream states the
same contract as `memcpySymSpec` in a module that needs a separately generated musl object).
No hooks are involved.
-/

@[expose] public section

namespace ChaChaPoly.Proofs

open Arm64 Arm64.Obj ProofLib

set_option maxRecDepth 200000

/-- The demangled name of musl's `memcpy`. -/
def memcpySym : String := "memcpy"

/-- The demangled name of musl's `memset`. -/
def memsetSym : String := "memset"

/-- Block 11 holds musl's `memcpy`, at its base. -/
theorem memcpy_hasWords [CpPlacement] :
    (chachapolyLib.blockProgram cpMpl 11).hasWords (cpMpl.base 11)
      VerifiedLibraries.Musl.memcpySymWords := by
  have ⟨hw, _⟩ := MultiPlacedLib.hasWords_of_checkSegment (lib := chachapolyLib) (mpl := cpMpl)
    (i := 11) (fo := 0) (ws := VerifiedLibraries.Musl.memcpySymWords) (R := []) (X := fun _ => none) (svc := Syscall.standard)
    (by decide) CpPlacement.placeable (by decide +kernel)
  simpa [Obj.patchRelocs] using hw

/-- Block 12 holds musl's `memset`, at its base. -/
theorem memset_hasWords [CpPlacement] :
    (chachapolyLib.blockProgram cpMpl 12).hasWords (cpMpl.base 12)
      VerifiedLibraries.Musl.memsetWordsSym := by
  have ⟨hw, _⟩ := MultiPlacedLib.hasWords_of_checkSegment (lib := chachapolyLib) (mpl := cpMpl)
    (i := 12) (fo := 0) (ws := VerifiedLibraries.Musl.memsetWordsSym) (R := []) (X := fun _ => none) (svc := Syscall.standard)
    (by decide) CpPlacement.placeable (by decide +kernel)
  simpa [Obj.patchRelocs] using hw

/-- The C contract of `memcpy(dst, src, n)` for non-overlapping buffers (as in upstream
    `memcpySymSpec`, with the length bound `n < 2^63` stated instead of derived). -/
def muslMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ bs.length < 2 ^ 63⌝ ∗
    memRegion dst bs.length ∗ (src ↦ₛ bs)
  post := fun (dst, src, bs) _ sf =>
    ⌜sf.readReg64 .x0 = dst⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs)

/-- musl's `memcpy` (block 11) meets `muslMemcpySpec`. -/
theorem memcpy_blk_ok [CpPlacement] :
    subroutine_ok (chachapolyLib.blockProgram cpMpl 11) (cpMpl.base 11) muslMemcpySpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre -
  simp only [muslMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, h63⟩, hmem⟩ := hpre
  have hn : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat]; omega
  refine ⟨memRegion dst bs.length ∗ (src ↦ₛ bs), by rwa [sepConj_assoc], ?_⟩
  rw [memRegion_eq_exists_bytes dst bs.length (by omega), sepExists_sepConj_left]
  refine SepWP.exists_elim fun old => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hold => ?_
  refine SepWP.mono (VerifiedLibraries.Musl.memcpy_sepwp false _ _ memcpy_hasWords s0 dst src
    (BitVec.ofNat 64 bs.length) old bs hpc hrun hx0 hx1 hx2 (by omega) (by omega) (by omega)) ?_
  rintro sf P_f - - ⟨⟨hx0f, hspf, hcsf⟩, hent⟩
  refine ⟨fun hm => ?_, hspf, hcsf⟩
  simp only [muslMemcpySpec, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hx0f, ?_⟩
  rw [← sepConj_assoc]
  exact Satisfies.mono (sepConj_mono_left hent) hm

/-- musl's `memset` (block 12) meets upstream's full C contract. -/
theorem memset_blk_ok [CpPlacement] :
    subroutine_ok (chachapolyLib.blockProgram cpMpl 12) (cpMpl.base 12)
      VerifiedLibraries.Musl.memsetSymSpec :=
  VerifiedLibraries.Musl.memset_codeAt_ok_sym _ _ memset_hasWords

end ChaChaPoly.Proofs
