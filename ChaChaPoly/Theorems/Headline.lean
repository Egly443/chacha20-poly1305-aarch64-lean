module

public import ChaChaPoly.Spec
public import ChaChaPoly.Generated.ChachapolyPlacedObj
public import ChaChaPoly.Generated.ChachapolyElfObj
public import Arm64.Trusted.Process.Placed
public import Arm64.Trusted.Spec.Placed
import ChaChaPoly.Generated.ChachapolyPlacedWitness
import ChaChaPoly.Proofs

/-!
# Headline theorems

Every theorem here is stated only in terms of trusted definitions (`ChaChaPoly.Spec.*`, the
`Arm64` semantics, and the generated library/ELF constants) and is proved without `sorry`.
`scripts/audit` checks their axioms and `comparator/` re-checks the statements independently.
See `README.md` for what is and is not covered.
-/

@[expose] public section

namespace ChaChaPoly.Theorems

open Arm64 Arm64.Obj ChaChaPoly ChaChaPoly.Spec

/-- **The verified library is the code in the pinned executable.** The stock-linked,
    SHA-256-pinned ELF `impl/chachapoly_cli.elf` contains `chachapolyLib` (the object code
    extracted by `rust-obj2lean`) at some placement a standard static linker could produce,
    with `chachapoly_encrypt` and `chachapoly_decrypt` at their `.symtab` addresses. -/
theorem chachapoly_linked_in : chachapolyLib.LinkedIn chachapolyElfBytes :=
  chachapolyLib_linkedIn

set_option maxRecDepth 200000 in
/-- **ChaCha20 block function (machine code).** For every placement of the library, the
    AArch64 code of RustCrypto's `write_keystream_block` satisfies `chachaBlockSpec`: it writes
    `(doubleRound^10 s) + s` to the output block and increments the block counter. No hooks. -/
theorem chacha20_block_refines (mpl : MultiPlacement) (hpl : chachapolyLib.Placeable mpl) :
    subroutine_ok (chachapolyLib.blockProgram mpl 3)
      (chachapolyLib.fnAddr mpl writeKeystreamBlockSym)
      (chachapolyLib.withCodeLoaded mpl chachaBlockSpec) := by
  have hfn : chachapolyLib.fnAddr mpl writeKeystreamBlockSym = mpl.base 3 := by
    have h : lookupBlockSym writeKeystreamBlockSym chachapolyLib.blocks = some (3, 0) := by
      decide +kernel
    simp [MultiPlacedLib.fnAddr, h]
  rw [hfn]
  exact @Proofs.chachaBlock_ok ⟨mpl, hpl⟩

set_option maxRecDepth 200000 in
/-- **Poly1305 block step (machine code).** For every placement of the library, the AArch64
    code of RustCrypto's `State::compute_block` (called with `partial = false`) satisfies
    `polyBlockContract`: the accumulator becomes `(acc + block ‖ 0x01) * r mod 2^130 - 5`,
    one iteration of `polyBlocks` of RFC 8439 §2.5.1. No hooks. -/
theorem poly1305_block_refines (mpl : MultiPlacement) (hpl : chachapolyLib.Placeable mpl) :
    subroutine_ok (chachapolyLib.blockProgram mpl 7)
      (chachapolyLib.fnAddr mpl polyComputeBlockSym)
      (chachapolyLib.withCodeLoaded mpl polyBlockContract) := by
  have hfn : chachapolyLib.fnAddr mpl polyComputeBlockSym = mpl.base 7 := by
    have h : lookupBlockSym polyComputeBlockSym chachapolyLib.blocks = some (7, 0) := by
      decide +kernel
    simp [MultiPlacedLib.fnAddr, h]
  rw [hfn]
  exact @Proofs.polyBlockContract_ok ⟨mpl, hpl⟩

/-- **Round trip (model).** RFC 8439 decryption inverts encryption on all inputs. -/
theorem aead_roundtrip (key nonce aad pt : Bytes) :
    aeadDecrypt key nonce aad (aeadEncrypt key nonce aad pt).1 (aeadEncrypt key nonce aad pt).2 =
      some pt :=
  Spec.aead_roundtrip key nonce aad pt

/-- **The RFC model is the generic construction at the real primitives.** -/
theorem aead_is_construction (key nonce aad d tag : Bytes) :
    aeadEncrypt key nonce aad d = Aead.encrypt rfcPrims key nonce aad d ∧
    aeadDecrypt key nonce aad d tag = Aead.decrypt rfcPrims key nonce aad d tag :=
  ⟨rfl, rfl⟩

/-- **Symbolic integrity (construction).** Under an ideal MAC, if `(ct, tag)` encrypts some
    plaintext under `(key, nonce, aad)`, then decryption under `(key, nonce)` rejects every
    other `(aad', ct')` presented with `tag`: any modification of the ciphertext or of the
    associated data is rejected. -/
theorem aead_integrity {Tag : Type} [DecidableEq Tag] (P : Prims Tag) (hideal : P.IdealMac)
    {key nonce aad pt ct aad' ct' : Bytes} {tag : Tag}
    (henc : Aead.encrypt P key nonce aad pt = (ct, tag))
    (hlen : LengthsOk aad ct) (hlen' : LengthsOk aad' ct')
    (hne : (aad', ct') ≠ (aad, ct)) :
    Aead.decrypt P key nonce aad' ct' tag = none :=
  Aead.integrity P hideal henc hlen hlen' hne

/-- **The symbolic model is satisfiable.** Ideal MACs exist for every stream cipher. -/
theorem ideal_mac_exists (stream : Bytes → Bytes → Bytes → Bytes)
    (macKey : Bytes → Bytes → Bytes) : (idealPrims stream macKey).IdealMac :=
  idealPrims_idealMac stream macKey

end ChaChaPoly.Theorems
