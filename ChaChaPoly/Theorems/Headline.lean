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
/-- **ChaCha20 stream XOR (machine code).** For every placement of the library, the AArch64
    code of RustCrypto's `StreamCipherCoreWrapper::apply_keystream` (295 instructions, with
    the inlined block function and its `write_keystream_block` call for the tail) satisfies
    `applyKeystreamContract`: started with key-stream position 0, it XORs the `len` data bytes in
    place with the key stream of the cipher state `s` (`streamXor s data`), advances the block
    counter by `⌈len / 64⌉` and leaves position `len mod 64`. The precondition excludes the
    counter-overflow panic (`⌈len / 64⌉ + counter < 2^32`). No hooks. -/
theorem apply_keystream_refines (mpl : MultiPlacement) (hpl : chachapolyLib.Placeable mpl) :
    subroutine_ok (chachapolyLib.blockProgram mpl 4)
      (chachapolyLib.fnAddr mpl applyKeystreamSym)
      (chachapolyLib.withCodeLoaded mpl applyKeystreamContract) := by
  have hfn : chachapolyLib.fnAddr mpl applyKeystreamSym = mpl.base 4 := by
    have h : lookupBlockSym applyKeystreamSym chachapolyLib.blocks = some (4, 0) := by
      decide +kernel
    simp [MultiPlacedLib.fnAddr, h]
  rw [hfn]
  exact @Proofs.applyKeystream_ok ⟨mpl, hpl⟩

set_option maxRecDepth 200000 in
/-- **AEAD encryption (machine code).** For every placement of the library, the AArch64 code of
    `chachapoly_encrypt` (307 instructions, calling the verified blocks above and musl's
    `memcpy` / `memset`) satisfies `aeadEncryptContract`: given the key, nonce, associated data and
    a message of at most `maxMsgLen` bytes in non-overlapping buffers, and the library's read-only
    ChaCha constant at its placed address, it returns `0`, leaves the RFC 8439 §2.8 ciphertext
    `(aeadEncrypt key nonce aad msg).1` in the buffer and writes the tag
    `(aeadEncrypt key nonce aad msg).2`. No hooks. -/
theorem chachapoly_encrypt_refines (mpl : MultiPlacement) (hpl : chachapolyLib.Placeable mpl) :
    subroutine_ok (chachapolyLib.blockProgram mpl 6)
      (chachapolyLib.fnAddr mpl encryptSym)
      (chachapolyLib.withCodeLoaded mpl (aeadEncryptContract (mpl.ρ sigmaDataSym))) := by
  have hfn : chachapolyLib.fnAddr mpl encryptSym = mpl.base 6 := by
    have h : lookupBlockSym encryptSym chachapolyLib.blocks = some (6, 0) := by
      decide +kernel
    simp [MultiPlacedLib.fnAddr, h]
  rw [hfn]
  exact @Proofs.encrypt_ok ⟨mpl, hpl⟩

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

set_option maxRecDepth 200000 in
/-- **Poly1305 finalisation (machine code).** For every placement of the library, the AArch64
    code of `<Poly1305 as UniversalHash>::finalize` satisfies `polyFinalContract`: from
    accumulator limbs within the representation bounds it writes the 16-byte tag
    `(acc mod (2^130 - 5) + s) mod 2^128`. No hooks. -/
theorem poly1305_finalize_refines (mpl : MultiPlacement) (hpl : chachapolyLib.Placeable mpl) :
    subroutine_ok (chachapolyLib.blockProgram mpl 8)
      (chachapolyLib.fnAddr mpl polyFinalizeSym)
      (chachapolyLib.withCodeLoaded mpl polyFinalContract) := by
  have hfn : chachapolyLib.fnAddr mpl polyFinalizeSym = mpl.base 8 := by
    have h : lookupBlockSym polyFinalizeSym chachapolyLib.blocks = some (8, 0) := by
      decide +kernel
    simp [MultiPlacedLib.fnAddr, h]
  rw [hfn]
  exact @Proofs.polyFinalContract_ok ⟨mpl, hpl⟩

set_option maxRecDepth 200000 in
/-- **Poly1305 key setup (machine code).** For every placement of the library, the AArch64 code
    of `<Poly1305 as KeyInit>::new` satisfies `polyNewContract`: from a 32-byte key it builds a
    state whose limbs represent `r = clamp (leNat key[0..16])` and accumulator `0`, with pad
    `s = leNat key[16..32]` (RFC 8439 §2.5.1). No hooks. -/
theorem poly1305_new_refines (mpl : MultiPlacement) (hpl : chachapolyLib.Placeable mpl) :
    subroutine_ok (chachapolyLib.blockProgram mpl 10)
      (chachapolyLib.fnAddr mpl polyNewSym)
      (chachapolyLib.withCodeLoaded mpl polyNewContract) := by
  have hfn : chachapolyLib.fnAddr mpl polyNewSym = mpl.base 10 := by
    have h : lookupBlockSym polyNewSym chachapolyLib.blocks = some (10, 0) := by
      decide +kernel
    simp [MultiPlacedLib.fnAddr, h]
  rw [hfn]
  exact @Proofs.polyNewContract_ok ⟨mpl, hpl⟩

set_option maxRecDepth 200000 in
/-- **Poly1305 full-block wrapper (machine code).** For every placement, `proc_block` (which
    sets `partial = false` and tail-calls `compute_block` in another code block) satisfies
    `polyProcBlockContract`: one RFC 8439 §2.5.1 step on a full 16-byte block. No hooks. -/
theorem poly1305_proc_block_refines (mpl : MultiPlacement) (hpl : chachapolyLib.Placeable mpl) :
    subroutine_ok (chachapolyLib.blockProgram mpl 9)
      (chachapolyLib.fnAddr mpl polyProcBlockSym)
      (chachapolyLib.withCodeLoaded mpl polyProcBlockContract) := by
  have hfn : chachapolyLib.fnAddr mpl polyProcBlockSym = mpl.base 9 := by
    have h : lookupBlockSym polyProcBlockSym chachapolyLib.blocks = some (9, 0) := by
      decide +kernel
    simp [MultiPlacedLib.fnAddr, h]
  rw [hfn]
  exact @Proofs.polyProcBlockContract_ok ⟨mpl, hpl⟩

set_option maxRecDepth 200000 in
/-- **`subtle::black_box::<u8>` (machine code).** Returns its byte argument. No hooks. -/
theorem black_box_refines (mpl : MultiPlacement) (hpl : chachapolyLib.Placeable mpl) :
    subroutine_ok (chachapolyLib.blockProgram mpl 0)
      (chachapolyLib.fnAddr mpl blackBoxSym)
      (chachapolyLib.withCodeLoaded mpl blackBoxContract) := by
  have hfn : chachapolyLib.fnAddr mpl blackBoxSym = mpl.base 0 := by
    have h : lookupBlockSym blackBoxSym chachapolyLib.blocks = some (0, 0) := by
      decide +kernel
    simp [MultiPlacedLib.fnAddr, h]
  rw [hfn]
  exact @Proofs.blackBox_ok ⟨mpl, hpl⟩

set_option maxRecDepth 200000 in
/-- **`Cipher` drop glue (machine code).** Owns and returns the 129-byte key-stream state. No hooks. -/
theorem cipher_drop_refines (mpl : MultiPlacement) (hpl : chachapolyLib.Placeable mpl) :
    subroutine_ok (chachapolyLib.blockProgram mpl 1)
      (chachapolyLib.fnAddr mpl cipherDropSym)
      (chachapolyLib.withCodeLoaded mpl cipherDropContract) := by
  have hfn : chachapolyLib.fnAddr mpl cipherDropSym = mpl.base 1 := by
    have h : lookupBlockSym cipherDropSym chachapolyLib.blocks = some (1, 0) := by
      decide +kernel
    simp [MultiPlacedLib.fnAddr, h]
  rw [hfn]
  exact @Proofs.cipherDrop_ok ⟨mpl, hpl⟩

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
