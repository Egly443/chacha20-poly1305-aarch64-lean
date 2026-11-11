# Machine-code verification of ChaCha20-Poly1305 (RFC 8439) on AArch64, in Lean 4

This repository works towards a machine-checked proof that an unmodified, stock-compiled
AArch64 binary of the RustCrypto `chacha20poly1305` AEAD computes RFC 8439, on top of the
`arm64-semantics` engine of
[google-deepmind/code-verification](https://github.com/google-deepmind/code-verification)
(pinned as a submodule at `808b4b7`).

**The refinement proof is not complete.** Read [Status](#status) before relying on anything
here: it lists exactly which theorems are proved and which parts of the binary are not yet
covered.

## Status

Proved, kernel-checked, no `sorry`, standard axioms only (`scripts/audit`):

| Theorem (`ChaChaPoly/Theorems/Headline.lean`) | What it says |
| --- | --- |
| `chachapoly_linked_in` | The SHA-256-pinned ELF contains the extracted library (all 11 functions reachable from `chachapoly_encrypt` / `chachapoly_decrypt`) at a placement a standard static linker could produce. |
| `chacha20_block_refines` | For every placement, the machine code of `ChaChaCore::write_keystream_block` (167 instructions) writes `(doubleRound^10 s) + s` and increments the block counter. No hooks. |
| `poly1305_block_refines` | For every placement, the machine code of Poly1305's `State::compute_block` (74 instructions, `partial = false`) performs one RFC 8439 §2.5.1 step: the accumulator becomes `(acc + block‖0x01) · r mod 2^130 − 5`. No hooks. |
| `poly1305_finalize_refines` | For every placement, the machine code of `Poly1305::finalize` (59 instructions, including the constant-time final reduction) writes the tag `(acc mod 2^130 − 5 + s) mod 2^128`. No hooks. |
| `poly1305_new_refines` | For every placement, the machine code of `Poly1305::new` (24 instructions) builds a state representing `r = clamp(key[0..16])`, accumulator 0 and pad `key[16..32]`. The clamp is checked bit by bit by the kernel-checked ROBDD procedure. No hooks. |
| `poly1305_proc_block_refines` | For every placement, `proc_block` (sets `partial = false`, tail-calls `compute_block` in another code block) performs one §2.5.1 step. No hooks. |
| `aead_roundtrip` | In the RFC 8439 model, decryption inverts encryption on all inputs. |
| `aead_is_construction` | The RFC model is the generic §2.8 construction instantiated with the real ChaCha20 / Poly1305. |
| `aead_integrity` | Symbolic integrity of the construction: under an ideal MAC, any change to the ciphertext or the associated data is rejected. |
| `ideal_mac_exists` | The ideal-MAC assumption is satisfiable (the symbolic model is not vacuous). |

Not yet proved:

- Machine-code refinement of the remaining six functions: the stream-cipher wrapper
  `apply_keystream`, the `Cipher` drop glue (zeroises the key schedule), `subtle::black_box`,
  a 5-instruction error formatter on the panic path, and the two entry points
  `chachapoly_encrypt` / `chachapoly_decrypt`.
- Consequently there is **no end-to-end theorem about the entry points yet**, and the symbolic
  integrity theorem is about the Lean construction, not yet transferred to the binary.

## Target

| | |
| --- | --- |
| Source | RustCrypto `chacha20poly1305` 0.10.1, `chacha20` 0.9.1, `poly1305` 0.8.0 and dependencies from crates.io, exact versions and checksums pinned by `impl/Cargo.lock`; thin `extern "C"` wrapper in `impl/src/lib.rs` |
| Entry points | `chachapoly_encrypt` / `chachapoly_decrypt(key, nonce, aad, aad_len, buf, len, tag)`: in place, detached 16-byte tag |
| Toolchain | stock `rustc` / `cargo` 1.98.1 (the version the Signal proofs pin), its bundled LLVM `ld.lld` (`rust-lld`), target `aarch64-unknown-linux-musl`, static |
| Flags | `opt-level=2`, `codegen-units=1`, `panic=abort`, `relocation-model=static`, `target-cpu=generic`, `no-vectorize-loops`, `no-vectorize-slp` (the flags `rust-obj2lean` uses) |
| Binary | `impl/chachapoly_cli.elf`, SHA-256 `bc2586b4f00fbb21366019035f2fd95edc3c4274e0c460426006ec364566ceaa` |

The executable runs the RFC 8439 §2.8.2 vector through both entry points and exits `0`.

## Layout

```text
impl/                       wrapper crate, Cargo.lock, translation.toml, pinned ELF + .sha256
scripts/build-elf           reproducible build, --verify-pin, --check (rebuild and compare)
scripts/extract             rust-obj2lean extraction into ChaChaPoly/Generated (--check)
scripts/audit               sorry / axiom / pin audit of the headline theorems
scripts/gen-challenge       derives the comparator challenge from the headline file
ChaChaPoly/Spec/            TRUSTED: RFC 8439 model, test vectors, symbolic model, contracts
ChaChaPoly/Generated/       rust-obj2lean output: placed library, ELF bytes, link witness
ChaChaPoly/Proofs/          untrusted proofs
ChaChaPoly/Theorems/        headline theorems
comparator/                 leanprover/comparator challenge, solution, config, runner
third_party/code-verification   pinned upstream (Arm64 semantics, ProofLib, rust-obj2lean)
```

## Rebuild and recheck

```bash
git submodule update --init
# Lean (elan picks leanprover/lean4:v4.34.0 from lean-toolchain); first build compiles the
# upstream Arm64 + ProofLib libraries (roughly an hour on 4 cores).
ulimit -S -s 524288
lake build
scripts/audit

# Binary reproducibility (needs rustup toolchain 1.98.1 with the aarch64-unknown-linux-musl
# target, rust-src and llvm-tools):
scripts/build-elf --check        # rebuild from pinned sources, compare with the SHA-256 pin
scripts/extract --check          # re-extract, compare with ChaChaPoly/Generated

# Independent statement / axiom / kernel-replay check:
third_party/code-verification/comparator/install-tools.sh .lake/comparator-tools
set -a; source .lake/comparator-tools/env; set +a
comparator/run.sh
```

## Trusted assumptions

- **Lean kernel** and the three standard axioms.
- **AArch64 and process semantics**: `Arm64/Trusted` of the upstream engine (instruction
  decoding and execution, memory permissions, the ELF loader model). Single-threaded.
- **Placement model**: theorems quantify over every `Placeable` placement
  (`Arm64.Trusted.Object.Placed`); `chachapoly_linked_in` shows the pinned ELF is one.
- **Extraction**: `rust-obj2lean`'s trusted `.o` parser. The link witness independently ties
  the extracted bytes to the pinned ELF, so an extraction error makes that check fail.
- **Specification**: `ChaChaPoly/Spec/`. `RFC8439.lean` is a direct transcription of the RFC,
  checked in the kernel against the RFC's vectors for the quarter round, block function,
  encryption, Poly1305, key generation and the AEAD (`RFC8439Vectors.lean`).
- **Memory model of the contracts**: byte-granular separation logic; each contract names the
  memory it owns, including its stack frame (144 bytes for the block function).
- **Hooks**: none so far. The library's external references are `memcpy`, `memset`, and the
  two panic-path functions `core::result::unwrap_failed` / `Formatter::write_str`; they are
  only reached from functions that are not yet verified, and how each is treated will be
  recorded here when those proofs land.
- **Symbolic model**: `aead_integrity` assumes `Prims.IdealMac` (no two messages share a tag
  under one key). Real Poly1305 has 16-byte tags and cannot satisfy it; the theorem excludes
  forgeries that do not go through a MAC collision and is not a computational bound.
- **Compiler flags**: auto-vectorisation is off, as in the upstream case studies, so the
  ChaCha20 code is scalar. The proofs are about the resulting bytes, whatever the flags.

Out of scope: computational reductions, multi-message security, side channels, protocols.
