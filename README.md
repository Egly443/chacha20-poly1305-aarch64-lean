# Machine-code verification of ChaCha20-Poly1305 (RFC 8439) on AArch64, in Lean 4

This repository contains a machine-checked proof that an unmodified, stock-compiled AArch64
binary of the RustCrypto `chacha20poly1305` AEAD computes RFC 8439, on top of the
`arm64-semantics` engine of
[google-deepmind/code-verification](https://github.com/google-deepmind/code-verification)
(pinned as a submodule at `808b4b7`).

Both entry points, `chachapoly_encrypt` and `chachapoly_decrypt`, and every function they call
are proved against the RFC 8439 model. Read [Status](#status) and [Trusted assumptions](#trusted-assumptions)
for exactly what is claimed.

## Status

Proved, kernel-checked, no `sorry`, standard axioms only (`scripts/audit`):

| Theorem (`ChaChaPoly/Theorems/Headline.lean`) | What it says |
| --- | --- |
| `chachapoly_linked_in` | The SHA-256-pinned ELF contains the extracted library (all 11 functions reachable from `chachapoly_encrypt` / `chachapoly_decrypt`) at a placement a standard static linker could produce. |
| `chacha20_block_refines` | For every placement, the machine code of `ChaChaCore::write_keystream_block` (167 instructions) writes `(doubleRound^10 s) + s` and increments the block counter. No hooks. |
| `apply_keystream_refines` | For every placement, the machine code of the stream-cipher wrapper `apply_keystream` (295 instructions: the per-block loop with the block function inlined, plus a `write_keystream_block` call for a final partial block) XORs the buffer in place with the RFC 8439 §2.4 key stream of the cipher state, advances the block counter by `⌈len/64⌉` and records `len mod 64` as the key-stream position. Precondition: position 0 on entry (true for the fresh cipher the entry points build) and no counter overflow (`⌈len/64⌉ + counter < 2^32`, the condition under which the code panics). No hooks. |
| `chachapoly_encrypt_refines` | For every placement, the machine code of the entry point `chachapoly_encrypt` (307 instructions) meets `aeadEncryptContract`: given key, nonce, associated data and a message of at most `maxMsgLen` bytes in non-overlapping buffers (and the library's read-only ChaCha constant at its placed address), it returns `0`, leaves `(aeadEncrypt key nonce aad msg).1` in the buffer and writes `(aeadEncrypt key nonce aad msg).2` as the tag. Calls only verified code (the blocks above and musl's `memcpy` / `memset`). No hooks. |
| `chachapoly_decrypt_refines` | For every placement, the machine code of the entry point `chachapoly_decrypt` (410 instructions) meets `aeadDecryptContract`: given key, nonce, associated data, a ciphertext of at most `maxMsgLen` bytes and a tag in non-overlapping buffers (and the read-only ChaCha constant), if `aeadDecrypt key nonce aad ct tag = some p` it returns `0` and leaves `p` in the buffer; if it is `none` it returns `-1` and leaves the buffer unchanged. The tag check is the binary's constant-time comparison (16 byte comparisons, each through `subtle::black_box`, AND-ed). No hooks. |
| `chachapoly_decrypt_integrity` | Symbolic integrity transferred to the machine code: if the presented tag is the honest tag of an encryption of `(aad0, pt)` under the same key and nonce and the presented `(aad, ct)` differs from `(aad0, ct0)`, the binary returns `-1` and leaves the buffer unchanged, unless Poly1305 under the one-time key collides on the two distinct authenticated encodings (`polyCollision`), which is exactly what the ideal-MAC assumption of `aead_integrity` excludes. |
| `poly1305_block_refines` | For every placement, the machine code of Poly1305's `State::compute_block` (74 instructions, `partial = false`) performs one RFC 8439 §2.5.1 step: the accumulator becomes `(acc + block‖0x01) · r mod 2^130 − 5`. No hooks. |
| `poly1305_finalize_refines` | For every placement, the machine code of `Poly1305::finalize` (59 instructions, including the constant-time final reduction) writes the tag `(acc mod 2^130 − 5 + s) mod 2^128`. No hooks. |
| `poly1305_new_refines` | For every placement, the machine code of `Poly1305::new` (24 instructions) builds a state representing `r = clamp(key[0..16])`, accumulator 0 and pad `key[16..32]`. The clamp is checked bit by bit by the kernel-checked ROBDD procedure. No hooks. |
| `poly1305_proc_block_refines` | For every placement, `proc_block` (sets `partial = false`, tail-calls `compute_block` in another code block) performs one §2.5.1 step. No hooks. |
| `black_box_refines`, `cipher_drop_refines` | The constant-time comparison's `black_box::<u8>` returns its argument; the `Cipher` drop glue owns and returns its 129-byte key-stream state (it also zeroises it; that is not claimed). No hooks. |
| `aead_roundtrip` | In the RFC 8439 model, decryption inverts encryption on all inputs. |
| `aead_is_construction` | The RFC model is the generic §2.8 construction instantiated with the real ChaCha20 / Poly1305. |
| `aead_integrity` | Symbolic integrity of the construction: under an ideal MAC, any change to the ciphertext or the associated data is rejected. |
| `ideal_mac_exists` | The ideal-MAC assumption is satisfiable (the symbolic model is not vacuous). |

Every function reachable from the two entry points is covered; there is no unproved part of
the binary on the paths the contracts allow (the panic paths they exclude are listed under
[Trusted assumptions](#trusted-assumptions)).

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
  memory it owns, including its stack frame (144 bytes for the block function, `0x4a0` bytes for
  `chachapoly_encrypt`, `0x490` bytes for `chachapoly_decrypt`). The entry-point contracts own the key, nonce, associated data, buffer and
  tag as separate byte slices, so they apply when these do not overlap. They also own, read-only,
  the 16-byte ChaCha constant `"expand 32-byte k"` at its placed address in the library's
  `.rodata`; loading the ELF establishes it (`MultiPlacedLib.satisfies_dataRO_of_inElf`).
- **Length bounds**: messages of at most `maxMsgLen = 274,877,906,816` bytes (so the 32-bit block
  counter, started at 1, cannot overflow; RustCrypto's own guard only rejects lengths of at least
  `274,877,906,880`, and on the 63 lengths in between the binary panics), and associated data of
  fewer than `2^63` bytes.
- **Hooks**: none. musl's AArch64 `memcpy` and `memset` (called by the entry points to pad a
  partial Poly1305 block) are not hooked: their machine code is extracted into the library as
  blocks 11 and 12 (`memcpy.lo` / `memset.lo` from the toolchain's self-contained `libc.a`,
  SHA-256 `b03473b6…813f`, checked by `scripts/extract`), and the kernel checks that it is word for
  word the code upstream `VerifiedLibraries.Musl` verifies, whose proofs give their full C
  contracts (`Proofs/MuslBlocks.lean`). The only remaining external references are the
  panic-path functions `core::result::unwrap_failed` / `Formatter::write_str`, reached only on
  the paths the contracts exclude.
- **Symbolic model**: `aead_integrity` assumes `Prims.IdealMac` (no two messages share a tag
  under one key). Real Poly1305 has 16-byte tags and cannot satisfy it; the theorem excludes
  forgeries that do not go through a MAC collision and is not a computational bound.
  `chachapoly_decrypt_integrity` states the same property for the binary with the collision made
  explicit (`polyCollision` in `Spec/Contracts.lean`) instead of assumed away.
- **Compiler flags**: auto-vectorisation is off, as in the upstream case studies, so the
  ChaCha20 code is scalar. The proofs are about the resulting bytes, whatever the flags.

Out of scope: computational reductions, multi-message security, side channels, protocols.

## License and acknowledgements

Copyright 2026 Brian Sanders. Licensed under the [Apache License, Version 2.0](LICENSE), the
same license as the upstream code it builds on; see [NOTICE](NOTICE).

This work is built on [google-deepmind/code-verification](https://github.com/google-deepmind/code-verification)
(Copyright 2026 Google LLC, Apache 2.0): its AArch64 semantics, proof library, verified musl
routines, `rust-obj2lean` extractor and comparator setup make these proofs possible. Thanks to
its authors. The pinned binary also contains compiled code from RustCrypto's crates, the Rust
standard library and musl, under their own (MIT / Apache-2.0) licenses.
