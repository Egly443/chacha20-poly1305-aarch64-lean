import Lake
open Lake DSL

/-!
# `chachapoly-verification`

Machine-code verification of the RustCrypto IETF ChaCha20-Poly1305 AEAD (RFC 8439) as compiled
to AArch64, on top of the `arm64-semantics` engine (`Arm64` trusted semantics + `ProofLib`
untrusted proof automation) of the pinned `third_party/code-verification` submodule.

Libraries, in trust order:

* `Spec`      — `ChaChaPoly.Spec.*`: the human-reviewable RFC 8439 model and the machine-code
                contracts. Imports only Lean core and the trusted `Arm64` vocabulary.
* `Generated` — `ChaChaPoly.Generated.*`: `rust-obj2lean` output for the pinned ELF.
* `Proofs`    — `ChaChaPoly.Proofs.*`: untrusted proofs.
* `Theorems`  — `ChaChaPoly.Theorems.*`: the headline theorem statements and their proofs.
-/

package «chachapoly-verification» where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
  weakLeanArgs := #["-M", "12288"]

require prooflib from "third_party/code-verification/arm64-semantics/ProofLib"

lean_lib Generated where
  roots := #[`ChaChaPoly.Generated]
  globs := #[.andSubmodules `ChaChaPoly.Generated]

@[default_target]
lean_lib Spec where
  roots := #[`ChaChaPoly.Spec]
  globs := #[.andSubmodules `ChaChaPoly.Spec]

@[default_target]
lean_lib Proofs where
  roots := #[`ChaChaPoly.Proofs]
  globs := #[.andSubmodules `ChaChaPoly.Proofs]

@[default_target]
lean_lib Theorems where
  roots := #[`ChaChaPoly.Theorems]
  globs := #[.andSubmodules `ChaChaPoly.Theorems]
