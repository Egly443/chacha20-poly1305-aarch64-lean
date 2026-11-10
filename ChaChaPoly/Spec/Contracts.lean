module

public import Arm64
public import ChaChaPoly.Spec.RFC8439

/-!
# Machine-code contracts (trusted statements)

Pre/postconditions, in the separation logic of `Arm64.Trusted.Spec`, for the AArch64 functions of
the pinned library. They are stated against the RFC 8439 model of `Spec/RFC8439.lean` and import
only the trusted `Arm64` vocabulary.

A contract `Spec α` is read as: for every ghost value `x : α`, if the function is entered in a
state `s0` whose memory satisfies `pre x s0 ∗ R` (for any frame `R`), then it returns, with the
AAPCS64 callee-saved registers and the stack pointer restored, in a state whose memory satisfies
`post x s0 sf ∗ R`. Panics, exits and out-of-memory are excluded (`Spec` defaults).
-/

@[expose] public section

namespace ChaChaPoly.Spec

open Arm64

/-- Sixteen little-endian 32-bit words at `p`: a ChaCha state (or a 64-byte key-stream block). -/
def stateAt (p : BitVec 64) (s : State) : SepProp :=
  (p ↦₃₂ s.x0) ∗ ((p + 4#64) ↦₃₂ s.x1) ∗ ((p + 8#64) ↦₃₂ s.x2) ∗ ((p + 12#64) ↦₃₂ s.x3) ∗
  ((p + 16#64) ↦₃₂ s.x4) ∗ ((p + 20#64) ↦₃₂ s.x5) ∗ ((p + 24#64) ↦₃₂ s.x6) ∗ ((p + 28#64) ↦₃₂ s.x7) ∗
  ((p + 32#64) ↦₃₂ s.x8) ∗ ((p + 36#64) ↦₃₂ s.x9) ∗ ((p + 40#64) ↦₃₂ s.x10) ∗ ((p + 44#64) ↦₃₂ s.x11) ∗
  ((p + 48#64) ↦₃₂ s.x12) ∗ ((p + 52#64) ↦₃₂ s.x13) ∗ ((p + 56#64) ↦₃₂ s.x14) ∗ ((p + 60#64) ↦₃₂ s.x15)

/-- The demangled name of RustCrypto's ChaCha20 block function in the pinned object. -/
def writeKeystreamBlockSym : String :=
  "<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>> as cipher::stream_core::StreamCipherCore>::write_keystream_block"

/-- Contract of `ChaChaCore::write_keystream_block(&mut self, block: &mut [u8; 64])`.

    Ghosts: the state pointer `st` (in `x0`), the output pointer `out` (in `x1`), the ChaCha state
    `s` stored at `st`, and the previous contents `o` of the output block.

    The function writes `(doubleRound^10 s) + s` (word-wise, little-endian) to `out`, which is
    `chacha20Block` of RFC 8439 §2.3 when `s` is an `initState`, and increments the block counter
    `s.x12` in place. It uses a 144-byte stack frame. -/
def chachaBlockSpec : Spec (BitVec 64 × BitVec 64 × State × State) where
  pre := fun (st, out, s, o) s0 =>
    ⌜s0.readReg64 .x0 = st ∧ s0.readReg64 .x1 = out⌝ ∗
    stateAt st s ∗ stateAt out o ∗ stackFrame s0 0x90
  post := fun (st, out, s, _) s0 _ =>
    stateAt st { s with x12 := s.x12 + 1 } ∗
    stateAt out ((iter doubleRound 10 s).add s) ∗ stackFrame s0 0x90

end ChaChaPoly.Spec
