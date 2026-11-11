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

/-! ## Poly1305 accumulator in five 26-bit limbs -/

/-- The value of five 26-bit limbs. -/
def limbVal (h0 h1 h2 h3 h4 : Nat) : Nat :=
  h0 + 2 ^ 26 * h1 + 2 ^ 52 * h2 + 2 ^ 78 * h3 + 2 ^ 104 * h4

/-- Five 32-bit limbs at `p`. -/
def limbsAt (p : BitVec 64) (l0 l1 l2 l3 l4 : BitVec 32) : SepProp :=
  (p ↦₃₂ l0) ∗ ((p + 4#64) ↦₃₂ l1) ∗ ((p + 8#64) ↦₃₂ l2) ∗ ((p + 12#64) ↦₃₂ l3) ∗
  ((p + 16#64) ↦₃₂ l4)

/-- The ten limbs of RustCrypto's `poly1305::backend::soft::State`: multiplier `r`, accumulator `h`. -/
structure PolyLimbs where
  (r0 r1 r2 r3 r4 h0 h1 h2 h3 h4 : BitVec 32)

/-- The limbs `l` represent multiplier `r` and an accumulator congruent to `acc` modulo
    `2^130 - 5`: the `r` limbs are below `2^26` and have value `r`; the `h` limbs are below
    `2^26` (`h1`: below `2^26 + 64`, it absorbs the last carry) and have value `≡ acc`. -/
def PolyLimbs.Rep (l : PolyLimbs) (r acc : Nat) : Prop :=
  (l.r0.toNat < 2 ^ 26 ∧ l.r1.toNat < 2 ^ 26 ∧ l.r2.toNat < 2 ^ 26 ∧ l.r3.toNat < 2 ^ 26 ∧
    l.r4.toNat < 2 ^ 26) ∧
  limbVal l.r0.toNat l.r1.toNat l.r2.toNat l.r3.toNat l.r4.toNat = r ∧
  (l.h0.toNat < 2 ^ 26 ∧ l.h1.toNat < 2 ^ 26 + 64 ∧ l.h2.toNat < 2 ^ 26 ∧ l.h3.toNat < 2 ^ 26 ∧
    l.h4.toNat < 2 ^ 26) ∧
  limbVal l.h0.toNat l.h1.toNat l.h2.toNat l.h3.toNat l.h4.toNat % p1305 = acc % p1305

/-- The `r` and `h` fields of a Poly1305 state at `st` (offsets `0x10` and `0x24`), holding `l`. -/
def polyLimbsAt (st : BitVec 64) (l : PolyLimbs) : SepProp :=
  limbsAt (st + 16#64) l.r0 l.r1 l.r2 l.r3 l.r4 ∗ limbsAt (st + 36#64) l.h0 l.h1 l.h2 l.h3 l.h4

/-- The demangled name of the Poly1305 block function in the pinned object. -/
def polyComputeBlockSym : String := "<poly1305::backend::soft::State>::compute_block"

/-- Contract of `poly1305::backend::soft::State::compute_block(&mut self, block, partial = false)`.

    Ghosts: state pointer `st` (`x0`), block pointer `blk` (`x1`), the 16 block bytes `bs`, the
    multiplier `r` and the accumulator `acc`.

    If the state's limbs represent `(r, acc)`, then afterwards they represent
    `(r, (acc + leNat (bs ++ [1])) * r mod 2^130 - 5)`: exactly one iteration of `polyBlocks`
    (RFC 8439 §2.5.1) on a full 16-byte chunk. The block is only read. No stack is used. -/
def polyBlockContract : Spec (BitVec 64 × BitVec 64 × Bytes × Nat × Nat) where
  pre := fun (st, blk, bs, r, acc) s0 =>
    ∃∗ l : PolyLimbs,
      ⌜(s0.readReg64 .x0 = st ∧ s0.readReg64 .x1 = blk ∧ s0.readReg64 .x2 = 0#64 ∧
          bs.length = 16) ∧ l.Rep r acc⌝ ∗
      (blk ↦ₛ bs) ∗ polyLimbsAt st l
  post := fun (st, blk, bs, r, acc) _ _ =>
    ∃∗ l : PolyLimbs,
      ⌜l.Rep r ((acc + leNat (bs ++ [1])) * r % p1305)⌝ ∗ (blk ↦ₛ bs) ∗ polyLimbsAt st l

/-! ## Poly1305 finalisation -/

/-- Four little-endian 32-bit words at `p`. -/
def words4At (p : BitVec 64) (w0 w1 w2 w3 : BitVec 32) : SepProp :=
  (p ↦₃₂ w0) ∗ ((p + 4#64) ↦₃₂ w1) ∗ ((p + 8#64) ↦₃₂ w2) ∗ ((p + 12#64) ↦₃₂ w3)

/-- The 128-bit little-endian value of four 32-bit words. -/
def words4Val (w0 w1 w2 w3 : BitVec 32) : Nat :=
  w0.toNat + 2 ^ 32 * w1.toNat + 2 ^ 64 * w2.toNat + 2 ^ 96 * w3.toNat

/-- The demangled name of the Poly1305 finalisation in the pinned object. -/
def polyFinalizeSym : String := "<poly1305::Poly1305 as universal_hash::UniversalHash>::finalize"

/-- Ghost state of a `finalize` call: state pointer `st` (`x0`), output pointer `out` (`x8`,
    the AAPCS64 indirect-result register), the pad `s` stored at `st` as four words, the
    accumulator limbs `h` at `st + 0x24`, and the previous contents of the output. -/
structure PolyFinalArgs where
  st : BitVec 64
  out : BitVec 64
  (s0 s1 s2 s3 h0 h1 h2 h3 h4 o0 o1 o2 o3 : BitVec 32)

/-- Contract of `<Poly1305 as UniversalHash>::finalize(self) -> Tag`.

    If the accumulator limbs are within the representation bounds, the 16-byte tag written to
    `out` is `(acc mod (2^130 - 5) + s) mod 2^128` (RFC 8439 §2.5.1, the last step of
    `poly1305Mac`), where `acc` is the limbs' value and `s` the pad's. The state is only read. -/
def polyFinalContract : Spec PolyFinalArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.st ∧ s0.readReg64 .x8 = a.out ∧
      a.h0.toNat < 2 ^ 26 ∧ a.h1.toNat < 2 ^ 26 + 64 ∧ a.h2.toNat < 2 ^ 26 ∧
      a.h3.toNat < 2 ^ 26 ∧ a.h4.toNat < 2 ^ 26⌝ ∗
    words4At a.st a.s0 a.s1 a.s2 a.s3 ∗ limbsAt (a.st + 36#64) a.h0 a.h1 a.h2 a.h3 a.h4 ∗
    words4At a.out a.o0 a.o1 a.o2 a.o3
  post := fun a _ _ =>
    words4At a.st a.s0 a.s1 a.s2 a.s3 ∗ limbsAt (a.st + 36#64) a.h0 a.h1 a.h2 a.h3 a.h4 ∗
    ∃∗ t : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32,
      ⌜words4Val t.1 t.2.1 t.2.2.1 t.2.2.2 =
        (limbVal a.h0.toNat a.h1.toNat a.h2.toNat a.h3.toNat a.h4.toNat % p1305 +
          words4Val a.s0 a.s1 a.s2 a.s3) % 2 ^ 128⌝ ∗
      words4At a.out t.1 t.2.1 t.2.2.1 t.2.2.2

/-! ## Poly1305 key setup -/

/-- The demangled name of `Poly1305::new` in the pinned object. -/
def polyNewSym : String := "<poly1305::Poly1305 as crypto_common::KeyInit>::new"

/-- Contract of `<Poly1305 as KeyInit>::new(key: &[u8; 32]) -> Poly1305`.

    Ghosts: key pointer `k` (`x0`), output pointer `out` (`x8`, the indirect-result register,
    56 writable bytes) and the 32 key bytes `kb`.

    The new state holds the pad `s = leNat kb[16..32]` as four words at `out`, and limbs that
    represent the multiplier `clamp (leNat kb[0..16])` and the accumulator `0` (RFC 8439 §2.5.1).
    The key is only read. -/
def polyNewContract : Spec (BitVec 64 × BitVec 64 × Bytes) where
  pre := fun (k, out, kb) s0 =>
    ⌜s0.readReg64 .x0 = k ∧ s0.readReg64 .x8 = out ∧ kb.length = 32⌝ ∗
    (k ↦ₛ kb) ∗ memRegion out 56
  post := fun (k, out, kb) _ _ =>
    (k ↦ₛ kb) ∗
    ∃∗ w : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32, ∃∗ l : PolyLimbs,
      ⌜words4Val w.1 w.2.1 w.2.2.1 w.2.2.2 = leNat (kb.drop 16) ∧
        l.Rep (clamp (leNat (kb.take 16))) 0⌝ ∗
      words4At out w.1 w.2.1 w.2.2.1 w.2.2.2 ∗ polyLimbsAt out l

/-- The demangled name of `proc_block` (a full-block wrapper around `compute_block`). -/
def polyProcBlockSym : String :=
  "<poly1305::backend::soft::State as universal_hash::UhfBackend>::proc_block"

/-- Contract of `<State as UhfBackend>::proc_block(&mut self, block)`: `polyBlockContract`
    without the `partial` argument (the wrapper passes `false`). -/
def polyProcBlockContract : Spec (BitVec 64 × BitVec 64 × Bytes × Nat × Nat) where
  pre := fun (st, blk, bs, r, acc) s0 =>
    ∃∗ l : PolyLimbs,
      ⌜(s0.readReg64 .x0 = st ∧ s0.readReg64 .x1 = blk ∧ bs.length = 16) ∧ l.Rep r acc⌝ ∗
      (blk ↦ₛ bs) ∗ polyLimbsAt st l
  post := polyBlockContract.post

/-! ## Helpers: `subtle::black_box` and the cipher's drop glue -/

/-- The demangled name of `subtle::black_box::<u8>` in the pinned object. -/
def blackBoxSym : String := "subtle::black_box::<u8>"

/-- Contract of `subtle::black_box::<u8>(x: u8) -> u8` (an optimisation barrier used by the
    constant-time tag comparison): returns its argument, using a 16-byte stack frame. -/
def blackBoxContract : Spec (BitVec 8) where
  pre := fun b s0 => ⌜(s0.readReg64 .x0).truncate 8 = b⌝ ∗ stackFrame s0 16
  post := fun b s0 sf => ⌜sf.readReg64 .x0 = b.zeroExtend 64⌝ ∗ stackFrame s0 16

/-- The demangled name of the drop glue of RustCrypto's `chacha20poly1305::cipher::Cipher`. -/
def cipherDropSym : String :=
  "core::ptr::drop_glue::<chacha20poly1305::cipher::Cipher<cipher::stream_wrapper::StreamCipherCoreWrapper<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>>>>>"

/-- Contract of the `Cipher` drop glue: it owns the 129 bytes at offset `0x38` of the cipher
    (the ChaCha state and the key-stream buffer) and gives them back. (The code zeroises them;
    that memory-hygiene property is not claimed here.) -/
def cipherDropContract : Spec (BitVec 64) where
  pre := fun c s0 => ⌜s0.readReg64 .x0 = c⌝ ∗ memRegion (c + 56#64) 129
  post := fun c _ _ => memRegion (c + 56#64) 129

/-! ## The ChaCha20 stream cipher wrapper -/

/-- The demangled name of `StreamCipherCoreWrapper<ChaChaCore>::apply_keystream`. -/
def applyKeystreamSym : String :=
  "<cipher::stream_wrapper::StreamCipherCoreWrapper<chacha20::ChaChaCore<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UInt<typenum::uint::UTerm, typenum::bit::B1>, typenum::bit::B0>, typenum::bit::B1>, typenum::bit::B0>>> as cipher::stream::StreamCipher>::apply_keystream"

/-- Ghost state of an `apply_keystream` call: cipher pointer `c` (`x0`), data pointer `bufp`
    (`x1`), the data bytes, the ChaCha state `s` at `c`, and the key-stream buffer at `c + 0x40`. -/
structure ApplyKeystreamArgs where
  c : BitVec 64
  bufp : BitVec 64
  data : Bytes
  s : State
  buf : State

/-- Contract of `<StreamCipherCoreWrapper<ChaChaCore> as StreamCipher>::apply_keystream(&mut self,
    buf: &mut [u8])`, entered with an empty key-stream buffer (position byte `0` at `c + 0x80`),
    as both call sites in the AEAD do.

    Precondition: the data length fits the 32-bit block counter
    (`⌈len / 64⌉ + s.x12 < 2^32`); otherwise the code panics. The code uses `0x230` bytes of stack
    (its own `0x1a0`-byte frame and the `0x90` bytes the block function needs below it).

    Postcondition: the data is XORed with the key stream of `s` (`streamXor`, RFC 8439 §2.4 from
    an explicit state), the counter advanced by `⌈len / 64⌉`, and the buffer position is
    `len mod 64`. -/
def applyKeystreamContract : Spec ApplyKeystreamArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.c ∧ s0.readReg64 .x1 = a.bufp ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 a.data.length ∧ a.data.length < 2 ^ 63 ∧
      (a.data.length + 63) / 64 + a.s.x12.toNat < 2 ^ 32⌝ ∗
    stateAt a.c a.s ∗ stateAt (a.c + 0x40#64) a.buf ∗ ((a.c + 0x80#64) ↦₈ 0#8) ∗
    (a.bufp ↦ₛ a.data) ∗ stackFrame s0 0x230
  post := fun a s0 _ =>
    stateAt a.c (a.s.advance ((a.data.length + 63) / 64)) ∗
    (∃∗ b : State, stateAt (a.c + 0x40#64) b) ∗
    ((a.c + 0x80#64) ↦₈ BitVec.ofNat 8 (a.data.length % 64)) ∗
    (a.bufp ↦ₛ streamXor a.s a.data) ∗ stackFrame s0 0x230

/-! ## The AEAD entry points -/

/-- The C symbol of the encryption entry point. -/
def encryptSym : String := "chachapoly_encrypt"

/-- The C symbol of the decryption entry point. -/
def decryptSym : String := "chachapoly_decrypt"

/-- Largest message length the contracts admit: `64 · (2^32 − 1) − 64` bytes. Encryption
    starts the ChaCha20 block counter at 1, so this is the longest message whose key stream fits
    the 32-bit counter (`⌈len / 64⌉ + 1 < 2^32`). RustCrypto's own length guard
    (`P_MAX = 2^38 − 64`) rejects only lengths of at least `274,877,906,880`; on the 63 lengths in
    between the binary panics in `apply_keystream`, so they are excluded here. -/
def maxMsgLen : Nat := 274877906816

/-- The 16-byte ChaCha constant `"expand 32-byte k"` (RFC 8439 §2.3, words `0..3` of the state),
    which the entry points load from read-only data. -/
def sigmaBytes : Bytes :=
  [0x65, 0x78, 0x70, 0x61, 0x6e, 0x64, 0x20, 0x33, 0x32, 0x2d, 0x62, 0x79, 0x74, 0x65, 0x20, 0x6b]

/-- The data symbol, in the pinned library, of the read-only constant `sigmaBytes`. -/
def sigmaDataSym : String := "chachapoly_verified:.rodata.cst16+0x0"

/-- Ghost state of an entry-point call: the five pointers (`x0`, `x1`, `x2`, `x4`, `x6`) and the
    bytes behind them — key, nonce, associated data, the in-place buffer `msg` (plaintext for
    encryption, ciphertext for decryption) and the 16 tag bytes (previous contents of the output
    for encryption, the tag to check for decryption). -/
structure AeadArgs where
  key : BitVec 64
  nonce : BitVec 64
  aad : BitVec 64
  buf : BitVec 64
  tag : BitVec 64
  k : Bytes
  n : Bytes
  a : Bytes
  msg : Bytes
  t : Bytes

/-- The common precondition: argument registers per the C prototype
    `(key, nonce, aad, aad_len, buf, len, tag)`, lengths, and ownership of the five buffers as
    separate byte slices (so they do not overlap). -/
def aeadPre (g : AeadArgs) (s0 : Arm64.State) : SepProp :=
  ⌜s0.readReg64 .x0 = g.key ∧ s0.readReg64 .x1 = g.nonce ∧ s0.readReg64 .x2 = g.aad ∧
    s0.readReg64 .x3 = BitVec.ofNat 64 g.a.length ∧ s0.readReg64 .x4 = g.buf ∧
    s0.readReg64 .x5 = BitVec.ofNat 64 g.msg.length ∧ s0.readReg64 .x6 = g.tag ∧
    g.k.length = 32 ∧ g.n.length = 12 ∧ g.t.length = 16 ∧
    g.a.length < 2 ^ 63 ∧ g.msg.length ≤ maxMsgLen⌝ ∗
  (g.key ↦ₛ g.k) ∗ (g.nonce ↦ₛ g.n) ∗ (g.aad ↦ₛ g.a) ∗ (g.buf ↦ₛ g.msg) ∗ (g.tag ↦ₛ g.t)

/-- Contract of `chachapoly_encrypt` (RFC 8439 §2.8 AEAD encryption, in place, detached tag).

    It returns `0` (as a 32-bit `int`), the buffer holds the ciphertext and `tag` the tag of
    `aeadEncrypt key nonce aad msg`; key, nonce and associated data are unchanged. `sigma` is
    the address of the read-only constant `sigmaBytes` (in the library's `.rodata`; the headline
    theorems instantiate it with its placed address). Stack: the
    function's `0x270`-byte frame plus `0x230` bytes for `apply_keystream`. -/
def aeadEncryptContract (sigma : BitVec 64) : Spec AeadArgs where
  pre := fun g s0 => aeadPre g s0 ∗ (sigma ↦ᵣ sigmaBytes) ∗ stackFrame s0 0x4a0
  post := fun g s0 sf =>
    ⌜(sf.readReg64 .x0).truncate 32 = 0#32⌝ ∗ (sigma ↦ᵣ sigmaBytes) ∗
    (g.key ↦ₛ g.k) ∗ (g.nonce ↦ₛ g.n) ∗ (g.aad ↦ₛ g.a) ∗
    (g.buf ↦ₛ (aeadEncrypt g.k g.n g.a g.msg).1) ∗ (g.tag ↦ₛ (aeadEncrypt g.k g.n g.a g.msg).2) ∗
    stackFrame s0 0x4a0

/-- Contract of `chachapoly_decrypt` (RFC 8439 §2.8 AEAD decryption, in place, detached tag).

    If `aeadDecrypt key nonce aad msg tag` accepts with plaintext `p`, it returns `0` and the
    buffer holds `p`; if it rejects, it returns `-1` and the buffer is unchanged. All other
    inputs are unchanged. Stack: the function's `0x260`-byte frame plus `0x230` bytes for
    `apply_keystream`. -/
def aeadDecryptContract (sigma : BitVec 64) : Spec AeadArgs where
  pre := fun g s0 => aeadPre g s0 ∗ (sigma ↦ᵣ sigmaBytes) ∗ stackFrame s0 0x490
  post := fun g s0 sf =>
    (match aeadDecrypt g.k g.n g.a g.msg g.t with
      | some p => ⌜(sf.readReg64 .x0).truncate 32 = 0#32⌝ ∗ (g.buf ↦ₛ p)
      | none => ⌜(sf.readReg64 .x0).truncate 32 = 0xffffffff#32⌝ ∗ (g.buf ↦ₛ g.msg)) ∗
    (g.key ↦ₛ g.k) ∗ (g.nonce ↦ₛ g.n) ∗ (g.aad ↦ₛ g.a) ∗ (g.tag ↦ₛ g.t) ∗ (sigma ↦ᵣ sigmaBytes) ∗
    stackFrame s0 0x490

end ChaChaPoly.Spec
