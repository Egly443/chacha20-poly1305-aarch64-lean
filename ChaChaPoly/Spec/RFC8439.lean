module

/-!
# IETF ChaCha20-Poly1305 (RFC 8439): reference model

A direct, executable transcription of RFC 8439 into Lean 4, using only Lean core (`BitVec`,
`Nat`, `List`). Section numbers refer to RFC 8439. This file is part of the trusted
specification: it is what the machine code is proved to compute. `Spec/RFC8439Vectors.lean`
checks it against the RFC's own test vectors in the Lean kernel.

Conventions: a byte string is a `List (BitVec 8)`; multi-byte integers are little-endian.
Functions are total; where the RFC fixes a length (32-byte key, 12-byte nonce) the functions
read missing bytes as `0`, and the machine-code contracts only use them at the right lengths.
-/

@[expose] public section

namespace ChaChaPoly.Spec

abbrev Byte := BitVec 8
abbrev Bytes := List Byte

/-! ## Little-endian encodings -/

/-- The natural number a byte string denotes, little-endian. -/
def leNat : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- The `len`-byte little-endian encoding of `n` (of `n mod 256^len`). -/
def natLe : (len : Nat) → Nat → Bytes
  | 0, _ => []
  | len + 1, n => BitVec.ofNat 8 n :: natLe len (n / 256)

/-- Byte `i` of a byte string, `0` beyond its end. -/
def byteAt (bs : Bytes) (i : Nat) : Byte := bs.getD i 0

/-- The little-endian 32-bit word at byte offset `off`. -/
def word32At (bs : Bytes) (off : Nat) : BitVec 32 :=
  byteAt bs (off + 3) ++ byteAt bs (off + 2) ++ byteAt bs (off + 1) ++ byteAt bs off

/-- The four little-endian bytes of a 32-bit word. -/
def word32Bytes (w : BitVec 32) : Bytes :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-! ## ChaCha20 (§2.1–§2.4) -/

/-- The ChaCha quarter round (§2.1). -/
def quarterRound (a b c d : BitVec 32) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let a := a + b; let d := (d ^^^ a).rotateLeft 16
  let c := c + d; let b := (b ^^^ c).rotateLeft 12
  let a := a + b; let d := (d ^^^ a).rotateLeft 8
  let c := c + d; let b := (b ^^^ c).rotateLeft 7
  (a, b, c, d)

/-- The ChaCha state: sixteen 32-bit words (§2.3). -/
structure State where
  (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : BitVec 32)
deriving DecidableEq

/-- One column round followed by one diagonal round (§2.3.1 `inner_block`). -/
def doubleRound (s : State) : State :=
  let (x0, x4, x8, x12) := quarterRound s.x0 s.x4 s.x8 s.x12
  let (x1, x5, x9, x13) := quarterRound s.x1 s.x5 s.x9 s.x13
  let (x2, x6, x10, x14) := quarterRound s.x2 s.x6 s.x10 s.x14
  let (x3, x7, x11, x15) := quarterRound s.x3 s.x7 s.x11 s.x15
  let (x0, x5, x10, x15) := quarterRound x0 x5 x10 x15
  let (x1, x6, x11, x12) := quarterRound x1 x6 x11 x12
  let (x2, x7, x8, x13) := quarterRound x2 x7 x8 x13
  let (x3, x4, x9, x14) := quarterRound x3 x4 x9 x14
  ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩

/-- `f` applied `n` times. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => iter f n (f a)

/-- The initial state for a 32-byte `key`, 32-bit block `counter` and 12-byte `nonce` (§2.3). -/
def initState (key : Bytes) (counter : BitVec 32) (nonce : Bytes) : State :=
  ⟨0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
   word32At key 0, word32At key 4, word32At key 8, word32At key 12,
   word32At key 16, word32At key 20, word32At key 24, word32At key 28,
   counter, word32At nonce 0, word32At nonce 4, word32At nonce 8⟩

/-- Word-wise addition of two states. -/
def State.add (s t : State) : State :=
  ⟨s.x0 + t.x0, s.x1 + t.x1, s.x2 + t.x2, s.x3 + t.x3, s.x4 + t.x4, s.x5 + t.x5, s.x6 + t.x6,
   s.x7 + t.x7, s.x8 + t.x8, s.x9 + t.x9, s.x10 + t.x10, s.x11 + t.x11, s.x12 + t.x12,
   s.x13 + t.x13, s.x14 + t.x14, s.x15 + t.x15⟩

/-- The 64-byte little-endian serialization of a state. -/
def State.bytes (s : State) : Bytes :=
  word32Bytes s.x0 ++ word32Bytes s.x1 ++ word32Bytes s.x2 ++ word32Bytes s.x3 ++
  word32Bytes s.x4 ++ word32Bytes s.x5 ++ word32Bytes s.x6 ++ word32Bytes s.x7 ++
  word32Bytes s.x8 ++ word32Bytes s.x9 ++ word32Bytes s.x10 ++ word32Bytes s.x11 ++
  word32Bytes s.x12 ++ word32Bytes s.x13 ++ word32Bytes s.x14 ++ word32Bytes s.x15

/-- The ChaCha20 block function (§2.3): 20 rounds (10 double rounds), then add the input state
    and serialize. Returns 64 bytes of key stream. -/
def chacha20Block (key : Bytes) (counter : BitVec 32) (nonce : Bytes) : Bytes :=
  let s := initState key counter nonce
  ((iter doubleRound 10 s).add s).bytes

/-- Byte-wise XOR of `data` with the key stream `ks` (truncated to the shorter of the two). -/
def xorBytes (data ks : Bytes) : Bytes := List.zipWith (· ^^^ ·) data ks

/-- ChaCha20 encryption (§2.4): XOR `data` with the key stream of blocks `counter`,
    `counter + 1`, …. Decryption is the same function. -/
def chacha20Encrypt (key : Bytes) (counter : BitVec 32) (nonce : Bytes) (data : Bytes) : Bytes :=
  if _ : data.length ≤ 64 then
    xorBytes data (chacha20Block key counter nonce)
  else
    xorBytes (data.take 64) (chacha20Block key counter nonce) ++
      chacha20Encrypt key (counter + 1) nonce (data.drop 64)
termination_by data.length
decreasing_by simp only [List.length_drop]; omega

/-! ## Poly1305 (§2.5) -/

/-- The prime `2^130 - 5`. -/
def p1305 : Nat := 2 ^ 130 - 5

/-- Clamping of the multiplier `r` (§2.5.1). -/
def clamp (r : Nat) : Nat := r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- Absorb `msg` in 16-byte chunks into the accumulator `acc` (§2.5.1): each chunk, with a `1`
    byte appended, is added as a little-endian number and the sum is multiplied by `r` mod `p`. -/
def polyBlocks (r : Nat) (acc : Nat) (msg : Bytes) : Nat :=
  if h : msg = [] then acc
  else polyBlocks r ((acc + leNat (msg.take 16 ++ [1])) * r % p1305) (msg.drop 16)
termination_by msg.length
decreasing_by
  simp only [List.length_drop]
  have : 0 < msg.length := List.length_pos_iff.mpr h
  omega

/-- The Poly1305 one-time authenticator (§2.5): `key` is 32 bytes (`r ‖ s`), the tag 16 bytes. -/
def poly1305Mac (key : Bytes) (msg : Bytes) : Bytes :=
  let r := clamp (leNat (key.take 16))
  let s := leNat ((key.drop 16).take 16)
  natLe 16 (polyBlocks r 0 msg + s)

/-- The one-time Poly1305 key (§2.6): the first 32 bytes of key-stream block `0`. -/
def poly1305KeyGen (key nonce : Bytes) : Bytes := (chacha20Block key 0 nonce).take 32

/-! ## AEAD construction (§2.8) -/

/-- Zero padding of `data` up to a multiple of 16 bytes. -/
def pad16 (data : Bytes) : Bytes := List.replicate ((16 - data.length % 16) % 16) 0

/-- The byte string that is authenticated (§2.8):
    `aad ‖ pad16(aad) ‖ ct ‖ pad16(ct) ‖ le64(|aad|) ‖ le64(|ct|)`. -/
def macData (aad ct : Bytes) : Bytes :=
  aad ++ pad16 aad ++ ct ++ pad16 ct ++ natLe 8 aad.length ++ natLe 8 ct.length

/-- AEAD encryption (§2.8): returns the ciphertext and the 16-byte tag. -/
def aeadEncrypt (key nonce aad plaintext : Bytes) : Bytes × Bytes :=
  let ct := chacha20Encrypt key 1 nonce plaintext
  (ct, poly1305Mac (poly1305KeyGen key nonce) (macData aad ct))

/-- AEAD decryption (§2.8): `some plaintext` if `tag` is the tag of `(aad, ct)`, else `none`. -/
def aeadDecrypt (key nonce aad ct tag : Bytes) : Option Bytes :=
  if poly1305Mac (poly1305KeyGen key nonce) (macData aad ct) = tag then
    some (chacha20Encrypt key 1 nonce ct)
  else none

end ChaChaPoly.Spec
