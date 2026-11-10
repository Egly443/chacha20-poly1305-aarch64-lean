module

public import ChaChaPoly.Spec.RFC8439

/-!
# The AEAD construction over abstract primitives, and its idealised (symbolic) model

RFC 8439 §2.8 builds the AEAD from three primitives: a stream cipher, a one-time-key
derivation, and a one-time MAC. `Aead.encrypt` / `Aead.decrypt` state that construction once,
for any primitives `P : Prims Tag`; `rfcPrims` instantiates it with the real ChaCha20 and
Poly1305 of `Spec/RFC8439.lean` (and `aeadEncrypt_eq` / `aeadDecrypt_eq` show this is exactly
the RFC model the machine code is proved to compute).

The *symbolic* model idealises the MAC: `Prims.IdealMac` says that, under one key, two
different messages never have the same tag. Real Poly1305 cannot satisfy this (its tags are
16 bytes), so the integrity theorem is a statement about the construction, not a computational
security bound: it rules out every forgery that does not go through a collision of the MAC.
`idealPrims` shows the assumption is satisfiable.
-/

@[expose] public section

namespace ChaChaPoly.Spec

/-- The primitives of the AEAD construction, with an abstract tag type. -/
structure Prims (Tag : Type) where
  /-- XOR `data` with the key stream for `(key, nonce)` starting at block counter 1. -/
  stream : (key nonce data : Bytes) → Bytes
  /-- The one-time MAC key for `(key, nonce)`. -/
  macKey : (key nonce : Bytes) → Bytes
  /-- The one-time MAC of a message under a MAC key. -/
  mac : (macKey msg : Bytes) → Tag

namespace Aead

variable {Tag : Type}

/-- AEAD encryption (§2.8) over primitives `P`. -/
def encrypt (P : Prims Tag) (key nonce aad plaintext : Bytes) : Bytes × Tag :=
  let ct := P.stream key nonce plaintext
  (ct, P.mac (P.macKey key nonce) (macData aad ct))

/-- AEAD decryption (§2.8) over primitives `P`. -/
def decrypt [DecidableEq Tag] (P : Prims Tag) (key nonce aad ct : Bytes) (tag : Tag) :
    Option Bytes :=
  if P.mac (P.macKey key nonce) (macData aad ct) = tag then some (P.stream key nonce ct) else none

end Aead

/-- The real primitives: ChaCha20 with initial counter 1, the §2.6 key generator, Poly1305. -/
def rfcPrims : Prims Bytes where
  stream key nonce data := chacha20Encrypt key 1 nonce data
  macKey := poly1305KeyGen
  mac := poly1305Mac

/-- Idealised MAC: under one MAC key, distinct messages have distinct tags. -/
def Prims.IdealMac {Tag : Type} (P : Prims Tag) : Prop :=
  ∀ k m m', P.mac k m = P.mac k m' → m = m'

/-- A free ("term algebra") MAC: the tag is the pair of key and message. With any stream
    cipher it satisfies `IdealMac`, so the symbolic model is not vacuous. -/
def idealPrims (stream : Bytes → Bytes → Bytes → Bytes) (macKey : Bytes → Bytes → Bytes) :
    Prims (Bytes × Bytes) where
  stream := stream
  macKey := macKey
  mac k m := (k, m)

/-- Lengths the AEAD can authenticate: both fit the 64-bit length fields of §2.8. -/
def LengthsOk (aad ct : Bytes) : Prop := aad.length < 2 ^ 64 ∧ ct.length < 2 ^ 64

end ChaChaPoly.Spec
