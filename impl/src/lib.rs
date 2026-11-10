//! Thin C-ABI entry points over the unmodified RustCrypto `chacha20poly1305` crate (v0.10.1),
//! the IETF ChaCha20-Poly1305 AEAD of RFC 8439.
//!
//! Both entry points work in place on `buf[..len]` with a detached 16-byte tag, so no allocator
//! is involved. They are the two functions whose AArch64 machine code is verified in Lean.
#![no_std]

use chacha20poly1305::{aead::AeadInPlace, ChaCha20Poly1305, Key, KeyInit, Nonce, Tag};

/// Encrypts `buf[..len]` in place under `key`/`nonce` with associated data `aad[..aad_len]`
/// and writes the 16-byte tag to `tag`. Returns `0` on success and `-1` if the RustCrypto
/// length check rejects the input.
///
/// # Safety
/// `key`, `nonce`, `tag` must be valid for 32, 12 and 16 bytes; `aad` for `aad_len` bytes of
/// reads; `buf` for `len` bytes of reads and writes; `buf` and `tag` must not overlap the inputs.
#[no_mangle]
pub unsafe extern "C" fn chachapoly_encrypt(
    key: *const [u8; 32],
    nonce: *const [u8; 12],
    aad: *const u8,
    aad_len: usize,
    buf: *mut u8,
    len: usize,
    tag: *mut [u8; 16],
) -> i32 {
    let cipher = ChaCha20Poly1305::new(Key::from_slice(&*key));
    let aad = core::slice::from_raw_parts(aad, aad_len);
    let buf = core::slice::from_raw_parts_mut(buf, len);
    match cipher.encrypt_in_place_detached(Nonce::from_slice(&*nonce), aad, buf) {
        Ok(t) => {
            (*tag).copy_from_slice(&t);
            0
        }
        Err(_) => -1,
    }
}

/// Verifies `tag` over `aad[..aad_len]` and the ciphertext `buf[..len]`; on success decrypts
/// `buf[..len]` in place and returns `0`. On tag mismatch (or a rejected length) returns `-1`
/// and leaves `buf` unchanged.
///
/// # Safety
/// As for [`chachapoly_encrypt`], with `tag` valid for 16 bytes of reads.
#[no_mangle]
pub unsafe extern "C" fn chachapoly_decrypt(
    key: *const [u8; 32],
    nonce: *const [u8; 12],
    aad: *const u8,
    aad_len: usize,
    buf: *mut u8,
    len: usize,
    tag: *const [u8; 16],
) -> i32 {
    let cipher = ChaCha20Poly1305::new(Key::from_slice(&*key));
    let aad = core::slice::from_raw_parts(aad, aad_len);
    let buf = core::slice::from_raw_parts_mut(buf, len);
    match cipher.decrypt_in_place_detached(Nonce::from_slice(&*nonce), aad, buf, Tag::from_slice(&*tag)) {
        Ok(()) => 0,
        Err(_) => -1,
    }
}
