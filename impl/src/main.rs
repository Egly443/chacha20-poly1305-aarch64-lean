//! `chachapoly-cli`: a minimal static executable that links the two verified entry points.
//!
//! It runs the RFC 8439 §2.8.2 AEAD test vector through `chachapoly_encrypt`, checks the
//! ciphertext tag, decrypts it again with `chachapoly_decrypt`, and checks that a one-bit
//! change to the ciphertext is rejected. Exit code `0` means all checks passed.
use chachapoly_verified::{chachapoly_decrypt, chachapoly_encrypt};
use std::process::ExitCode;

const KEY: [u8; 32] = [
    0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f,
    0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e, 0x9f,
];
const NONCE: [u8; 12] = [0x07, 0, 0, 0, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47];
const AAD: [u8; 12] = [0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7];
const PLAINTEXT: &[u8; 114] = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
const TAG: [u8; 16] = [
    0x1a, 0xe1, 0x0b, 0x59, 0x4f, 0x09, 0xe2, 0x6a, 0x7e, 0x90, 0x2e, 0xcb, 0xd0, 0x60, 0x06, 0x91,
];

fn main() -> ExitCode {
    let mut buf = *PLAINTEXT;
    let mut tag = [0u8; 16];
    let rc = unsafe {
        chachapoly_encrypt(&KEY, &NONCE, AAD.as_ptr(), AAD.len(), buf.as_mut_ptr(), buf.len(), &mut tag)
    };
    if rc != 0 || tag != TAG || buf[0] != 0xd3 {
        return ExitCode::from(1);
    }
    let mut bad = buf;
    bad[5] ^= 1;
    let rc = unsafe {
        chachapoly_decrypt(&KEY, &NONCE, AAD.as_ptr(), AAD.len(), bad.as_mut_ptr(), bad.len(), &tag)
    };
    if rc != -1 {
        return ExitCode::from(2);
    }
    let rc = unsafe {
        chachapoly_decrypt(&KEY, &NONCE, AAD.as_ptr(), AAD.len(), buf.as_mut_ptr(), buf.len(), &tag)
    };
    if rc != 0 || &buf != PLAINTEXT {
        return ExitCode::from(3);
    }
    ExitCode::SUCCESS
}
