// SPDX-License-Identifier: PMPL-1.0-or-later

//! Authentication helpers with HS256 JWT-compatible token support.

use base64::engine::general_purpose::URL_SAFE_NO_PAD;
use base64::Engine;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Claims {
    pub sub: String,
    pub exp: u64,
    pub iat: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub iss: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub aud: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct JwtHeader {
    alg: String,
    typ: String,
}

impl JwtHeader {
    fn hs256() -> Self {
        Self {
            alg: "HS256".to_string(),
            typ: "JWT".to_string(),
        }
    }
}

/// Mint a JWT-compatible HS256 token from claims.
pub fn mint_hs256(claims: &Claims, secret: &[u8]) -> Result<String, String> {
    if secret.is_empty() {
        return Err("secret must not be empty".to_string());
    }

    let header = serde_json::to_vec(&JwtHeader::hs256()).map_err(|e| e.to_string())?;
    let payload = serde_json::to_vec(claims).map_err(|e| e.to_string())?;

    let header_b64 = URL_SAFE_NO_PAD.encode(header);
    let payload_b64 = URL_SAFE_NO_PAD.encode(payload);
    let signing_input = format!("{}.{}", header_b64, payload_b64);
    let sig = hmac_sha256(signing_input.as_bytes(), secret);
    let sig_b64 = URL_SAFE_NO_PAD.encode(sig);

    Ok(format!("{}.{}", signing_input, sig_b64))
}

/// Verify an HS256 token and return decoded claims.
pub fn verify_hs256(token: &str, secret: &[u8]) -> Result<Claims, String> {
    if secret.is_empty() {
        return Err("secret must not be empty".to_string());
    }

    let mut parts = token.split('.');
    let header_b64 = parts.next().ok_or("missing jwt header")?;
    let payload_b64 = parts.next().ok_or("missing jwt payload")?;
    let sig_b64 = parts.next().ok_or("missing jwt signature")?;
    if parts.next().is_some() {
        return Err("jwt must have exactly 3 segments".to_string());
    }

    let header_raw = URL_SAFE_NO_PAD
        .decode(header_b64)
        .map_err(|_| "invalid header b64")?;
    let header: JwtHeader =
        serde_json::from_slice(&header_raw).map_err(|_| "invalid jwt header json")?;
    if header.alg != "HS256" || header.typ != "JWT" {
        return Err("unsupported jwt header".to_string());
    }

    let signing_input = format!("{}.{}", header_b64, payload_b64);
    let expected_sig = hmac_sha256(signing_input.as_bytes(), secret);
    let got_sig = URL_SAFE_NO_PAD
        .decode(sig_b64)
        .map_err(|_| "invalid signature b64")?;

    if !constant_time_eq(&expected_sig, &got_sig) {
        return Err("invalid signature".to_string());
    }

    let payload_raw = URL_SAFE_NO_PAD
        .decode(payload_b64)
        .map_err(|_| "invalid payload b64")?;
    let claims: Claims = serde_json::from_slice(&payload_raw).map_err(|_| "invalid claims json")?;

    let now = now_secs();
    if claims.exp < now {
        return Err("token expired".to_string());
    }

    Ok(claims)
}

/// Backward-compatible wrapper for older API shape.
pub fn mint_token(subject: &str, ttl_secs: u64, secret: &str) -> String {
    let now = now_secs();
    let claims = Claims {
        sub: subject.to_string(),
        iat: now,
        exp: now.saturating_add(ttl_secs),
        iss: None,
        aud: None,
    };
    mint_hs256(&claims, secret.as_bytes()).unwrap_or_default()
}

/// Backward-compatible wrapper for older API shape.
pub fn verify_token(token: &str, secret: &str) -> Result<Claims, String> {
    verify_hs256(token, secret.as_bytes())
}

fn hmac_sha256(message: &[u8], key: &[u8]) -> [u8; 32] {
    // RFC 2104 HMAC with SHA-256.
    const BLOCK_SIZE: usize = 64;

    let mut key_block = [0u8; BLOCK_SIZE];
    if key.len() > BLOCK_SIZE {
        let mut hasher = Sha256::new();
        hasher.update(key);
        let digest = hasher.finalize();
        key_block[..32].copy_from_slice(&digest);
    } else {
        key_block[..key.len()].copy_from_slice(key);
    }

    let mut o_key_pad = [0u8; BLOCK_SIZE];
    let mut i_key_pad = [0u8; BLOCK_SIZE];
    for i in 0..BLOCK_SIZE {
        o_key_pad[i] = key_block[i] ^ 0x5c;
        i_key_pad[i] = key_block[i] ^ 0x36;
    }

    let mut inner = Sha256::new();
    inner.update(i_key_pad);
    inner.update(message);
    let inner_hash = inner.finalize();

    let mut outer = Sha256::new();
    outer.update(o_key_pad);
    outer.update(inner_hash);
    let result = outer.finalize();

    let mut out = [0u8; 32];
    out.copy_from_slice(&result);
    out
}

fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(val) => val,
            Err(err) => panic!("Expected Ok, got Err: {:?}", err),
        }
    }

    #[test]
    fn test_mint_and_verify_hs256() {
        let now = now_secs();
        let claims = Claims {
            sub: "alice".to_string(),
            iat: now,
            exp: now + 30,
            iss: Some("eclexia".to_string()),
            aud: None,
        };

        let token = expect_ok(mint_hs256(&claims, b"secret"));
        let verified = expect_ok(verify_hs256(&token, b"secret"));
        assert_eq!(verified.sub, "alice");
        assert_eq!(verified.iss, Some("eclexia".to_string()));
    }

    #[test]
    fn test_reject_bad_signature() {
        let token = mint_token("alice", 30, "secret-a");
        assert!(verify_token(&token, "secret-b").is_err());
    }

    #[test]
    fn test_reject_expired() {
        let now = now_secs();
        let claims = Claims {
            sub: "old".to_string(),
            iat: now.saturating_sub(10),
            exp: now.saturating_sub(1),
            iss: None,
            aud: None,
        };
        let token = expect_ok(mint_hs256(&claims, b"secret"));
        assert!(verify_hs256(&token, b"secret").is_err());
    }
}
