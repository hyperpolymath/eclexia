// SPDX-License-Identifier: PMPL-1.0-or-later

//! UUID v4 generation and validation.

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static FALLBACK_COUNTER: AtomicU64 = AtomicU64::new(1);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Uuid([u8; 16]);

impl Uuid {
    pub fn new_v4() -> Self {
        let mut bytes = [0u8; 16];
        fill_random(&mut bytes);

        // Set version (4) and variant (RFC4122).
        bytes[6] = (bytes[6] & 0x0f) | 0x40;
        bytes[8] = (bytes[8] & 0x3f) | 0x80;
        Self(bytes)
    }

    pub fn parse(input: &str) -> Result<Self, String> {
        let normalized = input.trim();
        let parts = normalized.split('-').collect::<Vec<_>>();
        if parts.len() != 5
            || parts[0].len() != 8
            || parts[1].len() != 4
            || parts[2].len() != 4
            || parts[3].len() != 4
            || parts[4].len() != 12
        {
            return Err("invalid uuid shape".to_string());
        }

        let compact = parts.concat();
        if compact.len() != 32 {
            return Err("invalid uuid length".to_string());
        }
        let mut bytes = [0u8; 16];
        for (i, byte) in bytes.iter_mut().enumerate() {
            let idx = i * 2;
            let pair = &compact[idx..idx + 2];
            *byte = u8::from_str_radix(pair, 16).map_err(|_| "invalid hex digit in uuid")?;
        }
        Ok(Self(bytes))
    }

    pub fn as_bytes(&self) -> &[u8; 16] {
        &self.0
    }

    pub fn is_v4(&self) -> bool {
        (self.0[6] >> 4) == 0x4
    }

    pub fn is_rfc4122_variant(&self) -> bool {
        (self.0[8] & 0b1100_0000) == 0b1000_0000
    }
}

impl std::fmt::Display for Uuid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let b = &self.0;
        write!(
            f,
            "{:02x}{:02x}{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
            b[0],
            b[1],
            b[2],
            b[3],
            b[4],
            b[5],
            b[6],
            b[7],
            b[8],
            b[9],
            b[10],
            b[11],
            b[12],
            b[13],
            b[14],
            b[15]
        )
    }
}

/// Backward-compatible helper.
pub fn new_v4_like() -> String {
    Uuid::new_v4().to_string()
}

pub fn is_valid_uuid(input: &str) -> bool {
    Uuid::parse(input).is_ok()
}

fn fill_random(out: &mut [u8; 16]) {
    if read_os_random(out).is_ok() {
        return;
    }

    // Fallback for environments without /dev/urandom.
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos() as u64;
    let ctr = FALLBACK_COUNTER.fetch_add(1, Ordering::Relaxed);
    let mut state = nanos ^ ctr.rotate_left(17) ^ 0x9e3779b97f4a7c15;

    for chunk in out.chunks_mut(8) {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let bytes = state.to_be_bytes();
        let n = chunk.len();
        chunk.copy_from_slice(&bytes[..n]);
    }
}

fn read_os_random(out: &mut [u8; 16]) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::io::Read;
        let mut file = std::fs::File::open("/dev/urandom")
            .map_err(|e| format!("failed to open /dev/urandom: {}", e))?;
        file.read_exact(out)
            .map_err(|e| format!("failed to read /dev/urandom: {}", e))
    }
    #[cfg(not(unix))]
    {
        Err("os random not supported on this platform".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_uuid_shape_and_version() {
        let id = Uuid::new_v4();
        let text = id.to_string();
        assert_eq!(text.len(), 36);
        assert_eq!(text.chars().filter(|c| *c == '-').count(), 4);
        assert!(id.is_v4());
        assert!(id.is_rfc4122_variant());
    }

    #[test]
    fn test_parse_roundtrip() {
        let original = Uuid::new_v4();
        let parsed = Uuid::parse(&original.to_string()).expect("parse failed");
        assert_eq!(original, parsed);
    }

    #[test]
    fn test_invalid_uuid() {
        assert!(!is_valid_uuid("not-a-uuid"));
        assert!(!is_valid_uuid("deadbeef"));
    }
}
