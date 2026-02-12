// SPDX-License-Identifier: PMPL-1.0-or-later

//! Encoding utilities: hex, base64, URL encoding.

const BASE64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

pub fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

pub fn hex_decode(input: &str) -> Result<Vec<u8>, String> {
    if !input.len().is_multiple_of(2) {
        return Err("hex string length must be even".to_string());
    }
    let mut out = Vec::with_capacity(input.len() / 2);
    let bytes = input.as_bytes();
    for i in (0..bytes.len()).step_by(2) {
        let chunk = std::str::from_utf8(&bytes[i..i + 2]).map_err(|_| "invalid utf8")?;
        let byte = u8::from_str_radix(chunk, 16).map_err(|_| "invalid hex")?;
        out.push(byte);
    }
    Ok(out)
}

pub fn base64_encode(bytes: &[u8]) -> String {
    let mut out = String::new();
    let mut i = 0usize;
    while i < bytes.len() {
        let b0 = bytes[i];
        let b1 = if i + 1 < bytes.len() { bytes[i + 1] } else { 0 };
        let b2 = if i + 2 < bytes.len() { bytes[i + 2] } else { 0 };

        let n = ((b0 as u32) << 16) | ((b1 as u32) << 8) | (b2 as u32);
        out.push(BASE64[((n >> 18) & 0x3f) as usize] as char);
        out.push(BASE64[((n >> 12) & 0x3f) as usize] as char);

        if i + 1 < bytes.len() {
            out.push(BASE64[((n >> 6) & 0x3f) as usize] as char);
        } else {
            out.push('=');
        }
        if i + 2 < bytes.len() {
            out.push(BASE64[(n & 0x3f) as usize] as char);
        } else {
            out.push('=');
        }
        i += 3;
    }
    out
}

pub fn base64_decode(input: &str) -> Result<Vec<u8>, String> {
    let clean = input.trim();
    if !clean.len().is_multiple_of(4) {
        return Err("invalid base64 length".to_string());
    }

    let mut out = Vec::with_capacity(clean.len() / 4 * 3);
    for chunk in clean.as_bytes().chunks_exact(4) {
        let mut sextets = [0u8; 4];
        let mut pad = 0usize;

        for (idx, ch) in chunk.iter().enumerate() {
            sextets[idx] = match *ch {
                b'A'..=b'Z' => ch - b'A',
                b'a'..=b'z' => ch - b'a' + 26,
                b'0'..=b'9' => ch - b'0' + 52,
                b'+' => 62,
                b'/' => 63,
                b'=' => {
                    pad += 1;
                    0
                }
                _ => return Err("invalid base64 character".to_string()),
            };
        }

        let n = ((sextets[0] as u32) << 18)
            | ((sextets[1] as u32) << 12)
            | ((sextets[2] as u32) << 6)
            | (sextets[3] as u32);
        out.push(((n >> 16) & 0xff) as u8);
        if pad < 2 {
            out.push(((n >> 8) & 0xff) as u8);
        }
        if pad < 1 {
            out.push((n & 0xff) as u8);
        }
    }
    Ok(out)
}

pub fn url_encode(input: &str) -> String {
    let mut out = String::new();
    for b in input.bytes() {
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'~' => {
                out.push(b as char)
            }
            b' ' => out.push('+'),
            _ => out.push_str(&format!("%{:02X}", b)),
        }
    }
    out
}

pub fn url_decode(input: &str) -> Result<String, String> {
    let bytes = input.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'+' => {
                out.push(b' ');
                i += 1;
            }
            b'%' => {
                if i + 2 >= bytes.len() {
                    return Err("incomplete percent sequence".to_string());
                }
                let hi = hex_nibble(bytes[i + 1]).ok_or("invalid percent encoding")?;
                let lo = hex_nibble(bytes[i + 2]).ok_or("invalid percent encoding")?;
                out.push((hi << 4) | lo);
                i += 3;
            }
            other => {
                out.push(other);
                i += 1;
            }
        }
    }
    String::from_utf8(out).map_err(|_| "decoded bytes are not valid utf8".to_string())
}

fn hex_nibble(ch: u8) -> Option<u8> {
    match ch {
        b'0'..=b'9' => Some(ch - b'0'),
        b'a'..=b'f' => Some(ch - b'a' + 10),
        b'A'..=b'F' => Some(ch - b'A' + 10),
        _ => None,
    }
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
    fn test_hex_roundtrip() {
        let bytes = b"eclexia";
        let hex = hex_encode(bytes);
        assert_eq!(expect_ok(hex_decode(&hex)), bytes);
    }

    #[test]
    fn test_base64_roundtrip() {
        let input = b"hello world";
        let encoded = base64_encode(input);
        assert_eq!(expect_ok(base64_decode(&encoded)), input);
    }

    #[test]
    fn test_url_roundtrip() {
        let encoded = url_encode("a b&c/%");
        assert_eq!(expect_ok(url_decode(&encoded)), "a b&c/%");
    }
}
