// SPDX-License-Identifier: PMPL-1.0-or-later

//! Compression abstractions with real codec backends and RLE fallback.

use std::io::Write;
use std::process::{Command, Stdio};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompressionAlgorithm {
    Gzip,
    Zstd,
    Brotli,
    Rle,
}

pub fn compress(input: &[u8], algo: CompressionAlgorithm) -> Result<Vec<u8>, String> {
    match algo {
        CompressionAlgorithm::Gzip => run_codec("gzip", &["-c", "-n"], input),
        CompressionAlgorithm::Zstd => run_codec("zstd", &["--quiet", "--stdout"], input),
        CompressionAlgorithm::Brotli => run_codec("brotli", &["--stdout"], input),
        CompressionAlgorithm::Rle => Ok(rle_compress(input)),
    }
}

pub fn decompress(input: &[u8], algo: CompressionAlgorithm) -> Result<Vec<u8>, String> {
    match algo {
        CompressionAlgorithm::Gzip => run_codec("gzip", &["-d", "-c"], input),
        CompressionAlgorithm::Zstd => {
            run_codec("zstd", &["--quiet", "--decompress", "--stdout"], input)
        }
        CompressionAlgorithm::Brotli => run_codec("brotli", &["--decompress", "--stdout"], input),
        CompressionAlgorithm::Rle => rle_decompress(input),
    }
}

fn run_codec(program: &str, args: &[&str], input: &[u8]) -> Result<Vec<u8>, String> {
    let mut child = Command::new(program)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn {}: {}", program, e))?;

    if let Some(stdin) = child.stdin.as_mut() {
        stdin
            .write_all(input)
            .map_err(|e| format!("failed to write {} stdin: {}", program, e))?;
    }

    let out = child
        .wait_with_output()
        .map_err(|e| format!("failed to wait {}: {}", program, e))?;

    if !out.status.success() {
        return Err(format!(
            "{} failed: {}",
            program,
            String::from_utf8_lossy(&out.stderr)
        ));
    }

    Ok(out.stdout)
}

fn rle_compress(input: &[u8]) -> Vec<u8> {
    if input.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < input.len() {
        let byte = input[i];
        let mut run = 1u8;
        while i + (run as usize) < input.len() && input[i + (run as usize)] == byte && run < u8::MAX
        {
            run += 1;
        }
        out.push(run);
        out.push(byte);
        i += run as usize;
    }
    out
}

fn rle_decompress(input: &[u8]) -> Result<Vec<u8>, String> {
    if !input.len().is_multiple_of(2) {
        return Err("invalid rle payload".to_string());
    }
    let mut out = Vec::new();
    for chunk in input.chunks_exact(2) {
        let count = chunk[0] as usize;
        let byte = chunk[1];
        out.extend(std::iter::repeat_n(byte, count));
    }
    Ok(out)
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

    fn command_exists(cmd: &str) -> bool {
        Command::new("sh")
            .arg("-c")
            .arg(format!("command -v {} >/dev/null 2>&1", cmd))
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    }

    #[test]
    fn test_rle_roundtrip() {
        let input = b"aaabbbbbccccccccdddd";
        let enc = expect_ok(compress(input, CompressionAlgorithm::Rle));
        let dec = expect_ok(decompress(&enc, CompressionAlgorithm::Rle));
        assert_eq!(dec, input);
    }

    #[test]
    fn test_gzip_roundtrip_when_available() {
        if !command_exists("gzip") {
            return;
        }
        let input = b"eclexia gzip codec test";
        let enc = expect_ok(compress(input, CompressionAlgorithm::Gzip));
        let dec = expect_ok(decompress(&enc, CompressionAlgorithm::Gzip));
        assert_eq!(dec, input);
    }

    #[test]
    fn test_zstd_roundtrip_when_available() {
        if !command_exists("zstd") {
            return;
        }
        let input = b"eclexia zstd codec test";
        let enc = expect_ok(compress(input, CompressionAlgorithm::Zstd));
        let dec = expect_ok(decompress(&enc, CompressionAlgorithm::Zstd));
        assert_eq!(dec, input);
    }

    #[test]
    fn test_brotli_roundtrip_when_available() {
        if !command_exists("brotli") {
            return;
        }
        let input = b"eclexia brotli codec test";
        let enc = expect_ok(compress(input, CompressionAlgorithm::Brotli));
        let dec = expect_ok(decompress(&enc, CompressionAlgorithm::Brotli));
        assert_eq!(dec, input);
    }
}
