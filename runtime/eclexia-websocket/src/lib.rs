// SPDX-License-Identifier: PMPL-1.0-or-later

//! RFC6455-compatible websocket frame codec.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpCode {
    Continuation = 0x0,
    Text = 0x1,
    Binary = 0x2,
    Close = 0x8,
    Ping = 0x9,
    Pong = 0xA,
}

impl OpCode {
    fn parse(tag: u8) -> Result<Self, String> {
        match tag {
            0x0 => Ok(Self::Continuation),
            0x1 => Ok(Self::Text),
            0x2 => Ok(Self::Binary),
            0x8 => Ok(Self::Close),
            0x9 => Ok(Self::Ping),
            0xA => Ok(Self::Pong),
            _ => Err(format!("unsupported websocket opcode 0x{:x}", tag)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Frame {
    pub fin: bool,
    pub opcode: OpCode,
    pub payload: Vec<u8>,
}

impl Frame {
    pub fn text(payload: impl Into<Vec<u8>>) -> Self {
        Self {
            fin: true,
            opcode: OpCode::Text,
            payload: payload.into(),
        }
    }
}

/// Encode a websocket frame.
///
/// Pass `Some(mask_key)` for client-style masked frames.
pub fn encode(frame: &Frame, mask_key: Option<[u8; 4]>) -> Vec<u8> {
    let mut out = Vec::with_capacity(2 + frame.payload.len());
    let b0 = (if frame.fin { 0x80 } else { 0x00 }) | (frame.opcode as u8);
    out.push(b0);

    let masked = mask_key.is_some();
    let len = frame.payload.len();
    if len <= 125 {
        out.push((if masked { 0x80 } else { 0x00 }) | (len as u8));
    } else if u16::try_from(len).is_ok() {
        out.push((if masked { 0x80 } else { 0x00 }) | 126);
        out.extend_from_slice(&(len as u16).to_be_bytes());
    } else {
        out.push((if masked { 0x80 } else { 0x00 }) | 127);
        out.extend_from_slice(&(len as u64).to_be_bytes());
    }

    if let Some(mask) = mask_key {
        out.extend_from_slice(&mask);
        for (idx, byte) in frame.payload.iter().enumerate() {
            out.push(byte ^ mask[idx % 4]);
        }
    } else {
        out.extend_from_slice(&frame.payload);
    }
    out
}

/// Decode a websocket frame from a byte slice.
/// Returns `(frame, consumed_bytes)`.
pub fn decode(raw: &[u8]) -> Result<(Frame, usize), String> {
    if raw.len() < 2 {
        return Err("frame too short".to_string());
    }

    let b0 = raw[0];
    let fin = (b0 & 0x80) != 0;
    let opcode = OpCode::parse(b0 & 0x0f)?;

    let b1 = raw[1];
    let masked = (b1 & 0x80) != 0;
    let mut payload_len = (b1 & 0x7f) as usize;
    let mut offset = 2usize;

    if payload_len == 126 {
        if raw.len() < offset + 2 {
            return Err("frame missing extended length".to_string());
        }
        payload_len = u16::from_be_bytes([raw[offset], raw[offset + 1]]) as usize;
        offset += 2;
    } else if payload_len == 127 {
        if raw.len() < offset + 8 {
            return Err("frame missing extended length".to_string());
        }
        payload_len = u64::from_be_bytes([
            raw[offset],
            raw[offset + 1],
            raw[offset + 2],
            raw[offset + 3],
            raw[offset + 4],
            raw[offset + 5],
            raw[offset + 6],
            raw[offset + 7],
        ]) as usize;
        offset += 8;
    }

    let mask = if masked {
        if raw.len() < offset + 4 {
            return Err("frame missing mask".to_string());
        }
        let key = [
            raw[offset],
            raw[offset + 1],
            raw[offset + 2],
            raw[offset + 3],
        ];
        offset += 4;
        Some(key)
    } else {
        None
    };

    if raw.len() < offset + payload_len {
        return Err("frame truncated payload".to_string());
    }

    let mut payload = raw[offset..offset + payload_len].to_vec();
    if let Some(mask_key) = mask {
        for (idx, byte) in payload.iter_mut().enumerate() {
            *byte ^= mask_key[idx % 4];
        }
    }

    Ok((
        Frame {
            fin,
            opcode,
            payload,
        },
        offset + payload_len,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundtrip_unmasked_text() {
        let frame = Frame::text(b"hello".to_vec());
        let encoded = encode(&frame, None);
        let (decoded, consumed) = decode(&encoded).expect("decode failed");
        assert_eq!(consumed, encoded.len());
        assert_eq!(decoded, frame);
    }

    #[test]
    fn test_roundtrip_masked_binary() {
        let frame = Frame {
            fin: true,
            opcode: OpCode::Binary,
            payload: vec![1, 2, 3, 4, 5],
        };
        let encoded = encode(&frame, Some([0x11, 0x22, 0x33, 0x44]));
        let (decoded, _) = decode(&encoded).expect("decode failed");
        assert_eq!(decoded.payload, frame.payload);
        assert_eq!(decoded.opcode, OpCode::Binary);
    }

    #[test]
    fn test_large_payload_uses_extended_length() {
        let payload = vec![42u8; 256];
        let frame = Frame {
            fin: true,
            opcode: OpCode::Binary,
            payload: payload.clone(),
        };
        let encoded = encode(&frame, None);
        assert_eq!(encoded[1] & 0x7f, 126);
        let (decoded, _) = decode(&encoded).expect("decode failed");
        assert_eq!(decoded.payload, payload);
    }
}
