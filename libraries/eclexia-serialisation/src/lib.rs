// SPDX-License-Identifier: PMPL-1.0-or-later

//! Serialization helpers for JSON, MessagePack, CBOR, and Protobuf envelope.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Format {
    Json,
    MessagePack,
    Cbor,
    Protobuf,
}

pub fn encode_json(value: &serde_json::Value) -> Result<Vec<u8>, String> {
    serde_json::to_vec(value).map_err(|e| e.to_string())
}

pub fn decode_json(bytes: &[u8]) -> Result<serde_json::Value, String> {
    serde_json::from_slice(bytes).map_err(|e| e.to_string())
}

pub fn encode_with_format(value: &serde_json::Value, format: Format) -> Result<Vec<u8>, String> {
    match format {
        Format::Json => encode_json(value),
        Format::MessagePack => encode_msgpack(value),
        Format::Cbor => encode_cbor(value),
        Format::Protobuf => encode_protobuf_json_envelope(value),
    }
}

pub fn decode_with_format(bytes: &[u8], format: Format) -> Result<serde_json::Value, String> {
    match format {
        Format::Json => decode_json(bytes),
        Format::MessagePack => decode_msgpack(bytes),
        Format::Cbor => decode_cbor(bytes),
        Format::Protobuf => decode_protobuf_json_envelope(bytes),
    }
}

pub fn encode_msgpack(value: &serde_json::Value) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    encode_msgpack_value(value, &mut out)?;
    Ok(out)
}

pub fn decode_msgpack(bytes: &[u8]) -> Result<serde_json::Value, String> {
    let mut idx = 0usize;
    let value = decode_msgpack_value(bytes, &mut idx)?;
    if idx != bytes.len() {
        return Err("trailing bytes in msgpack payload".to_string());
    }
    Ok(value)
}

pub fn encode_cbor(value: &serde_json::Value) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    encode_cbor_value(value, &mut out)?;
    Ok(out)
}

pub fn decode_cbor(bytes: &[u8]) -> Result<serde_json::Value, String> {
    let mut idx = 0usize;
    let value = decode_cbor_value(bytes, &mut idx)?;
    if idx != bytes.len() {
        return Err("trailing bytes in cbor payload".to_string());
    }
    Ok(value)
}

/// Protobuf envelope schema:
/// message JsonEnvelope { string json = 1; }
pub fn encode_protobuf_json_envelope(value: &serde_json::Value) -> Result<Vec<u8>, String> {
    let json = serde_json::to_string(value).map_err(|e| e.to_string())?;
    let mut out = Vec::new();
    out.push(0x0a); // field 1, wire type 2 (len-delimited)
    write_varint(json.len() as u64, &mut out);
    out.extend_from_slice(json.as_bytes());
    Ok(out)
}

pub fn decode_protobuf_json_envelope(bytes: &[u8]) -> Result<serde_json::Value, String> {
    if bytes.is_empty() || bytes[0] != 0x0a {
        return Err("invalid protobuf envelope: expected field 1 string".to_string());
    }
    let mut idx = 1usize;
    let len = read_varint(bytes, &mut idx)? as usize;
    if idx + len > bytes.len() {
        return Err("invalid protobuf envelope length".to_string());
    }
    let payload = &bytes[idx..idx + len];
    decode_json(payload)
}

fn encode_msgpack_value(value: &serde_json::Value, out: &mut Vec<u8>) -> Result<(), String> {
    match value {
        serde_json::Value::Null => out.push(0xc0),
        serde_json::Value::Bool(false) => out.push(0xc2),
        serde_json::Value::Bool(true) => out.push(0xc3),
        serde_json::Value::Number(n) => {
            if let Some(u) = n.as_u64() {
                encode_msgpack_uint(u, out);
            } else if let Some(i) = n.as_i64() {
                encode_msgpack_int(i, out);
            } else if let Some(f) = n.as_f64() {
                out.push(0xcb);
                out.extend_from_slice(&f.to_be_bytes());
            } else {
                return Err("unsupported number representation".to_string());
            }
        }
        serde_json::Value::String(s) => {
            encode_msgpack_str_header(s.len() as u32, out);
            out.extend_from_slice(s.as_bytes());
        }
        serde_json::Value::Array(items) => {
            encode_msgpack_array_header(items.len() as u32, out);
            for item in items {
                encode_msgpack_value(item, out)?;
            }
        }
        serde_json::Value::Object(map) => {
            encode_msgpack_map_header(map.len() as u32, out);
            for (k, v) in map {
                encode_msgpack_str_header(k.len() as u32, out);
                out.extend_from_slice(k.as_bytes());
                encode_msgpack_value(v, out)?;
            }
        }
    }
    Ok(())
}

fn encode_msgpack_uint(v: u64, out: &mut Vec<u8>) {
    if v <= 0x7f {
        out.push(v as u8);
    } else if u8::try_from(v).is_ok() {
        out.push(0xcc);
        out.push(v as u8);
    } else if u16::try_from(v).is_ok() {
        out.push(0xcd);
        out.extend_from_slice(&(v as u16).to_be_bytes());
    } else if u32::try_from(v).is_ok() {
        out.push(0xce);
        out.extend_from_slice(&(v as u32).to_be_bytes());
    } else {
        out.push(0xcf);
        out.extend_from_slice(&v.to_be_bytes());
    }
}

fn encode_msgpack_int(v: i64, out: &mut Vec<u8>) {
    if (0..=127).contains(&v) {
        out.push(v as u8);
    } else if (-32..=-1).contains(&v) {
        out.push((0xe0i16 + (v + 32) as i16) as u8);
    } else if i8::try_from(v).is_ok() {
        out.push(0xd0);
        out.push(v as i8 as u8);
    } else if i16::try_from(v).is_ok() {
        out.push(0xd1);
        out.extend_from_slice(&(v as i16).to_be_bytes());
    } else if i32::try_from(v).is_ok() {
        out.push(0xd2);
        out.extend_from_slice(&(v as i32).to_be_bytes());
    } else {
        out.push(0xd3);
        out.extend_from_slice(&v.to_be_bytes());
    }
}

fn encode_msgpack_str_header(len: u32, out: &mut Vec<u8>) {
    if len <= 31 {
        out.push(0xa0 | (len as u8));
    } else if u8::try_from(len).is_ok() {
        out.push(0xd9);
        out.push(len as u8);
    } else if u16::try_from(len).is_ok() {
        out.push(0xda);
        out.extend_from_slice(&(len as u16).to_be_bytes());
    } else {
        out.push(0xdb);
        out.extend_from_slice(&len.to_be_bytes());
    }
}

fn encode_msgpack_array_header(len: u32, out: &mut Vec<u8>) {
    if len <= 15 {
        out.push(0x90 | (len as u8));
    } else if u16::try_from(len).is_ok() {
        out.push(0xdc);
        out.extend_from_slice(&(len as u16).to_be_bytes());
    } else {
        out.push(0xdd);
        out.extend_from_slice(&len.to_be_bytes());
    }
}

fn encode_msgpack_map_header(len: u32, out: &mut Vec<u8>) {
    if len <= 15 {
        out.push(0x80 | (len as u8));
    } else if u16::try_from(len).is_ok() {
        out.push(0xde);
        out.extend_from_slice(&(len as u16).to_be_bytes());
    } else {
        out.push(0xdf);
        out.extend_from_slice(&len.to_be_bytes());
    }
}

fn decode_msgpack_value(bytes: &[u8], idx: &mut usize) -> Result<serde_json::Value, String> {
    let marker = read_u8(bytes, idx)?;

    if marker <= 0x7f {
        return Ok(serde_json::Value::from(marker as u64));
    }
    if marker >= 0xe0 {
        return Ok(serde_json::Value::from((marker as i8) as i64));
    }

    match marker {
        0xc0 => Ok(serde_json::Value::Null),
        0xc2 => Ok(serde_json::Value::Bool(false)),
        0xc3 => Ok(serde_json::Value::Bool(true)),
        0xcc => Ok(serde_json::Value::from(read_u8(bytes, idx)? as u64)),
        0xcd => Ok(serde_json::Value::from(read_u16_be(bytes, idx)? as u64)),
        0xce => Ok(serde_json::Value::from(read_u32_be(bytes, idx)? as u64)),
        0xcf => Ok(serde_json::Value::from(read_u64_be(bytes, idx)?)),
        0xd0 => Ok(serde_json::Value::from(read_u8(bytes, idx)? as i8 as i64)),
        0xd1 => Ok(serde_json::Value::from(
            read_u16_be(bytes, idx)? as i16 as i64
        )),
        0xd2 => Ok(serde_json::Value::from(
            read_u32_be(bytes, idx)? as i32 as i64
        )),
        0xd3 => Ok(serde_json::Value::from(read_u64_be(bytes, idx)? as i64)),
        0xcb => Ok(serde_json::Value::from(f64::from_be_bytes(read_n::<8>(
            bytes, idx,
        )?))),
        0xd9 => {
            let len = read_u8(bytes, idx)? as usize;
            decode_msgpack_str(bytes, idx, len)
        }
        0xda => {
            let len = read_u16_be(bytes, idx)? as usize;
            decode_msgpack_str(bytes, idx, len)
        }
        0xdb => {
            let len = read_u32_be(bytes, idx)? as usize;
            decode_msgpack_str(bytes, idx, len)
        }
        0xdc => {
            let len = read_u16_be(bytes, idx)? as usize;
            decode_msgpack_array(bytes, idx, len)
        }
        0xdd => {
            let len = read_u32_be(bytes, idx)? as usize;
            decode_msgpack_array(bytes, idx, len)
        }
        0xde => {
            let len = read_u16_be(bytes, idx)? as usize;
            decode_msgpack_map(bytes, idx, len)
        }
        0xdf => {
            let len = read_u32_be(bytes, idx)? as usize;
            decode_msgpack_map(bytes, idx, len)
        }
        m if (0xa0..=0xbf).contains(&m) => decode_msgpack_str(bytes, idx, (m & 0x1f) as usize),
        m if (0x90..=0x9f).contains(&m) => decode_msgpack_array(bytes, idx, (m & 0x0f) as usize),
        m if (0x80..=0x8f).contains(&m) => decode_msgpack_map(bytes, idx, (m & 0x0f) as usize),
        _ => Err(format!("unsupported msgpack marker: 0x{:x}", marker)),
    }
}

fn decode_msgpack_str(
    bytes: &[u8],
    idx: &mut usize,
    len: usize,
) -> Result<serde_json::Value, String> {
    if *idx + len > bytes.len() {
        return Err("msgpack string out of bounds".to_string());
    }
    let s = std::str::from_utf8(&bytes[*idx..*idx + len])
        .map_err(|_| "msgpack invalid utf8 string")?
        .to_string();
    *idx += len;
    Ok(serde_json::Value::String(s))
}

fn decode_msgpack_array(
    bytes: &[u8],
    idx: &mut usize,
    len: usize,
) -> Result<serde_json::Value, String> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(decode_msgpack_value(bytes, idx)?);
    }
    Ok(serde_json::Value::Array(arr))
}

fn decode_msgpack_map(
    bytes: &[u8],
    idx: &mut usize,
    len: usize,
) -> Result<serde_json::Value, String> {
    let mut map = serde_json::Map::new();
    for _ in 0..len {
        let key = match decode_msgpack_value(bytes, idx)? {
            serde_json::Value::String(s) => s,
            _ => return Err("msgpack map key must be string".to_string()),
        };
        let value = decode_msgpack_value(bytes, idx)?;
        map.insert(key, value);
    }
    Ok(serde_json::Value::Object(map))
}

fn encode_cbor_value(value: &serde_json::Value, out: &mut Vec<u8>) -> Result<(), String> {
    match value {
        serde_json::Value::Null => out.push(0xf6),
        serde_json::Value::Bool(false) => out.push(0xf4),
        serde_json::Value::Bool(true) => out.push(0xf5),
        serde_json::Value::Number(n) => {
            if let Some(u) = n.as_u64() {
                write_cbor_type_and_len(0, u, out);
            } else if let Some(i) = n.as_i64() {
                if i >= 0 {
                    write_cbor_type_and_len(0, i as u64, out);
                } else {
                    // major type 1 encodes -1 - n
                    write_cbor_type_and_len(1, (-1 - i) as u64, out);
                }
            } else if let Some(f) = n.as_f64() {
                out.push(0xfb);
                out.extend_from_slice(&f.to_be_bytes());
            } else {
                return Err("unsupported number representation".to_string());
            }
        }
        serde_json::Value::String(s) => {
            write_cbor_type_and_len(3, s.len() as u64, out);
            out.extend_from_slice(s.as_bytes());
        }
        serde_json::Value::Array(items) => {
            write_cbor_type_and_len(4, items.len() as u64, out);
            for item in items {
                encode_cbor_value(item, out)?;
            }
        }
        serde_json::Value::Object(map) => {
            write_cbor_type_and_len(5, map.len() as u64, out);
            for (k, v) in map {
                write_cbor_type_and_len(3, k.len() as u64, out);
                out.extend_from_slice(k.as_bytes());
                encode_cbor_value(v, out)?;
            }
        }
    }
    Ok(())
}

fn decode_cbor_value(bytes: &[u8], idx: &mut usize) -> Result<serde_json::Value, String> {
    let head = read_u8(bytes, idx)?;
    let major = head >> 5;
    let ai = head & 0x1f;

    match major {
        0 => Ok(serde_json::Value::from(read_cbor_len(bytes, idx, ai)?)),
        1 => {
            let n = read_cbor_len(bytes, idx, ai)?;
            let signed = -1i128 - n as i128;
            Ok(serde_json::Value::from(signed as i64))
        }
        3 => {
            let len = read_cbor_len(bytes, idx, ai)? as usize;
            if *idx + len > bytes.len() {
                return Err("cbor text out of bounds".to_string());
            }
            let s = std::str::from_utf8(&bytes[*idx..*idx + len])
                .map_err(|_| "cbor invalid utf8")?
                .to_string();
            *idx += len;
            Ok(serde_json::Value::String(s))
        }
        4 => {
            let len = read_cbor_len(bytes, idx, ai)? as usize;
            let mut arr = Vec::with_capacity(len);
            for _ in 0..len {
                arr.push(decode_cbor_value(bytes, idx)?);
            }
            Ok(serde_json::Value::Array(arr))
        }
        5 => {
            let len = read_cbor_len(bytes, idx, ai)? as usize;
            let mut map = serde_json::Map::new();
            for _ in 0..len {
                let key = match decode_cbor_value(bytes, idx)? {
                    serde_json::Value::String(s) => s,
                    _ => return Err("cbor map key must be string".to_string()),
                };
                let value = decode_cbor_value(bytes, idx)?;
                map.insert(key, value);
            }
            Ok(serde_json::Value::Object(map))
        }
        7 => match ai {
            20 => Ok(serde_json::Value::Bool(false)),
            21 => Ok(serde_json::Value::Bool(true)),
            22 => Ok(serde_json::Value::Null),
            27 => Ok(serde_json::Value::from(f64::from_be_bytes(read_n::<8>(
                bytes, idx,
            )?))),
            _ => Err("unsupported cbor simple value".to_string()),
        },
        _ => Err(format!("unsupported cbor major type {}", major)),
    }
}

fn write_cbor_type_and_len(major: u8, len: u64, out: &mut Vec<u8>) {
    if len <= 23 {
        out.push((major << 5) | (len as u8));
    } else if u8::try_from(len).is_ok() {
        out.push((major << 5) | 24);
        out.push(len as u8);
    } else if u16::try_from(len).is_ok() {
        out.push((major << 5) | 25);
        out.extend_from_slice(&(len as u16).to_be_bytes());
    } else if u32::try_from(len).is_ok() {
        out.push((major << 5) | 26);
        out.extend_from_slice(&(len as u32).to_be_bytes());
    } else {
        out.push((major << 5) | 27);
        out.extend_from_slice(&len.to_be_bytes());
    }
}

fn read_cbor_len(bytes: &[u8], idx: &mut usize, ai: u8) -> Result<u64, String> {
    match ai {
        0..=23 => Ok(ai as u64),
        24 => Ok(read_u8(bytes, idx)? as u64),
        25 => Ok(read_u16_be(bytes, idx)? as u64),
        26 => Ok(read_u32_be(bytes, idx)? as u64),
        27 => Ok(read_u64_be(bytes, idx)?),
        _ => Err("unsupported cbor additional-info".to_string()),
    }
}

fn read_u8(bytes: &[u8], idx: &mut usize) -> Result<u8, String> {
    if *idx >= bytes.len() {
        return Err("unexpected eof".to_string());
    }
    let b = bytes[*idx];
    *idx += 1;
    Ok(b)
}

fn read_u16_be(bytes: &[u8], idx: &mut usize) -> Result<u16, String> {
    Ok(u16::from_be_bytes(read_n::<2>(bytes, idx)?))
}

fn read_u32_be(bytes: &[u8], idx: &mut usize) -> Result<u32, String> {
    Ok(u32::from_be_bytes(read_n::<4>(bytes, idx)?))
}

fn read_u64_be(bytes: &[u8], idx: &mut usize) -> Result<u64, String> {
    Ok(u64::from_be_bytes(read_n::<8>(bytes, idx)?))
}

fn read_n<const N: usize>(bytes: &[u8], idx: &mut usize) -> Result<[u8; N], String> {
    if *idx + N > bytes.len() {
        return Err("unexpected eof".to_string());
    }
    let mut out = [0u8; N];
    out.copy_from_slice(&bytes[*idx..*idx + N]);
    *idx += N;
    Ok(out)
}

fn write_varint(mut n: u64, out: &mut Vec<u8>) {
    loop {
        let mut byte = (n & 0x7f) as u8;
        n >>= 7;
        if n != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if n == 0 {
            break;
        }
    }
}

fn read_varint(bytes: &[u8], idx: &mut usize) -> Result<u64, String> {
    let mut shift = 0u32;
    let mut out = 0u64;
    loop {
        if shift >= 64 {
            return Err("varint overflow".to_string());
        }
        let b = read_u8(bytes, idx)?;
        out |= ((b & 0x7f) as u64) << shift;
        if (b & 0x80) == 0 {
            return Ok(out);
        }
        shift += 7;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(val) => val,
            Err(err) => panic!("Expected Ok, got Err: {:?}", err),
        }
    }

    fn sample() -> serde_json::Value {
        json!({
            "ok": true,
            "n": 42,
            "neg": -5,
            "f": 3.14,
            "arr": [1, "x", false],
            "obj": {"k": "v"},
            "nil": null
        })
    }

    #[test]
    fn test_json_roundtrip() {
        let v = sample();
        let encoded = expect_ok(encode_json(&v));
        let decoded = expect_ok(decode_json(&encoded));
        assert_eq!(v, decoded);
    }

    #[test]
    fn test_msgpack_roundtrip() {
        let v = sample();
        let encoded = expect_ok(encode_msgpack(&v));
        let decoded = expect_ok(decode_msgpack(&encoded));
        assert_eq!(v, decoded);
    }

    #[test]
    fn test_cbor_roundtrip() {
        let v = sample();
        let encoded = expect_ok(encode_cbor(&v));
        let decoded = expect_ok(decode_cbor(&encoded));
        assert_eq!(v, decoded);
    }

    #[test]
    fn test_protobuf_roundtrip() {
        let v = sample();
        let encoded = expect_ok(encode_protobuf_json_envelope(&v));
        let decoded = expect_ok(decode_protobuf_json_envelope(&encoded));
        assert_eq!(v, decoded);
    }

    #[test]
    fn test_generic_dispatch() {
        let v = sample();
        for format in [
            Format::Json,
            Format::MessagePack,
            Format::Cbor,
            Format::Protobuf,
        ] {
            let enc = expect_ok(encode_with_format(&v, format));
            let dec = expect_ok(decode_with_format(&enc, format));
            assert_eq!(v, dec);
        }
    }
}
