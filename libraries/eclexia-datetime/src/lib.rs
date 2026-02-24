// SPDX-License-Identifier: PMPL-1.0-or-later

//! Date/time utility helpers.

use std::time::{SystemTime, UNIX_EPOCH};

pub fn unix_timestamp_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

pub fn unix_timestamp_millis() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis()
}

/// RFC3339 UTC formatter (e.g. `2026-02-11T10:34:12Z`).
pub fn format_rfc3339_utc(timestamp_secs: i64) -> String {
    let (year, month, day, hour, minute, second) = to_utc_components(timestamp_secs);
    format!(
        "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
        year, month, day, hour, minute, second
    )
}

pub fn format_utc_basic(timestamp_secs: u64) -> String {
    format_rfc3339_utc(timestamp_secs as i64)
}

pub fn parse_rfc3339_utc(input: &str) -> Result<i64, String> {
    let s = input.trim();
    if s.len() != 20 || !s.ends_with('Z') {
        return Err("unsupported rfc3339 format, expected YYYY-MM-DDTHH:MM:SSZ".to_string());
    }

    let year = s[0..4].parse::<i32>().map_err(|_| "invalid year")?;
    let month = s[5..7].parse::<u32>().map_err(|_| "invalid month")?;
    let day = s[8..10].parse::<u32>().map_err(|_| "invalid day")?;
    let hour = s[11..13].parse::<u32>().map_err(|_| "invalid hour")?;
    let minute = s[14..16].parse::<u32>().map_err(|_| "invalid minute")?;
    let second = s[17..19].parse::<u32>().map_err(|_| "invalid second")?;

    if &s[4..5] != "-"
        || &s[7..8] != "-"
        || &s[10..11] != "T"
        || &s[13..14] != ":"
        || &s[16..17] != ":"
    {
        return Err("invalid timestamp delimiters".to_string());
    }

    let days = days_from_civil(year, month, day)?;
    Ok(days * 86_400 + (hour as i64) * 3600 + (minute as i64) * 60 + second as i64)
}

/// Parse compact human duration strings:
/// - `500ms`
/// - `5s`
/// - `2m`
/// - `1h`
/// - compound: `1h30m15s250ms`
///
/// Returns milliseconds.
pub fn parse_duration(input: &str) -> Result<u64, String> {
    let mut i = 0usize;
    let bytes = input.as_bytes();
    if bytes.is_empty() {
        return Err("empty duration".to_string());
    }

    let mut total_ms: u64 = 0;
    while i < bytes.len() {
        let start = i;
        while i < bytes.len() && bytes[i].is_ascii_digit() {
            i += 1;
        }
        if i == start {
            return Err("expected duration number".to_string());
        }
        let value = input[start..i]
            .parse::<u64>()
            .map_err(|_| "invalid duration number")?;

        if i >= bytes.len() {
            return Err("missing duration unit".to_string());
        }

        if input[i..].starts_with("ms") {
            total_ms = total_ms.saturating_add(value);
            i += 2;
            continue;
        }
        let unit = bytes[i] as char;
        i += 1;
        total_ms = total_ms.saturating_add(match unit {
            's' => value.saturating_mul(1000),
            'm' => value.saturating_mul(60_000),
            'h' => value.saturating_mul(3_600_000),
            'd' => value.saturating_mul(86_400_000),
            _ => return Err(format!("unsupported duration unit '{}'", unit)),
        });
    }
    Ok(total_ms)
}

pub fn parse_utc_offset(input: &str) -> Result<i32, String> {
    // ±HH:MM in seconds.
    let s = input.trim();
    if s.len() != 6 {
        return Err("offset must be ±HH:MM".to_string());
    }
    let sign = match &s[0..1] {
        "+" => 1i32,
        "-" => -1i32,
        _ => return Err("offset must start with + or -".to_string()),
    };
    if &s[3..4] != ":" {
        return Err("offset must include ':'".to_string());
    }
    let hours = s[1..3].parse::<i32>().map_err(|_| "invalid offset hour")?;
    let mins = s[4..6]
        .parse::<i32>()
        .map_err(|_| "invalid offset minute")?;
    if hours > 23 || mins > 59 {
        return Err("offset out of range".to_string());
    }
    Ok(sign * (hours * 3600 + mins * 60))
}

fn to_utc_components(timestamp_secs: i64) -> (i32, u32, u32, u32, u32, u32) {
    let days = timestamp_secs.div_euclid(86_400);
    let rem = timestamp_secs.rem_euclid(86_400);
    let (year, month, day) = civil_from_days(days);
    let hour = (rem / 3600) as u32;
    let minute = ((rem % 3600) / 60) as u32;
    let second = (rem % 60) as u32;
    (year, month, day, hour, minute, second)
}

// Howard Hinnant date algorithms.
fn civil_from_days(days: i64) -> (i32, u32, u32) {
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = mp + if mp < 10 { 3 } else { -9 };
    let year = (y + (m <= 2) as i64) as i32;
    (year, m as u32, d as u32)
}

fn days_from_civil(year: i32, month: u32, day: u32) -> Result<i64, String> {
    if !(1..=12).contains(&month) {
        return Err("month out of range".to_string());
    }
    if day == 0 || day > days_in_month(year, month) {
        return Err("day out of range".to_string());
    }
    let y = year as i64 - (month <= 2) as i64;
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let m = month as i64;
    let doy = (153 * (m + if m > 2 { -3 } else { 9 }) + 2) / 5 + day as i64 - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    Ok(era * 146_097 + doe - 719_468)
}

fn days_in_month(year: i32, month: u32) -> u32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if is_leap_year(year) {
                29
            } else {
                28
            }
        }
        _ => 0,
    }
}

fn is_leap_year(year: i32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(v) => v,
            Err(e) => panic!("expected ok, got {:?}", e),
        }
    }

    #[test]
    fn test_parse_duration_compound() {
        assert_eq!(expect_ok(parse_duration("5s")), 5000);
        assert_eq!(expect_ok(parse_duration("2m")), 120_000);
        assert_eq!(expect_ok(parse_duration("1h30m15s250ms")), 5_415_250);
    }

    #[test]
    fn test_rfc3339_roundtrip() {
        let ts = 1_707_650_096i64; // 2024-02-10T17:48:16Z
        let text = format_rfc3339_utc(ts);
        assert_eq!(expect_ok(parse_rfc3339_utc(&text)), ts);
    }

    #[test]
    fn test_parse_offset() {
        assert_eq!(expect_ok(parse_utc_offset("+02:30")), 9000);
        assert_eq!(expect_ok(parse_utc_offset("-01:00")), -3600);
    }
}
