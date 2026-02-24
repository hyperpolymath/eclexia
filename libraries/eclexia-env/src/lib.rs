// SPDX-License-Identifier: PMPL-1.0-or-later

//! Environment variable helpers.

use std::collections::BTreeMap;

pub fn get(key: &str) -> Option<String> {
    std::env::var(key).ok()
}

pub fn get_or(key: &str, default: &str) -> String {
    get(key).unwrap_or_else(|| default.to_string())
}

pub fn require(key: &str) -> Result<String, String> {
    get(key).ok_or_else(|| format!("required environment variable '{}' is missing", key))
}

pub fn get_bool(key: &str, default: bool) -> bool {
    match get(key) {
        Some(v) => matches!(
            v.to_ascii_lowercase().as_str(),
            "1" | "true" | "yes" | "on" | "enabled"
        ),
        None => default,
    }
}

pub fn get_i64(key: &str, default: i64) -> i64 {
    get(key)
        .and_then(|v| v.parse::<i64>().ok())
        .unwrap_or(default)
}

pub fn get_u64(key: &str, default: u64) -> u64 {
    get(key)
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(default)
}

pub fn get_f64(key: &str, default: f64) -> f64 {
    get(key)
        .and_then(|v| v.parse::<f64>().ok())
        .unwrap_or(default)
}

pub fn collect_with_prefix(prefix: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for (key, value) in std::env::vars() {
        if let Some(suffix) = key.strip_prefix(prefix) {
            out.insert(suffix.to_string(), value);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_helpers() {
        assert_eq!(get_or("ECLEXIA_MISSING_TEST_KEY", "fallback"), "fallback");
        assert_eq!(get_u64("ECLEXIA_MISSING_TEST_KEY", 42), 42);
        assert_eq!(get_f64("ECLEXIA_MISSING_TEST_KEY", 1.5), 1.5);
    }

    #[test]
    fn test_collect_with_prefix() {
        let key = "ECLEXIA_ENV_TEST_COLLECT_ALPHA";
        std::env::set_var(key, "1");
        let values = collect_with_prefix("ECLEXIA_ENV_TEST_COLLECT_");
        assert_eq!(values.get("ALPHA").map(String::as_str), Some("1"));
        std::env::remove_var(key);
    }
}
