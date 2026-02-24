#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Keep inputs bounded to avoid pathological memory usage.
    if data.is_empty() || data.len() > 100000 {
        return;
    }

    // Test UTF-8 handling.
    let text = match std::str::from_utf8(data) {
        Ok(text) => text,
        Err(_) => return,
    };

    // Exercise parser for crash-safety on arbitrary source.
    let _ = eclexia_parser::parse(text);

    // Exercise JSON parser as a secondary fuzz target.
    if data.len() >= 4 {
        let _ = serde_json::from_slice::<serde_json::Value>(data);
    }
});
