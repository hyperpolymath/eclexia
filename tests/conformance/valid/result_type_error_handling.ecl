// SPDX-License-Identifier: PMPL-1.0-or-later

// Test: Result type for error handling
fn parse_number(s: string) -> Result<int, string> {
    // Simplified parsing
    if s == "42" {
        Ok(42)
    } else {
        Err("Parse error")
    }
}

fn main() {
    let ok_result = parse_number("42");
    assert(ok_result.is_ok());
    
    let err_result = parse_number("abc");
    assert(err_result.is_err());
}
