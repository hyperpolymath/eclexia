// SPDX-License-Identifier: PMPL-1.0-or-later

//! Input validation helpers.

pub fn validate_non_empty(value: &str, field: &str) -> Result<(), String> {
    if value.trim().is_empty() {
        return Err(format!("{} must not be empty", field));
    }
    Ok(())
}

pub fn validate_email(value: &str) -> Result<(), String> {
    let trimmed = value.trim();
    let (local, domain) = trimmed
        .split_once('@')
        .ok_or("invalid email address: missing '@'")?;
    if local.is_empty() || domain.is_empty() {
        return Err("invalid email address".to_string());
    }
    if !domain.contains('.') {
        return Err("invalid email address: missing domain dot".to_string());
    }
    if domain.starts_with('.') || domain.ends_with('.') || domain.contains("..") {
        return Err("invalid email address domain".to_string());
    }
    if local.contains(' ') || domain.contains(' ') {
        return Err("invalid email address: contains whitespace".to_string());
    }
    Ok(())
}

pub fn validate_range_i64(value: i64, min: i64, max: i64, field: &str) -> Result<(), String> {
    if value < min || value > max {
        return Err(format!("{} must be between {} and {}", field, min, max));
    }
    Ok(())
}

pub fn validate_slug(value: &str, field: &str) -> Result<(), String> {
    validate_non_empty(value, field)?;
    if !value
        .chars()
        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
    {
        return Err(format!(
            "{} must contain only lowercase letters, digits, and '-'",
            field
        ));
    }
    if value.starts_with('-') || value.ends_with('-') || value.contains("--") {
        return Err(format!("{} has invalid '-' placement", field));
    }
    Ok(())
}

pub fn validate_uuid(value: &str, field: &str) -> Result<(), String> {
    if !eclexia_uuid::is_valid_uuid(value) {
        return Err(format!("{} must be a valid UUID", field));
    }
    Ok(())
}

pub fn validate_password_strength(value: &str, min_len: usize) -> Result<(), String> {
    if value.len() < min_len {
        return Err(format!("password must be at least {} characters", min_len));
    }
    let has_upper = value.chars().any(|c| c.is_ascii_uppercase());
    let has_lower = value.chars().any(|c| c.is_ascii_lowercase());
    let has_digit = value.chars().any(|c| c.is_ascii_digit());
    let has_symbol = value
        .chars()
        .any(|c| !c.is_ascii_alphanumeric() && !c.is_whitespace());

    if !(has_upper && has_lower && has_digit && has_symbol) {
        return Err("password must contain upper/lowercase letters, digit, and symbol".to_string());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_non_empty() {
        assert!(validate_non_empty("abc", "name").is_ok());
        assert!(validate_non_empty("", "name").is_err());
    }

    #[test]
    fn test_email() {
        assert!(validate_email("user@example.com").is_ok());
        assert!(validate_email("invalid").is_err());
        assert!(validate_email("bad@domain").is_err());
    }

    #[test]
    fn test_slug() {
        assert!(validate_slug("hello-world-2", "slug").is_ok());
        assert!(validate_slug("Hello", "slug").is_err());
    }

    #[test]
    fn test_password_strength() {
        assert!(validate_password_strength("Aa1!aaaa", 8).is_ok());
        assert!(validate_password_strength("weak", 8).is_err());
    }
}
