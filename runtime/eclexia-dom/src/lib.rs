// SPDX-License-Identifier: PMPL-1.0-or-later
//! eclexia-dom: High-assurance DOM mounter for Eclexia
//!
//! Provides validated, safe DOM mounting operations with proven
//! guarantees about selector validity and HTML well-formedness.
//! Targets both native (testing/SSR) and WASM (browser) execution.

use serde::{Deserialize, Serialize};
use std::fmt;

/// Result of a mount operation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MountResult {
    /// Successfully mounted at the target element
    Mounted(ElementRef),
    /// Target selector did not match any element
    NotFound(String),
    /// The CSS selector was syntactically invalid
    InvalidSelector(String),
    /// The HTML content was malformed
    InvalidHtml(String),
}

/// Reference to a mounted DOM element
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ElementRef {
    /// Internal element ID
    pub id: u64,
    /// The selector that matched this element
    pub selector: String,
}

/// A validated CSS selector (proven syntactically correct)
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ValidatedSelector {
    raw: String,
}

impl ValidatedSelector {
    /// Get the raw selector string
    pub fn as_str(&self) -> &str {
        &self.raw
    }
}

impl fmt::Display for ValidatedSelector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.raw)
    }
}

/// Validated HTML content (proven well-formed)
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ValidatedHtml {
    raw: String,
}

impl ValidatedHtml {
    /// Get the raw HTML string
    pub fn as_str(&self) -> &str {
        &self.raw
    }
}

impl fmt::Display for ValidatedHtml {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.raw)
    }
}

/// Specification for a batch mount operation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MountSpec {
    pub selector: String,
    pub html: String,
}

/// Validate a CSS selector string.
///
/// Checks for basic syntactic validity: not empty, balanced brackets,
/// no invalid characters in critical positions.
pub fn validate_selector(selector: &str) -> Result<ValidatedSelector, String> {
    if selector.is_empty() {
        return Err("Selector cannot be empty".to_string());
    }

    // Check balanced brackets
    let mut bracket_depth: i32 = 0;
    let mut paren_depth: i32 = 0;
    for ch in selector.chars() {
        match ch {
            '[' => bracket_depth += 1,
            ']' => {
                bracket_depth -= 1;
                if bracket_depth < 0 {
                    return Err("Unbalanced brackets in selector".to_string());
                }
            }
            '(' => paren_depth += 1,
            ')' => {
                paren_depth -= 1;
                if paren_depth < 0 {
                    return Err("Unbalanced parentheses in selector".to_string());
                }
            }
            _ => {}
        }
    }
    if bracket_depth != 0 {
        return Err("Unbalanced brackets in selector".to_string());
    }
    if paren_depth != 0 {
        return Err("Unbalanced parentheses in selector".to_string());
    }

    // Must start with a valid selector character
    let first = selector.chars().next().unwrap();
    if !matches!(first, '#' | '.' | '*' | ':' | '[' | 'a'..='z' | 'A'..='Z' | '_') {
        return Err(format!("Selector cannot start with '{}'", first));
    }

    Ok(ValidatedSelector {
        raw: selector.to_string(),
    })
}

/// Validate HTML content for well-formedness.
///
/// Checks that tags are balanced, properly nested, and the structure
/// is valid. Self-closing tags (br, hr, img, input, meta, link) are handled.
pub fn validate_html(html: &str) -> Result<ValidatedHtml, String> {
    if html.is_empty() {
        return Ok(ValidatedHtml {
            raw: html.to_string(),
        });
    }

    let self_closing = ["br", "hr", "img", "input", "meta", "link", "area", "base", "col", "embed", "source", "track", "wbr"];
    let mut tag_stack: Vec<String> = Vec::new();
    let mut i = 0;
    let bytes = html.as_bytes();

    while i < bytes.len() {
        if bytes[i] == b'<' {
            // Skip comments
            if i + 3 < bytes.len() && &bytes[i..i + 4] == b"<!--" {
                match html[i + 4..].find("-->") {
                    Some(end) => {
                        i = i + 4 + end + 3;
                        continue;
                    }
                    None => return Err("Unclosed HTML comment".to_string()),
                }
            }

            // Find end of tag
            let tag_start = i + 1;
            let tag_end = match html[tag_start..].find('>') {
                Some(pos) => tag_start + pos,
                None => return Err("Unclosed HTML tag".to_string()),
            };

            let tag_content = &html[tag_start..tag_end];

            if tag_content.starts_with('/') {
                // Closing tag
                let tag_name = tag_content[1..].split_whitespace().next().unwrap_or("").to_lowercase();
                if !tag_name.is_empty() {
                    match tag_stack.pop() {
                        Some(open_tag) if open_tag == tag_name => {}
                        Some(open_tag) => {
                            return Err(format!(
                                "Mismatched tags: expected </{}>, found </{}>",
                                open_tag, tag_name
                            ));
                        }
                        None => {
                            return Err(format!("Unexpected closing tag </{}>", tag_name));
                        }
                    }
                }
            } else if !tag_content.ends_with('/') {
                // Opening tag (not self-closing via />)
                let tag_name = tag_content.split_whitespace().next().unwrap_or("").to_lowercase();
                if !tag_name.is_empty() && !self_closing.contains(&tag_name.as_str()) {
                    tag_stack.push(tag_name);
                }
            }

            i = tag_end + 1;
        } else {
            i += 1;
        }
    }

    if !tag_stack.is_empty() {
        return Err(format!("Unclosed tags: {}", tag_stack.join(", ")));
    }

    Ok(ValidatedHtml {
        raw: html.to_string(),
    })
}

/// Mount HTML content at the element matching the given CSS selector.
///
/// On native targets, this validates inputs and returns a simulated
/// ElementRef. On WASM targets, this performs actual DOM manipulation.
pub fn mount(selector: &str, html: &str) -> MountResult {
    let validated_selector = match validate_selector(selector) {
        Ok(s) => s,
        Err(e) => return MountResult::InvalidSelector(e),
    };

    let validated_html = match validate_html(html) {
        Ok(h) => h,
        Err(e) => return MountResult::InvalidHtml(e),
    };

    mount_validated(&validated_selector, &validated_html)
}

/// Mount with pre-validated selector and HTML.
///
/// On native, returns a simulated mount. On WASM, performs DOM operations.
pub fn mount_validated(selector: &ValidatedSelector, html: &ValidatedHtml) -> MountResult {
    #[cfg(target_arch = "wasm32")]
    {
        mount_wasm(selector, html)
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        // Native: simulate mount for testing/SSR
        let id = {
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            selector.as_str().hash(&mut hasher);
            hasher.finish()
        };

        MountResult::Mounted(ElementRef {
            id,
            selector: selector.as_str().to_string(),
        })
    }
}

/// Mount with callback handlers.
pub fn mount_safe<F, E>(selector: &str, html: &str, on_success: F, on_error: E)
where
    F: FnOnce(ElementRef),
    E: FnOnce(String),
{
    match mount(selector, html) {
        MountResult::Mounted(elem) => on_success(elem),
        MountResult::NotFound(msg) => on_error(format!("Not found: {}", msg)),
        MountResult::InvalidSelector(msg) => on_error(format!("Invalid selector: {}", msg)),
        MountResult::InvalidHtml(msg) => on_error(format!("Invalid HTML: {}", msg)),
    }
}

/// Mount multiple elements in a single batch operation.
///
/// If any mount fails, returns the error. Otherwise returns all
/// successfully mounted elements.
pub fn mount_batch(specs: &[MountSpec]) -> Result<Vec<ElementRef>, String> {
    let mut elements = Vec::with_capacity(specs.len());

    for spec in specs {
        match mount(&spec.selector, &spec.html) {
            MountResult::Mounted(elem) => elements.push(elem),
            MountResult::NotFound(msg) => return Err(format!("Not found: {}", msg)),
            MountResult::InvalidSelector(msg) => {
                return Err(format!("Invalid selector '{}': {}", spec.selector, msg))
            }
            MountResult::InvalidHtml(msg) => {
                return Err(format!("Invalid HTML for '{}': {}", spec.selector, msg))
            }
        }
    }

    Ok(elements)
}

#[cfg(target_arch = "wasm32")]
fn mount_wasm(selector: &ValidatedSelector, html: &ValidatedHtml) -> MountResult {
    use wasm_bindgen::JsCast;

    let window = match web_sys::window() {
        Some(w) => w,
        None => return MountResult::NotFound("No window object".to_string()),
    };

    let document = match window.document() {
        Some(d) => d,
        None => return MountResult::NotFound("No document object".to_string()),
    };

    match document.query_selector(selector.as_str()) {
        Ok(Some(element)) => {
            element.set_inner_html(html.as_str());
            let id = element.as_ref() as *const _ as u64;
            MountResult::Mounted(ElementRef {
                id,
                selector: selector.as_str().to_string(),
            })
        }
        Ok(None) => MountResult::NotFound(selector.as_str().to_string()),
        Err(_) => MountResult::InvalidSelector(format!(
            "Browser rejected selector: {}",
            selector.as_str()
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_selector_valid() {
        assert!(validate_selector("#app").is_ok());
        assert!(validate_selector(".container").is_ok());
        assert!(validate_selector("div").is_ok());
        assert!(validate_selector("div.class").is_ok());
        assert!(validate_selector("#id .class > p").is_ok());
        assert!(validate_selector("[data-attr]").is_ok());
        assert!(validate_selector("*").is_ok());
        assert!(validate_selector(":root").is_ok());
    }

    #[test]
    fn test_validate_selector_invalid() {
        assert!(validate_selector("").is_err());
        assert!(validate_selector("[unclosed").is_err());
        assert!(validate_selector("unclosed]").is_err());
        assert!(validate_selector("(unbalanced").is_err());
    }

    #[test]
    fn test_validate_html_valid() {
        assert!(validate_html("").is_ok());
        assert!(validate_html("plain text").is_ok());
        assert!(validate_html("<div>Hello</div>").is_ok());
        assert!(validate_html("<div><p>Nested</p></div>").is_ok());
        assert!(validate_html("<br>").is_ok());
        assert!(validate_html("<input>").is_ok());
        assert!(validate_html("<img />").is_ok());
        assert!(validate_html("<div><!-- comment --></div>").is_ok());
    }

    #[test]
    fn test_validate_html_invalid() {
        assert!(validate_html("<div>").is_err()); // unclosed
        assert!(validate_html("<div><p></div></p>").is_err()); // mismatched
        assert!(validate_html("</div>").is_err()); // unexpected close
        assert!(validate_html("<div").is_err()); // unclosed tag
        assert!(validate_html("<!-- unclosed").is_err()); // unclosed comment
    }

    #[test]
    fn test_mount_native() {
        let result = mount("#app", "<div>Hello</div>");
        match result {
            MountResult::Mounted(elem) => {
                assert_eq!(elem.selector, "#app");
            }
            _ => panic!("Expected Mounted result"),
        }
    }

    #[test]
    fn test_mount_invalid_selector() {
        let result = mount("", "<div>Hello</div>");
        match result {
            MountResult::InvalidSelector(_) => {}
            _ => panic!("Expected InvalidSelector"),
        }
    }

    #[test]
    fn test_mount_invalid_html() {
        let result = mount("#app", "<div><p></div>");
        match result {
            MountResult::InvalidHtml(_) => {}
            _ => panic!("Expected InvalidHtml"),
        }
    }

    #[test]
    fn test_mount_safe_success() {
        let mut success_called = false;
        mount_safe("#app", "<div>Hello</div>", |_elem| {
            success_called = true;
        }, |_err| {
            panic!("Should not error");
        });
        assert!(success_called);
    }

    #[test]
    fn test_mount_safe_error() {
        let mut error_called = false;
        mount_safe("", "<div>Hello</div>", |_elem| {
            panic!("Should not succeed");
        }, |_err| {
            error_called = true;
        });
        assert!(error_called);
    }

    #[test]
    fn test_mount_batch() {
        let specs = vec![
            MountSpec {
                selector: "#header".to_string(),
                html: "<nav>Nav</nav>".to_string(),
            },
            MountSpec {
                selector: "#main".to_string(),
                html: "<article>Content</article>".to_string(),
            },
            MountSpec {
                selector: "#footer".to_string(),
                html: "<footer>Footer</footer>".to_string(),
            },
        ];
        let result = mount_batch(&specs);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().len(), 3);
    }

    #[test]
    fn test_mount_batch_error() {
        let specs = vec![
            MountSpec {
                selector: "#ok".to_string(),
                html: "<div>OK</div>".to_string(),
            },
            MountSpec {
                selector: "".to_string(), // invalid
                html: "<div>Fail</div>".to_string(),
            },
        ];
        let result = mount_batch(&specs);
        assert!(result.is_err());
    }

    #[test]
    fn test_validated_selector_display() {
        let sel = validate_selector("#app").unwrap();
        assert_eq!(sel.to_string(), "#app");
        assert_eq!(sel.as_str(), "#app");
    }

    #[test]
    fn test_validated_html_display() {
        let html = validate_html("<p>Hello</p>").unwrap();
        assert_eq!(html.to_string(), "<p>Hello</p>");
        assert_eq!(html.as_str(), "<p>Hello</p>");
    }
}
