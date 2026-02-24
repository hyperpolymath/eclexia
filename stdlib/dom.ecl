// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! High-Assurance DOM Mounter for Eclexia.
//!
//! Provides validated, safe DOM mounting operations with proven
//! guarantees about selector validity and HTML well-formedness.
//!
//! Backed by the eclexia-dom runtime crate.

// === Core Types ===

/// Result of a mount operation.
type MountResult {
    /// Successfully mounted at the target element.
    Mounted(Element),
    /// Target selector did not match any element.
    NotFound(String),
    /// The CSS selector was syntactically invalid.
    InvalidSelector(String),
    /// The HTML content was malformed.
    InvalidHtml(String),
}

/// Opaque handle to a mounted DOM element.
type Element {
    /// Internal element reference.
    @builtin("dom_element")
    _ref: Int,
}

/// Specification for a batch mount operation.
type MountSpec {
    selector: String,
    html: String,
}

/// Validated CSS selector (proven syntactically correct).
type ValidatedSelector {
    /// The validated selector string.
    raw: String,
}

/// Validated HTML content (proven well-formed).
type ValidatedHtml {
    /// The validated HTML string.
    raw: String,
}

// === Validation ===

/// Validate a CSS selector string.
///
/// Returns Ok with a ValidatedSelector if the selector is syntactically
/// valid, or Err with a description of the problem.
///
/// # Example
/// ```
/// match validate_selector("#app") {
///     Ok(sel) => mount_validated(sel, html),
///     Err(msg) => println("Bad selector: " ++ msg),
/// }
/// ```
@builtin("dom_validate_selector")
fn validate_selector(selector: String) -> Result<ValidatedSelector, String>;

/// Validate an HTML string for well-formedness.
///
/// Checks that tags are balanced, attributes are properly quoted,
/// and the structure is valid.
///
/// # Example
/// ```
/// match validate_html("<div>Hello</div>") {
///     Ok(html) => mount_validated(sel, html),
///     Err(msg) => println("Bad HTML: " ++ msg),
/// }
/// ```
@builtin("dom_validate_html")
fn validate_html(html: String) -> Result<ValidatedHtml, String>;

// === Mount Operations ===

/// Mount HTML content at the element matching the given CSS selector.
///
/// This is the basic mount operation. It validates both the selector
/// and HTML before mounting. Returns a MountResult indicating success
/// or the specific failure.
///
/// # Example
/// ```
/// match mount("#app", "<h1>Hello, World!</h1>") {
///     Mounted(el) => println("Mounted successfully"),
///     NotFound(sel) => println("No element matches: " ++ sel),
///     InvalidSelector(msg) => println("Bad selector: " ++ msg),
///     InvalidHtml(msg) => println("Bad HTML: " ++ msg),
/// }
/// ```
@builtin("dom_mount")
fn mount(selector: String, html: String) -> MountResult;

/// Mount with pre-validated selector and HTML.
///
/// Skips validation since inputs are already proven valid.
/// This is more efficient for hot paths.
@builtin("dom_mount_validated")
fn mount_validated(selector: ValidatedSelector, html: ValidatedHtml) -> MountResult;

/// Mount with callback handlers for success and error.
///
/// Calls on_success with the mounted element on success,
/// or on_error with an error message on failure.
///
/// # Example
/// ```
/// mount_safe("#app", "<div>Content</div>",
///     |el| println("Mounted!"),
///     |err| println("Error: " ++ err))
/// ```
@builtin("dom_mount_safe")
fn mount_safe(
    selector: String,
    html: String,
    on_success: (Element) -> (),
    on_error: (String) -> (),
) -> ();

/// Mount when the DOM is ready.
///
/// Waits for DOMContentLoaded (or fires immediately if already loaded)
/// before attempting the mount. Useful for scripts in <head>.
///
/// # Example
/// ```
/// mount_when_ready("#app", "<div>App content</div>",
///     |el| println("App mounted"),
///     |err| println("Mount failed: " ++ err))
/// ```
@builtin("dom_mount_when_ready")
fn mount_when_ready(
    selector: String,
    html: String,
    on_success: (Element) -> (),
    on_error: (String) -> (),
) -> ();

/// Mount multiple elements in a single batch operation.
///
/// All mounts succeed or none do (atomic). Returns a list of
/// mounted elements on success, or an error message.
///
/// # Example
/// ```
/// let specs = [
///     MountSpec { selector: "#header", html: "<nav>...</nav>" },
///     MountSpec { selector: "#main", html: "<article>...</article>" },
///     MountSpec { selector: "#footer", html: "<footer>...</footer>" },
/// ]
/// match mount_batch(specs) {
///     Ok(elements) => println("All mounted"),
///     Err(msg) => println("Batch mount failed: " ++ msg),
/// }
/// ```
@builtin("dom_mount_batch")
fn mount_batch(specs: List<MountSpec>) -> Result<List<Element>, String>;

// === Element Operations ===

/// Get the inner HTML of a mounted element.
@builtin("dom_inner_html")
fn inner_html(element: Element) -> String;

/// Set the inner HTML of a mounted element.
@builtin("dom_set_inner_html")
fn set_inner_html(element: Element, html: String) -> Result<(), String>;

/// Get a text content of a mounted element.
@builtin("dom_text_content")
fn text_content(element: Element) -> String;

/// Set the text content of a mounted element (safe, no HTML injection).
@builtin("dom_set_text_content")
fn set_text_content(element: Element, text: String) -> ();

/// Add a CSS class to an element.
@builtin("dom_add_class")
fn add_class(element: Element, class_name: String) -> ();

/// Remove a CSS class from an element.
@builtin("dom_remove_class")
fn remove_class(element: Element, class_name: String) -> ();

/// Toggle a CSS class on an element.
@builtin("dom_toggle_class")
fn toggle_class(element: Element, class_name: String) -> Bool;

/// Set an attribute on an element.
@builtin("dom_set_attribute")
fn set_attribute(element: Element, name: String, value: String) -> ();

/// Get an attribute from an element.
@builtin("dom_get_attribute")
fn get_attribute(element: Element, name: String) -> Option<String>;

/// Remove an element from the DOM.
@builtin("dom_remove")
fn remove(element: Element) -> ();

// === Query Operations ===

/// Query a single element matching a selector.
@builtin("dom_query_selector")
fn query_selector(selector: String) -> Option<Element>;

/// Query all elements matching a selector.
@builtin("dom_query_selector_all")
fn query_selector_all(selector: String) -> List<Element>;
