// SPDX-License-Identifier: PMPL-1.0-or-later

//! Template engine with variable, `if`, and `each` block support.

use serde_json::Value;
use std::collections::HashMap;

/// Backward-compatible simple renderer.
pub fn render(template: &str, vars: &HashMap<String, String>) -> String {
    let mut obj = serde_json::Map::new();
    for (k, v) in vars {
        obj.insert(k.clone(), Value::String(v.clone()));
    }
    render_value(template, &Value::Object(obj)).unwrap_or_else(|_| template.to_string())
}

/// Render a template against a JSON context.
///
/// Supported directives:
/// - `{{path.to.value}}`
/// - `{{#if flag}}...{{/if}}`
/// - `{{#each items}}...{{this}}...{{/each}}`
pub fn render_value(template: &str, context: &Value) -> Result<String, String> {
    render_section(template, context, None)
}

fn render_section(
    template: &str,
    context: &Value,
    this_value: Option<&Value>,
) -> Result<String, String> {
    let mut out = String::new();
    let mut idx = 0usize;

    while let Some(open_rel) = template[idx..].find("{{") {
        let open = idx + open_rel;
        out.push_str(&template[idx..open]);
        let close = template[open + 2..]
            .find("}}")
            .ok_or("unterminated template tag")?
            + open
            + 2;
        let tag = template[open + 2..close].trim();
        idx = close + 2;

        if let Some(expr) = tag.strip_prefix("#if ") {
            let (inner, new_idx) = extract_block(template, idx, "if")?;
            if is_truthy(lookup(expr.trim(), context, this_value)) {
                out.push_str(&render_section(inner, context, this_value)?);
            }
            idx = new_idx;
            continue;
        }

        if let Some(expr) = tag.strip_prefix("#each ") {
            let (inner, new_idx) = extract_block(template, idx, "each")?;
            if let Some(value) = lookup(expr.trim(), context, this_value) {
                match value {
                    Value::Array(items) => {
                        for item in items {
                            out.push_str(&render_section(inner, context, Some(item))?);
                        }
                    }
                    Value::Object(map) => {
                        for item in map.values() {
                            out.push_str(&render_section(inner, context, Some(item))?);
                        }
                    }
                    _ => {}
                }
            }
            idx = new_idx;
            continue;
        }

        if tag.starts_with('/') {
            return Err(format!("unexpected closing block '{}'", tag));
        }

        if let Some(value) = lookup(tag, context, this_value) {
            out.push_str(&value_to_string(value));
        }
    }

    out.push_str(&template[idx..]);
    Ok(out)
}

fn extract_block<'a>(
    template: &'a str,
    from: usize,
    kind: &str,
) -> Result<(&'a str, usize), String> {
    let open_tag = format!("{{{{#{} ", kind);
    let close_tag = format!("{{{{/{}}}}}", kind);
    let mut depth = 1usize;
    let mut scan = from;
    let mut content_end = None;

    while scan < template.len() {
        let next_open = template[scan..].find(&open_tag).map(|v| scan + v);
        let next_close = template[scan..].find(&close_tag).map(|v| scan + v);
        match (next_open, next_close) {
            (Some(open), Some(close)) if open < close => {
                depth += 1;
                scan = open + open_tag.len();
            }
            (_, Some(close)) => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    content_end = Some(close);
                    scan = close + close_tag.len();
                    break;
                }
                scan = close + close_tag.len();
            }
            _ => return Err(format!("missing closing block '{}'", kind)),
        }
    }

    let end = content_end.ok_or_else(|| format!("missing closing block '{}'", kind))?;
    Ok((&template[from..end], scan))
}

fn lookup<'a>(path: &str, context: &'a Value, this_value: Option<&'a Value>) -> Option<&'a Value> {
    let trimmed = path.trim();
    if trimmed == "this" {
        return this_value;
    }

    let (start, rest) = if let Some(suffix) = trimmed.strip_prefix("this.") {
        (this_value?, suffix)
    } else {
        (context, trimmed)
    };

    if rest.is_empty() {
        return Some(start);
    }

    let mut cur = start;
    for key in rest.split('.') {
        match cur {
            Value::Object(map) => {
                cur = map.get(key)?;
            }
            Value::Array(items) => {
                let idx = key.parse::<usize>().ok()?;
                cur = items.get(idx)?;
            }
            _ => return None,
        }
    }
    Some(cur)
}

fn is_truthy(value: Option<&Value>) -> bool {
    match value {
        Some(Value::Bool(v)) => *v,
        Some(Value::Number(n)) => n.as_i64() != Some(0),
        Some(Value::String(s)) => !s.is_empty(),
        Some(Value::Array(a)) => !a.is_empty(),
        Some(Value::Object(o)) => !o.is_empty(),
        Some(Value::Null) | None => false,
    }
}

fn value_to_string(value: &Value) -> String {
    match value {
        Value::Null => String::new(),
        Value::Bool(v) => v.to_string(),
        Value::Number(n) => n.to_string(),
        Value::String(s) => s.clone(),
        other => serde_json::to_string(other).unwrap_or_default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(v) => v,
            Err(e) => panic!("expected ok, got {:?}", e),
        }
    }

    #[test]
    fn test_render_template_legacy() {
        let mut vars = HashMap::new();
        vars.insert("name".to_string(), "Eclexia".to_string());
        let out = render("Hello {{name}}", &vars);
        assert_eq!(out, "Hello Eclexia");
    }

    #[test]
    fn test_if_and_each_blocks() {
        let ctx = json!({
            "title": "Docs",
            "published": true,
            "items": ["a", "b", "c"]
        });
        let tpl =
            "{{title}} {{#if published}}(published){{/if}} {{#each items}}[{{this}}]{{/each}}";
        let out = expect_ok(render_value(tpl, &ctx));
        assert!(out.contains("Docs"));
        assert!(out.contains("(published)"));
        assert!(out.contains("[a][b][c]"));
    }
}
