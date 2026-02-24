// SPDX-License-Identifier: PMPL-1.0-or-later

//! GraphQL query parsing and schema execution primitives.

use serde_json::{json, Value};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operation {
    Query,
    Mutation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    pub name: String,
    pub arguments: HashMap<String, String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedQuery {
    pub operation: Operation,
    pub fields: Vec<Field>,
}

pub type Resolver = Arc<dyn Fn(&Field) -> Result<Value, String> + Send + Sync + 'static>;

#[derive(Default)]
pub struct Schema {
    resolvers: HashMap<String, Resolver>,
}

impl Schema {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register<F>(&mut self, field: &str, resolver: F)
    where
        F: Fn(&Field) -> Result<Value, String> + Send + Sync + 'static,
    {
        self.resolvers.insert(field.to_string(), Arc::new(resolver));
    }

    pub fn execute_query(&self, query: &str) -> Value {
        let parsed = match parse(query) {
            Ok(p) => p,
            Err(err) => return json!({ "data": Value::Null, "errors": [err] }),
        };

        let mut data = serde_json::Map::new();
        let mut errors = Vec::new();

        for field in &parsed.fields {
            match self.resolvers.get(&field.name) {
                Some(resolver) => match resolver(field) {
                    Ok(value) => {
                        data.insert(field.name.clone(), value);
                    }
                    Err(err) => errors.push(format!("{}: {}", field.name, err)),
                },
                None => errors.push(format!("unknown field '{}'", field.name)),
            }
        }

        if errors.is_empty() {
            json!({ "data": Value::Object(data) })
        } else {
            json!({ "data": Value::Object(data), "errors": errors })
        }
    }
}

pub fn parse(query: &str) -> Result<ParsedQuery, String> {
    let trimmed = query.trim();
    if trimmed.is_empty() {
        return Err("empty query".to_string());
    }

    let operation = if trimmed.starts_with("mutation") {
        Operation::Mutation
    } else {
        Operation::Query
    };

    let start = trimmed.find('{').ok_or("missing '{'")?;
    let end = trimmed.rfind('}').ok_or("missing '}'")?;
    if end <= start {
        return Err("invalid selection set".to_string());
    }

    let body = &trimmed[start + 1..end];
    let fields = parse_fields(body)?;
    if fields.is_empty() {
        return Err("empty selection set".to_string());
    }

    Ok(ParsedQuery { operation, fields })
}

fn parse_fields(body: &str) -> Result<Vec<Field>, String> {
    let bytes = body.as_bytes();
    let mut i = 0usize;
    let mut fields = Vec::new();

    while i < bytes.len() {
        skip_ws_and_commas(bytes, &mut i);
        if i >= bytes.len() {
            break;
        }

        let name_start = i;
        while i < bytes.len() && is_ident_char(bytes[i] as char) {
            i += 1;
        }
        if i == name_start {
            return Err(format!("unexpected token near '{}'", &body[i..].trim()));
        }
        let name = body[name_start..i].to_string();

        skip_ws_and_commas(bytes, &mut i);
        let mut arguments = HashMap::new();
        if i < bytes.len() && bytes[i] == b'(' {
            i += 1;
            arguments = parse_arguments(body, bytes, &mut i)?;
        }

        fields.push(Field { name, arguments });
        skip_ws_and_commas(bytes, &mut i);
    }

    Ok(fields)
}

fn parse_arguments(
    source: &str,
    bytes: &[u8],
    i: &mut usize,
) -> Result<HashMap<String, String>, String> {
    let mut args = HashMap::new();
    loop {
        skip_ws_and_commas(bytes, i);
        if *i >= bytes.len() {
            return Err("unterminated arguments list".to_string());
        }
        if bytes[*i] == b')' {
            *i += 1;
            return Ok(args);
        }

        let key_start = *i;
        while *i < bytes.len() && is_ident_char(bytes[*i] as char) {
            *i += 1;
        }
        if *i == key_start {
            return Err("expected argument name".to_string());
        }
        let key = source[key_start..*i].to_string();

        skip_ws_and_commas(bytes, i);
        if *i >= bytes.len() || bytes[*i] != b':' {
            return Err(format!("expected ':' after argument '{}'", key));
        }
        *i += 1;
        skip_ws_and_commas(bytes, i);

        let value = parse_value_token(source, bytes, i)?;
        args.insert(key, value);
        skip_ws_and_commas(bytes, i);
    }
}

fn parse_value_token(source: &str, bytes: &[u8], i: &mut usize) -> Result<String, String> {
    if *i >= bytes.len() {
        return Err("expected value".to_string());
    }
    if bytes[*i] == b'"' {
        *i += 1;
        let start = *i;
        while *i < bytes.len() && bytes[*i] != b'"' {
            if bytes[*i] == b'\\' {
                *i += 1;
            }
            *i += 1;
        }
        if *i >= bytes.len() {
            return Err("unterminated string literal".to_string());
        }
        let value = source[start..*i].to_string();
        *i += 1;
        return Ok(value);
    }

    let start = *i;
    while *i < bytes.len() && !matches!(bytes[*i], b',' | b')' | b' ' | b'\n' | b'\t' | b'\r') {
        *i += 1;
    }
    Ok(source[start..*i].to_string())
}

fn skip_ws_and_commas(bytes: &[u8], i: &mut usize) {
    while *i < bytes.len() && matches!(bytes[*i], b' ' | b'\n' | b'\t' | b'\r' | b',') {
        *i += 1;
    }
}

fn is_ident_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
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
    fn test_parse_query_with_args() {
        let parsed = expect_ok(parse(r#"query { user(id: "7"), health }"#));
        assert_eq!(parsed.operation, Operation::Query);
        assert_eq!(parsed.fields.len(), 2);
        assert_eq!(parsed.fields[0].name, "user");
        assert_eq!(
            parsed.fields[0].arguments.get("id").cloned(),
            Some("7".to_string())
        );
    }

    #[test]
    fn test_execute_query() {
        let mut schema = Schema::new();
        schema.register("health", |_field| Ok(json!("ok")));
        schema.register("user", |field| {
            let id = field.arguments.get("id").cloned().unwrap_or_default();
            Ok(json!({ "id": id, "name": "Ada" }))
        });

        let result = schema.execute_query(r#"query { health, user(id:"1"), missing }"#);
        assert_eq!(result["data"]["health"], "ok");
        assert_eq!(result["data"]["user"]["name"], "Ada");
        assert!(result["errors"].is_array());
    }
}
