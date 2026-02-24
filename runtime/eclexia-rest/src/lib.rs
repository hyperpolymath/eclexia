// SPDX-License-Identifier: PMPL-1.0-or-later

//! REST utilities on top of `eclexia-web-server`.

use eclexia_web_server::{Method, Request, Response, Router};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

#[derive(Debug, Clone)]
pub struct RestEndpoint {
    pub method: Method,
    pub path: String,
    pub operation_id: String,
}

#[derive(Debug, Clone, Default)]
pub struct RestApi {
    endpoints: Vec<RestEndpoint>,
}

impl RestApi {
    pub fn new() -> Self {
        Self {
            endpoints: Vec::new(),
        }
    }

    pub fn resource(mut self, base_path: &str, name: &str) -> Self {
        let base = normalize_resource_base(base_path);
        self.endpoints.push(RestEndpoint {
            method: Method::Get,
            path: base.to_string(),
            operation_id: format!("list_{}", name),
        });
        self.endpoints.push(RestEndpoint {
            method: Method::Get,
            path: format!("{}/:id", base),
            operation_id: format!("get_{}", name),
        });
        self.endpoints.push(RestEndpoint {
            method: Method::Post,
            path: base.to_string(),
            operation_id: format!("create_{}", name),
        });
        self.endpoints.push(RestEndpoint {
            method: Method::Put,
            path: format!("{}/:id", base),
            operation_id: format!("update_{}", name),
        });
        self.endpoints.push(RestEndpoint {
            method: Method::Delete,
            path: format!("{}/:id", base),
            operation_id: format!("delete_{}", name),
        });
        self
    }

    pub fn endpoints(&self) -> &[RestEndpoint] {
        &self.endpoints
    }

    pub fn openapi_fragment(&self) -> Value {
        let mut paths = serde_json::Map::new();
        for endpoint in &self.endpoints {
            let method = match endpoint.method {
                Method::Get => "get",
                Method::Post => "post",
                Method::Put => "put",
                Method::Patch => "patch",
                Method::Delete => "delete",
                Method::Head => "head",
                Method::Options => "options",
            };
            let entry = paths
                .entry(endpoint.path.clone())
                .or_insert_with(|| json!({}));
            if let Some(obj) = entry.as_object_mut() {
                obj.insert(
                    method.to_string(),
                    json!({
                        "operationId": endpoint.operation_id,
                        "responses": {"200": {"description": "OK"}},
                    }),
                );
            }
        }
        json!({ "paths": paths })
    }
}

#[derive(Debug, Clone, Default)]
pub struct InMemoryCollection {
    state: Arc<Mutex<CollectionState>>,
}

#[derive(Debug, Default)]
struct CollectionState {
    next_id: u64,
    items: BTreeMap<String, Value>,
}

impl InMemoryCollection {
    pub fn new() -> Self {
        Self {
            state: Arc::new(Mutex::new(CollectionState::default())),
        }
    }

    pub fn insert_with_id(&self, id: impl Into<String>, value: Value) {
        let mut guard = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        guard.items.insert(id.into(), value);
    }

    pub fn mount(&self, router: &mut Router, base_path: &str) {
        let base = normalize_resource_base(base_path);

        let list_store = self.clone();
        router.add_route(Method::Get, &base, move |_req: &Request| {
            list_store.handle_list()
        });

        let get_store = self.clone();
        router.add_route(
            Method::Get,
            &format!("{}/:id", base),
            move |req: &Request| {
                let Some(id) = req.params.get("id") else {
                    return json_error(400, "missing id param");
                };
                get_store.handle_get(id)
            },
        );

        let create_store = self.clone();
        router.add_route(Method::Post, &base, move |req: &Request| {
            create_store.handle_create(&req.body)
        });

        let update_store = self.clone();
        router.add_route(
            Method::Put,
            &format!("{}/:id", base),
            move |req: &Request| {
                let Some(id) = req.params.get("id") else {
                    return json_error(400, "missing id param");
                };
                update_store.handle_update(id, &req.body)
            },
        );

        let update_patch_store = self.clone();
        router.add_route(
            Method::Patch,
            &format!("{}/:id", base),
            move |req: &Request| {
                let Some(id) = req.params.get("id") else {
                    return json_error(400, "missing id param");
                };
                update_patch_store.handle_patch(id, &req.body)
            },
        );

        let delete_store = self.clone();
        router.add_route(
            Method::Delete,
            &format!("{}/:id", base),
            move |req: &Request| {
                let Some(id) = req.params.get("id") else {
                    return json_error(400, "missing id param");
                };
                delete_store.handle_delete(id)
            },
        );
    }

    fn handle_list(&self) -> Response {
        let guard = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let mut out = Vec::new();
        for (id, item) in &guard.items {
            out.push(json!({
                "id": id,
                "value": item
            }));
        }
        json_ok(200, &json!({ "items": out }))
    }

    fn handle_get(&self, id: &str) -> Response {
        let guard = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        match guard.items.get(id) {
            Some(value) => json_ok(200, &json!({ "id": id, "value": value })),
            None => json_error(404, "resource not found"),
        }
    }

    fn handle_create(&self, body: &[u8]) -> Response {
        let payload = match parse_json_payload(body) {
            Ok(v) => v,
            Err(msg) => return json_error(422, &msg),
        };

        let mut guard = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let id = if guard.next_id == 0 {
            guard.next_id = 1;
            "1".to_string()
        } else {
            guard.next_id += 1;
            guard.next_id.to_string()
        };
        guard.items.insert(id.clone(), payload);

        json_ok(201, &json!({ "id": id }))
    }

    fn handle_update(&self, id: &str, body: &[u8]) -> Response {
        let payload = match parse_json_payload(body) {
            Ok(v) => v,
            Err(msg) => return json_error(422, &msg),
        };

        let mut guard = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if !guard.items.contains_key(id) {
            return json_error(404, "resource not found");
        }
        guard.items.insert(id.to_string(), payload);
        json_ok(200, &json!({ "id": id }))
    }

    fn handle_patch(&self, id: &str, body: &[u8]) -> Response {
        let payload = match parse_json_payload(body) {
            Ok(v) => v,
            Err(msg) => return json_error(422, &msg),
        };

        let mut guard = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let Some(existing) = guard.items.get_mut(id) else {
            return json_error(404, "resource not found");
        };

        merge_values(existing, &payload);
        json_ok(200, &json!({ "id": id }))
    }

    fn handle_delete(&self, id: &str) -> Response {
        let mut guard = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if guard.items.remove(id).is_none() {
            return json_error(404, "resource not found");
        }
        json_ok(200, &json!({ "deleted": id }))
    }
}

fn normalize_resource_base(input: &str) -> String {
    let trimmed = input.trim();
    if trimmed.is_empty() || trimmed == "/" {
        "/".to_string()
    } else {
        format!("/{}", trimmed.trim_matches('/'))
    }
}

fn parse_json_payload(body: &[u8]) -> Result<Value, String> {
    if body.is_empty() {
        return Ok(json!({}));
    }
    serde_json::from_slice(body).map_err(|e| format!("invalid json body: {}", e))
}

fn merge_values(target: &mut Value, patch: &Value) {
    match (target, patch) {
        (Value::Object(t), Value::Object(p)) => {
            for (k, v) in p {
                match t.get_mut(k) {
                    Some(existing) => merge_values(existing, v),
                    None => {
                        t.insert(k.clone(), v.clone());
                    }
                }
            }
        }
        (target_slot, patch_value) => {
            *target_slot = patch_value.clone();
        }
    }
}

fn json_ok(status: u16, value: &Value) -> Response {
    let body = serde_json::to_vec(value).unwrap_or_else(|_| b"{\"error\":\"encode\"}".to_vec());
    Response::new(status, body).with_header("content-type", "application/json")
}

fn json_error(status: u16, message: &str) -> Response {
    let body = serde_json::to_vec(&json!({ "error": message }))
        .unwrap_or_else(|_| b"{\"error\":\"encode\"}".to_vec());
    Response::new(status, body).with_header("content-type", "application/json")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn req(method: Method, path: &str, body: &[u8], params: &[(&str, &str)]) -> Request {
        let mut p = HashMap::new();
        for (k, v) in params {
            p.insert((*k).to_string(), (*v).to_string());
        }
        Request {
            method,
            path: path.to_string(),
            query: HashMap::new(),
            params: p,
            headers: HashMap::new(),
            body: body.to_vec(),
            version: "HTTP/1.1".to_string(),
        }
    }

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(v) => v,
            Err(e) => panic!("expected ok, got {:?}", e),
        }
    }

    #[test]
    fn test_crud_resource_generation() {
        let api = RestApi::new().resource("/users", "user");
        assert_eq!(api.endpoints().len(), 5);
        assert_eq!(api.endpoints()[0].path, "/users");
        let openapi = api.openapi_fragment();
        assert!(openapi["paths"]["/users"]["get"].is_object());
    }

    #[test]
    fn test_in_memory_collection_crud() {
        let collection = InMemoryCollection::new();

        let create = collection.handle_create(br#"{"name":"Ada"}"#);
        assert_eq!(create.status, 201);

        let get = collection.handle_get("1");
        assert_eq!(get.status, 200);

        let patch = collection.handle_patch("1", br#"{"role":"admin"}"#);
        assert_eq!(patch.status, 200);

        let listed = collection.handle_list();
        let listed_json: Value = expect_ok(serde_json::from_slice(&listed.body));
        assert_eq!(listed_json["items"].as_array().map_or(0, Vec::len), 1);
        assert_eq!(listed_json["items"][0]["value"]["role"], "admin");

        let deleted = collection.handle_delete("1");
        assert_eq!(deleted.status, 200);
        assert_eq!(collection.handle_get("1").status, 404);
    }

    #[test]
    fn test_mount_routes_into_router() {
        let mut router = Router::new();
        let collection = InMemoryCollection::new();
        collection.insert_with_id("10", json!({"name":"Grace"}));
        collection.mount(&mut router, "/users");

        let request = req(Method::Get, "/users/10", b"", &[("id", "10")]);
        let response = router.dispatch(&request);
        assert_eq!(response.status, 200);
        let body: Value = expect_ok(serde_json::from_slice(&response.body));
        assert_eq!(body["value"]["name"], "Grace");
    }
}
