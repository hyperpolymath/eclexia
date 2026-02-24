// SPDX-License-Identifier: PMPL-1.0-or-later

//! gRPC service registry and wire framing primitives.

use std::collections::HashMap;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatusCode {
    Ok = 0,
    Cancelled = 1,
    Unknown = 2,
    InvalidArgument = 3,
    NotFound = 5,
    AlreadyExists = 6,
    PermissionDenied = 7,
    Unauthenticated = 16,
    Internal = 13,
    Unavailable = 14,
}

#[derive(Debug, Clone)]
pub struct GrpcRequest {
    pub service: String,
    pub method: String,
    pub metadata: HashMap<String, String>,
    pub payload: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct GrpcResponse {
    pub status: StatusCode,
    pub message: String,
    pub metadata: HashMap<String, String>,
    pub payload: Vec<u8>,
}

impl GrpcResponse {
    pub fn ok(payload: impl Into<Vec<u8>>) -> Self {
        Self {
            status: StatusCode::Ok,
            message: String::new(),
            metadata: HashMap::new(),
            payload: payload.into(),
        }
    }

    pub fn error(status: StatusCode, message: &str) -> Self {
        Self {
            status,
            message: message.to_string(),
            metadata: HashMap::new(),
            payload: Vec::new(),
        }
    }
}

pub type Handler = Arc<dyn Fn(&GrpcRequest) -> GrpcResponse + Send + Sync + 'static>;

#[derive(Default)]
pub struct ServiceRegistry {
    handlers: HashMap<(String, String), Handler>,
}

impl ServiceRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register<F>(&mut self, service: &str, method: &str, handler: F)
    where
        F: Fn(&GrpcRequest) -> GrpcResponse + Send + Sync + 'static,
    {
        self.handlers
            .insert((service.to_string(), method.to_string()), Arc::new(handler));
    }

    pub fn call(&self, req: &GrpcRequest) -> GrpcResponse {
        match self
            .handlers
            .get(&(req.service.clone(), req.method.clone()))
        {
            Some(handler) => handler(req),
            None => GrpcResponse::error(StatusCode::NotFound, "method not found"),
        }
    }

    pub fn call_full_method(
        &self,
        full_method: &str,
        payload: &[u8],
        metadata: HashMap<String, String>,
    ) -> GrpcResponse {
        let parts = full_method
            .trim_start_matches('/')
            .split('/')
            .collect::<Vec<_>>();
        if parts.len() != 2 {
            return GrpcResponse::error(StatusCode::InvalidArgument, "invalid grpc method path");
        }
        let req = GrpcRequest {
            service: parts[0].to_string(),
            method: parts[1].to_string(),
            metadata,
            payload: payload.to_vec(),
        };
        self.call(&req)
    }
}

/// Encode payload using gRPC message framing:
/// 1 byte compression flag + 4 bytes big-endian message length + message bytes.
pub fn encode_grpc_frame(payload: &[u8], compressed: bool) -> Vec<u8> {
    let mut out = Vec::with_capacity(payload.len() + 5);
    out.push(if compressed { 1 } else { 0 });
    out.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    out.extend_from_slice(payload);
    out
}

pub fn decode_grpc_frame(raw: &[u8]) -> Result<(bool, Vec<u8>), String> {
    if raw.len() < 5 {
        return Err("grpc frame too short".to_string());
    }
    let compressed = raw[0] == 1;
    let len = u32::from_be_bytes([raw[1], raw[2], raw[3], raw[4]]) as usize;
    if raw.len() != 5 + len {
        return Err("grpc frame length mismatch".to_string());
    }
    Ok((compressed, raw[5..].to_vec()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_call() {
        let mut registry = ServiceRegistry::new();
        registry.register("Echo", "Ping", |req| GrpcResponse::ok(req.payload.clone()));

        let req = GrpcRequest {
            service: "Echo".to_string(),
            method: "Ping".to_string(),
            metadata: HashMap::new(),
            payload: b"hi".to_vec(),
        };
        let res = registry.call(&req);
        assert_eq!(res.status, StatusCode::Ok);
        assert_eq!(res.payload, b"hi".to_vec());
    }

    #[test]
    fn test_call_full_method() {
        let mut registry = ServiceRegistry::new();
        registry.register("Svc", "Do", |_req| GrpcResponse::ok(b"done".to_vec()));
        let res = registry.call_full_method("/Svc/Do", b"{}", HashMap::new());
        assert_eq!(res.status, StatusCode::Ok);
        assert_eq!(res.payload, b"done");
    }

    #[test]
    fn test_grpc_frame_roundtrip() {
        let frame = encode_grpc_frame(b"payload", false);
        let (compressed, payload) = decode_grpc_frame(&frame).expect("decode failed");
        assert!(!compressed);
        assert_eq!(payload, b"payload");
    }
}
