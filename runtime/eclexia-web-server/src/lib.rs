// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Lightweight HTTP server/router foundation for Eclexia.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Method {
    Get,
    Post,
    Put,
    Patch,
    Delete,
    Head,
    Options,
}

impl Method {
    pub fn parse(input: &str) -> Option<Self> {
        match input {
            "GET" => Some(Self::Get),
            "POST" => Some(Self::Post),
            "PUT" => Some(Self::Put),
            "PATCH" => Some(Self::Patch),
            "DELETE" => Some(Self::Delete),
            "HEAD" => Some(Self::Head),
            "OPTIONS" => Some(Self::Options),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Request {
    pub method: Method,
    pub path: String,
    pub query: HashMap<String, String>,
    pub params: HashMap<String, String>,
    pub headers: HashMap<String, String>,
    pub body: Vec<u8>,
    pub version: String,
}

impl Request {
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .get(&name.to_ascii_lowercase())
            .map(std::string::String::as_str)
    }
}

#[derive(Debug, Clone)]
pub struct Response {
    pub status: u16,
    pub headers: HashMap<String, String>,
    pub body: Vec<u8>,
}

impl Response {
    pub fn new(status: u16, body: impl Into<Vec<u8>>) -> Self {
        Self {
            status,
            headers: HashMap::new(),
            body: body.into(),
        }
    }

    pub fn text(status: u16, body: &str) -> Self {
        let mut out = Self::new(status, body.as_bytes().to_vec());
        out.headers.insert(
            "content-type".to_string(),
            "text/plain; charset=utf-8".to_string(),
        );
        out
    }

    pub fn json(body: &str) -> Self {
        let mut out = Self::new(200, body.as_bytes().to_vec());
        out.headers
            .insert("content-type".to_string(), "application/json".to_string());
        out
    }

    pub fn not_found() -> Self {
        Self::text(404, "Not Found")
    }

    pub fn method_not_allowed() -> Self {
        Self::text(405, "Method Not Allowed")
    }

    pub fn with_header(mut self, key: &str, value: &str) -> Self {
        self.headers
            .insert(key.to_ascii_lowercase(), value.to_string());
        self
    }
}

pub type Handler = Arc<dyn Fn(&Request) -> Response + Send + Sync + 'static>;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Segment {
    Static(String),
    Param(String),
    Wildcard,
}

#[derive(Clone)]
struct Route {
    method: Method,
    pattern: String,
    segments: Vec<Segment>,
    handler: Handler,
}

impl std::fmt::Debug for Route {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Route")
            .field("method", &self.method)
            .field("pattern", &self.pattern)
            .field("segments", &self.segments)
            .finish()
    }
}

#[derive(Default, Clone)]
pub struct Router {
    routes: Vec<Route>,
}

impl Router {
    pub fn new() -> Self {
        Self { routes: Vec::new() }
    }

    pub fn route<F>(mut self, method: Method, pattern: &str, handler: F) -> Self
    where
        F: Fn(&Request) -> Response + Send + Sync + 'static,
    {
        self.add_route(method, pattern, handler);
        self
    }

    pub fn add_route<F>(&mut self, method: Method, pattern: &str, handler: F)
    where
        F: Fn(&Request) -> Response + Send + Sync + 'static,
    {
        self.routes.push(Route {
            method,
            pattern: normalize_path(pattern),
            segments: parse_pattern(pattern),
            handler: Arc::new(handler),
        });
    }

    pub fn dispatch(&self, req: &Request) -> Response {
        let route_path = normalize_path(&req.path);
        let mut path_exists_with_other_method = false;

        for route in &self.routes {
            if let Some(params) = match_segments(&route.segments, &split_segments(&route_path)) {
                if route.method == req.method {
                    let mut with_params = req.clone();
                    with_params.params = params;
                    return (route.handler)(&with_params);
                }
                path_exists_with_other_method = true;
            }
        }

        if path_exists_with_other_method {
            Response::method_not_allowed()
        } else {
            Response::not_found()
        }
    }
}

pub struct HttpServer {
    bind: String,
    router: Router,
}

impl HttpServer {
    pub fn new(bind: &str, router: Router) -> Self {
        Self {
            bind: bind.to_string(),
            router,
        }
    }

    pub fn run(&self) -> std::io::Result<()> {
        let listener = TcpListener::bind(&self.bind)?;
        let router = Arc::new(self.router.clone());

        for stream in listener.incoming() {
            let Ok(stream) = stream else {
                continue;
            };
            let router = router.clone();
            std::thread::spawn(move || {
                let _ = handle_connection(stream, &router);
            });
        }
        Ok(())
    }
}

pub fn parse_request_bytes(raw: &[u8]) -> Result<Request, String> {
    let header_end = raw
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .ok_or("missing header terminator")?;
    let header_bytes = &raw[..header_end];
    let body = raw[header_end + 4..].to_vec();
    let header_text = std::str::from_utf8(header_bytes).map_err(|_| "invalid header utf8")?;

    let mut lines = header_text.split("\r\n");
    let request_line = lines.next().ok_or("missing request line")?;
    let mut parts = request_line.split_whitespace();
    let method = Method::parse(parts.next().ok_or("missing method")?).ok_or("invalid method")?;
    let target = parts.next().ok_or("missing request target")?;
    let version = parts.next().ok_or("missing http version")?.to_string();

    let mut headers = HashMap::new();
    for line in lines {
        if line.is_empty() {
            continue;
        }
        let (k, v) = line
            .split_once(':')
            .ok_or_else(|| format!("invalid header line '{}'", line))?;
        headers.insert(k.trim().to_ascii_lowercase(), v.trim().to_string());
    }

    let (path, query) = split_path_and_query(target);
    Ok(Request {
        method,
        path,
        query,
        params: HashMap::new(),
        headers,
        body,
        version,
    })
}

fn handle_connection(mut stream: TcpStream, router: &Router) -> std::io::Result<()> {
    let mut buf = [0u8; 8192];
    let mut read_buf = Vec::new();

    loop {
        let n = stream.read(&mut buf)?;
        if n == 0 {
            break;
        }
        read_buf.extend_from_slice(&buf[..n]);
        if read_buf.windows(4).any(|w| w == b"\r\n\r\n") {
            break;
        }
        if read_buf.len() > 64 * 1024 {
            write_response(&mut stream, &Response::text(413, "Payload Too Large"))?;
            return Ok(());
        }
    }

    let header_end = match read_buf.windows(4).position(|w| w == b"\r\n\r\n") {
        Some(pos) => pos,
        None => {
            write_response(&mut stream, &Response::text(400, "Bad Request"))?;
            return Ok(());
        }
    };

    let header_prefix = &read_buf[..header_end];
    let header_text = match std::str::from_utf8(header_prefix) {
        Ok(v) => v,
        Err(_) => {
            write_response(&mut stream, &Response::text(400, "Bad Request"))?;
            return Ok(());
        }
    };

    let content_length = header_text
        .lines()
        .find_map(|line| {
            let (k, v) = line.split_once(':')?;
            if k.trim().eq_ignore_ascii_case("content-length") {
                v.trim().parse::<usize>().ok()
            } else {
                None
            }
        })
        .unwrap_or(0);

    let already = read_buf.len().saturating_sub(header_end + 4);
    if already < content_length {
        let mut remain = vec![0u8; content_length - already];
        stream.read_exact(&mut remain)?;
        read_buf.extend_from_slice(&remain);
    }

    let req = match parse_request_bytes(&read_buf) {
        Ok(req) => req,
        Err(_) => {
            write_response(&mut stream, &Response::text(400, "Bad Request"))?;
            return Ok(());
        }
    };

    let response = router.dispatch(&req);
    write_response(&mut stream, &response)?;
    Ok(())
}

fn write_response(stream: &mut TcpStream, response: &Response) -> std::io::Result<()> {
    let mut out = Vec::new();
    let reason = reason_phrase(response.status);
    out.extend_from_slice(format!("HTTP/1.1 {} {}\r\n", response.status, reason).as_bytes());

    let mut headers = response.headers.clone();
    headers
        .entry("content-length".to_string())
        .or_insert_with(|| response.body.len().to_string());
    headers
        .entry("connection".to_string())
        .or_insert_with(|| "close".to_string());

    for (k, v) in headers {
        out.extend_from_slice(format!("{}: {}\r\n", k, v).as_bytes());
    }
    out.extend_from_slice(b"\r\n");
    out.extend_from_slice(&response.body);
    stream.write_all(&out)
}

fn reason_phrase(status: u16) -> &'static str {
    match status {
        200 => "OK",
        201 => "Created",
        202 => "Accepted",
        204 => "No Content",
        400 => "Bad Request",
        401 => "Unauthorized",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        409 => "Conflict",
        413 => "Payload Too Large",
        422 => "Unprocessable Entity",
        500 => "Internal Server Error",
        503 => "Service Unavailable",
        _ => "OK",
    }
}

fn parse_pattern(pattern: &str) -> Vec<Segment> {
    split_segments(&normalize_path(pattern))
        .into_iter()
        .map(|seg| {
            if seg == "*" {
                Segment::Wildcard
            } else if let Some(name) = seg.strip_prefix(':') {
                Segment::Param(name.to_string())
            } else {
                Segment::Static(seg.to_string())
            }
        })
        .collect()
}

fn normalize_path(path: &str) -> String {
    let raw = path.split('?').next().unwrap_or(path);
    if raw.is_empty() || raw == "/" {
        return "/".to_string();
    }
    let joined = split_segments(raw).join("/");
    format!("/{}", joined)
}

fn split_segments(path: &str) -> Vec<&str> {
    path.trim_matches('/')
        .split('/')
        .filter(|seg| !seg.is_empty())
        .collect()
}

fn match_segments(pattern: &[Segment], actual: &[&str]) -> Option<HashMap<String, String>> {
    let mut params = HashMap::new();
    let mut i = 0usize;
    let mut j = 0usize;

    while i < pattern.len() && j < actual.len() {
        match &pattern[i] {
            Segment::Static(s) if s == actual[j] => {
                i += 1;
                j += 1;
            }
            Segment::Param(name) => {
                params.insert(name.clone(), actual[j].to_string());
                i += 1;
                j += 1;
            }
            Segment::Wildcard => {
                params.insert("wildcard".to_string(), actual[j..].join("/"));
                return Some(params);
            }
            _ => return None,
        }
    }

    if i == pattern.len() && j == actual.len() {
        Some(params)
    } else if i + 1 == pattern.len() && matches!(pattern[i], Segment::Wildcard) {
        params.insert("wildcard".to_string(), String::new());
        Some(params)
    } else {
        None
    }
}

fn split_path_and_query(target: &str) -> (String, HashMap<String, String>) {
    let (path, query_raw) = match target.split_once('?') {
        Some((p, q)) => (normalize_path(p), q),
        None => (normalize_path(target), ""),
    };

    let mut query = HashMap::new();
    for pair in query_raw.split('&') {
        if pair.is_empty() {
            continue;
        }
        if let Some((k, v)) = pair.split_once('=') {
            query.insert(url_decode(k), url_decode(v));
        } else {
            query.insert(url_decode(pair), String::new());
        }
    }
    (path, query)
}

fn url_decode(input: &str) -> String {
    let bytes = input.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'+' => {
                out.push(b' ');
                i += 1;
            }
            b'%' if i + 2 < bytes.len() => {
                let hi = bytes[i + 1] as char;
                let lo = bytes[i + 2] as char;
                if let (Some(h), Some(l)) = (hi.to_digit(16), lo.to_digit(16)) {
                    out.push(((h << 4) | l) as u8);
                    i += 3;
                } else {
                    out.push(bytes[i]);
                    i += 1;
                }
            }
            other => {
                out.push(other);
                i += 1;
            }
        }
    }
    String::from_utf8_lossy(&out).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_some<T>(value: Option<T>, msg: &str) -> T {
        match value {
            Some(v) => v,
            None => panic!("{}", msg),
        }
    }

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(v) => v,
            Err(e) => panic!("expected ok, got {:?}", e),
        }
    }

    #[test]
    fn test_route_param_match() {
        let router = Router::new().route(Method::Get, "/users/:id", |req| {
            Response::text(
                200,
                req.params
                    .get("id")
                    .map(std::string::String::as_str)
                    .unwrap_or("missing"),
            )
        });

        let req = Request {
            method: Method::Get,
            path: "/users/42".to_string(),
            query: HashMap::new(),
            params: HashMap::new(),
            headers: HashMap::new(),
            body: Vec::new(),
            version: "HTTP/1.1".to_string(),
        };

        let res = router.dispatch(&req);
        assert_eq!(res.status, 200);
        assert_eq!(String::from_utf8_lossy(&res.body), "42");
    }

    #[test]
    fn test_wildcard_match() {
        let router = Router::new().route(Method::Get, "/assets/*", |req| {
            Response::text(
                200,
                req.params
                    .get("wildcard")
                    .map(std::string::String::as_str)
                    .unwrap_or(""),
            )
        });

        let req = Request {
            method: Method::Get,
            path: "/assets/css/main.css".to_string(),
            query: HashMap::new(),
            params: HashMap::new(),
            headers: HashMap::new(),
            body: Vec::new(),
            version: "HTTP/1.1".to_string(),
        };
        let res = router.dispatch(&req);
        assert_eq!(String::from_utf8_lossy(&res.body), "css/main.css");
    }

    #[test]
    fn test_parse_request_bytes_with_query() {
        let raw =
            b"GET /api/users?id=7&active=true HTTP/1.1\r\nHost: localhost\r\nContent-Length: 0\r\n\r\n";
        let req = expect_ok(parse_request_bytes(raw));
        assert_eq!(req.method, Method::Get);
        assert_eq!(req.path, "/api/users");
        assert_eq!(expect_some(req.query.get("id").cloned(), "missing id"), "7");
        assert_eq!(
            expect_some(req.query.get("active").cloned(), "missing active"),
            "true"
        );
    }

    #[test]
    fn test_not_found_and_method_not_allowed() {
        let router = Router::new().route(Method::Get, "/health", |_req| Response::text(200, "ok"));
        let post = Request {
            method: Method::Post,
            path: "/health".to_string(),
            query: HashMap::new(),
            params: HashMap::new(),
            headers: HashMap::new(),
            body: Vec::new(),
            version: "HTTP/1.1".to_string(),
        };
        let not_allowed = router.dispatch(&post);
        assert_eq!(not_allowed.status, 405);

        let missing = Request {
            method: Method::Get,
            path: "/missing".to_string(),
            query: HashMap::new(),
            params: HashMap::new(),
            headers: HashMap::new(),
            body: Vec::new(),
            version: "HTTP/1.1".to_string(),
        };
        let not_found = router.dispatch(&missing);
        assert_eq!(not_found.status, 404);
    }
}
