// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Minimal HTTP server exposing /health and /ready endpoints for Kubernetes.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;

use crate::Runtime;

/// Simple health server that answers /health and /ready requests.
pub struct HealthServer {
    addr: String,
    runtime: Arc<Mutex<Runtime>>,
}

impl HealthServer {
    /// Create a new server bound to the provided address.
    pub fn new(addr: impl Into<String>, runtime: Arc<Mutex<Runtime>>) -> Self {
        Self {
            addr: addr.into(),
            runtime,
        }
    }

    /// Run the server (blocking).
    pub fn run(self) -> std::io::Result<()> {
        let listener = TcpListener::bind(&self.addr)?;
        eprintln!("health server listening on {}", self.addr);

        for stream in listener.incoming() {
            match stream {
                Ok(stream) => {
                    let runtime = Arc::clone(&self.runtime);
                    thread::spawn(move || {
                        let _ = handle_connection(stream, runtime);
                    });
                }
                Err(err) => {
                    eprintln!("health server error: {}", err);
                }
            }
        }

        Ok(())
    }
}

fn handle_connection(mut stream: TcpStream, runtime: Arc<Mutex<Runtime>>) -> std::io::Result<()> {
    let mut buffer = [0u8; 1024];
    let n = stream.read(&mut buffer)?;
    if n == 0 {
        return Ok(());
    }

    let request = String::from_utf8_lossy(&buffer[..n]);
    let line = request.lines().next().unwrap_or("");
    let mut parts = line.split_whitespace();
    let _method = parts.next().unwrap_or("");
    let path = parts.next().unwrap_or("");

    let (status_line, body) = match path {
        "/health" => {
            let snapshot = match runtime.lock() {
                Ok(guard) => guard.health_snapshot(),
                Err(poisoned) => poisoned.into_inner().health_snapshot(),
            };
            let body = format!(
                r#"{{"status":"ok","total_resources":{},"carbon_signal":"{:?}"}}"#,
                snapshot.stats.total_resources, snapshot.carbon_signal
            );
            ("HTTP/1.1 200 OK", body)
        }
        "/ready" => {
            let ready = match runtime.lock() {
                Ok(guard) => guard.is_ready(),
                Err(poisoned) => poisoned.into_inner().is_ready(),
            };
            let body = format!(r#"{{"ready":{}}}"#, ready);
            let status = if ready {
                "HTTP/1.1 200 OK"
            } else {
                "HTTP/1.1 503 Service Unavailable"
            };
            (status, body)
        }
        _ => {
            let body = r#"{"error":"not found"}"#.to_string();
            ("HTTP/1.1 404 Not Found", body)
        }
    };

    let response = format!(
        "{status}\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n{body}",
        body.len(),
        status = status_line,
        body = body,
    );

    stream.write_all(response.as_bytes())?;
    stream.flush()?;
    Ok(())
}
