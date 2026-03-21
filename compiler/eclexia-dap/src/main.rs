// SPDX-License-Identifier: PMPL-1.0-or-later
//! Debug Adapter Protocol (DAP) implementation for Eclexia
//!
//! This is a minimal DAP adapter for Eclexia, focusing on resource-aware debugging.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};

#[derive(Debug, Serialize, Deserialize)]
struct DapRequest {
    seq: i64,
    r#type: String,
    command: String,
    arguments: Option<serde_json::Value>,
}

#[derive(Debug, Serialize)]
struct DapResponse {
    seq: i64,
    r#type: String,
    request_seq: i64,
    command: String,
    success: bool,
    message: Option<String>,
    body: Option<serde_json::Value>,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:4713")?;
    println!("Eclexia DAP server listening on 127.0.0.1:4713");

    loop {
        let (socket, _) = listener.accept().await?;
        tokio::spawn(async move {
            if let Err(e) = handle_client(socket).await {
                eprintln!("Error handling client: {}", e);
            }
        });
    }
}

async fn handle_client(stream: TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let (reader, mut writer) = tokio::io::split(stream);
    let mut reader = BufReader::new(reader);
    let mut buf = String::new();

    loop {
        buf.clear();
        let bytes_read = reader.read_line(&mut buf).await?;
        if bytes_read == 0 {
            break;
        }

        let request: DapRequest = serde_json::from_str(&buf)?;
        let response = match request.command.as_str() {
            "initialize" => {
                serde_json::to_string(&DapResponse {
                    seq: 1,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "initialize".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({
                        "supportsConfigurationDoneRequest": true,
                        "supportsFunctionBreakpoints": true,
                        "supportsConditionalBreakpoints": true,
                        "supportsEvaluateForHovers": true,
                        "exceptionBreakpointFilters": [],
                    })),
                })?
            }
            "launch" => {
                serde_json::to_string(&DapResponse {
                    seq: 2,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "launch".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"success": true})),
                })?
            }
            "setBreakpoints" => {
                serde_json::to_string(&DapResponse {
                    seq: 3,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "setBreakpoints".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"breakpoints": []})),
                })?
            }
            "threads" => {
                serde_json::to_string(&DapResponse {
                    seq: 4,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "threads".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"threads": [{"id": 1, "name": "main"}]}));
                })?
            }
            "stackTrace" => {
                serde_json::to_string(&DapResponse {
                    seq: 5,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "stackTrace".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"stackFrames": []})),
                })?
            }
            "scopes" => {
                serde_json::to_string(&DapResponse {
                    seq: 6,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "scopes".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"scopes": [{"name": "Locals", "variablesReference": 1, "expensive": false}]}));
                })?
            }
            "variables" => {
                serde_json::to_string(&DapResponse {
                    seq: 7,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "variables".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"variables": []})),
                })?
            }
            "disconnect" => {
                serde_json::to_string(&DapResponse {
                    seq: 8,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "disconnect".to_string(),
                    success: true,
                    message: None,
                    body: None,
                })?
            }
            _ => {
                serde_json::to_string(&DapResponse {
                    seq: 0,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: request.command,
                    success: false,
                    message: Some("Unknown command".to_string()),
                    body: None,
                })?
            }
        };

        writer.write_all(response.as_bytes()).await?;
        writer.write_all(b"\n").await?;
    }

    Ok(())
}
