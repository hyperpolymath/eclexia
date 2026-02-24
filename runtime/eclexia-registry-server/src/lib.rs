// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Eclexia package registry server.
//!
//! This crate provides a simple HTTP server for hosting Eclexia packages.
//! It implements three core endpoints:
//! - GET /packages/:name/:version - Return package metadata
//! - GET /packages/:name/:version/download - Serve package tarball
//! - POST /packages - Upload a new package (requires authentication)
//!
//! Packages are stored in a flat filesystem structure:
//! ```text
//! packages/
//!   <name>/
//!     <version>/
//!       metadata.json
//!       <name>-<version>.tar
//! ```

use eclexia_web_server::{Method, Request, Response, Router};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};

/// Package metadata stored in metadata.json
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageMetadata {
    pub name: String,
    pub version: String,
    pub description: Option<String>,
    pub authors: Vec<String>,
    pub license: Option<String>,
    pub repository: Option<String>,
    pub dependencies: Vec<Dependency>,
    pub checksum: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Dependency {
    pub name: String,
    pub version: String,
}

/// Package registry server
pub struct RegistryServer {
    packages_dir: PathBuf,
    auth_token: Option<String>,
}

impl RegistryServer {
    /// Create a new registry server with a packages directory.
    pub fn new(packages_dir: impl AsRef<Path>) -> Self {
        Self {
            packages_dir: packages_dir.as_ref().to_path_buf(),
            auth_token: None,
        }
    }

    /// Set authentication token for POST /packages endpoint.
    pub fn with_auth_token(mut self, token: String) -> Self {
        self.auth_token = Some(token);
        self
    }

    /// Build the router for this registry server.
    pub fn router(&self) -> Router {
        let packages_dir = self.packages_dir.clone();
        let auth_token = self.auth_token.clone();

        let packages_dir_1 = packages_dir.clone();
        let packages_dir_2 = packages_dir.clone();
        let packages_dir_3 = packages_dir;

        Router::new()
            .route(Method::Get, "/packages/:name/:version", move |req| {
                let name = req.params.get("name").cloned().unwrap_or_default();
                let version = req.params.get("version").cloned().unwrap_or_default();
                get_package_metadata(&packages_dir_1, &name, &version)
            })
            .route(
                Method::Get,
                "/packages/:name/:version/download",
                move |req| {
                    let name = req.params.get("name").cloned().unwrap_or_default();
                    let version = req.params.get("version").cloned().unwrap_or_default();
                    download_package(&packages_dir_2, &name, &version)
                },
            )
            .route(Method::Post, "/packages", move |req| {
                upload_package(&packages_dir_3, &auth_token, req)
            })
    }
}

/// GET /packages/:name/:version - Return package metadata
fn get_package_metadata(packages_dir: &Path, name: &str, version: &str) -> Response {
    let metadata_path = packages_dir.join(name).join(version).join("metadata.json");

    match fs::read_to_string(&metadata_path) {
        Ok(contents) => Response::json(&contents),
        Err(_) => Response::not_found(),
    }
}

/// GET /packages/:name/:version/download - Serve package tarball
fn download_package(packages_dir: &Path, name: &str, version: &str) -> Response {
    let tarball_name = format!("{}-{}.tar", name, version);
    let tarball_path = packages_dir.join(name).join(version).join(&tarball_name);

    match fs::read(&tarball_path) {
        Ok(contents) => Response::new(200, contents)
            .with_header("content-type", "application/x-tar")
            .with_header(
                "content-disposition",
                &format!("attachment; filename=\"{}\"", tarball_name),
            ),
        Err(_) => Response::not_found(),
    }
}

/// POST /packages - Upload a new package (requires authentication)
fn upload_package(packages_dir: &Path, auth_token: &Option<String>, req: &Request) -> Response {
    // Check authentication if token is configured
    if let Some(expected_token) = auth_token {
        let provided_token = req
            .header("authorization")
            .and_then(|h| h.strip_prefix("Bearer "))
            .unwrap_or("");

        if provided_token != expected_token {
            return Response::new(401, b"Unauthorized").with_header("content-type", "text/plain");
        }
    }

    // Parse metadata from request body
    let metadata: PackageMetadata = match serde_json::from_slice(&req.body) {
        Ok(m) => m,
        Err(e) => {
            return Response::new(400, format!("Invalid metadata: {}", e).as_bytes())
                .with_header("content-type", "text/plain")
        }
    };

    // Create package directory
    let pkg_dir = packages_dir.join(&metadata.name).join(&metadata.version);
    if let Err(e) = fs::create_dir_all(&pkg_dir) {
        return Response::new(500, format!("Failed to create directory: {}", e).as_bytes())
            .with_header("content-type", "text/plain");
    }

    // Write metadata file
    let metadata_path = pkg_dir.join("metadata.json");
    let metadata_json = match serde_json::to_string_pretty(&metadata) {
        Ok(json) => json,
        Err(e) => {
            return Response::new(
                500,
                format!("Failed to serialize metadata: {}", e).as_bytes(),
            )
            .with_header("content-type", "text/plain")
        }
    };

    if let Err(e) = fs::write(&metadata_path, metadata_json) {
        return Response::new(500, format!("Failed to write metadata: {}", e).as_bytes())
            .with_header("content-type", "text/plain");
    }

    Response::new(201, b"Package uploaded successfully").with_header("content-type", "text/plain")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn setup_test_registry() -> (tempfile::TempDir, RegistryServer) {
        let temp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let server = RegistryServer::new(temp_dir.path()).with_auth_token("test-token".into());

        // Create a test package
        let pkg_dir = temp_dir.path().join("testpkg").join("1.0.0");
        fs::create_dir_all(&pkg_dir).expect("Failed to create test package dir");

        let metadata = PackageMetadata {
            name: "testpkg".to_string(),
            version: "1.0.0".to_string(),
            description: Some("A test package".to_string()),
            authors: vec!["Test Author".to_string()],
            license: Some("PMPL-1.0-or-later".to_string()),
            repository: None,
            dependencies: vec![],
            checksum: "abc123".to_string(),
        };

        let metadata_json = serde_json::to_string_pretty(&metadata).expect("Failed to serialize");
        fs::write(pkg_dir.join("metadata.json"), metadata_json).expect("Failed to write metadata");

        // Create a test tarball
        let tarball_path = pkg_dir.join("testpkg-1.0.0.tar");
        let mut file = fs::File::create(&tarball_path).expect("Failed to create tarball");
        file.write_all(b"test tarball content")
            .expect("Failed to write tarball");

        (temp_dir, server)
    }

    #[test]
    fn test_get_package_metadata() {
        let (_temp_dir, server) = setup_test_registry();
        let router = server.router();

        let req = Request {
            method: Method::Get,
            path: "/packages/testpkg/1.0.0".to_string(),
            query: Default::default(),
            params: [
                ("name".to_string(), "testpkg".to_string()),
                ("version".to_string(), "1.0.0".to_string()),
            ]
            .iter()
            .cloned()
            .collect(),
            headers: Default::default(),
            body: vec![],
            version: "HTTP/1.1".to_string(),
        };

        let response = router.dispatch(&req);
        assert_eq!(response.status, 200);

        let metadata: PackageMetadata =
            serde_json::from_slice(&response.body).expect("Failed to parse metadata");
        assert_eq!(metadata.name, "testpkg");
        assert_eq!(metadata.version, "1.0.0");
    }

    #[test]
    fn test_download_package() {
        let (_temp_dir, server) = setup_test_registry();
        let router = server.router();

        let req = Request {
            method: Method::Get,
            path: "/packages/testpkg/1.0.0/download".to_string(),
            query: Default::default(),
            params: [
                ("name".to_string(), "testpkg".to_string()),
                ("version".to_string(), "1.0.0".to_string()),
            ]
            .iter()
            .cloned()
            .collect(),
            headers: Default::default(),
            body: vec![],
            version: "HTTP/1.1".to_string(),
        };

        let response = router.dispatch(&req);
        assert_eq!(response.status, 200);
        assert_eq!(response.body, b"test tarball content");
        assert_eq!(
            response.headers.get("content-type"),
            Some(&"application/x-tar".to_string())
        );
    }
}
