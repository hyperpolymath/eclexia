// SPDX-License-Identifier: PMPL-1.0-or-later

//! Child process execution helpers.

use std::collections::HashMap;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

#[derive(Debug, Clone)]
pub struct ProcessOutput {
    pub status_code: i32,
    pub stdout: String,
    pub stderr: String,
    pub timed_out: bool,
}

#[derive(Debug, Clone, Default)]
pub struct ProcessSpec {
    pub program: String,
    pub args: Vec<String>,
    pub env: HashMap<String, String>,
    pub cwd: Option<PathBuf>,
    pub timeout: Option<Duration>,
}

pub fn run(command: &str, args: &[&str]) -> Result<ProcessOutput, String> {
    run_with_spec(ProcessSpec {
        program: command.to_string(),
        args: args.iter().map(|s| (*s).to_string()).collect(),
        ..ProcessSpec::default()
    })
}

pub fn run_with_spec(spec: ProcessSpec) -> Result<ProcessOutput, String> {
    if spec.program.trim().is_empty() {
        return Err("program must not be empty".to_string());
    }

    let mut cmd = Command::new(&spec.program);
    cmd.args(&spec.args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    if let Some(cwd) = &spec.cwd {
        cmd.current_dir(cwd);
    }
    for (k, v) in &spec.env {
        cmd.env(k, v);
    }

    let mut child = cmd
        .spawn()
        .map_err(|e| format!("failed to spawn '{}': {}", spec.program, e))?;

    if let Some(timeout) = spec.timeout {
        let deadline = Instant::now() + timeout;
        loop {
            match child.try_wait() {
                Ok(Some(_)) => break,
                Ok(None) => {
                    if Instant::now() >= deadline {
                        let _ = child.kill();
                        let output = child.wait_with_output().map_err(|e| e.to_string())?;
                        return Ok(ProcessOutput {
                            status_code: output.status.code().unwrap_or(-1),
                            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
                            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
                            timed_out: true,
                        });
                    }
                    std::thread::sleep(Duration::from_millis(10));
                }
                Err(e) => return Err(format!("failed while waiting for process: {}", e)),
            }
        }
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("failed to wait for '{}': {}", spec.program, e))?;

    Ok(ProcessOutput {
        status_code: output.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&output.stdout).to_string(),
        stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        timed_out: false,
    })
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
    fn test_run_echo() {
        let out = expect_ok(run("echo", &["ok"]));
        assert_eq!(out.status_code, 0);
        assert!(out.stdout.contains("ok"));
        assert!(!out.timed_out);
    }

    #[test]
    fn test_env_injection() {
        let mut env = HashMap::new();
        env.insert("ECLEXIA_TEST_VALUE".to_string(), "42".to_string());
        let out = expect_ok(run_with_spec(ProcessSpec {
            program: "sh".to_string(),
            args: vec!["-c".to_string(), "echo $ECLEXIA_TEST_VALUE".to_string()],
            env,
            cwd: None,
            timeout: Some(Duration::from_secs(2)),
        }));
        assert_eq!(out.stdout.trim(), "42");
    }
}
