// SPDX-License-Identifier: PMPL-1.0-or-later

//! Queue abstractions: in-memory and durable file-backed queue.

use serde::{Deserialize, Serialize};
use std::collections::VecDeque;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Message {
    pub id: u64,
    pub payload: Vec<u8>,
    pub enqueued_at_unix_secs: u64,
}

impl Message {
    fn new(id: u64, payload: Vec<u8>) -> Self {
        Self {
            id,
            payload,
            enqueued_at_unix_secs: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs(),
        }
    }
}

pub trait Queue {
    fn enqueue(&mut self, payload: Vec<u8>) -> Result<u64, String>;
    fn dequeue(&mut self) -> Result<Option<Message>, String>;
    fn peek(&self) -> Option<&Message>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Debug, Default)]
pub struct InMemoryQueue {
    next_id: u64,
    items: VecDeque<Message>,
}

impl InMemoryQueue {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Queue for InMemoryQueue {
    fn enqueue(&mut self, payload: Vec<u8>) -> Result<u64, String> {
        self.next_id = self.next_id.saturating_add(1);
        let id = self.next_id;
        self.items.push_back(Message::new(id, payload));
        Ok(id)
    }

    fn dequeue(&mut self) -> Result<Option<Message>, String> {
        Ok(self.items.pop_front())
    }

    fn peek(&self) -> Option<&Message> {
        self.items.front()
    }

    fn len(&self) -> usize {
        self.items.len()
    }
}

#[derive(Debug)]
pub struct FileQueue {
    path: PathBuf,
    next_id: u64,
    items: VecDeque<Message>,
}

impl FileQueue {
    pub fn open(path: impl AsRef<Path>) -> Result<Self, String> {
        let path = path.as_ref().to_path_buf();
        if !path.exists() {
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)
                    .map_err(|e| format!("failed to create '{}': {}", parent.display(), e))?;
            }
            std::fs::write(&path, b"[]")
                .map_err(|e| format!("failed to initialize '{}': {}", path.display(), e))?;
        }

        let raw = std::fs::read_to_string(&path)
            .map_err(|e| format!("failed to read '{}': {}", path.display(), e))?;
        let parsed: Vec<Message> =
            serde_json::from_str(&raw).map_err(|e| format!("invalid queue file json: {}", e))?;
        let next_id = parsed.iter().map(|m| m.id).max().unwrap_or(0);

        Ok(Self {
            path,
            next_id,
            items: parsed.into(),
        })
    }

    fn flush(&self) -> Result<(), String> {
        let vec = self.items.iter().cloned().collect::<Vec<_>>();
        let data = serde_json::to_vec_pretty(&vec).map_err(|e| e.to_string())?;
        std::fs::write(&self.path, data)
            .map_err(|e| format!("failed to write '{}': {}", self.path.display(), e))
    }
}

impl Queue for FileQueue {
    fn enqueue(&mut self, payload: Vec<u8>) -> Result<u64, String> {
        self.next_id = self.next_id.saturating_add(1);
        let id = self.next_id;
        self.items.push_back(Message::new(id, payload));
        self.flush()?;
        Ok(id)
    }

    fn dequeue(&mut self) -> Result<Option<Message>, String> {
        let out = self.items.pop_front();
        self.flush()?;
        Ok(out)
    }

    fn peek(&self) -> Option<&Message> {
        self.items.front()
    }

    fn len(&self) -> usize {
        self.items.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env::temp_dir;

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(v) => v,
            Err(e) => panic!("expected ok, got {:?}", e),
        }
    }

    #[test]
    fn test_fifo_behavior_in_memory() {
        let mut q = InMemoryQueue::new();
        let id1 = expect_ok(q.enqueue(b"first".to_vec()));
        let id2 = expect_ok(q.enqueue(b"second".to_vec()));
        assert!(id2 > id1);

        let first = expect_ok(q.dequeue()).expect("missing first");
        let second = expect_ok(q.dequeue()).expect("missing second");
        assert_eq!(first.payload, b"first");
        assert_eq!(second.payload, b"second");
    }

    #[test]
    fn test_file_queue_persistence() {
        let path = temp_dir().join(format!(
            "eclexia-queue-test-{}.json",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos()
        ));

        {
            let mut q = expect_ok(FileQueue::open(&path));
            expect_ok(q.enqueue(b"a".to_vec()));
            expect_ok(q.enqueue(b"b".to_vec()));
            assert_eq!(q.len(), 2);
        }

        {
            let mut q = expect_ok(FileQueue::open(&path));
            assert_eq!(q.len(), 2);
            let first = expect_ok(q.dequeue()).expect("missing first");
            assert_eq!(first.payload, b"a");
        }

        let _ = std::fs::remove_file(path);
    }
}
