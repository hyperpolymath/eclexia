// SPDX-License-Identifier: PMPL-1.0-or-later

//! In-memory cache with LRU eviction and optional TTL.

use std::collections::{HashMap, VecDeque};
use std::hash::Hash;
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CacheStats {
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
    pub expirations: u64,
}

#[derive(Debug)]
struct Entry<V> {
    value: V,
    expires_at: Option<Instant>,
}

pub struct LruCache<K, V>
where
    K: Eq + Hash + Clone,
{
    capacity: usize,
    map: HashMap<K, Entry<V>>,
    order: VecDeque<K>,
    stats: CacheStats,
}

impl<K, V> LruCache<K, V>
where
    K: Eq + Hash + Clone,
{
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity: capacity.max(1),
            map: HashMap::new(),
            order: VecDeque::new(),
            stats: CacheStats::default(),
        }
    }

    pub fn put(&mut self, key: K, value: V) {
        self.put_with_ttl(key, value, None);
    }

    pub fn put_for(&mut self, key: K, value: V, ttl: Duration) {
        self.put_with_ttl(key, value, Some(ttl));
    }

    pub fn put_with_ttl(&mut self, key: K, value: V, ttl: Option<Duration>) {
        self.purge_expired();

        let expires_at = ttl.map(|dur| Instant::now() + dur);
        if self.map.contains_key(&key) {
            self.map.insert(key.clone(), Entry { value, expires_at });
            self.touch(&key);
            return;
        }

        if self.map.len() >= self.capacity {
            while let Some(oldest) = self.order.pop_front() {
                if self.map.remove(&oldest).is_some() {
                    self.stats.evictions = self.stats.evictions.saturating_add(1);
                    break;
                }
            }
        }

        self.order.push_back(key.clone());
        self.map.insert(key, Entry { value, expires_at });
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        self.purge_expired();
        if !self.map.contains_key(key) {
            self.stats.misses = self.stats.misses.saturating_add(1);
            return None;
        }
        self.touch(key);
        self.stats.hits = self.stats.hits.saturating_add(1);
        self.map.get(key).map(|entry| &entry.value)
    }

    pub fn contains_key(&mut self, key: &K) -> bool {
        self.purge_expired();
        self.map.contains_key(key)
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        if let Some(pos) = self.order.iter().position(|item| item == key) {
            self.order.remove(pos);
        }
        self.map.remove(key).map(|entry| entry.value)
    }

    pub fn purge_expired(&mut self) {
        let now = Instant::now();
        let mut expired_keys = Vec::new();
        for (key, entry) in &self.map {
            if entry.expires_at.is_some_and(|t| now >= t) {
                expired_keys.push(key.clone());
            }
        }
        for key in expired_keys {
            if self.remove(&key).is_some() {
                self.stats.expirations = self.stats.expirations.saturating_add(1);
            }
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn stats(&self) -> CacheStats {
        self.stats
    }

    fn touch(&mut self, key: &K) {
        if let Some(pos) = self.order.iter().position(|k| k == key) {
            self.order.remove(pos);
        }
        self.order.push_back(key.clone());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eviction_lru() {
        let mut cache = LruCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);
        assert_eq!(cache.get(&"a"), Some(&1)); // make "b" LRU
        cache.put("c", 3); // evicts b
        assert!(cache.get(&"b").is_none());
        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.get(&"c"), Some(&3));
    }

    #[test]
    fn test_ttl_expiry() {
        let mut cache = LruCache::new(2);
        cache.put_for("token", 123, Duration::from_millis(5));
        std::thread::sleep(Duration::from_millis(15));
        assert!(cache.get(&"token").is_none());
        let stats = cache.stats();
        assert!(stats.expirations >= 1);
    }
}
