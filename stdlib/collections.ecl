// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Collections module providing common data structures.
//!
//! Data structures for economics-as-code:
//!   - Vec<T>              Dynamically-sized array
//!   - HashMap<K, V>       Key-value hash table (unordered)
//!   - HashSet<T>          Collection of unique values
//!   - SortedMap<K, V>     Ordered key-value map (for time series, sorted data)
//!   - Queue<T>            FIFO queue (for scheduling, event ordering)
//!   - PriorityQueue<T>    Min-heap priority queue (for cost-ordered scheduling)
//!   - Set operations       Union, intersection, difference, subset checks

import core::{Option, Result}

// ============================================================================
// Vec<T>: dynamically-sized array
// ============================================================================

/// Vector: dynamically-sized array.
type Vec<T> {
    data: Array<T>,
    len: Int,
    capacity: Int,
}

impl<T> Vec<T> {
    /// Creates a new empty vector.
    fn new() -> Vec<T> {
        Vec {
            data: [],
            len: 0,
            capacity: 0,
        }
    }

    /// Creates a new vector with specified capacity.
    fn with_capacity(capacity: Int) -> Vec<T> {
        Vec {
            data: @builtin("array_with_capacity", capacity),
            len: 0,
            capacity,
        }
    }

    /// Returns the number of elements in the vector.
    fn len(self) -> Int {
        self.len
    }

    /// Returns true if the vector is empty.
    fn is_empty(self) -> Bool {
        self.len == 0
    }

    /// Appends an element to the end of the vector.
    fn push(self, value: T) {
        if self.len >= self.capacity {
            self.resize(self.capacity * 2 + 1)
        }
        @builtin("array_set", self.data, self.len, value)
        self.len = self.len + 1
    }

    /// Removes and returns the last element, or None if empty.
    fn pop(self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len = self.len - 1
            let value = @builtin("array_get", self.data, self.len)
            Some(value)
        }
    }

    /// Returns a reference to the element at index, or None if out of bounds.
    fn get(self, index: Int) -> Option<T> {
        if index >= 0 && index < self.len {
            Some(@builtin("array_get", self.data, index))
        } else {
            None
        }
    }

    /// Sets the element at index. Panics if out of bounds.
    fn set(self, index: Int, value: T) {
        if index >= 0 && index < self.len {
            @builtin("array_set", self.data, index, value)
        } else {
            panic("Vec::set: index out of bounds")
        }
    }

    /// Returns the first element, or None if empty.
    fn first(self) -> Option<T> {
        self.get(0)
    }

    /// Returns the last element, or None if empty.
    fn last(self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.get(self.len - 1)
        }
    }

    /// Clears the vector, removing all values.
    fn clear(self) {
        self.len = 0
    }

    /// Returns true if the vector contains the given value.
    fn contains(self, value: T) -> Bool {
        let i = 0
        while i < self.len {
            let elem = @builtin("array_get", self.data, i)
            if elem == value {
                return true
            }
            i = i + 1
        }
        false
    }

    /// Reverses the vector in place.
    fn reverse(self) {
        let i = 0
        let j = self.len - 1
        while i < j {
            let a = @builtin("array_get", self.data, i)
            let b = @builtin("array_get", self.data, j)
            @builtin("array_set", self.data, i, b)
            @builtin("array_set", self.data, j, a)
            i = i + 1
            j = j - 1
        }
    }

    /// Resizes the vector to a new capacity.
    fn resize(self, new_capacity: Int) {
        let new_data = @builtin("array_with_capacity", new_capacity)
        let i = 0
        while i < self.len {
            let value = @builtin("array_get", self.data, i)
            @builtin("array_set", new_data, i, value)
            i = i + 1
        }
        self.data = new_data
        self.capacity = new_capacity
    }
}

// ============================================================================
// HashMap<K, V>: key-value hash table
// ============================================================================

/// HashMap: key-value hash table.
///
/// Provides O(1) average-case lookup, insertion, and deletion.
/// Keys are hashed; order is not preserved.
///
/// Economics use cases:
///   - Market participant attributes lookup
///   - Configuration/parameter stores
///   - Symbol tables for economic models
type HashMap<K, V> {
    buckets: Array<Vec<(K, V)>>,
    len: Int,
    bucket_count: Int,
}

impl<K, V> HashMap<K, V> {
    /// Creates a new empty hash map with default capacity.
    fn new() -> HashMap<K, V> {
        let bucket_count = 16
        HashMap {
            buckets: @builtin("array_with_capacity", bucket_count),
            len: 0,
            bucket_count,
        }
    }

    /// Creates a new hash map with specified bucket count.
    fn with_capacity(capacity: Int) -> HashMap<K, V> {
        let bucket_count = capacity
        HashMap {
            buckets: @builtin("array_with_capacity", bucket_count),
            len: 0,
            bucket_count,
        }
    }

    /// Inserts a key-value pair into the map. Overwrites if key exists.
    fn insert(self, key: K, value: V) {
        let hash = @builtin("hash", key)
        let bucket_index = hash % self.bucket_count
        let bucket = @builtin("array_get", self.buckets, bucket_index)

        // Check if key exists
        let i = 0
        while i < bucket.len() {
            let (k, v) = bucket.get(i).unwrap()
            if k == key {
                // Update existing value
                @builtin("array_set", bucket.data, i, (key, value))
                return
            }
            i = i + 1
        }

        // Insert new key-value pair
        bucket.push((key, value))
        self.len = self.len + 1
    }

    /// Gets the value associated with a key, or None.
    fn get(self, key: K) -> Option<V> {
        let hash = @builtin("hash", key)
        let bucket_index = hash % self.bucket_count
        let bucket = @builtin("array_get", self.buckets, bucket_index)

        let i = 0
        while i < bucket.len() {
            let (k, v) = bucket.get(i).unwrap()
            if k == key {
                return Some(v)
            }
            i = i + 1
        }

        None
    }

    /// Returns true if the map contains the given key.
    fn contains_key(self, key: K) -> Bool {
        self.get(key).is_some()
    }

    /// Removes a key-value pair from the map. Returns the removed value, or None.
    fn remove(self, key: K) -> Option<V> {
        let hash = @builtin("hash", key)
        let bucket_index = hash % self.bucket_count
        let bucket = @builtin("array_get", self.buckets, bucket_index)

        let i = 0
        while i < bucket.len() {
            let (k, v) = bucket.get(i).unwrap()
            if k == key {
                // Remove by swapping with last element
                @builtin("array_remove_at", bucket.data, i)
                self.len = self.len - 1
                return Some(v)
            }
            i = i + 1
        }

        None
    }

    /// Returns the number of key-value pairs in the map.
    fn len(self) -> Int {
        self.len
    }

    /// Returns true if the map is empty.
    fn is_empty(self) -> Bool {
        self.len == 0
    }

    /// Gets the value for key, or inserts and returns default.
    fn get_or_insert(self, key: K, default: V) -> V {
        match self.get(key) {
            Some(v) => v,
            None => {
                self.insert(key, default)
                default
            }
        }
    }
}

// ============================================================================
// HashSet<T>: collection of unique values
// ============================================================================

/// Set: collection of unique values.
///
/// Backed by HashMap, provides O(1) average-case membership testing.
///
/// Economics use cases:
///   - Unique market participants
///   - Policy group membership
///   - Resource category tracking
type HashSet<T> {
    map: HashMap<T, ()>,
}

impl<T> HashSet<T> {
    /// Creates a new empty set.
    fn new() -> HashSet<T> {
        HashSet {
            map: HashMap::new(),
        }
    }

    /// Adds a value to the set. Returns true if the value was newly inserted.
    fn insert(self, value: T) -> Bool {
        if self.map.contains_key(value) {
            false
        } else {
            self.map.insert(value, ())
            true
        }
    }

    /// Removes a value from the set. Returns true if the value was present.
    fn remove(self, value: T) -> Bool {
        self.map.remove(value).is_some()
    }

    /// Returns true if the set contains the value.
    fn contains(self, value: T) -> Bool {
        self.map.contains_key(value)
    }

    /// Returns the number of values in the set.
    fn len(self) -> Int {
        self.map.len()
    }

    /// Returns true if the set is empty.
    fn is_empty(self) -> Bool {
        self.map.is_empty()
    }
}

// ============================================================================
// SortedMap<K, V>: ordered key-value map (BTreeMap-backed)
// ============================================================================

/// SortedMap: ordered key-value map.
///
/// Keys are maintained in sorted order. Provides O(log n) lookup, insertion,
/// and deletion, plus efficient range queries and min/max access.
///
/// Economics use cases:
///   - Time-series data (dates as keys, values as measurements)
///   - Price books (sorted by price level)
///   - Priority-ordered resource allocation
///   - Quartile/percentile computation on sorted data
type SortedMap<K, V> {
    // Backed by native BTreeMap via builtins
    _handle: Int,
}

impl<K, V> SortedMap<K, V> {
    /// Creates a new empty sorted map.
    fn new() -> SortedMap<K, V> {
        @builtin("sortedmap_new")
    }

    /// Inserts a key-value pair. Overwrites if key exists.
    fn insert(self, key: K, value: V) {
        @builtin("sortedmap_insert", self, key, value)
    }

    /// Gets the value associated with a key, or Unit if not found.
    fn get(self, key: K) -> V {
        @builtin("sortedmap_get", self, key)
    }

    /// Removes a key-value pair. Returns the removed value, or Unit.
    fn remove(self, key: K) -> V {
        @builtin("sortedmap_remove", self, key)
    }

    /// Returns the number of entries.
    fn len(self) -> Int {
        @builtin("sortedmap_len", self)
    }

    /// Returns all keys in sorted order.
    fn keys(self) -> Array<K> {
        @builtin("sortedmap_keys", self)
    }

    /// Returns the entry with the smallest key, or Unit.
    fn min_entry(self) -> (K, V) {
        @builtin("sortedmap_min_key", self)
    }

    /// Returns the entry with the largest key, or Unit.
    fn max_entry(self) -> (K, V) {
        @builtin("sortedmap_max_key", self)
    }

    /// Returns all entries with keys in [from, to] in sorted order.
    fn range(self, from: K, to: K) -> Array<(K, V)> {
        @builtin("sortedmap_range", self, from, to)
    }
}

// ============================================================================
// Queue<T>: FIFO queue
// ============================================================================

/// Queue: first-in, first-out queue.
///
/// Elements are added to the back and removed from the front.
///
/// Economics use cases:
///   - Event ordering in discrete-event simulation
///   - Task scheduling in sequential processing
///   - Order book FIFO matching at same price level
type Queue<T> {
    _handle: Int,
}

impl<T> Queue<T> {
    /// Creates a new empty queue.
    fn new() -> Queue<T> {
        @builtin("queue_new")
    }

    /// Adds an element to the back of the queue.
    fn enqueue(self, value: T) {
        @builtin("queue_enqueue", self, value)
    }

    /// Removes and returns the front element. Panics if empty.
    fn dequeue(self) -> T {
        @builtin("queue_dequeue", self)
    }

    /// Returns the front element without removing it, or Unit if empty.
    fn peek(self) -> T {
        @builtin("queue_peek", self)
    }

    /// Returns the number of elements in the queue.
    fn len(self) -> Int {
        @builtin("queue_len", self)
    }

    /// Returns true if the queue is empty.
    fn is_empty(self) -> Bool {
        @builtin("queue_is_empty", self)
    }
}

// ============================================================================
// PriorityQueue<T>: min-heap priority queue
// ============================================================================

/// PriorityQueue: min-heap priority queue.
///
/// Elements are ordered by priority (lower numeric priority = higher urgency).
/// Elements with the same priority are served in FIFO order.
///
/// Economics use cases:
///   - Cost-ordered resource allocation
///   - Urgency-based task scheduling
///   - Dijkstra-style shortest path in supply chains
///   - Event-driven simulation (next event = lowest timestamp)
type PriorityQueue<T> {
    _handle: Int,
}

impl<T> PriorityQueue<T> {
    /// Creates a new empty priority queue.
    fn new() -> PriorityQueue<T> {
        @builtin("priority_queue_new")
    }

    /// Adds an element with the given priority (lower = higher urgency).
    fn push(self, priority: Float, value: T) {
        @builtin("priority_queue_push", self, priority, value)
    }

    /// Removes and returns the highest-priority (lowest score) element.
    /// Panics if empty.
    fn pop(self) -> T {
        @builtin("priority_queue_pop", self)
    }

    /// Returns the highest-priority element without removing it, or Unit.
    fn peek(self) -> T {
        @builtin("priority_queue_peek", self)
    }

    /// Returns the total number of elements.
    fn len(self) -> Int {
        @builtin("priority_queue_len", self)
    }
}

// ============================================================================
// Set operations (functions operating on arrays as sets)
// ============================================================================

/// Returns the union of two sets (arrays treated as sets).
fn set_union<T>(a: Array<T>, b: Array<T>) -> Array<T> {
    @builtin("set_union", a, b)
}

/// Returns the intersection of two sets.
fn set_intersection<T>(a: Array<T>, b: Array<T>) -> Array<T> {
    @builtin("set_intersection", a, b)
}

/// Returns the difference A - B (elements in A but not in B).
fn set_difference<T>(a: Array<T>, b: Array<T>) -> Array<T> {
    @builtin("set_difference", a, b)
}

/// Returns the symmetric difference (A-B) union (B-A).
fn set_symmetric_difference<T>(a: Array<T>, b: Array<T>) -> Array<T> {
    @builtin("set_symmetric_difference", a, b)
}

/// Returns true if A is a subset of B.
fn set_is_subset<T>(a: Array<T>, b: Array<T>) -> Bool {
    @builtin("set_is_subset", a, b)
}

/// Deduplicates an array, returning a new array with unique elements.
fn set_from_array<T>(arr: Array<T>) -> Array<T> {
    @builtin("set_from_array", arr)
}
