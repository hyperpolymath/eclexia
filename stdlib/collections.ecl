// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Collections module providing common data structures.

import core::{Option, Result}

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

    /// Clears the vector, removing all values.
    fn clear(self) {
        self.len = 0
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

/// HashMap: key-value hash table.
type HashMap<K, V> {
    buckets: Array<Vec<(K, V)>>,
    len: Int,
}

impl<K, V> HashMap<K, V> {
    /// Creates a new empty hash map.
    fn new() -> HashMap<K, V> {
        HashMap {
            buckets: @builtin("array_with_capacity", 16),
            len: 0,
        }
    }

    /// Inserts a key-value pair into the map.
    fn insert(self, key: K, value: V) {
        let hash = @builtin("hash", key)
        let bucket_index = hash % 16
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

    /// Gets the value associated with a key.
    fn get(self, key: K) -> Option<V> {
        let hash = @builtin("hash", key)
        let bucket_index = hash % 16
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

    /// Removes a key-value pair from the map.
    fn remove(self, key: K) -> Option<V> {
        let hash = @builtin("hash", key)
        let bucket_index = hash % 16
        let bucket = @builtin("array_get", self.buckets, bucket_index)

        let i = 0
        while i < bucket.len() {
            let (k, v) = bucket.get(i).unwrap()
            if k == key {
                // TODO: Actually remove the element
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
}

/// Set: collection of unique values.
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

    /// Adds a value to the set.
    fn insert(self, value: T) {
        self.map.insert(value, ())
    }

    /// Removes a value from the set.
    fn remove(self, value: T) {
        self.map.remove(value)
    }

    /// Returns true if the set contains the value.
    fn contains(self, value: T) -> Bool {
        self.map.get(value).is_some()
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
