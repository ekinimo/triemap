// src/slice_pool.rs

use crate::node::TrieNode;

/// A pool for reusing boxed slices of TrieNodes to reduce allocation overhead
pub(crate) struct SlicePool {
    pub(crate) pools: [Vec<Box<[TrieNode]>>; 257],
}

impl SlicePool {
    /// Creates a new empty slice pool
    pub fn new() -> Self {
        let pools = std::array::from_fn(|_| Vec::new());
        SlicePool { pools }
    }
    /// Gets a boxed slice of the specified length from the pool, or creates a new one
    pub fn get(&mut self, len: usize) -> Box<[TrieNode]> {
        if len == 0 {
            return Box::new([]);
        }
        let idx = len.max(256);
        if let Some(slice) = self.pools[idx as usize].pop() {
            return slice;
        }
        let mut vec = Vec::with_capacity(len as usize);
        for _ in 0..len {
            vec.push(TrieNode::new());
        }
        vec.into_boxed_slice()
    }

    /// Returns a boxed slice to the pool for future reuse
    pub fn put(&mut self, slice: Box<[TrieNode]>) {
        let len = slice.len();

        if len == 0 {
            return; // Don't pool empty slices
        }

        let idx = len.min(255);
        self.pools[idx].push(slice);
    }

    /// Clears all pools, dropping all stored slices
    pub fn clear(&mut self) {
        for pool in &mut self.pools {
            pool.clear();
        }
    }
}

impl Drop for SlicePool {
    fn drop(&mut self) {
        // Clear all pools when the pool itself is dropped
        self.clear();
    }
}
