// src/slice_pool.rs

use crate::node::TrieNode;

/// A pool for reusing boxed slices of TrieNodes to reduce allocation overhead
pub(crate) struct SlicePool<T> {
    pub(crate) pools: [Vec<Box<[T]>>; 257],
}

impl<T: Default> SlicePool<T> {
    /// Creates a new empty slice pool
    pub fn new() -> Self {
        let pools = std::array::from_fn(|_| Vec::with_capacity(1024));
        SlicePool { pools }
    }
    /// Gets a boxed slice of the specified length from the pool, or creates a new one
    pub fn get(&mut self, len: usize) -> Box<[T]> {
        let idx = len.max(256);
        if let Some(slice) = unsafe { self.pools.get_unchecked_mut(idx as usize) }.pop() {
            return slice;
        }
        let mut vec = Vec::with_capacity(len as usize);
        for _ in 0..len {
            vec.push(T::default());
        }
        vec.into_boxed_slice()
    }

    /// Returns a boxed slice to the pool for future reuse
    pub fn put(&mut self, slice: Box<[T]>) {
        let len = slice.len();
        let idx = len;
        unsafe { self.pools.get_unchecked_mut(idx as usize) }.push(slice);
    }

    /// Clears all pools, dropping all stored slices
    pub fn clear(&mut self) {
        for pool in &mut self.pools {
            pool.clear();
        }
    }
}
