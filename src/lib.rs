//! A prefix tree (trie) based map implementation.
//!
//! This crate provides a `TrieMap`, which is a key-value data structure
//! that uses a trie (prefix tree) for storage and retrieval of data.
//!
//! # Features
//!
//! - Fast key lookups with O(k) complexity where k is the key length
//! - Prefix-based operations (matching keys with a common prefix)
//! - Iterator support
//! - Entry API for efficient in-place updates

mod as_bytes;
mod entry;
mod iter;
mod node;
mod trie_map;

pub use as_bytes::AsBytes;
pub use entry::{Entry, OccupiedEntry, VacantEntry};
pub use iter::{DrainIter, Iter, Keys, PrefixIter, PrefixKeys, PrefixValues, Values};
pub use trie_map::TrieMap;

// Re-export common types at the crate level
pub type Result<T> = std::result::Result<T, T>;

#[cfg(test)]
mod proptest_triemap;
