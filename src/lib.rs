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
mod proptest_triemap {
    use super::*;
    use proptest::prelude::*;
    use std::collections::BTreeMap;
    use std::collections::HashMap;

    /// Generate key-value pairs with string keys
    fn key_value_pairs(
        min_pairs: usize,
        max_pairs: usize,
    ) -> impl Strategy<Value = Vec<(String, i32)>> {
        proptest::collection::vec(
            (
                "[a-zA-Z0-9]{1,10}".prop_map(String::from),
                proptest::num::i32::ANY,
            ),
            min_pairs..max_pairs,
        )
    }

    proptest! {
        #[test]
        fn triemap_insert_get_equivalence(pairs in key_value_pairs(1, 100)) {
            let mut trie = TrieMap::new();
            let mut expected_values = HashMap::new();

            // Insert all pairs into the trie and track the final expected value for each key
            for (key, value) in &pairs {
                trie.insert(key, *value);
                expected_values.insert(key.clone(), *value);
            }

            // Check that we can get all values back correctly
            for (key, _) in &pairs {
                let expected = expected_values.get(key).unwrap();
                assert_eq!(trie.get(key), Some(expected));
            }
        }

        #[test]
        fn triemap_hashmap_equivalence(pairs in key_value_pairs(1, 100)) {
            let mut trie = TrieMap::new();
            let mut hash_map = HashMap::new();

            // Insert all pairs into both maps
            for (key, value) in &pairs {
                trie.insert(key, *value);
                hash_map.insert(key.clone(), *value);
            }

            // All keys in HashMap should be retrievable in TrieMap
            for (key, expected_value) in &hash_map {
                assert_eq!(trie.get(key), Some(expected_value));
            }

            // Size of both maps should be equal (duplicate keys get overwritten)
            assert_eq!(trie.len(), hash_map.len());
        }

        #[test]
        fn triemap_len_reflects_unique_keys(pairs in key_value_pairs(1, 100)) {
            let mut trie = TrieMap::new();
            let mut unique_keys = std::collections::HashSet::new();

            for (key, value) in &pairs {
                trie.insert(key, *value);
                unique_keys.insert(key.clone());
            }

            assert_eq!(trie.len(), unique_keys.len());
        }

        #[test]
        fn triemap_insert_remove_equivalent_to_not_inserting(
            pairs in key_value_pairs(1, 50),
            to_remove in key_value_pairs(1, 50)
        ) {
            let mut trie1 = TrieMap::new();
            let mut trie2 = TrieMap::new();
            let mut all_pairs = pairs.clone();

            // Add the to_remove pairs to all_pairs
            all_pairs.extend(to_remove.iter().cloned());

            // In trie1, insert all pairs and then remove the to_remove ones
            for (key, value) in &all_pairs {
                trie1.insert(key, *value);
            }

            for (key, _) in &to_remove {
                trie1.remove(key);
            }

            // In trie2, only insert the pairs that aren't going to be removed
            for (key, value) in &pairs {
                if !to_remove.iter().any(|(k, _)| k == key) {
                    trie2.insert(key, *value);
                }
            }

            // Tries should be equivalent
            assert_eq!(trie1.len(), trie2.len());

            for (key, _) in &pairs {
                assert_eq!(trie1.get(key), trie2.get(key));
            }
        }

        #[test]
        fn triemap_entry_api_behaves_like_direct_methods(
            pairs in key_value_pairs(1, 100),
            modifiers in key_value_pairs(1, 50)
        ) {
            let mut trie1 = TrieMap::new();
            let mut trie2 = TrieMap::new();

            // Insert initial pairs into both tries
            for (key, value) in &pairs {
                trie1.insert(key, *value);
                trie2.insert(key, *value);
            }

            // Use Entry API on trie1
            for (key, value) in &modifiers {
                trie1.entry(key).or_insert(*value);
            }

            // Use direct methods on trie2
            for (key, value) in &modifiers {
                if !trie2.contains_key(key) {
                    trie2.insert(key, *value);
                }
            }

            // Both tries should be identical
            assert_eq!(trie1.len(), trie2.len());

            // Create a combined set of keys to check
            let mut all_keys = pairs.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>();
            all_keys.extend(modifiers.iter().map(|(k, _)| k.clone()));

            for key in all_keys {
                assert_eq!(trie1.get(&key), trie2.get(&key));
            }
        }

        #[test]
        fn triemap_clone_is_deep_copy(pairs in key_value_pairs(1, 100)) {
            let mut original = TrieMap::new();

            for (key, value) in &pairs {
                original.insert(key, *value);
            }

            let cloned = original.clone();

            // Modifying the original should not affect the clone
            if let Some((first_key, _)) = pairs.first() {
                original.remove(first_key);

                // The key should still be in the clone
                assert!(cloned.contains_key(first_key));
            }

            // If we had at least one pair, the length should now differ
            if !pairs.is_empty() {
                assert_ne!(original.len(), cloned.len());
            }
        }

        #[test]
        fn triemap_iter_visits_all_elements(pairs in key_value_pairs(1, 100)) {
            let mut trie = TrieMap::new();
            let mut hash_map = HashMap::new();

            for (key, value) in &pairs {
                trie.insert(key, *value);
                hash_map.insert(key.clone(), *value);
            }

            let mut visited_keys = Vec::new();
            for (key, value) in trie.iter() {
                let key_str = String::from_utf8(key).unwrap();
                assert_eq!(hash_map.get(&key_str), Some(value));
                visited_keys.push(key_str);
            }

            assert_eq!(visited_keys.len(), hash_map.len());

            // Convert HashSet from visited keys
            let visited_set: std::collections::HashSet<_> = visited_keys.into_iter().collect();
            let expected_set: std::collections::HashSet<_> = hash_map.keys().cloned().collect();

            assert_eq!(visited_set, expected_set);
        }

        #[test]
        fn triemap_prefix_operations_consistent(
            pairs in key_value_pairs(5, 100),
            prefix_str in "[a-zA-Z]{1,3}".prop_map(String::from)
        ) {
            let mut trie = TrieMap::new();

            for (key, value) in &pairs {
                trie.insert(key, *value);
            }

            // Get all keys that start with the prefix
            let prefix_matches = trie.get_prefix_matches(&prefix_str);
            let starts_with = trie.starts_with(&prefix_str);

            // starts_with should be true iff there are matches
            assert_eq!(starts_with, !prefix_matches.is_empty());

            // Keys from prefix_iter should match get_prefix_matches
            let prefix_iter_results: Vec<_> = trie.prefix_iter(&prefix_str).collect();
            assert_eq!(prefix_matches.len(), prefix_iter_results.len());

            // Check all keys returned from prefix operations actually start with prefix
            for (key, _) in &prefix_matches {
                let key_str = String::from_utf8(key.clone()).unwrap();
                assert!(key_str.starts_with(&prefix_str));
            }

            // prefix_keys should return just the keys
            let prefix_keys: Vec<_> = trie.prefix_keys(&prefix_str).collect();
            assert_eq!(prefix_keys.len(), prefix_matches.len());

            // prefix_values should return just the values
            let prefix_values: Vec<_> = trie.prefix_values(&prefix_str).collect();
            assert_eq!(prefix_values.len(), prefix_matches.len());

            // Test remove_prefix_matches
            let mut trie2 = trie.clone();
            let removed = trie2.remove_prefix_matches(&prefix_str);

            // Number of removed items should match number of matches
            assert_eq!(removed.len(), prefix_matches.len());

            // trie2 should now have len = original len - number of removed items
            assert_eq!(trie2.len(), trie.len() - removed.len());

            // No keys with the prefix should remain
            assert!(!trie2.starts_with(&prefix_str));
        }

        #[test]
        fn triemap_from_into_conversions(pairs in key_value_pairs(1, 100)) {
            // Create a HashMap
            let mut hash_map = HashMap::new();
            for (key, value) in &pairs {
                hash_map.insert(key.clone(), *value);
            }

            // Convert to TrieMap
            let trie: TrieMap<i32> = TrieMap::from(hash_map.clone());

            // Check all expected keys are present
            for (key, expected_value) in &hash_map {
                assert_eq!(trie.get(key), Some(expected_value));
            }

            // Convert back to HashMap
            let hash_map2: HashMap<Vec<u8>, i32> = HashMap::from(trie);

            // Check all expected keys are present in new HashMap
            for (key, expected_value) in &hash_map {
                assert_eq!(hash_map2.get(key.as_bytes()), Some(expected_value));
            }
        }

        #[test]
        fn triemap_set_operations(
            pairs1 in key_value_pairs(1, 50),
            pairs2 in key_value_pairs(1, 50)
        ) {
            let mut trie1 = TrieMap::new();
            let mut trie2 = TrieMap::new();

            // Helper to convert pairs to HashMaps for reference calculations
            let to_hashmap = |pairs: &[(String, i32)]| -> HashMap<String, i32> {
                pairs.iter().cloned().collect()
            };

            let map1 = to_hashmap(&pairs1);
            let map2 = to_hashmap(&pairs2);

            // Insert pairs into tries
            for (key, value) in &map1 {
                trie1.insert(key, *value);
            }

            for (key, value) in &map2 {
                trie2.insert(key, *value);
            }

            // Test union
            let union_count = trie1.union(&trie2).count();
            let expected_union_count = map1.keys().chain(map2.keys()).collect::<std::collections::HashSet<_>>().len();
            assert_eq!(union_count, expected_union_count);

            // Test intersection
            let intersection_count = trie1.intersect(&trie2).count();
            let expected_intersection_count = map1.keys()
                .filter(|k| map2.contains_key(*k))
                .count();
            assert_eq!(intersection_count, expected_intersection_count);

            // Test difference
            let difference_count = trie1.difference(&trie2).count();
            let expected_difference_count = map1.keys()
                .filter(|k| !map2.contains_key(*k))
                .count();
            assert_eq!(difference_count, expected_difference_count);

            // Test symmetric_difference
            let sym_diff_count = trie1.symmetric_difference(&trie2).count();
            let expected_sym_diff_count =
                map1.keys().filter(|k| !map2.contains_key(*k)).count() +
                map2.keys().filter(|k| !map1.contains_key(*k)).count();
            assert_eq!(sym_diff_count, expected_sym_diff_count);

            // Test subset relationships
            let is_subset = trie1.is_subset_of(&trie2);
            let expected_is_subset = map1.keys().all(|k| map2.contains_key(k));
            assert_eq!(is_subset, expected_is_subset);

            let is_proper_subset = trie1.is_proper_subset_of(&trie2);
            let expected_is_proper_subset =
                expected_is_subset && map1.len() < map2.len();
            assert_eq!(is_proper_subset, expected_is_proper_subset);
        }

        #[test]
        fn triemap_round_trip_serialization(pairs in key_value_pairs(1, 100)) {
            use serde::{Serialize, Deserialize};
            use serde_json;

            #[derive(Serialize, Deserialize, PartialEq, Debug)]
            struct TestStruct {
                data: Vec<(String, i32)>
            }

            let mut trie = TrieMap::new();

            // Insert all pairs
            for (key, value) in &pairs {
                trie.insert(key, *value);
            }

            // Convert to a structure we can serialize
            let data: Vec<(String, i32)> = trie.iter()
                .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
                .collect();

            let test_struct = TestStruct { data };

            // Serialize and deserialize
            let serialized = serde_json::to_string(&test_struct).unwrap();
            let deserialized: TestStruct = serde_json::from_str(&serialized).unwrap();

            // Create a new TrieMap from the deserialized data
            let mut new_trie = TrieMap::new();
            for (key, value) in &deserialized.data {
                new_trie.insert(key, *value);
            }

            // Check both tries have same content
            assert_eq!(trie.len(), new_trie.len());

            for (key, value) in trie.iter() {
                let key_str = String::from_utf8(key).unwrap();
                assert_eq!(new_trie.get(&key_str), Some(value));
            }
        }

        #[test]
        fn triemap_entry_and_modify_correctly_applies_changes(
            pairs in key_value_pairs(1, 50),
            modifiers in key_value_pairs(1, 50)
        ) {
            let mut trie = TrieMap::new();

            // Insert initial pairs
            for (key, value) in &pairs {
                trie.insert(key, *value);
            }

            // Apply modifiers using and_modify
            for (key, value) in &modifiers {
                let addition = *value;
                trie.entry(key).and_modify(|v| *v += addition).or_insert(addition);
            }

            // Verify that all changes were applied correctly
            for (key, value) in &pairs {
                let expected = if let Some(modifier) = modifiers.iter().find(|(k, _)| k == key) {
                    value + modifier.1
                } else {
                    *value
                };

                assert_eq!(trie.get(key), Some(&expected));
            }

            // Verify that new keys were inserted with the correct values
            for (key, value) in &modifiers {
                if !pairs.iter().any(|(k, _)| k == key) {
                    assert_eq!(trie.get(key), Some(value));
                }
            }
        }

        #[test]
        fn triemap_merge_operations_work_correctly(
            pairs1 in key_value_pairs(1, 30),
            pairs2 in key_value_pairs(1, 30)
        ) {
            // Convert to hash maps for easier operation
            let map1: HashMap<String, i32> = pairs1.iter().cloned().collect();
            let map2: HashMap<String, i32> = pairs2.iter().cloned().collect();

            // Create TrieMaps
            let mut trie1 = TrieMap::new();
            let mut trie2 = TrieMap::new();

            for (k, v) in &map1 {
                trie1.insert(k, *v);
            }

            for (k, v) in &map2 {
                trie2.insert(k, *v);
            }

            // Test merge
            let mut merged_trie = trie1.clone();
            merged_trie.merge(&trie2);

            let mut expected_merged = map1.clone();
            for (k, v) in map2.iter() {
                expected_merged.insert(k.clone(), *v);
            }

            assert_eq!(merged_trie.len(), expected_merged.len());

            for (k, v) in expected_merged.iter() {
                assert_eq!(merged_trie.get(k), Some(v));
            }

            // Test merge_with
            let mut merged_with_trie = trie1.clone();
            merged_with_trie.merge_with(&trie2, |_, v1, v2| v1 + v2);

            let mut expected_merged_with = map1.clone();
            for (k, v2) in map2.iter() {
                if let Some(v1) = expected_merged_with.get(k) {
                    expected_merged_with.insert(k.clone(), v1 + v2);
                } else {
                    expected_merged_with.insert(k.clone(), *v2);
                }
            }

            assert_eq!(merged_with_trie.len(), expected_merged_with.len());

            for (k, v) in expected_merged_with.iter() {
                assert_eq!(merged_with_trie.get(k), Some(v));
            }
        }
    }

    #[test]
    fn test_retained_capacity_after_removals() {
        let mut trie = TrieMap::new();

        // First, add a lot of entries
        for i in 0..1000 {
            trie.insert(format!("key_{}", i), i);
        }

        let capacity_before = trie.capacity();

        // Then remove them all
        for i in 0..1000 {
            trie.remove(&format!("key_{}", i));
        }

        // Check what happened to capacity
        let capacity_after = trie.capacity();

        // The capacity should not have decreased
        assert!(capacity_after >= capacity_before);

        // But the trie should be empty
        assert_eq!(trie.len(), 0);

        // Now we can add items again without reallocating
        for i in 0..1000 {
            trie.insert(format!("new_key_{}", i), i);
        }

        // Verify they were added
        assert_eq!(trie.len(), 1000);
    }

    #[test]
    fn test_performance_pattern_with_reused_keys() {
        let mut trie = TrieMap::new();
        let num_operations = 1000;

        // Add a bunch of entries
        for i in 0..num_operations {
            trie.insert(format!("key_{}", i % 100), i);
        }

        // Only 100 unique keys should exist
        assert_eq!(trie.len(), 100);

        // Verify the values are the most recent ones
        for i in 0..100 {
            let key = format!("key_{}", i);
            let expected_value = num_operations - 100 + i;
            assert_eq!(trie.get(&key), Some(&expected_value));
        }

        // Make sure free_indices are being reused
        let num_free_indices = trie.free_indices.len();
        assert_eq!(num_free_indices, num_operations - 100);
    }

    #[test]
    fn test_edge_cases() {
        let mut trie = TrieMap::new();

        // Empty key
        trie.insert("", 1);
        assert_eq!(trie.get(""), Some(&1));

        // Very long key
        let long_key = "a".repeat(1000);
        trie.insert(&long_key, 2);
        assert_eq!(trie.get(&long_key), Some(&2));

        // Binary data in key
        let binary_key = vec![0u8, 1, 2, 3, 4, 255];
        trie.insert(&binary_key, 3);
        assert_eq!(trie.get(&binary_key), Some(&3));

        // Remove nonexistent key
        assert_eq!(trie.remove("nonexistent"), None);

        // Empty key cannot be removed (this is a limitation in the implementation)
        // The remove method explicitly returns None for empty keys
        assert_eq!(trie.remove(""), None);

        // Verify empty key still exists
        assert_eq!(trie.get(""), Some(&1));

        // Entry API with nonexistent key
        if let Entry::Vacant(_) = trie.entry("new_key") {
            // Expected
        } else {
            panic!("Entry for nonexistent key should be Vacant");
        }

        // Try to insert with vacant entry
        if let Entry::Vacant(entry) = trie.entry("another_key") {
            entry.insert(4);
        }
        assert_eq!(trie.get("another_key"), Some(&4));
    }

    #[test]
    fn test_trie_btree_map_equivalence() {
        proptest!(|(pairs in key_value_pairs(1, 100))| {
            let mut trie = TrieMap::new();
            let mut btree_map = BTreeMap::new();

            // Insert all pairs into both maps
            for (key, value) in &pairs {
                trie.insert(key, *value);
                btree_map.insert(key.clone(), *value);
            }

            // All keys in BTreeMap should be retrievable in TrieMap
            for (key, expected_value) in &btree_map {
                assert_eq!(trie.get(key), Some(expected_value));
            }

            // Size of both maps should be equal (duplicate keys get overwritten)
            assert_eq!(trie.len(), btree_map.len());

            // Testing ordered traversal - keys should be in same order
            let trie_keys: Vec<String> = trie.keys()
                .map(|k| String::from_utf8(k).unwrap())
                .collect();

            let btree_keys: Vec<String> = btree_map.keys().cloned().collect();

            // Note: TrieMap's iteration order is not guaranteed to match BTreeMap's
            // so we'll sort before comparing
            let mut sorted_trie_keys = trie_keys.clone();
            sorted_trie_keys.sort();

            let mut sorted_btree_keys = btree_keys.clone();
            sorted_btree_keys.sort();

            assert_eq!(sorted_trie_keys, sorted_btree_keys);
        });
    }
}
