use super::*;
use proptest::prelude::*;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;

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

fn prefixed_keys(
    prefixes: Vec<&'static str>,
    min_pairs: usize,
    max_pairs: usize,
) -> impl Strategy<Value = Vec<(String, i32)>> {
    let prefixes_strategy = proptest::sample::select(prefixes);
    proptest::collection::vec(
        (
            prefixes_strategy.prop_flat_map(|prefix| {
                "[a-zA-Z0-9]{0,8}".prop_map(move |s| format!("{}{}", prefix, s))
            }),
            proptest::num::i32::ANY,
        ),
        min_pairs..max_pairs,
    )
}

fn binary_key_value_pairs(
    min_pairs: usize,
    max_pairs: usize,
) -> impl Strategy<Value = Vec<(Vec<u8>, i32)>> {
    proptest::collection::vec(
        (
            proptest::collection::vec(any::<u8>(), 1..20),
            proptest::num::i32::ANY,
        ),
        min_pairs..max_pairs,
    )
}

#[derive(Debug, Clone)]
enum Operation {
    Insert(String, i32),
    Remove(String),
    RemovePrefix(String),
}

#[test]
fn test_triemap_more_edge_cases() {
    // Test with empty key
    let mut trie = TrieMap::new();
    trie.insert("", 1);
    assert_eq!(trie.get(""), Some(&1));
    assert_eq!(trie.len(), 1);

    // Test with very long key
    let long_key = "a".repeat(1000);
    trie.insert(&long_key, 2);
    assert_eq!(trie.get(&long_key), Some(&2));
    assert_eq!(trie.len(), 2);

    // Test with keys containing all possible byte values
    for byte in 0..=255u8 {
        let key = vec![byte];
        trie.insert(&key, byte as i32);
    }

    assert_eq!(trie.len(), 2 + 256);

    for byte in 0..=255u8 {
        let key = vec![byte];
        assert_eq!(trie.get(&key), Some(&(byte as i32)));
    }

    // Test with a key containing zero bytes
    let zero_bytes_key = vec![0, 0, 0];
    trie.insert(&zero_bytes_key, 999);
    assert_eq!(trie.get(&zero_bytes_key), Some(&999));

    // Test prefix operations on binary data
    let prefix = vec![0];
    let matches = trie.get_prefix_matches(&prefix);
    assert!(matches.len() >= 2); // At least the single zero byte key and the zero_bytes_key

    // Test with key containing all possible byte values
    let all_bytes: Vec<u8> = (0..=255).collect();
    trie.insert(&all_bytes, 1000);
    assert_eq!(trie.get(&all_bytes), Some(&1000));
}

#[test]
fn test_triemap_memory_reuse() {
    let mut trie = TrieMap::new();

    // Insert data
    for i in 0..100 {
        trie.insert(format!("key_{}", i), i);
    }

    // Record free indices before removal
    let free_indices_before = trie.free_indices.len();

    // Remove some data
    for i in 0..50 {
        trie.remove(format!("key_{}", i));
    }

    // Check free indices after removal
    let free_indices_after = trie.free_indices.len();
    assert_eq!(free_indices_after, free_indices_before + 50);

    // Insert new data, should reuse free indices
    for i in 100..150 {
        trie.insert(format!("key_{}", i), i);
    }

    // Free indices should be used up
    assert_eq!(trie.free_indices.len(), free_indices_before);

    // Verify data integrity
    for i in 50..150 {
        assert_eq!(trie.get(format!("key_{}", i)), Some(&{ i }));
    }
}

// Test for empty trie behavior
#[test]
fn test_empty_triemap_behavior() {
    let mut trie: TrieMap<i32> = TrieMap::new();

    // Empty trie tests
    assert!(trie.is_empty());
    assert_eq!(trie.len(), 0);
    assert!(trie.iter().next().is_none());
    assert!(trie.keys().next().is_none());
    assert!(trie.values().next().is_none());

    // Empty prefix operations
    assert!(!trie.starts_with("any"));
    assert!(trie.get_prefix_matches("any").is_empty());
    assert!(trie.prefix_iter("any").next().is_none());

    // Entry API on empty trie
    if let Entry::Vacant(_) = trie.entry("test") {
        // This is expected
    } else {
        panic!("Entry for nonexistent key should be Vacant");
    }

    // Remove on empty trie
    assert_eq!(trie.remove("anything"), None);

    // Ensure trie is still empty
    assert!(trie.is_empty());
}

proptest! {

              #[test]
        fn pruning_preserves_values(pairs in key_value_pairs(1, 100), to_remove in key_value_pairs(1, 50)) {
            let mut trie = TrieMap::new();
            let mut reference_map = BTreeMap::new();

            for (key, value) in &pairs {
                trie.insert(key, *value);
                reference_map.insert(key.clone(), *value);
            }

            for (key, _) in &to_remove {
                trie.remove(key);
                reference_map.remove(key);
            }

            trie.prune();

            for (key, expected_value) in &reference_map {
                prop_assert_eq!(trie.get(key), Some(expected_value));
            }

            for (key, _) in &to_remove {
                if !reference_map.contains_key(key) {
                    prop_assert_eq!(trie.get(key), None);
                }
            }

            prop_assert_eq!(trie.len(), reference_map.len());
        }
        // Test that multiple prune operations are idempotent
        #[test]
        fn multiple_prunes_are_idempotent(
            pairs in key_value_pairs(1, 100),
            to_remove in key_value_pairs(1, 50)
        ) {
            let mut trie = TrieMap::new();

            // Insert all pairs
            for (key, value) in &pairs {
                trie.insert(key, *value);
            }

            // Remove some keys
            for (key, _) in &to_remove {
                trie.remove(key);
            }

            // First prune
            let first_pruned = trie.prune();
            let size_after_first = trie.len();

            // Second prune
            let second_pruned = trie.prune();
            let size_after_second = trie.len();

            // The second prune should not remove any nodes
            prop_assert_eq!(second_pruned, 0);

            // Sizes should be the same
            prop_assert_eq!(size_after_first, size_after_second);
        }

            #[test]
        fn removal_works_correctly(pairs in key_value_pairs(5, 100)) {
            let mut trie = TrieMap::new();
            let mut reference_map = BTreeMap::new();

            // Insert all pairs
            for (key, value) in &pairs {
                trie.insert(key, *value);
                reference_map.insert(key.clone(), *value);
            }

            // Get the unique keys that were actually inserted (last value wins for duplicates)
            let unique_keys: Vec<String> = reference_map.keys().cloned().collect();

            // Remove half of the unique keys
            let mut removed = 0;
            for (i, key) in unique_keys.iter().enumerate() {
                if i % 2 == 0 {  // Only remove every other key
                    let expected_value = reference_map.get(key).copied();
                    let trie_removed = trie.remove(key);
                    let ref_removed = reference_map.remove(key);

                    // The removed value should match between trie and reference map
                    prop_assert_eq!(trie_removed, ref_removed);
                    // And should match what we expected to remove
                    prop_assert_eq!(trie_removed, expected_value);

                    removed += 1;
                }
            }

            // Check that the size is correct
            prop_assert_eq!(trie.len(), reference_map.len());

            // Check that all remaining keys are accessible
            for (key, value) in &reference_map {
                prop_assert_eq!(trie.get(key), Some(value));
            }

            // Check that removed keys are not accessible
            for (i, key) in unique_keys.iter().enumerate() {
                if i % 2 == 0 {  // These were removed
                    prop_assert_eq!(trie.get(key), None);
                }
            }
        }

        #[test]
        fn iteration_after_removal_is_correct(
            pairs in key_value_pairs(5, 100),
            removal_indices in proptest::collection::vec(0..100usize, 1..50)
        ) {
            let mut trie = TrieMap::new();
            let mut reference_map = BTreeMap::new();

            // Insert all pairs
            for (key, value) in &pairs {
                trie.insert(key, *value);
                reference_map.insert(key.clone(), *value);
            }

            // Create list of keys to remove (using indices to prevent duplicates)
            let keys_to_remove: Vec<String> = removal_indices.iter()
                .filter(|&idx| *idx < pairs.len())
                .map(|&idx| pairs[idx].0.clone())
                .collect();

            // Remove selected keys
            for key in &keys_to_remove {
                trie.remove(key);
                reference_map.remove(key);
            }

            // Get all key-value pairs from trie iteration
            let mut trie_pairs: Vec<(String, i32)> = trie.iter()
                .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
                .collect();

            // Get all key-value pairs from reference map
            let mut ref_pairs: Vec<(String, i32)> = reference_map
                .iter()
                .map(|(k, &v)| (k.clone(), v))
                .collect();

            // Sort both for comparison
            trie_pairs.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
            ref_pairs.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

            // They should be equal
            prop_assert_eq!(trie_pairs, ref_pairs);

            // Size should match
            prop_assert_eq!(trie.len(), reference_map.len());

            // Check iterator count matches expected count
            prop_assert_eq!(trie.iter().count(), reference_map.len());

            // Also check keys() and values() iterators
            prop_assert_eq!(trie.keys().count(), reference_map.len());
            prop_assert_eq!(trie.values().count(), reference_map.len());

            // Verify removed keys are not present
            for key in &keys_to_remove {
                prop_assert_eq!(trie.get(key), None);
                prop_assert!(!trie.keys().any(|k| String::from_utf8(k.into()).unwrap() == *key));
            }
        }

    #[test]
    fn triemap_correctly_handles_common_prefixes(
        pairs in prefixed_keys(vec!["app", "ban", "car", "dog"], 5, 50)
    ) {
        let mut trie = TrieMap::new();
        let mut hash_map = HashMap::new();

        for (key, value) in &pairs {
            trie.insert(key, *value);
            hash_map.insert(key.clone(), *value);
        }

        for (key, _) in &pairs {
            if key.len() >= 3 {
                let prefix = &key[0..3];

                let prefix_matches = trie.get_prefix_matches(prefix);
                let expected_matches: Vec<_> = hash_map.iter()
                    .filter(|(k, _)| k.starts_with(prefix))
                    .map(|(k, v)| (k.as_bytes().to_vec(), v))
                    .collect();

                assert_eq!(prefix_matches.len(), expected_matches.len());

                let starts_with_result = trie.starts_with(prefix);
                assert_eq!(starts_with_result, !expected_matches.is_empty());
            }
        }
    }

    // New test: TrieMap updates should handle value replacement correctly
    #[test]
    fn triemap_updates_handle_value_replacement(pairs in key_value_pairs(1, 100)) {
        let mut trie = TrieMap::new();
        let mut hash_map = HashMap::new();

        // First insert
        for (key, value) in &pairs {
            trie.insert(key, *value);
            hash_map.insert(key.clone(), *value);
        }

        // Now replace values by adding 100
        for (key, _) in &pairs {
            if let Some(value) = hash_map.get_mut(key) {
                *value += 100;
                trie.insert(key, *value);
            }
        }

        // Verify values were updated
        for (key, expected_value) in &hash_map {
            assert_eq!(trie.get(key), Some(expected_value));
        }
    }



    #[test]
    fn triemap_handles_binary_keys_correctly(pairs in binary_key_value_pairs(1, 50)) {
        let mut trie = TrieMap::new();
        let mut reference_map = HashMap::new();

        for (key, value) in &pairs {
            trie.insert(key, *value);
            reference_map.insert(key.clone(), *value);
        }

        for (key, expected) in &reference_map {
            assert_eq!(trie.get(key), Some(expected));
        }

        assert_eq!(trie.len(), reference_map.len());

        // Test removal
        if let Some((first_key, _)) = pairs.first() {
            trie.remove(first_key);
            reference_map.remove(first_key);

            assert!(!trie.contains_key(first_key));
            assert_eq!(trie.len(), reference_map.len());
        }
    }

    #[test]
    fn triemap_entry_api_complex_operations(
        pairs in key_value_pairs(1, 50),
        new_keys in proptest::collection::vec("[a-zA-Z0-9]{1,10}".prop_map(String::from), 1..30)
    ) {
        let mut trie = TrieMap::new();
        let mut reference_map = HashMap::new();

        for (key, value) in &pairs {
            trie.insert(key, *value);
            reference_map.insert(key.clone(), *value);
        }

        let mut counter = 0;
        for key in &new_keys {
            // Use entry API
            trie.entry(key).or_insert_with(|| {
                counter &= 1;
                counter
            });

            // Reference implementation
            reference_map.entry(key.clone()).or_insert_with(|| {
                counter
            });
        }

        // Test and_modify for existing entries
        for key in reference_map.keys().cloned().collect::<Vec<_>>() {
            trie.entry(&key).and_modify(|v| *v |= 2).or_insert(0);
            reference_map.entry(key).and_modify(|v| *v
                                                |= 2).or_insert(0);
        }

        // Verify maps are equivalent
        assert_eq!(trie.len(), reference_map.len());

        for (key, expected) in &reference_map {
            assert_eq!(trie.get(key), Some(expected));
        }
    }

    #[test]
    fn triemap_retain_predicate(pairs in key_value_pairs(5, 100)) {
        let mut trie = TrieMap::new();
        let mut hash_map = HashMap::new();

        for (key, value) in &pairs {
            trie.insert(key, *value);
            hash_map.insert(key.clone(), *value);
        }

        // Retain only even values
        let predicate = |_: &[u8], v: &mut i32| *v % 2 == 0;
        trie.retain(predicate);

        // Apply same filter to reference map
        hash_map.retain(|_, v| *v % 2 == 0);

        // Verify maps are equivalent
        assert_eq!(trie.len(), hash_map.len());

        for (key, expected) in &hash_map {
            assert_eq!(trie.get(key), Some(expected));
        }

        // Make sure no odd values remain
        for (_, value) in trie.iter() {
            assert_eq!(*value % 2, 0);
        }
    }

    // New test: Drain operation should empty the map
    #[test]
    fn triemap_drain_empties_map(pairs in key_value_pairs(1, 50)) {
        let mut trie = TrieMap::new();

        for (key, value) in &pairs {
            trie.insert(key, *value);
        }

        let original_len = trie.len();
        let drained: Vec<_> = trie.drain().collect();

        // Drained elements should match original length
        assert_eq!(drained.len(), original_len);

        // Map should be empty
        assert_eq!(trie.len(), 0);
        assert!(trie.is_empty());
    }



    #[test]
                fn triemap_insert_get_equivalence(pairs in key_value_pairs(1, 100)) {
                    let mut trie = TrieMap::new();
                    let mut expected_values = HashMap::new();


                    for (key, value) in &pairs {
                        trie.insert(key, *value);
                        expected_values.insert(key.clone(), *value);
                    }


                    for (key, _) in &pairs {
                        let expected = expected_values.get(key).unwrap();
                        assert_eq!(trie.get(key), Some(expected));
                    }
                }

                #[test]
                fn triemap_hashmap_equivalence(pairs in key_value_pairs(1, 100)) {
                    let mut trie = TrieMap::new();
                    let mut hash_map = HashMap::new();


                    for (key, value) in &pairs {
                        trie.insert(key, *value);
                        hash_map.insert(key.clone(), *value);
                    }


                    for (key, expected_value) in &hash_map {
                        assert_eq!(trie.get(key), Some(expected_value));
                    }


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


                    all_pairs.extend(to_remove.iter().cloned());


                    for (key, value) in &all_pairs {
                        trie1.insert(key, *value);
                    }

                    for (key, _) in &to_remove {
                        trie1.remove(key);
                    }


                    for (key, value) in &pairs {
                        if !to_remove.iter().any(|(k, _)| k == key) {
                            trie2.insert(key, *value);
                        }
                    }


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


                    for (key, value) in &pairs {
                        trie1.insert(key, *value);
                        trie2.insert(key, *value);
                    }


                    for (key, value) in &modifiers {
                        trie1.entry(key).or_insert(*value);
                    }


                    for (key, value) in &modifiers {
                        if !trie2.contains_key(key) {
                            trie2.insert(key, *value);
                        }
                    }


                    assert_eq!(trie1.len(), trie2.len());


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


                    if let Some((first_key, _)) = pairs.first() {
                        original.remove(first_key);


                        assert!(cloned.contains_key(first_key));
                    }


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


                    let prefix_matches = trie.get_prefix_matches(&prefix_str);
                    let starts_with = trie.starts_with(&prefix_str);


                    assert_eq!(starts_with, !prefix_matches.is_empty());


                    let prefix_iter_results: Vec<_> = trie.prefix_iter(&prefix_str).collect();
                    assert_eq!(prefix_matches.len(), prefix_iter_results.len());


                    for (key, _) in &prefix_matches {
                        let key_str = String::from_utf8(key.clone()).unwrap();
                        assert!(key_str.starts_with(&prefix_str));
                    }


                    let prefix_keys: Vec<_> = trie.prefix_keys(&prefix_str).collect();
                    assert_eq!(prefix_keys.len(), prefix_matches.len());


                    let prefix_values: Vec<_> = trie.prefix_values(&prefix_str).collect();
                    assert_eq!(prefix_values.len(), prefix_matches.len());


                    let mut trie2 = trie.clone();
                    let removed = trie2.remove_prefix_matches(&prefix_str);


                    assert_eq!(removed.len(), prefix_matches.len());


                    assert_eq!(trie2.len(), trie.len() - removed.len());


                    assert!(!trie2.starts_with(&prefix_str));
                }

                #[test]
                fn triemap_from_into_conversions(pairs in key_value_pairs(1, 100)) {

                    let mut hash_map = HashMap::new();
                    for (key, value) in &pairs {
                        hash_map.insert(key.clone(), *value);
                    }


                    let trie: TrieMap<i32> = TrieMap::from(hash_map.clone());


                    for (key, expected_value) in &hash_map {
                        assert_eq!(trie.get(key), Some(expected_value));
                    }


                    let hash_map2: HashMap<Vec<u8>, i32> = HashMap::from(trie);


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


                    let to_hashmap = |pairs: &[(String, i32)]| -> HashMap<String, i32> {
                        pairs.iter().cloned().collect()
                    };

                    let map1 = to_hashmap(&pairs1);
                    let map2 = to_hashmap(&pairs2);


                    for (key, value) in &map1 {
                        trie1.insert(key, *value);
                    }

                    for (key, value) in &map2 {
                        trie2.insert(key, *value);
                    }


                    let union_count = trie1.union(&trie2).count();
                    let expected_union_count = map1.keys().chain(map2.keys()).collect::<std::collections::HashSet<_>>().len();
                    assert_eq!(union_count, expected_union_count);


                    let intersection_count = trie1.intersect(&trie2).count();
                    let expected_intersection_count = map1.keys()
                        .filter(|k| map2.contains_key(*k))
                        .count();
                    assert_eq!(intersection_count, expected_intersection_count);


                    let difference_count = trie1.difference(&trie2).count();
                    let expected_difference_count = map1.keys()
                        .filter(|k| !map2.contains_key(*k))
                        .count();
                    assert_eq!(difference_count, expected_difference_count);


                    let sym_diff_count = trie1.symmetric_difference(&trie2).count();
                    let expected_sym_diff_count =
                        map1.keys().filter(|k| !map2.contains_key(*k)).count() +
                        map2.keys().filter(|k| !map1.contains_key(*k)).count();
                    assert_eq!(sym_diff_count, expected_sym_diff_count);


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


                    for (key, value) in &pairs {
                        trie.insert(key, *value);
                    }


                    let data: Vec<(String, i32)> = trie.iter()
                        .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
                        .collect();

                    let test_struct = TestStruct { data };


                    let serialized = serde_json::to_string(&test_struct).unwrap();
                    let deserialized: TestStruct = serde_json::from_str(&serialized).unwrap();


                    let mut new_trie = TrieMap::new();
                    for (key, value) in &deserialized.data {
                        new_trie.insert(key, *value);
                    }


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

        let mut test_trie = TrieMap::new();
        let mut reference_trie = TrieMap::new();


        for (key, value) in &pairs {
            test_trie.insert(key, *value);
            reference_trie.insert(key, *value);
        }


        for (key, addition) in &modifiers {
            test_trie.entry(key).and_modify(|v| *v &= *addition).or_insert(*addition);
        }


        for (key, addition) in &modifiers {
            if let Some(current) = reference_trie.get_mut(key) {
                *current &= *addition;
            } else {
                reference_trie.insert(key, *addition);
            }
        }
                    assert_eq!(test_trie.len(), reference_trie.len());


let mut all_keys = std::collections::HashSet::new();
for (k, _) in &pairs {
    all_keys.insert(k.clone());
}
for (k, _) in &modifiers {
    all_keys.insert(k.clone());
}


for key in &all_keys {
    assert_eq!(
        test_trie.get(key),
        reference_trie.get(key),
        "Values differ for key: {}", key
    );
                }
                }
                #[test]
                fn triemap_merge_operations_work_correctly(
                    pairs1 in key_value_pairs(1, 30),
                    pairs2 in key_value_pairs(1, 30)
                ) {

                    let map1: HashMap<String, i32> = pairs1.iter().cloned().collect();
                    let map2: HashMap<String, i32> = pairs2.iter().cloned().collect();

                    let mut trie1 = TrieMap::new();
                    let mut trie2 = TrieMap::new();

                    for (k, v) in &map1 {
                        trie1.insert(k, *v);
                    }

                    for (k, v) in &map2 {
                        trie2.insert(k, *v);
                    }

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

                    let mut merged_with_trie = trie1.clone();
                    merged_with_trie.merge_with(&trie2, |_, v1, v2| v1 | v2);

                    let mut expected_merged_with = map1.clone();
                    for (k, v2) in map2.iter() {
                        if let Some(v1) = expected_merged_with.get(k) {
                            expected_merged_with.insert(k.clone(), v1 | v2);
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

    for i in 0..1000 {
        trie.insert(format!("key_{}", i), i);
    }

    let capacity_before = trie.capacity();

    for i in 0..1000 {
        trie.remove(format!("key_{}", i));
    }

    let capacity_after = trie.capacity();

    assert!(capacity_after >= capacity_before);

    assert_eq!(trie.len(), 0);

    for i in 0..1000 {
        trie.insert(format!("new_key_{}", i), i);
    }

    assert_eq!(trie.len(), 1000);
}

#[test]
fn test_reused_indices_after_removal() {
    let mut trie = TrieMap::new();

    for i in 0..10 {
        trie.insert(format!("key_{}", i), i);
    }

    assert_eq!(trie.free_indices.len(), 0);

    for i in 0..5 {
        trie.remove(format!("key_{}", i));
    }

    assert_eq!(trie.free_indices.len(), 5);

    for i in 10..15 {
        trie.insert(format!("key_{}", i), i);
    }

    assert_eq!(trie.free_indices.len(), 0);

    for i in 5..15 {
        assert_eq!(trie.get(format!("key_{}", i)), Some(&i));
    }
}

#[test]
fn test_edge_cases() {
    let mut trie = TrieMap::new();

    trie.insert("", 1);
    assert_eq!(trie.get(""), Some(&1));

    let long_key = "a".repeat(1000);
    trie.insert(&long_key, 2);
    assert_eq!(trie.get(&long_key), Some(&2));

    let binary_key = vec![0u8, 1, 2, 3, 4, 255];
    trie.insert(&binary_key, 3);

    assert_eq!(trie.get(&binary_key), Some(&3));
    assert_eq!(trie.remove("nonexistent"), None);
    assert_eq!(trie.get(""), Some(&1));
    assert_eq!(trie.remove(""), Some(1));

    if let Entry::Vacant(_) = trie.entry("new_key") {
    } else {
        panic!("Entry for nonexistent key should be Vacant");
    }

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

        for (key, value) in &pairs {
            trie.insert(key, *value);
            btree_map.insert(key.clone(), *value);
        }

        for (key, expected_value) in &btree_map {
            assert_eq!(trie.get(key), Some(expected_value));
        }

        assert_eq!(trie.len(), btree_map.len());

        let trie_keys: Vec<String> = trie.keys()
            .map(|k| String::from_utf8(k.into()).unwrap())
            .collect();

        let btree_keys: Vec<String> = btree_map.keys().cloned().collect();

        let mut sorted_trie_keys = trie_keys.clone();
        sorted_trie_keys.sort();

        let mut sorted_btree_keys = btree_keys.clone();
        sorted_btree_keys.sort();

        assert_eq!(sorted_trie_keys, sorted_btree_keys);
    });
}
