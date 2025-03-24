use super::*;
use crate::node::{set_bit, test_bit, TrieNode};
use std::hash::DefaultHasher;

// Test for the edge case where idx >= current.children.len()
#[test]
fn test_remove_with_corrupted_trie() {
    let mut trie = TrieMap::new();
    trie.insert("abc", 1);

    unsafe {
        // SAFETY: This is unsafe and only for testing purposes
        // We're directly manipulating the internal structure to create an inconsistent state
        let root_ptr = &mut trie.root as *mut TrieNode;
        let root = &mut *root_ptr;

        // Set a bit for a non-existent child
        set_bit(&mut root.is_present, b'x');

        // Verify the bit is set but no corresponding child exists
        assert!(test_bit(&root.is_present, b'x'));
        assert!(popcount(&root.is_present, b'x') as usize >= root.children.len());
    }

    // Now try to remove a key that would require traversing the corrupted path
    let result = trie.remove("x");
    assert_eq!(result, None);

    // The original data should still be intact
    assert_eq!(trie.get("abc"), Some(&1));
}

// Test for the branch that prunes empty nodes during removal
#[test]
fn test_remove_with_node_pruning() {
    let mut trie = TrieMap::new();

    // Insert keys that share a prefix but have distinct endings
    trie.insert("abc", 1);
    trie.insert("abd", 2);
    trie.insert("abcde", 3);

    // Remove a leaf node
    assert_eq!(trie.remove("abcde"), Some(3));

    // The shared prefix nodes should still exist
    assert_eq!(trie.get("abc"), Some(&1));
    assert_eq!(trie.get("abd"), Some(&2));

    // Structure should be optimized - internal nodes without values and without other children
    // should have been removed. Let's verify this by checking that the structure is still navigable.
    assert_eq!(trie.get("abc"), Some(&1));

    // Now remove "abc" - this should trigger pruning of empty nodes
    assert_eq!(trie.remove("abc"), Some(1));

    // "abd" should still be accessible
    assert_eq!(trie.get("abd"), Some(&2));

    // Let's test a more complex case
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);
    trie.insert("abcd", 4);

    // Remove "abcd" - should remove the deepest leaf node
    assert_eq!(trie.remove("abcd"), Some(4));
    assert_eq!(trie.get("abc"), Some(&3));

    // Remove "abc" - should remove the node but keep "ab"
    assert_eq!(trie.remove("abc"), Some(3));
    assert_eq!(trie.get("ab"), Some(&2));

    // Remove "ab" - should remove the node but keep "a"
    assert_eq!(trie.remove("ab"), Some(2));
    assert_eq!(trie.get("a"), Some(&1));

    // Remove "a" - should empty the trie
    assert_eq!(trie.remove("a"), Some(1));
    assert_eq!(trie.len(), 0);
}

// Test for the recursive pruning behavior
#[test]
fn test_cascading_node_pruning() {
    let mut trie = TrieMap::new();

    // Create a deep, linear path
    trie.insert("a", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);
    trie.insert("abcd", 4);
    trie.insert("abcde", 5);

    // Remove the deepest leaf
    assert_eq!(trie.remove("abcde"), Some(5));

    // All other nodes should still be there
    assert_eq!(trie.get("abcd"), Some(&4));
    assert_eq!(trie.get("abc"), Some(&3));
    assert_eq!(trie.get("ab"), Some(&2));
    assert_eq!(trie.get("a"), Some(&1));

    // Now remove the values in reverse order, one by one
    // This should test the recursive node pruning
    assert_eq!(trie.remove("abcd"), Some(4));
    assert_eq!(trie.get("abc"), Some(&3));

    assert_eq!(trie.remove("abc"), Some(3));
    assert_eq!(trie.get("ab"), Some(&2));

    assert_eq!(trie.remove("ab"), Some(2));
    assert_eq!(trie.get("a"), Some(&1));

    assert_eq!(trie.remove("a"), Some(1));
    assert_eq!(trie.len(), 0);

    // Test with branching structure
    let mut trie = TrieMap::new();
    trie.insert("abc", 1);
    trie.insert("abd", 2);
    trie.insert("abe", 3);

    // Remove nodes in a way that tests the delete_child flag propagation
    assert_eq!(trie.remove("abe"), Some(3));
    assert_eq!(trie.len(), 2);

    assert_eq!(trie.remove("abd"), Some(2));
    assert_eq!(trie.len(), 1);

    assert_eq!(trie.remove("abc"), Some(1));
    assert_eq!(trie.len(), 0);
}

// Test for complex pruning with branches
#[test]
fn test_complex_pruning_with_branches() {
    let mut trie = TrieMap::new();

    // Create a structure with multiple branches
    trie.insert("a", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);
    trie.insert("abd", 4);
    trie.insert("abx", 5);
    trie.insert("ac", 6);
    trie.insert("acd", 7);

    // Remove a leaf node
    assert_eq!(trie.remove("abd"), Some(4));

    // The branch should be preserved because other nodes exist
    assert_eq!(trie.get("abc"), Some(&3));
    assert_eq!(trie.get("abx"), Some(&5));

    // Remove another node on the same branch
    assert_eq!(trie.remove("abc"), Some(3));

    // "abx" should still be accessible
    assert_eq!(trie.get("abx"), Some(&5));

    // Remove the last node on this branch
    assert_eq!(trie.remove("abx"), Some(5));

    // "ab" should still be accessible
    assert_eq!(trie.get("ab"), Some(&2));

    // Other branch should be untouched
    assert_eq!(trie.get("ac"), Some(&6));
    assert_eq!(trie.get("acd"), Some(&7));

    // Remove internal node "ab"
    assert_eq!(trie.remove("ab"), Some(2));

    // Other branch still intact
    assert_eq!(trie.get("ac"), Some(&6));
    assert_eq!(trie.get("acd"), Some(&7));

    // Remove from other branch
    assert_eq!(trie.remove("acd"), Some(7));
    assert_eq!(trie.get("ac"), Some(&6));

    // Remove remaining nodes
    assert_eq!(trie.remove("ac"), Some(6));
    assert_eq!(trie.get("a"), Some(&1));

    assert_eq!(trie.remove("a"), Some(1));
    assert_eq!(trie.len(), 0);
}

#[test]
fn test_union() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);
    trie1.insert("b", 2);
    trie1.insert("c", 3);

    let mut trie2 = TrieMap::new();
    trie2.insert("c", 30); // Different value for same key
    trie2.insert("d", 4);
    trie2.insert("e", 5);

    // Collect union results
    let union_results: Vec<(Vec<u8>, &i32)> = trie1.union(&trie2).collect();

    // Sort for consistent comparison
    let mut sorted_results = union_results.clone();
    sorted_results.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    // Check correct number of entries
    assert_eq!(sorted_results.len(), 5);

    // Check each key-value pair
    let result_map: HashMap<String, i32> = sorted_results
        .into_iter()
        .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
        .collect();

    assert_eq!(result_map.get("a"), Some(&1));
    assert_eq!(result_map.get("b"), Some(&2));
    assert_eq!(result_map.get("c"), Some(&3)); // Should use value from trie1
    assert_eq!(result_map.get("d"), Some(&4));
    assert_eq!(result_map.get("e"), Some(&5));

    // Original tries should remain unchanged
    assert_eq!(trie1.len(), 3);
    assert_eq!(trie2.len(), 3);
}

#[test]
fn test_union_empty_maps() {
    // Union with empty maps
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);

    let empty_trie: TrieMap<i32> = TrieMap::new();

    // Union with empty second map
    let union1: Vec<_> = trie1.union(&empty_trie).collect();
    assert_eq!(union1.len(), 1);
    assert_eq!(String::from_utf8(union1[0].0.clone()).unwrap(), "a");
    assert_eq!(*union1[0].1, 1);

    // Union with empty first map
    let union2: Vec<_> = empty_trie.union(&trie1).collect();
    assert_eq!(union2.len(), 1);
    assert_eq!(String::from_utf8(union2[0].0.clone()).unwrap(), "a");
    assert_eq!(*union2[0].1, 1);

    // Union of two empty maps
    let empty_trie2: TrieMap<i32> = TrieMap::new();
    let union3: Vec<_> = empty_trie.union(&empty_trie2).collect();
    assert_eq!(union3.len(), 0);
}

// Tests for Entry API with empty entries
#[test]
fn test_entry_empty_key() {
    let mut trie = TrieMap::new();

    // Test with empty string key
    let empty_str = "";
    {
        let entry = trie.entry(empty_str);
        entry.or_insert(42);
    }

    assert_eq!(trie.get(empty_str), Some(&42));
    assert_eq!(trie.len(), 1);

    // Test with empty byte slice
    let empty_bytes: &[u8] = &[];
    {
        let entry = trie.entry(empty_bytes);
        match entry {
            Entry::Vacant(_) => panic!("Entry should be vacant for a new empty bytes key"),
            Entry::Occupied(mut vacant) => {
                assert_eq!(vacant.key(), empty_bytes);
                vacant.insert(100);
            }
        }
    }

    assert_eq!(trie.get(empty_bytes), Some(&100));

    // Update empty key
    {
        let entry = trie.entry(empty_str);
        match entry {
            Entry::Occupied(mut occupied) => {
                assert_eq!(occupied.key(), empty_bytes);
                assert_eq!(occupied.get(), &100);
                *occupied.get_mut() = 200;
            }
            Entry::Vacant(_) => panic!("Entry should be occupied"),
        }
    }

    assert_eq!(trie.get(empty_str), Some(&200));
}

#[test]
fn test_entry_vacant_methods() {
    let mut trie = TrieMap::new();

    // Test VacantEntry methods
    {
        let entry = trie.entry("test_key");
        match entry {
            Entry::Vacant(vacant) => {
                assert_eq!(vacant.key(), "test_key".as_bytes());
                let value_ref = vacant.insert(42);
                assert_eq!(*value_ref, 42);
            }
            Entry::Occupied(_) => panic!("Entry should be vacant"),
        }
    }

    assert_eq!(trie.get("test_key"), Some(&42));

    // Test Entry::or_default
    {
        let key = "default_key";
        let value_ref = trie.entry(key).or_default();
        assert_eq!(*value_ref, 0); // Default value for i32
        *value_ref = 100;
    }

    assert_eq!(trie.get("default_key"), Some(&100));

    // Test Entry::or_insert_with_key
    {
        let key = "key_length";
        let value_ref = trie.entry(key).or_insert_with_key(|key| key.len() as i32);
        assert_eq!(*value_ref, 10); // Length of "key_length"
    }

    assert_eq!(trie.get("key_length"), Some(&10));
}

#[test]
fn test_occupied_entry_methods() {
    let mut trie = TrieMap::new();
    trie.insert("key1", 10);

    // Test OccupiedEntry::get and get_mut
    {
        let entry = trie.entry("key1");
        match entry {
            Entry::Occupied(mut occupied) => {
                assert_eq!(occupied.key(), "key1".as_bytes());
                assert_eq!(occupied.get(), &10);

                *occupied.get_mut() = 20;
                assert_eq!(occupied.get(), &20);
            }
            Entry::Vacant(_) => panic!("Entry should be occupied"),
        }
    }

    assert_eq!(trie.get("key1"), Some(&20));

    // Test OccupiedEntry::into_mut
    {
        let entry = trie.entry("key1");
        match entry {
            Entry::Occupied(occupied) => {
                let value_ref = occupied.into_mut();
                assert_eq!(*value_ref, 20);
                *value_ref = 30;
            }
            Entry::Vacant(_) => panic!("Entry should be occupied"),
        }
    }

    assert_eq!(trie.get("key1"), Some(&30));

    // Test Entry::and_modify
    {
        let entry = trie.entry("key1");
        let modified_entry = entry.and_modify(|v| *v *= 2);

        match modified_entry {
            Entry::Occupied(occupied) => {
                assert_eq!(occupied.get(), &60);
            }
            Entry::Vacant(_) => panic!("Entry should be occupied"),
        }
    }

    assert_eq!(trie.get("key1"), Some(&60));

    // Test OccupiedEntry::insert
    {
        let entry = trie.entry("key1");
        match entry {
            Entry::Occupied(mut occupied) => {
                let old_value = occupied.insert(100);
                assert_eq!(old_value, 60);
                assert_eq!(occupied.get(), &100);
            }
            Entry::Vacant(_) => panic!("Entry should be occupied"),
        }
    }

    assert_eq!(trie.get("key1"), Some(&100));

    // Test OccupiedEntry::remove
    {
        let entry = trie.entry("key1");
        match entry {
            Entry::Occupied(occupied) => {
                let value = occupied.remove();
                assert_eq!(value, 100);
            }
            Entry::Vacant(_) => panic!("Entry should be occupied"),
        }
    }

    assert_eq!(trie.get("key1"), None);
}

#[test]
fn test_vacant_entry_on_empty_trie() {
    let mut empty_trie: TrieMap<i32> = TrieMap::new();

    // Check that entries in an empty trie are vacant
    match empty_trie.entry("key") {
        Entry::Vacant(vacant) => {
            assert_eq!(vacant.key(), b"key");
            let value_ref = vacant.insert(42);
            assert_eq!(*value_ref, 42);
        }
        Entry::Occupied(_) => panic!("Entry should be vacant in an empty trie"),
    }

    assert_eq!(empty_trie.len(), 1);
    assert_eq!(empty_trie.get("key"), Some(&42));

    // Test entry API chaining on an empty trie
    let mut new_empty_trie: TrieMap<String> = TrieMap::new();

    let value = new_empty_trie
        .entry("chain")
        .or_insert_with(|| String::from("initial"));

    assert_eq!(value, "initial");

    // Test or_default on empty trie
    let mut default_trie: TrieMap<Vec<i32>> = TrieMap::new();
    let vec_ref = default_trie.entry("default").or_default();
    assert!(vec_ref.is_empty()); // Default for Vec<i32> is an empty vec

    vec_ref.push(1);
    vec_ref.push(2);

    assert_eq!(default_trie.get("default"), Some(&vec![1, 2]));

    // Test multiple entry operations on same empty trie
    let mut multi_entry_trie: TrieMap<i32> = TrieMap::new();

    multi_entry_trie.entry("a").or_insert(1);
    multi_entry_trie.entry("b").or_insert(2);
    multi_entry_trie.entry("c").or_insert(3);

    assert_eq!(multi_entry_trie.len(), 3);

    // Test entry_ref on empty trie
    let mut ref_trie: TrieMap<i32> = TrieMap::new();
    let key = String::from("ref_key");

    match ref_trie.entry_ref(&key) {
        Entry::Vacant(vacant) => {
            assert_eq!(vacant.key(), b"ref_key");
            vacant.insert(100);
        }
        Entry::Occupied(_) => panic!("Entry should be vacant"),
    }

    assert_eq!(ref_trie.get(&key), Some(&100));
}

// Tests for set operations (intersection, difference, symmetric_difference)
#[test]
fn test_intersection() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);
    trie1.insert("b", 2);
    trie1.insert("c", 3);

    let mut trie2 = TrieMap::new();
    trie2.insert("b", 20); // Different value
    trie2.insert("c", 30); // Different value
    trie2.insert("d", 40);

    // Test intersection - should contain keys present in both tries with values from trie1
    let intersection: Vec<_> = trie1.intersect(&trie2).collect();

    assert_eq!(intersection.len(), 2);

    // Sort for consistent comparison
    let mut sorted_intersection = intersection.clone();
    sorted_intersection.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    // Check keys and values
    assert_eq!(
        String::from_utf8(sorted_intersection[0].0.clone()).unwrap(),
        "b"
    );
    assert_eq!(*sorted_intersection[0].1, 2); // Value from trie1

    assert_eq!(
        String::from_utf8(sorted_intersection[1].0.clone()).unwrap(),
        "c"
    );
    assert_eq!(*sorted_intersection[1].1, 3); // Value from trie1

    // Empty intersection
    let empty_trie: TrieMap<i32> = TrieMap::new();
    let empty_intersection: Vec<_> = trie1.intersect(&empty_trie).collect();
    assert_eq!(empty_intersection.len(), 0);

    // Intersection with self
    let self_intersection: Vec<_> = trie1.intersect(&trie1).collect();
    assert_eq!(self_intersection.len(), 3); // Should contain all keys
}

#[test]
fn test_difference() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);
    trie1.insert("b", 2);
    trie1.insert("c", 3);

    let mut trie2 = TrieMap::new();
    trie2.insert("b", 20);
    trie2.insert("c", 30);
    trie2.insert("d", 40);

    // Test difference - should contain keys in trie1 that aren't in trie2
    let difference: Vec<_> = trie1.difference(&trie2).collect();

    assert_eq!(difference.len(), 1);
    assert_eq!(String::from_utf8(difference[0].0.clone()).unwrap(), "a");
    assert_eq!(*difference[0].1, 1);

    // Test difference in the other direction
    let reverse_difference: Vec<_> = trie2.difference(&trie1).collect();

    assert_eq!(reverse_difference.len(), 1);
    assert_eq!(
        String::from_utf8(reverse_difference[0].0.clone()).unwrap(),
        "d"
    );
    assert_eq!(*reverse_difference[0].1, 40);

    // Difference with empty map
    let empty_trie: TrieMap<i32> = TrieMap::new();
    let diff_with_empty: Vec<_> = trie1.difference(&empty_trie).collect();
    assert_eq!(diff_with_empty.len(), 3); // Should contain all keys from trie1

    // Difference with self
    let self_diff: Vec<_> = trie1.difference(&trie1).collect();
    assert_eq!(self_diff.len(), 0); // Should be empty
}

#[test]
fn test_symmetric_difference() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);
    trie1.insert("b", 2);
    trie1.insert("c", 3);

    let mut trie2 = TrieMap::new();
    trie2.insert("b", 20);
    trie2.insert("c", 30);
    trie2.insert("d", 40);

    // Test symmetric difference - should contain keys that are in either trie but not both
    let sym_diff: Vec<_> = trie1.symmetric_difference(&trie2).collect();

    assert_eq!(sym_diff.len(), 2);

    // Sort for consistent comparison
    let mut sorted_sym_diff = sym_diff.clone();
    sorted_sym_diff.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    // Check keys and values
    assert_eq!(
        String::from_utf8(sorted_sym_diff[0].0.clone()).unwrap(),
        "a"
    );
    assert_eq!(*sorted_sym_diff[0].1, 1);

    assert_eq!(
        String::from_utf8(sorted_sym_diff[1].0.clone()).unwrap(),
        "d"
    );
    assert_eq!(*sorted_sym_diff[1].1, 40);

    // Symmetric difference with empty map
    let empty_trie: TrieMap<i32> = TrieMap::new();
    let sym_diff_with_empty: Vec<_> = trie1.symmetric_difference(&empty_trie).collect();
    assert_eq!(sym_diff_with_empty.len(), 3); // Should contain all keys from trie1

    // Symmetric difference with self
    let self_sym_diff: Vec<_> = trie1.symmetric_difference(&trie1).collect();
    assert_eq!(self_sym_diff.len(), 0); // Should be empty
}

// Tests for chained set operations
#[test]
fn test_chained_set_operations() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);
    trie1.insert("b", 2);

    let mut trie2 = TrieMap::new();
    trie2.insert("b", 20);
    trie2.insert("c", 30);

    let mut trie3 = TrieMap::new();
    trie3.insert("c", 300);
    trie3.insert("d", 400);

    // Chain union and intersection
    // Union of trie1 and trie2, then intersect with trie3
    let union_then_intersect: Vec<_> = trie1
        .union(&trie2)
        .filter(|(key, _)| trie3.contains_key(key))
        .collect();

    assert_eq!(union_then_intersect.len(), 1);
    assert_eq!(
        String::from_utf8(union_then_intersect[0].0.clone()).unwrap(),
        "c"
    );
    assert_eq!(*union_then_intersect[0].1, 30); // Value from trie2

    // Chain difference and collect
    let key_difference: Vec<String> = trie1
        .difference(&trie2)
        .map(|(key, _)| String::from_utf8(key).unwrap())
        .collect();

    assert_eq!(key_difference, vec!["a".to_string()]);

    // Chain for complex set operation (elements in trie1 not in trie2, plus elements in trie3)
    let complex_operation: Vec<_> = trie1.difference(&trie2).chain(trie3.iter()).collect();

    assert_eq!(complex_operation.len(), 3); // "a" from difference + "c" and "d" from trie3

    // Sort for consistent checking
    let mut sorted_complex = complex_operation.clone();
    sorted_complex.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    assert_eq!(String::from_utf8(sorted_complex[0].0.clone()).unwrap(), "a");
    assert_eq!(*sorted_complex[0].1, 1);

    assert_eq!(String::from_utf8(sorted_complex[1].0.clone()).unwrap(), "c");
    assert_eq!(*sorted_complex[1].1, 300);

    assert_eq!(String::from_utf8(sorted_complex[2].0.clone()).unwrap(), "d");
    assert_eq!(*sorted_complex[2].1, 400);
}

// Tests for AsBytes trait
#[test]
fn test_as_bytes_implementations() {
    // Test AsBytes for str
    let s = "hello";
    assert_eq!(s.as_bytes(), b"hello");

    // Test AsBytes for String
    let string = String::from("hello");
    assert_eq!(string.as_bytes(), b"hello");

    // Test AsBytes for &str
    let s_ref: &str = "hello";
    assert_eq!(s_ref.as_bytes(), b"hello");

    // Test AsBytes for &String
    let string_ref: &String = &string;
    assert_eq!(string_ref.as_bytes(), b"hello");

    // Test AsBytes for [u8]
    let bytes = b"hello".as_slice();
    assert_eq!(bytes.as_bytes(), b"hello");

    // Test AsBytes for Vec<u8>
    let vec_bytes = b"hello".to_vec();
    assert_eq!(vec_bytes.as_bytes(), b"hello");

    // Test AsBytes for &[u8]
    let bytes_ref: &[u8] = b"hello";
    assert_eq!(bytes_ref.as_bytes(), b"hello");

    // Test AsBytes for [u8; N]
    let array_bytes: [u8; 5] = *b"hello";
    assert_eq!(array_bytes.as_bytes(), b"hello");

    // Test as_bytes_vec method
    assert_eq!(s.as_bytes_vec(), b"hello".to_vec());
    assert_eq!(string.as_bytes_vec(), b"hello".to_vec());
    assert_eq!(bytes.as_bytes_vec(), b"hello".to_vec());
    assert_eq!(vec_bytes.as_bytes_vec(), b"hello".to_vec());
}

#[test]
fn test_as_bytes_in_trie_operations() {
    let mut trie = TrieMap::new();

    // Insert with different key types
    trie.insert("string_key", 1); // &str
    trie.insert(String::from("owned_key"), 2); // String
    trie.insert(b"byte_key".as_ref(), 3); // &[u8]
    trie.insert(b"vec_key".to_vec(), 4); // Vec<u8>

    let static_array: [u8; 10] = *b"array_key\0";
    trie.insert(static_array, 5); // [u8; N]

    // Access with different key types
    assert_eq!(trie.get("string_key"), Some(&1));
    assert_eq!(trie.get(String::from("string_key")), Some(&1));
    assert_eq!(trie.get(b"string_key".as_ref()), Some(&1));
    assert_eq!(trie.get(b"string_key".to_vec()), Some(&1));

    assert_eq!(trie.get("owned_key"), Some(&2));
    assert_eq!(trie.get(String::from("owned_key")), Some(&2));

    assert_eq!(trie.get("byte_key"), Some(&3));
    assert_eq!(trie.get(b"byte_key"), Some(&3));

    assert_eq!(trie.get("vec_key"), Some(&4));
    assert_eq!(trie.get(b"vec_key".to_vec()), Some(&4));

    assert_eq!(trie.get("array_key\0"), Some(&5));
    assert_eq!(trie.get(static_array), Some(&5));

    // Entry API with different key types
    trie.entry(String::from("new_key")).or_insert(10);
    assert_eq!(trie.get("new_key"), Some(&10));

    *trie.entry(b"byte_entry".to_vec()).or_insert(20) += 5;
    assert_eq!(trie.get("byte_entry"), Some(&25));
}

#[test]
fn test_iter_mut() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    for (_, value) in trie.iter_mut() {
        *value *= 10;
    }

    assert_eq!(trie.get("a"), Some(&10));
    assert_eq!(trie.get("b"), Some(&20));
    assert_eq!(trie.get("c"), Some(&30));
}

#[test]
fn test_values_mut() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    let mut sum = 0;
    for value in trie.values_mut() {
        sum += *value;
        *value += 5;
    }

    assert_eq!(sum, 6);
    assert_eq!(trie.get("a"), Some(&6));
    assert_eq!(trie.get("b"), Some(&7));
    assert_eq!(trie.get("c"), Some(&8));
}

#[test]
fn test_iter_mut_modification_during_iteration() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    // Make sure we can modify values based on key content
    for (key, value) in trie.iter_mut() {
        if String::from_utf8_lossy(&key) == "b" {
            *value *= 100;
        } else {
            *value *= 10;
        }
    }

    assert_eq!(trie.get("a"), Some(&10));
    assert_eq!(trie.get("b"), Some(&200));
    assert_eq!(trie.get("c"), Some(&30));
}

#[test]
fn test_prefix_iterators() {
    let mut map = TrieMap::new();
    map.insert("apple", 1);
    map.insert("application", 2);
    map.insert("banana", 3);
    map.insert("app", 4);

    // Test prefix_iter
    let mut iter = map.prefix_iter("app").collect::<Vec<_>>();
    iter.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    assert_eq!(iter.len(), 3);
    assert_eq!(String::from_utf8(iter[0].0.clone()).unwrap(), "app");
    assert_eq!(*iter[0].1, 4);
    assert_eq!(String::from_utf8(iter[1].0.clone()).unwrap(), "apple");
    assert_eq!(*iter[1].1, 1);
    assert_eq!(String::from_utf8(iter[2].0.clone()).unwrap(), "application");
    assert_eq!(*iter[2].1, 2);

    // Test prefix_keys
    let mut keys = map.prefix_keys("app").collect::<Vec<_>>();
    keys.sort();

    assert_eq!(keys.len(), 3);
    assert_eq!(String::from_utf8(keys[0].clone()).unwrap(), "app");
    assert_eq!(String::from_utf8(keys[1].clone()).unwrap(), "apple");
    assert_eq!(String::from_utf8(keys[2].clone()).unwrap(), "application");

    // Test prefix_values
    let mut values = map.prefix_values("app").collect::<Vec<_>>();
    values.sort();

    assert_eq!(values, vec![&1, &2, &4]);
}

#[test]
fn test_subset() {
    let mut map1 = TrieMap::new();
    map1.insert("a", 1);
    map1.insert("b", 2);

    let mut map2 = TrieMap::new();
    map2.insert("a", 10);
    map2.insert("b", 20);
    map2.insert("c", 30);

    assert!(map1.is_subset_of(&map2));
    assert!(!map2.is_subset_of(&map1));

    let mut map3 = TrieMap::new();
    map3.insert("a", 1);
    map3.insert("b", 2);

    assert!(map1.is_subset_of(&map3));
    assert!(map3.is_subset_of(&map1));

    assert!(!map1.is_proper_subset_of(&map3));
    assert!(!map3.is_proper_subset_of(&map1));
    assert!(map1.is_proper_subset_of(&map2));
}

#[test]
fn test_add_find() {
    let mut trie = TrieMap::new();

    let test_words = [
        "a", "aa", "aaaa", "al", "aal", "aaaal", "aaa", "aaah", "ah", "aala", "aaaala",
    ];

    for word in &test_words {
        trie.insert(word, 1u32);
    }

    for word in &test_words {
        assert_eq!(trie.get(word), Some(&1));
    }

    assert_eq!(trie.get("xyz"), None);
}

#[test]
fn test_starts_with() {
    let mut trie = TrieMap::new();

    trie.insert("hello", 1);
    trie.insert("help", 2);
    trie.insert("world", 3);
    trie.insert("hero", 4);

    assert!(trie.starts_with("h"));
    assert!(trie.starts_with("he"));
    assert!(trie.starts_with("hel"));
    assert!(trie.starts_with("hell"));
    assert!(trie.starts_with("help"));
    assert!(trie.starts_with("wo"));
    assert!(trie.starts_with("wor"));
    assert!(trie.starts_with("worl"));
    assert!(trie.starts_with("world"));

    assert!(!trie.starts_with("x"));
    assert!(!trie.starts_with("hi"));
    assert!(!trie.starts_with("hellx"));
    assert!(!trie.starts_with("worldx"));

    assert!(trie.starts_with("hello"));
    assert!(trie.starts_with("help"));
    assert!(trie.starts_with("world"));

    trie.remove("hello");
    assert!(!trie.contains_key("hello"));
    assert!(trie.starts_with("hel"));

    trie.remove("help");
    assert!(!trie.starts_with("hel"));
    assert!(trie.starts_with("he"));
}

#[test]
fn test_get_prefix_matches() {
    let mut trie = TrieMap::new();

    trie.insert("hello", 1);
    trie.insert("help", 2);
    trie.insert("world", 3);
    trie.insert("hero", 4);
    trie.insert("helmet", 5);

    let matches_he = trie.get_prefix_matches("he");
    assert_eq!(matches_he.len(), 4);

    let mut sorted_matches: Vec<(String, i32)> = matches_he
        .into_iter()
        .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
        .collect();
    sorted_matches.sort_by_key(|(k, _)| k.clone());

    assert_eq!(sorted_matches[1], ("helmet".to_string(), 5));
    assert_eq!(sorted_matches[0], ("hello".to_string(), 1));
    assert_eq!(sorted_matches[2], ("help".to_string(), 2));
    assert_eq!(sorted_matches[3], ("hero".to_string(), 4));

    let matches_world = trie.get_prefix_matches("world");
    assert_eq!(matches_world.len(), 1);
    assert_eq!(
        String::from_utf8(matches_world[0].0.clone()).unwrap(),
        "world"
    );
    assert_eq!(matches_world[0].1, &3);

    let matches_x = trie.get_prefix_matches("x");
    assert_eq!(matches_x.len(), 0);

    trie.remove("hello");
    trie.remove("help");

    let matches_he_after_remove = trie.get_prefix_matches("he");
    assert_eq!(matches_he_after_remove.len(), 2);

    let mut sorted_matches_after: Vec<(String, i32)> = matches_he_after_remove
        .into_iter()
        .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
        .collect();
    sorted_matches_after.sort_by_key(|(k, _)| k.clone());

    assert_eq!(sorted_matches_after[0], ("helmet".to_string(), 5));
    assert_eq!(sorted_matches_after[1], ("hero".to_string(), 4));
}

#[test]
fn test_bit_operations() {
    let mut bits = [0u64; 4];

    set_bit(&mut bits, 5);
    set_bit(&mut bits, 65);
    set_bit(&mut bits, 127);
    set_bit(&mut bits, 128);

    assert!(test_bit(&bits, 5));
    assert!(test_bit(&bits, 65));
    assert!(test_bit(&bits, 127));
    assert!(test_bit(&bits, 128));
    assert!(!test_bit(&bits, 6));

    clear_bit(&mut bits, 65);
    assert!(!test_bit(&bits, 65));

    assert_eq!(popcount(&bits, 10), 1);
}

#[test]
fn test_update_value() {
    let mut trie = TrieMap::new();

    trie.insert("test", 1);
    assert_eq!(trie.get("test"), Some(&1));

    trie.insert("test", 2);
    assert_eq!(trie.get("test"), Some(&2));

    if let Some(value) = trie.get_mut("test") {
        *value = 3;
    }

    assert_eq!(trie.get("test"), Some(&3));
}

#[test]
fn test_remove() {
    let mut trie = TrieMap::new();

    trie.insert("abc", 1);
    trie.insert("abcd", 2);
    trie.insert("abce", 3);

    assert_eq!(trie.len(), 3);

    assert_eq!(trie.remove("abcd"), Some(2));
    assert_eq!(trie.len(), 2);

    assert_eq!(trie.get("abcd"), None);

    assert_eq!(trie.get("abc"), Some(&1));
    assert_eq!(trie.get("abce"), Some(&3));

    assert_eq!(trie.remove("abc"), Some(1));
    assert_eq!(trie.len(), 1);

    assert_eq!(trie.remove("xyz"), None);
    assert_eq!(trie.len(), 1);
}

#[test]
fn test_clear() {
    let mut trie = TrieMap::new();

    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    assert_eq!(trie.len(), 3);

    trie.clear();

    assert_eq!(trie.len(), 0);
    assert!(trie.is_empty());

    assert_eq!(trie.get("a"), None);
    assert_eq!(trie.get("b"), None);
    assert_eq!(trie.get("c"), None);
}

#[test]
fn test_iterators() {
    let mut trie = TrieMap::new();

    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    let mut keys = trie
        .keys()
        .map(|k| String::from_utf8(k).unwrap())
        .collect::<Vec<_>>();
    keys.sort();
    assert_eq!(keys, vec!["a", "b", "c"]);

    let mut values = trie.values().cloned().collect::<Vec<_>>();
    values.sort();
    assert_eq!(values, vec![1, 2, 3]);

    let mut pairs = trie
        .iter()
        .map(|(k, v)| (String::from_utf8(k).unwrap(), *v))
        .collect::<Vec<_>>();
    pairs.sort_by_key(|(k, _)| k.clone());
    assert_eq!(
        pairs,
        vec![
            ("a".to_string(), 1),
            ("b".to_string(), 2),
            ("c".to_string(), 3)
        ]
    );
}

#[test]
fn test_remove_prefix_matches() {
    let mut trie = TrieMap::new();

    trie.insert("hello", 1);
    trie.insert("help", 2);
    trie.insert("world", 3);
    trie.insert("hero", 4);
    trie.insert("helmet", 5);

    assert_eq!(trie.len(), 5);

    let removed = trie.remove_prefix_matches("hel");

    let mut sorted_removed: Vec<(String, i32)> = removed
        .into_iter()
        .map(|(k, v)| (String::from_utf8(k).unwrap(), v))
        .collect();
    sorted_removed.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    assert_eq!(sorted_removed.len(), 3);
    assert_eq!(sorted_removed[1], ("helmet".to_string(), 5));
    assert_eq!(sorted_removed[0], ("hello".to_string(), 1));
    assert_eq!(sorted_removed[2], ("help".to_string(), 2));

    assert_eq!(trie.len(), 2);
    assert!(!trie.contains_key("hello"));
    assert!(!trie.contains_key("help"));
    assert!(!trie.contains_key("helmet"));
    assert!(trie.contains_key("world"));
    assert!(trie.contains_key("hero"));

    assert!(!trie.starts_with("hel"));

    let empty_removed = trie.remove_prefix_matches("x");
    assert_eq!(empty_removed.len(), 0);
    assert_eq!(trie.len(), 2);

    let world_removed = trie.remove_prefix_matches("world");
    assert_eq!(world_removed.len(), 1);
    assert_eq!(
        String::from_utf8(world_removed[0].0.clone()).unwrap(),
        "world"
    );
    assert_eq!(world_removed[0].1, 3);

    assert_eq!(trie.len(), 1);
    assert!(trie.contains_key("hero"));
    assert!(!trie.contains_key("world"));

    let hero_removed = trie.remove_prefix_matches("h");
    assert_eq!(hero_removed.len(), 1);
    assert_eq!(
        String::from_utf8(hero_removed[0].0.clone()).unwrap(),
        "hero"
    );
    assert_eq!(hero_removed[0].1, 4);

    assert_eq!(trie.len(), 0);
    assert!(trie.is_empty());
}

#[test]
fn test_entry_or_insert() {
    let mut trie = TrieMap::new();

    {
        let entry = trie.entry("key1");
        let value = entry.or_insert(42);
        assert_eq!(*value, 42);
    }

    assert_eq!(trie.get("key1"), Some(&42));

    {
        let entry = trie.entry("key1");
        let value = entry.or_insert(100);
        assert_eq!(*value, 42);
        *value = 100;
    }

    assert_eq!(trie.get("key1"), Some(&100));
}

#[test]
fn test_entry_and_modify() {
    let mut trie = TrieMap::new();
    trie.insert("key1", 42);

    {
        let entry = trie.entry("key1");
        let value = entry.and_modify(|v| *v += 10).or_insert(0);
        assert_eq!(*value, 52);
    }

    assert_eq!(trie.get("key1"), Some(&52));

    {
        let entry = trie.entry("key2");
        let value = entry.and_modify(|v| *v += 10).or_insert(10);
        assert_eq!(*value, 10);
    }

    assert_eq!(trie.get("key2"), Some(&10));
}

#[test]
fn test_entry_or_insert_with() {
    let mut trie = TrieMap::new();

    {
        let entry = trie.entry("key1");
        let value = entry.or_insert_with(|| 42 * 2);
        assert_eq!(*value, 84);
    }

    assert_eq!(trie.get("key1"), Some(&84));

    let called = std::cell::Cell::new(false);
    {
        let entry = trie.entry("key1");
        let value = entry.or_insert_with(|| {
            called.set(true);
            100
        });
        assert_eq!(*value, 84);
        assert_eq!(called.get(), false);
    }
}

#[test]
fn test_entry_or_insert_with_key() {
    let mut trie = TrieMap::new();

    {
        let entry = trie.entry("key1");
        let value = entry.or_insert_with_key(|key| key.len() as i32);
        assert_eq!(*value, 4);
    }

    assert_eq!(trie.get("key1"), Some(&4));
}

#[test]
fn test_occupied_entry_insert() {
    let mut trie = TrieMap::new();
    trie.insert("key1", 42);

    if let Entry::Occupied(mut entry) = trie.entry("key1") {
        let old_value = entry.insert(100);
        assert_eq!(old_value, 42);
    } else {
        panic!("Entry should be occupied");
    }

    assert_eq!(trie.get("key1"), Some(&100));
}

#[test]
fn test_occupied_entry_remove() {
    let mut trie = TrieMap::new();
    trie.insert("key1", 42);

    let value = if let Entry::Occupied(entry) = trie.entry("key1") {
        entry.remove()
    } else {
        panic!("Entry should be occupied");
    };

    assert_eq!(value, 42);

    assert_eq!(trie.get("key1"), None);
}

#[test]
fn test_from_iterator() {
    let pairs = vec![
        ("apple", 1),
        ("banana", 2),
        ("cherry", 3),
        ("date", 4),
        ("elderberry", 5),
    ];

    let trie: TrieMap<i32> = pairs.into_iter().collect();

    assert_eq!(trie.len(), 5);
    assert_eq!(trie.get("apple"), Some(&1));
    assert_eq!(trie.get("banana"), Some(&2));
    assert_eq!(trie.get("cherry"), Some(&3));
    assert_eq!(trie.get("date"), Some(&4));
    assert_eq!(trie.get("elderberry"), Some(&5));

    assert_eq!(trie.get("fig"), None);
}

#[test]
fn test_from_iterator_with_capacity() {
    let mut pairs = Vec::with_capacity(1000);
    for i in 0..100 {
        pairs.push((format!("key_{}", i), i));
    }

    let trie: TrieMap<i32> = pairs.into_iter().collect();

    assert_eq!(trie.len(), 100);
    for i in 0..100 {
        let key = format!("key_{}", i);
        assert_eq!(trie.get(&key), Some(&i));
    }
}

#[test]
fn test_from_iterator_empty() {
    let pairs: Vec<(&str, i32)> = Vec::new();

    let trie: TrieMap<i32> = pairs.into_iter().collect();

    assert_eq!(trie.len(), 0);
    assert!(trie.is_empty());
}

#[test]
fn test_from_iterator_with_duplicates() {
    let pairs = vec![("key", 1), ("key", 2), ("key", 3), ("other", 4)];

    let trie: TrieMap<i32> = pairs.into_iter().collect();

    assert_eq!(trie.len(), 2);
    assert_eq!(trie.get("key"), Some(&3));
    assert_eq!(trie.get("other"), Some(&4));
}

#[test]
fn test_from_iterator_with_different_key_types() {
    let string_pairs = vec![("string_key", 1), ("owned_string", 2)];
    let trie1: TrieMap<i32> = string_pairs.into_iter().collect();
    assert_eq!(trie1.len(), 2);
    assert_eq!(trie1.get("string_key"), Some(&1));
    assert_eq!(trie1.get("owned_string"), Some(&2));

    let byte_pairs = vec![(b"byte_key".to_vec(), 3), (b"another_byte_key".to_vec(), 4)];
    let trie2: TrieMap<i32> = byte_pairs.into_iter().collect();
    assert_eq!(trie2.len(), 2);
    assert_eq!(trie2.get(b"byte_key"), Some(&3));
    assert_eq!(trie2.get(b"another_byte_key"), Some(&4));
}

#[test]
fn test_collect_into_triemap() {
    let pairs = [("one", 1), ("two", 2), ("three", 3)];

    let trie: TrieMap<i32> = pairs.iter().map(|(k, v)| (*k, *v)).collect();

    assert_eq!(trie.len(), 3);
    assert_eq!(trie.get("one"), Some(&1));
    assert_eq!(trie.get("two"), Some(&2));
    assert_eq!(trie.get("three"), Some(&3));
}

#[test]
fn test_from_iterator_with_string_keys() {
    let pairs = vec![
        (String::from("apple"), 1),
        (String::from("banana"), 2),
        (String::from("cherry"), 3),
    ];

    let trie: TrieMap<i32> = pairs.into_iter().collect();

    assert_eq!(trie.len(), 3);
    assert_eq!(trie.get("apple"), Some(&1));
    assert_eq!(trie.get("banana"), Some(&2));
    assert_eq!(trie.get("cherry"), Some(&3));

    assert_eq!(trie.get(String::from("apple")), Some(&1));
}

use std::collections::{BTreeMap, HashMap};

#[test]
fn test_clone() {
    let mut trie = TrieMap::new();
    trie.insert("apple", 1);
    trie.insert("banana", 2);

    let cloned = trie.clone();
    assert_eq!(trie.len(), cloned.len());
    assert_eq!(trie.get("apple"), cloned.get("apple"));
    assert_eq!(trie.get("banana"), cloned.get("banana"));

    trie.insert("apple", 10);
    assert_eq!(trie.get("apple"), Some(&10));
    assert_eq!(cloned.get("apple"), Some(&1));
}

#[test]
fn test_debug() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    let debug_str = format!("{:?}", trie);
    assert!(debug_str.contains("a") && debug_str.contains("1"));
    assert!(debug_str.contains("b") && debug_str.contains("2"));
}

#[test]
fn test_eq() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);
    trie1.insert("b", 2);

    let mut trie2 = TrieMap::new();
    trie2.insert("a", 1);
    trie2.insert("b", 2);

    assert_eq!(trie1, trie2);

    trie2.insert("c", 3);
    assert_ne!(trie1, trie2);

    trie1.insert("c", 3);
    assert_eq!(trie1, trie2);

    trie1.insert("c", 4);
    assert_ne!(trie1, trie2);
}

#[test]
fn test_into_iterator() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    let mut vec: Vec<_> = trie.into_iter().collect();
    vec.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    assert_eq!(vec.len(), 3);
    assert_eq!(vec[0].1, 1);
    assert_eq!(vec[1].1, 2);
    assert_eq!(vec[2].1, 3);

    assert_eq!(String::from_utf8(vec[0].0.clone()).unwrap(), "a");
    assert_eq!(String::from_utf8(vec[1].0.clone()).unwrap(), "b");
    assert_eq!(String::from_utf8(vec[2].0.clone()).unwrap(), "c");
}

#[test]
fn test_into_iter() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    let mut vec: Vec<_> = trie.into_iter().collect();
    vec.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    assert_eq!(vec.len(), 2);
    assert_eq!(vec[0].1, 1);
    assert_eq!(vec[1].1, 2);
}

#[test]
fn test_index() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    assert_eq!(trie["a"], 1);
    assert_eq!(trie["b"], 2);

    trie["a"] = 10;
    assert_eq!(trie["a"], 10);
}

#[test]
#[should_panic(expected = "no entry found for key")]
fn test_index_panic() {
    let trie: TrieMap<i32> = TrieMap::new();
    let _ = trie["nonexistent"];
}

#[test]
fn test_extend() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);

    let vec = vec![("b", 2), ("c", 3)];
    trie.extend(vec);

    assert_eq!(trie.len(), 3);
    assert_eq!(trie.get("a"), Some(&1));
    assert_eq!(trie.get("b"), Some(&2));
    assert_eq!(trie.get("c"), Some(&3));
}

#[test]
fn test_shrink_to_fit() {
    let mut trie = TrieMap::with_capacity(1000);
    assert!(trie.capacity() >= 1000);

    trie.insert("a", 1);
    trie.insert("b", 2);

    trie.shrink_to_fit();

    assert!(trie.capacity() < 1000);
}

#[test]
fn test_reserve() {
    let mut trie: TrieMap<()> = TrieMap::new();
    let initial_cap = trie.capacity();

    trie.reserve(1000);
    assert!(trie.capacity() >= initial_cap + 1000);
}

#[test]
fn test_try_insert() {
    let mut trie = TrieMap::new();

    let result = trie.try_insert("key", 1);
    assert!(result.is_ok());
    assert_eq!(*result.unwrap(), 1);

    let result = trie.try_insert("key", 2);
    assert!(result.is_err());
    assert_eq!(result.err().unwrap(), 2);

    assert_eq!(trie.get("key"), Some(&1));
}

#[test]
fn test_get_key_value() {
    let mut trie = TrieMap::new();
    trie.insert("key", 42);

    let result = trie.get_key_value("key");
    assert!(result.is_some());

    let (key, value) = result.unwrap();
    assert_eq!(String::from_utf8(key).unwrap(), "key");
    assert_eq!(*value, 42);

    assert!(trie.get_key_value("nonexistent").is_none());
}

#[test]
fn test_retain() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);
    trie.insert("d", 4);

    trie.retain(|_, v| *v % 2 == 0);

    assert_eq!(trie.len(), 2);
    assert!(trie.get("a").is_none());
    assert_eq!(trie.get("b"), Some(&2));
    assert!(trie.get("c").is_none());
    assert_eq!(trie.get("d"), Some(&4));
}

#[test]
fn test_retain_with_mutation() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    trie.retain(|_, v| {
        *v *= 2;
        true
    });

    assert_eq!(trie.len(), 2);
    assert_eq!(trie.get("a"), Some(&2));
    assert_eq!(trie.get("b"), Some(&4));
}

#[test]
fn test_drain() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    let mut items = trie.drain().collect::<Vec<_>>();
    items.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    assert_eq!(items.len(), 3);
    assert_eq!(String::from_utf8(items[0].0.clone()).unwrap(), "a");
    assert_eq!(items[0].1, 1);
    assert_eq!(String::from_utf8(items[1].0.clone()).unwrap(), "b");
    assert_eq!(items[1].1, 2);
    assert_eq!(String::from_utf8(items[2].0.clone()).unwrap(), "c");
    assert_eq!(items[2].1, 3);

    assert_eq!(trie.len(), 0);
    assert!(trie.is_empty());
}

#[test]
fn test_into_keys_values() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    let trie_clone = trie.clone();

    let mut keys = trie.into_keys().collect::<Vec<_>>();
    keys.sort();

    assert_eq!(keys.len(), 3);
    assert_eq!(String::from_utf8(keys[0].clone()).unwrap(), "a");
    assert_eq!(String::from_utf8(keys[1].clone()).unwrap(), "b");
    assert_eq!(String::from_utf8(keys[2].clone()).unwrap(), "c");

    let mut values = trie_clone.into_values().collect::<Vec<_>>();
    values.sort();

    assert_eq!(values, vec![1, 2, 3]);
}

#[test]
fn test_entry_ref() {
    let mut trie = TrieMap::new();

    let key_str = "test_key".to_string();
    {
        let entry = trie.entry_ref(&key_str);
        entry.or_insert(42);
    }

    assert_eq!(trie.get(&key_str), Some(&42));

    {
        let entry = trie.entry_ref(&key_str);
        if let Entry::Occupied(mut occupied) = entry {
            *occupied.get_mut() = 100;
        }
    }

    assert_eq!(trie.get(&key_str), Some(&100));
}

#[test]
fn test_conversions_from_map() {
    let mut map = HashMap::new();
    map.insert("a".to_string(), 1);
    map.insert("b".to_string(), 2);

    let trie: TrieMap<i32> = TrieMap::from(map);
    assert_eq!(trie.len(), 2);
    assert_eq!(trie.get("a"), Some(&1));
    assert_eq!(trie.get("b"), Some(&2));

    let mut btree = BTreeMap::new();
    btree.insert("c".to_string(), 3);
    btree.insert("d".to_string(), 4);

    let trie: TrieMap<i32> = TrieMap::from(btree);
    assert_eq!(trie.len(), 2);
    assert_eq!(trie.get("c"), Some(&3));
    assert_eq!(trie.get("d"), Some(&4));
}

#[test]
fn test_conversion_to_hashmap() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    let map: HashMap<Vec<u8>, i32> = HashMap::from(trie);
    assert_eq!(map.len(), 2);
    assert_eq!(map.get("a".as_bytes()), Some(&1));
    assert_eq!(map.get("b".as_bytes()), Some(&2));
}

#[test]
fn test_hash() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);
    trie1.insert("b", 2);

    let mut trie2 = TrieMap::new();
    trie2.insert("a", 1);
    trie2.insert("b", 2);

    let mut hasher1 = DefaultHasher::new();
    trie1.hash(&mut hasher1);
    let hash1 = hasher1.finish();

    let mut hasher2 = DefaultHasher::new();
    trie2.hash(&mut hasher2);
    let hash2 = hasher2.finish();

    assert_eq!(hash1, hash2);

    trie2.insert("c", 3);

    let mut hasher3 = DefaultHasher::new();
    trie2.hash(&mut hasher3);
    let hash3 = hasher3.finish();

    assert_ne!(hash1, hash3);
}

#[test]
fn test_entry_or_default() {
    let mut trie = TrieMap::new();

    {
        let entry = trie.entry("key1");
        let value = entry.or_default();
        *value = 42;
    }

    assert_eq!(trie.get("key1"), Some(&42));

    {
        let entry = trie.entry("key2");
        let _value = entry.or_default();
    }

    assert_eq!(trie.get("key2"), Some(&0));
}

#[test]
fn test_merge() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);
    trie1.insert("b", 2);

    let mut trie2 = TrieMap::new();
    trie2.insert("b", 3);
    trie2.insert("c", 4);

    trie1.merge(&trie2);

    assert_eq!(trie1.len(), 3);
    assert_eq!(trie1.get("a"), Some(&1));
    assert_eq!(trie1.get("b"), Some(&3));
    assert_eq!(trie1.get("c"), Some(&4));
}

#[test]
fn test_merge_with() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);
    trie1.insert("b", 2);

    let mut trie2 = TrieMap::new();
    trie2.insert("b", 3);
    trie2.insert("c", 4);

    trie1.merge_with(&trie2, |_, v1, v2| v1 + v2);

    assert_eq!(trie1.len(), 3);
    assert_eq!(trie1.get("a"), Some(&1));
    assert_eq!(trie1.get("b"), Some(&5));
    assert_eq!(trie1.get("c"), Some(&4));
}

#[test]
fn test_get_or_insert_default() {
    let mut trie = TrieMap::new();

    {
        let value = trie.get_or_insert_default("key1");
        *value = 42;
    }

    assert_eq!(trie.get("key1"), Some(&42));

    {
        let value = trie.get_or_insert_default("key1");
        assert_eq!(*value, 42);
        *value = 100;
    }

    assert_eq!(trie.get("key1"), Some(&100));
}

#[test]
fn test_get_or_insert_with() {
    let mut trie = TrieMap::new();

    {
        let value = trie.get_or_insert_with("key1", || 42);
        assert_eq!(*value, 42);
    }

    let called = std::cell::Cell::new(false);
    {
        let value = trie.get_or_insert_with("key1", || {
            called.set(true);
            100
        });

        assert_eq!(*value, 42);
        assert_eq!(called.get(), false);
    }
}

#[test]
fn test_immutable_operations() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    let trie2 = trie.inserted("c", 3);
    assert_eq!(trie.len(), 2);
    assert_eq!(trie2.len(), 3);
    assert_eq!(trie2.get("c"), Some(&3));

    let trie3 = trie2.removed("b");
    assert_eq!(trie2.len(), 3);
    assert_eq!(trie3.len(), 2);
    assert_eq!(trie3.get("b"), None);

    let trie4 = trie.without_prefix("a");
    assert_eq!(trie4.len(), 1);
    assert_eq!(trie4.get("a"), None);
    assert_eq!(trie4.get("b"), Some(&2));
}

#[test]
fn test_from_array() {
    let trie = TrieMap::from([("a", 1), ("b", 2), ("c", 3)]);

    assert_eq!(trie.len(), 3);
    assert_eq!(trie.get("a"), Some(&1));
    assert_eq!(trie.get("b"), Some(&2));
    assert_eq!(trie.get("c"), Some(&3));
}

#[test]
fn test_from_slice() {
    let slice = [("a", 1), ("b", 2), ("c", 3)];
    let trie = TrieMap::from(&slice[..]);

    assert_eq!(trie.len(), 3);
    assert_eq!(trie.get("a"), Some(&1));
    assert_eq!(trie.get("b"), Some(&2));
    assert_eq!(trie.get("c"), Some(&3));
}

#[test]
fn test_keys_starting_with() {
    let mut trie = TrieMap::new();
    trie.insert("apple", 1);
    trie.insert("apply", 2);
    trie.insert("banana", 3);

    let keys = trie.keys_starting_with("app");
    assert_eq!(keys.len(), 2);

    let mut string_keys: Vec<String> = keys
        .into_iter()
        .map(|k| String::from_utf8(k).unwrap())
        .collect();
    string_keys.sort();

    assert_eq!(string_keys, vec!["apple".to_string(), "apply".to_string()]);
}

#[test]
fn test_update() {
    let mut trie = TrieMap::new();
    trie.insert("key", 10);

    trie.update("key", |v| *v *= 2);
    assert_eq!(trie.get("key"), Some(&20));

    trie.update("nonexistent", |v| *v *= 2);
    assert_eq!(trie.get("nonexistent"), None);
}

#[test]
fn test_update_or_insert() {
    let mut trie = TrieMap::new();
    trie.insert("key1", 10);

    trie.update_or_insert("key1", |v| *v *= 2, || 0);
    assert_eq!(trie.get("key1"), Some(&20));

    trie.update_or_insert("key2", |v| *v *= 2, || 5);
    assert_eq!(trie.get("key2"), Some(&5));
}
