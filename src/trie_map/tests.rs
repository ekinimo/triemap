use super::*;
use crate::entry::{Entry, OccupiedEntry, VacantEntry};
use crate::iter::{DrainIter, Iter, Keys, PrefixIter, PrefixKeys, PrefixValues, Values};
use crate::node::{clear_bit, popcount, set_bit, test_bit};
use crate::node::{TrieNode, TrieNodeIdx};
use std::hash::DefaultHasher;

#[test]
fn test_entry_or_default_with_occupied() {
    let mut trie = TrieMap::new();
    trie.insert("key", 42);

    let value = trie.entry("key").or_default();
    assert_eq!(*value, 42);

    assert_eq!(trie.get("key"), Some(&42));
}

#[test]
fn test_entry_or_insert_with_key_occupied() {
    let mut trie = TrieMap::new();
    trie.insert("key", 42);

    let called = std::cell::Cell::new(false);
    let value = trie.entry("key").or_insert_with_key(|key| {
        called.set(true);
        key.len() as i32
    });

    assert_eq!(*value, 42);
    assert!(!called.get());
}

#[test]
fn test_vacant_entry_all_methods() {
    let mut trie = TrieMap::new();

    let entry = trie.entry("key");

    match entry {
        Entry::Vacant(vacant) => {
            assert_eq!(vacant.key(), b"key");

            let value = vacant.insert(42);
            assert_eq!(*value, 42);
            *value = 100;
        }
        Entry::Occupied(_) => panic!("Expected a vacant entry"),
    }

    assert_eq!(trie.get("key"), Some(&100));
}

#[test]
fn test_occupied_entry_all_methods() {
    let mut trie = TrieMap::new();
    trie.insert("key", 42);

    let entry = trie.entry("key");

    match entry {
        Entry::Occupied(mut occupied) => {
            assert_eq!(occupied.get(), &42);

            *occupied.get_mut() = 100;
            assert_eq!(occupied.get(), &100);

            assert_eq!(occupied.key(), b"key");

            let old_value = occupied.insert(200);
            assert_eq!(old_value, 100);
        }
        Entry::Vacant(_) => panic!("Expected an occupied entry"),
    }

    assert_eq!(trie.get("key"), Some(&200));

    let entry = trie.entry("key");
    if let Entry::Occupied(occupied) = entry {
        let value = occupied.remove();
        assert_eq!(value, 200);
    }

    assert!(!trie.contains_key("key"));
}

#[test]
fn test_entry_and_modify_with_vacant() {
    let mut trie: TrieMap<()> = TrieMap::new();

    let called = std::cell::Cell::new(false);
    let entry = trie.entry("key").and_modify(|_| {
        called.set(true);
    });

    assert!(!called.get());

    match entry {
        Entry::Vacant(_) => {}
        Entry::Occupied(_) => panic!("Expected a vacant entry"),
    }
}

#[test]
fn test_iter_keys_struct() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    let keys_iter = Keys { inner: trie.iter() };
    let keys: Vec<_> = keys_iter.collect();
    assert_eq!(keys.len(), 3);

    let keys_iter = Keys { inner: trie.iter() };
    let hint = keys_iter.size_hint();
    assert_eq!(hint.0, 0);
}

#[test]
fn test_iter_edge_cases() {
    let mut trie = TrieMap::new();

    let mut empty_iter = trie.iter();
    assert_eq!(empty_iter.next(), None);

    trie.insert("a", 1);
    trie.remove("a");

    let key_bytes = "a".as_bytes().to_vec();
    let mut current_id = trie.root;
    for &byte in &key_bytes {
        let has_child = {
            let current_node = trie.pool.get_node(current_id);
            test_bit(&current_node.is_present, byte)
        };

        if !has_child {
            current_id = trie.pool.add_child(current_id, byte);
        } else {
            current_id = trie.pool.get_child_idx_unchecked(current_id, byte);
        }
    }

    let node = trie.pool.get_node(current_id);
    if let Some(data_idx) = node.data_idx {
        assert!(trie.data.get(data_idx).unwrap().is_none());
    }

    assert_eq!(trie.iter().count(), 0);
}

#[test]
fn test_drain_iter_edge_cases() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);

    trie.insert("b", 2);
    trie.remove("b");

    let mut drain = trie.drain();

    assert_eq!(drain.next(), Some(("a".as_bytes().to_vec(), 1)));

    let hint = drain.size_hint();
    assert!(hint.0 <= 1);

    drop(drain);

    assert_eq!(trie.len(), 0);
}

#[test]
fn test_prefix_iter_size_hint() {
    let mut trie = TrieMap::new();
    trie.insert("apple", 1);
    trie.insert("application", 2);

    let prefix_iter = trie.prefix_iter("app");
    let hint = prefix_iter.size_hint();
    assert_eq!(hint.0, 0);
    assert!(hint.1.unwrap() >= 2);

    let prefix_keys = trie.prefix_keys("app");
    let hint = prefix_keys.size_hint();
    assert_eq!(hint.0, 0);
    assert!(hint.1.unwrap() >= 2);

    let prefix_values = trie.prefix_values("app");
    let hint = prefix_values.size_hint();
    assert_eq!(hint.0, 0);
    assert!(hint.1.unwrap() >= 2);
}

#[test]
fn test_entry_vacant_then_occupied() {
    let mut trie = TrieMap::new();

    let key = "test_key";
    assert!(matches!(trie.entry(key), Entry::Vacant(_)));

    assert_eq!(trie.entry(key).get(), None);

    assert_eq!(trie.entry(key).get_mut(), None);

    trie.insert(key, 42);

    assert!(matches!(trie.entry(key), Entry::Occupied(_)));

    assert_eq!(trie.entry(key).get(), Some(&42));

    if let Entry::Occupied(entry) = trie.entry(key) {
        assert_eq!(entry.key(), key.as_bytes());
    }
}

#[test]
fn test_node_from_usize() {
    let idx: TrieNodeIdx = 42.into();
    assert_eq!(idx.0, 42);
}

#[test]
fn test_into_iter_edge_cases() {
    let mut trie: TrieMap<(())> = TrieMap::new();

    let mut empty_into_iter = trie.into_iter();
    assert_eq!(empty_into_iter.next(), None);

    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    trie.insert("c", 3);
    trie.remove("c");

    let mut into_iter = trie.into_iter();
    let mut items = Vec::new();
    while let Some(item) = into_iter.next() {
        items.push(item);
    }

    assert_eq!(items.len(), 2);
    assert!(items.iter().any(|(k, v)| k == b"a" && *v == 1));
    assert!(items.iter().any(|(k, v)| k == b"b" && *v == 2));
}

#[test]
fn test_drain_iter_with_none_value() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    trie.remove("b");

    let drained: Vec<_> = trie.drain().collect();
    assert_eq!(drained.len(), 1);
    assert_eq!(drained[0].0, b"a");
    assert_eq!(drained[0].1, 1);
}

#[test]
fn test_occupied_entry_with_edge_cases() {
    let mut trie = TrieMap::new();
    trie.insert("key", 10);

    let entry = trie.entry("key");
    if let Entry::Occupied(occupied) = entry {
        assert_eq!(occupied.key(), b"key");
    } else {
        panic!("Expected Occupied entry");
    }
}

#[test]
fn test_entry_key_mutated() {
    let mut trie = TrieMap::new();
    trie.insert("key", 10);

    let key = String::from("key");
    let entry = trie.entry_ref(&key);
    match entry {
        Entry::Occupied(occupied) => {
            assert_eq!(occupied.key(), key.as_bytes());
        }
        Entry::Vacant(_) => panic!("Expected Occupied entry"),
    }

    let nonexistent = "nonexistent";
    let entry = trie.entry_ref(nonexistent);
    match entry {
        Entry::Vacant(vacant) => {
            assert_eq!(vacant.key(), nonexistent.as_bytes());
        }
        Entry::Occupied(_) => panic!("Expected Vacant entry"),
    }
}

#[test]
fn test_values_with_none_values() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    trie.remove("b");

    let values: Vec<_> = trie.values().collect();
    assert_eq!(values.len(), 1);
    assert_eq!(*values[0], 1);
}

#[test]
fn test_values_size_hint() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    let values = trie.values();
    let hint = values.size_hint();
    assert!(hint.0 <= hint.1.unwrap_or(usize::MAX));
}
#[test]
fn test_keys_and_data_idx_iterator() {
    let mut map = TrieMap::new();
    map.insert("apple", 1);
    map.insert("app", 2);
    map.insert("banana", 3);

    let keys_data_iter = map.pool.keys_and_indices(map.root);

    let items: Vec<(Box<[u8]>, usize)> = keys_data_iter.collect();

    assert_eq!(items.len(), 3, "Iterator should return exactly 3 items");

    let keys: Vec<String> = items
        .iter()
        .map(|(key, _)| String::from_utf8_lossy(key).to_string())
        .collect();

    assert!(
        keys.contains(&"apple".to_string()),
        "Iterator should return 'apple'"
    );
    assert!(
        keys.contains(&"app".to_string()),
        "Iterator should return 'app'"
    );
    assert!(
        keys.contains(&"banana".to_string()),
        "Iterator should return 'banana'"
    );

    for (_, data_idx) in items {
        assert!(data_idx < map.data.len(), "Data index should be valid");
        assert!(
            map.data[data_idx].is_some(),
            "Data at index should not be None"
        );
    }

    let iter_items: Vec<(Vec<u8>, &i32)> = map.iter().collect();
    assert_eq!(iter_items.len(), 3, "Iter should return exactly 3 items");

    assert_eq!(map.get("apple"), Some(&1));
    assert_eq!(map.get("app"), Some(&2));
    assert_eq!(map.get("banana"), Some(&3));
}

#[test]
fn test_iteration_after_specific_removal_patterns() {
    {
        let mut trie = TrieMap::new();
        trie.insert("apple", 1);
        trie.insert("application", 2);
        trie.insert("banana", 3);

        trie.remove("application");

        let pairs: Vec<(String, i32)> = trie
            .iter()
            .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
            .collect();

        assert_eq!(pairs.len(), 2);
        assert!(pairs.contains(&("apple".to_string(), 1)));
        assert!(pairs.contains(&("banana".to_string(), 3)));
        assert!(!pairs.contains(&("application".to_string(), 2)));
    }

    {
        let mut trie = TrieMap::new();
        trie.insert("a", 1);
        trie.insert("ab", 2);
        trie.insert("abc", 3);

        trie.remove("ab");

        let pairs: Vec<(String, i32)> = trie
            .iter()
            .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
            .collect();

        assert_eq!(pairs.len(), 2);
        assert!(pairs.contains(&("a".to_string(), 1)));
        assert!(pairs.contains(&("abc".to_string(), 3)));
        assert!(!pairs.contains(&("ab".to_string(), 2)));
    }

    {
        let mut trie = TrieMap::new();
        trie.insert("a", 1);

        trie.remove("a");

        let pairs: Vec<(String, i32)> = trie
            .iter()
            .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
            .collect();

        assert_eq!(pairs.len(), 0);
    }

    {
        let mut trie = TrieMap::new();
        trie.insert("a", 1);
        trie.insert("b", 2);

        trie.remove("a");
        trie.insert("a", 10);

        let pairs: Vec<(String, i32)> = trie
            .iter()
            .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
            .collect();

        assert_eq!(pairs.len(), 2);
        assert!(pairs.contains(&("a".to_string(), 10)));
        assert!(pairs.contains(&("b".to_string(), 2)));
    }

    {
        let mut trie = TrieMap::new();
        trie.insert("test", 1);
        trie.insert("testing", 2);
        trie.insert("tested", 3);
        trie.insert("tester", 4);

        trie.remove("testing");
        trie.remove("tested");

        let pairs: Vec<(String, i32)> = trie
            .iter()
            .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
            .collect();

        assert_eq!(pairs.len(), 2);
        assert!(pairs.contains(&("test".to_string(), 1)));
        assert!(pairs.contains(&("tester".to_string(), 4)));
    }

    {
        let mut trie = TrieMap::new();
        trie.insert("foo1", 1);
        trie.insert("foo2", 2);
        trie.insert("bar", 3);

        trie.remove("foo1");
        trie.remove("foo2");

        let pairs: Vec<(String, i32)> = trie
            .iter()
            .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
            .collect();

        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0], ("bar".to_string(), 3));
    }

    {
        let mut trie = TrieMap::new();

        trie.insert("a", 1);
        trie.insert("b", 2);
        trie.remove("a");
        trie.insert("c", 3);
        trie.remove("b");
        trie.insert("d", 4);

        let pairs: Vec<(String, i32)> = trie
            .iter()
            .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
            .collect();

        assert_eq!(pairs.len(), 2);
        assert!(pairs.contains(&("c".to_string(), 3)));
        assert!(pairs.contains(&("d".to_string(), 4)));
    }

    {
        let mut trie = TrieMap::new();
        trie.insert("normal", 1);
        trie.insert("special!@#", 2);
        trie.insert("numbers123", 3);

        trie.remove("special!@#");

        let pairs: Vec<(String, i32)> = trie
            .iter()
            .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
            .collect();

        assert_eq!(pairs.len(), 2);
        assert!(pairs.contains(&("normal".to_string(), 1)));
        assert!(pairs.contains(&("numbers123".to_string(), 3)));
    }
}

#[test]
fn test_improved_remove() {
    let mut trie = TrieMap::new();
    trie.insert("abc", 1);
    trie.insert("abcd", 2);
    trie.insert("abce", 3);

    assert_eq!(trie.remove("abcd"), Some(2));
    assert_eq!(trie.len(), 2);

    assert_eq!(trie.get("abcd"), None);

    assert_eq!(trie.get("abc"), Some(&1));
    assert_eq!(trie.get("abce"), Some(&3));

    trie.insert("abcd", 4);
    assert_eq!(trie.get("abcd"), Some(&4));
    assert_eq!(trie.len(), 3);
}

#[test]
fn test_basic_prune() {
    let mut trie = TrieMap::new();
    trie.insert("abc", 1);
    trie.insert("abcd", 2);
    trie.insert("abce", 3);

    assert_eq!(trie.remove("abcd"), Some(2));
    assert_eq!(trie.remove("abce"), Some(3));

    trie.insert("abcd", 4);
    assert_eq!(trie.get("abcd"), Some(&4));

    assert_eq!(trie.remove("abcd"), Some(4));

    let pruned = trie.prune();
    assert!(pruned > 0);

    trie.insert("abcd", 5);
    assert_eq!(trie.get("abcd"), Some(&5));
}

#[test]
fn test_prune_empty_trie() {
    let mut trie: TrieMap<i32> = TrieMap::new();

    let pruned = trie.prune();
    assert_eq!(pruned, 0);
}

#[test]
fn test_prune_mixed_paths() {
    let mut trie = TrieMap::new();

    trie.insert("a", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);
    trie.insert("abcd", 4);
    trie.insert("abcde", 5);

    trie.insert("abx", 6);
    trie.insert("aby", 7);

    assert_eq!(trie.remove("abcde"), Some(5));
    assert_eq!(trie.remove("abcd"), Some(4));
    assert_eq!(trie.remove("abx"), Some(6));

    let pruned = trie.prune();
    assert!(pruned > 0);

    assert_eq!(trie.get("a"), Some(&1));
    assert_eq!(trie.get("ab"), Some(&2));
    assert_eq!(trie.get("abc"), Some(&3));
    assert_eq!(trie.get("aby"), Some(&7));

    assert_eq!(trie.get("abcde"), None);
    assert_eq!(trie.get("abcd"), None);
    assert_eq!(trie.get("abx"), None);

    trie.insert("abx", 8);
    assert_eq!(trie.get("abx"), Some(&8));
}

#[test]
fn test_complex_branching_prune() {
    let mut trie = TrieMap::new();

    for i in 0..10 {
        for j in 0..10 {
            let key = format!("branch{}leaf{}", i, j);
            trie.insert(&key, i * 100 + j);
        }
    }

    for j in 0..10 {
        let key = format!("branch5leaf{}", j);
        trie.remove(&key);
    }

    let current_size = trie.len();
    let pruned = trie.prune();
    assert!(pruned > 0);

    assert_eq!(trie.len(), current_size);

    assert_eq!(trie.get("branch1leaf1"), Some(&101));
    assert_eq!(trie.get("branch9leaf9"), Some(&909));

    assert_eq!(trie.get("branch5leaf5"), None);
}

#[test]
fn test_prune_efficiency() {
    let mut trie = TrieMap::new();

    trie.insert("abc", 1);
    trie.insert("abcd", 2);
    trie.insert("abce", 3);

    trie.remove("abcd");

    let first_prune = trie.prune();
    assert!(first_prune > 0);

    let second_prune = trie.prune();
    assert_eq!(second_prune, 0);

    assert_eq!(trie.get("abc"), Some(&1));
    assert_eq!(trie.get("abce"), Some(&3));
}

#[test]
fn test_prune_large_dataset() {
    let mut trie = TrieMap::new();

    for i in 0..1000 {
        let key = format!("key{}", i);
        trie.insert(key, i);
    }

    for i in 0..500 {
        let key = format!("key{}", i);
        trie.remove(&key);
    }

    let start = std::time::Instant::now();
    let pruned = trie.prune();
    let duration = start.elapsed();

    assert!(pruned > 0);
    println!("Pruned {} nodes in {:?}", pruned, duration);

    for i in 500..1000 {
        let key = format!("key{}", i);
        assert_eq!(trie.get(&key), Some(&i));
    }
}

#[test]
fn test_prune_with_non_leaf_removals() {
    let mut trie = TrieMap::new();

    trie.insert("a", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);
    trie.insert("abcd", 4);

    trie.remove("ab");

    let pruned = trie.prune();
    assert_eq!(pruned, 0);

    assert_eq!(trie.get("a"), Some(&1));
    assert_eq!(trie.get("abc"), Some(&3));
    assert_eq!(trie.get("abcd"), Some(&4));

    trie.remove("abc");
    trie.remove("abcd");

    let pruned = trie.prune();
    assert!(pruned > 0);

    assert_eq!(trie.get("a"), Some(&1));
}

#[test]
fn test_entry_api_with_pruning() {
    let mut trie = TrieMap::new();

    trie.insert("key1", 1);
    trie.insert("key2", 2);

    trie.remove("key2");
    trie.prune();

    trie.entry("key1").and_modify(|v| *v += 10);
    trie.entry("key2").or_insert(20);
    trie.entry("key3").or_insert_with(|| 30);

    assert_eq!(trie.get("key1"), Some(&11));
    assert_eq!(trie.get("key2"), Some(&20));
    assert_eq!(trie.get("key3"), Some(&30));
}

#[test]
fn test_remove_all_and_prune() {
    let mut trie = TrieMap::new();

    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    trie.remove("a");
    trie.remove("b");
    trie.remove("c");

    let pruned = trie.prune();
    assert!(pruned > 0, "pruned count is {pruned}");

    assert_eq!(trie.len(), 0);
    assert!(trie.is_empty());

    trie.insert("new", 42);
    assert_eq!(trie.get("new"), Some(&42));
}

#[test]
fn test_remove_insert_prune_cycles() {
    let mut trie = TrieMap::new();

    for cycle in 0..5 {
        for i in 0..10 {
            let key = format!("cycle{}item{}", cycle, i);
            trie.insert(&key, i);
        }

        for i in 0..5 {
            let key = format!("cycle{}item{}", cycle, i);
            trie.remove(&key);
        }

        trie.prune();

        for i in 5..10 {
            let key = format!("cycle{}item{}", cycle, i);
            assert_eq!(trie.get(&key), Some(&i));
        }
    }

    assert_eq!(trie.len(), 5 * 5);
}

#[test]
fn test_remove_with_node_pruning() {
    let mut trie = TrieMap::new();

    trie.insert("abc", 1);
    trie.insert("abd", 2);
    trie.insert("abcde", 3);

    assert_eq!(trie.remove("abcde"), Some(3));

    assert_eq!(trie.get("abc"), Some(&1));
    assert_eq!(trie.get("abd"), Some(&2));

    assert_eq!(trie.get("abc"), Some(&1));

    assert_eq!(trie.remove("abc"), Some(1));

    assert_eq!(trie.get("abd"), Some(&2));

    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);
    trie.insert("abcd", 4);

    assert_eq!(trie.remove("abcd"), Some(4));
    assert_eq!(trie.get("abc"), Some(&3));

    assert_eq!(trie.remove("abc"), Some(3));
    assert_eq!(trie.get("ab"), Some(&2));

    assert_eq!(trie.remove("ab"), Some(2));
    assert_eq!(trie.get("a"), Some(&1));

    assert_eq!(trie.remove("a"), Some(1));
    assert_eq!(trie.len(), 0);
}

#[test]
fn test_cascading_node_pruning() {
    let mut trie = TrieMap::new();

    trie.insert("a", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);
    trie.insert("abcd", 4);
    trie.insert("abcde", 5);

    assert_eq!(trie.remove("abcde"), Some(5));

    assert_eq!(trie.get("abcd"), Some(&4));
    assert_eq!(trie.get("abc"), Some(&3));
    assert_eq!(trie.get("ab"), Some(&2));
    assert_eq!(trie.get("a"), Some(&1));

    assert_eq!(trie.remove("abcd"), Some(4));
    assert_eq!(trie.get("abc"), Some(&3));

    assert_eq!(trie.remove("abc"), Some(3));
    assert_eq!(trie.get("ab"), Some(&2));

    assert_eq!(trie.remove("ab"), Some(2));
    assert_eq!(trie.get("a"), Some(&1));

    assert_eq!(trie.remove("a"), Some(1));
    assert_eq!(trie.len(), 0);

    let mut trie = TrieMap::new();
    trie.insert("abc", 1);
    trie.insert("abd", 2);
    trie.insert("abe", 3);

    assert_eq!(trie.remove("abe"), Some(3));
    assert_eq!(trie.len(), 2);

    assert_eq!(trie.remove("abd"), Some(2));
    assert_eq!(trie.len(), 1);

    assert_eq!(trie.remove("abc"), Some(1));
    assert_eq!(trie.len(), 0);
}

#[test]
fn test_complex_pruning_with_branches() {
    let mut trie = TrieMap::new();

    trie.insert("a", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);
    trie.insert("abd", 4);
    trie.insert("abx", 5);
    trie.insert("ac", 6);
    trie.insert("acd", 7);

    assert_eq!(trie.remove("abd"), Some(4));

    assert_eq!(trie.get("abc"), Some(&3));
    assert_eq!(trie.get("abx"), Some(&5));

    assert_eq!(trie.remove("abc"), Some(3));

    assert_eq!(trie.get("abx"), Some(&5));

    assert_eq!(trie.remove("abx"), Some(5));

    assert_eq!(trie.get("ab"), Some(&2));

    assert_eq!(trie.get("ac"), Some(&6));
    assert_eq!(trie.get("acd"), Some(&7));

    assert_eq!(trie.remove("ab"), Some(2));

    assert_eq!(trie.get("ac"), Some(&6));
    assert_eq!(trie.get("acd"), Some(&7));

    assert_eq!(trie.remove("acd"), Some(7));
    assert_eq!(trie.get("ac"), Some(&6));

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
    trie2.insert("c", 30);
    trie2.insert("d", 4);
    trie2.insert("e", 5);

    let union_results: Vec<(Vec<u8>, &i32)> = trie1.union(&trie2).collect();

    let mut sorted_results = union_results.clone();
    sorted_results.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    assert_eq!(sorted_results.len(), 5);

    let result_map: HashMap<String, i32> = sorted_results
        .into_iter()
        .map(|(k, &v)| (String::from_utf8(k).unwrap(), v))
        .collect();

    assert_eq!(result_map.get("a"), Some(&1));
    assert_eq!(result_map.get("b"), Some(&2));
    assert_eq!(result_map.get("c"), Some(&3));
    assert_eq!(result_map.get("d"), Some(&4));
    assert_eq!(result_map.get("e"), Some(&5));

    assert_eq!(trie1.len(), 3);
    assert_eq!(trie2.len(), 3);
}

#[test]
fn test_union_empty_maps() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);

    let empty_trie: TrieMap<i32> = TrieMap::new();

    let union1: Vec<_> = trie1.union(&empty_trie).collect();
    assert_eq!(union1.len(), 1);
    assert_eq!(String::from_utf8(union1[0].0.clone()).unwrap(), "a");
    assert_eq!(*union1[0].1, 1);

    let union2: Vec<_> = empty_trie.union(&trie1).collect();
    assert_eq!(union2.len(), 1);
    assert_eq!(String::from_utf8(union2[0].0.clone()).unwrap(), "a");
    assert_eq!(*union2[0].1, 1);

    let empty_trie2: TrieMap<i32> = TrieMap::new();
    let union3: Vec<_> = empty_trie.union(&empty_trie2).collect();
    assert_eq!(union3.len(), 0);
}

#[test]
fn test_entry_empty_key() {
    let mut trie = TrieMap::new();

    let empty_str = "";
    {
        let entry = trie.entry(empty_str);
        entry.or_insert(42);
    }

    assert_eq!(trie.get(empty_str), Some(&42));
    assert_eq!(trie.len(), 1);

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

    {
        let key = "default_key";
        let value_ref = trie.entry(key).or_default();
        assert_eq!(*value_ref, 0);
        *value_ref = 100;
    }

    assert_eq!(trie.get("default_key"), Some(&100));

    {
        let key = "key_length";
        let value_ref = trie.entry(key).or_insert_with_key(|key| key.len() as i32);
        assert_eq!(*value_ref, 10);
    }

    assert_eq!(trie.get("key_length"), Some(&10));
}

#[test]
fn test_occupied_entry_methods() {
    let mut trie = TrieMap::new();
    trie.insert("key1", 10);

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

    let mut new_empty_trie: TrieMap<String> = TrieMap::new();

    let value = new_empty_trie
        .entry("chain")
        .or_insert_with(|| String::from("initial"));

    assert_eq!(value, "initial");

    let mut default_trie: TrieMap<Vec<i32>> = TrieMap::new();
    let vec_ref = default_trie.entry("default").or_default();
    assert!(vec_ref.is_empty());

    vec_ref.push(1);
    vec_ref.push(2);

    assert_eq!(default_trie.get("default"), Some(&vec![1, 2]));

    let mut multi_entry_trie: TrieMap<i32> = TrieMap::new();

    multi_entry_trie.entry("a").or_insert(1);
    multi_entry_trie.entry("b").or_insert(2);
    multi_entry_trie.entry("c").or_insert(3);

    assert_eq!(multi_entry_trie.len(), 3);

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

#[test]
fn test_intersection() {
    let mut trie1 = TrieMap::new();
    trie1.insert("a", 1);
    trie1.insert("b", 2);
    trie1.insert("c", 3);

    let mut trie2 = TrieMap::new();
    trie2.insert("b", 20);
    trie2.insert("c", 30);
    trie2.insert("d", 40);

    let intersection: Vec<_> = trie1.intersect(&trie2).collect();

    assert_eq!(intersection.len(), 2);

    let mut sorted_intersection = intersection.clone();
    sorted_intersection.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    assert_eq!(
        String::from_utf8(sorted_intersection[0].0.clone()).unwrap(),
        "b"
    );
    assert_eq!(*sorted_intersection[0].1, 2);

    assert_eq!(
        String::from_utf8(sorted_intersection[1].0.clone()).unwrap(),
        "c"
    );
    assert_eq!(*sorted_intersection[1].1, 3);

    let empty_trie: TrieMap<i32> = TrieMap::new();
    let empty_intersection: Vec<_> = trie1.intersect(&empty_trie).collect();
    assert_eq!(empty_intersection.len(), 0);

    let self_intersection: Vec<_> = trie1.intersect(&trie1).collect();
    assert_eq!(self_intersection.len(), 3);
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

    let difference: Vec<_> = trie1.difference(&trie2).collect();

    assert_eq!(difference.len(), 1);
    assert_eq!(String::from_utf8(difference[0].0.clone()).unwrap(), "a");
    assert_eq!(*difference[0].1, 1);

    let reverse_difference: Vec<_> = trie2.difference(&trie1).collect();

    assert_eq!(reverse_difference.len(), 1);
    assert_eq!(
        String::from_utf8(reverse_difference[0].0.clone()).unwrap(),
        "d"
    );
    assert_eq!(*reverse_difference[0].1, 40);

    let empty_trie: TrieMap<i32> = TrieMap::new();
    let diff_with_empty: Vec<_> = trie1.difference(&empty_trie).collect();
    assert_eq!(diff_with_empty.len(), 3);

    let self_diff: Vec<_> = trie1.difference(&trie1).collect();
    assert_eq!(self_diff.len(), 0);
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

    let sym_diff: Vec<_> = trie1.symmetric_difference(&trie2).collect();

    assert_eq!(sym_diff.len(), 2);

    let mut sorted_sym_diff = sym_diff.clone();
    sorted_sym_diff.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

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

    let empty_trie: TrieMap<i32> = TrieMap::new();
    let sym_diff_with_empty: Vec<_> = trie1.symmetric_difference(&empty_trie).collect();
    assert_eq!(sym_diff_with_empty.len(), 3);

    let self_sym_diff: Vec<_> = trie1.symmetric_difference(&trie1).collect();
    assert_eq!(self_sym_diff.len(), 0);
}

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

    let union_then_intersect: Vec<_> = trie1
        .union(&trie2)
        .filter(|(key, _)| trie3.contains_key(key))
        .collect();

    assert_eq!(union_then_intersect.len(), 1);
    assert_eq!(
        String::from_utf8(union_then_intersect[0].0.clone()).unwrap(),
        "c"
    );
    assert_eq!(*union_then_intersect[0].1, 30);

    let key_difference: Vec<String> = trie1
        .difference(&trie2)
        .map(|(key, _)| String::from_utf8(key).unwrap())
        .collect();

    assert_eq!(key_difference, vec!["a".to_string()]);

    let complex_operation: Vec<_> = trie1.difference(&trie2).chain(trie3.iter()).collect();

    assert_eq!(complex_operation.len(), 3);

    let mut sorted_complex = complex_operation.clone();
    sorted_complex.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    assert_eq!(String::from_utf8(sorted_complex[0].0.clone()).unwrap(), "a");
    assert_eq!(*sorted_complex[0].1, 1);

    assert_eq!(String::from_utf8(sorted_complex[1].0.clone()).unwrap(), "c");
    assert_eq!(*sorted_complex[1].1, 300);

    assert_eq!(String::from_utf8(sorted_complex[2].0.clone()).unwrap(), "d");
    assert_eq!(*sorted_complex[2].1, 400);
}

#[test]
fn test_as_bytes_implementations() {
    let s = "hello";
    assert_eq!(s.as_bytes(), b"hello");

    let string = String::from("hello");
    assert_eq!(string.as_bytes(), b"hello");

    let s_ref: &str = "hello";
    assert_eq!(s_ref.as_bytes(), b"hello");

    let string_ref: &String = &string;
    assert_eq!(string_ref.as_bytes(), b"hello");

    let bytes = b"hello".as_slice();
    assert_eq!(bytes.as_bytes(), b"hello");

    let vec_bytes = b"hello".to_vec();
    assert_eq!(vec_bytes.as_bytes(), b"hello");

    let bytes_ref: &[u8] = b"hello";
    assert_eq!(bytes_ref.as_bytes(), b"hello");

    let array_bytes: [u8; 5] = *b"hello";
    assert_eq!(array_bytes.as_bytes(), b"hello");

    assert_eq!(s.as_bytes_vec(), b"hello".to_vec());
    assert_eq!(string.as_bytes_vec(), b"hello".to_vec());
    assert_eq!(bytes.as_bytes_vec(), b"hello".to_vec());
    assert_eq!(vec_bytes.as_bytes_vec(), b"hello".to_vec());
}

#[test]
fn test_as_bytes_in_trie_operations() {
    let mut trie = TrieMap::new();

    trie.insert("string_key", 1);
    trie.insert(String::from("owned_key"), 2);
    trie.insert(b"byte_key".as_ref(), 3);
    trie.insert(b"vec_key".to_vec(), 4);

    let static_array: [u8; 10] = *b"array_key\0";
    trie.insert(static_array, 5);

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

    let mut iter = map.prefix_iter("app").collect::<Vec<_>>();
    iter.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

    assert_eq!(iter.len(), 3);
    assert_eq!(String::from_utf8(iter[0].0.clone()).unwrap(), "app");
    assert_eq!(*iter[0].1, 4);
    assert_eq!(String::from_utf8(iter[1].0.clone()).unwrap(), "apple");
    assert_eq!(*iter[1].1, 1);
    assert_eq!(String::from_utf8(iter[2].0.clone()).unwrap(), "application");
    assert_eq!(*iter[2].1, 2);

    let mut keys = map.prefix_keys("app").collect::<Vec<_>>();
    keys.sort();

    assert_eq!(keys.len(), 3);
    assert_eq!(String::from_utf8(keys[0].clone()).unwrap(), "app");
    assert_eq!(String::from_utf8(keys[1].clone()).unwrap(), "apple");
    assert_eq!(String::from_utf8(keys[2].clone()).unwrap(), "application");

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
        .map(|k| String::from_utf8(k.into()).unwrap())
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
        assert!(!called.get());
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
        assert!(!called.get());
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

#[test]
fn test_basic_remove_and_prune() {
    let mut trie = TrieMap::new();
    trie.insert("abc", 1);
    trie.insert("abcd", 2);
    trie.insert("abce", 3);

    assert_eq!(trie.len(), 3);
    assert_eq!(trie.get("abc"), Some(&1));
    assert_eq!(trie.get("abcd"), Some(&2));
    assert_eq!(trie.get("abce"), Some(&3));

    let removed = trie.remove_and_prune("abcd");
    assert_eq!(removed, Some(2));

    assert_eq!(trie.len(), 2);
    assert_eq!(trie.get("abc"), Some(&1));
    assert_eq!(trie.get("abcd"), None);
    assert_eq!(trie.get("abce"), Some(&3));
}

#[test]
fn test_remove_and_prune_exclusive_path() {
    let mut trie = TrieMap::new();

    trie.insert("common", 1);
    trie.insert("common_branch1", 2);
    trie.insert("common_branch2", 3);
    trie.insert("exclusive", 4);

    let removed = trie.remove_and_prune("exclusive");
    assert_eq!(removed, Some(4));

    assert_eq!(trie.get("exclusive"), None);

    assert_eq!(trie.get("common"), Some(&1));
    assert_eq!(trie.get("common_branch1"), Some(&2));
    assert_eq!(trie.get("common_branch2"), Some(&3));
}

#[test]
fn test_remove_and_prune_leaf_nodes() {
    let mut trie = TrieMap::new();

    trie.insert("a", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);
    trie.insert("abcd", 4);

    let removed = trie.remove_and_prune("abcd");
    assert_eq!(removed, Some(4));

    assert_eq!(trie.get("abcd"), None);
    assert_eq!(trie.get("abc"), Some(&3));
    assert_eq!(trie.get("ab"), Some(&2));
    assert_eq!(trie.get("a"), Some(&1));

    let removed = trie.remove_and_prune("abc");
    assert_eq!(removed, Some(3));

    assert_eq!(trie.get("abc"), None);

    assert_eq!(trie.get("ab"), Some(&2));
    assert_eq!(trie.get("a"), Some(&1));
}

#[test]
fn test_remove_and_prune_internal_nodes() {
    let mut trie = TrieMap::new();

    trie.insert("parent", 1);
    trie.insert("parent_child", 2);

    let removed = trie.remove_and_prune("parent");
    assert_eq!(removed, Some(1));

    assert_eq!(trie.get("parent"), None);

    assert_eq!(trie.get("parent_child"), Some(&2));
}

#[test]
fn test_remove_and_prune_forked_paths() {
    let mut trie = TrieMap::new();

    trie.insert("fork", 1);
    trie.insert("fork_a", 2);
    trie.insert("fork_b", 3);

    let removed = trie.remove_and_prune("fork_a");
    assert_eq!(removed, Some(2));

    assert_eq!(trie.get("fork_a"), None);

    assert_eq!(trie.get("fork"), Some(&1));
    assert_eq!(trie.get("fork_b"), Some(&3));

    let removed = trie.remove_and_prune("fork");
    assert_eq!(removed, Some(1));

    assert_eq!(trie.get("fork"), None);

    assert_eq!(trie.get("fork_b"), Some(&3));
}

#[test]
fn test_remove_and_prune_alternating() {
    let mut trie = TrieMap::new();

    trie.insert("path1", 1);
    trie.insert("path2", 2);
    trie.insert("path3", 3);

    let removed = trie.remove_and_prune("path2");
    assert_eq!(removed, Some(2));

    assert_eq!(trie.get("path2"), None);

    assert_eq!(trie.get("path1"), Some(&1));
    assert_eq!(trie.get("path3"), Some(&3));

    let removed = trie.remove_and_prune("path1");
    assert_eq!(removed, Some(1));

    assert_eq!(trie.get("path1"), None);

    assert_eq!(trie.get("path3"), Some(&3));
}

#[test]
fn test_remove_and_prune_nonexistent() {
    let mut trie = TrieMap::new();

    trie.insert("existing", 1);

    let removed = trie.remove_and_prune("nonexistent");
    assert_eq!(removed, None);

    let removed = trie.remove_and_prune("existi");
    assert_eq!(removed, None);

    let removed = trie.remove_and_prune("existingplus");
    assert_eq!(removed, None);

    assert_eq!(trie.len(), 1);
    assert_eq!(trie.get("existing"), Some(&1));
}

#[test]
fn test_remove_and_prune_binary_keys() {
    let mut trie = TrieMap::new();

    let common_prefix = vec![1, 2, 3];
    let key1 = vec![1, 2, 3, 4];
    let key2 = vec![1, 2, 3, 5];
    let unrelated = vec![5, 6, 7];

    trie.insert(&common_prefix, 1);
    trie.insert(&key1, 2);
    trie.insert(&key2, 3);
    trie.insert(&unrelated, 4);

    let removed = trie.remove_and_prune(&key1);
    assert_eq!(removed, Some(2));

    assert_eq!(trie.get(&key1), None);

    assert_eq!(trie.get(&common_prefix), Some(&1));
    assert_eq!(trie.get(&key2), Some(&3));
    assert_eq!(trie.get(&unrelated), Some(&4));
}

#[test]
fn test_remove_and_prune_empty_key() {
    let mut trie = TrieMap::new();

    trie.insert("", 1);
    trie.insert("normal", 2);

    let removed = trie.remove_and_prune("");
    assert_eq!(removed, Some(1));

    assert_eq!(trie.get(""), None);

    assert_eq!(trie.get("normal"), Some(&2));
}

#[test]
fn test_remove_and_prune_all() {
    let mut trie = TrieMap::new();

    trie.insert("key1", 1);
    trie.insert("key2", 2);
    trie.insert("key3", 3);

    let removed = trie.remove_and_prune("key1");
    assert_eq!(removed, Some(1));
    assert_eq!(trie.len(), 2);

    let removed = trie.remove_and_prune("key2");
    assert_eq!(removed, Some(2));
    assert_eq!(trie.len(), 1);

    let removed = trie.remove_and_prune("key3");
    assert_eq!(removed, Some(3));

    assert_eq!(trie.len(), 0);
    assert!(trie.is_empty());
}

#[test]
fn test_remove_and_prune_deep_exclusive_path() {
    let mut trie = TrieMap::new();

    let deep_key = "a".repeat(100);
    trie.insert(&deep_key, 1);
    trie.insert("other", 2);

    let removed = trie.remove_and_prune(&deep_key);
    assert_eq!(removed, Some(1));

    assert_eq!(trie.get(&deep_key), None);

    assert_eq!(trie.get("other"), Some(&2));
}

use proptest::prelude::*;
use std::collections::HashSet;

// Helper strategies
fn keys_strategy() -> impl Strategy<Value = Vec<String>> {
    // Use hash_set to ensure unique keys
    prop::collection::hash_set("[a-zA-Z0-9]{1,20}".prop_map(String::from), 1..100)
        .prop_map(|set| set.into_iter().collect())
}

fn key_value_pairs_strategy() -> impl Strategy<Value = Vec<(String, i32)>> {
    // First generate unique keys
    prop::collection::hash_set("[a-zA-Z0-9]{1,20}".prop_map(String::from), 1..100).prop_flat_map(
        |keys| {
            // Then pair them with values
            prop::collection::vec(proptest::num::i32::ANY, keys.len())
                .prop_map(move |values| keys.iter().cloned().zip(values.into_iter()).collect())
        },
    )
}

proptest! {

    #[test]
    fn prop_iter_properties(pairs in key_value_pairs_strategy()) {
        let mut trie = TrieMap::new();
        let mut reference = HashMap::new();


        for (key, value) in &pairs {
            trie.insert(key, *value);
            reference.insert(key.clone(), *value);
        }


        let items: Vec<(Vec<u8>, &i32)> = trie.iter().collect();


        prop_assert_eq!(items.len(), reference.len());


        for (key, value) in &items {
            let key_str = String::from_utf8(key.clone()).unwrap();
            prop_assert_eq!(reference.get(&key_str), Some(*value));
        }


        let keys: HashSet<Vec<u8>> = trie.keys().map(|x| x.into()).collect();
        prop_assert_eq!(keys.len(), reference.len());

        for key_bytes in &keys {
            let key_str = String::from_utf8(key_bytes.clone()).unwrap();
            prop_assert!(reference.contains_key(&key_str));
        }


        let mut values: Vec<&i32> = trie.values().collect();
        let mut ref_values: Vec<&i32> = reference.values().collect();

        values.sort();
        ref_values.sort();
        prop_assert_eq!(values, ref_values);
    }




    #[test]
    fn prop_drain_iterator(pairs in key_value_pairs_strategy()) {
        let mut trie = TrieMap::new();
        let mut reference_map = HashMap::new();


        for (key, value) in &pairs {
            trie.insert(key, *value);
            reference_map.insert(key.clone(), *value);
        }


        let drained_items: Vec<(Vec<u8>, i32)> = trie.drain().collect();


        prop_assert_eq!(drained_items.len(), reference_map.len());


        for (key, value) in &drained_items {
            let key_str = String::from_utf8(key.clone()).unwrap();
            prop_assert_eq!(reference_map.get(&key_str).copied(), Some(*value));
        }


        prop_assert_eq!(trie.len(), 0);
        prop_assert!(trie.is_empty());
    }


    #[test]
    fn prop_into_iter(pairs in key_value_pairs_strategy()) {
        let mut trie = TrieMap::new();
        let mut reference_map = HashMap::new();


        for (key, value) in &pairs {
            trie.insert(key, *value);
            reference_map.insert(key.clone(), *value);
        }


        prop_assert_eq!(trie.len(), reference_map.len());


        let items: Vec<(Vec<u8>, i32)> = trie.into_iter().collect();


        prop_assert_eq!(items.len(), reference_map.len());


        for (key, value) in &items {
            let key_str = String::from_utf8(key.clone()).unwrap();
            prop_assert_eq!(reference_map.get(&key_str).copied(), Some(*value));
        }


        let unique_keys: HashSet<Vec<u8>> = items.iter().map(|(k, _)| k.clone()).collect();
        prop_assert_eq!(unique_keys.len(), items.len());
    }


}

#[test]
fn test_entry_or_insert_none_value() {
    // Test inserting None where a node exists but has no value
    let mut trie = TrieMap::new();

    // Create a path without inserting a value
    let key_bytes = "test_key".as_bytes().to_vec();
    let mut current_id = trie.root;
    for &byte in &key_bytes {
        current_id = trie.pool.add_child(current_id, byte);
    }

    // Verify the path exists but has no value
    let mut found = true;
    let mut path_id = trie.root;
    for &byte in &key_bytes {
        let node = trie.pool.get_node(path_id);
        if !test_bit(&node.is_present, byte) {
            found = false;
            break;
        }
        path_id = trie.pool.get_child_idx_unchecked(path_id, byte);
    }

    assert!(found, "Path should exist");
    let node = trie.pool.get_node(path_id);
    assert!(node.data_idx.is_none(), "Node should have no data index");

    // Now use entry API to insert a value
    let value = trie.entry("test_key").or_insert(42);
    assert_eq!(*value, 42);

    // Verify it was inserted correctly
    assert_eq!(trie.get("test_key"), Some(&42));
    assert_eq!(trie.len(), 1);
}

#[test]
fn test_entry_or_default_edge_cases() {
    let mut trie = TrieMap::<Option<i32>>::new();

    // Test with empty string key
    let empty_key = "";
    let value = trie.entry(empty_key).or_default();
    assert_eq!(*value, None);

    // Test with already present None value
    let value = trie.entry(empty_key).or_default();
    assert_eq!(*value, None);

    // Modify the value
    *value = Some(42);

    // Test again to ensure it doesn't reset
    let value = trie.entry(empty_key).or_default();
    assert_eq!(*value, Some(42));
}

#[test]
fn test_entry_or_insert_with_callback_arguments() {
    let mut trie = TrieMap::new();

    // Create a stateful callback
    struct Counter {
        count: i32,
    }

    impl Counter {
        fn new() -> Self {
            Counter { count: 0 }
        }

        fn next(&mut self) -> i32 {
            self.count += 1;
            self.count
        }
    }

    let mut counter = Counter::new();

    // Test or_insert_with
    for _ in 0..5 {
        let key = "counter_key";
        let value = trie.entry(key).or_insert_with(|| counter.next());

        // If this is the first insertion, value should be 1
        // For subsequent iterations, it should remain 1
        assert_eq!(*value, 1);
    }

    // Counter should have been called exactly once despite 5 entry operations
    assert_eq!(counter.count, 1);

    // Test or_insert_with_key
    let mut trie = TrieMap::new();
    let mut lengths = HashMap::new();

    for key in ["a", "ab", "abc", "abcd", "abcde"] {
        let value = trie.entry(key).or_insert_with_key(|k| {
            let len = k.len();
            lengths.insert(len, true);
            len as i32
        });

        // Value should match the key length
        assert_eq!(*value, key.len() as i32);
    }

    // Each length callback should have been called exactly once
    assert_eq!(lengths.len(), 5);

    // Calling again for an existing key should not call the callback
    let called = std::cell::Cell::new(false);
    let value = trie.entry("abc").or_insert_with_key(|_| {
        called.set(true);
        100 // Different value
    });

    // Value should not change
    assert_eq!(*value, 3);
    // Callback should not be called
    assert!(!called.get());
}

#[test]
fn test_entry_manual_constructions() {
    let mut trie = TrieMap::new();
    trie.insert("key", 42);

    // Manually create a VacantEntry
    let vacant = VacantEntry {
        trie: &mut trie,
        key: "new_key".as_bytes().to_vec(),
    };

    // Test insert
    let value_ref = vacant.insert(100);
    assert_eq!(*value_ref, 100);
    assert_eq!(trie.get("new_key"), Some(&100));

    // Manually create an OccupiedEntry
    let data_idx = {
        let mut current_id = trie.root;
        for &byte in "key".as_bytes() {
            current_id = trie.pool.get_child_idx_unchecked(current_id, byte);
        }
        let node = trie.pool.get_node(current_id);
        node.data_idx.unwrap()
    };

    {
        let mut occupied = OccupiedEntry {
            trie: &mut trie,
            key: "key".as_bytes().to_vec(),
            data_idx,
        };

        // Test methods
        assert_eq!(occupied.get(), &42);
        *occupied.get_mut() = 200;
    }
    assert_eq!(trie.get("key"), Some(&200));
}

#[test]
fn test_entry_interface_with_zero_sized_types() {
    // Test with unit type ()
    let mut trie = TrieMap::<()>::new();

    // Test or_insert
    trie.entry("key1").or_insert(());
    assert!(trie.contains_key("key1"));

    // Test or_default
    trie.entry("key2").or_default();
    assert!(trie.contains_key("key2"));

    // Test or_insert_with
    trie.entry("key3").or_insert_with(|| ());
    assert!(trie.contains_key("key3"));

    // Test or_insert_with_key
    trie.entry("key4").or_insert_with_key(|_| ());
    assert!(trie.contains_key("key4"));

    // Test and_modify
    trie.entry("key1").and_modify(|_| {}).or_insert(());
    assert!(trie.contains_key("key1"));

    assert_eq!(trie.len(), 4);
}

#[test]
fn test_entry_complex_modifications() {
    let mut trie = TrieMap::<Vec<i32>>::new();

    // Test inserting and modifying complex values
    let key = "complex";

    // Insert initial value
    trie.entry(key).or_insert(vec![1, 2, 3]);

    // Modify through entry API
    match trie.entry(key) {
        Entry::Occupied(mut occupied) => {
            // Get mutable reference and push a value
            occupied.get_mut().push(4);

            // Verify change
            assert_eq!(occupied.get(), &vec![1, 2, 3, 4]);
        }
        _ => panic!("Entry should be occupied"),
    }

    // Chain multiple operations
    trie.entry(key)
        .and_modify(|v| v.push(5))
        .and_modify(|v| v.push(6))
        .or_insert(vec![]);

    // Verify final state
    assert_eq!(trie.get(key), Some(&vec![1, 2, 3, 4, 5, 6]));

    // Remove via entry
    if let Entry::Occupied(occupied) = trie.entry(key) {
        let removed = occupied.remove();
        assert_eq!(removed, vec![1, 2, 3, 4, 5, 6]);
    }

    // Verify removal
    assert!(!trie.contains_key(key));
}

#[test]
fn test_occupied_entry_with_none_value() {
    let mut trie = TrieMap::<Option<i32>>::new();

    // Insert None value
    trie.insert("key", None);

    // Verify entry
    if let Entry::Occupied(mut occupied) = trie.entry("key") {
        assert_eq!(occupied.get(), &None);

        // Update to Some
        *occupied.get_mut() = Some(42);

        // Verify update
        assert_eq!(occupied.get(), &Some(42));
    } else {
        panic!("Entry should be occupied");
    }

    // Verify final state
    assert_eq!(trie.get("key"), Some(&Some(42)));
}

// ----------------------------
// Additional Iterator Tests
// ----------------------------

#[test]
fn test_iter_borrowing_semantics() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);

    // Test that Iter borrows the trie immutably
    let iter = trie.iter();

    // We should still be able to use get since iter only borrows immutably
    assert_eq!(trie.get("a"), Some(&1));

    // Consume the iterator
    let _: Vec<_> = iter.collect();

    // Now test with multiple iterators simultaneously
    let iter1 = trie.iter();
    let iter2 = trie.iter();

    // Both should work independently
    assert_eq!(iter1.count(), 2);
    assert_eq!(iter2.count(), 2);
}

#[test]
fn test_keys_iterator_exhaustively() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    // Get keys iterator
    let mut keys_iter = trie.keys();

    // Collect all keys manually
    let mut keys = Vec::new();
    while let Some(key) = keys_iter.next() {
        keys.push(key);
    }

    // Verify count
    assert_eq!(keys.len(), 3);

    // Verify content
    let key_strs: Vec<String> = keys
        .iter()
        .map(|k| String::from_utf8(k.clone().into()).unwrap())
        .collect();

    assert!(key_strs.contains(&"a".to_string()));
    assert!(key_strs.contains(&"b".to_string()));
    assert!(key_strs.contains(&"c".to_string()));

    // Verify size_hint
    let keys_iter = trie.keys();
    let (min, max) = keys_iter.size_hint();
    assert!(min <= 3);
}

#[test]
fn test_nested_iterators() {
    let mut trie = TrieMap::<i32>::new();
    trie.insert("abc", 1);
    trie.insert("abd", 2);
    trie.insert("abe", 3);

    // Group by the second character
    let mut result: BTreeMap<String, Vec<i32>> = BTreeMap::new();

    for (key, value) in trie.iter() {
        if key.len() >= 2 {
            let group_key = String::from_utf8(key[0..2].to_vec()).unwrap();
            result.entry(group_key).or_default().push(*value);
        }
    }

    // Verify grouping
    assert_eq!(result.len(), 1);
    let values = result.get("ab").unwrap();
    assert_eq!(values.len(), 3);
    assert!(values.contains(&1));
    assert!(values.contains(&2));
    assert!(values.contains(&3));
}

#[test]
fn test_nonexistent_prefix() {
    let mut trie = TrieMap::new();
    trie.insert("apple", 1);
    trie.insert("banana", 2);

    // Test with a prefix that doesn't exist
    let mut prefix_iter = trie.prefix_iter("orange");
    assert_eq!(prefix_iter.next(), None);

    // Test prefix_keys
    let prefix_keys = trie.prefix_keys("orange");
    assert_eq!(prefix_keys.count(), 0);

    // Test prefix_values
    let prefix_values = trie.prefix_values("orange");
    assert_eq!(prefix_values.count(), 0);

    // Test with a prefix that's longer than any key
    let long_prefix = "apple_tree";
    assert_eq!(trie.prefix_iter(long_prefix).count(), 0);
    assert_eq!(trie.prefix_keys(long_prefix).count(), 0);
    assert_eq!(trie.prefix_values(long_prefix).count(), 0);
}

#[test]
fn test_iter_with_data_idx_out_of_bounds() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);

    // Create a node with a data_idx that's out of bounds
    let key_bytes = "invalid".as_bytes().to_vec();
    let mut current_id = trie.root;
    for &byte in &key_bytes {
        let has_child = {
            let current_node = trie.pool.get_node(current_id);
            test_bit(&current_node.is_present, byte)
        };

        if !has_child {
            current_id = trie.pool.add_child(current_id, byte);
        } else {
            current_id = trie.pool.get_child_idx_unchecked(current_id, byte);
        }
    }

    // Set an out-of-bounds data index
    {
        let node = trie.pool.get_node_mut(current_id);
        node.data_idx = Some(usize::MAX); // This is out of bounds
    }

    // Iteration should still work and skip the invalid node
    let items: Vec<_> = trie.iter().collect();
    assert_eq!(items.len(), 1); // Only the valid entry
    assert_eq!(items[0].0, b"a");
    assert_eq!(*items[0].1, 1);
}

#[test]
#[test]
fn test_into_iter_edge_cases_again() {
    // Test with empty trie
    let empty_trie: TrieMap<i32> = TrieMap::new();
    let empty_iter = empty_trie.into_iter();
    assert_eq!(empty_iter.count(), 0);

    // Test with invalid data indices
    let mut trie = TrieMap::new();
    trie.insert("a", 1);

    // Create another key with invalid data
    let key_bytes = "invalid".as_bytes().to_vec();
    let mut current_id = trie.root;
    for &byte in &key_bytes {
        let has_child = {
            let current_node = trie.pool.get_node(current_id);
            test_bit(&current_node.is_present, byte)
        };

        if !has_child {
            current_id = trie.pool.add_child(current_id, byte);
        } else {
            current_id = trie.pool.get_child_idx_unchecked(current_id, byte);
        }
    }

    // Set an invalid data index (beyond the Vec bounds)
    {
        let node = trie.pool.get_node_mut(current_id);
        node.data_idx = Some(trie.data.len() + 100); // This is out of bounds
    }

    // IntoIter should skip the invalid entry
    let items: Vec<_> = trie.into_iter().collect();
    assert_eq!(items.len(), 1); // Only the valid entry
}

#[test]
fn test_drain_iter_with_deep_paths() {
    let mut trie = TrieMap::new();

    // Insert items with varying path lengths
    trie.insert("a", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);
    trie.insert("abcd", 4);
    trie.insert("abcde", 5);

    // Drain and verify all items are included
    let drained: Vec<_> = trie.drain().collect();
    assert_eq!(drained.len(), 5);

    // Sort by key length to verify all depths are included
    let mut by_length: HashMap<usize, Vec<(Vec<u8>, i32)>> = HashMap::new();
    for (key, value) in drained {
        by_length.entry(key.len()).or_default().push((key, value));
    }

    // Verify all depths
    for i in 1..=5 {
        assert!(by_length.contains_key(&i));
        assert_eq!(by_length[&i].len(), 1);
    }

    // Trie should be empty
    assert_eq!(trie.len(), 0);
}

#[test]
fn test_specialized_iterators_size_hint() {
    let mut trie = TrieMap::new();

    // Insert test data
    for i in 0..10 {
        trie.insert(format!("key{}", i), i);
    }

    // Test Keys size_hint
    let keys_iter = Keys { inner: trie.iter() };
    let (min, max) = keys_iter.size_hint();
    assert!(min <= trie.len());

    // Test Values size_hint
    let values_iter = Values { inner: trie.iter() };
    let (min, max) = values_iter.size_hint();
    assert!(min <= trie.len());

    // Test PrefixKeys size_hint
    let prefix_iter = trie.prefix_iter("key");
    let prefix_keys_iter = PrefixKeys { inner: prefix_iter };
    let (min, max) = prefix_keys_iter.size_hint();
    assert_eq!(min, 0); // Conservative estimate
    assert!(max.unwrap() >= trie.len());

    // Test PrefixValues size_hint
    let prefix_iter = trie.prefix_iter("key");
    let prefix_values_iter = PrefixValues { inner: prefix_iter };
    let (min, max) = prefix_values_iter.size_hint();
    assert_eq!(min, 0); // Conservative estimate
    assert!(max.unwrap() >= trie.len());
}

#[test]
fn test_empty_prefix_matches_all() {
    let mut trie = TrieMap::new();
    trie.insert("a", 1);
    trie.insert("b", 2);
    trie.insert("c", 3);

    // Empty prefix should match everything
    let prefix_iter = trie.prefix_iter("");
    assert_eq!(prefix_iter.count(), 3);

    let prefix_keys = trie.prefix_keys("");
    assert_eq!(prefix_keys.count(), 3);

    let prefix_values = trie.prefix_values("");
    assert_eq!(prefix_values.count(), 3);
}
