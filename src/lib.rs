use std::hash::DefaultHasher;
use std::iter::FromIterator;

use std::borrow::Borrow;
use std::hash::{Hash, Hasher};

impl<T, K: AsBytes, V: Into<T>, const N: usize> From<[(K, V); N]> for TrieMap<T> {
    fn from(array: [(K, V); N]) -> Self {
        let mut trie = TrieMap::with_capacity(N);
        for (key, value) in array {
            trie.insert(key, value.into());
        }
        trie
    }
}

impl<T, K: AsBytes, V: Into<T>> From<&[(K, V)]> for TrieMap<T>
where
    K: Clone,
    V: Clone,
{
    fn from(slice: &[(K, V)]) -> Self {
        let mut trie = TrieMap::with_capacity(slice.len());
        for (key, value) in slice {
            let value_owned: V = value.clone();
            trie.insert(key.clone(), value_owned.into());
        }
        trie
    }
}

impl<T: Hash> Hash for TrieMap<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.size.hash(state);

        let mut entries: Vec<_> = self.iter().collect();
        entries.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

        for (key, value) in entries {
            key.hash(state);
            value.hash(state);
        }
    }
}
impl<T: Clone> Clone for TrieMap<T> {
    fn clone(&self) -> Self {
        TrieMap {
            data: self.data.clone(),
            free_indices: self.free_indices.clone(),
            root: self.root.clone(),
            size: self.size,
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for TrieMap<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut map_debug = f.debug_map();

        for (key, value) in self.iter() {
            let key_display = match std::str::from_utf8(&key) {
                Ok(s) => format!("{}", s),
                Err(_) => format!("{:?}", key),
            };

            map_debug.entry(&key_display, value);
        }

        map_debug.finish()
    }
}

impl<T: PartialEq> PartialEq for TrieMap<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.size != other.size {
            return false;
        }

        let mut self_pairs: Vec<_> = self.iter().collect();
        let mut other_pairs: Vec<_> = other.iter().collect();

        self_pairs.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
        other_pairs.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

        self_pairs == other_pairs
    }
}

impl<T: Eq> Eq for TrieMap<T> {}

pub struct IntoIter<T> {
    pairs: Vec<(Vec<u8>, T)>,
    position: usize,
}

impl<T> Iterator for IntoIter<T> {
    type Item = (Vec<u8>, T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.pairs.len() {
            let result = std::mem::replace(
                &mut self.pairs[self.position],
                (Vec::new(), unsafe { std::mem::zeroed() }),
            );
            self.position += 1;
            Some(result)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.pairs.len() - self.position;
        (remaining, Some(remaining))
    }
}

impl<T> IntoIterator for TrieMap<T> {
    type Item = (Vec<u8>, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        let mut pairs = Vec::with_capacity(self.size);
        let mut nodes = Vec::new();
        let mut prefixes = Vec::new();

        nodes.push(&self.root);
        prefixes.push(Vec::new());

        while let Some((node, prefix)) = nodes.pop().zip(prefixes.pop()) {
            if let Some(idx) = node.data_idx {
                if let Some(value) = &self.data[idx] {
                    let value = unsafe { std::ptr::read(value as *const T) };
                    pairs.push((prefix.clone(), value));
                }
            }

            for byte in (0..=255u8).rev() {
                if test_bit(&node.is_present, byte) {
                    let idx = popcount(&node.is_present, byte) as usize;
                    if idx < node.children.len() {
                        let mut new_prefix = prefix.clone();
                        new_prefix.push(byte);

                        nodes.push(&node.children[idx]);
                        prefixes.push(new_prefix);
                    }
                }
            }
        }

        IntoIter { pairs, position: 0 }
    }
}

impl<'a, T> IntoIterator for &'a TrieMap<T> {
    type Item = (Vec<u8>, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

use std::ops::{Index, IndexMut};

impl<T, Q: ?Sized> Index<&Q> for TrieMap<T>
where
    Q: AsBytes,
{
    type Output = T;

    fn index(&self, key: &Q) -> &Self::Output {
        self.get(key).expect("no entry found for key")
    }
}

impl<T, Q: ?Sized> IndexMut<&Q> for TrieMap<T>
where
    Q: AsBytes,
{
    fn index_mut(&mut self, key: &Q) -> &mut Self::Output {
        self.get_mut(key).expect("no entry found for key")
    }
}

impl<T, K: AsBytes, V: Into<T>> Extend<(K, V)> for TrieMap<T> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v.into());
        }
    }
}

impl<T, K, V> FromIterator<(K, V)> for TrieMap<T>
where
    K: AsBytes,
    V: Into<T>,
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut trie = TrieMap::new();
        for (key, value) in iter {
            trie.insert(key, value.into());
        }
        trie
    }
}

pub enum Entry<'a, T> {
    Occupied(OccupiedEntry<'a, T>),

    Vacant(VacantEntry<'a, T>),
}

pub struct OccupiedEntry<'a, T> {
    trie: &'a mut TrieMap<T>,
    key: Vec<u8>,
    data_idx: usize,
}

pub struct VacantEntry<'a, T> {
    trie: &'a mut TrieMap<T>,
    key: Vec<u8>,
}

impl<'a, T> Entry<'a, T> {
    pub fn get(&self) -> Option<&T> {
        match self {
            Entry::Occupied(entry) => Some(entry.get()),
            Entry::Vacant(_) => None,
        }
    }

    pub fn get_mut(&mut self) -> Option<&mut T> {
        match self {
            Entry::Occupied(entry) => Some(entry.get_mut()),
            Entry::Vacant(_) => None,
        }
    }
    pub fn or_default(self) -> &'a mut T
    where
        T: Default,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(T::default()),
        }
    }

    pub fn or_insert(self, default: T) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    pub fn or_insert_with_key<F: FnOnce(&[u8]) -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
        }
    }

    pub fn key(&self) -> &[u8] {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    pub fn and_modify<F: FnOnce(&mut T)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

impl<'a, T> OccupiedEntry<'a, T> {
    pub fn get(&self) -> &T {
        self.trie.data[self.data_idx].as_ref().unwrap()
    }

    pub fn get_mut(&mut self) -> &mut T {
        self.trie.data[self.data_idx].as_mut().unwrap()
    }

    pub fn into_mut(self) -> &'a mut T {
        self.trie.data[self.data_idx].as_mut().unwrap()
    }

    pub fn key(&self) -> &[u8] {
        &self.key
    }

    pub fn remove(self) -> T {
        let value = self.trie.remove(&self.key).unwrap();
        value
    }

    pub fn insert(&mut self, value: T) -> T {
        let old_value = std::mem::replace(&mut self.trie.data[self.data_idx], Some(value));
        old_value.unwrap()
    }
}

impl<'a, T> VacantEntry<'a, T> {
    pub fn key(&self) -> &[u8] {
        &self.key
    }

    pub fn insert(self, value: T) -> &'a mut T {
        self.trie.insert(&self.key, value);
        self.trie.get_mut(&self.key).unwrap()
    }
}

fn set_bit(a: &mut [u64; 4], k: u8) {
    a[(k / 64) as usize] |= 1u64 << (k % 64);
}

fn clear_bit(a: &mut [u64; 4], k: u8) {
    a[(k / 64) as usize] &= !(1u64 << (k % 64));
}

fn test_bit(a: &[u64; 4], k: u8) -> bool {
    (a[(k / 64) as usize] >> (k % 64)) & 0x01 != 0
}

fn popcount(a: &[u64; 4], k: u8) -> u16 {
    let mut res = 0;

    for i in 0..(k / 64) as usize {
        res += a[i].count_ones() as u16;
    }

    for i in 0..(k % 64) {
        res += (((a[(k / 64) as usize] >> i) & 0x01) != 0) as u16;
    }

    res
}

fn popcount_all(a: &[u64; 4]) -> u16 {
    a.iter().map(|&x| x.count_ones() as u16).sum()
}

pub trait AsBytes {
    fn as_bytes(&self) -> &[u8];
}

impl AsBytes for [u8] {
    fn as_bytes(&self) -> &[u8] {
        self
    }
}

impl AsBytes for Vec<u8> {
    fn as_bytes(&self) -> &[u8] {
        self
    }
}

impl AsBytes for str {
    fn as_bytes(&self) -> &[u8] {
        str::as_bytes(self)
    }
}

impl AsBytes for String {
    fn as_bytes(&self) -> &[u8] {
        self.as_str().as_bytes()
    }
}

impl<'a, T: AsBytes + ?Sized> AsBytes for &'a T {
    fn as_bytes(&self) -> &[u8] {
        T::as_bytes(*self)
    }
}

#[derive(Clone)]
struct TrieNode {
    is_present: [u64; 4],
    children: Box<[TrieNode]>,
    data_idx: Option<usize>,
}

impl TrieNode {
    fn new() -> Self {
        TrieNode {
            is_present: [0; 4],
            children: Box::new([]),
            data_idx: None,
        }
    }
}

pub struct TrieMap<T> {
    data: Vec<Option<T>>,
    free_indices: Vec<usize>,
    root: TrieNode,
    size: usize,
}

impl<T> Default for TrieMap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> From<std::collections::HashMap<String, T>> for TrieMap<T> {
    fn from(map: std::collections::HashMap<String, T>) -> Self {
        let mut trie = TrieMap::with_capacity(map.len());
        for (k, v) in map {
            trie.insert(k, v);
        }
        trie
    }
}

impl<T> From<std::collections::BTreeMap<String, T>> for TrieMap<T> {
    fn from(map: std::collections::BTreeMap<String, T>) -> Self {
        let mut trie = TrieMap::with_capacity(map.len());
        for (k, v) in map {
            trie.insert(k, v);
        }
        trie
    }
}

impl<T: Clone> From<TrieMap<T>> for std::collections::HashMap<Vec<u8>, T> {
    fn from(trie: TrieMap<T>) -> Self {
        trie.into_iter().collect()
    }
}

impl<T> TrieMap<T> {
    pub fn merge(&mut self, other: &TrieMap<T>)
    where
        T: Clone,
    {
        for (key, value) in other.iter() {
            self.insert(key.clone(), value.clone());
        }
    }

    pub fn merge_with<F>(&mut self, other: &TrieMap<T>, mut f: F)
    where
        F: FnMut(&[u8], &T, &T) -> T,
        T: Clone,
    {
        for (key, value) in other.iter() {
            if let Some(existing) = self.get(&key) {
                let merged_value = f(&key, existing, value);
                self.insert(key.clone(), merged_value);
            } else {
                self.insert(key.clone(), value.clone());
            }
        }
    }

    pub fn get_or_insert_default<K: AsBytes>(&mut self, key: K) -> &mut T
    where
        T: Default,
    {
        if self.contains_key(&key) {
            self.get_mut(key).unwrap()
        } else {
            let value = T::default();
            self.insert(&key, value);
            self.get_mut(key).unwrap()
        }
    }

    pub fn get_or_insert_with<K: AsBytes, F>(&mut self, key: K, f: F) -> &mut T
    where
        F: FnOnce() -> T,
    {
        if self.contains_key(&key) {
            self.get_mut(key).unwrap()
        } else {
            let value = f();
            self.insert(&key, value);
            self.get_mut(key).unwrap()
        }
    }

    pub fn keys_starting_with<K: AsBytes>(&self, prefix: K) -> Vec<Vec<u8>> {
        let bytes = prefix.as_bytes();
        let mut result = Vec::new();

        if let Some(node) = self.find_node(bytes) {
            let mut prefix_vec = bytes.to_vec();
            self.collect_keys_with_prefix(node, &mut prefix_vec, &mut result);
        }

        result
    }

    pub fn update<K: AsBytes, F>(&mut self, key: K, f: F) -> Option<T>
    where
        F: FnOnce(&mut T),
    {
        if let Some(value) = self.get_mut(key) {
            f(value);
            None
        } else {
            None
        }
    }

    pub fn update_or_insert<K: AsBytes, F, G>(&mut self, key: K, update: F, insert: G) -> &mut T
    where
        F: FnOnce(&mut T),
        G: FnOnce() -> T,
    {
        match self.entry(key) {
            Entry::Occupied(mut entry) => {
                update(entry.get_mut());
                entry.into_mut()
            }
            Entry::Vacant(entry) => entry.insert(insert()),
        }
    }

    pub fn inserted<K: AsBytes>(&self, key: K, value: T) -> Self
    where
        T: Clone,
    {
        let mut new_map = self.clone();
        new_map.insert(key, value);
        new_map
    }

    pub fn removed<K: AsBytes>(&self, key: K) -> Self
    where
        T: Clone,
    {
        let mut new_map = self.clone();
        new_map.remove(key);
        new_map
    }

    pub fn without_prefix<K: AsBytes>(&self, prefix: K) -> Self
    where
        T: Clone,
    {
        let mut new_map = self.clone();
        new_map.remove_prefix_matches(prefix);
        new_map
    }

    pub fn with_prefix_only<K: AsBytes>(&self, prefix: K) -> Self
    where
        T: Clone,
    {
        let mut new_map = TrieMap::new();

        if let Some(matches) = self.find_node(prefix.as_bytes()) {
            let mut prefix_vec = prefix.as_bytes().to_vec();
            let mut pairs = Vec::new();

            self.collect_prefix_matches(matches, &mut prefix_vec, &mut pairs);

            for (key, value) in pairs {
                new_map.insert(key, value.clone());
            }
        }

        new_map
    }
    pub fn to_iter_vec(self) -> IntoIter<T> {
        self.into_iter()
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&[u8], &mut T) -> bool,
    {
        let keys: Vec<Vec<u8>> = self.keys().collect();

        let keys_to_remove = keys
            .iter()
            .filter_map(|k| {
                if let Some(value) = self.get_mut(k) {
                    if !f(k, value) {
                        return Some(k.clone());
                    }
                }
                None
            })
            .collect::<Vec<_>>();

        for key in keys_to_remove {
            self.remove(&key);
        }
    }

    pub fn entry<K: AsBytes>(&mut self, key: K) -> Entry<'_, T> {
        let key_bytes = key.as_bytes().to_vec();

        let mut current = &self.root;
        let mut found = true;

        for &byte in &key_bytes {
            if !test_bit(&current.is_present, byte) {
                found = false;
                break;
            }

            let idx = popcount(&current.is_present, byte) as usize;
            if idx >= current.children.len() {
                found = false;
                break;
            }

            current = &current.children[idx];
        }

        if found && current.data_idx.is_some() {
            let data_idx = current.data_idx.unwrap();

            if data_idx < self.data.len() && self.data[data_idx].is_some() {
                return Entry::Occupied(OccupiedEntry {
                    trie: self,
                    key: key_bytes,
                    data_idx,
                });
            }
        }

        Entry::Vacant(VacantEntry {
            trie: self,
            key: key_bytes,
        })
    }

    pub fn new() -> Self {
        TrieMap {
            data: Vec::new(),
            free_indices: Vec::new(),
            root: TrieNode::new(),
            size: 0,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        TrieMap {
            data: Vec::with_capacity(capacity),
            free_indices: Vec::new(),
            root: TrieNode::new(),
            size: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn clear(&mut self) {
        self.data.clear();
        self.free_indices.clear();
        self.root = TrieNode::new();
        self.size = 0;
    }

    pub fn insert<K: AsBytes>(&mut self, key: K, value: T) -> Option<usize> {
        let bytes = key.as_bytes();
        let mut current = &mut self.root;

        for &byte in bytes {
            let idx = popcount(&current.is_present, byte) as usize;

            if !test_bit(&current.is_present, byte) {
                let current_size = current.children.len();
                let mut new_children = Vec::with_capacity(current_size + 1);

                for i in 0..idx {
                    new_children.push(std::mem::replace(&mut current.children[i], TrieNode::new()));
                }

                new_children.push(TrieNode::new());

                for i in idx..current_size {
                    new_children.push(std::mem::replace(&mut current.children[i], TrieNode::new()));
                }

                current.children = new_children.into_boxed_slice();

                set_bit(&mut current.is_present, byte);
            }

            current = &mut current.children[idx];
        }

        let idx = if let Some(free_idx) = self.free_indices.pop() {
            self.data[free_idx] = Some(value);
            free_idx
        } else {
            self.data.push(Some(value));
            self.data.len() - 1
        };

        let prev_idx = current.data_idx;
        current.data_idx = Some(idx);

        if prev_idx.is_none() {
            self.size += 1;
        }

        prev_idx
    }

    pub fn get<K: AsBytes>(&self, key: K) -> Option<&T> {
        let bytes = key.as_bytes();
        let mut current = &self.root;

        for &byte in bytes {
            if !test_bit(&current.is_present, byte) {
                return None;
            }

            let idx = popcount(&current.is_present, byte) as usize;
            if idx >= current.children.len() {
                return None;
            }

            current = &current.children[idx];
        }

        current.data_idx.and_then(|idx| self.data[idx].as_ref())
    }

    pub fn get_mut<K: AsBytes>(&mut self, key: K) -> Option<&mut T> {
        let bytes = key.as_bytes();
        let mut current = &self.root;

        for &byte in bytes {
            if !test_bit(&current.is_present, byte) {
                return None;
            }

            let idx = popcount(&current.is_present, byte) as usize;
            if idx >= current.children.len() {
                return None;
            }

            current = &current.children[idx];
        }

        if let Some(idx) = current.data_idx {
            self.data[idx].as_mut()
        } else {
            None
        }
    }

    pub fn contains_key<K: AsBytes>(&self, key: K) -> bool {
        self.get(key).is_some()
    }

    pub fn starts_with<K: AsBytes>(&self, prefix: K) -> bool {
        let bytes = prefix.as_bytes();

        if let Some(node) = self.find_node(bytes) {
            node.data_idx.is_some() && self.data[node.data_idx.unwrap()].is_some()
                || self.has_any_value(node)
        } else {
            false
        }
    }

    pub fn get_prefix_matches<'a, K: AsBytes>(&'a self, prefix: K) -> Vec<(Vec<u8>, &'a T)> {
        let bytes = prefix.as_bytes();
        let mut result = Vec::new();

        if let Some(node) = self.find_node(bytes) {
            let mut prefix_vec = bytes.to_vec();
            self.collect_prefix_matches(node, &mut prefix_vec, &mut result);
        }

        result
    }

    pub fn remove_prefix_matches<K: AsBytes>(&mut self, prefix: K) -> Vec<(Vec<u8>, T)> {
        let bytes = prefix.as_bytes();
        let mut result = Vec::new();

        let keys_to_remove = if let Some(node) = self.find_node(bytes) {
            let mut keys = Vec::new();
            let mut prefix_vec = bytes.to_vec();
            self.collect_keys_with_prefix(node, &mut prefix_vec, &mut keys);
            keys
        } else {
            return result;
        };

        for key in keys_to_remove {
            if let Some(value) = self.remove_internal(&key) {
                result.push((key, value));
            }
        }

        result
    }

    fn collect_keys_with_prefix(
        &self,
        node: &TrieNode,
        prefix: &mut Vec<u8>,
        keys: &mut Vec<Vec<u8>>,
    ) {
        if let Some(idx) = node.data_idx {
            if self.data[idx].is_some() {
                keys.push(prefix.clone());
            }
        }

        for byte in 0..=255u8 {
            if test_bit(&node.is_present, byte) {
                let idx = popcount(&node.is_present, byte) as usize;
                if idx < node.children.len() {
                    prefix.push(byte);

                    self.collect_keys_with_prefix(&node.children[idx], prefix, keys);

                    prefix.pop();
                }
            }
        }
    }

    fn find_node(&self, bytes: &[u8]) -> Option<&TrieNode> {
        let mut current = &self.root;

        for &byte in bytes {
            if !test_bit(&current.is_present, byte) {
                return None;
            }

            let idx = popcount(&current.is_present, byte) as usize;
            if idx >= current.children.len() {
                return None;
            }

            current = &current.children[idx];
        }

        Some(current)
    }

    fn collect_prefix_matches<'a>(
        &'a self,
        node: &TrieNode,
        prefix: &mut Vec<u8>,
        result: &mut Vec<(Vec<u8>, &'a T)>,
    ) {
        if let Some(idx) = node.data_idx {
            if let Some(value) = self.data[idx].as_ref() {
                result.push((prefix.clone(), value));
            }
        }

        for byte in 0..=255u8 {
            if test_bit(&node.is_present, byte) {
                let idx = popcount(&node.is_present, byte) as usize;
                if idx < node.children.len() {
                    prefix.push(byte);

                    self.collect_prefix_matches(&node.children[idx], prefix, result);

                    prefix.pop();
                }
            }
        }
    }

    fn has_any_value(&self, node: &TrieNode) -> bool {
        if let Some(idx) = node.data_idx {
            if self.data[idx].is_some() {
                return true;
            }
        }

        for byte in 0..=255u8 {
            if test_bit(&node.is_present, byte) {
                let idx = popcount(&node.is_present, byte) as usize;
                if idx < node.children.len() && self.has_any_value(&node.children[idx]) {
                    return true;
                }
            }
        }

        false
    }

    pub fn remove<K: AsBytes>(&mut self, key: K) -> Option<T> {
        let bytes = key.as_bytes();
        if bytes.is_empty() {
            return None;
        }

        self.remove_internal(bytes)
    }

    fn remove_internal(&mut self, bytes: &[u8]) -> Option<T> {
        let mut path = Vec::with_capacity(bytes.len());
        let mut path_indices = Vec::with_capacity(bytes.len());

        let mut current = &self.root;

        for &byte in bytes {
            if !test_bit(&current.is_present, byte) {
                return None;
            }

            let idx = popcount(&current.is_present, byte) as usize;
            if idx >= current.children.len() {
                return None;
            }

            path.push(byte);
            path_indices.push(idx);
            current = &current.children[idx];
        }

        if let Some(idx) = current.data_idx {
            self.size -= 1;

            self.free_indices.push(idx);

            let value = self.data[idx].take();

            let mut delete_child = true;

            for depth in (0..path.len()).rev() {
                let byte = path[depth];
                let child_idx = path_indices[depth];

                let mut current = &mut self.root;
                for i in 0..depth {
                    current = &mut current.children[path_indices[i]];
                }

                let child = &current.children[child_idx];
                if delete_child && child.data_idx.is_none() && child.children.is_empty() {
                    let mut new_children = Vec::with_capacity(current.children.len() - 1);
                    for i in 0..current.children.len() {
                        if i != child_idx {
                            new_children
                                .push(std::mem::replace(&mut current.children[i], TrieNode::new()));
                        }
                    }
                    current.children = new_children.into_boxed_slice();

                    clear_bit(&mut current.is_present, byte);

                    delete_child = current.data_idx.is_none() && current.children.is_empty();
                } else {
                    delete_child = false;
                }
            }

            value
        } else {
            None
        }
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, T> {
        let mut pairs = Vec::with_capacity(self.size);
        let mut current_key = Vec::new();

        self.collect_pairs(&self.root, &mut current_key, &mut pairs);

        Iter { pairs, position: 0 }
    }

    fn collect_pairs<'a>(
        &'a self,
        node: &TrieNode,
        current_key: &mut Vec<u8>,
        pairs: &mut Vec<(Vec<u8>, &'a T)>,
    ) {
        if let Some(idx) = node.data_idx {
            if let Some(value) = self.data[idx].as_ref() {
                pairs.push((current_key.clone(), value));
            }
        }

        for byte in 0..=255u8 {
            if test_bit(&node.is_present, byte) {
                let idx = popcount(&node.is_present, byte) as usize;

                current_key.push(byte);

                self.collect_pairs(&node.children[idx], current_key, pairs);

                current_key.pop();
            }
        }
    }

    pub fn keys<'a>(&'a self) -> Keys<'a, T> {
        Keys { inner: self.iter() }
    }

    pub fn values<'a>(&'a self) -> Values<'a, T> {
        Values { inner: self.iter() }
    }

    pub fn shrink_to_fit(&mut self) {
        self.data.shrink_to_fit();
        self.free_indices.shrink_to_fit();
    }

    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    pub fn reserve(&mut self, additional: usize) {
        self.data.reserve(additional);
    }

    pub fn try_insert<K: AsBytes>(&mut self, key: K, value: T) -> Result<&mut T, T> {
        match self.entry(key) {
            Entry::Vacant(entry) => Ok(entry.insert(value)),
            Entry::Occupied(_) => Err(value),
        }
    }

    pub fn get_key_value<K: AsBytes + Clone>(&self, key: K) -> Option<(Vec<u8>, &T)> {
        let k2 = key.clone();
        let bytes = key.as_bytes();
        self.get(k2).map(|value| (bytes.to_vec(), value))
    }

    pub fn drain(&mut self) -> DrainIter<T> {
        let mut keys = Vec::with_capacity(self.size);
        let mut current_key = Vec::new();

        self.collect_keys(&self.root, &mut current_key, &mut keys);

        DrainIter {
            trie_map: self,
            keys,
            position: 0,
        }
    }

    fn collect_keys(&self, node: &TrieNode, current_key: &mut Vec<u8>, keys: &mut Vec<Vec<u8>>) {
        if let Some(idx) = node.data_idx {
            if self.data[idx].is_some() {
                keys.push(current_key.clone());
            }
        }

        for byte in 0..=255u8 {
            if test_bit(&node.is_present, byte) {
                let idx = popcount(&node.is_present, byte) as usize;

                current_key.push(byte);
                self.collect_keys(&node.children[idx], current_key, keys);
                current_key.pop();
            }
        }
    }

    pub fn entry_ref<'a, K: AsBytes + ?Sized>(&'a mut self, key: &'a K) -> Entry<'a, T> {
        let key_bytes = key.as_bytes().to_vec();

        let mut current = &self.root;
        let mut found = true;

        for &byte in key.as_bytes() {
            if !test_bit(&current.is_present, byte) {
                found = false;
                break;
            }

            let idx = popcount(&current.is_present, byte) as usize;
            if idx >= current.children.len() {
                found = false;
                break;
            }

            current = &current.children[idx];
        }

        if found && current.data_idx.is_some() {
            let data_idx = current.data_idx.unwrap();
            if data_idx < self.data.len() && self.data[data_idx].is_some() {
                return Entry::Occupied(OccupiedEntry {
                    trie: self,
                    key: key_bytes,
                    data_idx,
                });
            }
        }

        Entry::Vacant(VacantEntry {
            trie: self,
            key: key_bytes,
        })
    }

    pub fn into_keys(self) -> IntoKeys<T> {
        IntoKeys {
            inner: self.into_iter(),
        }
    }

    pub fn into_values(self) -> IntoValues<T> {
        IntoValues {
            inner: self.into_iter(),
        }
    }
}
pub struct DrainIter<'a, T> {
    trie_map: &'a mut TrieMap<T>,
    keys: Vec<Vec<u8>>,
    position: usize,
}

impl<'a, T> Iterator for DrainIter<'a, T> {
    type Item = (Vec<u8>, T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.keys.len() {
            let key = self.keys[self.position].clone();
            self.position += 1;

            Some((key.clone(), self.trie_map.remove(&key).unwrap()))
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.keys.len() - self.position;
        (remaining, Some(remaining))
    }
}

impl<'a, T> Drop for DrainIter<'a, T> {
    fn drop(&mut self) {
        for i in self.position..self.keys.len() {
            let _ = self.trie_map.remove(&self.keys[i]);
        }
    }
}

pub struct IntoKeys<T> {
    inner: IntoIter<T>,
}

impl<T> Iterator for IntoKeys<T> {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

pub struct IntoValues<T> {
    inner: IntoIter<T>,
}

impl<T> Iterator for IntoValues<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

pub struct Iter<'a, T> {
    pairs: Vec<(Vec<u8>, &'a T)>,
    position: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Vec<u8>, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.pairs.len() {
            let result = (
                self.pairs[self.position].0.clone(),
                self.pairs[self.position].1,
            );
            self.position += 1;
            Some(result)
        } else {
            None
        }
    }
}

pub struct Keys<'a, T> {
    inner: Iter<'a, T>,
}

impl<'a, T> Iterator for Keys<'a, T> {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
}

pub struct Values<'a, T> {
    inner: Iter<'a, T>,
}

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}

impl<const N: usize> AsBytes for [u8; N] {
    fn as_bytes(&self) -> &[u8] {
        self.as_slice()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(popcount_all(&bits), 3);
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

    use super::*;

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
    fn test_iter_ref() {
        let mut trie = TrieMap::new();
        trie.insert("a", 1);
        trie.insert("b", 2);

        let mut vec: Vec<_> = (&trie).into_iter().collect();
        vec.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));

        assert_eq!(vec.len(), 2);
        assert_eq!(*vec[0].1, 1);
        assert_eq!(*vec[1].1, 2);

        assert_eq!(trie.get("a"), Some(&1));
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
}
