use crate::{slice_pool::SlicePool, AsBytes};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct VersionId(pub usize);


pub struct VersionTree<T> {

    nodes: Vec<Arc<TrieNode>>,
    pool: SlicePool<usize>,

    roots: HashMap<VersionId, usize>,
    latest_version: VersionId,
    parent_versions: HashMap<VersionId, VersionId>,
    child_versions: HashMap<VersionId, Vec<VersionId>>,


    sizes: HashMap<VersionId, usize>,


    next_version: usize,


    tombstones: Vec<Option<Arc<T>>>,
    free_tombstones: Vec<usize>,
}


#[derive(Clone)]
struct TrieNode {

    is_present: [u64; 4],


    children: Box<[usize]>,


    value: Option<usize>,
}


pub struct VersionTreeCursor<T> {
    current: VersionId,
    tree: VersionTree<T>,
}

impl TrieNode {
    fn new() -> Self {
        TrieNode {
            is_present: [0; 4],
            children: Box::new([]),
            value: None,
        }
    }
}

impl<T> VersionTree<T> {

    pub fn new() -> Self {
        let mut roots = HashMap::new();
        let root_node = Arc::new(TrieNode::new());


        let nodes = vec![root_node];
        roots.insert(VersionId(0), 0);


        let mut sizes = HashMap::new();
        sizes.insert(VersionId(0), 0);

        VersionTree {
            nodes,
            pool: SlicePool::new(),
            roots,
            latest_version: VersionId(0),
            parent_versions: HashMap::new(),
            child_versions: HashMap::new(),
            sizes,
            next_version: 1,
            tombstones: Vec::new(),
            free_tombstones: Vec::new(),
        }
    }


    pub fn cursor(self) -> VersionTreeCursor<T> {
        VersionTreeCursor {
            current: self.latest_version,
            tree: self,
        }
    }


    pub fn version(&self) -> VersionId {
        self.latest_version
    }


    pub fn len(&self, version: VersionId) -> Option<usize> {
        self.sizes.get(&version).copied()
    }


    pub fn is_empty(&self, version: VersionId) -> Option<bool> {
        self.len(version).map(|len| len == 0)
    }


    pub fn child_versions(&self, version: VersionId) -> impl Iterator<Item = VersionId> + '_ {
        self.child_versions
            .get(&version)
            .into_iter()
            .flat_map(|v| v.iter().copied())
    }


    pub fn parent_version(&self, version: VersionId) -> Option<VersionId> {
        self.parent_versions.get(&version).copied()
    }


    pub fn origin_version(&self) -> VersionId {
        VersionId(0)
    }


    fn find_node<K: AsBytes>(&self, version: VersionId, key: K) -> Option<usize> {
        let bytes = key.as_bytes();
        let root_idx = *self.roots.get(&version)?;

        let mut current_idx = root_idx;

        for &byte in bytes {
            let current = &self.nodes[current_idx];

            if !test_bit(&current.is_present, byte) {
                return None;
            }

            let idx = popcount(&current.is_present, byte) as usize;
            if idx >= current.children.len() {
                return None;
            }

            current_idx = current.children[idx];
        }

        Some(current_idx)
    }


    pub fn insert<K: AsBytes>(
        &mut self,
        version: VersionId,
        key: K,
        value: T,
    ) -> Option<VersionId> {

        let new_version = VersionId(self.next_version);
        self.next_version += 1;


        let prev_size = self.sizes.get(&version).copied().unwrap_or(0);
        self.sizes.insert(new_version, prev_size);


        self.parent_versions.insert(new_version, version);
        self.child_versions
            .entry(version)
            .or_insert_with(Vec::new)
            .push(new_version);


        let bytes = key.as_bytes();
        let root_idx = self.roots.get(&version).copied().unwrap_or(0);


        let new_root_idx = self.clone_and_insert_path(root_idx, bytes, value.into());


        let new_size = self.sizes.get_mut(&new_version).unwrap();
        *new_size += 1;


        self.roots.insert(new_version, new_root_idx);
        self.latest_version = new_version;

        Some(new_version)
    }


    fn clone_and_insert_path(&mut self, node_idx: usize, bytes: &[u8], value: Arc<T>) -> usize {
        if bytes.is_empty() {

            let new_node = Arc::new(TrieNode {
                is_present: self.nodes[node_idx].is_present.clone(),
                children: self.nodes[node_idx].children.clone(),
                value: Some(self.store_value(value.clone())),
            });

            self.nodes.push(new_node);
            return self.nodes.len() - 1;
        }

        let byte = bytes[0];
        let original_node = &self.nodes[node_idx];

        let mut new_node = TrieNode {
            is_present: original_node.is_present.clone(),
            children: original_node.children.clone(),
            value: original_node.value.clone(),
        };

        let child_idx = if test_bit(&original_node.is_present, byte) {

            popcount(&original_node.is_present, byte) as usize
        } else {

            set_bit(&mut new_node.is_present, byte);


            let current_size = original_node.children.len();
            let child_pos = popcount(&new_node.is_present, byte) as usize;

            let mut new_children = self.pool.get(current_size + 1);


            for i in 0..child_pos {
                new_children[i] = original_node.children[i];
            }


            new_children[child_pos] = 0;


            for i in child_pos..current_size {
                new_children[i + 1] = original_node.children[i];
            }

            new_node.children = new_children;
            child_pos
        };


        let child_node_idx = if test_bit(&original_node.is_present, byte) {
            original_node.children[child_idx]
        } else {

            let empty_node = Arc::new(TrieNode::new());
            self.nodes.push(empty_node);
            self.nodes.len() - 1
        };


        let new_child_idx = self.clone_and_insert_path(child_node_idx, &bytes[1..], value);


        new_node.children[child_idx] = new_child_idx;


        let new_node = Arc::new(new_node);
        self.nodes.push(new_node);
        self.nodes.len() - 1
    }


    fn store_value(&mut self, value: Arc<T>) -> usize {
        if let Some(idx) = self.free_tombstones.pop() {

            self.tombstones[idx] = Some(value);
            idx
        } else {

            self.tombstones.push(Some(value));
            self.tombstones.len() - 1
        }
    }


    pub fn remove<K: AsBytes>(&mut self, version: VersionId, key: K) -> Option<Arc<T>> {

        let node_idx = self.find_node(version, &key)?;
        let node = &self.nodes[node_idx];


        let value_idx = node.value?;
        let value = self.tombstones[value_idx].take()?;


        let new_version = VersionId(self.next_version);
        self.next_version += 1;


        let prev_size = self.sizes.get(&version).copied().unwrap_or(0);
        self.sizes.insert(new_version, prev_size - 1);


        self.parent_versions.insert(new_version, version);
        self.child_versions
            .entry(version)
            .or_insert_with(Vec::new)
            .push(new_version);


        let bytes = key.as_bytes();
        let root_idx = self.roots.get(&version).copied().unwrap_or(0);


        let new_root_idx = self.clone_and_remove_path(root_idx, bytes);


        self.roots.insert(new_version, new_root_idx);
        self.latest_version = new_version;


        self.free_tombstones.push(value_idx);

        Some(value)
    }


    fn clone_and_remove_path(&mut self, node_idx: usize, bytes: &[u8]) -> usize {
        if bytes.is_empty() {

            let new_node = Arc::new(TrieNode {
                is_present: self.nodes[node_idx].is_present.clone(),
                children: self.nodes[node_idx].children.clone(),
                value: None,
            });

            self.nodes.push(new_node);
            return self.nodes.len() - 1;
        }

        let byte = bytes[0];
        let original_node = &self.nodes[node_idx];

        if !test_bit(&original_node.is_present, byte) {

            return node_idx;
        }


        let mut new_node = TrieNode {
            is_present: original_node.is_present.clone(),
            children: original_node.children.clone(),
            value: original_node.value.clone(),
        };


        let child_idx = popcount(&original_node.is_present, byte) as usize;
        let child_node_idx = original_node.children[child_idx];


        let new_child_idx = self.clone_and_remove_path(child_node_idx, &bytes[1..]);


        new_node.children[child_idx] = new_child_idx;


        let new_node = Arc::new(new_node);
        self.nodes.push(new_node);
        self.nodes.len() - 1
    }


    pub fn get<K: AsBytes>(&self, version: VersionId, key: K) -> Option<Arc<T>> {
        let node_idx = self.find_node(version, key)?;
        let node = &self.nodes[node_idx];

        let value_idx = node.value?;
        self.tombstones[value_idx].clone()
    }


    pub fn get_key_value<K: AsBytes>(
        &self,
        version: VersionId,
        key: K,
    ) -> Option<(Vec<u8>, Arc<T>)> {
        let bytes = key.as_bytes().to_vec();
        self.get(version, &bytes).map(|value| (bytes, value))
    }


    pub fn contains_key<K: AsBytes>(&self, version: VersionId, key: K) -> bool {
        self.get(version, key).is_some()
    }
}

impl<T> VersionTreeCursor<T> {

    pub fn new() -> Self {
        let tree = VersionTree::new();
        Self {
            current: tree.latest_version,
            tree,
        }
    }


    pub fn version_tree(self) -> VersionTree<T> {
        self.tree
    }


    pub fn version(&self) -> VersionId {
        self.current
    }


    pub fn len(&self) -> usize {
        self.tree.len(self.current).unwrap_or(0)
    }


    pub fn is_empty(&self) -> bool {
        self.tree.is_empty(self.current).unwrap_or(true)
    }


    pub fn child_versions(&self) -> Vec<VersionId> {
        self.tree.child_versions(self.current).collect()
    }


    pub fn parent_version(&self) -> Option<VersionId> {
        self.tree.parent_version(self.current)
    }


    pub fn move_to_parent(&mut self) -> Option<()> {
        let parent = self.tree.parent_version(self.current)?;
        self.current = parent;
        Some(())
    }


    pub fn move_to_child(&mut self, idx: usize) -> Option<()> {
        let children = self.child_versions();
        let child = children.get(idx).copied()?;
        self.current = child;
        Some(())
    }


    pub fn move_to_version(&mut self, version: VersionId) -> Option<()> {
        if self.tree.roots.contains_key(&version) {
            self.current = version;
            Some(())
        } else {
            None
        }
    }


    pub fn move_to_origin(&mut self) -> Option<()> {
        self.current = self.tree.origin_version();
        Some(())
    }


    pub fn insert<K: AsBytes>(&mut self, key: K, value: T) {
        if let Some(new_version) = self.tree.insert(self.current, key, value) {
            self.current = new_version;
        }
    }


    pub fn remove<K: AsBytes>(&mut self, key: K) -> Option<Arc<T>> {
        let result = self.tree.remove(self.current, key);
        if result.is_some() {
            self.current = self.tree.latest_version;
        }
        result
    }


    pub fn get<K: AsBytes>(&self, key: K) -> Option<Arc<T>> {
        self.tree.get(self.current, key)
    }


    pub fn get_key_value<K: AsBytes>(&self, key: K) -> Option<(Vec<u8>, Arc<T>)> {
        self.tree.get_key_value(self.current, key)
    }


    pub fn contains_key<K: AsBytes>(&self, key: K) -> bool {
        self.tree.contains_key(self.current, key)
    }
}


#[inline]
fn set_bit(a: &mut [u64; 4], k: u8) {
    a[(k >> 6) as usize] |= 1u64 << (k & 0x3F);
}

#[inline]
fn test_bit(a: &[u64; 4], k: u8) -> bool {
    (a[(k >> 6) as usize] & (1u64 << (k & 0x3F))) != 0
}

#[inline]
fn popcount(a: &[u64; 4], k: u8) -> u16 {
    let full_chunks = (k >> 6) as usize;
    let remainder_bits = k & 0x3F;

    let full_sum: u16 = a[..full_chunks]
        .iter()
        .fold(0, |acc, &x| acc + x.count_ones() as u16);

    let has_remainder = (remainder_bits > 0) as u16;
    full_sum + has_remainder * (a[full_chunks] & ((1u64 << remainder_bits) - 1)).count_ones() as u16
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_new_tree() {
        let tree: VersionTree<i32> = VersionTree::new();
        assert_eq!(tree.version(), VersionId(0));
        assert_eq!(tree.len(VersionId(0)), Some(0));
        assert_eq!(tree.is_empty(VersionId(0)), Some(true));

        assert_eq!(tree.parent_version(VersionId(0)), None);
    }

    #[test]
    fn test_basic_insert() {
        let mut tree = VersionTree::new();


        tree.insert(VersionId(0), "key1", 100);


        let v1 = tree.version();
        assert_ne!(v1, VersionId(0));


        assert_eq!(tree.get(VersionId(0), "key1"), Some(100.into()));
        assert_eq!(tree.len(v1), Some(1));
        assert_eq!(tree.is_empty(v1), Some(false));


        assert_eq!(tree.get(VersionId(0), "key1"), None);
        assert_eq!(tree.len(VersionId(0)), Some(0));
    }

    #[test]
    fn test_multiple_inserts() {
        let mut tree = VersionTree::new();


        tree.insert(VersionId(0), "key1", 100);
        let v1 = tree.version();


        tree.insert(v1, "key2", 200);
        let v2 = tree.version();


        assert_eq!(tree.get(v2, "key1"), Some(100.into()));
        assert_eq!(tree.get(v2, "key2"), Some(200.into()));
        assert_eq!(tree.len(v2), Some(2));


        assert_eq!(tree.get(v1, "key1"), Some(100.into()));
        assert_eq!(tree.get(v1, "key2"), None);
        assert_eq!(tree.len(v1), Some(1));


        assert_eq!(tree.get(VersionId(0), "key1"), None);
        assert_eq!(tree.get(VersionId(0), "key2"), None);
        assert_eq!(tree.len(VersionId(0)), Some(0));
    }

    #[test]
    fn test_remove() {
        let mut tree = VersionTree::new();


        tree.insert(VersionId(0), "key1", 100);
        let v1 = tree.version();

        tree.insert(v1, "key2", 200);
        let v2 = tree.version();


        let removed = tree.remove(v2, "key1");
        let v3 = tree.version();


        assert_eq!(removed, Some(100.into()));


        assert_eq!(tree.get(v3, "key1"), None);
        assert_eq!(tree.get(v3, "key2"), Some(200.into()));
        assert_eq!(tree.len(v3), Some(1));


        assert_eq!(tree.get(v2, "key1"), Some(100.into()));
        assert_eq!(tree.get(v2, "key2"), Some(200.into()));
        assert_eq!(tree.len(v2), Some(2));

        assert_eq!(tree.get(v1, "key1"), Some(100.into()));
        assert_eq!(tree.get(v1, "key2"), None);
        assert_eq!(tree.len(v1), Some(1));
    }

    #[test]
    fn test_branching() {
        let mut tree = VersionTree::new();


        tree.insert(VersionId(0), "key1", 100);
        let v1 = tree.version();


        tree.insert(v1, "key2", 200);
        let branch1 = tree.version();


        tree.insert(v1, "key3", 300);
        let branch2 = tree.version();


        assert_ne!(branch1, branch2);


        assert_eq!(tree.get(branch1, "key1"), Some(100.into()));
        assert_eq!(tree.get(branch1, "key2"), Some(200.into()));
        assert_eq!(tree.get(branch1, "key3"), None);


        assert_eq!(tree.get(branch2, "key1"), Some(100.into()));
        assert_eq!(tree.get(branch2, "key2"), None);
        assert_eq!(tree.get(branch2, "key3"), Some(300.into()));


        assert_eq!(tree.parent_version(branch1), Some(v1));
        assert_eq!(tree.parent_version(branch2), Some(v1));


        /*let children = tree.child_versions(v1);
        assert_eq!(children.len(), 2);
        assert!(children.contains(&branch1));
        assert!(children.contains(&branch2));*/
    }
}
