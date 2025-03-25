use crate::node::{clear_bit, popcount, set_bit, test_bit, TrieNode, TrieNodeIdx};

#[derive(Clone)]
pub(crate) struct SlicePool {
    pub(crate) pools: [Vec<TrieNodeIdx>; 257],
    pub(crate) nodes: Vec<TrieNode>,
}

impl SlicePool {
    /// Creates a new empty slice pool
    pub(crate) fn new() -> Self {
        let pools = std::array::from_fn(|_| Vec::with_capacity(1024));
        let mut nodes = Vec::with_capacity(1024);
        nodes.push(TrieNode::new());
        SlicePool { pools, nodes }
    }

    /// Allocates a slice of nodes with the specified length
    #[inline(always)]
    pub(crate) fn allocate_slice(&mut self, len: usize) -> TrieNodeIdx {
        let idx = len;
        if let Some(slice) = unsafe { self.pools.get_unchecked_mut(idx) }.pop() {
            return slice;
        }

        let start_idx = self.nodes.len();
        self.nodes.extend((0..len).map(|_| TrieNode::new()));
        TrieNodeIdx(start_idx)
    }

    /// Returns a node slice to the pool for future reuse
    #[inline(always)]
    pub(crate) fn release_slice(&mut self, slice: TrieNodeIdx, len: usize) {
        let idx = len;
        unsafe { self.pools.get_unchecked_mut(idx) }.push(slice);
    }

    /// Clears all pools, dropping all stored slices
    #[inline(always)]
    pub(crate) fn clear(&mut self) {
        for pool in &mut self.pools {
            pool.clear();
        }
        self.nodes.clear();
        self.nodes.push(TrieNode::new())
    }

    /// Gets a node at the specified index
    #[inline(always)]
    pub(crate) fn get_node(&self, idx: TrieNodeIdx) -> &TrieNode {
        unsafe { self.nodes.get_unchecked(idx.0) }
    }

    /// Gets a mutable reference to a node at the specified index
    #[inline(always)]
    pub(crate) fn get_node_mut(&mut self, idx: TrieNodeIdx) -> &mut TrieNode {
        unsafe { self.nodes.get_unchecked_mut(idx.0) }
    }

    /// Inserts a new node into a slice at the specified position, returning the new slice
    #[inline(always)]
    pub(crate) fn insert_into_slice(
        &mut self,
        current_idx: TrieNodeIdx,
        current_len: usize,
        insert_pos: usize,
    ) -> TrieNodeIdx {
        let new_idx = self.allocate_slice(current_len + 1);

        for i in 0..insert_pos {
            let src = self.get_node(TrieNodeIdx(current_idx.0 + i));
            *self.get_node_mut(TrieNodeIdx(new_idx.0 + i)) = *src;
        }

        *self.get_node_mut(TrieNodeIdx(new_idx.0 + insert_pos)) = TrieNode::new();

        for i in insert_pos..current_len {
            let src = self.get_node(TrieNodeIdx(current_idx.0 + i));
            *self.get_node_mut(TrieNodeIdx(new_idx.0 + i + 1)) = *src;
        }

        self.release_slice(current_idx, current_len);

        new_idx
    }

    /// Removes a node from a slice at the specified position, returning the new slice
    #[inline(always)]
    pub(crate) fn remove_from_slice(
        &mut self,
        current_idx: TrieNodeIdx,
        current_len: usize,
        remove_pos: usize,
    ) -> TrieNodeIdx {
        if current_len == 0 {
            return TrieNodeIdx(usize::MAX); // Nothing to remove from an empty slice
        }
        let new_idx = self.allocate_slice(current_len - 1);

        for i in 0..remove_pos {
            let src = self.get_node(TrieNodeIdx(current_idx.0 + i));
            *self.get_node_mut(TrieNodeIdx(new_idx.0 + i)) = *src;
        }

        for i in remove_pos + 1..current_len {
            let src = self.get_node(TrieNodeIdx(current_idx.0 + i));
            *self.get_node_mut(TrieNodeIdx(new_idx.0 + i - 1)) = *src;
        }

        self.release_slice(current_idx, current_len);

        new_idx
    }

    /// Gets the child node index for a given byte in a trie node
    #[inline(always)]
    pub(crate) fn get_child_idx(&self, node_idx: TrieNodeIdx, byte: u8) -> Option<TrieNodeIdx> {
        let node = self.get_node(node_idx);

        if !test_bit(&node.is_present, byte) {
            return None;
        }

        let child_pos = popcount(&node.is_present, byte) as usize;
        if child_pos < node.child_len() as usize {
            Some(TrieNodeIdx(node.children.0 + child_pos))
        } else {
            None
        }
    }

    #[inline(always)]
    pub(crate) fn get_child_idx_unchecked(&self, node_idx: TrieNodeIdx, byte: u8) -> TrieNodeIdx {
        let node = self.get_node(node_idx);
        let child_pos = popcount(&node.is_present, byte) as usize;
        TrieNodeIdx(node.children.0 + child_pos)
    }

    #[inline(always)]
    pub(crate) fn add_child(&mut self, node_idx: TrieNodeIdx, byte: u8) -> TrieNodeIdx {
        let node = self.get_node(node_idx);
        if test_bit(&node.is_present, byte) {
            return self.get_child_idx_unchecked(node_idx, byte);
        }

        let child_count = node.child_len() as usize;
        let insert_pos = popcount(&node.is_present, byte) as usize;

        let current_children = node.children;

        let new_children = self.insert_into_slice(current_children, child_count, insert_pos);

        let node = self.get_node_mut(node_idx);
        node.children = new_children;
        set_bit(&mut node.is_present, byte);

        TrieNodeIdx(new_children.0 + insert_pos)
    }
    /// Removes a child node for a given byte in a trie node
    #[inline(always)]
    pub(crate) fn remove_child(&mut self, node_idx: TrieNodeIdx, byte: u8) -> bool {
        let node = self.get_node(node_idx);

        if !test_bit(&node.is_present, byte) {
            return false; // Child doesn't exist
        }

        let child_count = node.child_len() as usize;
        let remove_pos = popcount(&node.is_present, byte) as usize;

        let new_children = self.remove_from_slice(node.children, child_count, remove_pos);

        let node = self.get_node_mut(node_idx);
        node.children = new_children;
        clear_bit(&mut node.is_present, byte);

        true
    }

    pub(crate) fn into_keys_and_indices(self, root_idx: TrieNodeIdx) -> OwnedKeysAndDataIdx {
        OwnedKeysAndDataIdx::new(self.nodes, root_idx)
    }
    pub(crate) fn keys<'a>(&'a self, root_idx: TrieNodeIdx) -> KeysIterator<'a> {
        KeysIterator::new(self, root_idx)
    }

    pub(crate) fn keys_and_indices<'a>(&'a self, root_idx: TrieNodeIdx) -> KeysAndDataIdx<'a> {
        KeysAndDataIdx::new(self, root_idx)
    }
    pub(crate) fn prefix_keys_and_indices<'a>(
        &'a self,
        root_idx: TrieNodeIdx,
        prefix: Vec<u8>,
    ) -> PrefixKeysAndDataIdx<'a> {
        PrefixKeysAndDataIdx::new(self, root_idx, prefix)
    }
    #[inline(always)]
    pub(crate) fn has_children(&self, node_idx: TrieNodeIdx) -> bool {
        let node = self.get_node(node_idx);
        node.child_len() > 0
    }
}
pub struct KeysIterator<'a> {
    pool: &'a SlicePool,
    stack: Vec<(TrieNodeIdx, Vec<u8>)>, // Node index and complete path to node
}

impl<'a> KeysIterator<'a> {
    fn new(pool: &'a SlicePool, root_idx: TrieNodeIdx) -> Self {
        KeysIterator {
            pool,
            stack: vec![(root_idx, Vec::new())], // Start with root node and empty path
        }
    }
}

impl<'a> Iterator for KeysIterator<'a> {
    type Item = Box<[u8]>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node_idx, path)) = self.stack.pop() {
            let node = self.pool.get_node(node_idx);

            if node.data_idx.is_some() {
                for byte in (0..=255u8).rev() {
                    if test_bit(&node.is_present, byte) {
                        let child_idx = self.pool.get_child_idx_unchecked(node_idx, byte);
                        let mut child_path = path.clone();
                        child_path.push(byte);
                        self.stack.push((child_idx, child_path));
                    }
                }

                return Some(path.into_boxed_slice());
            }

            for byte in (0..=255u8).rev() {
                if test_bit(&node.is_present, byte) {
                    let child_idx = self.pool.get_child_idx_unchecked(node_idx, byte);
                    let mut child_path = path.clone();
                    child_path.push(byte);
                    self.stack.push((child_idx, child_path));
                }
            }
        }

        None
    }
}
pub(crate) struct KeysAndDataIdx<'a> {
    pool: &'a SlicePool,
    stack: Vec<(TrieNodeIdx, Vec<u8>)>, // Node index and complete path to node
}

impl<'a> KeysAndDataIdx<'a> {
    fn new(pool: &'a SlicePool, root_idx: TrieNodeIdx) -> Self {
        KeysAndDataIdx {
            pool,
            stack: vec![(root_idx, Vec::new())], // Start with root node and empty path
        }
    }
}

impl<'a> Iterator for KeysAndDataIdx<'a> {
    type Item = (Box<[u8]>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node_idx, path)) = self.stack.pop() {
            let node = self.pool.get_node(node_idx);
            if let Some(data_idx) = node.data_idx {
                for byte in (0..=255u8).rev() {
                    if test_bit(&node.is_present, byte) {
                        if let Some(child_idx) = self.pool.get_child_idx(node_idx, byte) {
                            let mut child_path = path.clone();
                            child_path.push(byte);
                            self.stack.push((child_idx, child_path));
                        }
                    }
                }
                return Some((path.into_boxed_slice(), data_idx));
            }

            for byte in (0..=255u8).rev() {
                if test_bit(&node.is_present, byte) {
                    let child_idx = self.pool.get_child_idx_unchecked(node_idx, byte);
                    let mut child_path = path.clone();
                    child_path.push(byte);
                    self.stack.push((child_idx, child_path));
                }
            }
        }

        None
    }
}

pub(crate) struct PrefixKeysAndDataIdx<'a> {
    pool: &'a SlicePool,
    stack: Vec<(TrieNodeIdx, Vec<u8>)>, // Node index and complete path
}

impl<'a> PrefixKeysAndDataIdx<'a> {
    fn new(pool: &'a SlicePool, root_idx: TrieNodeIdx, prefix: Vec<u8>) -> Self {
        let mut current_idx = root_idx;
        let mut found = true;

        for &byte in &prefix {
            let current = pool.get_node(current_idx);

            if !test_bit(&current.is_present, byte) {
                found = false;
                break;
            }

            current_idx = pool.get_child_idx_unchecked(current_idx, byte);
        }

        let stack = if found {
            vec![(current_idx, prefix.clone())]
        } else {
            vec![]
        };

        PrefixKeysAndDataIdx { pool, stack }
    }
}

impl<'a> Iterator for PrefixKeysAndDataIdx<'a> {
    type Item = (Box<[u8]>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node_idx, path)) = self.stack.pop() {
            let node = self.pool.get_node(node_idx);

            if let Some(data_idx) = node.data_idx {
                for byte in (0..=255u8).rev() {
                    if test_bit(&node.is_present, byte) {
                        let child_idx = self.pool.get_child_idx_unchecked(node_idx, byte);
                        let mut child_path = path.clone();
                        child_path.push(byte);
                        self.stack.push((child_idx, child_path));
                    }
                }

                return Some((path.into_boxed_slice(), data_idx));
            }

            for byte in (0..=255u8).rev() {
                if test_bit(&node.is_present, byte) {
                    let child_idx = self.pool.get_child_idx_unchecked(node_idx, byte);
                    let mut child_path = path.clone();
                    child_path.push(byte);
                    self.stack.push((child_idx, child_path));
                }
            }
        }

        None
    }
}
/// Iterator that takes ownership of a SlicePool and yields key-data_idx pairs
pub(crate) struct OwnedKeysAndDataIdx {
    stack: Vec<(TrieNodeIdx, Vec<u8>)>, // Node index and complete path to node
    nodes: Vec<TrieNode>,
}

impl OwnedKeysAndDataIdx {
    fn new(nodes: Vec<TrieNode>, root_idx: TrieNodeIdx) -> Self {
        OwnedKeysAndDataIdx {
            stack: vec![(root_idx, Vec::new())], // Start with root node and empty path
            nodes,
        }
    }

    fn get_node(&self, idx: TrieNodeIdx) -> &TrieNode {
        &self.nodes[idx.0]
    }

    fn get_child_idx_unchecked(&self, node_idx: TrieNodeIdx, byte: u8) -> TrieNodeIdx {
        let node = self.get_node(node_idx);

        let child_pos = popcount(&node.is_present, byte) as usize;
        TrieNodeIdx(node.children.0 + child_pos)
    }
}

impl Iterator for OwnedKeysAndDataIdx {
    type Item = (Box<[u8]>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node_idx, path)) = self.stack.pop() {
            let node = *self.get_node(node_idx);

            if let Some(data_idx) = node.data_idx {
                for byte in (0..=255u8).rev() {
                    if test_bit(&node.is_present, byte) {
                        let child_idx = self.get_child_idx_unchecked(node_idx, byte);
                        let mut child_path = path.clone();
                        child_path.push(byte);
                        self.stack.push((child_idx, child_path));
                    }
                }

                return Some((path.into_boxed_slice(), data_idx));
            }

            for byte in (0..=255u8).rev() {
                if test_bit(&node.is_present, byte) {
                    let child_idx = self.get_child_idx_unchecked(node_idx, byte);
                    let mut child_path = path.clone();
                    child_path.push(byte);
                    self.stack.push((child_idx, child_path));
                }
            }
        }

        None
    }
}
