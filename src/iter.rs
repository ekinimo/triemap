use crate::{node::test_bit, TrieMap};

/// An iterator over the key-value pairs of a `TrieMap`.
///
/// This struct is created by the [`iter`] method on [`TrieMap`].
///
/// [`iter`]: TrieMap::iter
pub struct Iter<'a, T> {
    pub(crate) trie: &'a TrieMap<T>,

    pub(crate) stack: Vec<IterState<'a>>,

    pub(crate) current_path: Vec<u8>,

    pub(crate) remaining: usize,
}

/// State for a single node in the traversal stack
pub(crate) struct IterState<'a> {
    pub(crate) node: &'a crate::node::TrieNode,

    pub(crate) byte_index: u16,

    pub(crate) value_emitted: bool,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Vec<u8>, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        // If we've yielded all items, we're done
        if self.remaining == 0 {
            return None;
        }

        while !self.stack.is_empty() {
            // Check the top of the stack
            let (node, byte_index, value_emitted) = {
                let state = self.stack.last_mut().unwrap();
                (state.node, state.byte_index, state.value_emitted)
            };

            if !value_emitted && node.data_idx.is_some() {
                let data_idx = node.data_idx.unwrap();
                if let Some(value) = self.trie.data[data_idx].as_ref() {
                    self.stack.last_mut().unwrap().value_emitted = true;
                    self.remaining -= 1;
                    return Some((self.current_path.clone(), value));
                } else {
                    self.stack.last_mut().unwrap().value_emitted = true;
                }
            }

            let mut found_next = false;
            let mut current_byte = byte_index;

            while current_byte <= 255 {
                let byte = current_byte as u8;

                self.stack.last_mut().unwrap().byte_index = current_byte + 1;

                if test_bit(&node.is_present, byte) {
                    let idx = crate::node::popcount(&node.is_present, byte) as usize;
                    if idx < node.children.len() {
                        // Get the child node
                        let child_node = &node.children[idx];

                        self.current_path.push(byte);
                        self.stack.push(IterState {
                            node: child_node,
                            byte_index: 0,
                            value_emitted: false,
                        });
                        found_next = true;
                        break;
                    }
                }

                current_byte += 1;
            }

            if found_next {
                continue;
            }

            self.stack.pop();
            if !self.current_path.is_empty() {
                self.current_path.pop();
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

/// An iterator over the keys of a `TrieMap`.
///
/// This struct is created by the [`keys`] method on [`TrieMap`].
///
/// [`keys`]: TrieMap::keys
pub struct Keys<'a, T> {
    pub(crate) inner: Iter<'a, T>,
}

impl<T> Iterator for Keys<'_, T> {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the values of a `TrieMap`.
///
/// This struct is created by the [`values`] method on [`TrieMap`].
///
/// [`values`]: TrieMap::values
pub struct Values<'a, T> {
    pub(crate) inner: Iter<'a, T>,
}

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// A draining iterator over the key-value pairs of a `TrieMap`.
///
/// This struct is created by the [`drain`] method on [`TrieMap`].
///
/// [`drain`]: TrieMap::drain
pub struct DrainIter<'a, T> {
    pub(crate) trie_map: &'a mut TrieMap<T>,
    pub(crate) keys: Vec<Vec<u8>>,
    pub(crate) position: usize,
}

impl<T> Iterator for DrainIter<'_, T> {
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

impl<T> Drop for DrainIter<'_, T> {
    fn drop(&mut self) {
        for i in self.position..self.keys.len() {
            let _ = self.trie_map.remove(&self.keys[i]);
        }
    }
}

/// An iterator over entries with keys that start with a specific prefix.
pub struct PrefixIter<'a, T> {
    pub(crate) trie: &'a TrieMap<T>,
    pub(crate) stack: Vec<IterState<'a>>,
    pub(crate) current_path: Vec<u8>,
    pub(crate) remaining: usize,
    pub(crate) prefix: Vec<u8>,
}

impl<'a, T> Iterator for PrefixIter<'a, T> {
    type Item = (Vec<u8>, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        while !self.stack.is_empty() {
            let (node, byte_index, value_emitted) = {
                let state = self.stack.last_mut().unwrap();
                (state.node, state.byte_index, state.value_emitted)
            };

            if !value_emitted && node.data_idx.is_some() {
                let data_idx = node.data_idx.unwrap();
                if let Some(value) = self.trie.data[data_idx].as_ref() {
                    self.stack.last_mut().unwrap().value_emitted = true;
                    self.remaining -= 1;
                    return Some((self.current_path.clone(), value));
                } else {
                    self.stack.last_mut().unwrap().value_emitted = true;
                }
            }

            let mut found_next = false;
            let mut current_byte = byte_index;

            while current_byte <= 255 {
                let byte = current_byte as u8;

                self.stack.last_mut().unwrap().byte_index = current_byte + 1;

                if test_bit(&node.is_present, byte) {
                    let idx = crate::node::popcount(&node.is_present, byte) as usize;
                    if idx < node.children.len() {
                        let child_node = &node.children[idx];

                        self.current_path.push(byte);
                        self.stack.push(IterState {
                            node: child_node,
                            byte_index: 0,
                            value_emitted: false,
                        });
                        found_next = true;
                        break;
                    }
                }

                current_byte += 1;
            }

            if found_next {
                continue;
            }

            self.stack.pop();
            if !self.current_path.is_empty() {
                self.current_path.pop();
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, T> ExactSizeIterator for PrefixIter<'a, T> {}
/// Iterator for keys that start with a specific prefix.
pub struct PrefixKeys<'a, T> {
    pub(crate) inner: PrefixIter<'a, T>,
}

impl<T> Iterator for PrefixKeys<'_, T> {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// Iterator for values that have keys starting with a specific prefix.
pub struct PrefixValues<'a, T> {
    pub(crate) inner: PrefixIter<'a, T>,
}

impl<'a, T> Iterator for PrefixValues<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// A consuming iterator over the key-value pairs of a `TrieMap`.
pub struct IntoIter<T> {
    data: Vec<Option<T>>,
    stack: Vec<TraversalState>,
    current_path: Vec<u8>,
    remaining: usize,
}

/// State for traversing the trie in IntoIter
struct TraversalState {
    node: crate::node::TrieNode,
    byte_index: u16,
    value_emitted: bool,
}

impl<T> Iterator for IntoIter<T> {
    type Item = (Vec<u8>, T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        loop {
            if self.stack.is_empty() {
                return None;
            }

            let has_value = {
                let state = self.stack.last_mut().unwrap();
                if !state.value_emitted && state.node.data_idx.is_some() {
                    let idx = state.node.data_idx.unwrap();
                    if idx < self.data.len() && self.data[idx].is_some() {
                        state.value_emitted = true;
                        true
                    } else {
                        state.value_emitted = true;
                        false
                    }
                } else {
                    false
                }
            };

            if has_value {
                let idx = self.stack.last().unwrap().node.data_idx.unwrap();
                let value = self.data[idx].take().unwrap();
                self.remaining -= 1;
                return Some((self.current_path.clone(), value));
            }

            let (found_next, byte) = {
                let state = self.stack.last_mut().unwrap();
                let mut found = false;
                let mut next_byte = 0;

                while state.byte_index <= 255 {
                    let b = state.byte_index as u8;
                    state.byte_index += 1;

                    if crate::node::test_bit(&state.node.is_present, b) {
                        let idx = crate::node::popcount(&state.node.is_present, b) as usize;
                        if idx < state.node.children.len() {
                            found = true;
                            next_byte = b;
                            break;
                        }
                    }
                }

                (found, next_byte)
            };

            if found_next {
                let child = {
                    let state = self.stack.last().unwrap();
                    let idx = crate::node::popcount(&state.node.is_present, byte) as usize;
                    state.node.children[idx].clone()
                };

                self.current_path.push(byte);
                self.stack.push(TraversalState {
                    node: child,
                    byte_index: 0,
                    value_emitted: false,
                });
            } else {
                self.stack.pop();
                if !self.current_path.is_empty() {
                    self.current_path.pop();
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> IntoIterator for TrieMap<T> {
    type Item = (Vec<u8>, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        let TrieMap {
            root, data, size, ..
        } = self;

        IntoIter {
            data,
            stack: vec![TraversalState {
                node: root,
                byte_index: 0,
                value_emitted: false,
            }],
            current_path: Vec::new(),
            remaining: size,
        }
    }
}
