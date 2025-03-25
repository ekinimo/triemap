use crate::{
    node::TrieNodeIdx,
    slice_pool::{KeysAndDataIdx, OwnedKeysAndDataIdx, PrefixKeysAndDataIdx},
    TrieMap,
};

/// An iterator over the key-value pairs of a `TrieMap`.
///
/// This struct is created by the [`iter`] method on [`TrieMap`].
///
/// [`iter`]: TrieMap::iter
pub struct Iter<'a, T> {
    pub(crate) data: &'a [Option<T>],
    pub(crate) iter: KeysAndDataIdx<'a>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Vec<u8>, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key_slice, data_idx)) = self.iter.next() {
            if data_idx < self.data.len() {
                if let Some(value) = &self.data[data_idx] {
                    return Some((Vec::from(&*key_slice), value));
                }
            }
        }
        None
    }
}
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
    pub(crate) data: &'a mut Vec<Option<T>>,
    pub(crate) free_indices: &'a mut Vec<usize>,
    pub(crate) size: &'a mut usize,
    pub(crate) keys: Vec<Vec<u8>>,
    pub(crate) position: usize,
    pub(crate) pool: &'a mut crate::slice_pool::SlicePool,
    pub(crate) root: TrieNodeIdx,
}

impl<'a, T> Iterator for DrainIter<'a, T> {
    type Item = (Vec<u8>, T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.keys.len() {
            let key = self.keys[self.position].clone();
            self.position += 1;

            // Search for the node that holds the data for this key
            let mut current_idx = self.root;
            let mut found = true;

            for &byte in &key {
                let current = self.pool.get_node(current_idx);
                if !crate::node::test_bit(&current.is_present, byte) {
                    found = false;
                    break;
                }

                if let Some(child_idx) = self.pool.get_child_idx(current_idx, byte) {
                    current_idx = child_idx;
                } else {
                    found = false;
                    break;
                }
            }

            if found {
                let node = self.pool.get_node_mut(current_idx);
                if let Some(data_idx) = node.data_idx.take() {
                    if data_idx < self.data.len() {
                        let value = self.data[data_idx].take();
                        self.free_indices.push(data_idx);
                        *self.size -= 1;

                        if let Some(val) = value {
                            return Some((key, val));
                        }
                    }
                }
            }

            // Continue to the next key if this one didn't yield a value
            self.next()
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.keys.len() - self.position;
        (0, Some(remaining)) // Conservative estimate
    }
}

impl<'a, T> Drop for DrainIter<'a, T> {
    fn drop(&mut self) {
        // Continue removing remaining items
        while self.next().is_some() {}
    }
}

/// An iterator over entries with keys that start with a specific prefix.
pub struct PrefixIter<'a, T> {
    pub(crate) data: &'a [Option<T>],
    pub(crate) iter: PrefixKeysAndDataIdx<'a>,
}

impl<'a, T> Iterator for PrefixIter<'a, T> {
    type Item = (Vec<u8>, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key_slice, data_idx)) = self.iter.next() {
            if data_idx < self.data.len() {
                if let Some(value) = &self.data[data_idx] {
                    return Some((Vec::from(&*key_slice), value));
                }
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.data.len())) // Conservative estimate
    }
}
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

/// An owning iterator over the key-value pairs of a `TrieMap`.
///
/// This struct is created when a `TrieMap` is consumed using `into_iter()`.
pub struct IntoIter<T> {
    data: Vec<Option<T>>,
    iter: OwnedKeysAndDataIdx,
}

impl<T> Iterator for IntoIter<T> {
    type Item = (Vec<u8>, T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key_slice, data_idx)) = self.iter.next() {
            if data_idx < self.data.len() {
                if let Some(value) = self.data[data_idx].take() {
                    let key = Vec::from(&*key_slice);
                    return Some((key, value));
                }
            }
        }
        None
    }
}

impl<T> IntoIterator for TrieMap<T> {
    type Item = (Vec<u8>, T);
    type IntoIter = IntoIter<T>;

    /// Consumes the map into an iterator yielding owned key-value pairs.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::TrieMap;
    /// let mut map = TrieMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    ///
    /// // Consume the map into an iterator
    /// for (key, value) in map {
    ///     println!("{}: {}", String::from_utf8_lossy(&key), value);
    /// }
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        // Get the owning iterator from the pool
        let iter = self.pool.into_keys_and_indices(self.root);

        // Take ownership of the data vector
        let data = self.data;

        IntoIter { data, iter }
    }
}

impl<'a, T> IntoIterator for &'a TrieMap<T> {
    type Item = (Vec<u8>, &'a T);
    type IntoIter = Iter<'a, T>;

    /// Returns an iterator over references to the key-value pairs of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::TrieMap;
    /// let mut map = TrieMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    ///
    /// // Iterate without consuming the map
    /// for (key, value) in &map {
    ///     println!("{}: {}", String::from_utf8_lossy(&key), value);
    /// }
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
