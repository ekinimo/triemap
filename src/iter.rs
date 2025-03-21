use crate::TrieMap;

/// An iterator over the key-value pairs of a `TrieMap`.
///
/// This struct is created by the [`iter`] method on [`TrieMap`].
///
/// [`iter`]: TrieMap::iter
pub struct Iter<'a, T> {
    pub(crate) pairs: Vec<(Vec<u8>, &'a T)>,
    pub(crate) position: usize,
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.pairs.len() - self.position;
        (remaining, Some(remaining))
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
    pub(crate) pairs: Vec<(Vec<u8>, &'a T)>,
    pub(crate) position: usize,
}

impl<'a, T> Iterator for PrefixIter<'a, T> {
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.pairs.len() - self.position;
        (remaining, Some(remaining))
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
