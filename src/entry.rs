use crate::TrieMap;

/// Represents an entry in a `TrieMap` which may either be vacant or occupied.
///
/// This is part of the `Entry API` and is used to ensure that only a single lookup is performed.
///
/// # Examples
///
/// ```
/// use triemap::{TrieMap, Entry};
///
/// let mut map = TrieMap::new();
///
/// match map.entry("a") {
///     Entry::Vacant(entry) => {
///         entry.insert(1);
///     }
///     Entry::Occupied(entry) => {
///         *entry.into_mut() += 1;
///     }
/// }
/// ```
pub enum Entry<'a, T> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, T>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, T>),
}

/// A view into an occupied entry in a `TrieMap`.
///
/// It is part of the [`Entry`] API.
pub struct OccupiedEntry<'a, T> {
    pub(crate) trie: &'a mut TrieMap<T>,
    pub(crate) key: Vec<u8>,
    pub(crate) data_idx: usize,
}

/// A view into a vacant entry in a `TrieMap`.
///
/// It is part of the [`Entry`] API.
pub struct VacantEntry<'a, T> {
    pub(crate) trie: &'a mut TrieMap<T>,
    pub(crate) key: Vec<u8>,
}

impl<'a, T> Entry<'a, T> {
    /// Returns a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::TrieMap;
    /// let mut map = TrieMap::new();
    /// map.insert("a", 1);
    ///
    /// if let Some(value) = map.entry("a").get() {
    ///     assert_eq!(*value, 1);
    /// }
    /// assert_eq!(map.entry("b").get(), None);
    /// ```
    pub fn get(&self) -> Option<&T> {
        match self {
            Entry::Occupied(entry) => Some(entry.get()),
            Entry::Vacant(_) => None,
        }
    }

    /// Returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::TrieMap;
    /// let mut map = TrieMap::new();
    /// map.insert("a", 1);
    ///
    /// if let Some(value) = map.entry("a").get_mut() {
    ///     *value += 1;
    /// }
    /// assert_eq!(map.get("a"), Some(&2));
    /// ```
    pub fn get_mut(&mut self) -> Option<&mut T> {
        match self {
            Entry::Occupied(entry) => Some(entry.get_mut()),
            Entry::Vacant(_) => None,
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::TrieMap;
    /// let mut map = TrieMap::new();
    ///
    /// map.entry("a").or_default();
    /// assert_eq!(map.get("a"), Some(&0));
    /// ```
    pub fn or_default(self) -> &'a mut T
    where
        T: Default,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(T::default()),
        }
    }

    /// Ensures a value is in the entry by inserting the given value if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::TrieMap;
    /// let mut map = TrieMap::new();
    ///
    /// map.entry("a").or_insert(1);
    /// assert_eq!(map.get("a"), Some(&1));
    ///
    /// *map.entry("a").or_insert(10) *= 2;
    /// assert_eq!(map.get("a"), Some(&2));
    /// ```
    pub fn or_insert(self, default: T) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the function if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::TrieMap;
    /// let mut map = TrieMap::new();
    ///
    /// map.entry("a").or_insert_with(|| 1);
    /// assert_eq!(map.get("a"), Some(&1));
    ///
    /// let mut called = false;
    /// map.entry("a").or_insert_with(|| {
    ///     called = true;
    ///     2
    /// });
    /// assert_eq!(called, false);
    /// ```
    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the function if empty.
    ///
    /// The function is given a reference to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::TrieMap;
    /// let mut map = TrieMap::new();
    ///
    /// map.entry("a").or_insert_with_key(|key| key.len());
    /// assert_eq!(map.get("a"), Some(&1));
    /// ```
    pub fn or_insert_with_key<F: FnOnce(&[u8]) -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
        }
    }

    /// Returns a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::TrieMap;
    /// let mut map : TrieMap<()> = TrieMap::new();
    ///
    /// assert_eq!(map.entry("a").key(), b"a");
    /// ```
    pub fn key(&self) -> &[u8] {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::TrieMap;
    /// let mut map = TrieMap::new();
    ///
    /// map.entry("a")
    ///    .and_modify(|v| *v += 1)
    ///    .or_insert(1);
    ///
    /// assert_eq!(map.get("a"), Some(&1));
    ///
    /// map.entry("a")
    ///    .and_modify(|v| *v += 1)
    ///    .or_insert(0);
    ///
    /// assert_eq!(map.get("a"), Some(&2));
    /// ```
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
    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::{TrieMap, Entry};
    /// let mut map = TrieMap::new();
    /// map.insert("a", 1);
    ///
    /// if let Entry::Occupied(entry) = map.entry("a") {
    ///     assert_eq!(entry.get(), &1);
    /// }
    /// ```
    pub fn get(&self) -> &T {
        self.trie.data[self.data_idx].as_ref().unwrap()
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::{TrieMap, Entry};
    /// let mut map = TrieMap::new();
    /// map.insert("a", 1);
    ///
    /// if let Entry::Occupied(mut entry) = map.entry("a") {
    ///     *entry.get_mut() += 1;
    /// }
    ///
    /// assert_eq!(map.get("a"), Some(&2));
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        self.trie.data[self.data_idx].as_mut().unwrap()
    }

    /// Converts the entry into a mutable reference to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::{TrieMap, Entry};
    /// let mut map = TrieMap::new();
    /// map.insert("a", 1);
    ///
    /// if let Entry::Occupied(entry) = map.entry("a") {
    ///     *entry.into_mut() += 1;
    /// }
    ///
    /// assert_eq!(map.get("a"), Some(&2));
    /// ```
    pub fn into_mut(self) -> &'a mut T {
        self.trie.data[self.data_idx].as_mut().unwrap()
    }

    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::{TrieMap, Entry};
    /// let mut map = TrieMap::new();
    /// map.insert("a", 1);
    ///
    /// if let Entry::Occupied(entry) = map.entry("a") {
    ///     assert_eq!(entry.key(), b"a");
    /// }
    /// ```
    pub fn key(&self) -> &[u8] {
        &self.key
    }

    /// Removes the entry, returning the value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::{TrieMap, Entry};
    /// let mut map = TrieMap::new();
    /// map.insert("a", 1);
    ///
    /// if let Entry::Occupied(entry) = map.entry("a") {
    ///     assert_eq!(entry.remove(), 1);
    /// }
    ///
    /// assert_eq!(map.contains_key("a"), false);
    /// ```
    pub fn remove(self) -> T {
        self.trie.remove(&self.key).unwrap()
    }

    /// Replaces the value in the entry with the given value, returning the old value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::{TrieMap, Entry};
    /// let mut map = TrieMap::new();
    /// map.insert("a", 1);
    ///
    /// if let Entry::Occupied(mut entry) = map.entry("a") {
    ///     assert_eq!(entry.insert(2), 1);
    /// }
    ///
    /// assert_eq!(map.get("a"), Some(&2));
    /// ```
    pub fn insert(&mut self, value: T) -> T {
        let old_value = std::mem::replace(&mut self.trie.data[self.data_idx], Some(value));
        old_value.unwrap()
    }
}

impl<'a, T> VacantEntry<'a, T> {
    /// Gets a reference to the key that would be used when inserting a value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::{TrieMap, Entry};
    /// let mut map : TrieMap<()> = TrieMap::new();
    ///
    /// if let Entry::Vacant(entry) = map.entry("a") {
    ///     assert_eq!(entry.key(), b"a");
    /// }
    /// ```
    pub fn key(&self) -> &[u8] {
        &self.key
    }

    /// Inserts the given value into the entry, and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use triemap::{TrieMap, Entry};
    /// let mut map = TrieMap::new();
    ///
    /// if let Entry::Vacant(entry) = map.entry("a") {
    ///     entry.insert(1);
    /// }
    ///
    /// assert_eq!(map.get("a"), Some(&1));
    /// ```
    pub fn insert(self, value: T) -> &'a mut T {
        self.trie.insert(&self.key, value);
        self.trie.get_mut(&self.key).unwrap()
    }
}
