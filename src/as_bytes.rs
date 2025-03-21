/// The `AsBytes` trait allows a type to be used as a key in a `TrieMap`.
///
/// It provides a method to convert the type to a byte slice.
///
pub trait AsBytes {
    /// Converts the value to a byte slice.
    fn as_bytes(&self) -> &[u8];

    fn as_bytes_vec(&self) -> Vec<u8> {
        self.as_bytes().into()
    }
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

impl<T: AsBytes + ?Sized> AsBytes for &T {
    fn as_bytes(&self) -> &[u8] {
        T::as_bytes(*self)
    }
}

impl<const N: usize> AsBytes for [u8; N] {
    fn as_bytes(&self) -> &[u8] {
        self.as_slice()
    }
}
