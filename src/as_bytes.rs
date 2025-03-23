/// The `AsBytes` trait allows a type to be used as a key in a `TrieMap`.
///
/// It provides a method to convert the type to a byte slice.
///
pub trait AsBytes {
    /// Converts the value to a byte slice.
    fn as_bytes(&self) -> impl Iterator<Item = u8>;

    fn as_bytes_vec(&self) -> Vec<u8> {
        self.as_bytes().collect()
    }
}

impl AsBytes for bool {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let val = if *self { Some(1) } else { Some(0) };
        val.into_iter()
    }
}

impl AsBytes for u8 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let val = Some(*self);
        val.into_iter()
    }
}

impl AsBytes for i8 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let val = Some(*self as u8);
        val.into_iter()
    }
}

impl AsBytes for u16 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}
impl AsBytes for i16 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        self.to_be_bytes().into_iter()
    }
}

impl AsBytes for u32 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}
impl AsBytes for i32 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}
impl AsBytes for u64 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}
impl AsBytes for i64 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}

impl AsBytes for u128 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}
impl AsBytes for i128 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}

impl AsBytes for usize {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}
impl AsBytes for isize {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}
impl AsBytes for f32 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}
impl AsBytes for f64 {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let bytes = self.to_be_bytes();
        bytes.into_iter()
    }
}
impl AsBytes for char {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        let s = self.to_digit(2).unwrap();
        s.as_bytes().collect::<Box<[_]>>().into_iter()
    }
}
impl<T: AsBytes> AsBytes for [T] {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        self.iter().flat_map(|x| x.as_bytes())
    }
}

impl<T: AsBytes> AsBytes for Vec<T> {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        self.iter().flat_map(|x| x.as_bytes())
    }
}

impl AsBytes for str {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        str::as_bytes(self).iter().copied()
    }
}

impl AsBytes for String {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        self.as_str().as_bytes().iter().copied()
    }
}

impl<T: AsBytes + ?Sized> AsBytes for &T {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        T::as_bytes(*self)
    }
}

impl<const N: usize, T: AsBytes> AsBytes for [T; N] {
    fn as_bytes(&self) -> impl Iterator<Item = u8> {
        self.as_slice().iter().flat_map(|x| x.as_bytes())
    }
}
