#[derive(Copy, Clone, Default)]
pub(crate) struct TrieNode {
    pub(crate) is_present: [u64; 4],
    pub(crate) children: TrieNodeIdx,
    pub(crate) data_idx: Option<usize>,
}

#[derive(Copy, Clone, Default)]
pub(crate) struct TrieNodeIdx(pub(crate) usize);

impl From<usize> for TrieNodeIdx {
    fn from(value: usize) -> Self {
        TrieNodeIdx(value)
    }
}
impl TrieNode {
    pub(crate) fn new() -> Self {
        TrieNode {
            is_present: [0; 4],
            children: TrieNodeIdx(usize::MAX),
            data_idx: None,
        }
    }

    #[inline(always)]
    pub(crate) fn child_len(&self) -> u32 {
        self.is_present
            .iter()
            .fold(0, |acc, &x| acc + x.count_ones())
    }
}

#[inline(always)]
pub(crate) fn set_bit(a: &mut [u64; 4], k: u8) {
    a[(k >> 6) as usize] |= 1u64 << (k & 0x3F);
}
#[inline(always)]
pub(crate) fn clear_bit(a: &mut [u64; 4], k: u8) {
    a[(k >> 6) as usize] &= !(1u64 << (k & 0x3F));
}
#[inline(always)]
pub(crate) fn test_bit(a: &[u64; 4], k: u8) -> bool {
    (a[(k >> 6) as usize] & (1u64 << (k & 0x3F))) != 0
}
#[inline(always)]
pub(crate) fn popcount(a: &[u64; 4], k: u8) -> u16 {
    // Calculate indices for full chunks and remainder
    let full_chunks = (k >> 6) as usize;
    let remainder_bits = k & 0x3F;

    // Use fold instead of map+sum for better performance
    let full_sum: u16 = a[..full_chunks]
        .iter()
        .fold(0, |acc, &x| acc + x.count_ones() as u16);

    // Add remaining bits (only if there are any)
    let has_remainder = (remainder_bits > 0) as u16;
    full_sum + has_remainder * (a[full_chunks] & ((1u64 << remainder_bits) - 1)).count_ones() as u16
}
