#[derive(Clone)]
pub(crate) struct TrieNode {
    pub(crate) is_present: [u64; 4],
    pub(crate) children: Box<[TrieNode]>,
    pub(crate) data_idx: Option<usize>,
}

impl TrieNode {
    pub(crate) fn new() -> Self {
        TrieNode {
            is_present: [0; 4],
            children: Box::new([]),
            data_idx: None,
        }
    }
}

// Bit manipulation utilities
pub(crate) fn set_bit(a: &mut [u64; 4], k: u8) {
    a[(k / 64) as usize] |= 1u64 << (k % 64);
}

pub(crate) fn clear_bit(a: &mut [u64; 4], k: u8) {
    a[(k / 64) as usize] &= !(1u64 << (k % 64));
}

pub(crate) fn test_bit(a: &[u64; 4], k: u8) -> bool {
    (a[(k / 64) as usize] >> (k % 64)) & 0x01 != 0
}

pub(crate) fn popcount(a: &[u64; 4], k: u8) -> u16 {
    let mut res = 0;

    for i in a.iter().take((k / 64) as usize) {
        res += i.count_ones() as u16;
    }

    for i in 0..(k % 64) {
        res += (((a[(k / 64) as usize] >> i) & 0x01) != 0) as u16;
    }

    res
}
