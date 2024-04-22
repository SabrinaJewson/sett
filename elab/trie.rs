#[derive(Clone)]
pub struct Trie<K: Borrow<[u8]>, T> {
    inner: qp_trie::Trie<Key<K>, T>,
}

impl<K: Borrow<[u8]>, T> Trie<K, T> {
    pub fn get_prefix(&self, pattern: impl AsRef<[u8]>) -> Option<(&K, &T)> {
        let prefix = self.inner.longest_common_prefix(pattern.as_ref());
        let (k, v) = self.inner.iter_prefix(prefix).next()?;
        if k.0.borrow().len() != prefix.len() {
            return None;
        }
        Some((&k.0, v))
    }
    pub fn get_exact(&self, key: impl AsRef<[u8]>) -> Option<&T> {
        self.inner.get(key.as_ref())
    }
    pub fn insert(&mut self, key: K, value: T) {
        self.inner.insert(Key(key), value);
    }
}

impl<K: Borrow<[u8]>, T> Default for Trie<K, T> {
    fn default() -> Self {
        Self {
            inner: qp_trie::Trie::default(),
        }
    }
}

#[derive(Clone)]
struct Key<K>(K);

impl<K: Borrow<[u8]>> Borrow<[u8]> for Key<K> {
    fn borrow(&self) -> &[u8] {
        self.0.borrow()
    }
}

impl<K: Borrow<[u8]>> qp_trie::Break for Key<K> {
    type Split = [u8];
    fn empty<'a>() -> &'a Self::Split {
        &[]
    }
    fn find_break(&self, loc: usize) -> &Self::Split {
        &self.0.borrow()[..loc]
    }
}

use std::borrow::Borrow;
