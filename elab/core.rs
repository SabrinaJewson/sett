pub(crate) mod ident {
    #[derive(Clone)]
    pub(crate) struct Ident(Rc<str>);

    impl Ident {
        pub fn try_from_rc(s: Rc<str>) -> Result<Self, String> {
            if s.chars().any(|c| c.is_control()) {
                return Err("identifier contains control code".to_owned());
            }
            if s.chars().any(|c| c.is_whitespace()) {
                return Err("identifier contains whitespace".to_owned());
            }
            if s.contains("//") || s.contains("/*") {
                return Err("identifier contains comment".to_owned());
            }
            if *s != *":" && s.contains(":") {
                return Err("identifier contains colon".to_owned());
            }
            if *s == *"super" {
                return Err("`super` is not a valid identifier".to_owned());
            }
            if s.is_empty() {
                return Err("the empty string is not an identifier".to_owned());
            }
            Ok(Ident(s))
        }
        pub fn len(&self) -> usize {
            self.0.len()
        }
    }

    impl Borrow<[u8]> for Ident {
        fn borrow(&self) -> &[u8] {
            self.0.as_bytes()
        }
    }

    pub(crate) fn parse_longest(input: &str, mut quit_at: impl FnMut(&str) -> bool) -> usize {
        let mut iter = input.char_indices();
        while let Some((i, c)) = iter.next() {
            if quit_at(iter.as_str()) {
                return i;
            }
            if iter.as_str().starts_with("//") || iter.as_str().starts_with("/*") {
                return i;
            }
            if c.is_control() || c.is_whitespace() || (i != 0 && c == ':') {
                return i;
            }
        }
        input.len()
    }

    use std::borrow::Borrow;
    use std::rc::Rc;
}
pub(crate) use ident::Ident;

mod namespace {
    #[derive(Clone)]
    pub(crate) struct Namespace<T> {
        trie: Trie<Ident, (Visibility, Box<T>)>,
    }

    impl<T> Namespace<T> {
        pub fn get_prefix(&self, pattern: &str) -> Option<(Ident, Visibility, &T)> {
            let (ident, &(vis, ref val)) = self.trie.get_prefix(pattern)?;
            Some((ident.clone(), vis, val))
        }
        pub fn get_exact(&self, pattern: &str) -> Option<(Visibility, &T)> {
            let &(vis, ref val) = self.trie.get_exact(pattern)?;
            Some((vis, val))
        }
        pub fn insert(&mut self, ident: Ident, vis: Visibility, val: T) {
            self.trie.insert(ident, (vis, Box::new(val)));
        }
    }

    impl<T> Default for Namespace<T> {
        fn default() -> Self {
            Self {
                trie: Trie::default(),
            }
        }
    }

    use super::*;
    use crate::Trie;
}
pub(crate) use namespace::Namespace;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Visibility {
    Private,
    Public,
}
