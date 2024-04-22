mod basic {
    /// Somewhat like a `Rc<dyn Hash + Eq>`, but not relying on Rust’s built-in `TypeId` mechanism
    /// at all, so it’s possible for two identical values of identical types to compare unequal if
    /// they originated from different families (but the converse does hold: any given family
    /// contains exactly one type). So it’s more nominally typed.
    pub(crate) struct TypeId {
        hash: u64,
        extra: ptr::NonNull<Header>,
    }

    #[repr(C)]
    struct Inner<T> {
        header: Header,
        index: T,
    }

    struct Header {
        count: Cell<u32>,
        variant: u32,
        index_eq: unsafe fn(*const (), *const ()) -> bool,
        drop_self: unsafe fn(*mut Header),
    }

    static VARIANT: AtomicU32 = AtomicU32::new(0);

    impl TypeId {
        pub(crate) fn new_family<Index: PartialEq + Eq + Hash>() -> Option<Family<Index>> {
            let variant = VARIANT.fetch_add(1, atomic::Ordering::Relaxed);
            if (u32::MAX >> 1) <= variant {
                VARIANT.store(u32::MAX >> 1, atomic::Ordering::Relaxed);
                return None;
            }
            Some(Family {
                variant,
                phantom: PhantomData,
            })
        }
    }

    pub(crate) struct Family<Index: PartialEq + Eq + Hash> {
        variant: u32,
        phantom: PhantomData<fn(Index)>,
    }

    impl<Index: PartialEq + Eq + Hash> Clone for Family<Index> {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<Index: PartialEq + Eq + Hash> Copy for Family<Index> {}

    impl<Index: PartialEq + Eq + Hash> Family<Index> {
        pub(crate) fn new_type_id(self, index: Index) -> TypeId {
            let mut hasher = FxHasher::default();
            self.variant.hash(&mut hasher);
            index.hash(&mut hasher);
            let hash = hasher.finish();

            let ptr = ptr::NonNull::from(Box::leak(Box::new(Inner {
                header: Header {
                    count: Cell::new(1),
                    variant: self.variant,
                    index_eq: |a, b| {
                        let (a, b) = (a.cast::<Index>(), b.cast::<Index>());
                        unsafe { Index::eq(&*a, &*b) }
                    },
                    drop_self: |ptr| {
                        unsafe { drop(Box::from_raw(ptr.cast::<Inner<Index>>())) };
                    },
                },
                index,
            })));
            let extra = ptr.cast::<Header>();

            TypeId { hash, extra }
        }
    }

    impl Clone for TypeId {
        fn clone(&self) -> Self {
            let count = unsafe { &self.extra.as_ref().count };
            count.set(count.get().checked_add(1).unwrap());
            Self {
                hash: self.hash,
                extra: self.extra,
            }
        }
    }

    impl PartialEq for TypeId {
        fn eq(&self, other: &Self) -> bool {
            if self.hash != other.hash {
                return false;
            }
            if self.extra == other.extra {
                return true;
            }
            let header_a = unsafe { self.extra.as_ref() };
            let header_b = unsafe { other.extra.as_ref() };
            if header_a.variant != header_b.variant {
                return false;
            }
            debug_assert_eq!(header_a.index_eq, header_b.index_eq);
            debug_assert_eq!(header_a.drop_self, header_b.drop_self);
            let ptr_a: *const () = unsafe { self.extra.as_ptr().add(1).cast::<()>() };
            let ptr_b: *const () = unsafe { other.extra.as_ptr().add(1).cast::<()>() };
            unsafe { (header_a.index_eq)(ptr_a, ptr_b) }
        }
    }

    impl Eq for TypeId {}

    impl Hash for TypeId {
        fn hash<H: Hasher>(&self, state: &mut H) {
            state.write_u64(self.hash);
        }
    }

    impl Drop for TypeId {
        fn drop(&mut self) {
            {
                let count = unsafe { &self.extra.as_ref().count };
                let new_count = count.get() - 1;
                if new_count != 0 {
                    count.set(new_count);
                    return;
                }
            }

            let drop_inner = unsafe { self.extra.as_ref() }.drop_self;
            unsafe { drop_inner(self.extra.as_ptr()) };
        }
    }

    use rustc_hash::FxHasher;
    use std::cell::Cell;
    use std::hash::Hash;
    use std::hash::Hasher;
    use std::marker::PhantomData;
    use std::ptr;
    use std::sync::atomic;
    use std::sync::atomic::AtomicU32;
}
pub(crate) use basic::*;

pub(crate) mod map {
    #[derive(Clone)]
    pub(crate) struct Map<V> {
        inner: HashMap<TypeId, V, NoHashing>,
    }

    impl<V> Default for Map<V> {
        fn default() -> Self {
            Self {
                inner: HashMap::with_hasher(NoHashing),
            }
        }
    }

    impl<V> Map<V> {
        pub fn insert(&mut self, key: TypeId, value: V) {
            self.inner.insert(key, value);
        }
        pub fn remove(&mut self, key: &TypeId) -> Option<V> {
            self.inner.remove(key)
        }
    }

    #[derive(Clone)]
    struct NoHashing;
    impl BuildHasher for NoHashing {
        type Hasher = NoopHasher;
        fn build_hasher(&self) -> Self::Hasher {
            NoopHasher(0)
        }
    }
    struct NoopHasher(u64);
    impl Hasher for NoopHasher {
        fn write(&mut self, _bytes: &[u8]) {
            unimplemented!()
        }
        fn write_u64(&mut self, i: u64) {
            self.0 = i;
        }
        fn finish(&self) -> u64 {
            self.0
        }
    }

    use super::*;
    use std::collections::HashMap;
    use std::hash::BuildHasher;
    use std::hash::Hasher;
}
pub(crate) use map::Map;
