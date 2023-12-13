pub(crate) struct Stack<'a, T> {
    // covariant in `T`
    lifetime: PhantomData<&'a T>,
    // must be a unique pointer; using `NonNull` for covariance
    ptr: ptr::NonNull<Vec<T>>,
}

impl<'a, T> Stack<'a, T> {
    pub fn new(v: &'a mut Vec<T>) -> Self {
        let lifetime = PhantomData;
        let ptr = ptr::NonNull::from(v);
        Self { lifetime, ptr }
    }
    pub fn reborrow(&mut self) -> Stack<'_, T> {
        Stack::new(unsafe { self.ptr.as_mut() })
    }
    pub fn with<R>(&mut self, value: T, f: impl for<'b> FnOnce(Stack<'b, T>) -> R) -> R {
        struct Guard<'a, T>(usize, Stack<'a, T>);
        impl<T> Drop for Guard<'_, T> {
            fn drop(&mut self) {
                unsafe { self.1.ptr.as_mut() }.truncate(self.0);
            }
        }
        let mut guard = Guard(self.len(), self.reborrow());
        unsafe { guard.1.ptr.as_mut() }.push(value);
        f(guard.1.reborrow())
    }
}

impl<T> Deref for Stack<'_, T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

use std::marker::PhantomData;
use std::ops::Deref;
use std::ptr;
