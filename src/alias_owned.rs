#![allow(unused)]
use std::{marker::PhantomData, ops::Deref, rc::Rc};

/// A pointer that owns `T` but allows for weak pointers that point into it. Once the `Own` is
/// dropped, the value is dropped and the weak pointers can't access it anymore. The backing memory
/// is only freed once all the `Weak` pointers expire.
///
/// Because the ownership structure is a tree, this ensures that dropping a value will work even in
/// the presence of pointer cycles.
#[derive(Debug)]
pub struct AliasOwn<T>(Rc<T>);

#[derive(Debug)]
pub struct Weak<T>(std::rc::Weak<T>);

#[derive(Debug)]
pub struct WeakBorrow<'a, T>(Rc<T>, PhantomData<&'a T>);

impl<T> AliasOwn<T> {
    pub fn new(x: T) -> Self {
        Self(Rc::new(x))
    }

    pub fn alias(&self) -> Weak<T> {
        Weak(Rc::downgrade(&self.0))
    }
    /// Panics if there are active `WeakBorrow`s pointing to this value.
    pub fn into_inner(self) -> T {
        Rc::into_inner(self.0).expect(
            "failure: tried to get ownership of an \
            `AliasOwn` while `WeakBorrow`s to it were active",
        )
    }
    pub fn ptr_eq(&self, other: &Weak<T>) -> bool {
        self.alias().ptr_eq(other)
    }
}

impl<T> Weak<T> {
    /// Attempts to get access to the pointed-to value. Returns `None` if it has been dropped.
    /// Calls to `AliasOwn::into_inner` on the corresponding owning pointer will panic while this
    /// borrow is live.
    pub fn try_borrow(&self) -> Option<WeakBorrow<'_, T>> {
        Some(WeakBorrow(self.0.upgrade()?, PhantomData))
    }
    /// Attempts to get access to the pointed-to value. Panics if it has been dropped.
    /// Calls to `AliasOwn::into_inner` on the corresponding owning pointer will panic while this
    /// borrow is live.
    pub fn borrow(&self) -> WeakBorrow<'_, T> {
        self.try_borrow().unwrap()
    }
    pub fn ptr_eq(&self, other: &Self) -> bool {
        std::rc::Weak::ptr_eq(&self.0, &other.0)
    }
}

impl<T> WeakBorrow<'_, T> {
    pub fn ptr_eq(&self, other: &Weak<T>) -> bool {
        std::rc::Weak::ptr_eq(&Rc::downgrade(&self.0), &other.0)
    }
}

impl<T> Deref for AliasOwn<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl<T> Deref for WeakBorrow<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl<T> Clone for Weak<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
