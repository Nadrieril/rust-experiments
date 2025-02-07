use std::{ops::Deref, rc::Rc};

#[derive(Debug)]
// Option so we can move out of the fields despite the `Drop` impl. This is very sad, see
// https://github.com/rust-lang/rfcs/pull/3738 .
pub struct BiOwned1<T>(Option<Rc<T>>);
#[derive(Debug)]
pub struct BiOwned2<T>(Option<Rc<T>>);

#[derive(Debug)]
pub struct NotTheSamePointer;

pub fn new<T>(val: T) -> (BiOwned1<T>, BiOwned2<T>) {
    let val = Some(Rc::new(val));
    (BiOwned1(val.clone()), BiOwned2(val))
}
pub fn destroy<T>(mut x: BiOwned1<T>, mut y: BiOwned2<T>) -> Result<T, NotTheSamePointer> {
    let x = x.0.take().unwrap();
    let y = y.0.take().unwrap();
    if Rc::ptr_eq(&x, &y) {
        drop(x);
        Ok(Rc::into_inner(y).unwrap())
    } else {
        Err(NotTheSamePointer)
    }
}

impl<T> Deref for BiOwned1<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.0.as_deref().unwrap()
    }
}
impl<T> Deref for BiOwned2<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.0.as_deref().unwrap()
    }
}

impl<T> Drop for BiOwned1<T> {
    fn drop(&mut self) {
        // Only panic if not already panicking. Solve problems one by one, don't create more of
        // them.
        if std::thread::panicking() == false && self.0.is_some() {
            panic!("Don't drop a `BiOwned`")
        }
    }
}
impl<T> Drop for BiOwned2<T> {
    fn drop(&mut self) {
        // Only panic if not already panicking. Solve problems one by one, don't create more of
        // them.
        if std::thread::panicking() == false && self.0.is_some() {
            panic!("Don't drop a `BiOwned`")
        }
    }
}
