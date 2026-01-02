use std::{marker::PhantomData, ops::Receiver, ptr::NonNull};

pub fn iterate_slice() {
    let mut x = [42];
    let mut s: &mut [_] = &mut x;
    while let Some((_x, new_s)) = s.split_first_mut() {
        s = new_s;
    }
}

// This doesn't work
// pub fn iterate_wrapped_slice() {
//     struct MySlice<'a>(&'a mut [u32]);
//     impl<'a> MySlice<'a> {
//         fn split_first_mut<'b>(&'b mut self) -> Option<(&'b mut u32, MySlice<'b>)> {
//             let (x, s) = self.0.split_first_mut()?;
//             Some((x, MySlice(s)))
//         }
//     }

//     let mut x = [42];
//     let mut s = MySlice(&mut x);
//     while let Some((_x, new_s)) = s.split_first_mut() {
//         s = new_s;
//     }
// }

// Botched experiment to see if a unique+covariant pointer would help.
// /// Unique pointer to a `T` that doesn't allow mutating the `T` directly. As such, it is covariant
// /// in `T`.
// struct Uniq<'a, T>(NonNull<T>, PhantomData<&'a T>);

// impl<'a, T> Uniq<'a, T> {
//     fn new(x: &'a mut T) -> Self {
//         Self(NonNull::from_mut(x), PhantomData)
//     }
// }

// impl<'a, T> Receiver for Uniq<'a, T> {
//     type Target = T;
// }

// pub fn iterate_wrapped_slice() {
//     struct MySlice<'a>(&'a mut [u32]);
//     impl<'a> MySlice<'a> {
//         fn split_first_mut<'b>(self: Uniq<'b, Self>) -> Option<(&'b mut u32, MySlice<'b>)> {
//             // todo
//             None
//         }
//     }

//     let mut x = [42];
//     let mut s = MySlice(&mut x);
//     while let Some((_x, new_s)) = Uniq::new(&mut s).split_first_mut() {
//         s = new_s;
//     }
// }
