use ghost_cell::{GhostCell, GhostToken};
use std::fmt::Debug;
use std::mem;

use crate::bi_owned::{self, BiOwned1, BiOwned2};

pub struct Node<'brand> {
    val: GhostCell<'brand, u32>,
    next: GhostCell<'brand, Option<BiOwned1<Node<'brand>>>>,
    // Invariant: this points to the previous node, if any.
    prev: GhostCell<'brand, Option<BiOwned2<Node<'brand>>>>,
}

pub struct List<'brand> {
    inner: ListInner<'brand>,
    /// Lists without a token can't be mutated.
    token: Option<GhostToken<'brand>>,
}
enum ListInner<'brand> {
    Empty,
    NonEmpty {
        first_node: BiOwned1<Node<'brand>>,
        last_node: BiOwned2<Node<'brand>>,
    },
}

impl<'brand> List<'brand> {
    // Helpers
    fn make(token: Option<GhostToken<'brand>>, inner: ListInner<'brand>) -> Self {
        List { inner, token }
    }
    fn inner(&self) -> &ListInner<'brand> {
        &self.inner
    }
    fn inner_mut(&mut self) -> &mut ListInner<'brand> {
        &mut self.inner
    }
    fn into_inner(mut self) -> ListInner<'brand> {
        // Can't move out directly because `Self` has a manual `Drop` impl.
        mem::replace(&mut self.inner, ListInner::Empty)
    }
    fn token(&self) -> &GhostToken<'brand> {
        self.token.as_ref().unwrap()
    }
    fn token_mut(&mut self) -> &mut GhostToken<'brand> {
        self.token.as_mut().unwrap()
    }

    pub fn new(token: GhostToken<'brand>) -> Self {
        List::make(Some(token), ListInner::Empty)
    }

    // Internal helper.
    fn first_node(&self) -> Option<&Node<'brand>> {
        match self.inner() {
            ListInner::Empty => None,
            ListInner::NonEmpty { first_node, .. } => Some(first_node),
        }
    }
    // Internal helper.
    fn last_node(&self) -> Option<&Node<'brand>> {
        match self.inner() {
            ListInner::Empty => None,
            ListInner::NonEmpty { last_node, .. } => Some(last_node),
        }
    }

    /// Add an element to the end of the list.
    pub fn push(&mut self, val: u32) {
        let (fwd, bwd) = bi_owned::new(Node {
            val: GhostCell::new(val),
            next: GhostCell::new(None),
            prev: GhostCell::new(None),
        });
        self.append(List::make(
            None,
            ListInner::NonEmpty {
                first_node: fwd,
                last_node: bwd,
            },
        ));
    }
    pub fn append(&mut self, other: Self) {
        match (self.inner_mut(), other.into_inner()) {
            (_, ListInner::Empty) => {}
            (ListInner::Empty, other) => self.inner = other,
            (
                ListInner::NonEmpty {
                    last_node: self_last,
                    ..
                },
                ListInner::NonEmpty {
                    first_node: other_first,
                    last_node: other_last,
                },
            ) => {
                let old_last = mem::replace(self_last, other_last);
                *other_first.prev.borrow_mut(self.token_mut()) = Some(old_last);
                unsafe {
                    // Problem: we want to move `other_first` into a location we can only access
                    // through `other_first`. This is fine because there's indirection: `next_ptr`
                    // points into the heap, so we can move `other_first`.
                    // Second problem: we're taking two `GhostCell` borrows. This is not UB because
                    // `x != x.next` for all nodes `x`.
                    let other_first: BiOwned1<Node<'_>> = other_first;
                    let next_ptr: *mut Option<BiOwned1<Node>> = other_first
                        .prev
                        .borrow(self.token())
                        .as_ref()
                        .unwrap()
                        .next
                        .as_ptr();
                    *next_ptr = Some(other_first);
                }
            }
        }
    }
    /// Remove the first element.
    pub fn pop_front(&mut self) -> Option<u32> {
        match mem::replace(self.inner_mut(), ListInner::Empty) {
            ListInner::Empty => None,
            ListInner::NonEmpty {
                first_node,
                last_node,
            } => {
                let token = self.token_mut();
                let first_node: BiOwned1<_> = first_node;
                let last_node: BiOwned2<_> = last_node;
                // Get the other pointer that owns `first_node`.
                let snd_ptr: BiOwned2<_> = if let Some(next) = first_node.next.take(token) {
                    let snd = next.prev.take(token).unwrap();
                    *first_node.next.borrow_mut(token) = Some(next);
                    snd
                } else {
                    let node: Node = bi_owned::destroy(first_node, last_node).unwrap();
                    return Some(node.val.into_inner());
                };
                let node: Node = bi_owned::destroy(first_node, snd_ptr).unwrap();
                *self.inner_mut() = ListInner::NonEmpty {
                    first_node: node.next.into_inner().unwrap(),
                    last_node,
                };
                Some(node.val.into_inner())
            }
        }
    }

    pub fn start<'a>(&'a self) -> ListCursor<'a, 'brand> {
        ListCursor {
            node: self.first_node(),
            list: self,
        }
    }
    // pub fn start_mut(&mut self) -> ListCursorMut<'_> {
    //     ListCursorMut {
    //         node: self.first_node().map(BiOwned1::alias),
    //         list: self,
    //     }
    // }
    pub fn end<'a>(&'a self) -> ListCursor<'a, 'brand> {
        ListCursor {
            node: Default::default(),
            list: self,
        }
    }
    // pub fn end_mut(&mut self) -> ListCursorMut<'_> {
    //     ListCursorMut {
    //         node: Default::default(),
    //         list: self,
    //     }
    // }
}

impl<'brand> Drop for List<'brand> {
    fn drop(&mut self) {
        while !matches!(self.inner(), ListInner::Empty) {
            self.pop_front();
        }
    }
}

/// A cursor into a list. Points in-between nodes, which includes the start (before all nodes) and
/// the end (after all nodes); `val()` returns the value of the next node.
pub struct ListCursor<'a, 'brand> {
    node: Option<&'a Node<'brand>>,
    list: &'a List<'brand>,
}

impl<'a, 'brand> ListCursor<'a, 'brand> {
    pub fn val(&self) -> Option<&'a u32> {
        Some(&self.node?.val.borrow(self.list.token()))
    }
    /// Move the cursor forward. Returns `None` if we were already at the end of the list.
    pub fn forward(&mut self) -> Option<()> {
        self.node = self.node?.next.borrow(self.list.token()).as_deref();
        Some(())
    }
    /// Move the cursor backward. Returns `None` if we were already at the start of the list.
    pub fn backward(&mut self) -> Option<()> {
        let prev = match self.node {
            None => self.list.last_node()?,
            Some(node) => node.prev.borrow(self.list.token()).as_deref()?,
        };
        self.node = Some(prev);
        Some(())
    }
}

impl<'a, 'brand> Iterator for ListCursor<'a, 'brand> {
    type Item = &'a u32;
    fn next(&mut self) -> Option<Self::Item> {
        let val = self.val();
        self.forward()?;
        val
    }
}

impl<'a, 'brand> DoubleEndedIterator for ListCursor<'a, 'brand> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.backward()?;
        self.val()
    }
}

// /// A cursor into a list. Points in-between nodes, which includes the start (before all nodes) and
// /// the end (after all nodes); `val()` returns the value of the next node.
// pub struct ListCursorMut<'a> {
//     node: Option<BiOwned2<Node>>,
//     list: &'a mut List,
// }

// impl ListCursorMut<'_> {
//     /// Note: the return value is valid for the lifetime of the `self` borrow, not for `'a`, since
//     /// we can move forwards and backwards.
//     pub fn val(&mut self) -> Option<&mut u32> {
//         let val_ptr = self.node.as_ref()?.borrow().as_ptr();
//         // # Safety: we have an exclusive borrow on `self` and transitively on the list, so no
//         // other borrow is accessible.
//         Some(unsafe { &mut (*val_ptr).val })
//     }
//     /// Observe the underlying list.
//     pub fn list(&self) -> &List {
//         &self.list
//     }

//     /// Move the cursor forward. Returns `None` if we were already at the end of the list.
//     pub fn forward(&mut self) -> Option<()> {
//         let node = self.node.as_ref()?;
//         let next = node.borrow().borrow().next.as_ref().map(BiOwned1::alias);
//         self.node = next;
//         Some(())
//     }
//     /// Move the cursor backward. Returns `None` if we were already at the start of the list.
//     pub fn backward(&mut self) -> Option<()> {
//         let prev = match &self.node {
//             None => self.list.last_node()?.clone(),
//             Some(node) => node.borrow().borrow().prev.clone()?,
//         };
//         self.node = Some(prev);
//         Some(())
//     }

//     /// Split the list at the cursor. Returns a list containing all the nodes after the cursor.
//     pub fn split(&mut self) -> List {
//         let Some(node) = self.node.take() else {
//             return List::Empty
//         };
//         let node = node.borrow();
//         if let Some(prev) = node.borrow_mut().prev.take() {
//             // The pointed-to node has a predecessor: we get ownership of the node, which is owned
//             // by its predecessor. Unwrap is ok by the invariant that self.prev.next == self.
//             let node = prev.borrow().borrow_mut().next.take().unwrap();
//             // `node.prev` is the new end of the current list.
//             let old_last_node = match self.list {
//                 List::NonEmpty { last_node, .. } => mem::replace(last_node, prev),
//                 // We have a node so the list isn't empty.
//                 List::Empty => unreachable!(),
//             };
//             List::NonEmpty {
//                 first_node: node,
//                 last_node: old_last_node,
//             }
//         } else {
//             // The pointed-to node has no predecessor: we must be at the start of the list.
//             mem::replace(self.list, List::Empty)
//         }
//     }
//     /// Remove the current node and return its value.
//     pub fn take(&mut self) -> Option<u32> {
//         let mut split_list = self.split();
//         let val = split_list.pop_front()?;
//         self.node = split_list.first_node().map(BiOwned1::alias);
//         self.list.append(split_list);
//         Some(val)
//     }
//     /// Insert this value after the cursor and advance the cursor to that new value.
//     pub fn insert(&mut self, val: u32) {
//         let split_list = self.split();
//         self.list.push(val);
//         self.node = self.list.last_node().cloned();
//         self.list.append(split_list);
//     }
// }

impl Debug for List<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vec: Vec<_> = self.start().collect();
        write!(f, "{vec:?}")?;
        Ok(())
    }
}

#[test]
fn test() {
    fn display(tag: &str, list: &List<'_>) {
        let fwd: Vec<_> = list.start().collect();
        println!("{tag: <15}: {fwd:?}");
        // Double-reverse to check that the `prev` pointers are good.
        let mut bwd: Vec<_> = list.end().rev().collect();
        bwd.reverse();
        assert_eq!(fwd, bwd);
    }
    GhostToken::new(|token| {
        let mut list = List::new(token);
        for i in 0..10 {
            list.push(i);
        }
        display("start", &list);

        // let mut cursor = list.start_mut();
        // cursor.forward();
        // cursor.forward();
        // cursor.backward();
        // cursor.forward();
        // *cursor.val().unwrap() = 42;
        // display("edit", cursor.list());

        // cursor.forward();
        // let _ = cursor.take();
        // display("take", cursor.list());

        // cursor.insert(43);
        // display("insert", &list);

        // // Take from the end.
        // let mut cursor = list.end_mut();
        // cursor.backward();
        // let _ = cursor.take();
        // display("remove last", &list);

        // // Take from the start.
        // let mut cursor = list.start_mut();
        // let _ = cursor.take();
        // display("remove first", &list);

        let vec: Vec<_> = list.start().copied().collect();
        assert_eq!(vec, vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
        // assert_eq!(vec, vec![1, 42, 43, 4, 5, 6, 7, 8]);
    })
}
