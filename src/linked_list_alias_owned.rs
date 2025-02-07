use std::{cell::RefCell, fmt::Debug, mem};

use crate::alias_owned::{AliasOwn, Weak};

// struct AliasOwn<tag, T>(..);
// impl<tag, T> AliasOwn<tag, T> {
//     pub fn alias(&self) -> Weak<tag, T> {..}
// }

// type Node<prev, cur, last> = RefCell<NodeInner<prev, cur, last>>;
// enum NodeInner<prev, cur, last> {
//     LastNode where last = cur {
//         val: u32,
//         // `unknown` is ok because we never take ownership of the relevant `Weak`s through
//         // this pointer.
//         prev: Option<Weak<prev, Node<unknown, unknown, last>>>,
//     }
//     InnerNode where exists<next> {
//         val: u32,
//         next: AliasOwn<next, Node<cur, next, last>>,
//         // `unknown` is ok because we never take ownership of the relevant `Weak`s through
//         // this pointer.
//         prev: Option<Weak<prev, Node<unknown, unknown, last>>>,
//     }
// }
// enum List {
//     Empty,
//     NonEmpty where exists<first, last> {
//         first_node: AliasOwn<first, Node<None, first, last>>,
//         // `unknown` is ok because we never take ownership of the relevant `Weak`s through
//         // this pointer.
//         last_node: Weak<last, Node<unknown, unknown, last>>,
//     },
// }
type Node = RefCell<NodeInner>;
pub struct NodeInner {
    val: u32,
    next: Option<AliasOwn<Node>>,
    // Invariant: this points to the previous node, if any.
    prev: Option<Weak<Node>>,
}

#[derive(Default)]
pub enum List {
    #[default]
    Empty,
    NonEmpty {
        first_node: AliasOwn<Node>,
        last_node: Weak<Node>,
    },
}

impl List {
    pub fn new() -> Self {
        List::default()
    }

    // Internal helper.
    fn first_node(&self) -> Option<&AliasOwn<Node>> {
        match self {
            List::Empty => None,
            List::NonEmpty { first_node, .. } => Some(first_node),
        }
    }
    // Internal helper.
    fn last_node(&self) -> Option<&Weak<Node>> {
        match self {
            List::Empty => None,
            List::NonEmpty { last_node, .. } => Some(last_node),
        }
    }

    /// Add an element to the end of the list.
    pub fn push(&mut self, val: u32) {
        let new = AliasOwn::new(RefCell::new(NodeInner {
            val,
            next: None,
            prev: self.last_node().cloned(),
        }));
        self.append(List::NonEmpty {
            last_node: new.alias(),
            first_node: new,
        });
    }
    pub fn append(&mut self, other: Self) {
        match (&mut *self, other) {
            (_, List::Empty) => {}
            (List::Empty, other) => *self = other,
            (
                List::NonEmpty {
                    last_node: self_last,
                    ..
                },
                List::NonEmpty {
                    first_node: other_first,
                    last_node: other_last,
                },
            ) => {
                let old_last = mem::replace(self_last, other_last);
                other_first.borrow_mut().prev = Some(old_last.clone());
                old_last.borrow().borrow_mut().next = Some(other_first);
            }
        }
    }
    /// Remove the first element.
    pub fn pop_front(&mut self) -> Option<u32> {
        match mem::replace(self, List::Empty) {
            List::Empty => None,
            List::NonEmpty {
                first_node,
                last_node,
            } => {
                // `into_inner` is ok because this is the only pointer to that node.
                let node = first_node.into_inner().into_inner();
                if let Some(next) = node.next {
                    next.borrow_mut().prev = None;
                    *self = List::NonEmpty {
                        first_node: next,
                        last_node,
                    }
                }
                Some(node.val)
            }
        }
    }

    pub fn start(&self) -> ListCursor<'_> {
        ListCursor {
            node: self.first_node().map(AliasOwn::alias),
            list: self,
        }
    }
    pub fn start_mut(&mut self) -> ListCursorMut<'_> {
        ListCursorMut {
            node: self.first_node().map(AliasOwn::alias),
            list: self,
        }
    }
    pub fn end(&self) -> ListCursor<'_> {
        ListCursor {
            node: Default::default(),
            list: self,
        }
    }
    pub fn end_mut(&mut self) -> ListCursorMut<'_> {
        ListCursorMut {
            node: Default::default(),
            list: self,
        }
    }
}

/// A cursor into a list. Points in-between nodes, which includes the start (before all nodes) and
/// the end (after all nodes); `val()` returns the value of the next node.
pub struct ListCursor<'a> {
    node: Option<Weak<Node>>,
    list: &'a List,
}

impl<'a> ListCursor<'a> {
    pub fn val(&self) -> Option<&'a u32> {
        let val_ptr = self.node.as_ref()?.borrow().as_ptr();
        // # Safety: the list is borrowed for `'a` and no operation on the list or the cursor
        // mutates the list.
        Some(unsafe { &(*val_ptr).val })
    }
    /// Move the cursor forward. Returns `None` if we were already at the end of the list.
    pub fn forward(&mut self) -> Option<()> {
        let node = self.node.as_ref()?;
        let next = node.borrow().borrow().next.as_ref().map(AliasOwn::alias);
        self.node = next;
        self.check_local_consistency();
        Some(())
    }
    /// Move the cursor backward. Returns `None` if we were already at the start of the list.
    pub fn backward(&mut self) -> Option<()> {
        let prev = match &self.node {
            None => self.list.last_node()?.clone(),
            Some(node) => node.borrow().borrow().prev.clone()?,
        };
        self.node = Some(prev);
        self.check_local_consistency();
        Some(())
    }
    pub fn check_local_consistency(&self) {
        if let Some(node) = &self.node {
            let node = node.borrow();
            if let Some(next) = node.borrow().next.as_ref() {
                let node2 = &next.borrow().prev;
                assert!(
                    node.ptr_eq(node2.as_ref().unwrap()),
                    "at node {}: node.next.prev != node",
                    node.borrow().val
                )
            } else {
                assert!(
                    node.ptr_eq(&self.list.last_node().unwrap()),
                    "node {} has no next but should",
                    node.borrow().val
                );
            }
            if let Some(prev) = &node.borrow().prev {
                let prev = prev.borrow();
                let node2 = &prev.borrow().next;
                assert!(
                    node.ptr_eq(&node2.as_ref().unwrap().alias()),
                    "at node {}: node.prev.next != node",
                    node.borrow().val
                )
            } else {
                let first = self.list.first_node().unwrap();
                assert!(
                    node.ptr_eq(&first.alias()),
                    "node {} has no prev but should",
                    node.borrow().val
                );
            }
        }
    }
}

impl<'a> Iterator for ListCursor<'a> {
    type Item = &'a u32;
    fn next(&mut self) -> Option<Self::Item> {
        let val = self.val();
        self.forward()?;
        val
    }
}

impl<'a> DoubleEndedIterator for ListCursor<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.backward()?;
        self.val()
    }
}

/// A cursor into a list. Points in-between nodes, which includes the start (before all nodes) and
/// the end (after all nodes); `val()` returns the value of the next node.
pub struct ListCursorMut<'a> {
    node: Option<Weak<Node>>,
    list: &'a mut List,
}

impl ListCursorMut<'_> {
    /// Note: the return value is valid for the lifetime of the `self` borrow, not for `'a`, since
    /// we can move forwards and backwards.
    pub fn val(&mut self) -> Option<&mut u32> {
        let val_ptr = self.node.as_ref()?.borrow().as_ptr();
        // # Safety: we have an exclusive borrow on `self` and transitively on the list, so no
        // other borrow is accessible.
        Some(unsafe { &mut (*val_ptr).val })
    }
    /// Observe the underlying list.
    pub fn list(&self) -> &List {
        &self.list
    }

    /// Move the cursor forward. Returns `None` if we were already at the end of the list.
    pub fn forward(&mut self) -> Option<()> {
        let node = self.node.as_ref()?;
        let next = node.borrow().borrow().next.as_ref().map(AliasOwn::alias);
        self.node = next;
        Some(())
    }
    /// Move the cursor backward. Returns `None` if we were already at the start of the list.
    pub fn backward(&mut self) -> Option<()> {
        let prev = match &self.node {
            None => self.list.last_node()?.clone(),
            Some(node) => node.borrow().borrow().prev.clone()?,
        };
        self.node = Some(prev);
        Some(())
    }

    /// Split the list at the cursor. Returns a list containing all the nodes after the cursor.
    pub fn split(&mut self) -> List {
        let Some(node) = self.node.take() else {
            return List::default();
        };
        let node = node.borrow();
        if let Some(prev) = node.borrow_mut().prev.take() {
            // The pointed-to node has a predecessor: we get ownership of the node, which is owned
            // by its predecessor. Unwrap is ok by the invariant that self.prev.next == self.
            let node = prev.borrow().borrow_mut().next.take().unwrap();
            // `node.prev` is the new end of the current list.
            let old_last_node = match self.list {
                List::NonEmpty { last_node, .. } => mem::replace(last_node, prev),
                // We have a node so the list isn't empty.
                List::Empty => unreachable!(),
            };
            List::NonEmpty {
                first_node: node,
                last_node: old_last_node,
            }
        } else {
            // The pointed-to node has no predecessor: we must be at the start of the list.
            mem::replace(self.list, List::Empty)
        }
    }
    /// Remove the current node and return its value.
    pub fn take(&mut self) -> Option<u32> {
        let mut split_list = self.split();
        let val = split_list.pop_front()?;
        self.node = split_list.first_node().map(AliasOwn::alias);
        self.list.append(split_list);
        Some(val)
    }
    /// Insert this value after the cursor and advance the cursor to that new value.
    pub fn insert(&mut self, val: u32) {
        let split_list = self.split();
        self.list.push(val);
        self.node = self.list.last_node().cloned();
        self.list.append(split_list);
    }
}

impl Debug for List {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vec: Vec<_> = self.start().collect();
        write!(f, "{vec:?}")?;
        Ok(())
    }
}

#[test]
fn test() {
    let display = |tag: &str, list: &List| {
        println!("{tag: <15}: {list:?}");
        // Double-reverse to check that the `prev` pointers are good.
        let fwd: Vec<_> = list.start().collect();
        let mut bwd: Vec<_> = list.end().rev().collect();
        bwd.reverse();
        assert_eq!(fwd, bwd);
    };

    let mut list = List::new();
    for i in 0..10 {
        list.push(i);
    }
    display("start", &list);

    let mut cursor = list.start_mut();
    cursor.forward();
    cursor.forward();
    cursor.backward();
    cursor.forward();
    *cursor.val().unwrap() = 42;
    display("edit", cursor.list());

    cursor.forward();
    let _ = cursor.take();
    display("take", cursor.list());

    cursor.insert(43);
    display("insert", &list);

    // Take from the end.
    let mut cursor = list.end_mut();
    cursor.backward();
    let _ = cursor.take();
    display("remove last", &list);

    // Take from the start.
    let mut cursor = list.start_mut();
    let _ = cursor.take();
    display("remove first", &list);

    let vec: Vec<_> = list.start().copied().collect();
    assert_eq!(vec, vec![1, 42, 43, 4, 5, 6, 7, 8]);
}
