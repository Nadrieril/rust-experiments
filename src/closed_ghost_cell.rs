//! See https://github.com/matthieu-m/ghost-cell/issues/36.
use std::{
    collections::HashSet,
    marker::PhantomData,
    rc::{Rc, Weak},
};

use ghost_cell::{GhostCell, GhostToken};
use higher_kinded_types::ForLt;

pub struct ClosedGhostCellContainer<C: ForLt> {
    // This lifetime is a lie.
    container: C::Of<'static>,
}
impl<C: ForLt> ClosedGhostCellContainer<C> {
    // The output lifetime needs to be mentioned in the output, hence the `PhantomData`.
    pub fn new(f: impl for<'brand> FnOnce(PhantomData<&'brand ()>) -> C::Of<'brand>) -> Self {
        Self {
            container: f(PhantomData),
        }
    }
    pub fn open_ref<R>(
        &self,
        f: impl for<'brand> FnOnce(&C::Of<'brand>, &GhostToken<'brand>) -> R,
    ) -> R {
        GhostToken::new(|token| {
            // Safety: uhhh
            let container_ref: &C::Of<'_> = unsafe { std::mem::transmute(&self.container) };
            f(container_ref, &token)
        })
    }
    pub fn open_mut<R>(
        &mut self,
        f: impl for<'brand> FnOnce(&mut C::Of<'brand>, &mut GhostToken<'brand>) -> R,
    ) -> R {
        GhostToken::new(|mut token| {
            // Safety: uhhh
            let container_ref: &mut C::Of<'_> = unsafe { std::mem::transmute(&mut self.container) };
            f(container_ref, &mut token)
        })
    }
}

struct MyGraphOpen<'brand> {
    nodes: Vec<Rc<GhostCell<'brand, Node<'brand>>>>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(usize);

type NodeRef<'brand> = Weak<GhostCell<'brand, Node<'brand>>>;
struct Node<'brand> {
    name: &'static str,
    edges: Vec<NodeRef<'brand>>,
}

impl<'brand> MyGraphOpen<'brand> {
    pub fn new() -> Self {
        Self { nodes: vec![] }
    }

    pub fn add_node(&mut self, name: &'static str) -> NodeId {
        let node_id = NodeId(self.nodes.len());
        let node = Rc::new(GhostCell::new(Node {
            name,
            edges: vec![],
        }));
        self.nodes.push(node);
        node_id
    }
    pub fn add_edge(&mut self, token: &mut GhostToken<'brand>, from: NodeId, to: NodeId) {
        let to = Rc::downgrade(&self.nodes[to.0]);
        let from = &self.nodes[from.0];
        from.borrow_mut(token).edges.push(to);
    }

    pub fn dfs_iter(&self, token: &GhostToken<'brand>) -> impl Iterator<Item = &'static str> {
        let mut to_visit = vec![];
        let mut visited: HashSet<*const _> = HashSet::with_capacity(self.nodes.len());
        if let Some(first) = self.nodes.first() {
            to_visit.push(first.clone());
            visited.insert(first.as_ptr());
        }
        std::iter::from_fn(move || {
            let node = to_visit.pop()?;
            let node = node.borrow(token);
            for neighbor in node.edges.iter().rev() {
                let neighbor = neighbor.upgrade().unwrap();
                if visited.insert(neighbor.as_ptr()) {
                    to_visit.push(neighbor);
                }
            }
            Some(node.name)
        })
    }
}

pub struct MyGraph(ClosedGhostCellContainer<ForLt!(MyGraphOpen<'_>)>);

impl MyGraph {
    pub fn new() -> Self {
        MyGraph(ClosedGhostCellContainer::new(|_| MyGraphOpen::new()))
    }

    pub fn add_node(&mut self, name: &'static str) -> NodeId {
        self.0.open_mut(|graph, _token| graph.add_node(name))
    }
    pub fn add_edge(&mut self, from: NodeId, to: NodeId) {
        self.0
            .open_mut(|graph, token| graph.add_edge(token, from, to))
    }
    pub fn dfs(&self, mut callback: impl FnMut(&'static str)) {
        self.0.open_ref(|graph, token| {
            for name in graph.dfs_iter(token) {
                callback(name)
            }
        })
    }
}

#[test]
fn test_graph() {
    let mut graph = MyGraph::new();
    let a = graph.add_node("A");
    let b = graph.add_node("B");
    let c = graph.add_node("C");
    let d = graph.add_node("D");
    graph.add_edge(a, b);
    graph.add_edge(b, c);
    graph.add_edge(c, a);
    graph.add_edge(a, d);

    let mut names = vec![];
    graph.dfs(|name| names.push(name));
    assert_eq!(names, vec!["A", "B", "C", "D"]);
}
