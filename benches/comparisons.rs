#![allow(dead_code)]
#![feature(test, allocator_api, generic_associated_types)]
extern crate fastrand;
extern crate petgraph;
extern crate test;
extern crate itertools;
use itertools::{Itertools};
use fastrand::Rng;
use graph_shrine::{AdjacencyList, CSRPlusPlus, Graph};
use test::Bencher;
use petgraph::{adj, csr::Csr, visit::{IntoNeighbors, NodeCount}};
use std::{slice, iter, collections::HashMap};



// impl<G, K,V,E> Wander<K> for G where G:Graph<K,V,E, Index = K>, K:Clone {
//     fn wander(from:K, r:&mut Rng)-> K {
//         let mut cur = from.clone();
//         for _ in 0..hops {
//             let oe = v.out_edges(cur.clone()).unwrap();
//             let oel = oe.len();
//             if oel == 0 {
//                 return cur;
//             };
//             cur = oe.skip(r.usize(0..oel)).next().unwrap().0;
//         }
//         cur
//     }
// }




trait Works<K:Clone> {
    type OutEdges<'a>: ExactSizeIterator<Item= K> where K: 'a;
    fn edges<'a>(&'a self, from:K)-> Self::OutEdges<'a>;
    fn random_vertex(&self, r:&mut Rng)-> K;
    // fn set_edge(&mut self, from:K, to:K);
    // fn into_id(&self, v:usize)-> K;
    // fn from_edge_iter(
    //     noden: usize,
    //     edges: impl Iterator<Item = (usize, usize)>,
    // )-> Self where Self: Sized {
    //     use graph_shrine::ALVert;
    //     let vertexes:Vec<_> = (0..noden).map(|i| ALVert{
    //         k:i,
    //         v:(),
    //         deleted: false,
    //         out_edges: Vec::new(),
    //         in_edges: Vec::new(),
    //     }).collect();
    //     let mut mapping = HashMap::new();
    //     for at in 0..vertexes.len() {
    //         mapping.insert(at, at);
    //     }
    //     let mut al = AdjacencyList::<usize, (), ()> {
    //         mapping,
    //         vertexes,
    //         total_live_vertices: noden,
    //     };
    //     for (from, to) in edges {
    //         Graph::set_edge(&mut al, from, to, (), false);
    //     }
    //     Self::from(&al)
    // }
}


// struct MapOutIter<I>(I);
// impl<I, E, Index> Iterator for MapOutIter<I> where I:Iterator<Item=(Index, E)> {
//     type Item = Index;
//     fn next(&mut self)-> Option<Self::Item> {
//         self.0.next().map(|(i,_)| i)
//     }
// }

struct WorkGraph<G>(G);

impl<K, G> Works<K> for WorkGraph<G> where G:Graph<usize,(),(), Index=K>, K: Clone + Eq {
    // type OutEdges<'a> = MapOutIter<<Self as Graph<usize,(),()>>::OutIter<'a>>;
    type OutEdges<'a> where K: 'a = iter::Map<
        <G as Graph<usize,(),()>>::OutIter<'a>,
        fn((K, &'a ()))-> K
    >;
    fn edges<'a>(&'a self, from:K)-> Self::OutEdges<'a> {
        self.0.out_edges(from).unwrap().map(|(k,_)| k)
    }
    // fn into_id(&self, v:usize)-> K { Graph::<usize,(),()>::into_id(&self.0, v) }
    fn random_vertex(&self, r:&mut Rng)-> K {
        self.0.random_vertex(r)
    }
}

impl Works<u32> for adj::List<()> {
    type OutEdges<'a> = adj::Neighbors<'a, (), u32>;
    // fn from(v:&AdjacencyList<usize, (), ()>)-> Self {
    //     let mut r = adj::List::with_capacity(v.vertex_count());
    //     for alv in v.vertexes.iter() {
    //         r.add_node_from_edges(alv.out_edges.iter().map(|&(n,_)| (n as u32, ())));
    //     }
    //     r
    // }
    fn edges<'a>(&'a self, from:u32)-> Self::OutEdges<'a> {
        self.neighbors(from)
    }
    fn random_vertex(&self, r:&mut Rng)-> u32 {
        r.usize(0..self.node_count()) as u32
    }
}



fn random_graph(
    r: &mut Rng,
    node_count: usize,
    proportion_of_edges: f64,
    additional_mandatory_edge_per_node: bool,
) -> Vec<(usize, usize)>
{
    let edge_add_n = (node_count as f64 * proportion_of_edges) as usize;
    let mut edges:Vec<(usize, usize)> = (0..edge_add_n).map(|_|{
        let firsti = r.usize(0..node_count);
        (
            firsti,
            (firsti + r.usize(1..(node_count - 1))) % node_count
        )
    }).collect();
    
    if additional_mandatory_edge_per_node {
        for i in 0..node_count {
            let secondi = (i + r.usize(1..(node_count - 1))) % node_count;
            edges.push((i, secondi));
        }
    }
    edges
}

fn wander<'a, G, K, V, E>(v: &'a G, r: &mut Rng, from: G::Index, hops: usize) -> G::Index
where
    G: Graph<K, V, E>,
    G::Index: Clone,
{
    let mut cur = from.clone();
    for _ in 0..hops {
        let oe = v.out_edges(cur.clone()).unwrap();
        let oel = oe.len();
        if oel == 0 {
            return cur;
        };
        cur = oe.skip(r.usize(0..oel)).next().unwrap().0;
    }
    cur
}

fn graph_prep(r: &mut Rng) -> Vec<(usize,usize)>
{
    random_graph(r, 70000, 12.0, true)
}
fn bench_graph_wander<G>(b: &mut Bencher, g: &G, r: &mut Rng)
where
    G: Graph<usize, (), ()>,
    G::Index: Clone,
{
    b.iter(|| {
        let mut ro = r.clone();
        let rv = g.random_vertex(&mut ro);
        wander(g, &mut ro, rv, 300)
    })
}

#[bench]
fn wander_adjacency_list(b: &mut Bencher) {
    let mut r = Rng::with_seed(40);
    let edges = graph_prep(&mut r);
    let nv = (0..edges.len()).map(|i| (i, ()));
    let g = AdjacencyList::from_edges(nv, edges.iter().map(|&(a,b)| (a, b, ())));
    bench_graph_wander(b, &g, &mut r);
}

// #[bench]
// fn wander_petgraph_adjacency_list(b: &mut Bencher) {
//     let mut r = Rng::with_seed(40);
//     let edges = graph_prep(&mut r);
//     let nv = (0..edges.len()).map(|i| (i, ()));
//     let g = adj::List::from_edges(nv, edges.iter().map(|&(a,b)| (a, b, ())));
//     bench_graph_wander(b, &g, &mut r);
// }

// #[bench]
// fn wander_adjacency_list(b: &mut Bencher) {
//     let mut r = Rng::with_seed(40);
//     let edges = graph_prep(&mut r);
//     let nv = (0..ei.len()).map(|i| (i, ()));
//     let g = AdjacencyList::from_edges(nv, ei.iter().map(|&(a,b)| (a, b, ())));
//     bench_graph_wander::<AdjacencyList<usize, (), ()>>(b, &g, &mut r);
// }

// #[bench]
// fn wander_csrpp(b: &mut Bencher) {
//     let mut r = Rng::with_seed(40);
//     bench_graph_wander::<CSRPlusPlus<usize, (), ()>>(b, &graph_prep(&mut r), &mut r);
// }

#[bench]
fn wander_patterned_csrpp(b: &mut Bencher) {
    let mut r = Rng::with_seed(40);
    let edges = graph_prep(&mut r);
    let nv = (0..edges.len()).map(|i| (i, ()));
    let ug: CSRPlusPlus<usize, (), ()> = CSRPlusPlus::from_edges(nv, edges.iter().map(|&(a,b)| (a,b,())));
    let g = CSRPlusPlus::from_graph_with_radial_patterning(&ug, (), std::alloc::Global::default());
    bench_graph_wander(b, &g, &mut r);
}

// #[bench]
// fn wander_csrpp(b: &mut Bencher) {
// 	bench_graph_wander::<CSRPlusPlus<usize, (), ()>>(b);
// }

// #[bench]
// fn wander_patterned_csrpp(b: &mut Bencher) {
//     bench_graph_wander::<CSRPlusPlus<usize, (), ()>>(b);
// }
