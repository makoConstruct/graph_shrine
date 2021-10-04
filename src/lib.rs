#![feature(
    result_into_ok_or_err,
    associated_type_defaults,
    destructuring_assignment,
    default_free_fn,
    allocator_api,
)]
#![allow(dead_code, unused_imports)]
// implementation of CSR++: DOI:10.4230/LIPIcs.OPODIS.2020.17
extern crate bitvec;
extern crate parking_lot;
extern crate vec_with_gaps;
extern crate itertools;
extern crate left_right;

use itertools::Itertools;
use bitvec::vec::{BitVec};
use fastrand::Rng;
use std::{
  error::Error,
  fmt,
  fmt::{Debug, Display, Formatter},
    cmp::{Ordering, Ordering::*},
    collections::{hash_map::Entry::*, HashMap, HashSet, VecDeque, BinaryHeap},
    hash::Hash,
    iter,
    iter::{ExactSizeIterator, Iterator, Peekable},
    alloc,
    alloc::Allocator,
    mem::{drop, replace, size_of},
    ptr, slice,
    default::default,
    vec::Vec,
};
use vec_with_gaps::{ VecWithGaps, VecWithGapsConfig };
// use left_right::{Absorb, ReadHandle, WriteHandle};

pub struct AdjacencyList<K, V, E> {
    mapping: HashMap<K, usize>,
    vertexes: Vec<ALVert<K, V, E>>,
}
struct ALVert<K, V, E> {
    k: K,
    v: V,
    out_edges: Vec<(usize, E)>,
    in_edges: Vec<usize>,
}

fn binary_insert_if_first_element_not_present<V: Clone + Ord, W>(vs: &mut Vec<(V, W)>, p: (V, W)) {
    match vs.binary_search_by_key(&p.0, |pp| pp.0.clone()) {
        Ok(_) => {}
        Err(i) => {
            vs.insert(i, p);
        }
    }
}

fn binary_insert_if_first_element_not_present_else_replace_second<V: Clone + Ord, W: Clone>(vs: &mut Vec<(V, W)>, p: (V, W)) {
    match vs.binary_search_by_key(&p.0, |pp| pp.0.clone()) {
        Ok(i) => {
          vs[i].1 = p.1.clone();
        }
        Err(i) => {
            vs.insert(i, p);
        }
    }
}

fn binary_insert_if_not_present<V: Ord>(vs: &mut Vec<V>, p: V)-> bool {
    match vs.binary_search(&p) {
        Ok(_) => { false }
        Err(i) => {
            vs.insert(i, p);
            true
        }
    }
}

//safe iff indices are disjoint
// unsafe fn simultanious_mut_get<'d, T>(
//     indices: impl Iterator<Item=usize>,
//     data: &'d mut [T],
// ) -> impl Iterator<Item = &'d mut T> {
//     let start = data.as_mut_ptr();
//     let len = data.len();
//     indices.map(move |i|{
//       if i >= len { panic!("index out of bounds in simultanious_mut_get"); }
//       {
//         &mut *start.add(i)
//       }
//     })
// }

impl<K:Hash + Eq + Clone, V: Clone, E: Clone> AdjacencyList<K, V, E> {
    /// by the way, nodes don't have to be specified if they're present in an edge
    pub fn from_edges<'a, I, IE>(nodes: I, edges: IE) -> Self
    where
        V: 'a,
        E: 'a,
        I: Iterator<Item = (K, &'a V)> + Clone,
        IE: Iterator<Item = (K, K, &'a E)> + Clone,
    {
        let mut vertex_mapping = HashMap::<K, usize>::new();
        let mut vertexes:Vec<ALVert<_,_,_>> = Vec::new();
        let vmm = &mut vertex_mapping;
        let vm = &mut vertexes;
        let mut consider_inserting = |k: K, v:&V| {
            match vmm.entry(k.clone()) {
              Occupied(ref mut oe)=>{
                let i = *oe.get();
                vm[i].v = v.clone();
              }
              Vacant(ve)=>{
                ve.insert(vm.len());
                vm.push(ALVert {
                    k: k.clone(),
                    v: v.clone(),
                    out_edges: Vec::new(),
                    in_edges: Vec::new(),
                });
              }
            }
        };

        for (k, v) in nodes.clone() {
            consider_inserting(k.clone(), v);
        }
        
        for vp in edges {
            let fromu: usize = vertex_mapping[&vp.0];
            let tou: usize = vertex_mapping[&vp.1];
            binary_insert_if_first_element_not_present(
                &mut vertexes[fromu].out_edges,
                (fromu, vp.2.clone()),
            );
            binary_insert_if_not_present(&mut vertexes[tou].in_edges, fromu);
        }
        Self {
            mapping: vertex_mapping,
            vertexes: vertexes,
        }
    }
    
    pub fn from_sized_iters(
      i: impl ExactSizeIterator<Item=(
        K,
        V,
        impl ExactSizeIterator<Item=(K, E)>
      )> + Clone,
    )-> Self
    {
      let mapping: HashMap<K,usize> = i.clone().enumerate().map(|(index, (k, _, _))| (k, index)).collect();
      let mut in_edges: Vec<Vec<usize>> = (0..i.len()).map(|_| Vec::new()).collect();
      let mut vertexes: Vec<ALVert<K,V,E>> = i.enumerate().map(|(index, (k, v, edge_i))| {
        let out_edges = edge_i.map(|(ov, e)|{
          let out_vertex_index = mapping[&ov];
          in_edges[out_vertex_index].push(index);
          (out_vertex_index, e)
        }).collect();
        ALVert{
          k,
          v,
          out_edges,
          in_edges: Vec::new(),
        }
      }).collect();
      for (v, ie) in vertexes.iter_mut().zip(in_edges) {
        v.in_edges = ie;
      }
      Self{
        mapping,
        vertexes,
      }
    }
    
    pub fn add_edge(&mut self, from:usize, to:usize, w:E){
      
      self.vertexes[from].out_edges.push((to, w));
      self.vertexes[to].in_edges.push(from);
    }
    pub fn add_sorted_edge(&mut self, from:usize, to:usize, w:E){
      binary_insert_if_first_element_not_present_else_replace_second(&mut self.vertexes[from].out_edges, (to, w));
      binary_insert_if_not_present(&mut self.vertexes[to].in_edges, from);
    }
    pub fn add_sorted_biedge(&mut self, from:usize, to:usize, w:E){
      let mut over = |from:usize, to:usize|{
        binary_insert_if_first_element_not_present_else_replace_second(&mut self.vertexes[from].out_edges, (to, w.clone()));
        binary_insert_if_not_present(&mut self.vertexes[to].in_edges, from);
      };
      over(from, to);
      over(to, from);
    }
    pub fn add_biedge(&mut self, a:usize, b:usize, w:E){
      let va = &mut self.vertexes[a];
      va.out_edges.push((b, w.clone()));
      va.in_edges.push(b);
      let vb = &mut self.vertexes[b];
      vb.out_edges.push((a, w.clone()));
      vb.in_edges.push(a);
    }
    
}
impl<K> AdjacencyList<K, f64, f64> {
  fn add_weight_accumulating_sorted_biedge(&mut self, a:usize, b:usize, weight:f64) {
    let mut over = |from:usize, to:usize|{
      let an = &mut self.vertexes[from];
      let dif = match an.out_edges.binary_search_by(|&(o,_)| o.cmp(&from)) {
        Ok(i)=> {
          let anr = &mut an.out_edges[i];
          let r = weight - anr.1;
          anr.1 = weight;
          r
        }
        Err(i)=> {
          an.out_edges.insert(i, (to, weight));
          weight
        }
      };
      an.v += dif;
      binary_insert_if_not_present(&mut an.in_edges, to);
    };
    
    over(a, b);
    over(b, a);
  }
}

//TODO: try HeaderVecing everything
pub enum Edit<K, V, E> {
    NewVertex(K, V),
    NewEdge(EdgeAdd<E>),
    DeleteVertex(K),
    DeleteDirectedEdges{ from:K, to:K },
}
use Edit::*;

pub struct EdgeAdd<E> {
    pub from: VAddr,
    pub to: VAddr,
    pub weight: E,
}

//TODO: try HeaderVecing everything

//leftover from when I was going to replicate the functionality of left-right myself
// struct CSRPlusPlus<'a, V, E, Conf> {
//   a: RwLock<CSRPlusPlusWrite<V, E, Conf>>,
//   b: RwLock<CSRPlusPlusWrite<V, E, Conf>>,
//   which: AtomicBool, //b is the write iff true
// }

// fn start_switching(&mut self){
//   let _ = self.switch_mutex.lock(); //just to make sure two switches can't happen at the same time x]
//   let (was_read, was_write) = if which.read() {
//     (&self.a, &self.b)
//   }else{
//     (&self.b, &self.a)
//   };
//   //evict lingering readers and prepare for writing
//   unsafe{ forget(was_read.superlock.acquire_write()) }
//   for s in was_read.segments.iter() {
//     unsafe{ s.read_unlock() }
//   }

//   //evict lingering writers and prepare for reading
//   for s in was_write.segments.iter() {
//     unsafe{ forget(s.read_acquire()) }
//   }
//   {
//     //replicate changes
//     let bwl = was_write.buffered_writes.lock()
//     was_read.apply(was_write.compiled_committed_writes)
//     was_read.buffered_writes.replicate(bwl)
//   }
//   unsafe{ was_write.superlock.release_write() }

//   //TODO: Replicate changes to the mapping hashmap with a simple copy iff it expanded since the last sync, otherwise repeat the insertions

//   self.which.fetch_xor(true);
// }

// fn read_segment<'a>(&'a self)-> RwLockReadGuard<'a, Segment<V,E>> {
//   if which {
//     a
//   }
// }

/// note, each segment was supposed to have a lock on it for parallel editing. I haven't put the locks in yet, because my use case is extremely read-heavy, wants to be lock-free most of the time
/// K: keys, unique IDs the nodes are known by outside of the db
/// V: values stored at each node
/// E: weights stored on each of the edges, 
#[derive(Clone)]
pub struct CSRPlusPlus<K, V, E, C:CSRPPTuning = (), A:Allocator = alloc::Global> {
    pub segments: Vec<Segment<K, V, E, A>>,
    pub mapping: HashMap<K, VAddr>,
    pub deletion_load: usize, //the number of vertices known to have been quick deleted (if deletion_load/total_live_vertices > 2.5, you might want to do a reindexing)
    pub total_live_vertices: usize, //the number of vertices known to be present since the last sync
    pub config: C,
    pub allocator: A,
}

/// A configuration of how some of the details behave
pub trait CSRPPTuning: Clone {
    /// the size in memory of the segments (capacity is calculated from this)
    fn segment_size(&self) -> usize {
        1024 / size_of::<vec_with_gaps::VWGSection>()
    }
    /// the proportion of each segment that is made empty, on loading the graph, to allow for expansion
    fn segment_extra(&self) -> f64 {
        0.16
    }
    /// the capacity allocated to an edge list that was empty on load
    fn edge_list_empty_capacity(&self) -> usize{
        4
    }
    /// the extra proportion of capacity allocated to edge lists on load to allow for expansion
    fn edge_list_load_extra_capacity(&self) -> f64{
        0.2
    }
    /// the extra proportion of capacity put at the very end of the edge list to allow for large tracts to be shifted over when one of the sublists needs to expand, without the entire DS being reallocated
    fn edge_list_extra_at_end_of_all(&self) -> f64{
        0.5
    }
    /// should be a little above average, it's used for capacity hints
    fn average_expected_cardinality(&self)-> f64 {
      4.0
    }
    // FEATURE: associated type defaults can't be defined in the trait? :/// generally aint baked #29661
    // type VecWithGapsConf: vec_with_gaps::VecWithGapsConfig = ();
    // FEATURE: can't use impls in trait methods
    // fn vec_with_gaps_conf(&self)-> impl Self::VecWithGapsConf {
    //   ()
    // }
}
impl CSRPPTuning for () {}
// struct CSRPPVWGConf()
// impl VecWithGapsConfig for CSRPPVWGConf {
//   fn 
// }
type VWGC = ();
const OUR_VEC_WITH_GAPS_CONF:VWGC = ();

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct VAddr {
    pub segment: u32,
    pub index: u32,
}
const INVALID_VADD: VAddr = VAddr {
    segment: u32::max_value(),
    index: u32::max_value(),
};
#[derive(Clone)]
pub struct Segment<K, V, E, A:Allocator> {
    //include a lock?
    pub live_count: usize, //note, vertices.len() doesn't always represent the number of vertices still alive, due to flag deletion
    pub external_vertex_ids: Vec<K>,
    pub vertex_weights: Vec<V>,
    pub out_edges: VecWithGaps<Edge<E>, VWGC, A>,
    pub in_edges: VecWithGaps<VAddr, VWGC, A>,
}
#[derive(Clone, Copy)]
pub struct BackEdge {
    pub from: VAddr,
}
#[derive(Clone)]
pub struct Edge<E> {
    pub to: VAddr,
    pub weight: E,
}
impl<V> PartialEq for Edge<V> {
    fn eq(&self, other: &Self) -> bool {
        self.to == other.to
    }
}
impl<V> Eq for Edge<V> {}
impl<V> PartialOrd for Edge<V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.to.cmp(&other.to))
    }
}
// struct Vertex {
//     out_edges_segment: u32,
//     in_edges_segment: u32,
//     out_edges_length: i32,
//     in_edges_length: i32,
// }
// impl Vertex {
//   fn deleted(&self)-> bool { self.out_edges_length == -1 }
// }
pub type Res<V> = Result<V, CSRPPError>;
trait Graph<'a, K, V, E>
where
    K: 'a,
    V: 'a,
    E: 'a,
{
    type InIter: ExactSizeIterator<Item = Self::Index> + Clone + 'a;
    type OutIter: ExactSizeIterator<Item = (Self::Index, &'a E)> + Clone + 'a;
    type Index: 'a = usize;
    fn next_id(&self) -> Self::Index; //needed for radial patterning. Must be greater than any vertex ID, and (for memory efficiency) should not be too much greater than the number of vertices in the structure, if it is, maybe regenerate your IDs.
    // fn vertex_count(&self) -> usize;
    fn vertexes(&self) -> Vec<Self::Index>;
    fn vertex_count(&self)-> usize;
    fn v(&self, at:Self::Index)-> Res<&V>;
    /// second val is true iff this was a new insertion
    fn set_vertex(&mut self, k:K, v:V)-> (Self::Index, bool) ;
    fn out_edges(&'a self, v: Self::Index) -> Res<Self::OutIter>;
    fn in_edges(&'a self, v: Self::Index) -> Res<Self::InIter>;
    /// (must point to a live vertex (is that obvious?))
    fn random_vertex_id(&self, r:&mut Rng)-> Self::Index;
    fn translate_from_k(&self, v:&K)-> Res<Self::Index>;
    fn translate_to_k(&self, v:&Self::Index)-> Res<K>;
}

impl<'a, K, V, E> Graph<'a, K, V, E> for AdjacencyList<K, V, E>
where
    Self: 'a,
    K: Debug + Clone + Hash + Eq,
{
  type InIter = iter::Cloned<slice::Iter<'a, Self::Index>>;
  type OutIter = iter::Map<
      slice::Iter<'a, (Self::Index, E)>,
      fn(&'a (Self::Index, E)) -> (Self::Index, &'a E),
  >;
  // fn vertex_count(&self) -> usize {
  //     self.vertexes.len()
  // }
  fn out_edges(&'a self, v: Self::Index) -> Res<Self::OutIter> {
      Ok(self.vertexes.get(v)
      .ok_or_else(|| NoAdjacencyIndex(v))?
          .out_edges
          .iter()
          .map(|(i, e)| (i.clone(), e)))
  }
  fn vertex_count(&self)-> usize { self.vertexes.len() }
  fn in_edges(&'a self, v: Self::Index) -> Res<Self::InIter> {
      Ok(self.vertexes.get(v)
      .ok_or_else(|| NoAdjacencyIndex(v))?
      .in_edges.iter().cloned())
  }
  fn translate_from_k(&self, v:&K)-> Res<Self::Index> {
    Ok(*self.mapping.get(v).ok_or_else(|| Misc(format!("Key {:?} does not correspond to an internal index", v)))?)
  }
  fn translate_to_k(&self, v:&Self::Index)-> Res<K> {
    self.vertexes.get(*v).ok_or_else(|| NoAdjacencyIndex(*v)).map(|v| v.k.clone())
  }
  fn next_id(&self) -> usize {
      self.vertexes.len()
  }
  fn v(&self, at:Self::Index)-> Res<&V> {
    self.vertexes.get(at).ok_or_else(|| NoAdjacencyIndex(at)).map(|a| &a.v)
  }
  fn vertexes(&self) -> Vec<Self::Index> {
      (0..self.vertexes.len()).collect()
  }
  fn random_vertex_id(&self, r:&mut Rng)-> Self::Index {
    r.usize(0..self.vertexes.len())
  }
  fn set_vertex(&mut self, k:K, v:V)-> (Self::Index, bool) {
    let r;
    let is_new = match self.mapping.entry(k.clone()) {
      Occupied(ref mut e)=> {
        r = *e.get();
        self.vertexes[r].v = v;
        false
      }
      Vacant(e)=> {
        r = self.vertexes.len();
        e.insert(r);
        self.vertexes.push(ALVert{
          k,
          v,
          out_edges: Vec::new(),
          in_edges: Vec::new(),
        });
        true
      }
    };
    (r, is_new)
  }
}
impl<K> AdjacencyList<K, f64, f64> where K: Debug + Clone + Hash + Eq {
    fn wander(&self, r:&mut Rng, from:usize, hops:usize)-> usize {
      let mut an = from;
      for _ in 0..hops {
        let mut fr = r.f64()*self.v(from).unwrap();
        let mut poe = self.out_edges(an).unwrap().peekable();
        while let Some(oe) = poe.next() {
          if fr < *oe.1 || poe.peek().is_none()  {
            an = oe.0;
            break;
          }
          fr -= oe.1;
        }
      }
      an
    }
}

//constant time sampling and removal from a bag of i..n, memory use is 8*n bytes
// struct Intrusivey {
//   mapping: Vec<u32>,
//   items: Vec<u32>,
// }

// impl Intrusivey {
//   fn new(n:usize)-> Self {
//     let m = (0..n).collect();
//     Intrusivey{
//       mapping: m.clone(),
//       items: m
//     }
//   }
//   fn has(&self, v:u32)-> bool { mapping[v] != -1 }
//   fn len(&self)-> usize { self.items.len() }
//   /// will panic if called when the bag is empty, will panic if called on an at out of bounds, do not call on the same at more than once
//   fn draw(&mut self, at:usize)-> u32 {
//     if at == self.items.len()-1 {
//       self.items.pop().unwrap()
//     }else{
//       let back = self.items.pop().unwrap();
//       let ret = self.items[at];
//       mapping[ret] = at;
//     }
//   }
// }

fn draw<V>(bag: &mut Vec<V>, r: &mut Rng) -> V {
    let at = r.usize(0..bag.len());
    if at != bag.len() - 1 {
        let back = bag.pop().unwrap();
        replace(&mut bag[at], back)
    } else {
        bag.pop().unwrap()
    }
}

// /// see below, this just passes some defaults
// fn create_radial_patterning<G:Graph>(v:& impl Graph)-> Vec<Vec<usize>> {
//   let bloom_size = 1024;
//   let rng = ..
//   create_radial_patterning_detailed(v, bloom_size, g.vertex_count()/bloom_size*2, |i|i, |i|i, &mut rng)
// }

/// takes a graph and returns a permutation on the vertices that, if the vertices in a CSR graph were arranged in this new order, the graph would have better performance in many basic graph operations, due to memory adjacency of related items
/// note, if your application has edge weights, you'll want a more complete implementation of radial patterning that takes them into account, as that often drastically effects the ordering in which nodes are accessed, the shape of the blooms will be different.
/// ultimately, this algorithm can only guess at general adjacency. To get the best possible patterning, you will need statistics about what roots the nodes are most often accessed from in reality.
/// `bloom_size`: the number of vertices that will be put in each cache line segment
// /// `sample_count_proportion`: the proportion of all vertices that will be sampled as bloom origins, should be very very small. A good rule of thumb is to use g.all_vertices().len()/bloom_size*2
/// `serialize`/`deserialize`: required for storing the seen vec. To be memory-efficient, the max usize generated by this should not be significantly greater than the number of vertices. If your indices can't easily be mapped to or from a tightly packed sequence like that, you'll have to implement another way of keeping the `seen` flags and the `unseen` draw bag, and it will be less efficient than this way I wanted to use. (although I'm not sure how much less efficient, for large inputs that weren't already radial-patterned, there will be cache misses just as often as there would be with a HashSet)
/// return value: The nodes ordered as a series of blooms, each exactly bloom_size long. To get an `Iterator<Item=&[Index]>` over the blooms, simply `return_value.chunks(bloom_size)`. Each thing in the return value is the index of the node in the original graph that would be in that position, in the patterned graph
fn create_radial_patterning_detailed<'a, Index: 'a, K, V, E>(
    g: &'a impl Graph<'a, K, V, E, Index = Index>,
    bloom_size: usize,
    serialize: impl Fn(Index) -> usize,
    r: &mut Rng,
) -> Vec<Index>
where
    K: Debug + 'a,
    V: 'a,
    E: 'a,
    Index: Clone,
{
    let mut unseen: Vec<Index> = g.vertexes();
    let mut seen = bitvec::bitvec![0;serialize(g.next_id())];
    let mut ret = Vec::with_capacity(seen.len());

    //TODO: try a more sophisticated one that does a BFS of BFSes from a single point then only does random starts at the end
    //we'll use the simplest possible version first and see if it goes
    //seek epicenter
    let mut frontier = VecDeque::new();
    while unseen.len() != 0 {
        //keep drawing until finding the next unseen
        let next_epicenter = draw(&mut unseen, r);
        let nes = serialize(next_epicenter.clone());
        if seen[nes] {
            continue;
        }

        seen.set(nes, true);
        ret.push(next_epicenter.clone());
        //breadth search until you hit bloom_size
        frontier.push_back(next_epicenter.clone());
        'both: while let Some(fno) = frontier.pop_front() {
            for ov in g.out_edges(fno).unwrap() {
                let ovs = serialize(ov.0.clone());
                if !seen[ovs] {
                    seen.set(ovs, true);
                    frontier.push_back(ov.0.clone());
                    ret.push(ov.0.clone());
                    if ret.len() % bloom_size == 0 {
                        break 'both;
                    }
                }
            }
        }
        frontier.clear();
    }
    ret
}

/// v must be a permutation on 0..v.len()
unsafe fn reverse_permutation<'a, B>(
    v: impl ExactSizeIterator<Item = &'a usize>,
    mapping: impl Fn(usize) -> B,
) -> Vec<B> {
    let vl = v.len();
    let mut ret: Vec<B> = Vec::with_capacity(vl);
    let p = ret.as_mut_ptr();
    for (from, to) in v.enumerate() {
        ptr::write(p.add(*to), mapping(from));
    }
    ret.set_len(vl);
    ret
}

#[derive(Debug, Clone)]
pub enum CSRPPError {
  NoSegment(u32),
  NoVertex(VAddr),
  NoAdjacencyIndex(usize),
  Misc(String),
}
use CSRPPError::*;
impl Display for CSRPPError {
  fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
    match *self {
      NoSegment(segment)=>
        write!(f, "CSRPlusPlus getting segment {} failed, out of bounds", segment),
      NoVertex(index)=>
        write!(f, "CSRPlusPlus getting vertex at index {:?} failed, vertex index {} does not exist", index, index.index),
      NoAdjacencyIndex(index)=>
        write!(f, "AdjacencyList getting vertex at index {} failed", index),
      Misc(ref message)=>
        write!(f, "{}", message),
    }
  }
}
impl Error for CSRPPError {
  fn description(&self)-> &str {
    "error in CSRPlusPlus"
  }
}

impl<K, V, E> CSRPlusPlus<K, V, E, (), alloc::Global> where
  K: Debug + Clone + Hash + Eq,
  V: Clone,
  E: Clone,
{
  pub fn new()-> Self {
    Self::new_detailed((), default())
  }
}

impl<K, V, E, Conf, Alloc> CSRPlusPlus<K, V, E, Conf, Alloc> where
  K: Debug + Clone + Hash + Eq,
  V: Clone,
  E: Clone,
  Conf: Clone + CSRPPTuning,
  Alloc: Clone + Allocator,
 {
    pub fn new_detailed(c: Conf, a: Alloc) -> Self {
        let ss = c.segment_size();
        Self {
            mapping: HashMap::new(),
            segments: vec![Segment {
              live_count: 0,
                external_vertex_ids: Vec::with_capacity(ss),
                vertex_weights: Vec::with_capacity(ss),
                out_edges: VecWithGaps::empty_detailed(OUR_VEC_WITH_GAPS_CONF.clone(), a.clone()),
                in_edges: VecWithGaps::empty_detailed(OUR_VEC_WITH_GAPS_CONF.clone(), a.clone()),
                // edge_weights: Vec::with_capacity(c.edge_list_empty_capacity()),
            }],
            deletion_load: 0,
            total_live_vertices: 0,
            allocator: a,
            config: c,
        }
    }

    pub fn from_edges<'a>(
        config: Conf,
        allocator: Alloc,
        nodes: impl Iterator<Item = (K, &'a V)> + Clone,
        edges: impl Iterator<Item = (K, K, &'a E)> + Clone
    ) -> Self
    where
        V: 'a + Eq,
        E: 'a,
    {
        let al = AdjacencyList::from_edges(nodes, edges);
        let mut rng = Rng::new();
        let patterning = create_radial_patterning_detailed(
            &al,
            config.segment_size(), //bloom_size:usize,
            |i| i,               //serialize: impl Fn(Index)-> usize,
            &mut rng,            //r: &mut impl Rng,
        );
        //TODO: Maybe do this in the radial patterning instead of here, you'll be able to skip the VAddr calculation sorta
        //safe: return value of create_radial_patterning is definitely a permutation
        let patterning_backmapping: Vec<VAddr> = unsafe {
            reverse_permutation(patterning.iter(), |i| VAddr {
                segment: (i / config.segment_size()) as u32,
                index: (i % config.segment_size()) as u32,
            })
        };
        let mut total_live_vertices = 0;
        let segments = patterning
            .chunks(config.segment_size())
            .map(|v| {
              let (ei, vi): (Vec<K>, Vec<V>) = v.iter().map(|vv| {let ve = &al.vertexes[*vv]; (ve.k.clone(), ve.v.clone())}).unzip();
              let live_count = ei.len();
              total_live_vertices += live_count;
              // let external_vertex_ids:Vec<K> = ei.collect();
              // let vertex_weights:Vec<V> = vi.collect();
              Segment {
                external_vertex_ids: ei,
                vertex_weights: vi,
                live_count,
                out_edges: VecWithGaps::from_sized_iters_detailed(v.iter().map(|vv| {
                    al.out_edges(*vv).unwrap().map(|i| Edge {
                        to: patterning_backmapping[i.0],
                        weight: i.1.clone(),
                    })
                }), OUR_VEC_WITH_GAPS_CONF.clone(), allocator.clone()),
                in_edges: VecWithGaps::from_sized_iters_detailed(v.iter().map(|vv| {
                    al.in_edges(*vv).unwrap().map(|i| patterning_backmapping[i])
                }), OUR_VEC_WITH_GAPS_CONF.clone(), allocator.clone())
            }})
            .collect();

        Self {
            // count: al.vertexes.len(),
            config,
            allocator,
            total_live_vertices,
            deletion_load: 0,
            mapping: al
                .mapping
                .iter()
                .map(|(v, i)| ((*v).clone(), patterning_backmapping[*i]))
                .collect(),
            segments,
        }
    }

    /// Note, if you're adding hundreds per second, you should consider batching the adds, some support for that has already been implemented in VecWithGaps. If you are only adding tens per second, though, batching per second wont make a difference, and this will be fine.
    /// returns true iff this was a new edge, false iff it overrode the old value, error if the indices are out of bounds
    pub fn add_edge(&mut self, from: VAddr, to: VAddr, w: E) -> Result<bool, CSRPPError> {
        let fl = self.segments.get_mut(from.segment as usize).ok_or_else(|| NoSegment(from.segment))?;
        if !fl.out_edges.get_section_slice(from.index as usize).is_some() {
          return Err(NoVertex(from));
        }
        fl.out_edges.insert_into_sorted_section_by(
            from.index as usize,
            Edge { to, weight: w },
            |a, b| a.to.cmp(&b.to),
        );
        let tl = self.segments.get_mut(to.segment as usize).ok_or_else(|| NoSegment(to.segment))?;
        if !tl.in_edges.get_section_slice(to.index as usize).is_some() {
          return Err(NoVertex(to));
        }
        Ok(tl.in_edges.insert_into_sorted_section(to.index as usize, from))
    }
    
    fn remove_vertex_innard(&mut self, at:VAddr, handle_mapping:bool){
      let se = self.segments.get_mut(at.segment as usize).ok_or_else(|| NoSegment(at.segment)).unwrap();
      if handle_mapping { self.mapping.remove(se.external_vertex_ids.get(at.index as usize).ok_or_else(|| NoVertex(at)).unwrap()); }
      //unlink out edges and in edges, going segment by segment to potentially improve cache performance
      //TODO: there's a probably unnecessary allocation here due to collects. I first wrote this to use iterators over references, but the borrow checker raised a fuss. It was right about one thing, there would have been problems if there were points-to-self edges. In the least, they could share a single allocation. So... maybe consider forbidding points-to-self? But this is just the remove_vertex fn, which doesn't need to be so fast.
      // let out_iter = se.out_edges.get_section_slice(at.index as usize).ok_or_else(|| NoVertex(at)).unwrap().iter().map(|e| e.to).group_by(|a| a.segment);
      // let in_iter = se.in_edges.get_section_slice(at.index as usize).ok_or_else(|| NoVertex(at)).unwrap().iter().group_by(|i| i.segment);
      
      //if the vertex is already removed, that isn't an error, caller is allowed to use this like that
      let oi = match se.out_edges.get_section_slice(at.index as usize) { Some(oi)=> oi, None=> return };
      let out_iter = oi.iter().map(|e| e.to);
      let in_iter = se.in_edges.get_section_slice(at.index as usize).ok_or_else(|| NoVertex(at)).unwrap().iter().cloned();
      let sep = out_iter.len();
      // saves an allocation by sharing vecs
      let referrers:Vec<VAddr> = out_iter.chain(in_iter).collect();
      let (out_slice, in_slice) = referrers.split_at(sep);
      for (block_segmenti, oout_e, oin_e) in match_when_possible(
        out_slice.iter().group_by(|s| s.segment).into_iter(),
        in_slice.iter().group_by(|s| s.segment).into_iter(),
      ).into_iter() {
        let bse = self.segments.get_mut(block_segmenti as usize).ok_or_else(|| NoSegment(block_segmenti)).unwrap();
        if let Some(out_e) = oout_e {
          for e in out_e {
            bse.in_edges.remove_from_sorted_section(e.index as usize, &at);
          }
        }
        if let Some(in_e) = oin_e {
          for e in in_e {
            bse.out_edges.remove_from_sorted_section_by(e.index as usize, |b| at.cmp(&b.to));
          }
        }
      }
      let se = self.segments.get_mut(at.segment as usize).unwrap(); //wont panic, above succeeded
      se.out_edges.quick_remove_section(at.index as usize);
      se.live_count -= 1;
      self.total_live_vertices -= 1;
      self.deletion_load += 1;
    }
    
    
    pub fn remove_vertex(&mut self, v:VAddr){
      self.remove_vertex_innard(v, true)
    }
    pub fn remove_vertex_called(&mut self, v:&K){
      let self_address = match self.mapping.remove(v) { Some(sa)=> sa, None=> {return;} };
      self.remove_vertex_innard(self_address, false);
    }
    
    pub fn translate_from_keys(&self, i: impl Iterator<Item=K>)-> Vec<VAddr> {
      i.map(|k| self.mapping[&k].clone()).collect()
    }
    
    //TODO: perf test this against the next one
    pub fn translate_to_keys_naive(&self, i: impl Iterator<Item=VAddr>)-> Vec<K> {
      i.map(|index| self.segments[index.segment as usize].external_vertex_ids[index.index as usize].clone()).collect()
    }
    //I'll presume that this will be faster or neutral
    pub fn translate_to_keys_batched(&self, i: impl Iterator<Item=VAddr>)-> Vec<K> {
      i.group_by(|index| index.segment).into_iter().flat_map(|(si, indexes)| {
        let se = &self.segments[si as usize];
        indexes.map(move |index| se.external_vertex_ids[index.index as usize].clone())
      }).collect()
    }
    //I feel like this couldn't possibly be faster but it's worth a try xD
    // pub fn translate_to_keys_extremely_batched(&self, i: impl ExactSizeIterator<Item=Self::Index> + Clone)-> impl Iterator<Item=K> {
    //   let mut segment_bags = HashMap::new();
    //   for (vi, v) in i.clone().enumerate() {
    //     let b = segment_bags.entry(v.segment).or_insert_with(|| Vec::new());
    //     b.push((vi, v.index));
    //   }
    //   let mut ret = Vec::with_capacity(i.len());
    //   for (si, b) in segment_bags {
    //     let se = self.segments[si];
    //     for (vi, vindex) in b {
    //       unsafe{ ptr::write(ret.as_ptr_mut().add(vi), se.external_vertex_ids[vindex]); }
    //     }
    //   }
    //   unsafe{ ret.set_len(i.len()) }
    //   ret.iter()
    // }
    
    /// Removes one edge going from `from` to `to`. If there are more than one such edge, then we can't make any guarantees about which one will be removed.
    pub fn remove_edge(&mut self, from:VAddr, to:VAddr) {
      let fl = &mut self.segments[from.segment as usize];
      fl.out_edges.remove_from_sorted_section_by(from.index as usize, |b| to.cmp(&b.to));
      let tl = &mut self.segments[to.segment as usize];
      tl.in_edges.remove_from_sorted_section_by(to.index as usize, |b| from.cmp(b));
    }

    ///finds a shortest path by breadth search
    ///returns an empty vec iff it sees `count_limit` or covers everything within `depth_limit` without finding `to`
    /// ignores edge weights, which simplifies it a bit (uses a deque instead of a priority queue, doesn't have to overwrite Found entries, faster final construction)
    /// these things probably don't win all that much performance, but it will be fun to see
    pub fn breadth_search_ignore_weights(
        &self,
        from: VAddr,
        to: VAddr,
        count_limit: usize,
        depth_limit: usize,
    ) -> Vec<VAddr> {
        if from == to {
            return vec![from];
        }
        // let mut locked_segments:Vec<usize> = Vec::new();
        let mut found: Vec<(usize, VAddr)> = Vec::new(); //a record of the found vertices, pointing back to the found vertex it was found through, enabling tracing back the chain at the end

        let mut frontier: VecDeque<(usize, VAddr)> = VecDeque::new(); //first represents the index in found this address has in found
        found.push((0, from));
        frontier.push_front((0, from));
        let mut seen: HashSet<VAddr> =
            HashSet::with_capacity((count_limit as f64 * 1.3).ceil() as usize); //we want to make sure that once it starts getting full it isn't just collisions all day... it might do this internally, TODO: Test that
        let mut depth = 0;
        while let Some((parenti, fno)) = frontier.pop_front() {
            if fno == INVALID_VADD {
                frontier.push_front((0, INVALID_VADD));
                depth += 1;
            }
            for (eto, _) in self.out_edges(fno).unwrap() {
                if !seen.contains(&eto) {
                    if eto == to {
                        let mut path: Vec<VAddr> = Vec::new();
                        found.push((parenti, eto));
                        let mut pparenti = parenti;
                        let mut pcf = eto;
                        while pparenti == 0 {
                            path.push(pcf);
                            (pparenti, pcf) = found[pparenti];
                        }
                        path.reverse();
                        return path;
                    }
                    seen.insert(eto);
                    if seen.len() >= count_limit {
                        return Vec::new();
                    }
                    if depth < depth_limit {
                        frontier.push_back((found.len(), eto));
                    }
                    found.push((parenti, eto));
                }
            }
        }

        Vec::new()
    }

    fn out_edge_edges<'a>(&'a self, from: VAddr) -> Res<slice::Iter<'a, Edge<E>>> {
        Ok(self.segments.get(from.segment as usize).ok_or_else(|| NoSegment(from.segment))?
            .out_edges
            .get_section_slice(from.index as usize).ok_or_else(|| NoVertex(from))?
            .iter())
    }
    
    // fn add_edge_batched(&mut self, a:VAddr, b:VAddr, w:E)-> bool {
    //   self.batched_insertions.entry(a).or_insert(Edge{to:b, weight:w});
    //   let s = &mut self.segments[a.segment];
    //   let section = a.index;
    //   let VWGSection{ start, ref mut length } = s.edges[a.index];
    //   match s.edges.section_slice(section).binary_search_by_key(b, |ref e| &e.neighbor) {
    //     Ok(_)=>{ false },
    //     Err(i)=>{
    //       s.edges.insert_at(section, i, w);
    //       true
    //     }
    //   }
    // }

    // unsafe fn merge_in_sorted_edges<'a>(&mut self){
    //   let comparator = |a,b| a.from.cmp(b.from).then_with(|| a.to.cmp(b.to));

    //   //TODO do this split operation in parallel
    //   let slices = self.batched_insertions.iter().split_by(|a,b| a.from.segment == b.from.segment);
    //   let indices = slices.map(|e| e.front().unwrap().from.segment);
    //   //safe: indices are guaranteed to be distinct by the above split
    //   unsafe {simultanious_mut_get(
    //     indices,
    //     self.segments.as_slice_mut()
    //   )}.zip(slices).map(|(segment, es)|{
    //     thread::spawn(move ||{
    //       segment.edges.batch_sorted_merge_insert_detailed(
    //         //src_insertions
    //         es.split_by(|a,b| a.from.index == b.from.index).map(|se| (se.first().unwrap().from.index, se)),
    //         //comparator
    //         |a,b|
    //       );
    //     })
    //   }).collect().for_each(|s| s.join().unwrap());
    // }

    // fn add_edge(&mut self, from: V, to: V)-> bool {

    // }
}

// useful for taking two iters over sorted elements and zipping them together so that if any two compare equally, they come together, otherwise, they come through alone
fn match_when_possible<A, B, K:Ord>(a: impl Iterator<Item=(K, A)>, b: impl Iterator<Item=(K, B)>)->
  impl IntoIterator<IntoIter=impl Iterator<Item=(K, Option<A>, Option<B>)>>
{
  MatchesWhenPossible{ a:a.peekable(), b:b.peekable() }
}
struct MatchesWhenPossible<AI:Iterator, BI:Iterator>{a:Peekable<AI>, b:Peekable<BI>}
impl<AI, BI, A, B, K> Iterator for MatchesWhenPossible<AI, BI>
where
  AI: Iterator<Item=(K, A)>,
  BI: Iterator<Item=(K, B)>,
  K: Ord,
{
  type Item = (K, Option<A>, Option<B>);
  fn next(&mut self)-> Option<Self::Item> {
    let Self{ ref mut a, ref mut b } = *self;
    if let Some(an) = a.peek() {
      if let Some(bn) = b.peek() {
        return match an.0.cmp(&bn.0) {
          Less=> {
            let (k, a) = a.next().unwrap();
            Some((k, Some(a), None))
          }
          Greater=> {
            let (k, b) = b.next().unwrap();
            Some((k, None, Some(b)))
          }
          Equal=> {
            let (k, a) = a.next().unwrap();
            let (_, b) = b.next().unwrap();
            Some((k, Some(a), Some(b)))
          }
        };
      }
    }
    None
  }
}


impl<'a, K, V, E, Conf, Alloc> Graph<'a, K, V, E> for CSRPlusPlus<K, V, E, Conf, Alloc>
where
    Self: 'a,
    Alloc: Clone + Allocator,
    Conf: Clone + CSRPPTuning,
    K: Debug + Clone + Hash + Eq,
    V: Clone,
    E: Clone,
{
    type InIter = iter::Cloned<slice::Iter<'a, Self::Index>>;
    type OutIter = iter::Map<
        slice::Iter<'a, Edge<E>>,
        fn(&'a Edge<E>) -> (Self::Index, &'a E),
    >;
    type Index = VAddr;
    fn next_id(&self) -> Self::Index {
      if let Some(ls) = self.segments.last() {
        if ls.vertex_weights.len() < self.config.segment_size() {
          let vsn = ls.vertex_weights.len();
          VAddr{ segment: self.segments.len() as u32 - 1, index: vsn as u32 }
        }else{
          VAddr{ segment: self.segments.len() as u32, index:0 }
        }
      }else{
        VAddr{segment:0, index:0}
      }
    }
    fn vertex_count(&self)-> usize { self.total_live_vertices }
    fn set_vertex(&mut self, k:K, v:V)-> (Self::Index, bool) {
      let nid = self.next_id();
      self.mapping.insert(k.clone(), nid);
      let sf = self.segments.get_mut(nid.segment as usize);
      let is_new = !sf.is_some();
      if let Some(se) = sf {
        se.external_vertex_ids.push(k);
        se.vertex_weights.push(v);
        se.live_count += 1;
      }else{
        //then nid is in the next segment to be, create it
        let mut vertex_weights = Vec::with_capacity(self.config.segment_size());
        vertex_weights.push(v);
        let mut external_vertex_ids = Vec::with_capacity(self.config.segment_size());
        external_vertex_ids.push(k);
        self.segments.push(Segment{
          live_count: 1,
          external_vertex_ids,
          vertex_weights,
          out_edges: VecWithGaps::many_with_capacity_detailed(self.config.segment_size(), self.config.average_expected_cardinality() as usize, OUR_VEC_WITH_GAPS_CONF.clone(), self.allocator.clone()),
          in_edges: VecWithGaps::many_with_capacity_detailed(self.config.segment_size(), self.config.average_expected_cardinality() as usize, OUR_VEC_WITH_GAPS_CONF.clone(), self.allocator.clone()),
        })
      }
      self.total_live_vertices += 1;
      (nid, is_new)
    }
    fn vertexes(&self) -> Vec<Self::Index> {
      self.segments.iter().enumerate().flat_map(|(si, s)|{
        s.out_edges.sections.iter().enumerate().filter_map(move |(vi, v)|{
          if v.deleted() { //then this one is deleted
            None
          }else{
            Some(VAddr{segment: si as u32, index: vi as u32})
          }
        })
      }).collect()
    }
    fn translate_from_k(&self, v:&K)-> Res<Self::Index> {
      Ok(*self.mapping.get(v).ok_or_else(|| Misc(format!("The key {:?} is not present in this CSRPlusPlus", v)))?)
    }
    fn translate_to_k(&self, v:&Self::Index)-> Res<K> {
      let se = self.segments.get(v.segment as usize).ok_or_else(|| NoSegment(v.segment))?;
      if se.out_edges.get_section_slice(v.index as usize).is_some() {
        Ok(se.external_vertex_ids[v.index as usize].clone())
      }else{
        Err(NoVertex(*v))
      }
    }
    fn v(&self, v:Self::Index)-> Res<&V> {
      let se = self.segments.get(v.segment as usize).ok_or_else(|| NoSegment(v.segment))?;
      if se.out_edges.get_section_slice(v.index as usize).is_some() {
        Ok(&se.vertex_weights[v.index as usize])
      }else{
        Err(NoVertex(v))
      }
    }
    fn out_edges(&'a self, v: Self::Index) -> Res<Self::OutIter> {
      Ok(self.out_edge_edges(v)?.map(|e| (e.to, &e.weight)))
    }
    fn in_edges(&'a self, v: Self::Index) -> Res<Self::InIter> {
      Ok(self.segments.get(v.segment as usize).ok_or_else(|| NoSegment(v.segment))?.in_edges.get_section_slice(v.index as usize).ok_or_else(|| NoVertex(v))?.iter().cloned())
    }
    fn random_vertex_id(&self, r:&mut Rng)-> Self::Index {
      if let Some(ls) = self.segments.last() {
        //should we catch the situations where the deletion load is so high that this would loop for quite a really really long time, and do a more methodical search instead? Okay I guess
        //this will have to do
        if self.total_live_vertices <= 0 { return INVALID_VADD; }
        loop {
          let lsl = ls.vertex_weights.len();
          let pr = r.usize(0..self.config.segment_size()*(self.segments.len()-1) + lsl);
          let segment = pr/self.config.segment_size();
          let ps = &self.segments[segment];
          let index = pr - segment*self.config.segment_size();
          if ps.out_edges.get_section_slice(index).is_some() {
            return VAddr{segment:segment as u32, index:index as u32};
          }
        }
      }else{
        INVALID_VADD
      }
    }
}

impl<K, V, E, C, A> left_right::Absorb<Edit<K, V, E>> for CSRPlusPlus<K, V, E, C, A> where
K: Debug + Clone + Hash + Eq,
V: Clone,
E: Clone,
C: Clone + CSRPPTuning,
A: Clone + Allocator
 {
  fn absorb_first(&mut self, operation: &mut Edit<K,V,E>, _: &Self) {
    //TODO: log errors??
    match *operation {
      NewVertex(ref k, ref v)=> {
        drop(self.set_vertex(k.clone(), v.clone()));
      }
      NewEdge(ref add)=> {
        drop(self.add_edge(add.from, add.to, add.weight.clone()));
      }
      DeleteVertex(ref v)=> {
        self.remove_vertex_called(v);
      }
      DeleteDirectedEdges{ref from, ref to}=> {
        if let Ok(tf) = self.translate_from_k(&from){
          if let Ok(tt) = self.translate_from_k(&to){
            self.remove_edge(tf, tt);
          }
        }
      }
    }
  }
  fn sync_with(&mut self, first:&Self) {
    *self = first.clone();
  }
}


// impl Clone for CSRPlusPlus<K,V,E,C,A> where
//   K: Clone + Hash + Eq,
//   V: Clone,
//   E: Clone,
//   C: Clone,
//   A: Clone,
// {
//   fn clone(&self)-> Self {
//     Self {
//       mapping: self.mapping.clone
//     }
//   }
// }





#[cfg(test)]
mod tests {
    extern crate itertools;
    use super::*;

    #[test]
    fn reverse_perm_ident() {
        let a: &[usize] = &[0, 1, 2, 3];
        let r = unsafe { reverse_permutation(a.iter(), |i| i) };
        itertools::assert_equal(r.iter(), a.iter());
    }
    #[test]
    fn reverse_perm_bigger() {
        let a: &[usize] = &[7, 2, 1, 0, 3, 5, 4, 6];
        let r = unsafe { reverse_permutation(a.iter(), |i| i) };
        itertools::assert_equal(r.iter(), (&[3, 2, 1, 4, 6, 5, 7, 0]).iter());
    }
    
    #[test]
    fn big_attack_csrpp(){
      //makes a random graph
      let mut v = CSRPlusPlus::new();
      let n:usize = 120;
      for i in 0..n {
        v.set_vertex(i, ());
      }
      let edge_p = 0.3;
      let edge_add_n = ((n*n) as f64 * edge_p) as usize;
      let mut r = Rng::with_seed(5);
      for _ in 0..edge_add_n {
        v.add_edge(v.random_vertex_id(&mut r), v.random_vertex_id(&mut r), ()).unwrap();
      }
      
      //delete some vertexes
      let delete_p = 0.1;
      let delete_n = (n as f64 * delete_p) as usize;
      for _ in 0..delete_n {
        v.remove_vertex(v.random_vertex_id(&mut r));
      }
      
      fn sample<'a, T>(r:&mut Rng, v:&'a Vec<T>)-> Option<&'a T> { if v.len() != 0 { Some(&v[r.usize(0..v.len())]) } else { None } }
      
      let wandern = 500;
      let mut cur_v = v.random_vertex_id(&mut r);
      // just wandering around the graph randomly
      for _ in 0..wandern {
        let mut es:Vec<VAddr>;
        loop {
          es = v.out_edges(cur_v).unwrap().map(|v| v.0).collect();
          if es.len() != 0 { break; }
          //back out
          es = v.in_edges(cur_v).unwrap().collect();
          if es.len() != 0 { break; }
          //then just start somewhere else
          cur_v = v.random_vertex_id(&mut r);
        }
        cur_v = sample(&mut r, &es).unwrap().clone();
      }
      
      //delete some edges
      let edge_deletion_p = 0.5;
      let edge_deletion_n = ((n*n) as f64 * edge_deletion_p) as usize;
      for _ in 0..edge_deletion_n {
        v.remove_edge(v.random_vertex_id(&mut r), v.random_vertex_id(&mut r));
      }
      
      assert!(v.vertex_count() > 0);
    }
}
