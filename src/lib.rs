// implementation of CSR++: DOI:10.4230/LIPIcs.OPODIS.2020.17
#![feature(
    associated_type_defaults,
    default_free_fn,
    allocator_api,
    return_position_impl_trait_in_trait,
)]
#[allow(incomplete_features)]

mod genesign_test;

mod util;

extern crate bitvec;
// extern crate itertools;
extern crate fastrand; //required for radial patterning
extern crate left_right;
extern crate vec_with_gaps;

// use bitvec::vec::BitVec;
use fastrand::Rng;
use itertools::Itertools;
use std::{
    alloc,
    alloc::Allocator,
    cmp::{Ordering, Ordering::*, Reverse},
    collections::{hash_map::Entry::*, BinaryHeap, HashMap, HashSet, VecDeque},
    default::{default, Default},
    error::Error,
    fmt,
    fmt::{Debug, Display, Formatter},
    hash::Hash,
    iter,
    iter::{ExactSizeIterator, Iterator, Peekable},
    mem::{replace, size_of},
    vec::Vec,
};
use vec_with_gaps::VecWithGaps;

#[derive(Clone)]
pub struct AdjacencyList<K, V, E> {
    pub mapping: HashMap<K, usize>,
    pub vertexes: Vec<ALVert<K, V, E>>,
    pub total_live_vertices: usize,
}
#[derive(Clone)]
pub struct ALVert<K, V, E> {
    pub out_edges: Vec<(usize, E)>,
    pub in_edges: Vec<usize>,
    pub k: K,
    pub v: V,
    pub deleted: bool,
}

fn binary_upsert_by_first<V: Clone + Ord, W: Clone>(
    vs: &mut Vec<(V, W)>,
    p: (V, W),
    overwrite: bool,
) -> bool {
    match vs.binary_search_by_key(&p.0, |pp| pp.0.clone()) {
        Ok(i) => {
            if overwrite {
                vs[i].1 = p.1.clone();
            }
            false
        }
        Err(i) => {
            vs.insert(i, p);
            true
        }
    }
}

fn binary_insert_if_not_present<V: Ord>(vs: &mut Vec<V>, p: V) -> bool {
    match vs.binary_search(&p) {
        Ok(_) => false,
        Err(i) => {
            vs.insert(i, p);
            true
        }
    }
}

fn binary_remove_if_present_by<T>(vs: &mut Vec<T>, comp: impl FnMut(&T) -> Ordering) -> Option<T> {
    match vs.binary_search_by(comp) {
        Ok(_) => None,
        Err(at) => Some(vs.remove(at)),
    }
}
fn binary_remove<T>(vs: &mut Vec<T>, v: &T) -> Option<T>
where
    T: Ord,
{
    match vs.binary_search(v) {
        Ok(_) => None,
        Err(at) => Some(vs.remove(at)),
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

impl<K, V, E> Default for AdjacencyList<K, V, E> {
    fn default() -> Self {
        Self {
            mapping: HashMap::new(),
            vertexes: Vec::new(),
            total_live_vertices: 0,
        }
    }
}

pub struct ALNeighborIterMut<'a, K, V, E> {
    this: &'a mut AdjacencyList<K, V, E>,
    from: usize,
    up_to: usize,
}
impl<'a, K, V, E> Iterator for ALNeighborIterMut<'a, K, V, E> {
    type Item = &'a mut V;
    fn next(&mut self) -> Option<&'a mut V> {
        let fr = &self.this.vertexes[self.from].out_edges;
        if fr.len() == self.up_to {
            None
        } else {
            let ad = fr[self.up_to].0;
            self.up_to += 1;
            //SAFETY: There are no duplicate edges
            Some(unsafe { &mut *(&mut self.this.vertexes[ad].v as *mut _) })
        }
    }
}
impl<'a, K, V, E> ExactSizeIterator for ALNeighborIterMut<'a, K, V, E> {
    fn len(&self) -> usize {
        self.this.vertexes[self.from].out_edges.len() - self.up_to
    }
}

//same as above
pub struct ALNeighborIter<'a, K, V, E> {
    this: &'a AdjacencyList<K, V, E>,
    from: usize,
    up_to: usize,
}
impl<'a, K, V, E> Iterator for ALNeighborIter<'a, K, V, E> {
    type Item = &'a V;
    fn next(&mut self) -> Option<&'a V> {
        let fr = &self.this.vertexes[self.from].out_edges;
        if fr.len() == self.up_to {
            None
        } else {
            let ad = fr[self.up_to].0;
            self.up_to += 1;
            Some(&self.this.vertexes[ad].v)
        }
    }
}
impl<'a, K, V, E> ExactSizeIterator for ALNeighborIter<'a, K, V, E> {
    fn len(&self) -> usize {
        self.this.vertexes[self.from].out_edges.len() - self.up_to
    }
}

const INVALID_VLI: usize = usize::max_value();

impl<K, V, E> AdjacencyList<K, V, E>
where
    E: Clone,
    K: Debug + Clone + Hash + Eq,
{
    //
    /// by the way, nodes don't have to be specified if they're present in an edge
    pub fn from_edges<'a>(
        nodes: impl Iterator<Item = (K, V)>,
        edges: impl Iterator<Item = (K, K, E)>,
    ) -> Self {
        let mut vertex_mapping =
            HashMap::<K, usize>::with_capacity(nodes.size_hint().1.unwrap_or(0));
        let mut vertexes: Vec<ALVert<_, _, _>> =
            Vec::with_capacity(nodes.size_hint().1.unwrap_or(0));
        let vmm = &mut vertex_mapping;
        let vm = &mut vertexes;

        for (k, v) in nodes {
            match vmm.entry(k.clone()) {
                Occupied(ref mut oe) => {
                    let i = *oe.get();
                    vm[i].v = v;
                }
                Vacant(ve) => {
                    ve.insert(vm.len());
                    vm.push(ALVert {
                        k: k.clone(),
                        v: v,
                        out_edges: Vec::new(),
                        in_edges: Vec::new(),
                        deleted: false,
                    });
                }
            }
        }

        for (a, b, e) in edges {
            let fromu: usize = vertex_mapping[&a];
            let tou: usize = vertex_mapping[&b];
            binary_upsert_by_first(&mut vertexes[fromu].out_edges, (fromu, e), true);
            binary_insert_if_not_present(&mut vertexes[tou].in_edges, fromu);
        }
        let vl = vertexes.len();
        Self {
            mapping: vertex_mapping,
            vertexes: vertexes,
            total_live_vertices: vl,
        }
    }

    fn remove_vertex_innard(&mut self, v: usize, handle_mapping: bool) -> bool {
        if let Some(ve) = self.vertexes.get_mut(v) {
            if !ve.deleted {
                if handle_mapping {
                    self.mapping.remove(&ve.k);
                }
                ve.deleted = true;
                let oit = ve.out_edges.iter().map(|(oi, _)| *oi);
                let sep = oit.len();
                let lv: Vec<usize> = oit.chain(ve.in_edges.iter().cloned()).collect();
                let (in_edges, out_edges) = lv.split_at(sep);
                for ii in in_edges {
                    binary_remove_if_present_by(&mut self.vertexes[*ii].out_edges, |b| b.0.cmp(&v));
                }
                for oi in out_edges {
                    binary_remove_if_present_by(&mut self.vertexes[*oi].in_edges, |b| b.cmp(&v));
                }
                self.total_live_vertices -= 1;
                return true;
            }
        }
        false
    }

    pub fn dijkstra_from_fold<D: Ord>(
        &self,
        start: usize,
        starting_distance: D,
        mut fold_distance: impl FnMut(&D, &E) -> D,
    ) -> Vec<(usize, D)> {
        let mut front = BinaryHeap::<(Reverse<D>, usize)>::new();
        let mut seen = HashSet::new();
        let mut ret = Vec::new();
        front.push((Reverse(starting_distance), start));
        while let Some((Reverse(d), ii)) = front.pop() {
            if seen.contains(&ii) { continue; }
            seen.insert(ii.clone());
            for (i, e) in self.out_edges(ii).unwrap() {
                if seen.contains(&i) { continue; }
                front.push((Reverse(fold_distance(&d, e)), i));
            }
            ret.push((ii, d));
        }
        ret
    }
    ///returns id, distance
    pub fn dijkstra_unweighted(&self, start: usize) -> Vec<(usize, usize)> {
        self.dijkstra_from_fold(start, 0, |d, _| d + 1)
    }

    pub fn from_sized_iters(
        i: impl ExactSizeIterator<Item = (K, V, impl ExactSizeIterator<Item = (K, E)>)> + Clone,
    ) -> Self {
        let mapping: HashMap<K, usize> = i
            .clone()
            .enumerate()
            .map(|(index, (k, _, _))| (k, index))
            .collect();
        let mut in_edges: Vec<Vec<usize>> = (0..i.len()).map(|_| Vec::new()).collect();
        let mut vertexes: Vec<ALVert<K, V, E>> = i
            .enumerate()
            .map(|(index, (k, v, edge_i))| {
                let out_edges = edge_i
                    .map(|(ov, e)| {
                        let out_vertex_index = mapping[&ov];
                        in_edges[out_vertex_index].push(index);
                        (out_vertex_index, e)
                    })
                    .collect();
                ALVert {
                    k,
                    v,
                    out_edges,
                    in_edges: Vec::new(),
                    deleted: false,
                }
            })
            .collect();
        for (v, ie) in vertexes.iter_mut().zip(in_edges) {
            v.in_edges = ie;
        }
        Self {
            mapping,
            vertexes,
            total_live_vertices: 0,
        }
    }
}
impl<K> AdjacencyList<K, f64, f64> {
    pub fn add_weight_accumulating_sorted_biedge(&mut self, a: usize, b: usize, weight: f64) {
        let mut over = |from: usize, to: usize| {
            let an = &mut self.vertexes[from];
            let dif = match an.out_edges.binary_search_by(|&(o, _)| o.cmp(&from)) {
                Ok(i) => {
                    let anr = &mut an.out_edges[i];
                    let r = weight - anr.1;
                    anr.1 = weight;
                    r
                }
                Err(i) => {
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

pub enum Edit<K, V, E> {
    NewVertex(K, V),
    NewEdge(EdgeAdd<E>),
    DeleteVertex(K),
    DeleteDirectedEdges { from: K, to: K },
}

pub struct EdgeAdd<E> {
    pub from: CSi,
    pub to: CSi,
    pub weight: E,
}

//   //TODO: Replicate changes to the mapping hashmap with a simple copy iff it expanded since the last sync, otherwise repeat the insertions

/// note, each segment was supposed to have a lock on it for parallel editing. I haven't put the locks in yet, because my use case is extremely read-heavy, wants to be lock-free most of the time
/// Once that is needed, it should be possible to make reads lock-free while making writes parallel with segment locks
/// K: keys, unique IDs the nodes are known by outside of the db
/// V: values stored at each node
/// E: weights stored on each of the edges,
#[derive(Clone)]
pub struct CSRPlusPlus<K, V, E, C: CSRPPTuning = (), A: Allocator = alloc::Global> {
    pub segments: Vec<Segment<K, V, E, A>>,
    pub mapping: HashMap<K, CSi>,
    pub deletion_load: usize, //the number of vertices known to have been quick deleted (if deletion_load/total_live_vertices > 2.5, you might want to do a reindexing)
    pub total_live_vertices: usize, //the number of vertices known to be present since the last sync
    pub config: C,
    pub allocator: A,
}

impl<K, V, E, C, A> PartialEq for CSRPlusPlus<K, V, E, C, A>
where
    K: PartialEq,
    V: PartialEq,
    E: PartialEq,
    C: CSRPPTuning,
    A: Allocator,
{
    fn eq(&self, other: &Self) -> bool {
        self.segments == other.segments
    }
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
    /// should be a little above average, it's used for capacity hints
    /// the capacity allocated to an edge list that was empty on load
    fn edge_list_empty_capacity(&self) -> usize {
        4
    }
    /// the extra proportion of capacity allocated to edge lists on load to allow for expansion
    fn edge_list_load_extra_capacity(&self) -> f64 {
        0.2
    }
    /// the extra proportion of capacity put at the very end of the edge list to allow for large tracts to be shifted over when one of the sublists needs to expand, without the entire DS being reallocated
    fn edge_list_extra_at_end_of_all(&self) -> f64 {
        0.5
    }
    // FEATURE: associated type defaults can't be defined in the trait? :/// generally aint baked #29661
    // type VecWithGapsConf: vec_with_gaps::VecWithGapsConfig = ();
    // FEATURE: can't use impls in trait methods
    // fn vec_with_gaps_conf(&self)-> impl Self::VecWithGapsConf {
    //   ()
    // }
}
impl CSRPPTuning for () {}
type VWGC = ();
const OUR_VEC_WITH_GAPS_CONF: VWGC = ();

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct CSi {
    pub segment: u32,
    pub index: u32,
}
impl Default for CSi {
    fn default() -> Self {
        INVALID_CSI
    }
}
impl Display for CSi {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "VAddr({} {})", self.segment, self.index)
    }
}
const INVALID_CSI: CSi = CSi {
    segment: u32::max_value(),
    index: u32::max_value(),
};
#[derive(Clone)]
pub struct Segment<K, V, E, A: Allocator> {
    //include a lock?
    pub live_count: usize, //note, vertices.len() doesn't always represent the number of vertices still alive, due to quick-deletion. To find out whether a vertex is deleted, check whether its out_edges segment is deleted. Usually I will do this with get_slice(...).is_some()
    pub external_vertex_ids: Vec<K>,
    pub vertex_weights: Vec<V>,
    pub out_edges: VecWithGaps<Edge<E>, VWGC, A>,
    pub in_edges: VecWithGaps<CSi, VWGC, A>,
}
impl<K, V, E, A: Allocator> Segment<K, V, E, A> {
    fn get_weight(&self, at: CSi) -> Result<&V, GraphError<CSi>> {
        self.vertex_weights
            .get(at.index as usize)
            .ok_or_else(|| NoVertex(at))
    }
}

impl<K, V, E, A> PartialEq for Segment<K, V, E, A>
where
    K: PartialEq,
    V: PartialEq,
    E: PartialEq,
    A: Allocator,
{
    fn eq(&self, other: &Self) -> bool {
        if self.vertex_weights.len() != other.vertex_weights.len() {
            return false;
        }
        for (i, (so, oo)) in self
            .out_edges
            .section_iter_mention_deleted()
            .zip(other.out_edges.section_iter_mention_deleted())
            .enumerate()
            .take(self.vertex_weights.len())
        {
            if let Some(ss) = so {
                if let Some(os) = oo {
                    if !(ss == os
                        && self.external_vertex_ids[i] == other.external_vertex_ids[i]
                        && self.vertex_weights[i] == other.vertex_weights[i])
                    {
                        return false;
                    }
                } else {
                    return false;
                }
            } else {
                if oo.is_some() {
                    return false;
                }
            }
        }
        true
        //ignores in_edges, as they're just a reflection of the out_edges
        //live_count is also just a reflection of the other data
    }
}

#[derive(Clone)]
pub struct Edge<E> {
    pub to: CSi,
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

impl<'a, K, V, E> From<&'a AdjacencyList<K, V, E>> for AdjacencyList<K, V, E>
where
    K: Clone,
    V: Clone,
    E: Clone,
{
    fn from(other: &'a AdjacencyList<K, V, E>) -> Self {
        other.clone()
    }
}

pub trait Graph<K, V, E> {
    // type InIter<'a>: ExactSizeIterator<Item = Self::Index> + Clone
    // where
    //     Self: 'a;
    // type OutIter<'a>: ExactSizeIterator<Item = (Self::Index, &'a E)> + Clone + 'a
    // where
    //     E: 'a,
    //     Self: 'a;
    // type VIter<'a>: ExactSizeIterator<Item = (Self::Index, &'a K, &'a V)> + Clone + 'a
    // where
    //     Self: 'a,
    //     K: 'a,
    //     V: 'a;
    type Index: Debug + Display = usize;
    fn next_id(&self) -> Self::Index; //needed for radial patterning. Must be greater than any vertex ID, and (for memory efficiency) should not be too much greater than the number of vertices in the structure, if it is, maybe regenerate your IDs.
    fn vertexes(&self) -> Vec<Self::Index>;
    fn vertex_iter<'a>(&'a self) -> impl ExactSizeIterator<Item = (Self::Index, &'a K, &'a V)>
    where
        K: 'a,
        V: 'a;
    fn vertex_count(&self) -> usize;
    /// converts a n:usize into the id that would be nth if the graph were fully packed
    fn into_id(&self, v: usize) -> Self::Index;
    fn from_id(&self, v: Self::Index) -> usize;
    fn v(&self, at: Self::Index) -> Result<&V, GraphError<Self::Index>>;
    fn v_mut(&mut self, at: usize) -> Result<&mut V, GraphError<Self::Index>>;
    fn e(&self, a: usize, b: usize) -> Result<&E, GraphError<Self::Index>>;
    fn k_and_v(&self, at: Self::Index) -> Result<(&K, &V), GraphError<Self::Index>>;
    /// second val is true iff this was a new insertion
    fn set_vertex(&mut self, k: K, v: V) -> (Self::Index, bool);
    fn remove_vertex(&mut self, v: Self::Index) -> bool;
    fn remove_vertex_called(&mut self, v: &K) -> bool;
    /// `overwrite` is about whether to overwrite the e of any existing edge between these two, if one exists
    fn remove_edge(
        &mut self,
        from: Self::Index,
        to: Self::Index,
    ) -> Result<E, GraphError<Self::Index>>;
    fn set_edge(
        &mut self,
        a: Self::Index,
        b: Self::Index,
        e: E,
        overwrite: bool,
    ) -> Result<bool, GraphError<Self::Index>>;
    fn set_biedge(
        &mut self,
        a: Self::Index,
        b: Self::Index,
        w: E,
        overwrite: bool,
    ) -> Result<(), GraphError<Self::Index>>
    where
        Self::Index: Clone,
        E: Clone,
    {
        self.set_edge(a.clone(), b.clone(), w.clone(), overwrite)?;
        self.set_edge(b.clone(), a.clone(), w, overwrite)?;
        Ok(())
    }
    fn out_edges<'a>(
        &'a self,
        v: Self::Index,
    ) -> Result<impl ExactSizeIterator<Item = (Self::Index, &'a E)>, GraphError<Self::Index>>
    where
        E: 'a;
    fn out_neighbors<'a>(
        &'a self,
        v: Self::Index,
    ) -> Result<impl ExactSizeIterator<Item = &'a V>, GraphError<Self::Index>>
    where
        E: 'a,
        V: 'a,
    {
        self.out_edges(v)
            .map(|o| o.map(|(i, _)| self.v(i).unwrap()))
    }
    // type NeighborIterMut<'a>: Iterator<Item = &'a mut V>
    // where
    //     Self: 'a,
    //     V: 'a;
    fn out_neighbors_mut<'a>(
        &'a mut self,
        v: Self::Index,
    ) -> Result<impl ExactSizeIterator<Item = &'a mut V>, GraphError<Self::Index>>
    where
        V: 'a;
    fn in_edges<'a>(
        &'a self,
        v: Self::Index,
    ) -> Result<impl ExactSizeIterator<Item = Self::Index> + 'a, GraphError<Self::Index>>;
    /// (must point to a live vertex (is that obvious?))
    fn random_vertex(&self, r: &mut Rng) -> Self::Index;
    fn translate_from_k(&self, v: &K) -> Result<Self::Index, GraphError<Self::Index>>;
    fn translate_to_k(&self, v: &Self::Index) -> Result<K, GraphError<Self::Index>>;
    fn mapping(&self) -> &HashMap<K, Self::Index>;
}

impl<K, V, E> Graph<K, V, E> for AdjacencyList<K, V, E>
where
    E: Clone,
    K: Debug + Clone + Hash + Eq,
{
    type Index = usize;
    fn from_id(&self, v: Self::Index) -> Self::Index {
        v
    }
    fn v_mut(&mut self, at: usize) -> Result<&mut V, GraphError<Self::Index>> {
        self.vertexes
            .get_mut(at)
            .ok_or_else(|| NoVertex(at))
            .map(|a| &mut a.v)
    }
    fn e(&self, a: usize, b: usize) -> Result<&E, GraphError<Self::Index>> {
        let oe = &self.vertexes.get(a).ok_or(NoVertex(a))?.out_edges;
        oe.binary_search_by(|&(o, _)| o.cmp(&b))
            .map(|at| &oe[at].1)
            .map_err(|_| GraphError::NoConnection(a, b))
    }
    fn into_id(&self, v: usize) -> Self::Index {
        v as Self::Index
    }
    fn mapping(&self) -> &HashMap<K, Self::Index> {
        &self.mapping
    }
    fn set_edge(
        &mut self,
        from: usize,
        to: usize,
        w: E,
        overwrite: bool,
    ) -> Result<bool, GraphError<Self::Index>> {
        let ve = &mut self.vertexes.get_mut(from).ok_or_else(|| NoVertex(from))?;
        let ret = binary_upsert_by_first(&mut ve.out_edges, (to, w), overwrite);
        let vo = self.vertexes.get_mut(to).ok_or_else(|| NoVertex(to))?;
        binary_insert_if_not_present(&mut vo.in_edges, from);
        Ok(ret)
    }
    fn out_edges<'a>(
        &'a self,
        v: Self::Index,
    ) -> Result<impl ExactSizeIterator<Item = (Self::Index, &'a E)>, GraphError<Self::Index>>
    where
        E: 'a,
    {
        Ok(self
            .vertexes
            .get(v)
            .ok_or_else(|| NoVertex(v))?
            .out_edges
            .iter()
            .map(|(i, e)| (i.clone(), e)))
    }
    fn vertex_count(&self) -> usize {
        self.total_live_vertices
    }
    fn in_edges<'a>(
        &'a self,
        v: Self::Index,
    ) -> Result<impl ExactSizeIterator<Item = Self::Index> + 'a, GraphError<Self::Index>> {
        Ok(self
            .vertexes
            .get(v)
            .ok_or_else(|| NoVertex(v))?
            .in_edges
            .iter()
            .cloned())
    }

    // type NeighborIterMut<'a> = iter::Map<Vec<Self::Index>::IntoIter, fn(Self::Index) -> &'a mut V>;
    fn out_neighbors_mut<'a>(
        &'a mut self,
        v: Self::Index,
    ) -> Result<impl ExactSizeIterator<Item = &'a mut V>, GraphError<Self::Index>>
    where
        V: 'a,
    {
        //just make sure that exists
        self.v_mut(v)?;
        Ok(ALNeighborIterMut {
            this: self,
            from: v,
            up_to: 0,
        })
    }

    fn remove_vertex_called(&mut self, v: &K) -> bool {
        let self_address = match self.mapping.remove(v) {
            Some(sa) => sa,
            None => {
                return false;
            }
        };
        self.remove_vertex_innard(self_address, false)
    }
    fn remove_vertex(&mut self, v: Self::Index) -> bool {
        self.remove_vertex_innard(v, true)
    }
    fn translate_from_k(&self, v: &K) -> Result<Self::Index, GraphError<Self::Index>> {
        Ok(*self.mapping.get(v).ok_or_else(|| {
            Misc(format!(
                "Key {:?} does not correspond to an internal index",
                v
            ))
        })?)
    }
    fn translate_to_k(&self, v: &Self::Index) -> Result<K, GraphError<Self::Index>> {
        self.vertexes
            .get(*v)
            .ok_or_else(|| NoVertex(*v))
            .map(|v| v.k.clone())
    }
    fn next_id(&self) -> usize {
        self.vertexes.len()
    }
    fn v(&self, at: Self::Index) -> Result<&V, GraphError<Self::Index>> {
        self.vertexes
            .get(at)
            .ok_or_else(|| NoVertex(at))
            .map(|a| &a.v)
    }
    fn vertexes(&self) -> Vec<Self::Index> {
        (0..self.vertexes.len())
            .filter(|i| !self.vertexes[*i].deleted)
            .collect()
    }
    fn vertex_iter<'a>(&'a self) -> impl ExactSizeIterator<Item = (Self::Index, &'a K, &'a V)>
    where
        V: 'a,
    {
        self.vertexes
            .iter()
            .enumerate()
            .map(|(i, alv)| (i, &alv.k, &alv.v))
    }
    fn random_vertex(&self, r: &mut Rng) -> Self::Index {
        r.usize(0..self.vertexes.len())
    }
    fn set_vertex(&mut self, k: K, v: V) -> (Self::Index, bool) {
        let r;
        let is_new = match self.mapping.entry(k.clone()) {
            Occupied(ref mut e) => {
                r = *e.get();
                self.vertexes[r].v = v;
                false
            }
            Vacant(e) => {
                r = self.vertexes.len();
                e.insert(r);
                self.vertexes.push(ALVert {
                    k,
                    v,
                    out_edges: Vec::new(),
                    in_edges: Vec::new(),
                    deleted: false,
                });
                self.total_live_vertices += 1;
                true
            }
        };
        (r, is_new)
    }
    fn remove_edge(
        &mut self,
        from: Self::Index,
        to: Self::Index,
    ) -> Result<E, GraphError<Self::Index>> {
        let fv = self.vertexes.get_mut(from).ok_or_else(|| NoVertex(from))?;
        let (_, ret) = binary_remove_if_present_by(&mut fv.out_edges, |b| b.0.cmp(&to))
            .ok_or_else(|| NoConnection(from, to))?;
        binary_remove(&mut self.vertexes[to].in_edges, &from);
        Ok(ret)
    }
    fn k_and_v(&self, at: Self::Index) -> Result<(&K, &V), GraphError<Self::Index>> {
        let ve = self.vertexes.get(at).ok_or_else(|| NoVertex(at))?;
        Ok((&ve.k, &ve.v))
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
/// return value: The nodes ordered as a series of blooms, each exactly bloom_size long. To get an `Iterator<Item=&[Index]>` over the blooms, simply `return_value.chunks(bloom_size)`. Each thing in the return value is the index of the node in the original graph that would be in that position, in the patterned graph
fn create_radial_patterning_detailed<Index, K, V, E>(
    g: &impl Graph<K, V, E, Index = Index>,
    bloom_size: usize,
    r: &mut Rng,
) -> Vec<Index>
where
    K: Debug,
    Index: Clone + Debug + Display,
{
    let mut unseen: Vec<Index> = g.vertexes();
    let mut seen = bitvec::bitvec![0;g.from_id(g.next_id())];
    for i in unseen.iter() {
        print!("{:?} ", i);
    }
    println!("{} {}", unseen.len(), g.from_id(g.next_id()));
    assert!(unseen.len() <= g.from_id(g.next_id()));
    let mut ret = Vec::with_capacity(seen.len());

    //TODO: try a more sophisticated one that does a BFS of BFSes from a single point then only does random starts at the end
    //we'll use the simplest possible version first and see if it goes
    //seek epicenter
    let mut frontier = VecDeque::new();
    while unseen.len() != 0 {
        //keep drawing until finding the next unseen
        let next_epicenter = draw(&mut unseen, r);
        let nes = g.from_id(next_epicenter.clone());
        if seen[nes] {
            continue;
        }

        seen.set(nes, true);
        ret.push(next_epicenter.clone());
        //breadth search until you hit bloom_size
        frontier.push_back(next_epicenter.clone());
        'both: while let Some(fno) = frontier.pop_front() {
            for ov in g.out_edges(fno).unwrap() {
                let ovs = g.from_id(ov.0.clone());
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

// fn wander<G>(v:&G, r: &mut Rng, from: G::Index, hops: usize) -> G::Index where G: Graph<_, f64, f64> {
//     let mut an = from;
//     for _ in 0..hops {
//         let mut fr = r.f64() * self.v(from).unwrap();
//         let mut poe = self.out_edges(an).unwrap().peekable();
//         while let Some(oe) = poe.next() {
//             if fr < *oe.1 || poe.peek().is_none() {
//                 an = oe.0;
//                 break;
//             }
//             fr -= oe.1;
//         }
//     }
//     an
// }

#[derive(Debug, Clone)]
pub enum GraphError<VA: Display> {
    NoSegment(u32),
    NoVertex(VA),
    NotLandmark(VA),
    NoConnection(VA, VA),
    VecWithGapsIssue(String),
    Misc(String),
}
use GraphError::*;
impl<I> Display for GraphError<I>
where
    I: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match *self {
            NoSegment(segment) => write!(
                f,
                "Graph error: getting segment {} failed, out of bounds",
                segment
            ),
            NoVertex(ref index) => write!(
                f,
                "Graph error: getting vertex at index {} failed, no such vertex",
                index
            ),
            NoConnection(ref a, ref b) => {
                write!(f, "Graph error: the nodes {} and {} weren't conneted", a, b)
            }
            NotLandmark(ref a) => write!(f, "Graph error: {} is not a landmark", a),
            VecWithGapsIssue(ref message) => {
                write!(
                    f,
                    "Graph error: CSRPlusPlus had a problem with one of its vec-with-gaps: {}",
                    message
                )
            }
            Misc(ref message) => write!(f, "{}", message),
        }
    }
}
impl<I: Debug + Display> Error for GraphError<I> {}

impl<K, V, E> Default for CSRPlusPlus<K, V, E, (), alloc::Global>
where
    K: Debug + Clone + Hash + Eq,
    V: Clone,
    E: Clone,
{
    fn default() -> Self {
        Self::new_detailed((), default())
    }
}
impl<K, V, E> CSRPlusPlus<K, V, E, (), alloc::Global>
where
    K: Debug + Clone + Hash + Eq,
    V: Clone + Eq,
    E: Clone,
{
    pub fn new() -> Self {
        default()
    }

    pub fn from_edges(
        nodes: impl Iterator<Item = (K, V)>,
        edges: impl Iterator<Item = (K, K, E)>,
    ) -> Self {
        Self::from_edges_detailed(nodes, edges, (), default())
    }
}

fn csrpp_offset_to_id(segment_size: usize, v: usize) -> CSi {
    CSi {
        segment: (v / segment_size) as u32,
        index: (v % segment_size) as u32,
    }
}

impl<K, V, E, Conf, Alloc> CSRPlusPlus<K, V, E, Conf, Alloc>
where
    K: Debug + Clone + Hash + Eq,
    V: Clone,
    E: Clone,
    Conf: Clone + CSRPPTuning,
    Alloc: Clone + Allocator,
{
    pub fn new_detailed(c: Conf, a: Alloc) -> Self {
        Self {
            mapping: HashMap::new(),
            segments: vec![],
            deletion_load: 0,
            total_live_vertices: 0,
            allocator: a,
            config: c,
        }
    }

    pub fn from_graph_with_radial_patterning<G>(al: &G, config: Conf, allocator: Alloc) -> Self
    where
        G: Graph<K, V, E>,
        G::Index: Clone,
    {
        let mut rng = Rng::new();

        let patterning: Vec<G::Index> = create_radial_patterning_detailed(
            al,
            config.segment_size(), //bloom_size:usize,
            &mut rng,              //r: &mut impl Rng,
        );
        //TODO: Maybe do this in the radial patterning instead of here, you'll be able to skip the VAddr calculation sorta. Also, these values don't need to be initialized.
        let mut patterning_backmapping: Vec<CSi> = iter::repeat(CSi::default())
            .take(al.from_id(al.next_id()))
            .collect();
        for (from, to) in patterning.iter().enumerate() {
            patterning_backmapping[al.from_id(to.clone())] =
                csrpp_offset_to_id(config.segment_size(), from);
        }

        let mut total_live_vertices = 0;
        let segments = patterning
            .chunks(config.segment_size())
            .map(|v| {
                let (eki, vi): (Vec<K>, Vec<V>) = v
                    .iter()
                    .map(|vv| {
                        let r = al.k_and_v(vv.clone()).unwrap();
                        (r.0.clone(), r.1.clone())
                    })
                    .unzip();
                let live_count = eki.len();
                total_live_vertices += live_count;
                Segment {
                    external_vertex_ids: eki,
                    vertex_weights: vi,
                    live_count,
                    out_edges: VecWithGaps::from_sized_iters_detailed(
                        v.iter().map(|vv| {
                            al.out_edges(vv.clone()).unwrap().map(|(out, e)| {
                                let e: E = (*e).clone();
                                Edge {
                                    to: patterning_backmapping[al.from_id(out)].clone(),
                                    weight: e,
                                }
                            })
                        }),
                        OUR_VEC_WITH_GAPS_CONF.clone(),
                        allocator.clone(),
                    ),
                    in_edges: VecWithGaps::from_sized_iters_detailed(
                        v.iter().map(|vv| {
                            al.in_edges(vv.clone())
                                .unwrap()
                                .map(|i| patterning_backmapping[al.from_id(i)].clone())
                        }),
                        OUR_VEC_WITH_GAPS_CONF.clone(),
                        allocator.clone(),
                    ),
                }
            })
            .collect();

        Self {
            // count: al.vertexes.len(),
            config,
            allocator,
            total_live_vertices,
            deletion_load: 0,
            mapping: al
                .mapping()
                .iter()
                .map(|(v, i)| {
                    (
                        (*v).clone(),
                        patterning_backmapping[al.from_id(i.clone())].clone(),
                    )
                })
                .collect(),
            segments,
        }
    }

    pub fn from_edges_detailed<'a>(
        nodes: impl Iterator<Item = (K, V)>,
        edges: impl Iterator<Item = (K, K, E)>,
        config: Conf,
        allocator: Alloc,
    ) -> Self
    where
        V: 'a + Eq,
        E: 'a,
    {
        Self::from_adjacency_list_detailed(
            &AdjacencyList::from_edges(nodes, edges),
            config,
            allocator,
        )
    }

    fn from_adjacency_list_detailed(
        al: &AdjacencyList<K, V, E>,
        config: Conf,
        allocator: Alloc,
    ) -> Self {
        Self::from_graph_with_radial_patterning(al, config, allocator)
    }

    fn get_segment(&self, at: CSi) -> Result<&Segment<K, V, E, Alloc>, GraphError<CSi>> {
        self.segments
            .get(at.segment as usize)
            .ok_or_else(|| NoSegment(at.segment))
    }

    fn remove_vertex_innard(&mut self, at: CSi, handle_mapping: bool) -> bool {
        let se = if let Some(se) = self.segments.get_mut(at.segment as usize) {
            se
        } else {
            return false;
        };
        if handle_mapping {
            self.mapping.remove(
                se.external_vertex_ids
                    .get(at.index as usize)
                    .ok_or_else(|| NoVertex(at))
                    .unwrap(),
            );
        }

        //unlink out edges and in edges, going segment by segment to potentially improve cache performance
        //TODO: there's a probably unnecessary allocation here due to collects. I first wrote this to use iterators over references, but the borrow checker raised a fuss. It was right about one thing, there would have been problems if there were points-to-self edges. So... maybe consider forbidding points-to-self? But this is just the remove_vertex fn, which doesn't need to be so fast that sacrifices of functionality like that should be made (although who ever uses reflexive edges, they're usually trouble).
        // let out_iter = se.out_edges.get_section_slice(at.index as usize).ok_or_else(|| NoVertex(at)).unwrap().iter().map(|e| e.to).group_by(|a| a.segment);
        // let in_iter = se.in_edges.get_section_slice(at.index as usize).ok_or_else(|| NoVertex(at)).unwrap().iter().group_by(|i| i.segment);

        //if the vertex is already removed, that isn't an error, caller is allowed to use this like that
        let oi = match se.out_edges.get_section_slice(at.index as usize) {
            Ok(oi) => oi,
            Err(_) => return false,
        };
        let out_iter = oi.iter().map(|e| e.to);
        let in_iter = se
            .in_edges
            .get_section_slice(at.index as usize)
            .unwrap() //wont panic though, the above out_edges get already succeeded
            .iter()
            .cloned();
        let sep = out_iter.len();
        // saves an allocation by sharing vecs
        let referrers: Vec<CSi> = out_iter.chain(in_iter).collect();
        let (out_slice, in_slice) = referrers.split_at(sep);
        for (block_segmenti, oout_e, oin_e) in match_when_possible(
            out_slice.iter().group_by(|s| s.segment).into_iter(),
            in_slice.iter().group_by(|s| s.segment).into_iter(),
        )
        .into_iter()
        {
            let bse = self
                .segments
                .get_mut(block_segmenti as usize)
                .ok_or_else(|| NoSegment::<CSi>(block_segmenti))
                .unwrap();
            if let Some(out_e) = oout_e {
                for e in out_e {
                    bse.in_edges
                        .remove_from_sorted_section(e.index as usize, &at)
                        .unwrap();
                }
            }
            if let Some(in_e) = oin_e {
                for e in in_e {
                    bse.out_edges
                        .remove_from_sorted_section_by(e.index as usize, |b| at.cmp(&b.to))
                        .unwrap();
                }
            }
        }
        let se = self.segments.get_mut(at.segment as usize).unwrap(); //wont panic, above succeeded
        se.out_edges
            .quick_remove_section(at.index as usize)
            .unwrap();
        se.live_count -= 1;
        self.total_live_vertices -= 1;
        self.deletion_load += 1;
        true
    }

    pub fn translate_from_keys(&self, i: impl Iterator<Item = K>) -> Vec<CSi> {
        i.map(|k| self.mapping[&k].clone()).collect()
    }

    //TODO: perf test this against the next one
    pub fn translate_to_keys_naive(&self, i: impl Iterator<Item = CSi>) -> Vec<K> {
        i.map(|index| {
            self.segments[index.segment as usize].external_vertex_ids[index.index as usize].clone()
        })
        .collect()
    }
    //I'll presume that this will be faster or neutral
    pub fn translate_to_keys_batched(&self, i: impl Iterator<Item = CSi>) -> Vec<K> {
        i.group_by(|index| index.segment)
            .into_iter()
            .flat_map(|(si, indexes)| {
                let se = &self.segments[si as usize];
                indexes.map(move |index| se.external_vertex_ids[index.index as usize].clone())
            })
            .collect()
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

    ///finds a shortest path by breadth search
    ///returns an empty vec iff it sees `count_limit` or covers everything within `depth_limit` without finding `to`
    /// ignores edge weights, which simplifies it a bit (uses a deque instead of a priority queue, doesn't have to overwrite Found entries, faster final construction)
    /// these things probably don't win all that much performance, but it will be fun to see
    pub fn breadth_search_ignore_weights(
        &self,
        from: CSi,
        to: CSi,
        count_limit: usize,
        depth_limit: usize,
    ) -> Vec<CSi> {
        if from == to {
            return vec![from];
        }
        // let mut locked_segments:Vec<usize> = Vec::new();
        let mut found: Vec<(usize, CSi)> = Vec::new(); //a record of the found vertices, pointing back to the found vertex it was found through, enabling tracing back the chain at the end

        let mut frontier: VecDeque<(usize, CSi)> = VecDeque::new(); //first represents the index in found this address has in found
        found.push((0, from));
        frontier.push_front((0, from));
        let mut seen: HashSet<CSi> =
            HashSet::with_capacity((count_limit as f64 * 1.3).ceil() as usize); //we want to make sure that once it starts getting full it isn't just collisions all day... it might do this internally, TODO: Test that
        let mut depth = 0;
        while let Some((parenti, fno)) = frontier.pop_front() {
            if fno == INVALID_CSI {
                frontier.push_front((0, INVALID_CSI));
                depth += 1;
            }
            for (eto, _) in self.out_edges(fno).unwrap() {
                if !seen.contains(&eto) {
                    if eto == to {
                        let mut path: Vec<CSi> = Vec::new();
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

    fn out_edges<'a>(
        &'a self,
        from: CSi,
    ) -> Result<impl Iterator<Item = (CSi, &'a E)>, GraphError<CSi>> {
        Ok(self
            .segments
            .get(from.segment as usize)
            .ok_or_else(|| NoSegment(from.segment))?
            .out_edges
            .get_section_slice(from.index as usize)
            .map_err(|_| NoVertex(from))?
            .iter()
            .map(|ee| (ee.to, &ee.weight)))
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
fn match_when_possible<A, B, K: Ord>(
    a: impl Iterator<Item = (K, A)>,
    b: impl Iterator<Item = (K, B)>,
) -> impl IntoIterator<IntoIter = impl Iterator<Item = (K, Option<A>, Option<B>)>> {
    MatchesWhenPossible {
        a: a.peekable(),
        b: b.peekable(),
    }
}
struct MatchesWhenPossible<AI: Iterator, BI: Iterator> {
    a: Peekable<AI>,
    b: Peekable<BI>,
}
impl<AI, BI, A, B, K> Iterator for MatchesWhenPossible<AI, BI>
where
    AI: Iterator<Item = (K, A)>,
    BI: Iterator<Item = (K, B)>,
    K: Ord,
{
    type Item = (K, Option<A>, Option<B>);
    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            ref mut a,
            ref mut b,
        } = *self;
        if let Some(an) = a.peek() {
            if let Some(bn) = b.peek() {
                return match an.0.cmp(&bn.0) {
                    Less => {
                        let (k, a) = a.next().unwrap();
                        Some((k, Some(a), None))
                    }
                    Greater => {
                        let (k, b) = b.next().unwrap();
                        Some((k, None, Some(b)))
                    }
                    Equal => {
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

#[cfg(test)]
mod tests {
    extern crate itertools;
    use super::*;

    //these are commented out because we no longer have random_csrpp (because I'm pretty sure I'm getting rid of csrpp, and the tests have already been run). It just generated a random csrpp with $1 vertices and uh, gosh I don't remember what $2 meant. Check past commits.
    // #[test]
    // fn csrpp_equal() {
    //     let a = random_csrpp(340, 1.2, &mut Rng::with_seed(30));
    //     let b = random_csrpp(340, 1.2, &mut Rng::with_seed(30));
    //     assert!(&a == &b);
    // }

    // #[test]
    // fn radial_patterning_doesnt_crash() {
    //     let a = random_csrpp(70000, 1.5, &mut Rng::with_seed(48));
    //     let _b =
    //         CSRPlusPlus::from_graph_with_radial_patterning(&a, (), std::alloc::Global::default());
    // }

    // #[test]
    // fn big_attack_csrpp() {
    //     //makes a random graph
    //     let mut r = Rng::with_seed(5);
    //     let n = 120;
    //     let mut v = random_csrpp(n, 0.3, &mut r);
    //     //delete some vertexes
    //     let delete_p = 0.1;
    //     let delete_n = (n as f64 * delete_p) as usize;
    //     for _ in 0..delete_n {
    //         v.remove_vertex(v.random_vertex(&mut r));
    //     }

    //     fn sample<'a, T>(r: &mut Rng, v: &'a Vec<T>) -> Option<&'a T> {
    //         if v.len() != 0 {
    //             Some(&v[r.usize(0..v.len())])
    //         } else {
    //             None
    //         }
    //     }

    //     let wandern = 500;
    //     let mut cur_v = v.random_vertex(&mut r);
    //     // just wandering around the graph randomly
    //     for _ in 0..wandern {
    //         let mut es: Vec<CSi>;
    //         loop {
    //             es = v.out_edges(cur_v).unwrap().map(|v| v.0).collect();
    //             if es.len() != 0 {
    //                 break;
    //             }
    //             //back out
    //             es = v.in_edges(cur_v).unwrap().collect();
    //             if es.len() != 0 {
    //                 break;
    //             }
    //             //then just start somewhere else
    //             cur_v = v.random_vertex(&mut r);
    //         }
    //         cur_v = sample(&mut r, &es).unwrap().clone();
    //     }

    //     //delete some edges
    //     let edge_deletion_p = 0.5;
    //     let edge_deletion_n = ((n * n) as f64 * edge_deletion_p) as usize;
    //     for _ in 0..edge_deletion_n {
    //         v.remove_edge(v.random_vertex(&mut r), v.random_vertex(&mut r));
    //     }

    //     assert!(v.vertex_count() > 0);
    // }
}
