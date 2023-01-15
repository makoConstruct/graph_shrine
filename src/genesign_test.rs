use crate::{AdjacencyList, Graph, INVALID_VADD};
use fastrand::Rng;
use std::{cmp::Eq, collections::hash_set::HashSet, hash::Hash};

trait Genome: Hash + Eq + Clone {
    fn new(rng: &mut Rng) -> Self;
    fn similarity(&self, other: &Genome) -> usize;
    fn mate(&self, other: &Genome) -> Self;
}

fn bytes_equal(a: u64, b: u64) -> usize {
    let onb:  u64 = 0x00ff00ff00ff00ff;
    let onad: u64 = 0x0001000100010001;
    let ofb:  u64 = 0xff00ff00ff00ff00;
    let ofad: u64 = 0x0100010001000100;
    let biteq = !(a ^ b);
    ((ofb & ((onb & biteq).wrapping_add(onad))) | (onb & ((ofb & biteq).wrapping_add(ofad))))
        .count_ones() as usize
}

fn elongate(a: u8) -> u64 {
    //optimization: isaac has made some suggestions
    let mut ret = 0;
    for i in 0..sizeof::<u8>() {
        if ((a >> i) & 1) as bool {
            ret = ret | (0xffu64 << i);
        }
    }
    ret
}

//has a 1/4 chance of passing along each mutation
fn mate64(a: u64, other: u64, rng: &mut Rng) -> u64 {
    let a = rng.u16(..);
    a & (a>>1) && 
    let mask: u64 = elongate();
    Self((self.0 & mask) | (other.0 & !mask))
}

#[derive(Hash, Eq, Clone)]
struct BasicGenome(u64);
impl Genome for BasicGenome {
    fn new(rng: &mut Rng) -> Self {
        Self(rng.u64(..))
    }
    fn similarity(&self, other: &Genome) -> usize {
        (!(self.0 ^ other.0)).count_ones() as usize
    }
    fn mate(&self, other: &Genome, rng: &mut Rng) -> Self {
        Self(mate64(self.0, other.0, rng))
    }
}

#[derive(Hash, Eq, Clone)]
struct Codon8Genome(u64);
impl Genome for Codon8Genome {
    fn new(rng: &mut Rng) -> Self {
        Self(rng.u64(..))
    }
    fn similarity(&self, other: &Genome) -> usize {
        bytes_equal(self.0, other.0)
    }
    fn mate(&self, other: &Genome, rng: &mut Rng) -> Self {
        Self(mate64(self.0, other.0, rng))
    }
}

struct Body<G> {
    //never changes, is also the node's key
    germline: G,
    //is a mix of the germline and the neighboring genes
    somatic: G,
    prior_neighbor_similarity: f64,
    //its index in the unstable list, removes when it stabilizes
    unstable_list_intrusive: usize,
    //records changes in gene frequency, if they linger at the same value for n phases, stop breeding
    near_average: f64,
    long_average: f64,
    stability: u8,
    // if this reaches conf.mating_timeout, it stabilizes artificially
    instability: u8,
}


// TODO: Consider more sophisticated stabilization processes: instead of a timeout, the noise floor increases over time. The noise floor is proportionate to the number of edges (the more, the lower it should be)
struct TestConf<G: Genome> {
    seed: u64,
    member_count: usize,
    link_adjacent_probability: f64,
    link_probability_zero_distance: usize,
    //if it's still unstable after mating_timeout iterations, it stops on its own and emits a warning
    mating_timeout: usize,
    //the max distance between near and long averages we can stand while still registering as stable. Unit: codon matches
    noise_floor: f64,
    near_average_weighting: f64,
    long_average_weighting: f64,
    stability_threshold: u8,
    g_type: PhantomData<G>,
}
impl TestConf {
    fn new() -> TestConf<BasicGenome> {
        TestConf {
            seed: 0,
            member_count: 300,
            link_adjacent_probability: 0.2,
            link_probability_zero_distance: 9,
            mating_timeout: 100,
            noise_floor: 0.1,
            near_average_weighting: 0.3,
            long_average_weighting: 0.05,
            stability_threshold: 5,
            g_type: PhantomData::new(),
        }
    }
}

// fn genome_for(i:usize)-> u64 {
//     let mut hasher = std::collections::hash_map::DefaultHasher::new();
//     hasher.write_u64(0xffa78390);
//     hasher.write_u64(i);
//     hasher.write_u64(0x2728);
//     hasher.finish()
// }

fn run_test<GenomeType>(conf: &TestConf<GenomeType>) {
    let mut rng = Rng::with_seed(conf.seed);
    let mut g = AdjacencyList::from_edges(
        (0..conf.member_count).map(|i| {
            let g = GenomeType::new(rng);
            (
                g.clone(),
                Body {
                    germline: g.clone(),
                    unstable_list_intrusive: i,
                    somatic: g,
                    prior_neighbor_similarity: 0.0,
                    long_average: 0.0,
                    near_average: 1.0,
                    stability: 0,
                },
            )
        }),
        None.iter(),
    );
    for i in 0..conf.member_count {
        //guarantee that every one has a link
        let mut has_link = false;
        while !has_link {
            for to in 0..conf.member_count {
                if i == to {
                    continue;
                }
                let p: f64 = ((conf.link_probability_zero_distance as isize
                    - (to as isize - i as isize).abs()
                    - 1) as f64);
                if p >= rng.f64() {
                    has_link = true;
                    g.set_edge(i, to, (), true).unwrap();
                }
            }
        }
    }

    let mut unstable: Vec<usize> = g.vertex_iter().map(|(i, _, _)| i).collect();

    //do mating
    while !unstable.is_empty() {
        for i in 0..unstable.len() {
            let vi = unstable[i];
            let Body{germline, ..} = g.v(vi).unwrap();
            let mut on = g.out_neighbors(i);
            let onl = on.len();
            let local_similarity = on.map(|(i, ob)| {
                ob.somatic.similarity(&germline)
            }).sum()/onl;
            let bm = &mut g.v_mut(vi).unwrap();
            bm.near_average = (local_similarity - bm.near_average)*conf.near_average_weighting;
            bm.long_average = (local_similarity - bm.long_average)*conf.long_average_weighting;
            let timed_out = bm.instability == conf.mating_timeout;
            if timed_out {
                bm.stability = conf.stability_threshold;
            }
            if timed_out || (bm.long_average - bm.near_average).abs() < conf.noise_floor {
                //it's stable
                if timed_out || bm.stability == conf.stability_threshold {
                    //stabilization event
                    unstable[i] = AdjacencyList::invalid_vi();
                    bm.unstable_list_intrusive = AdjacencyList::invalid_vi();
                    bm.instability = 0;
                }else{
                    bm.stability += 1;
                }
            }else{
                //mating event
                germline.mate(&mut bm.somatic);
                let new_somatic = bm.somatic; //allows us to end borrow on g
                for (_, b) in g.out_neighbors_mut(i).unwrap() {
                    new_somatic.mate(&mut b.somatic);
                    if b.stabilized == conf.stability_threshold {
                        //wait, how does a network ever stabilize then????
                        b.stabilized = 0;
                    }
                }
            }
        }
        
        // now shuffle and repair unstable
        // shuffles unstable, also removes all instances of dead_val and shortens the vec
        let dead_val = AdjacencyList::invalid_vi();
        let mut i = 0;
        'shuffle: while i < v.len() {
            //take from the end until you get a non-dead val to replace it with, or until it turns out that this is the end of the vec
            while v[i] == dead_val {
                if let Some(fb) = v.pop() {
                    if i == v.len() {
                        break 'shuffle;
                    }
                    if fb != dead_val {
                        v[i] = fb;
                        break;
                    }
                } else {
                    break 'shuffle;
                }
            }
            //now has a non-dead value
            unstable.swap(i, rng.usize(i..(v.len() - 1)));
            if v[i] != dead_val {
                g.v(unstable[v]).unwrap().unstable_list_intrusive = i;
                i = i + 1;
            }
        }
        //TODO remove this test
        assert!(unstable.iter().all(|i|{
            i != dead_val && g.v(i).unwrap().unstable_list_intrusive == i
        }));
    }
}
