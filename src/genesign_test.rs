use crate::{AdjacencyList, Graph, INVALID_VLI};
use fastrand::Rng;
use itertools::{FormatWith, Itertools};
use std::{
    cmp::Eq,
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
    mem::size_of,
};

trait Genome: Hash + Eq + Clone + Copy + Debug + Display {
    fn new(rng: &mut Rng) -> Self;
    fn similarity(&self, other: &Self) -> usize;
    fn mate(&self, other: &Self, rng: &mut Rng) -> Self {
        self.mix_with_strength(other, 127, rng)
    }
    fn reassert_self(&self, other: &Self, rng: &mut Rng) -> Self {
        self.mix_with_strength(other, 52, rng)
    }
    /// strength is just the probability of passing each gene along
    fn mix_with_strength(&self, other: &Self, strength: u8, rng: &mut Rng) -> Self;
    /// the number of copies. Two is good because it ensures that what we have now gets out before incoming stuff clobbers it, I believe it more than doubles transmission diversity.
    const PLOIDY: usize = 2;
}

fn bytes_equal(a: u64, b: u64) -> usize {
    let onb: u64 = 0x00ff00ff00ff00ff;
    let onad: u64 = 0x0001000100010001;
    let ofb: u64 = 0xff00ff00ff00ff00;
    let ofad: u64 = 0x0100010001000100;
    let biteq = !(a ^ b);
    let (oad, ob) = (ofb & biteq).overflowing_add(ofad);
    let mut ret =
        ((ofb & ((onb & biteq).wrapping_add(onad))) | (onb & (oad))).count_ones() as usize;
    if ob {
        ret += 1;
    }
    ret
}

fn elongate_8x(a: u8) -> u64 {
    //optimization: isaac has made some suggestions
    let mut ret = 0;
    for i in 0..size_of::<u8>() {
        if ((a >> i) & 1) != 0 {
            ret = ret | (0xffu64 << i);
        }
    }
    ret
}

fn bitslice_iter(v: u64, in_bits: u8) -> impl Iterator<Item = u8> {
    let mut vm = v;
    let in_mask = (1u64 << in_bits) - 1;
    (0..((8 * size_of::<u64>() as u64) / in_bits as u64)).map(move |_| {
        let ret = (vm & in_mask) as u8;
        vm = vm >> in_bits;
        ret
    })
}

fn accumulate_bitslices(v: impl Iterator<Item = u8>, out_bits: u8) -> u64 {
    let mut ret = 0;
    for b in v {
        ret = (ret << out_bits) | b as u64;
    }
    ret
}

/// passes along a bytes at strength/255 probability
fn mate64_by(a: u64, b: u64, strength: u8, rng: &mut Rng) -> u64 {
    let rngo = rng.u64(..);
    let mut ret: [u8; 8] = [0; 8];
    for i in 0..8 {
        //you might think we could use to_ne_bytes here, but I want deterministic randomness across different platforms
        ret[i] = if rngo.to_le_bytes()[i] <= strength {
            a.to_le_bytes()[i]
        } else {
            b.to_le_bytes()[i]
        }
    }
    u64::from_le_bytes(ret)
}

//has a 1/4 chance of passing along mutations
fn mate64_weak(a: u64, other: u64, rng: &mut Rng) -> u64 {
    let mask = accumulate_bitslices(
        bitslice_iter(rng.u32(..) as u64, 2)
            .take(8)
            .map(|a| if a == 3 { 0xff } else { 0 }),
        8,
    );
    (a & mask) | (other & !mask)
}
//has a 3/8 chance of passing along each mutation
fn mate64(a: u64, other: u64, rng: &mut Rng) -> u64 {
    //this can be optimized, see isaac's suggestions in the engineering notes
    let mask = accumulate_bitslices(
        bitslice_iter(rng.u32(..) as u64, 3).take(8).map(|a| {
            if (a & 1) != 0 && a != 7 {
                0xff
            } else {
                0
            }
        }),
        8,
    );
    (a & mask) | (other & !mask)
}

fn write_byte_representation(
    f: &mut std::fmt::Formatter,
    bytes: impl Iterator<Item = u8>,
) -> std::fmt::Result {
    let mut pn = bytes.peekable();
    while let Some(b) = pn.next() {
        write!(f, "{:x}", b)?;
        if pn.peek().is_some() {
            write!(f, " ")?;
        }
    }
    Ok(())
}

// #[derive(Hash, PartialEq, Eq, Clone, Debug)]
// struct BasicGenome(u64);
// impl Genome for BasicGenome {
//     fn new(rng: &mut Rng) -> Self {
//         Self(rng.u64(..))
//     }
//     fn similarity(&self, other: &Self) -> usize {
//         (!(self.0 ^ other.0)).count_ones() as usize
//     }
//     fn mate(&self, other: &Self, rng: &mut Rng) -> Self {
//         Self(mate64(self.0, other.0, rng))
//     }
//     fn mate_weak(&self, other: &Self, rng: &mut Rng) -> Self {
//         Self(mate64_weak(self.0, other.0, rng))
//     }
// }
// impl Display for BasicGenome {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "BasicGenome(")?;
//         write_byte_representation(f, self.0.to_be_bytes().iter().cloned())?;
//         write!(f, ")")?;
//         Ok(())
//     }
// }

#[derive(Hash, PartialEq, Debug, Eq, Clone, Copy)]
struct Gen8_64(u64);
impl Genome for Gen8_64 {
    fn new(rng: &mut Rng) -> Self {
        Self(rng.u64(..))
    }
    fn similarity(&self, other: &Self) -> usize {
        bytes_equal(self.0, other.0)
    }
    fn mate(&self, other: &Self, rng: &mut Rng) -> Self {
        Self(mate64(self.0, other.0, rng))
    }
    fn mix_with_strength(&self, other: &Self, strength: u8, rng: &mut Rng) -> Self {
        Self(mate64_by(self.0, other.0, strength, rng))
    }
}
impl Display for Gen8_64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Gen8_64(")?;
        write_byte_representation(f, self.0.to_be_bytes().iter().cloned())?;
        write!(f, ")")?;
        Ok(())
    }
}

#[derive(Hash, PartialEq, Debug, Eq, Clone, Copy)]
struct Gen4_64(u64);
impl Genome for Gen4_64 {
    fn new(rng: &mut Rng) -> Self {
        Self(rng.u64(..))
    }
    fn similarity(&self, other: &Self) -> usize {
        hexes_equal(self.0, other.0)
    }
    fn mix_with_strength(&self, other: &Self, strength: u8, rng: &mut Rng) -> Self {
        Self(mate64_hexes_by(self.0, other.0, strength, rng))
    }
}
impl Display for Gen4_64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Gen4_64(")?;
        let mut hs = bitslice_iter(self.0, 4).peekable();
        while let Some(h) = hs.next() {
            write!(f, "{:x}", h);
            if hs.peek().is_some() {
                write!(f, " ");
            }
        }
        write!(f, ")")?;
        Ok(())
    }
}
fn mate64_hexes_by(a: u64, b: u64, strength: u8, rng: &mut Rng) -> u64 {
    let mut ret = 0;
    let mut rngo = rng.u128(..);
    for i in 0..16 {
        ret = ret
            | ((if rngo.to_le_bytes()[i] <= strength {
                a
            } else {
                b
            })
                & (0x0f << (4*i)));
    }
    ret
}
fn hexes_equal(a:u64, b:u64)-> usize {
    let onb: u64 = 0x0f0f0f0f0f0f0f0f;
    let onad: u64 = 0x0101010101010101;
    let ofb: u64 = 0xf0f0f0f0f0f0f0f0;
    let ofad: u64 = 0x1010101010101010;
    let biteq = !(a ^ b);
    let (oad, ob) = (ofb & biteq).overflowing_add(ofad);
    let mut ret =
        ((ofb & ((onb & biteq).wrapping_add(onad))) | (onb & (oad))).count_ones() as usize;
    if ob {
        ret += 1;
    }
    ret
}


#[derive(Hash, PartialEq, Debug, Eq, Clone, Copy)]
struct Gen1_64(u64);
impl Genome for Gen1_64 {
    fn new(rng: &mut Rng) -> Self {
        Self(rng.u64(..))
    }
    fn similarity(&self, other: &Self) -> usize {
        (!(self.0 ^ other.0)).count_ones() as usize
    }
    fn mix_with_strength(&self, other: &Self, strength: u8, rng: &mut Rng) -> Self {
        let mut mask = 0;
        //this can absolutely be optimized a hecklot https://stackoverflow.com/questions/35795110/fast-way-to-generate-pseudo-random-bits-with-a-given-probability-of-0-or-1-for-e and you shouldn't be using a general mix_with_strength, if you shot for a specific probability you could just use one bitwise combination of a few generated u64s
        for _ in  0..64 {
            mask = (mask << 1) | (rng.u8(..) <= strength) as u64;
        }
        Self((self.0&mask) | (other.0&!mask))
    }
}
impl Display for Gen1_64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Gen1_64({:b})", self.0)
    }
}



const PLOIDY: usize = 60;

struct Body<G> {
    //never changes, is also the node's key
    germline: G,
    //is a mix of the germline and the incoming genes
    somatic: [G; PLOIDY],
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
    //further decreases the amount of time a genome is passed along
    softening: f64,
    //if it's still unstable after mating_timeout iterations, it stops on its own and emits a warning
    mating_timeout: usize,
    //the max distance between near and long averages we can stand while still registering as stable. Unit: codon matches
    noise_floor: f64,
    do_spread: bool,
    show_structure: bool,
    show_similarity: bool,
    spread_iterations: usize,
    near_average_weighting: f64,
    long_average_weighting: f64,
    stability_threshold: u8,
    g_type: PhantomData<G>,
}
impl<G: Genome> TestConf<G> {
    fn new(show_structure: bool, do_spread: bool) -> TestConf<G> {
        TestConf {
            seed: 9394493,
            member_count: 300,
            link_adjacent_probability: 0.8,
            link_probability_zero_distance: 8,
            softening: 0.3,
            mating_timeout: 100,
            noise_floor: 0.1,
            do_spread,
            show_structure,
            show_similarity: true,
            spread_iterations: 60,
            near_average_weighting: 0.3,
            long_average_weighting: 0.05,
            stability_threshold: 5,
            g_type: PhantomData::default(),
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

#[test]
fn default_test() {
    run_test(&TestConf::<Gen8_64>::new(false, true));
    run_test(&TestConf::<Gen4_64>::new(false, true));
    run_test(&TestConf::<Gen1_64>::new(false, true));
}

fn run_test<GenomeType: Genome>(conf: &TestConf<GenomeType>) {
    let mut rng = Rng::with_seed(conf.seed);
    let mut g = AdjacencyList::from_edges(
        (0..conf.member_count).map(|i| {
            let g = GenomeType::new(&mut rng);
            (
                g.clone(),
                Body {
                    germline: g.clone(),
                    unstable_list_intrusive: i,
                    somatic: [g; PLOIDY],
                    prior_neighbor_similarity: 0.0,
                    long_average: 0.0,
                    near_average: 1.0,
                    stability: 0,
                    instability: 0,
                },
            )
        }),
        [].into_iter(),
    );
    for i in 0..conf.member_count {
        //guarantee that every one has a link
        let mut has_link = false;
        while !has_link {
            for to in 0..conf.member_count {
                if i == to {
                    continue;
                }
                let distance = (to as isize - i as isize).abs();
                if distance >= conf.link_probability_zero_distance as isize {
                    continue;
                }
                let p: f64 = (conf.link_probability_zero_distance as isize - distance) as f64
                    / (conf.link_probability_zero_distance as f64 - 1.0) as f64
                    * conf.link_adjacent_probability;
                if p >= rng.f64() {
                    has_link = true;
                    g.set_edge(i, to, (), true).unwrap();
                }
            }
        }
    }

    let middlei = g.vertex_count() / 2;
    let middleg = g.v(middlei).unwrap().germline.clone();
    println!(
        "middle ({}) germline is {}, and it has {} out and {} in",
        middlei,
        middleg,
        g.out_edges(middlei).unwrap().count(),
        g.in_edges(middlei).unwrap().count()
    );

    let mut unstable: Vec<usize> = g.vertex_iter().map(|(i, _, _)| i).collect();

    if conf.show_structure {
        let mut dd = HashMap::new();
        for (i, d) in g.dijkstra_unweighted(middlei) {
            dd.insert(i, d);
        }
        for i in 0..g.vertex_count() {
            if let Some(di) = dd.get(&i) {
                print!("{} ", di);
            } else {
                print!("ur ");
            }
        }
        println!("");
    }

    if conf.do_spread {
        let mut read_wave = 0 % PLOIDY;
        let mut write_wave = 1 % PLOIDY;
        for _ in 0..(conf.spread_iterations*PLOIDY) {
            for i in 0..unstable.len() {
                let vi = unstable[i];
                let mut ieg: Vec<GenomeType> = g
                    .in_edges(vi)
                    .unwrap()
                    .map(|i| g.v(i).unwrap().somatic[read_wave])
                    .collect();
                if ieg.len() > 0 {
                    //in weights would be important here
                    rng.shuffle(&mut ieg);
                    //this is probably not the ideal weighting to minimize volatility, but it doesn't matter, there wont be too much bias or anything, they're randomized, no way that's worth optimizing
                    //also I'm pretty sure it should take the out ratio into account
                    let component_strength =
                        255 - (255.0 / ieg.len() as f64 * conf.softening) as u8;
                    let bm = g.v_mut(vi).unwrap();
                    let germline = bm.germline.clone();

                    let ts = &mut bm.somatic[write_wave];

                    for ng in ieg.iter() {
                        *ts = ng.mix_with_strength(ts, component_strength, &mut rng);
                    }
                    *ts = germline.reassert_self(ts, &mut rng);
                }
            }
            
            
            // let zero = GenomeType::new(&mut rng);
            // println!("{} + {} = {}", zero, middleg, zero.reassert_self(&middleg, &mut rng));

            let ms = g.v(middlei).unwrap().somatic.clone();
            // println!("{} {}", ms, middleg.similarity(&ms));

            if unstable.is_empty() {
                break;
            }

            rng.shuffle(&mut unstable);

            read_wave = (read_wave + 1) % PLOIDY;
            write_wave = (write_wave + 1) % PLOIDY;
        }
    }

    if conf.show_similarity {
        for (i, _, b) in g.vertex_iter() {
            let total_similarity = b
                .somatic
                .iter()
                .map(|a| a.similarity(&middleg))
                .fold(0, |a, b| a + b);
            print!("{}{} ", if i == middlei { "→" } else { "" }, total_similarity);
        }
        print!("\n");
    }
}
