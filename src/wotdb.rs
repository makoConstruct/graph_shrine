use std::{cmp::{Reverse, Ordering}, hash::Hash, collections::{BinaryHeap, HashMap, BTreeSet, VecDeque, HashSet}, ops::Mul, error::Error};
use crate::{CSRPPError::NoVertex, Graph, AdjacencyList, util::{IntersectionSortedIterator, ChangeSortedIterator, DiffSortedIterator, Diff, sorted_iter_diff, sq}, INVALID_VADD};
extern crate noisy_float;
use noisy_float::prelude::N64;
use fastrand::Rng;
extern crate priority_queue;
use priority_queue::PriorityQueue;

/// An index for quickly getting bounds on the lengths of the shortest paths between nodes. Can be sumarized as a bidirectional version of "FulHL". Not fully implemneted, and wont compile. Most of the complexity is in the remove_edge method, so I wrote that first. In the process of writing that, and getting to know the algorithm's behavior in all of the edge cases, it became clear to me that its performance is almost certainly going to be abysmal and it isn't currently worth finishing, for me.
/// In short, the way of segmenting the graph, landmark shadows (I think FulHL calls them "covers"), seems to make it difficult to access information about whether a node is going to need to mention another landmark after even very small changes in distances of the intermediating/shading landmarks, which seems to mean that edge removals need to scan out over most of the graph. Anything that can't prove that it has a shorter path has to be checked, and the checks are extremely expensive, requiring getting the min of all of the distances over all of the landmarks visible from all of the neighbors.
/// There may be solutions to these problems. I should work a little longer to see if I can prove that there aren't. Right now, I feel like a disproof of feasibility is within reach.
/// But in looking, I might find a way to pull up out of this.
/// But today I want to explore other methods.
/// If you're interested in completing this, feel free to contact the author.
pub struct LarkWeb<K, Conf> {
	// pub landmarks: BTreeSet<Ni>,
	pub core: AdjacencyList<K, LarkNode, N64>,
	pub conf: Conf,
}

//Node index
type Ni = usize;

//there are landmarks and there are randos. landmarks see all other landmarks out to a certain distance.
//the lower bound distance queries can be used as an A* heuristic.

// landmark placement is periodically reset/tuned via `reindex`, by picking random starting points and spidering forwards and backwards over random edges, marking as you go. Landmarks are picked from the nodes with the highest max(forward_hits, backwards_hits).
// this is not dynamic enough for my tastes, but the landmarks will remain somewhat useful as new edges are added and removed, at least for a while. Watch out for increasing memory use. That's what'll get you.
// each time a landmark is placed, its traces are erased and this decreases the hit count of the other nodes caught in the trace, this should make it slightly more economical? I'm not sure.

//randos see all *uncovered* landmarks, forward and backward, 

// I can't bring myself to engage in this level of premature abstraction, but this is the kind of thing you'd use for writing a piece of code that can handle both updating forward links and backlinks, we probably will eventually need it
// trait Direction {
// 	type EdgeIter<'a>: Iterator<'a, Item=VAddr>;
// 	fn landmarks(v:&LarkNode)-> &Vec<VAddr>;
// 	fn edges(v:&'a LarkNode)-> &EdgeIter<'a>;
// 	fn remove_edge(alf:&mut AdjacencyList, v:VAddr, v:Addr)
// }
// struct In;
// struct Out;
// use Direction::*;
// impl LarkNode {
// 	fn landmarks(&self, dir:Direction)-> &Vec<(N64, VAddr)> {
// 		match dir {
// 			In=> &self.in_landmarks,
// 			Out=> &self.out_landmarks,
// 		}
// 	}
// 	fn landmarks_mut(&mut self, dir:Direction)-> &Vec<(N64, VAddr)> {
// 		match dir {
// 			In=> &mut self.in_landmarks,
// 			Out=> &mut self.out_landmarks,
// 		}
// 	}
// }
struct LarkNode {
	whether_landmark: bool,
	out_landmarks: Vec<(Ni, N64)>, //sorted by VAddr
	in_landmarks: Vec<(Ni, N64)>,
}
impl LarkNode {
	fn local_landmark_distance(&self, landmark:Ni)-> Option<N64> {
		binary_search_v_by(&self.in_landmarks, |b| b.0.cmp(landmark)).map(|(_, d)| d)
	}
}

pub trait LarkWebConfig {
	fn max_distance()-> N64 { 34.0 }
	fn indexing_trail_sample_rate()-> N64 { 0.15 }
	fn landmark_identification_trail_length()-> N64 { 11 }
	fn proportion_of_vertices_that_should_be_landmarks()-> N64 { 0.07 }
}
impl LarkWebConfig for () {}



#[derive(Debug)]
struct CriticalLarkError<E> {
	msg: String,
	inner:E,
}
impl Error for CriticalLarkError<E> {
	fn source(&self) -> Option<&(dyn Error + 'static)> {
		Some(&self.inner)
	}
	fn description(&self)-> &str {
		if self.msg.is_empty() {
			"CRITICAL error in LarkWeb DB, this should never happen ({})"
		}else{
			&self.msg
		}
	}
}

macro_rules! try_or_return {
	($self:expr, $msg:expr, $r:expr, $or_else:expr) => {
		match $r {
			Ok(v)=> v,
			Err(e)=> {
				$self.report_error(&CriticalLarkError{msg:$msg.into(),inner: e});
				return $or_else
			}
		}
	};
}

impl<K, Conf> LarkWeb<K, Conf = ()> where K:Hash + Eq + Copy, Conf: LarkWebConfig {
	
	//deletes all landmarks and finds better ones
	pub fn reindex_with_seed(&mut self, seed:u64) -> Result<(), Box<dyn Error>> {
		//todo: make this parallel
		//todo: Make this good. You should be trying to separate cliques, but this clusters landmarks in whatever cliques aremost intense, when really you should give up on separating cliques that're too intense. Clique identification is probably an important first step.
		unimplemented!("indexing not implemented");
		
		let mut rng = Rng::with_seed(seed);
		
		let desired_landmark_count = (self.conf.proportion_of_vertices_that_should_be_landmarks()*(self.core.vertex_count() as N64)) as usize;
		let mut lowest_landmark_rank = 0 as N64;
		let mut best_candidates:BinaryHeap<Ni, Reverse<N64>> = BinaryHeap::with_capacity(desired_landmark_count);
		let mut marks:Vec<N64> = iter::repeat(0.0).take(self.core.vertex_count()).collect();
		//abuse protection: consider only drawing from human nodes rather than drawing uniformly
		let sample_count = (self.core.vertex_count() as N64 * self.conf.indexing_trail_sample_rate()) as usize;
		for _ in 0..sample_count {
			let mut at_vi:usize = rng.random_vertex(&mut rng);
			//lay a trail
			let ultimate_length = self.conf.landmark_identification_trail_length();
			let mut trail_length = ultimate_length;
			while trail_length > 0 {
				let oe = self.core.out_edges(at_vi).unwrap();
				if oe.len() == 0 {
					break;
				}
				let (at_vi, e) = oe.nth(rng.usize(0..oe.len())).unwrap();
				trail_length -= e;
				let md = &mut marks[at_vi];
				md += ((ultimate_length - trail_length)/ultimate_length).max(0.0);
				let space_free = best_candidates.len() < desired_landmark_count;
				if space_free || md > best_candidates.peek().unwrap_or(0.0).0 {
					if !space_free {
						best_candidates.pop();
					}
					best_candidates.push(at_vi, Reverse(*md));
				}
			}
		}
		
		if best_candidates.len() < self.conf.desired_landmark_count {
			return Err("we didn't get enough landmarks, somehow. This should never happen.".into());
		}
		
		let landmarks:BTreeSet<Ni> = best_candidates.into_iter().map(|(_,a)| a).collect();
		let (new_landmarks, removed_landmarks) = change_sorted_iter(self.landmarks.iter(), landmarks.iter()).comb();
		for rl in removed_landmarks {
			self.core.unlandmark(rl);
		}
		for nl in new_landmarks {
			self.core.enlandmark(nl);
		}
		self.landmarks = landmarks;
		
		Ok(())
	}
	
	fn unlandmark(&mut self, v:Ni)-> Result<(), Box<dyn Error>> {
		let vn = self.core.v_mut(v)?;
		if !vn.whether_landmark { return Ok(()); }
		let out_landmarks = replace(&mut vn.out_landmarks, Vec::new());
		let in_landmarks = replace(&mut vn.in_landmarks, Vec::new());
		for (_, oli) in out_landmarks.iter() {
			let oi = &mut self.core.v_mut(oli)?;
			let ins = &mut oi.in_landmarks;
			if let Ok(at) = ins.binary_search_by(|b| b.0.cmp(v)) {
				ins.erase(at);
			}
		}
		for (_, oli) in in_landmarks.iter() {
			let oi = &mut self.core.v_mut(oli)?;
			let ins = &mut oi.out_landmarks;
			if let Ok(at) = ins.binary_search_by(|b| b.0.cmp(v)) {
				ins.erase(at);
			}
		}
		// transition, heal
		
		// delist from all of the randos connected to you
		let mut healed = HashSet::<Ni>::New();
		healed.insert(v);
		// take on the landmark listings from around you
		
		// Ok(())
		unimplemented!()
	}
	
	fn new(c:Conf)-> Self {
		Self{
			landmarks: BTreeSet::new(),
			core: AdjacencyList::default(),
			conf: c,
		}
	}
	
	//
	fn report_error(&self, e:& impl Error){
		//eventually: replace this with parallel logging or something. Maybe do a transaction rollback thing? Which I guess just means aborting the last left-right epoch.
		println!("{}", e);
	}
	
	fn get_in_landmark_distance(&self, a:Ni, landmark:Ni)-> N64 {
		//TODO figure out a way to make this faster if possible. It probably isn't though!! :(((
		let an:&LarkNode = try_or_return!(self, "CRITICAL larkweb error in get_in_landmark_distance, missing target", self.v(a), N64::infinity());
		// let an = match self.v(a) {
		// 	Ok(an)=> an,
		// 	Err(e)=> {self.report_error(&CriticalLarkError{msg: "CRITICAL larkweb error in get_in_landmark_distance, missing target".into(), inner:e}); return N64::infinity()}
		// };
		an.local_landmark_distance(landmark).unwrap_or_else(||{
			an.in_landmarks.iter().fold(N64::infinity(), |a,b|{
				let b = try_or_return!(self, "CRITICAL larkweb error in get_in_landmark_distance, an in_landmark didn't exist", self.v(b), N64::infinity());
				if let Some(bd) = b.local_landmark_distance(landmark) { a.min(bd) } else { a }
			})
		})
	}
	
	fn distance_upper_bound(&self, a:Ni, b:Ni)-> Res<N64> {
		let saw = self.core.v(a)?;
		let sbw = self.core.v(b)?;
		let long_iter_on = 
				|over:&Vec<(N64, Ni)>| over.iter().map(|(i, bl)| (i, self.core.v(bl).unwrap()));
		let short_iter_on = |v:&LarkNode| [(0.0, v)].iter();
		//interestingly, this part could have been much more concise with dynamic typing, issue where conditionals have to return the same type, and although impl Iterator and impl Iterator are very similar types, they are not guaranteed to be the same, so we have to enunciate each combination of landmark or not as a different call. This was still made much more concise by rust's struct (iter) inlining
		//TODO: try a polymorphic version
		match *saw {
			Landmark{ .. } =>
				match *sbw {
					Landmark{ .. } =>
						self.distance_upper_bound_landmark_iters(short_iter_on(saw), short_iter_on(sbw)),
					Rando { ref in_landmarks, .. } =>
						self.distance_upper_bound_landmark_iters(short_iter_on(saw), long_iter_on(in_landmarks)),
				}
			Rando{ ref out_landmarks , .. } =>
				match *sbw {
					Landmark { .. }=>
						self.distance_upper_bound_landmark_iters(long_iter_on(out_landmarks), short_iter_on(sbw)),
					Rando { ref in_landmarks, .. }=>
						self.distance_upper_bound_landmark_iters(long_iter_on(out_landmarks), long_iter_on(in_landmarks)),
				}
		}
	}
	
	fn distance_lower_bound(&self, a:Ni, b:Ni)-> Res<N64> {
		//The reason there are four calls here instead of two branches on whether a and b are landmarks then one call, is that each call here is actually a different morphism depending on the types of the iters. This is probably unnecessary, using polymorphic iters would probably be fine, but until I can do a perf test, it'll be like this.
		//TODO: try a polymorphic version just to see how it impacts perf
		
		let saw = self.core.v(a)?;
		let sbw = self.core.v(b)?;
		let long_iter_on = 
				|over:&Vec<(N64, Ni)>| over.iter().map(|(i, bl)| (i, self.core.v(bl).unwrap()));
		let short_iter_on = |v:&LarkNode| [(0.0, v)].iter();
		match *saw {
			Landmark{ .. } =>
				match *sbw {
					Landmark{ .. } =>
						self.distance_lower_bound_landmark_iters(short_iter_on(saw), short_iter_on(sbw)),
					Rando { ref in_landmarks, .. } =>
						self.distance_lower_bound_landmark_iters(short_iter_on(saw), long_iter_on(&in_landmarks)),
				}
			Rando{ ref out_landmarks , .. } =>
				match *sbw {
					Landmark { .. }=>
						self.distance_lower_bound_landmark_iters(long_iter_on(out_landmarks), short_iter_on(sbw)),
					Rando { ref in_landmarks, .. }=>
						self.distance_lower_bound_landmark_iters(long_iter_on(out_landmarks), long_iter_on(in_landmarks)),
				}
		}
	}
	
	fn distance_upper_bound_landmark_iters<'a>(
		&self,
		from_a: impl Iterator<Item=(N64, Ni)>,
		to_b: impl Iterator<Item=(N64, Ni)> + Clone
	)-> Res<N64> {
		let mut shortest_dist = N64::INFINITY;
		for (dist, la) in from_a {
			if dist < shortest_dist {
				for (bdist, lb) in to_b.clone() {
					let dt = dist + bdist;
					if dt < shortest_dist {
						if la == lb {
							shortest_dist = dt;
						}else{
							let bd = self.core.get_weight(la).out_landmarks.iter().find(|p| p.1 == lb).unwrap().0;
							let td = dt + bd;
							if td < shortest_dist {
								shortest_dist = td;
							}
						}
					}
				}
			}
		}
		Ok(shortest_dist)
	}
	
	fn distance_le(&self, from:Ni, to:Ni, distance:N64)-> Res<bool> {
		//TODO: there's probably a faster way of doing this
		self.distance_upper_bound(from, to).map(|d| d <= distance)
	}
	
	/// returns infinity iff it was greater than max_distance
	fn distance_lower_bound_bounded(&self, from:Ni, to:Ni, max_distance:N64)-> Res<N64> {
		//TODO: This signature was provided to make an optimization possible, and isn't useful otherwise, but it currently isn't doing the optimization...
		self.distance_lower_bound(from, to).map(|d| if d > max_distance { N64::INFINITY } else{ d })
	}
	
	/// note this wont tell you whether there actually is a path, it discusses shared out landmarks, and when there isn't even a shared out landmark, it will return the extremely misleading figure of 0.
	fn distance_lower_bound_landmark_iters<'a>(
		&self,
		from_a: impl Iterator<Item=(N64, Ni)> + Clone,
		from_b: impl Iterator<Item=(N64, Ni)>
	)-> Res<N64> {
		let mut longest_dist = N64::zero();
		//iterates over the out landmarks on b and finds the shortest path from a to each of them. There is no way (a to b) is shorter than (actual shortest a to l) - (b to l), so that's our bound 
		let mut intersection = IntersectionSortedIterator{a: from_a.peekable(), b: from_b.peekable(), comparator: |a, b| a.1.cmp(b.1)};
		for ((bdist, _), (adist, _)) in intersection {
			longest_dist = longest_dist.max(adist - bdist);
		}
		Ok(longest_dist)
	}
	
	
	fn landmark_distance(&self, a:Ni, b:Ni)-> Res<N64> {
		self.core.get_weight(a).and_then(|la|{
			if let Landmark{ref outs, ..} = *la {
				match outs.binary_search_by(|c| c.1.cmp(b)) {
					Ok(at)=> Ok(outs[at].0),
					Err(at)=> Err(LandmarksNotConnected(a, b)),
				}
			}else{
				Err(NotLandmark(a))
			}
		})
	}
	
	/// returns (total_path_length, None if there is no path, otherwise returns the values between them)
	fn shortest_path(&self, a:Ni, b:Ni, depth_limit:N64)-> Res<(N64, Option<Vec<Ni>>)> {
		//TODO: Once in a position to performance test, try a version of this that takes upper bounds as well, to rule out paths that're definitely too long
		if a == b { return Ok((0.0.into(), Some(vec![]))); }
		let mut trackback = HashMap::<Ni, Ni>::new(); //(to, from)
		let mut frontier = BinaryHeap::<Reverse<AStarFrontierEntry>>::new();
		let mut landmark_search_cache = LandmarkSearchCache::new();
		frontier.push(Reverse(AStarFrontierEntry{
			total_distance_so_far: 0.0.into(),
			estimated_total_distance: self.distance_lower_bound_bounded(a, b, depth_limit)?,
			v: a,
		}));
		while let Some(afe) = frontier.pop_front() {
			if afe.v == b {
				//terminate, this is the shortest path to b
				let mut ret = vec![];
				let mut ne = afe.v;
				while ne != a {
					ret.push(ne);
					ne = trackback[&ne];
				}
				return Ok((afe.total_distance_so_far, Some(ret)));
			}else{
				for (ve, d) in self.core.out_edges(afe.v).unwrap() {
					if trackback.contains(ve) {continue;}
					trackback.insert(ve, afe.v);
					let total_distance_so_far = afe.total_distance_so_far + d;
					frontier.push(Reverse(AStarFrontierEntry{
						v:ve,
						total_distance_so_far,
						estimated_total_distance: total_distance_so_far + distance_lower_bound_bounded(ve, b, depth_limit - total_distance_so_far),
					}));
				}
			}
		}
		
		Ok(ret)
	}
	// fn shortest_path(a:K, b:K, depth_limit:N64)-> Vec<K> {}
	
	fn add_edge(&mut self, a:Ni, b:Ni, distance:N64){
		unimplemented!()
	}
	
	// errors: NoConnection(a, b) if not connected
	fn remove_edge(&mut self, a:Ni, b:Ni, distance:N64)-> Res<()> {
		let atb:N64 = self.core.e(a, b)?;
		self.core.remove_edge(a, b); //controversial, doing this so early (should it roll back in case of error? But there shouldn't be any errors! x])
		
		//forward, updating the in_landmarks (that which flows in with the edges)
		//so, abstract this and call this twice in both directions
		// b, ltb, in_landmarks, out_landmarks, get_in_landmark_distance,
		// initial_from_l:N64,
		// in_landmarks:FnMut(&LarkNode)-> impl Iterator<Item=(N64, Ni)>,
		// out_landmarks:FnMut(&LarkNode)-> impl Iterator<Item=(N64, Ni)>,
		// out_landmarks:FnMut(&LarkNode, l:Ni)-> N64,
		
		// Basically, for each landmark accessible via a:
		// figures out what's inside the wound by dijstraing forward until it has covered everything that is shortest reachable from a
		// then reevaluates their shortest paths to l, going from shortest to longest
		
		//Consider: This (the branch over landmarks) is easily parallelizable. The distancing process for each landmark doesn't interact with the others. You can replace N64s with https://crates.io/crates/atomic_float
		
		#[derive(Ord)]
		struct InsidenessSearchEntry {
			distance_from_l_via_a: N64,
			subject: Ni,
			shading_landmark: Option<Ni>,
		}
		
		for (l, lta) in self.core.v(a)?.in_landmarks.iter() {
			let mut invalidated = HashSet::<Ni>::new();
			let mut frontier = BinaryHeap::<InsidenessSearchEntry>::new(); //the distance here is an overestimate of their distance from l, via a before a-b was removed. We stop expanding when we encounter a Ni that is less far from l than that, because that means it has another route that's unaffected by the removal. This will include everything that will be affected by the removal.
			
			frontier.push(InsidenessSearchEntry{
				distance_from_l_via_a: (lta + atb).into(),
				subject: b,
				shading_landmark: if a.is_landmark { Some(a) } else { None }
			});
			while let (distance, n, parent) = frontier.pop() {
				//I think a none here would mean that l is shadowed by another landmark (which you will have passed at some point), and this is not hte correct way to handle it
				let vnr = self.v(n)?;
				let ltn = self.get_in_landmark_distance(n, l);
				if ltn == distance && n != l && !invalidated.contains(&n) {
					//otherwise, it has another shorter route to the landmark, and definitely wont be affected by the edge removal, and we can leave that alone
					//otherwise, n will definitely not have its distance from l changed by the edge deletion, nor will anything shadowed by it
					invalidated.insert(n);
					for (we, ne) in self.out_edges(n) {
						if !invalidated.contains(ne) {
							frontier.push((we + distance, ne));
						}
					}
				}
				assert!(ltn <= distance); //it should be impossible for ltn to be greater than distance, because there exists a path from l of distance, so that should be that node's distance
			}
			
			// optimization: only put the distance in the priorityqueue (stuff in priority queues has to be able to move around), and store the rest in a hash map or not at all?
			#[derive(Ord)]
			struct ValidationSeepEntry {
				distance_from_l_via_outside: N64,
				via_neighbor_index: usize,
				via_landmark: Option<Ni>
			}
			//insides noted, now you know you can ignore those neighbors, because their distance might no longer be accurate.
			//find shortest entries from adjacent non-inside nodes
			let mut seep = PriorityQueue::<Ni, ValidationSeepEntry>::new();
			for ni in invalidated.iter() {
				if let Some(to_push) = self.v(ni)?.in_edges().iter().enumerate().map(|(i, (nni, nnd))|{
					if !invalidated.contains(nni) {
						Some(ValidationSeepEntry{
							distance_from_l_via_outside: nnd + self.get_in_landmark_distance(nnd, l)?,
							via_neighbor_index: i,
							via_landmark: unimplemented!("todo: replace the above get_in_landmark_distance call with something that returns any shade that may be involved")
						})
					}else{
						None
					}
				}) {
					seep.push(to_push.distance_from_l_via_outside, to_push);
				}
			}
			// now process that stuff, this should eventually set the new distances of every inside node
			while let Some((iv, oe)) = seep.pop() {
				//idk
				unimplemented!("idk, it needs to integrate the new path information, this may involve removing landmarks, removing a distance entry to l if there's a new shade, so on. but you have all of the information you need to do it, at this point. iv can become valid again.");
				unimplemented!("check neighbors for invalidated ones, update their `seep` entry in light of what this node can now offer them");
				
				invalidated.remove(iv);
			}
			assert!(invalidated.is_empty())
		}
		
		unimplemented!("do all of that again in reverse, from the other node as a starting point for out-landmarks");
		
		Ok(())
	}
}


struct AStarTrackbackEntry {
	distance_so_far: N64,
	coming_from: usize,
	v: Ni,
}
#[derive(PartialEq, Eq)]
struct AStarFrontierEntry {
	estimated_total_distance: N64,
	total_distance_so_far: N64,
	v: Ni,
}
impl Ord for AStarFrontierEntry {
	fn cmp(&self, other:&Self)-> Ordering {
		self.distance_so_far.cmp(&other.distance_so_far)
	}
}

impl PartialOrd for AStarFrontierEntry {
	fn cmp(&self, other:&Self)-> Option<Ordering> { Some(self.cmp(other)) }
}