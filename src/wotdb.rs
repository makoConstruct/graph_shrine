use std::{cmp::Ordering, hash::Hash, collections::{BinaryHeap, HashMap}};
use crate::{VAddr, Res, CSRPPError::NoVertex, Graph, AdjacencyList, util::IntersectionSortedIterator};
extern crate noisy_float;
use noisy_float::N64;


/// Web of Trust Database
pub struct LandmarkIndex<K> {
	pub core: AdjacencyList<K, INFCNode, N64>,
}


//I think I wont actually use INCFD+, I think I'll do something else
//let's call it a brunk.
//there are landmarks
//a node knows the nearest four landmarks from and to it
//landmarks know the way to every other landmark
//these can be used for lower and upper bound queries
//the lower bound distance queries can be used as an A* heuristic
//landmarks are periodically reset by doing spidering forwards and backwards and selecting random nodes, strongly biased towards nodes with the highest min(forward_hits, backwards_hits) at first.
//	each time a landmark is placed, its spider traces are erased and this decreases the hit count of the other nodes caught in the trace, this should make it slightly more economical? I'm not sure.

// pub enum PockNode {
// 	Leaf {
// 		out_landmarks: [(N64, VAddr); 4], //sorted by their distance, nearest first
// 		in_landmarks: [(N64, VAddr); 4],
// 	},
// 	Landmark {
// 		depths: [LandmarkDepthLevel; 6], //the size of this should be log_{landmark_branching_factor}(number_of_presences). That will double slowly enough that we can totally recompile every time it does. This feels bad though lol.
// 		outs: Vec<(N64, VAddr)>, //the first four are the nearest four landmarks, sorted by their distance, the rest are the full series sorted by VAddr
// 		ins: Vec<(N64, VAddr)>,
// 		parent: Option<*mut Landmark>
// 	},
// 	Landmark {
// 		outs: Vec<(N64, VAddr)>, //the first four are the nearest four landmarks, sorted by their distance, the rest are the full series sorted by VAddr
// 		ins: Vec<(N64, VAddr)>,
// 	}
// }

pub enum INFCNode {
	NonLandmark {
		out_landmarks: Vec<(N64, VAddr)>, //sorted by their distance, nearest first
		in_landmarks: Vec<(N64, VAddr)>,
	},
	Landmark {
		outs: Vec<(N64, VAddr)>, //sorted by vaddr
		ins: Vec<(N64, VAddr)>,
	}
}
use INFCNode::*;

impl INFCNode {
	fn nearest_four_out_landmarks(&self, f: impl FnMut(&(N64, VAddr))) {
		match *self {
			NonLandmark{
				ref out_landmarks, ..
			}=> out_landmarks.iter().take(4).for_each(f),
			Landmark{
				ref outs, ..
			}=> outs.iter().take(4).for_each(f),
		}
	}
	
	fn nearest_four_in_landmarks(&self, f: impl FnMut(&(N64, VAddr))) {
		match *self {
			NonLandmark{
				ref in_landmarks, ..
			}=> in_landmarks.iter().take(4).for_each(f),
			Landmark{
				ref ins, ..
			}=> ins.iter().take(4).for_each(f),
		}
	}
}


impl<K> LandmarkIndex<K> where K:Hash + Eq + Copy {
	
	//deletes all landmarks and finds better ones
	fn index(&mut self){
		//todo: make this parallel
		unimplemented!("indexing not implemented");
	}
	
	fn distance_upper_bound(&self, a:VAddr, b:VAddr)-> Res<N64> {
		let saw = self.core.v(a)?;
		let sbw = self.core.v(b)?;
		let long_iter_on = 
				|over:&Vec<(N64, VAddr)>| over.iter().map(|(i, bl)| (i, self.core.v(bl).unwrap()));
		let short_iter_on |v:&INFCNode| [(0.0, v)].iter();
		//interestingly, this part could have been much more concise with dynamic typing, issue where conditionals have to return the same type, and although impl Iterator and impl Iterator are very similar types, they are not guaranteed to be the same, so we have to enunciate each combination of landmark or not as a different call. This was still made much more concise by rust's struct (iter) inlining
		//TODO: try a polymorphic version
		match *saw {
			Landmark{ .. } =>
				match *sbw {
					Landmark{ .. } =>
						self.distance_upper_bound_landmark_iters(short_iter_on(saw), short_iter_on(sbw)),
					NonLandmark { ref in_landmarks, .. } =>
						self.distance_upper_bound_landmark_iters(short_iter_on(saw), long_iter_on(in_landmarks)),
				}
			NonLandmark{ ref out_landmarks , .. } =>
				match *sbw {
					Landmark { .. }=>
						self.distance_upper_bound_landmark_iters(long_iter_on(out_landmarks), short_iter_on(sbw)),
					NonLandmark { ref in_landmarks, .. }=>
						self.distance_upper_bound_landmark_iters(long_iter_on(out_landmarks), long_iter_on(in_landmarks)),
				}
		}
	}
	
	fn distance_lower_bound(&self, a:VAddr, b:VAddr)-> Res<N64> {
		//The reason there are four calls here instead of two branches on whether a and b are landmarks then one call, is that each call here is actually a different morphism depending on the types of the iters. This is probably unnecessary, using polymorphic iters would probably be fine, but until I can do a perf test, it'll be like this.
		//TODO: try a polymorphic version just to see how it impacts perf
		
		let saw = self.core.v(a)?;
		let sbw = self.core.v(b)?;
		let long_iter_on = 
				|over:&Vec<(N64, VAddr)>| over.iter().map(|(i, bl)| (i, self.core.v(bl).unwrap()));
		let short_iter_on |v:&INFCNode| [(0.0, v)].iter();
		match *saw {
			Landmark{ .. } =>
				match *sbw {
					Landmark{ .. } =>
						self.distance_lower_bound_landmark_iters(short_iter_on(saw), short_iter_on(sbw)),
					NonLandmark { ref in_landmarks, .. } =>
						self.distance_lower_bound_landmark_iters(short_iter_on(saw), long_iter_on(&in_landmarks)),
				}
			NonLandmark{ ref out_landmarks , .. } =>
				match *sbw {
					Landmark { .. }=>
						self.distance_lower_bound_landmark_iters(long_iter_on(out_landmarks), short_iter_on(sbw)),
					NonLandmark { ref in_landmarks, .. }=>
						self.distance_lower_bound_landmark_iters(long_iter_on(out_landmarks), long_iter_on(in_landmarks)),
				}
		}
	}
	
	fn distance_upper_bound_landmark_iters<'a>(
		&self,
		from_a: impl Iterator<Item=(N64, VAddr)>,
		to_b: impl Iterator<Item=(N64, VAddr)> + Clone
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
	
	fn distance_le(&self, from:VAddr, to:VAddr, distance:N64): Res<bool> {
		//TODO: there's probably a faster way of doing this
		self.distance_upper_bound(from, to).map(|d| d <= distance)
	}
	
	/// returns infinity iff it was greater than max_distance
	fn distance_lower_bound_bounded(&self, from:VAddr, to:VAddr, max_distance:N64): Res<N64> {
		//TODO: This signature was provided to make an optimization possible, and isn't useful otherwise, but it currently isn't doing the optimization...
		self.distance_lower_bound(from, to).map(|d| if d > max_distance { N64::INFINITY } else{ d })
	}
	
	/// note this wont tell you whether there actually is a path, it discusses shared out landmarks, and when there isn't even a shared out landmark, it will return the extremely misleading figure of 0.
	fn distance_lower_bound_landmark_iters<'a>(
		&self,
		from_a: impl Iterator<Item=(N64, VAddr)> + Clone,
		from_b: impl Iterator<Item=(N64, VAddr)>
	)-> Res<N64> {
		let mut longest_dist = N64::zero();
		//iterates over the out landmarks on b and finds the shortest path from a to each of them. There is no way (a to b) is shorter than (actual shortest a to l) - (b to l), so that's our bound 
		let mut intersection = IntersectionSortedIterator{a: from_a.peekable(), b: from_b.peekable(), comparator: |a, b| a.1.cmp(b.1)};
		for ((bdist, _), (adist, _)) in intersection {
			longest_dist = longest_dist.max(adist - bdist);
		}
		Ok(longest_dist)
	}
	
	
	fn landmark_distance(&self, a:VAddr, b:VAddr)-> Res<N64> {
		self.core.get_weight(a).flat_map(|la|{
			if let Landmark{ref outs, ..} = *la {
				Ok(outs.binary_search_by(|c| b.cmp(c.1)).unwrap().0)
			}else{
				Err(NoVertex(a)) //not really true, but I don't want to allocate a string here
			}
		})
	}
	
	/// returns (total_path_length, None if there is no path, otherwise returns the values between them)
	fn shortest_path(&self, a:VAddr, b:VAddr, depth_limit:N64)-> Res<(N64, Option<Vec<VAddr>>)> {
		//TODO: Once in a position to performance test, try a version of this that takes upper bounds as well, to rule out paths that're definitely too long
		if a == b { return Ok((0.0, Some(vec![]))); }
		let mut trackback:HashMap<VAddr, VAddr> = HashMap::new(); //(coming_from, distance_so_far)
		trackback.insert(a, (0, 0.0));
		let mut frontier:BinaryHeap<AStarFrontierEntry> = BinaryHeap::new();
		frontier.push(AStarFrontierEntry{
			estimated_total_distance: self.distance_lower_bound_bounded(a, b, depth_limit),
			trackback: 0,
		});
		while let Some(afe) = frontier.pop_front() {
			if afe.v == b {
				//terminate, this is the shortest path to b
				let mut ret = vec![];
				loop{
					let ne = trackback[afe.v];
					if ne == a { break; }
					ret.push(ne);
				}
				return Ok((afe.total_distance_so_far, Some(ret)));
			}else{
				for (ve, d) in self.core.out_edges(afe.v).unwrap() {
					trackback.insert(ve, afe.v);
					let total_distance_so_far = afe.total_distance_so_far + d;
					frontier.push(AStarFrontierEntry{
						v:ve,
						total_distance_so_far,
						//todo: set this to use the current most optimistic estimate instead of depth_limit? Too tired, can't think about it
						estimated_total_distance: total_distance_so_far + distance_lower_bound_bounded(ve, b, depth_limit),
					});
				}
			}
		}
		
		Ok(ret)
	}
	// fn shortest_path(a:K, b:K, depth_limit:N64)-> Vec<K> {}
	
	fn add_edge(&mut self, a:VAddr, b:VAddr, distance:N64){
		
	}
}

struct AStarTrackbackEntry {
	distance_so_far: N64,
	coming_from: usize,
	v: VAddr,
}
#[derive(PartialEq, Eq)]
struct AStarFrontierEntry {
	estimated_total_distance: N64,
	total_distance_so_far: N64,
	v: VAddr,
}
impl Ord for AStarFrontierEntry {
	fn cmp(&self, other:&Self)-> Ordering {
		//reverse order, because BinaryHeap returns the max
		other.distance_so_far.cmp(&self.distance_so_far)
	}
}

impl PartialOrd for AStarFrontierEntry {
	fn cmp(&self, other:&Self)-> Option<Ordering> { Some(self.cmp(other)) }
}