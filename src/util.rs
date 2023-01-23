use std::{
    cmp::{
        Ord, Ordering,
        Ordering::{Equal, Greater, Less},
    },
    ops::Mul,
    iter::{Iterator, Peekable},
};





pub fn sq<T>(v:T)-> T where T:Mul<Output=T>+Copy { v*v }


/// reports whatever is in both A and B
pub struct IntersectionSortedIterator<IA:Iterator, IB:Iterator, CF> {
    pub a: Peekable<IA>,
    pub b: Peekable<IB>,
    pub comparator: CF,
}

impl<A, B, IA, IB, CF> Iterator for IntersectionSortedIterator<IA, IB, CF>
where
    IA: Iterator<Item = A>,
    IB: Iterator<Item = B>,
    CF: FnMut(&A, &B) -> Ordering,
{
    type Item = (A, B);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let an = self.a.peek()?;
            let bn = self.b.peek()?;
            match (self.comparator)(an, bn) {
                Less => {
                    self.a.next();
                }
                Greater => {
                    self.b.next();
                }
                Equal => {
                    return Some((self.a.next().unwrap(), self.b.next().unwrap()));
                }
            }
        }
    }
}

pub fn sorted_iter_intersection<A, IA, IB, CF>(a: IA, b:IB)-> DiffSortedIterator<IA, IB, fn(&A, &A)-> Ordering>
where
    IA: Iterator<Item = A>,
    IB: Iterator<Item = A>,
    A: Ord,
{
    DiffSortedIterator { a:a.peekable(), b:b.peekable(), comparator: A::cmp }
}


/// reports whatever is in A but not in B
pub struct SubtractionSortedIterator<IA:Iterator, IB:Iterator, CF> {
    a: Peekable<IA>,
    b: Peekable<IB>,
    comparator: CF,
}

impl<A, B, IA, IB, CF> Iterator for SubtractionSortedIterator<IA, IB, CF>
where
    IA: Iterator<Item = A>,
    IB: Iterator<Item = B>,
    CF: FnMut(&A, &B) -> Ordering,
{
    type Item = A;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let am = self.a.peek();
            let bm = self.b.peek();
            let com: Option<Ordering> = am.and_then(|an| bm.map(|bn| (self.comparator)(an, bn)));
            if bm.is_none() || com == Some(Less) {
                return self.a.next();
            } else if am.is_none() || com == Some(Greater) {
                self.b.next();
            }else{
                // (neither are none, and so com must be Some(Equal))
                self.a.next();
                self.b.next();
            }
        }
    }
}



/// reports the differences between the input iterators, which should represent sorted sets. B is considered the more recent version, after the change, so elements that are in B and not in A are Additions, and elements that are in A and not in B are Removals.
pub struct ChangeSortedIterator<IA:Iterator, IB:Iterator, CF> {
    a: Peekable<IA>,
    b: Peekable<IB>,
    comparator: CF,
}
pub enum Change {
    Addition,
    Removal,
}
impl<A, IA, IB, CF> Iterator for ChangeSortedIterator<IA, IB, CF>
where
    IA: Iterator<Item = A>,
    IB: Iterator<Item = A>,
    CF: FnMut(&A, &A) -> Ordering,
{
    type Item = (A, Change);
    fn next(&mut self) -> Option<Self::Item> {
        use Change::*;
        loop {
            let am = self.a.peek();
            let bm = self.b.peek();
            let com: Option<Ordering> = am.and_then(|an| bm.map(|bn| (self.comparator)(an, bn)));
            if bm.is_none() || com == Some(Less) {
                return self.a.next().map(|v| (v, Removal))
            } else if am.is_none() || com == Some(Greater) {
                return self.b.next().map(|v| (v, Addition))
            }else{
                // (neither are none, and so com must be Some(Equal))
                self.a.next();
                self.b.next();
            }
        }
    }
}

fn change_sorted_iter<A, IA, IB, CF>(a: IA, b:IB)-> ChangeSortedIterator<IA, IB, fn(&A, &A)-> Ordering>
where
    IA: Iterator<Item = A>,
    IB: Iterator<Item = A>,
    A: Ord,
{
    ChangeSortedIterator { a:a.peekable(), b:b.peekable(), comparator: A::cmp }
}

impl<A, IA, IB, CF> ChangeSortedIterator<IA, IB, CF> where
    IA: Iterator<Item = A>,
    IB: Iterator<Item = A>,
    CF: FnMut(&A, &A) -> Ordering,
{
    /// Additions, Removals
    // minor optimization: output into one reusable vec
    fn comb(self)-> (Vec<A>, Vec<A>) {
        use Change::*;
        let mut a = Vec::new();
        let mut b = Vec::new();
        for (e, c) in self {
            match c {
                Addition => { a.push(e); }
                Removal => { b.push(e); }
            }
        }
        (a, b)
    }
}


pub struct DiffSortedIterator<IA, IB, CF> where IA: Iterator, IB: Iterator {
    pub a: Peekable<IA>,
    pub b: Peekable<IB>,
    pub comparator: CF,
}
pub enum Diff {
    Addition,
    Removal,
    Unchanged,
}
impl<A, IA, IB, CF> Iterator for DiffSortedIterator<IA, IB, CF>
where
    IA: Iterator<Item = A>,
    IB: Iterator<Item = A>,
    CF: FnMut(&A, &A) -> Ordering,
{
    type Item = (A, Diff);
    fn next(&mut self) -> Option<Self::Item> {
        use Diff::*;
        loop {
            let am = self.a.peek();
            let bm = self.b.peek();
            let com: Option<Ordering> = am.and_then(|an| bm.map(|bn| (self.comparator)(an, bn)));
            if bm.is_none() || com == Some(Less) {
                return self.a.next().map(|v| (v, Removal))
            } else if am.is_none() || com == Some(Greater) {
                return self.b.next().map(|v| (v, Addition))
            }else{
                // (neither are none, and so com must be Some(Equal))
                self.a.next();
                return self.b.next().map(|v| (v, Unchanged))
            }
        }
    }
}

pub fn sorted_iter_diff<A, IA, IB, CF>(a: IA, b:IB)-> DiffSortedIterator<IA, IB, fn(&A, &A)-> Ordering>
where
    IA: Iterator<Item = A>,
    IB: Iterator<Item = A>,
    A: Ord,
{
    DiffSortedIterator { a:a.peekable(), b:b.peekable(), comparator: A::cmp }
}

pub fn binary_search_v_by<T>(this:&Vec<T>, by: impl FnMut(&T)-> Ordering)-> Option<&T> {
    match this.binary_search_by(by) {
        Ok(at)=> Some(&this[at]),
        Err(_)=> None
    }
}



#[cfg(tests)]
mod tests {
    use super::*;
    #[test]
    fn intersection(){
        let a = [0, 1, 3, 4];
        let b = [1, 2, 3, 5];
        let r: Vec<int> = IntersectionSortedIter {
            a: a.iter(),
            b: b.iter(),
            comparator: int::cmp,
        }
        .collect();
        assert!(&r == &[1, 3]);
    }
    
    #[test]
    fn exclusion(){
        let a = [0, 1, 3, 4];
        let b = [1, 2, 3, 5];
        let r: Vec<int> = ExclusionSortedIter {
            a: a.iter(),
            b: b.iter(),
            comparator: int::cmp,
        }
        .collect();
        assert!(&r == &[0, 4]);
    }
    
    #[test]
    fn change() {
        let a = [0, 1, 3, 4];
        let b = [1, 2, 3, 5];
        let r: Vec<(Change, int)> = ChangeSortedIterator {
            a: a.iter(),
            b: b.iter(),
            comparator: int::cmp,
        }
        .collect();
        assert!(&r == &[(Removal, 0), (Addition, 2), (Removal, 4), (Addition, 5)]);
    }
}

