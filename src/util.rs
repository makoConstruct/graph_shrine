use std::{
    cmp::{
        Ord, Ordering,
        Ordering::{Equal, Greater, Less},
    },
    iter::{Iterator, Peekable},
};

struct IntersectionSortedIterator<IA, IB, CF> {
    a: IA,
    b: IB,
    comparator: CF,
}

impl<A, B, IA, IB, CF> Iterator for IntersectionSortedIterator<IA, IB, CF>
where
    IA: Peekable<Item = A>,
    IB: Peekable<Item = B>,
    CF: FnMut(&A, &B) -> Ordering,
{
    type Item = (A, B);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let an = self.a.peek()?;
            let bn = self.b.peek()?;
            match self.comparator(an, bn) {
                Less => {
                    self.a.next();
                }
                Greater => {
                    self.b.next();
                }
                Equal => {
                    return Some((
                        self.a.next().unwrap(),
                        self.b.next().unwrap()
                    ));
                }
            }
        }
    }
}
