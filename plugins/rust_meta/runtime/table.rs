//! The tables the checker looks terms up in, written out in full: open
//! addressing over vectors, with linear probing. The store's table of all
//! terms is in `Store` itself (`find`, `place`, `grow` in lib.rs), since
//! it compares the terms' data; here are the hash functions and the small
//! table that the list operations count terms with.
//!
//! A hash only chooses where a search starts. Every search compares what
//! it finds with what it looks for, so a collision costs time and nothing
//! else.

use crate::Term;

/// One step of the multiply-rotate hash: `w` added to `h`.
#[inline]
pub(crate) fn mix(h: u64, w: u64) -> u64 {
    (h.rotate_left(5) ^ w).wrapping_mul(0x517c_c1b7_2722_0a95)
}

/// The 32 bits kept of a hash. The high half is folded in, since the
/// multiplication of `mix` leaves the low bits the weakest.
#[inline]
pub(crate) fn fold(h: u64) -> u32 {
    (h ^ (h >> 32)) as u32
}

/// The least power of two that is at least `2 * (n + 1)`: the number of
/// slots for `n` entries, so that a table is never more than half full and
/// every search ends at an empty slot.
pub(crate) fn slots_for(n: usize) -> usize {
    let mut slots = 16;
    while slots / 2 < n + 1 {
        slots *= 2;
    }
    slots
}

/// A stack of pairs of terms. Popping only moves `len`, so that the stack
/// uses nothing of `Vec` but `push`, `len` and indexing.
pub(crate) struct PairStack {
    items: Vec<(Term, Term)>,
    /// The number of pairs on the stack: the first `len` of `items`.
    len: usize,
}

impl PairStack {
    pub(crate) fn new() -> PairStack {
        PairStack {
            items: Vec::new(),
            len: 0,
        }
    }
    pub(crate) fn push(&mut self, pair: (Term, Term)) {
        if self.len < self.items.len() {
            self.items[self.len] = pair;
        } else {
            self.items.push(pair);
        }
        self.len += 1;
    }
    /// Takes the pair pushed last off the stack.
    pub(crate) fn pop(&mut self) -> Option<(Term, Term)> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            Some(self.items[self.len])
        }
    }
}

/// How many times each term of a list occurs. Made for at most a given
/// number of different terms, which its user knows.
pub(crate) struct TermCounts {
    /// For each slot, 0 or one more than the place of an entry.
    slots: Vec<u32>,
    keys: Vec<Term>,
    counts: Vec<usize>,
}

impl TermCounts {
    /// An empty table for up to `n` different terms. Its user must not add
    /// more than `n` different terms: the table does not grow, and a search
    /// of a full table would not end.
    pub(crate) fn new(n: usize) -> TermCounts {
        TermCounts {
            slots: vec![0; slots_for(n)],
            keys: Vec::new(),
            counts: Vec::new(),
        }
    }
    /// The slot of `t`, or the empty slot where it would go.
    fn slot(&self, t: Term) -> usize {
        let mask = self.slots.len() - 1;
        let mut i = (fold(mix(0, u64::from(t.0))) as usize) & mask;
        let mut searching = true;
        while searching {
            let s = self.slots[i];
            if s == 0 || self.keys[(s - 1) as usize] == t {
                searching = false;
            } else {
                i = (i + 1) & mask;
            }
        }
        i
    }
    /// The place of the entry of `t`, if it has one.
    pub(crate) fn entry(&self, t: Term) -> Option<usize> {
        let s = self.slots[self.slot(t)];
        if s == 0 { None } else { Some((s - 1) as usize) }
    }
    /// The count of the entry at `place`.
    pub(crate) fn count(&self, place: usize) -> usize {
        self.counts[place]
    }
    /// One more occurrence of `t`.
    pub(crate) fn add(&mut self, t: Term) {
        let i = self.slot(t);
        let s = self.slots[i];
        if s == 0 {
            self.keys.push(t);
            self.counts.push(1);
            self.slots[i] = self.keys.len() as u32;
        } else {
            self.counts[(s - 1) as usize] += 1;
        }
    }
    /// One occurrence fewer at `place`, if there is one left.
    pub(crate) fn remove_one(&mut self, place: usize) {
        if self.counts[place] > 0 {
            self.counts[place] -= 1;
        }
    }
    /// Whether no occurrence is left.
    pub(crate) fn all_zero(&self) -> bool {
        let mut zero = true;
        let mut i = 0;
        while i < self.counts.len() {
            if self.counts[i] != 0 {
                zero = false;
            }
            i += 1;
        }
        zero
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts() {
        let mut c = TermCounts::new(3);
        for t in [5, 7, 5, 9, 5] {
            c.add(Term(t));
        }
        assert_eq!(c.entry(Term(4)), None);
        let five = c.entry(Term(5)).unwrap();
        assert_eq!(c.count(five), 3);
        assert_eq!(c.count(c.entry(Term(9)).unwrap()), 1);
        assert!(!c.all_zero());
        for t in [5, 5, 5, 5, 7, 9] {
            let place = c.entry(Term(t)).unwrap();
            c.remove_one(place);
        }
        assert!(c.all_zero());
        // as many different terms as it was made for, colliding or not
        let mut c = TermCounts::new(1000);
        for t in 0..1000 {
            c.add(Term(t * 16));
        }
        for t in 0..1000 {
            assert_eq!(c.count(c.entry(Term(t * 16)).unwrap()), 1);
            assert_eq!(c.entry(Term(t * 16 + 1)), None);
        }
    }
    #[test]
    fn slots() {
        assert_eq!(slots_for(0), 16);
        assert_eq!(slots_for(7), 16);
        assert_eq!(slots_for(8), 32);
        assert_eq!(slots_for(1000), 2048);
    }
}
