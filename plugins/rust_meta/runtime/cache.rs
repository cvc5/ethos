//! Memoization over arena-local handles. Every stored result is the result of
//! a completed pure evaluation on these exact arguments. Growing the arena
//! preserves that invariant; errors and unfinished evaluations are never stored.

use crate::Term;

#[derive(Copy, Clone)]
pub(crate) struct ProgramId(pub(crate) u32);

#[derive(Copy, Clone)]
pub(crate) enum TypeCacheKind {
    Eunoia,
    #[allow(dead_code)] // Signatures without SMT semantics only query EO types.
    Smt,
}

/// Cumulative counters for measuring memoization. Clearing caches resets them.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct CacheStats {
    pub type_hits: u64,
    pub type_misses: u64,
    pub program_hits: u64,
    pub program_misses: u64,
    pub type_entries: usize,
    pub program_entries: usize,
}

struct TypeEntry {
    eo: Option<Term>,
    smt: Option<Term>,
}

impl TypeEntry {
    fn empty() -> Self {
        Self {
            eo: None,
            smt: None,
        }
    }
}

struct ProgramEntry {
    program: ProgramId,
    args: Vec<Term>,
    result: Term,
}

/// An open-addressed table. Slots contain entry indices plus one; zero is
/// empty. Keys are compared in full after hashing, including program and arity.
struct ProgramCache {
    entries: Vec<ProgramEntry>,
    slots: Vec<u32>,
    max_entries: usize,
}

impl ProgramCache {
    fn new(max_entries: usize) -> Self {
        Self {
            entries: Vec::new(),
            slots: Vec::new(),
            max_entries,
        }
    }

    fn hash(program: ProgramId, args: &[Term]) -> u64 {
        let mut hash = 0xcbf2_9ce4_8422_2325_u64 ^ u64::from(program.0);
        let mut i = 0;
        while i < args.len() {
            hash = (hash ^ u64::from(args[i].0)).wrapping_mul(0x100_0000_01b3);
            i += 1;
        }
        hash ^= args.len() as u64;
        hash = (hash ^ (hash >> 32)).wrapping_mul(0xd6e8_feb8_6659_fd93);
        hash ^ (hash >> 32)
    }

    fn matches(entry: &ProgramEntry, program: ProgramId, args: &[Term]) -> bool {
        if entry.program.0 != program.0 || entry.args.len() != args.len() {
            return false;
        }
        let mut i = 0;
        while i < args.len() {
            if entry.args[i].0 != args[i].0 {
                return false;
            }
            i += 1;
        }
        true
    }

    /// The table is nonempty, has a power-of-two length, and is at most half
    /// full, so probing always reaches an empty slot.
    fn find(&self, program: ProgramId, args: &[Term]) -> usize {
        let mask = self.slots.len() - 1;
        let mut slot = (Self::hash(program, args) as usize) & mask;
        loop {
            let index = self.slots[slot];
            if index == 0 || Self::matches(&self.entries[(index - 1) as usize], program, args) {
                return slot;
            }
            slot = (slot + 1) & mask;
        }
    }

    fn get(&self, program: ProgramId, args: &[Term]) -> Option<Term> {
        if self.slots.is_empty() {
            return None;
        }
        let slot = self.find(program, args);
        let index = self.slots[slot];
        if index == 0 {
            None
        } else {
            Some(self.entries[(index - 1) as usize].result)
        }
    }

    fn grow(&mut self) -> bool {
        let size = if self.slots.is_empty() {
            16
        } else {
            let Some(size) = self.slots.len().checked_mul(2) else {
                return false;
            };
            size
        };
        let mut slots = vec![0; size];
        let mut i = 0;
        while i < self.entries.len() {
            let entry = &self.entries[i];
            let mut slot = (Self::hash(entry.program, &entry.args) as usize) & (size - 1);
            while slots[slot] != 0 {
                slot = (slot + 1) & (size - 1);
            }
            slots[slot] = (i as u32) + 1;
            i += 1;
        }
        self.slots = slots;
        true
    }

    fn insert(&mut self, program: ProgramId, args: &[Term], result: Term) {
        if self.entries.len() >= self.max_entries || self.entries.len() >= u32::MAX as usize {
            return;
        }
        if self.entries.len() >= self.slots.len() / 2 && !self.grow() {
            return;
        }
        let slot = self.find(program, args);
        if self.slots[slot] != 0 {
            return;
        }
        let mut key = Vec::new();
        let mut i = 0;
        while i < args.len() {
            key.push(args[i]);
            i += 1;
        }
        self.entries.push(ProgramEntry {
            program,
            args: key,
            result,
        });
        self.slots[slot] = self.entries.len() as u32;
    }

    fn clear(&mut self) {
        self.entries = Vec::new();
        let mut i = 0;
        while i < self.slots.len() {
            self.slots[i] = 0;
            i += 1;
        }
    }
}

/// All evaluation caches live here. A type row is allocated with each arena
/// node, with distinct EO/SMT slots because these are different pure functions.
pub(crate) struct Caches {
    types: Vec<TypeEntry>,
    programs: ProgramCache,
    enabled: bool,
    stats: CacheStats,
}

impl Caches {
    pub(crate) fn new(program_limit: usize) -> Self {
        Self {
            types: vec![TypeEntry::empty()], // the initial Stuck handle
            programs: ProgramCache::new(program_limit),
            enabled: true,
            stats: CacheStats::default(),
        }
    }

    pub(crate) fn push_term(&mut self) {
        self.types.push(TypeEntry::empty());
    }

    pub(crate) fn stats(&self) -> CacheStats {
        let mut stats = self.stats;
        stats.program_entries = self.programs.entries.len();
        stats
    }

    pub(crate) fn set_enabled(&mut self, enabled: bool) {
        self.enabled = enabled;
    }

    pub(crate) fn clear(&mut self) {
        let mut i = 0;
        while i < self.types.len() {
            self.types[i] = TypeEntry::empty();
            i += 1;
        }
        self.programs.clear();
        self.stats = CacheStats::default();
    }

    pub(crate) fn type_get(&mut self, kind: TypeCacheKind, term: Term) -> Option<Term> {
        if !self.enabled {
            return None;
        }
        let i = term.0 as usize;
        if i >= self.types.len() {
            return None;
        }
        let entry = &self.types[i];
        let result = match kind {
            TypeCacheKind::Eunoia => entry.eo,
            TypeCacheKind::Smt => entry.smt,
        };
        if result.is_some() {
            self.stats.type_hits = self.stats.type_hits.saturating_add(1);
        } else {
            self.stats.type_misses = self.stats.type_misses.saturating_add(1);
        }
        result
    }

    pub(crate) fn type_insert(&mut self, kind: TypeCacheKind, term: Term, result: Term) {
        if !self.enabled {
            return;
        }
        let Some(entry) = self.types.get_mut(term.0 as usize) else {
            return;
        };
        let slot = match kind {
            TypeCacheKind::Eunoia => &mut entry.eo,
            TypeCacheKind::Smt => &mut entry.smt,
        };
        if slot.is_none() {
            self.stats.type_entries += 1;
        }
        *slot = Some(result);
    }

    pub(crate) fn program_get(&mut self, program: ProgramId, args: &[Term]) -> Option<Term> {
        if !self.enabled {
            return None;
        }
        let result = self.programs.get(program, args);
        if result.is_some() {
            self.stats.program_hits = self.stats.program_hits.saturating_add(1);
        } else {
            self.stats.program_misses = self.stats.program_misses.saturating_add(1);
        }
        result
    }

    pub(crate) fn program_insert(&mut self, program: ProgramId, args: &[Term], result: Term) {
        if self.enabled {
            self.programs.insert(program, args, result);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collisions_growth_program_ids_arity_and_stuck_results() {
        let mut table = ProgramCache::new(1000);
        // All these keys initially hash to slot zero, forcing collisions.
        let mut keys = Vec::new();
        let mut n = 0;
        while keys.len() < 100 {
            let args = [Term(n)];
            if ProgramCache::hash(ProgramId(1), &args) & 15 == 0 {
                keys.push(Term(n));
            }
            n += 1;
        }
        let mut i = 0;
        while i < keys.len() {
            table.insert(ProgramId(1), &[keys[i]], Term(i as u32));
            i += 1;
        }
        i = 0;
        while i < keys.len() {
            assert_eq!(table.get(ProgramId(1), &[keys[i]]), Some(Term(i as u32)));
            i += 1;
        }
        assert_eq!(table.get(ProgramId(2), &[keys[0]]), None);
        assert_eq!(table.get(ProgramId(1), &[keys[0], Term(0)]), None);
        table.insert(ProgramId(2), &[keys[0]], Term(500));
        assert_eq!(table.get(ProgramId(2), &[keys[0]]), Some(Term(500)));
        table.insert(ProgramId(1), &[], Term(0));
        assert_eq!(table.get(ProgramId(1), &[]), Some(Term(0)));
        table.clear();
        assert_eq!(table.get(ProgramId(1), &[keys[0]]), None);
        table.insert(ProgramId(1), &[keys[0]], Term(7));
        assert_eq!(table.get(ProgramId(1), &[keys[0]]), Some(Term(7)));
    }

    #[test]
    fn bounded_optional_cache_and_type_domains() {
        let mut caches = Caches::new(1);
        caches.push_term();
        caches.type_insert(TypeCacheKind::Eunoia, Term(1), Term(0));
        assert_eq!(
            caches.type_get(TypeCacheKind::Eunoia, Term(1)),
            Some(Term(0))
        );
        assert_eq!(caches.type_get(TypeCacheKind::Smt, Term(1)), None);
        caches.type_insert(TypeCacheKind::Smt, Term(1), Term(1));
        assert_eq!(caches.type_get(TypeCacheKind::Smt, Term(1)), Some(Term(1)));
        caches.program_insert(ProgramId(1), &[Term(1)], Term(0));
        caches.program_insert(ProgramId(2), &[Term(1)], Term(1));
        assert_eq!(caches.program_get(ProgramId(1), &[Term(1)]), Some(Term(0)));
        assert_eq!(caches.program_get(ProgramId(2), &[Term(1)]), None);
        assert_eq!(caches.stats().program_entries, 1);
        caches.set_enabled(false);
        assert_eq!(caches.type_get(TypeCacheKind::Eunoia, Term(1)), None);
        assert_eq!(caches.program_get(ProgramId(1), &[Term(1)]), None);
        caches.set_enabled(true);
        caches.clear();
        assert_eq!(caches.stats(), CacheStats::default());
        assert_eq!(caches.type_get(TypeCacheKind::Eunoia, Term(1)), None);
        assert_eq!(caches.type_get(TypeCacheKind::Smt, Term(1)), None);
    }
}
