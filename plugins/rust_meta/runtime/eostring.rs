//! Strings of Unicode code points, as `util/string.cpp` in Ethos.
//!
//! From `crates/pathos-term/src/eostring.rs` of pathos (as of its commit
//! acae6aa). The reading of a string from text (`parse`) and its printing
//! are in front.rs; the operations here are written with loops over the
//! code points.

/// The number of code points a string character can take: the first three
/// planes of Unicode, as in the SMT-LIB theory of strings.
pub const NUM_CODES: u32 = 196_608;

/// A string literal: a sequence of code points below [`NUM_CODES`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct EoString(Vec<u32>);

impl EoString {
    pub fn from_code_points(v: Vec<u32>) -> EoString {
        EoString(v)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn code_points(&self) -> &[u32] {
        &self.0
    }

    pub fn concat(&self, other: &EoString) -> EoString {
        let mut v = Vec::with_capacity(self.0.len() + other.0.len());
        append(&mut v, &self.0);
        append(&mut v, &other.0);
        EoString(v)
    }

    /// The first position at which `y` occurs, if any.
    pub fn find(&self, y: &EoString) -> Option<usize> {
        if self.len() < y.len() {
            return None;
        }
        if y.is_empty() {
            return Some(0);
        }
        let last = self.len() - y.len();
        let mut found = None;
        let mut i = 0;
        while i <= last {
            if occurs_at(&self.0, &y.0, i) {
                found = Some(i);
                i = last;
            }
            i += 1;
        }
        found
    }

    /// The substring of `len` code points starting at `start`. Requires
    /// `start + len <= self.len()`.
    pub fn substr(&self, start: usize, len: usize) -> EoString {
        let mut v = Vec::with_capacity(len);
        let mut i = 0;
        while i < len {
            v.push(self.0[start + i]);
            i += 1;
        }
        EoString(v)
    }
}

/// Adds the code points of `from` to `to`.
fn append(to: &mut Vec<u32>, from: &[u32]) {
    let mut i = 0;
    while i < from.len() {
        to.push(from[i]);
        i += 1;
    }
}

/// Whether `y` occurs in `x` at position `at`. Requires
/// `at + y.len() <= x.len()`.
fn occurs_at(x: &[u32], y: &[u32], at: usize) -> bool {
    let mut same = true;
    let mut i = 0;
    while i < y.len() {
        if x[at + i] != y[i] {
            same = false;
        }
        i += 1;
    }
    same
}

#[cfg(test)]
mod tests {
    use super::*;

    fn roundtrip(s: &str) -> String {
        EoString::parse(s, true).to_string()
    }

    #[test]
    fn escapes() {
        assert_eq!(EoString::parse("\\u{41}", true).code_points(), &[0x41]);
        assert_eq!(
            EoString::parse("\\u0041b", true).code_points(),
            &[0x41, 0x62]
        );
        // in range unless the checker was generated for a smaller maximum, in
        // which case it is kept verbatim
        if crate::MAX_CODE_POINT >= 0x2ffff {
            assert_eq!(
                EoString::parse("\\u{2ffff}", true).code_points(),
                &[0x2ffff]
            );
        } else {
            assert_eq!(roundtrip("\\u{2ffff}"), "\\u{5c}u{2ffff}");
        }
        // out of range: kept verbatim
        if crate::MAX_CODE_POINT < 0x30000 {
            assert_eq!(roundtrip("\\u{30000}"), "\\u{5c}u{30000}");
        } else {
            assert_eq!(roundtrip("\\u{30000}"), "\\u{30000}");
        }
        assert_eq!(roundtrip("\\u{110000}"), "\\u{5c}u{110000}");
        // malformed
        assert_eq!(roundtrip("\\u{}"), "\\u{5c}u{}");
        assert_eq!(roundtrip("\\u12"), "\\u{5c}u12");
        assert_eq!(roundtrip("\\x"), "\\u{5c}x");
        assert_eq!(roundtrip("a\\"), "a\\u{5c}");
        assert_eq!(roundtrip("\\u{a}"), "\\u{a}");
    }

    #[test]
    fn printing_is_stable() {
        for s in ["abc", "\\u{5c}u{30000}", "\\u{7f}", "\\u{1}x"] {
            assert_eq!(roundtrip(&roundtrip(s)), roundtrip(s));
        }
    }

    #[test]
    fn unprintable_input_is_dropped() {
        assert_eq!(EoString::parse("a\tb\nc", true).to_string(), "abc");
    }

    #[test]
    fn find_and_substr() {
        let s = EoString::parse("hello", false);
        assert_eq!(s.find(&EoString::parse("ll", false)), Some(2));
        assert_eq!(s.find(&EoString::parse("", false)), Some(0));
        assert_eq!(s.find(&EoString::parse("z", false)), None);
        assert_eq!(s.substr(1, 3).to_string(), "ell");
    }
}
