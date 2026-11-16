// Copied from daniel-larraz/pathos at f77aff7a457a73fb1708b8867d76f21e50fef081.
// BSD-3-Clause; see LICENSE.pathos. Local changes belong to this backend.
//! Strings of Unicode code points, as `util/string.cpp` in Ethos.

use std::fmt::Write;

/// The number of code points a string character can take: the first three
/// planes of Unicode, as in the SMT-LIB theory of strings.
pub const NUM_CODES: u32 = 196_608;

/// A string literal: a sequence of code points below [`NUM_CODES`].
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct EoString(Vec<u32>);

fn is_hex_digit(c: char) -> bool {
    c.is_ascii_hexdigit()
}

/// Characters outside printable ASCII are dropped, as in Ethos, whose
/// `addCharToInternal` builds an error message for them and then discards it.
fn add_char(c: char, out: &mut Vec<u32>) {
    let code = u32::from(c);
    if (32..=127).contains(&code) {
        out.push(code);
    }
}

impl EoString {
    pub fn from_code_points(v: Vec<u32>) -> EoString {
        EoString(v)
    }

    /// Converts text to a string. With `use_escapes`, the SMT-LIB escape
    /// sequences `폒d1d0` and `\u{d0}` to `\u{d4d3d2d1d0}` denote single
    /// code points; malformed or out-of-range sequences are kept verbatim.
    pub fn parse(s: &str, use_escapes: bool) -> EoString {
        let chars: Vec<char> = s.chars().collect();
        let mut out = Vec::with_capacity(chars.len());
        let mut i = 0;
        while i < chars.len() {
            let mut si = chars[i];
            if si != '\\' || !use_escapes {
                add_char(si, &mut out);
                i += 1;
                continue;
            }
            // The characters read so far, in case this is not an escape.
            let mut non_esc = Vec::new();
            add_char(si, &mut non_esc);
            i += 1;
            let mut is_escape = true;
            let mut hex = String::new();
            if i >= chars.len() || chars[i] != 'u' {
                is_escape = false;
            } else {
                add_char(chars[i], &mut non_esc);
                i += 1;
                let mut is_start = true;
                let mut is_end = false;
                let mut has_brace = false;
                while i < chars.len() {
                    si = chars[i];
                    if is_start {
                        is_start = false;
                        if si == '{' {
                            has_brace = true;
                            add_char(si, &mut non_esc);
                            i += 1;
                            continue;
                        }
                    } else if si == '}' {
                        // only ends an escape opened by a brace, with a digit
                        is_escape = has_brace && !hex.is_empty();
                        is_end = true;
                        add_char(si, &mut non_esc);
                        i += 1;
                        break;
                    }
                    if !is_hex_digit(si) {
                        is_escape = false;
                        break;
                    }
                    hex.push(si);
                    add_char(si, &mut non_esc);
                    i += 1;
                    if !has_brace && hex.len() == 4 {
                        is_end = true;
                        break;
                    } else if has_brace && hex.len() > 5 {
                        is_escape = false;
                        break;
                    }
                }
                if !is_end {
                    is_escape = false;
                }
            }
            if is_escape {
                match u32::from_str_radix(&hex, 16) {
                    Ok(val) if val < NUM_CODES => out.push(val),
                    _ => is_escape = false,
                }
            }
            if !is_escape {
                out.extend_from_slice(&non_esc);
            }
        }
        EoString(out)
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
        let mut v = self.0.clone();
        v.extend_from_slice(&other.0);
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
        self.0.windows(y.len()).position(|w| w == y.0.as_slice())
    }

    /// The substring of `len` code points starting at `start`. Requires
    /// `start + len <= self.len()`.
    pub fn substr(&self, start: usize, len: usize) -> EoString {
        EoString(self.0[start..start + len].to_vec())
    }
}

impl std::fmt::Display for EoString {
    /// Printable ASCII is printed as is, except the backslash; everything
    /// else is printed as `\u{<hex>}`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for &c in &self.0 {
            if (32..=126).contains(&c) && c != u32::from(b'\\') {
                f.write_char(char::from_u32(c).unwrap_or('?'))?;
            } else {
                write!(f, "\\u{{{c:x}}}")?;
            }
        }
        Ok(())
    }
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
        assert_eq!(
            EoString::parse("\\u{2ffff}", true).code_points(),
            &[0x2ffff]
        );
        // out of range: kept verbatim
        assert_eq!(roundtrip("\\u{30000}"), "\\u{5c}u{30000}");
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
