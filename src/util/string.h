#ifndef UTIL__STRING_H
#define UTIL__STRING_H

#include <iosfwd>
#include <string>
#include <vector>
#include <cstdint>

namespace alfc {

/** The cvc5 string class
 *
 * This data structure is the domain of values for the string type. It can also
 * be used as a generic utility for representing strings.
 */
class String
{
 public:
  /**
   * This is the cardinality of the alphabet that is representable by this
   * class. Notice that this must be greater than or equal to the cardinality
   * of the alphabet that the string theory reasons about.
   *
   * This must be strictly less than std::numeric_limits<unsigned>::max().
   *
   * As per the SMT-LIB standard for strings, we support the first 3 planes of
   * Unicode characters, where 196608 = 3*16^4.
   */
  static inline unsigned num_codes() { return 196608; }
  /** constructors for String
   *
   * Internally, a cvc5::internal::String is represented by a vector of unsigned
   * integers (d_str) representing the code points of the characters.
   *
   * To build a string from a C++ string, we may process escape sequences
   * according to the SMT-LIB standard. In particular, if useEscSequences is
   * true, we convert unicode escape sequences:
   *  \u d_3 d_2 d_1 d_0
   *  \u{d_0}
   *  \u{d_1 d_0}
   *  \u{d_2 d_1 d_0}
   *  \u{d_3 d_2 d_1 d_0}
   *  \u{d_4 d_3 d_2 d_1 d_0}
   * where d_0 ... d_4 are hexadecimal digits, to the appropriate character.
   *
   * If useEscSequences is false, then the characters of the constructed
   * cvc5::internal::String correspond one-to-one with the input string.
   */
  String() = default;
  explicit String(const std::string& s, bool useEscSequences = false)
      : d_str(toInternal(s, useEscSequences))
  {
  }
  explicit String(const std::vector<unsigned>& s);

  String& operator=(const String& y) {
    if (this != &y) {
      d_str = y.d_str;
    }
    return *this;
  }

  String concat(const String& other) const;

  bool operator==(const String& y) const { return cmp(y) == 0; }

  /* toString
   * Converts this string to a std::string.
   *
   * The unprintable characters are converted to unicode escape sequences as
   * described above.
   *
   * If useEscSequences is false, the string's printable characters are
   * printed as characters. Notice that for all std::string s having only
   * printable characters, we have that
   *    cvc5::internal::String( s ).toString() = s.
   */
  std::string toString(bool useEscSequences = false) const;
  /** is less than or equal to string y */
  bool isLeq(const String& y) const;
  /** Return the length of the string */
  std::size_t size() const { return d_str.size(); }

  /**
   * Return the first position y occurs in this string, or std::string::npos
   * otherwise.
   */
  std::size_t find(const String& y, const std::size_t start = 0) const;
  /**
   * Return the first position y occurs in this string searching from the end,
   * or std::string::npos otherwise.
   */
  std::size_t rfind(const String& y, const std::size_t start = 0) const;
  /** Replace the character at index i in this string with t */
  String update(std::size_t i, const String& t) const;
  /** Replace the first occurrence of s in this string with t */
  String replace(const String& s, const String& t) const;
  /** Return the substring of this string starting at index i with size at most
   * j */
  String substr(std::size_t i, std::size_t j) const;

  /**
   * Returns true if this string corresponds in text to a number, for example
   * this returns true for strings "7", "12", "004", "0" and false for strings
   * "abc", "4a", "-4", "".
   */
  bool isNumber() const;
  /** Get the unsigned representation (code points) of this string */
  const std::vector<unsigned>& getVec() const { return d_str; }
  /** is the unsigned a digit?
   *
   * This is true for code points between 48 ('0') and 57 ('9').
   */
  static bool isDigit(unsigned character);
  /** is the unsigned a hexadecimal digit?
   *
   * This is true for code points between 48 ('0') and 57 ('9'), code points
   * between 65 ('A') and 70 ('F) and code points between 97 ('a') and 102 ('f).
   */
  static bool isHexDigit(unsigned character);
  /** is the unsigned a printable code point?
   *
   * This is true for Unicode 32 (' ') to 126 ('~').
   */
  static bool isPrintable(unsigned character);

  /**
   * Returns the maximum length of string representable by this class.
   * Corresponds to the maximum size of d_str.
   */
  static size_t maxSize();
 private:
  /**
   * Helper for toInternal: add character ch to vector vec, storing a string in
   * internal format. This throws an error if ch is not a printable character,
   * since non-printable characters must be escaped in SMT-LIB.
   */
  static void addCharToInternal(unsigned char ch, std::vector<unsigned>& vec);
  /**
   * Convert the string s to the internal format (vector of code points).
   * The argument useEscSequences is whether to process unicode escape
   * sequences.
   */
  static std::vector<unsigned> toInternal(const std::string& s,
                                          bool useEscSequences);

  /**
   * Returns a negative number if *this < y, 0 if *this and y are equal and a
   * positive number if *this > y.
   */
  int cmp(const String& y) const;
  /** The data */
  std::vector<unsigned> d_str;
}; /* class String */

std::ostream& operator<<(std::ostream& os, const String& s);

}  // namespace cvc5::internal

#endif /* UTIL__STRING_H */
