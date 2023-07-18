#ifndef TOKENS_H
#define TOKENS_H

#include <sstream>
#include <string>

namespace atc {

/**
 */
enum class Token
{
  EOF_TOK = 0,
  ASSUME_TOK,
  ATTRIBUTE_TOK,
  BINARY_LITERAL,
  DECIMAL_LITERAL,
  DECLARE_CONST_TOK,
  DECLARE_FUN_TOK,
  DECLARE_POOL_TOK,
  DECLARE_SORT_TOK,
  DEFINE_CONST_TOK,
  DEFINE_FUN_TOK,
  DEFINE_SORT_TOK,
  ECHO_TOK,
  EXIT_TOK,
  HEX_LITERAL,
  INCLUDE_TOK,
  INTEGER_LITERAL,
  KEYWORD,
  LET_TOK,
  LPAREN_TOK,
  NUMERAL,
  PAR_TOK,
  QUOTED_SYMBOL,
  RESET_TOK,
  RPAREN_TOK,
  SET_INFO_TOK,
  SET_LOGIC_TOK,
  SET_OPTION_TOK,
  STRING_LITERAL,
  SYMBOL,
  UNTERMINATED_QUOTED_SYMBOL,
  UNTERMINATED_STRING_LITERAL,
  NONE
};

/** Print a token to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Token t);

}  // namespace atc

#endif /* TOKENS_H */
