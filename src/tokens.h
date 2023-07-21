#ifndef TOKENS_H
#define TOKENS_H

#include <sstream>
#include <string>

namespace alfc {

/**
 */
enum class Token
{
  EOF_TOK = 0,
  ABSTRACT_TYPE,
  ASSUME,
  ATTRIBUTE,
  BOOL_TYPE,
  BINARY_LITERAL,
  DECIMAL_LITERAL,
  DECLARE_CONST,
  DECLARE_CONSTS,
  DECLARE_FUN,
  DECLARE_RULE,
  DECLARE_SORT,
  DECLARE_TYPE,
  DEFINE_CONST,
  DEFINE_FUN,
  DEFINE_SORT,
  DEFINE_TYPE,
  ECHO,
  EXIT,
  HEX_LITERAL,
  INCLUDE,
  INTEGER_LITERAL,
  KEYWORD,
  LET,
  LPAREN,
  NUMERAL,
  PAR,
  PROGRAM,
  PROOF,
  PROOF_TYPE,
  QUOTED_SYMBOL,
  RESET,
  RPAREN,
  SET_INFO,
  SET_LOGIC,
  SET_OPTION,
  STEP,
  STRING_LITERAL,
  SYMBOL,
  TYPE,
  UNTERMINATED_QUOTED_SYMBOL,
  UNTERMINATED_STRING_LITERAL,
  NONE
};

/** Print a token to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Token t);

}  // namespace alfc

#endif /* TOKENS_H */
