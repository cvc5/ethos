#include "tokens.h"

#include <iostream>

namespace atc {

std::ostream& operator<<(std::ostream& o, Token t)
{
  switch (t)
  {
    case Token::EOF_TOK: o << "EOF_TOK"; break;
    case Token::ATTRIBUTE_TOK: o << "ATTRIBUTE_TOK"; break;
    case Token::BINARY_LITERAL: o << "BINARY_LITERAL"; break;
    case Token::DECIMAL_LITERAL: o << "DECIMAL_LITERAL"; break;
    case Token::DECLARE_CONST_TOK: o << "DECLARE_CONST_TOK"; break;
    case Token::DECLARE_FUN_TOK: o << "DECLARE_FUN_TOK"; break;
    case Token::DECLARE_SORT_TOK: o << "DECLARE_SORT_TOK"; break;
    case Token::DEFINE_CONST_TOK: o << "DEFINE_CONST_TOK"; break;
    case Token::DEFINE_FUN_TOK: o << "DEFINE_FUN_TOK"; break;
    case Token::DEFINE_SORT_TOK: o << "DEFINE_SORT_TOK"; break;
    case Token::ECHO_TOK: o << "ECHO_TOK"; break;
    case Token::EXIT_TOK: o << "EXIT_TOK"; break;
    case Token::HEX_LITERAL: o << "HEX_LITERAL"; break;
    case Token::INCLUDE_TOK: o << "INCLUDE_TOK"; break;
    case Token::INTEGER_LITERAL: o << "INTEGER_LITERAL"; break;
    case Token::KEYWORD: o << "KEYWORD"; break;
    case Token::LET_TOK: o << "LET_TOK"; break;
    case Token::LPAREN_TOK: o << "LPAREN_TOK"; break;
    case Token::NUMERAL: o << "NUMERAL"; break;
    case Token::PAR_TOK: o << "PAR_TOK"; break;
    case Token::QUOTED_SYMBOL: o << "QUOTED_SYMBOL"; break;
    case Token::RESET_TOK: o << "RESET_TOK"; break;
    case Token::RPAREN_TOK: o << "RPAREN_TOK"; break;
    case Token::SET_INFO_TOK: o << "SET_INFO_TOK"; break;
    case Token::SET_LOGIC_TOK: o << "SET_LOGIC_TOK"; break;
    case Token::SET_OPTION_TOK: o << "SET_OPTION_TOK"; break;
    case Token::STRING_LITERAL: o << "STRING_LITERAL"; break;
    case Token::SYMBOL: o << "SYMBOL"; break;
    case Token::UNTERMINATED_QUOTED_SYMBOL:
      o << "UNTERMINATED_QUOTED_SYMBOL";
      break;
    case Token::UNTERMINATED_STRING_LITERAL:
      o << "UNTERMINATED_STRING_LITERAL";
      break;
    case Token::NONE: o << "NONE"; break;
    default: o << "Unknown Token (" << unsigned(t) << ")"; break;
  }
  return o;
}

}  // namespace atc
