#include "tokens.h"

#include <iostream>

namespace atc {

std::ostream& operator<<(std::ostream& o, Token t)
{
  switch (t)
  {
    case Token::EOF_TOK: o << "EOF"; break;
    case Token::ATTRIBUTE: o << "ATTRIBUTE"; break;
    case Token::BINARY_LITERAL: o << "BINARY_LITERAL"; break;
    case Token::DECIMAL_LITERAL: o << "DECIMAL_LITERAL"; break;
    case Token::DECLARE_CONST: o << "DECLARE_CONST"; break;
    case Token::DECLARE_FUN: o << "DECLARE_FUN"; break;
    case Token::DECLARE_SORT: o << "DECLARE_SORT"; break;
    case Token::DECLARE_TYPE: o << "DECLARE_TYPE"; break;
    case Token::DEFINE_CONST: o << "DEFINE_CONST"; break;
    case Token::DEFINE_FUN: o << "DEFINE_FUN"; break;
    case Token::DEFINE_SORT: o << "DEFINE_SORT"; break;
    case Token::DEFINE_TYPE: o << "DEFINE_TYPE"; break;
    case Token::ECHO: o << "ECHO"; break;
    case Token::EXIT: o << "EXIT"; break;
    case Token::HEX_LITERAL: o << "HEX_LITERAL"; break;
    case Token::INCLUDE: o << "INCLUDE"; break;
    case Token::INTEGER_LITERAL: o << "INTEGER_LITERAL"; break;
    case Token::KEYWORD: o << "KEYWORD"; break;
    case Token::LET: o << "LET"; break;
    case Token::LPAREN: o << "LPAREN"; break;
    case Token::NUMERAL: o << "NUMERAL"; break;
    case Token::PAR: o << "PAR"; break;
    case Token::PROOF: o << "PROOF"; break;
    case Token::QUOTED_SYMBOL: o << "QUOTED_SYMBOL"; break;
    case Token::RESET: o << "RESET"; break;
    case Token::RPAREN: o << "RPAREN"; break;
    case Token::SET_INFO: o << "SET_INFO"; break;
    case Token::SET_LOGIC: o << "SET_LOGIC"; break;
    case Token::SET_OPTION: o << "SET_OPTION"; break;
    case Token::STEP: o << "STEP"; break;
    case Token::STRING_LITERAL: o << "STRING_LITERAL"; break;
    case Token::SYMBOL: o << "SYMBOL"; break;
    case Token::TYPE: o << "TYPE"; break;
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
