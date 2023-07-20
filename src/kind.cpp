#include "kind.h"

#include <iostream>

namespace atc {

std::ostream& operator<<(std::ostream& o, Kind k)
{
  switch (k)
  {
    case Kind::NONE: o << "NONE"; break;
    case Kind::TYPE: o << "TYPE"; break;
    case Kind::FUNCTION_TYPE: o << "FUNCTION_TYPE"; break;
    case Kind::REQUIRES_TYPE: o << "REQUIRES_TYPE"; break;
    case Kind::PROOF_TYPE: o << "PROOF_TYPE"; break;
    case Kind::ABSTRACT_TYPE: o << "ABSTRACT_TYPE"; break;
    case Kind::BOOL_TYPE: o << "BOOL_TYPE"; break;
    case Kind::QUOTE_TYPE: o << "QUOTE_TYPE"; break;
    // terms
    case Kind::APPLY: o << "APPLY"; break;
    case Kind::LAMBDA: o << "LAMBDA"; break;
    case Kind::CONST: o << "CONST"; break;
    case Kind::VARIABLE: o << "VARIABLE"; break;
    case Kind::VARIABLE_LIST: o << "VARIABLE_LIST"; break;
    case Kind::QUOTE: o << "QUOTE"; break;
    // literals
    case Kind::INTEGER: o << "INTEGER"; break;
    case Kind::DECIMAL: o << "DECIMAL"; break;
    case Kind::HEXADECIMAL: o << "HEXADECIMAL"; break;
    case Kind::BINARY: o << "BINARY"; break;
    case Kind::STRING: o << "STRING"; break;
    // programs
    case Kind::PROGRAM: o << "PROGRAM"; break;
    case Kind::PAIR: o << "PAIR"; break;
    default: o << "UnknownKind(" << unsigned(k) << ")"; break;
  }
  return o;
}

std::string kindToTerm(Kind k)
{
  std::stringstream ss;
  switch (k)
  {
    case Kind::TYPE: ss << "Type"; break;
    case Kind::FUNCTION_TYPE: ss << "->"; break;
    case Kind::PROOF_TYPE: ss << "Proof"; break;
    case Kind::ABSTRACT_TYPE: ss << "?"; break;
    case Kind::BOOL_TYPE: ss << "Bool"; break;
    case Kind::QUOTE_TYPE: ss << "Quote"; break;
    // terms
    case Kind::APPLY: ss << "@"; break;
    case Kind::LAMBDA: ss << "lambda"; break;
    case Kind::QUOTE: ss << "quote"; break;
    default: ss << "[" << k << "]"; break;
  }
  return ss.str();
}

}  // namespace atc
