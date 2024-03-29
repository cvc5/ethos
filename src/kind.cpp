/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "kind.h"

#include <iostream>

namespace alfc {

std::ostream& operator<<(std::ostream& o, Kind k)
{
  switch (k)
  {
    case Kind::NONE: o << "NONE"; break;
    case Kind::TYPE: o << "TYPE"; break;
    case Kind::FUNCTION_TYPE: o << "FUNCTION_TYPE"; break;
    case Kind::PROOF_TYPE: o << "PROOF_TYPE"; break;
    case Kind::ABSTRACT_TYPE: o << "ABSTRACT_TYPE"; break;
    case Kind::BOOL_TYPE: o << "BOOL_TYPE"; break;
    case Kind::QUOTE_TYPE: o << "QUOTE_TYPE"; break;
    // terms
    case Kind::APPLY: o << "APPLY"; break;
    case Kind::LAMBDA: o << "LAMBDA"; break;
    case Kind::PARAM: o << "PARAM"; break;
    case Kind::CONST: o << "CONST"; break;
    case Kind::PROGRAM_CONST: o << "PROGRAM_CONST"; break;
    case Kind::PROOF_RULE: o << "PROOF_RULE"; break;
    case Kind::VARIABLE: o << "VARIABLE"; break;
    case Kind::ORACLE: o << "ORACLE"; break;
    case Kind::TUPLE: o << "TUPLE"; break;
    case Kind::NULL_EXPR: o << "NIL"; break;
    case Kind::PROGRAM: o << "PROGRAM"; break;
    case Kind::AS: o << "AS"; break;
    case Kind::PARAMETERIZED: o << "PARAMETERIZED"; break;
    // literals
    case Kind::BOOLEAN: o << "BOOLEAN"; break;
    case Kind::NUMERAL: o << "NUMERAL"; break;
    case Kind::DECIMAL: o << "DECIMAL"; break;
    case Kind::RATIONAL: o << "RATIONAL"; break;
    case Kind::HEXADECIMAL: o << "HEXADECIMAL"; break;
    case Kind::BINARY: o << "BINARY"; break;
    case Kind::STRING: o << "STRING"; break;
    // operations on literals
    case Kind::EVAL_IS_EQ: o << "EVAL_IS_EQ"; break;
    case Kind::EVAL_IF_THEN_ELSE: o << "EVAL_IF_THEN_ELSE"; break;
    case Kind::EVAL_REQUIRES: o << "EVAL_REQUIRES"; break;
    case Kind::EVAL_HASH: o << "EVAL_HASH"; break;
    case Kind::EVAL_VAR: o << "EVAL_VAR"; break;
    case Kind::EVAL_TYPE_OF: o << "EVAL_TYPE_OF"; break;
    case Kind::EVAL_NAME_OF: o << "EVAL_NAME_OF"; break;
    // lists
    case Kind::EVAL_NIL: o << "EVAL_EMPTYLIST";break;
    case Kind::EVAL_CONS: o << "EVAL_CONS"; break;
    // boolean
    case Kind::EVAL_NOT: o << "EVAL_NOT"; break;
    case Kind::EVAL_AND: o << "EVAL_AND"; break;
    case Kind::EVAL_OR: o << "EVAL_OR"; break;
    case Kind::EVAL_XOR: o << "EVAL_XOR"; break;
    // arithmetic
    case Kind::EVAL_ADD: o << "EVAL_ADD"; break;
    case Kind::EVAL_NEG: o << "EVAL_NEG"; break;
    case Kind::EVAL_MUL: o << "EVAL_MUL"; break;
    case Kind::EVAL_INT_DIV: o << "EVAL_INT_DIV"; break;
    case Kind::EVAL_INT_MOD: o << "EVAL_INT_MOD"; break;
    case Kind::EVAL_RAT_DIV: o << "EVAL_RAT_DIV"; break;
    case Kind::EVAL_IS_NEG: o << "EVAL_IS_NEG"; break;
    // strings
    case Kind::EVAL_LENGTH: o << "EVAL_LENGTH"; break;
    case Kind::EVAL_CONCAT: o << "EVAL_CONCAT"; break;
    case Kind::EVAL_EXTRACT: o << "EVAL_EXTRACT"; break;
    case Kind::EVAL_FIND: o << "EVAL_FIND"; break;
    // conversions
    case Kind::EVAL_TO_INT: o << "EVAL_TO_INT"; break;
    case Kind::EVAL_TO_RAT: o << "EVAL_TO_RAT"; break;
    case Kind::EVAL_TO_BIN: o << "EVAL_TO_BIN"; break;
    case Kind::EVAL_TO_STRING: o << "EVAL_TO_STRING"; break;
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
    case Kind::NULL_EXPR: ss << "alf.nil"; break;
    // terms
    case Kind::APPLY: ss << "_"; break;
    case Kind::LAMBDA: ss << "lambda"; break;
    case Kind::PROGRAM: ss << "program"; break;
    case Kind::AS: ss << "alf.as"; break;
    case Kind::PARAMETERIZED: ss << "__"; break;
    // operations on literals
    default:
      if (isLiteralOp(k))
      {
        ss << "alf.";
        switch (k)
        {
        case Kind::EVAL_IS_EQ: ss << "is_eq"; break;
        case Kind::EVAL_IF_THEN_ELSE: ss << "ite"; break;
        case Kind::EVAL_REQUIRES: ss << "requires"; break;
        case Kind::EVAL_HASH: ss << "hash"; break;
        case Kind::EVAL_VAR: ss << "var"; break;
        case Kind::EVAL_TYPE_OF: ss << "typeof"; break;
        case Kind::EVAL_NAME_OF: ss << "nameof"; break;
        // lists
        case Kind::EVAL_NIL: ss << "emptylist"; break;
        case Kind::EVAL_CONS: ss << "cons"; break;
        // boolean
        case Kind::EVAL_NOT: ss << "not"; break;
        case Kind::EVAL_AND: ss << "and"; break;
        case Kind::EVAL_OR: ss << "or"; break;
        case Kind::EVAL_XOR: ss << "xor"; break;
        // arithmetic
        case Kind::EVAL_ADD: ss << "add";break;
        case Kind::EVAL_NEG: ss << "neg";break;
        case Kind::EVAL_MUL: ss << "mul";break;
        case Kind::EVAL_INT_DIV: ss << "zdiv";break;
        case Kind::EVAL_INT_MOD: ss << "zmod";break;
        case Kind::EVAL_RAT_DIV: ss << "qdiv";break;
        case Kind::EVAL_IS_NEG: ss << "is_neg";break;
        // strings
        case Kind::EVAL_LENGTH: ss << "len"; break;
        case Kind::EVAL_CONCAT: ss << "concat"; break;
        case Kind::EVAL_EXTRACT: ss << "extract"; break;
        case Kind::EVAL_FIND: ss << "find"; break;
        // conversions
        case Kind::EVAL_TO_INT: ss << "to_z";break;
        case Kind::EVAL_TO_RAT: ss << "to_q";break;
        case Kind::EVAL_TO_BIN: ss << "to_bin";break;
        case Kind::EVAL_TO_STRING: ss << "to_str";break;
        default:ss << "[" << k << "]";break;
        }
      }
      else
      {
        ss << "[" << k << "]";
      }
      break;
  }
  return ss.str();
}

bool isSymbol(Kind k)
{
  switch(k)
  {
    case Kind::PARAM:
    case Kind::CONST:
    case Kind::PROGRAM_CONST:
    case Kind::PROOF_RULE:
    case Kind::VARIABLE:
    case Kind::ORACLE: return true; break;
    default: break;
  }
  return false;
}
bool isLiteral(Kind k)
{
  switch(k)
  {
    case Kind::BOOLEAN:
    case Kind::NUMERAL:
    case Kind::DECIMAL:
    case Kind::RATIONAL:
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    case Kind::STRING: return true; break;
    default: break;
  }
  return false;
}
bool isLiteralOp(Kind k)
{
  switch(k)
  {
    case Kind::EVAL_IS_EQ:
    case Kind::EVAL_IF_THEN_ELSE:
    case Kind::EVAL_REQUIRES:
    case Kind::EVAL_HASH:
    case Kind::EVAL_VAR:
    case Kind::EVAL_TYPE_OF:
    case Kind::EVAL_NAME_OF:
    // lists
    case Kind::EVAL_NIL:
    case Kind::EVAL_CONS:
    // boolean
    case Kind::EVAL_NOT:
    case Kind::EVAL_AND:
    case Kind::EVAL_OR:
    case Kind::EVAL_XOR:
    // arithmetic
    case Kind::EVAL_ADD:
    case Kind::EVAL_NEG:
    case Kind::EVAL_MUL:
    case Kind::EVAL_INT_DIV:
    case Kind::EVAL_INT_MOD:
    case Kind::EVAL_RAT_DIV:
    case Kind::EVAL_IS_NEG:
    // strings
    case Kind::EVAL_LENGTH:
    case Kind::EVAL_CONCAT:
    case Kind::EVAL_EXTRACT:
    case Kind::EVAL_FIND:
    // conversions
    case Kind::EVAL_TO_INT:
    case Kind::EVAL_TO_RAT:
    case Kind::EVAL_TO_BIN:
    case Kind::EVAL_TO_STRING:return true; break;
    default: break;
  }
  return false;
}

}  // namespace alfc
