#ifndef KIND_H
#define KIND_H

#include <sstream>
#include <string>

namespace alfc {

/**
 */
enum class Kind
{
  NONE = 0,
  
  // types
  TYPE,
  FUNCTION_TYPE,
  PROOF_TYPE,
  ABSTRACT_TYPE,
  BOOL_TYPE,
  QUOTE_TYPE,
  
  // terms
  APPLY,
  LAMBDA,
  PARAM,
  CONST,
  PROGRAM_CONST,
  PROOF_RULE,
  VARIABLE,
  VARIABLE_LIST,
  NIL,
  PROGRAM,
  PAIR,
  COLLECT,
  FAIL,

  // literals
  BOOLEAN,
  NUMERAL,
  DECIMAL,
  HEXADECIMAL,
  BINARY,
  STRING,

  // operations on literals
  // core
  EVAL_IS_EQ,
  EVAL_IF_THEN_ELSE,
  EVAL_REQUIRES,
  EVAL_CONS,
  EVAL_APPEND,
  // boolean
  EVAL_NOT,
  EVAL_AND,
  EVAL_OR,
  // arithmetic
  EVAL_ADD,
  EVAL_NEG,
  EVAL_MUL,
  EVAL_INT_DIV,
  EVAL_RAT_DIV,
  EVAL_IS_NEG,
  EVAL_IS_ZERO,
  // strings
  EVAL_LENGTH,
  EVAL_CONCAT,
  EVAL_EXTRACT,
  // conversions
  EVAL_TO_INT,
  EVAL_TO_RAT,
  EVAL_TO_BV,
  EVAL_TO_STRING
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Kind k);

std::string kindToTerm(Kind k);

/** */
bool isSymbol(Kind k);
/** */
bool isLiteral(Kind k);
/** */
bool isLiteralOp(Kind k);

}  // namespace alfc

#endif /* KIND_H */
