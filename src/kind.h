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
  REQUIRES_TYPE,
  PROOF_TYPE,
  ABSTRACT_TYPE,
  BOOL_TYPE,
  QUOTE_TYPE,
  
  // terms
  APPLY,
  LAMBDA,
  CONST,
  PROGRAM_CONST,
  PROOF_RULE,
  VARIABLE,
  VARIABLE_LIST,
  QUOTE,
  NIL,
  PROGRAM,
  PAIR,

  // literals
  BOOLEAN,
  NUMERAL,
  DECIMAL,
  HEXADECIMAL,
  BINARY,
  STRING,

  // operations on literals
  EVAL_ADD,
  EVAL_NEG,
  EVAL_MUL,
  EVAL_INT_DIV,
  EVAL_RAT_DIV,
  EVAL_IS_NEG,
  EVAL_IS_ZERO,
  EVAL_TO_INT,
  EVAL_TO_RAT
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
