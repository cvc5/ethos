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

  // literals
  INTEGER,
  DECIMAL,
  HEXADECIMAL,
  BINARY,
  STRING,
  
  // programs
  PROGRAM,
  PAIR
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Kind k);

std::string kindToTerm(Kind k);

/** */
bool isVariable(Kind k);
/** */
bool isLiteral(Kind k);

}  // namespace alfc

#endif /* KIND_H */
