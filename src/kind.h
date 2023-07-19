#ifndef KIND_H
#define KIND_H

#include <sstream>
#include <string>

namespace atc {

/**
 */
enum class Kind
{
  NONE = 0,
  
  // types
  TYPE,
  FUNCTION,
  PROOF,
  ABSTRACT,
  
  // terms
  APPLY,
  LAMBDA,
  CONST,
  VARIABLE,
  VARIABLE_LIST,

  // literals
  INTEGER,
  DECIMAL,
  HEXADECIMAL,
  BINARY,
  STRING
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Kind k);

/** */
bool isVariable(Kind k);
/** */
bool isLiteral(Kind k);

}  // namespace atc

#endif /* KIND_H */
