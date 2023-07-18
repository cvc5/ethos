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
  APPLY,
  VARIABLE_LIST,
  INTEGER,
  DECIMAL,
  HEXADECIMAL,
  BINARY,
  STRING
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Kind k);

}  // namespace atc

#endif /* KIND_H */
