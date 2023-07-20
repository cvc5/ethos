#ifndef ATTR_H
#define ATTR_H

#include <sstream>
#include <string>

namespace atc {

/**
 */
enum class Attr
{
  NONE = 0,
  
  // types
  VAR,
  IMPLICIT,
  LIST
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Attr a);

}  // namespace atc

#endif /* ATTR_H */
