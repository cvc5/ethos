#ifndef ATTR_H
#define ATTR_H

#include <sstream>
#include <string>

namespace alfc {

/**
 */
enum class Attr
{
  NONE = 0,
  
  // types
  VAR,
  IMPLICIT,
  LIST,
  SYNTAX
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Attr a);

}  // namespace alfc

#endif /* ATTR_H */
