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
  SYNTAX,
  
  RIGHT_ASSOC,
  LEFT_ASSOC,
  CHAINABLE,
  PAIRWISE,
  
  // internal
  CLOSURE
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Attr a);

}  // namespace alfc

#endif /* ATTR_H */
