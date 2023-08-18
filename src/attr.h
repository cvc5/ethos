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
  
  VAR,
  IMPLICIT,
  LIST,
  SYNTAX,
  REQUIRES,
  
  RIGHT_ASSOC,
  LEFT_ASSOC,
  RIGHT_ASSOC_NIL,
  LEFT_ASSOC_NIL,
  CHAINABLE,
  PAIRWISE,
  
  // internal
  CLOSURE
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Attr a);

}  // namespace alfc

#endif /* ATTR_H */
