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
  REQUIRES,

  //------------------ below here is mutually exclusive?
  LIST,
  SYNTAX,
  PROGRAM,
  ORACLE,

  // indicate how to construct proof rule steps
  PREMISE_LIST,
  MATCH_CONCLUSION,
  PREMISE_LIST_MATCH_CONCLUSION,  // It is possible to have both

  // indicate how to construct apps of function symbols
  RIGHT_ASSOC,
  LEFT_ASSOC,
  RIGHT_ASSOC_NIL,
  LEFT_ASSOC_NIL,
  CHAINABLE,
  PAIRWISE,

  // datatypes
  DATATYPE,
  DATATYPE_CONSTRUCTOR,
  CODATATYPE,

  // internal
  CLOSURE
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Attr a);

}  // namespace alfc

#endif /* ATTR_H */
