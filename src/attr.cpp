#include "attr.h"

namespace alfc {

std::ostream& operator<<(std::ostream& o, Attr a)
{
  switch (a)
  {
    case Attr::NONE: o << "NONE"; break;
    case Attr::VAR: o << "VAR"; break;
    case Attr::IMPLICIT: o << "IMPLICIT"; break;
    case Attr::LIST: o << "LIST"; break;
    case Attr::SYNTAX: o << "SYNTAX"; break;
    case Attr::REQUIRES: o << "REQUIRES"; break;
    case Attr::RIGHT_ASSOC: o << "RIGHT_ASSOC"; break;
    case Attr::LEFT_ASSOC: o << "LEFT_ASSOC"; break;
    case Attr::RIGHT_ASSOC_NIL: o << "RIGHT_ASSOC_NIL"; break;
    case Attr::LEFT_ASSOC_NIL: o << "LEFT_ASSOC_NIL"; break;
    case Attr::CHAINABLE: o << "CHAINABLE"; break;
    case Attr::PAIRWISE: o << "PAIRWISE"; break;
    default: o << "UnknownAttr(" << unsigned(a) << ")"; break;
  }
  return o;
}

}  // namespace alfc
