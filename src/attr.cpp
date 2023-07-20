#include "attr.h"

namespace atc {

std::ostream& operator<<(std::ostream& o, Attr a)
{
  switch (a)
  {
    case Attr::NONE: o << "NONE"; break;
    case Attr::VAR: o << "VAR"; break;
    case Attr::IMPLICIT: o << "IMPLICIT"; break;
    case Attr::LIST: o << "LIST"; break;
    default: o << "UnknownAttr(" << unsigned(a) << ")"; break;
  }
  return o;
}

}  // namespace atc
