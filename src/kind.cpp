#include "kind.h"

#include <iostream>

namespace atc {

std::ostream& operator<<(std::ostream& o, Kind k)
{
  switch (k)
  {
    case Kind::NONE: o << "NONE"; break;
    case Kind::APPLY: o << "APPLY"; break;
    default: o << "UnknownKind(" << unsigned(k) << ")"; break;
  }
  return o;
}

}  // namespace atc
