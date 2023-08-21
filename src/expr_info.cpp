#include "expr_info.h"

namespace alfc {

AppInfo::AppInfo() : d_attrCons( ), d_kind(Kind::NONE) {}

bool AppInfo::hasAttribute(Attr a) const
{
  return d_attrs.find(a)!=d_attrs.end();
}

}  // namespace alfc
