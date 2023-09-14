#ifndef EXPR_INFO_H
#define EXPR_INFO_H

#include <map>
#include <string>
#include <memory>

#include "kind.h"
#include "attr.h"
#include "expr.h"

namespace alfc {

using AttrMap = std::map<Attr, std::vector<Expr>>;

/**
 * Information about how to construct applications of a function.
 */
class AppInfo
{
public:
  AppInfo() : d_attrCons( ), d_kind(Kind::NONE) {}
  /** Attribute */
  Attr d_attrCons;
  /** Attribute */
  Expr d_attrConsTerm;
  /** Associated kind */
  Kind d_kind;
};

}  // namespace alfc

#endif /* STATE_H */
