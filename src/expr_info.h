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
  AppInfo();
  /** Attribute */
  Attr d_attrCons;
  /** Attribute */
  Expr d_attrConsTerm;
  /** Other marked attributes */
  AttrMap d_attrs;
  /** Associated kind */
  Kind d_kind;
  /** */
  bool hasAttribute(Attr a) const;
};

}  // namespace alfc

#endif /* STATE_H */
