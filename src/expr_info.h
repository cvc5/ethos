#ifndef EXPR_INFO_H
#define EXPR_INFO_H

#include <unordered_set>
#include <string>
#include <memory>

#include "kind.h"
#include "attr.h"

namespace alfc {

class ExprValue;

class ExprInfo
{
public:
  ExprInfo();
  /**
   * String data
   */
  std::string d_str;
};

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
  std::shared_ptr<ExprValue> d_attrConsTerm;
  /** Other marked attributes */
  std::unordered_set<Attr> d_attrs;
  /**
   * Associated kind
   */
  Kind d_kind;
  /** Marked attributes */
  bool d_isClosure;
};

}  // namespace alfc

#endif /* STATE_H */
