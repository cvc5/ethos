#ifndef EXPR_INFO_H
#define EXPR_INFO_H

#include <map>
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
  std::map<Attr, std::shared_ptr<ExprValue>> d_attrs;
  /** Associated kind */
  Kind d_kind;
  /** */
  bool hasAttribute(Attr a) const;
};

}  // namespace alfc

#endif /* STATE_H */
