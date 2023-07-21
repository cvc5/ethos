#ifndef EXPR_INFO_H
#define EXPR_INFO_H

#include <string>
#include "kind.h"

namespace alfc {

class ExprInfo
{
public:
  ExprInfo();
  /**
   * String data
   */
  std::string d_str;
  /**
   * Associated kind
   */
  Kind d_kind;
  /** Marked attributes */
  bool d_isClosure;
};

}  // namespace alfc

#endif /* STATE_H */
