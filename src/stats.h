#ifndef STATS_H
#define STATS_H

#include <string>

namespace alfc {

class Stats
{
public:
  Stats();
  size_t d_mkExprCount;
  size_t d_exprCount;
  size_t d_symCount;
  size_t d_litCount;
  std::string toString();
};

}  // namespace alfc

#endif /* STATS_H */
