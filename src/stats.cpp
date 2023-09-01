#include "stats.h"

#include <sstream>

namespace alfc {

Stats::Stats() : d_mkExprCount(0), d_exprCount(0), d_symCount(0), d_litCount(0){}
 
std::string Stats::toString()
{
  std::stringstream ss;
  ss << "mkExprCount = " << d_mkExprCount << std::endl;
  ss << "exprCount = " << d_exprCount << std::endl;
  ss << "symCount = " << d_symCount << std::endl;
  ss << "litCount = " << d_litCount << std::endl;
  return ss.str();
}

}  // namespace alfc
