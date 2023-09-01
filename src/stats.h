#ifndef STATS_H
#define STATS_H

#include <string>
#include <map>

#include <ctime>

namespace alfc {

class ExprValue;
class Stats;

class RuleStat
{
 public:
  RuleStat();
  size_t d_count;
  size_t d_mkExprCount;
  std::time_t d_time;
  void increment(Stats& s);
  // frame
  static std::time_t d_startTime;
  static size_t d_startMkExprCount;
  static void start(Stats& s);
  std::string toString(std::time_t totalTime) const;
};

class Stats
{
public:
  Stats();
  size_t d_mkExprCount;
  size_t d_exprCount;
  size_t d_symCount;
  size_t d_litCount;
  std::time_t d_startTime;
  std::map<const ExprValue*, RuleStat> d_rstats;
  std::string toString() const;
  
  static std::time_t getCurrentTime();
};

}  // namespace alfc

#endif /* STATS_H */
