/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef STATS_H
#define STATS_H

#include <string>
#include <map>

#include <ctime>

namespace ethos {

class ExprValue;
class Stats;
class State;

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
  size_t d_deleteExprCount;
  size_t d_symCount;
  size_t d_litCount;
  std::time_t d_startTime;
  std::map<const ExprValue*, RuleStat> d_rstats;
  std::map<const ExprValue*, RuleStat> d_pstats;
  std::string toString(State& s, bool compact) const;

  static std::time_t getCurrentTime();
};

}  // namespace ethos

#endif /* STATS_H */
