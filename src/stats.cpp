/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "stats.h"

#include <algorithm>
#include <chrono>
#include <iomanip>
#include <sstream>

#include "base/check.h"
#include "expr.h"
#include "state.h"

namespace ethos {

std::time_t RuleStat::d_startTime;
size_t RuleStat::d_startMkExprCount;
  
RuleStat::RuleStat() : d_count(0), d_mkExprCount(0), d_time(0)
{
}

void RuleStat::start(Stats& s)
{
  d_startTime = Stats::getCurrentTime();
  d_startMkExprCount = s.d_mkExprCount;
}

void RuleStat::increment(Stats& s)
{
  // we assume count is already incremented separately
  d_mkExprCount += (s.d_mkExprCount-d_startMkExprCount);
  d_time += (Stats::getCurrentTime()-d_startTime);
}
  
std::string RuleStat::toString(std::time_t totalTime) const
{
  std::stringstream ss;
  ss << std::left << std::setw(7) << d_count;
  std::stringstream st;
  double pct = static_cast<double>(100*d_time)/static_cast<double>(totalTime);
  st << d_time << " (" << std::fixed << std::setprecision(1) << pct << "%)";
  ss << std::left << std::setw(17) << st.str();
  // time per rule
  double timePerRule = static_cast<double>(d_time)/static_cast<double>(d_count);
  std::stringstream sp;
  sp << std::fixed << std::setprecision(0) << timePerRule;
  ss << std::left << std::setw(10) << sp.str();
  std::stringstream se;
  se << d_mkExprCount;
  ss << std::left << std::setw(10) << se.str();
  return ss.str();
}
  
Stats::Stats() : d_mkExprCount(0), d_exprCount(0), d_deleteExprCount(0), d_symCount(0), d_litCount(0)
{
  d_startTime = getCurrentTime();
}

/**
 * Either sorts by time or by counts
 */
struct SortRuleTime
{
  SortRuleTime(const std::map<const ExprValue*, RuleStat>& rs) : d_rstats(rs)
  {
  }
  const std::map<const ExprValue*, RuleStat>& d_rstats;
  bool operator()(const ExprValue* i, const ExprValue* j)
  {
    std::map<const ExprValue*, RuleStat>::const_iterator itri;
    itri = d_rstats.find(i);
    Assert (itri!=d_rstats.end());
    std::map<const ExprValue*, RuleStat>::const_iterator itrj;
    itrj = d_rstats.find(j);
    Assert (itrj!=d_rstats.end());
    if (itri->second.d_time==itrj->second.d_time)
    {
      return itri->second.d_count>itrj->second.d_count;
    }
    return itri->second.d_time>itrj->second.d_time;
  }
};

std::string Stats::toString(State& s, bool compact, bool all) const
{
  std::stringstream ss;
  if (!compact)
  {
    ss << "====================================================================================" << std::endl;
  }
  ss << "mkExprCount = " << d_mkExprCount << std::endl;
  ss << "newExprCount = " << d_exprCount << std::endl;
  ss << "deleteExprCount = " << d_deleteExprCount << std::endl;
  ss << "symCount = " << d_symCount << std::endl;
  ss << "litCount = " << d_litCount << std::endl;
  std::time_t totalTime = (getCurrentTime()-d_startTime);
  ss << "time = " << totalTime << std::endl;
  size_t imax = all ? 2 : 1;
  for (size_t i=0; i<imax; i++)
  {
    const std::map<const ExprValue*, RuleStat>& rs = i==0 ? d_rstats : d_pstats;
    if (rs.empty())
    {
      continue;
    }
    if (!compact)
    {
      ss << "====================================================================================" << std::endl;
      ss << std::right << std::setw(40) << (i==0 ? "Rule  " : "Program  ");
      ss << std::left << std::setw(7) << "#";
      if (i==0)
      {
        ss << std::left << std::setw(17) << "t";
        ss << std::left << std::setw(10) << "t/#";
        ss << std::left << std::setw(10) << "#mkExpr";
      }
      ss << std::endl;
      ss << "====================================================================================" << std::endl;
    }
    // display stats for each rule
    std::vector<const ExprValue*> sortedStats;
    for (const std::pair<const ExprValue* const, RuleStat>& r : rs)
    {
      // might be an internal match program, in which case, skip
      Expr sym(r.first);
      std::string symbol = sym.getSymbol();
      if (symbol.compare(0, 4, "eo::")==0)
      {
        continue;
      }
      sortedStats.push_back(r.first);
    }
    // sort based on time
    SortRuleTime srt(rs);
    std::sort(sortedStats.begin(), sortedStats.end(), srt);    
    std::map<const ExprValue*, RuleStat>::const_iterator itr;
    std::stringstream ssCount;
    std::stringstream ssCheck;
    std::stringstream ssMkExpr;
    bool firstTime = true;
    for (const ExprValue* e : sortedStats)
    {
      itr = rs.find(e);
      Assert (itr!=rs.end());
      const RuleStat& rs = itr->second;
      std::stringstream sss;
      sss << Expr(e);
      if (compact)
      {
        if (firstTime)
        {
          firstTime = false;
        }
        else
        {
          ssCount << ", ";
          ssCheck << ", ";
          ssMkExpr << ", ";
        }
        ssCount << sss.str() << ": " << rs.d_count;
        ssCheck << sss.str() << ": " << rs.d_time;
        ssMkExpr << sss.str() << ": " << rs.d_mkExprCount;
      }
      else
      {
        sss << ": ";
        ss << std::right << std::setw(40) << sss.str();
        if (i==0)
        {
          ss << rs.toString(totalTime) << std::endl;
        }
        else
        {
          ss << rs.d_count << std::endl;
        }
      }
    }
    if (compact)
    {
      ss << (i==0 ? "rule" : "prog") << "Count = { " << ssCount.str() << " }" << std::endl;
      if (i==0)
      {
        ss << "checkTime = { " << ssCheck.str() << " }" << std::endl;
        ss << "mkExpr = { " << ssMkExpr.str() << " }" << std::endl;
      }
    }
  }
  return ss.str();
}

std::time_t Stats::getCurrentTime()
{
  auto now = std::chrono::high_resolution_clock::now();
  //auto now_ns = std::chrono::time_point_cast<std::chrono::nanoseconds>(now);
  auto now_ns = std::chrono::time_point_cast<std::chrono::microseconds>(now);
  auto epoch_time = now_ns.time_since_epoch();
  std::time_t t = epoch_time.count();
  return t;
}

}  // namespace ethos
