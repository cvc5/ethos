/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "native_layer.h"

#include <fstream>
#include <sstream>

#include "base/check.h"

namespace ethos {

NativeLayer::NativeLayer(const std::string& path,
                         const std::string& comment,
                         const std::string& top)
    : d_top(top)
{
  std::ifstream in(path);
  if (!in.is_open())
  {
    EO_FATAL() << "NativeLayer: could not read " << path;
  }
  const std::string opens = comment + " $native";
  const std::string keeps = opens + "-keep ";
  const std::string block = opens + " ";
  std::vector<std::string> keep;
  std::string line;
  while (std::getline(in, line))
  {
    if (line.compare(0, opens.size(), opens) != 0)
    {
      // Everything under the line that opens a block is the block, its own
      // comment included, up to the line that opens the next.
      if (!d_defs.empty())
      {
        d_defs.back().d_text += line + "\n";
      }
      continue;
    }
    bool isKeep = line.compare(0, keeps.size(), keeps) == 0;
    if (!isKeep && line.compare(0, block.size(), block) != 0)
    {
      EO_FATAL() << "NativeLayer: `" << line << "` is not a line " << path
                 << " writes";
    }
    std::vector<std::string> ws;
    std::stringstream ls(line.substr(isKeep ? keeps.size() : block.size()));
    std::string w;
    while (ls >> w)
    {
      ws.push_back(w);
    }
    if (isKeep)
    {
      keep = ws;
      continue;
    }
    if (ws.size() < 2)
    {
      EO_FATAL() << "NativeLayer: a block says its name and the narrowest "
                    "scope it can come out in, got `"
                 << line << "`";
    }
    Def d;
    d.d_name = ws[0];
    d.d_needs = ws[1];
    d.d_deps.assign(ws.begin() + 2, ws.end());
    d_of[d.d_name] = d_defs.size();
    d_defs.push_back(d);
  }
  if (d_defs.empty())
  {
    EO_FATAL() << "NativeLayer: " << path << " holds no block";
  }
  // What no input asks for, because the resources of the stage are what name
  // it. They are written above every module that holds a block, so the scope
  // they all see is where it comes out.
  for (const std::string& n : keep)
  {
    use(n, d_top);
  }
}

void NativeLayer::use(const std::string& n) { use(n, d_top); }

void NativeLayer::use(const std::string& n, const std::string& scope)
{
  std::map<std::string, size_t>::const_iterator b = d_of.find(n);
  if (b == d_of.end())
  {
    return;
  }
  const Def& d = d_defs[b->second];
  std::string at = scope;
  if (d.d_needs != d_top)
  {
    // One module can hold it, so nothing narrower is being asked for; a
    // module that cannot see that one has named something it cannot reach.
    if (scope != d.d_needs && scope != d_top)
    {
      EO_FATAL() << "NativeLayer: `" << n << "` comes out in " << d.d_needs
                 << ", which the " << scope
                 << " scope that names it cannot see";
    }
    at = d.d_needs;
  }
  std::pair<std::map<std::string, std::string>::iterator, bool> u =
      d_at.emplace(n, at);
  if (!u.second)
  {
    if (u.first->second == at)
    {
      return;
    }
    // Reached from two scopes, so it comes out in the one they share.
    at = d_top;
    if (u.first->second == at)
    {
      return;
    }
    u.first->second = at;
  }
  for (const std::string& dep : d.d_deps)
  {
    use(dep, at);
  }
}

std::string NativeLayer::defs(const std::string& scope) const
{
  // The order of the layer is an order in which the backend can read it, so
  // what comes out in one scope keeps it.
  std::stringstream out;
  for (const Def& d : d_defs)
  {
    std::map<std::string, std::string>::const_iterator u = d_at.find(d.d_name);
    if (u != d_at.end() && u->second == scope)
    {
      out << d.d_text;
    }
  }
  // A block carries the blank line that separates it from the next, which the
  // last of them has no use for: the module writes its own.
  std::string text = out.str();
  text.erase(text.find_last_not_of('\n') + 1);
  return text;
}

}  // namespace ethos
