/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "trim_defs.h"

#include <cctype>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "input.h"

namespace ethos {

struct Command
{
  std::string d_cmdName;
  std::string d_symbolName;
  std::unordered_set<std::string> d_bodySyms;
  std::string d_fullText;
};

// Read one token, skipping whitespace
std::string nextToken(std::istream& in)
{
  std::string tok;
  char c;
  while (in.get(c))
  {
    if (c == ';')
    {
      // Skip to end of line
      while (in.get(c) && c != '\n')
        ;
      continue;
    }
    if (std::isspace(c))
    {
      if (!tok.empty()) break;
      continue;
    }
    else if (c == '(' || c == ')')
    {
      if (tok.empty())
        tok += c;
      else
        in.putback(c);
      break;
    }
    else
    {
      tok += c;
    }
  }
  return tok;
}

// Read one full top-level s-expression from '(' to matching ')'
std::string readFullCommand(std::istream& in)
{
  std::string result;
  int depth = 0;
  bool started = false;
  char c;

  while (in.get(c))
  {
    if (c == ';')
    {
      // skip comment to newline
      while (in.get(c) && c != '\n')
        ;
      result += '\n';
      continue;
    }
    result += c;
    if (c == '(')
    {
      depth++;
      started = true;
    }
    else if (c == ')')
    {
      depth--;
      if (depth == 0 && started) break;
    }
  }

  Assert(depth == 0);
  return result;
}

// Parse the command name, symbol, and collect body symbols
Command parseCommand(const std::string& s_expr_text)
{
  Command cmd;
  cmd.d_fullText = s_expr_text;

  std::istringstream in(s_expr_text);
  if (nextToken(in) != "(")
  {
    Assert (false);
  }

  cmd.d_cmdName = nextToken(in);
  cmd.d_symbolName = nextToken(in);

  int depth = 0;
  while (true)
  {
    std::string tok = nextToken(in);
    if (tok.empty()) break;
    if (tok == "(")
    {
      ++depth;
    }
    else if (tok == ")")
    {
      if (depth == 0) break;
      --depth;
    }
    else
    {
      cmd.d_bodySyms.insert(tok);
    }
  }

  return cmd;
}

// Main parser from istream
void TrimDefs::parseCommands(std::istream& in)
{
  std::map<std::string, size_t>::iterator its;
  while (in)
  {
    std::string tok = nextToken(in);
    if (tok == "(")
    {
      in.putback('(');
      std::string full = readFullCommand(in);
      Command cmd = parseCommand(full);
      if (cmd.d_cmdName == "include")
      {
        continue;
      }
      //std::cout << "Command: " << cmd.d_cmdName << " " << cmd.d_symbolName
      //          << std::endl;
      its = d_symToId.find(cmd.d_symbolName);
      size_t id;
      if (its == d_symToId.end())
      {
        ++d_idCounter;
        d_symToId[cmd.d_symbolName] = d_idCounter;
        id = d_idCounter;
      }
      else
      {
        id = its->second;
      }
      size_t cid = d_commands.size();
      d_symCommands[id].insert(cid);
      // declare-consts must always be visited
      // $eo_test is a builtin way to ensure tests are included
      if (cmd.d_cmdName=="declare-consts" || cmd.d_symbolName=="$eo_test")
      {
        d_toVisit.push_back(id);
      }
      //std::cout << "*** command " << cmd.d_fullText << std::endl;
      d_commands.push_back(cmd.d_fullText);
      std::unordered_set<size_t>& csyms = d_cmdSyms[cid];
      for (const std::string& s : cmd.d_bodySyms)
      {
        its = d_symToId.find(s);
        if (its != d_symToId.end() && its->second != id)  // no self
        {
          //std::cout << "...*** sym " << s << std::endl;
          csyms.insert(its->second);
        }
        else
        {
          //std::cout << "...non-sym " << s << std::endl;
        }
      }
    }
  }
}

TrimDefs::TrimDefs(State& s) : d_state(s)
{
  d_setDefTarget = false;
  d_idCounter = 0;
}

TrimDefs::~TrimDefs() {}

void TrimDefs::finalizeIncludeFile(const Filepath& s,
                                   bool isSignature,
                                   bool isReference,
                                   const Expr& referenceNf)
{
  if (!isSignature)
  {
    return;
  }
  //std::cout << "Trim defs: " << s.getRawPath() << std::endl;
  std::unique_ptr<Input> i = Input::mkFileInput(s.getRawPath());
  std::istream* is = i->getStream();
  parseCommands(*is);
}

bool TrimDefs::echo(const std::string& msg)
{
  //std::cout << "Echos " << msg << " \"" << msg.substr(10) << "\"" << std::endl;
  if (msg.compare(0, 10, "trim-defs ")==0)
  {
    d_setDefTarget = true;
    d_defTarget = msg.substr(10);
    //std::cout << "...set target" << std::endl;
    return false;
  }
  return true;
}

void TrimDefs::finalize()
{
  if (!d_setDefTarget)
  {
    EO_FATAL() << "Must set target with (echo \"trim-defs <symbol>\"), where <symbol> is the name of the "
                  "symbol to trim with respect to."
               << std::endl;
  }
  std::map<std::string, size_t>::iterator it = d_symToId.find(d_defTarget);
  if (it == d_symToId.end())
  {
    EO_FATAL() << "Could not find target definition \"" << d_defTarget << "\""
               << std::endl;
  }
  std::unordered_set<size_t> cdeps;
  std::unordered_set<size_t> visited;
  d_toVisit.push_back(it->second);
  do
  {
    size_t cur = d_toVisit.back();
    d_toVisit.pop_back();
    if (visited.find(cur)!=visited.end())
    {
      continue;
    }
    visited.insert(cur);
    std::unordered_set<size_t>& sc = d_symCommands[cur];
    Assert (!sc.empty());
    for (size_t cid : sc)
    {
      if (cdeps.find(cid)==cdeps.end())
      {
        cdeps.insert(cid);
        std::unordered_set<size_t>& csyms = d_cmdSyms[cid];
        d_toVisit.insert(d_toVisit.end(), csyms.begin(), csyms.end());
      }
    }
  }
  while (!d_toVisit.empty());
  std::cout << "; trim-defs: " << d_defTarget << std::endl;
  std::cout << "; #trim-defs: " << cdeps.size() << std::endl;
  std::vector<size_t> allCmd(cdeps.begin(), cdeps.end());
  std::sort(allCmd.begin(), allCmd.end());
  for (size_t i : allCmd)
  {
    std::cout << d_commands[i];
    std::cout << std::endl;
  }
}

}  // namespace ethos
