/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "trim_defs.h"

#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
#include <cctype>
#include "input.h"

namespace ethos {

struct Command
{
  std::string d_cmdName;
  std::string d_symbolName;
  std::unordered_set<std::string> d_bodySyms;
  std::string full_text;
};

// Read one token, skipping whitespace
std::string next_token(std::istream& in) {
  std::string tok;
  char c;
  while (in.get(c)) {
    if (c == ';') {
      // Skip to end of line
      while (in.get(c) && c != '\n');
      continue;
    }
    if (std::isspace(c)) {
      if (!tok.empty()) break;
      continue;
    } else if (c == '(' || c == ')') {
      if (tok.empty()) tok += c;
      else in.putback(c);
      break;
    } else {
      tok += c;
    }
  }
  return tok;
}

// Read one full top-level s-expression from '(' to matching ')'
std::string readFullCommand(std::istream& in) {
  std::string result;
  int depth = 0;
  bool started = false;
  char c;

  while (in.get(c)) {
    if (c == ';') {
      // skip comment to newline
      while (in.get(c) && c != '\n') ;
      result += '\n';
      continue;
    }
    result += c;
    if (c == '(') {
      depth++;
      started = true;
    } else if (c == ')') {
      depth--;
      if (depth == 0 && started) break;
    }
  }

  Assert (depth == 0);
  return result;
}

// Parse the command name, symbol, and collect body symbols
Command parseCommand(const std::string& s_expr_text) {
  Command cmd;
  cmd.full_text = s_expr_text;

  std::istringstream in(s_expr_text);
  Assert (next_token(in) == "(");

  cmd.d_cmdName = next_token(in);
  cmd.d_symbolName = next_token(in);

  int depth = 0;
  while (true) {
    std::string tok = next_token(in);
    if (tok.empty()) break;
    if (tok == "(") {
      ++depth;
    } else if (tok == ")") {
      if (depth == 0) break;
      --depth;
    } else {
      cmd.d_bodySyms.insert(tok);
    }
  }

  return cmd;
}

// Main parser from istream
void TrimDefs::parseCommands(std::istream& in)
{
  size_t idCounter = 0;
  std::map<std::string, size_t> symToId;
  std::map<std::string, size_t>::iterator its;
  std::vector<std::string> commands;
  std::map<size_t, std::unordered_set<size_t>> symCommands;
  std::map<size_t, std::unordered_set<size_t>> cmdSyms;
  while (in)
  {
    std::string tok = next_token(in);
    if (tok == "(")
    {
      in.putback('(');
      std::string full = readFullCommand(in);
      Command cmd = parseCommand(full);
      if (cmd.d_cmdName=="include")
      {
        continue;
      }
      std::cout << "Command: " << cmd.d_cmdName << " " << cmd.d_symbolName << std::endl;
      its = symToId.find(cmd.d_symbolName);
      size_t id;
      if (its==symToId.end())
      {
        ++idCounter;
        symToId[cmd.d_symbolName] = idCounter;
        id = idCounter;
      }
      else
      {
        id = its->second;
      }
      size_t cid = commands.size();
      symCommands[id].insert(cid);
      commands.push_back(cmd.full_text);
      std::unordered_set<size_t>& csyms = cmdSyms[cid];
      for (const std::string& s : cmd.d_bodySyms)
      {
        its = symToId.find(s);
        if (its!=symToId.end() && its->second!=id) // no self
        {
          csyms.insert(its->second);
        }
      }
    }
  }
}


TrimDefs::TrimDefs(State& s) : d_state(s)
{
  d_setDefTarget = false;
}

TrimDefs::~TrimDefs() {}


void TrimDefs::finalizeIncludeFile(const Filepath& s, bool isSignature, bool isReference, const Expr& referenceNf)
{
  if (!isSignature)
  {
    return;
  }
  std::cout << "Trim defs: " << s.getRawPath() << std::endl;
  std::unique_ptr<Input> i = Input::mkFileInput(s.getRawPath());
  std::istream* is = i->getStream();
  parseCommands(*is);
}

}  // namespace ethos
