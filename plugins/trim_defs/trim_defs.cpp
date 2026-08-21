/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "trim_defs.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "input.h"

namespace ethos {

namespace {

struct SExpr
{
  bool d_isList = false;
  bool d_isString = false;
  std::string d_value;
  std::vector<SExpr> d_children;
};

/** Read one token, skipping whitespace and comments. */
std::string nextToken(std::istream& in)
{
  std::string tok;
  char c;
  while (in.get(c))
  {
    if (c == ';')
    {
      // Skip to end of line
      while (in.get(c) && c != '\n');
      if (!tok.empty())
      {
        break;
      }
      continue;
    }
    if (std::isspace(static_cast<unsigned char>(c)))
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
    else if (c == '"' && tok.empty())
    {
      tok += c;
      bool closed = false;
      while (in.get(c))
      {
        tok += c;
        if (c == '"')
        {
          if (in.peek() == '"')
          {
            in.get(c);
            tok += c;
          }
          else
          {
            closed = true;
            break;
          }
        }
      }
      Assert(closed);
      break;
    }
    else if (c == '|' && tok.empty())
    {
      tok += c;
      while (in.get(c))
      {
        tok += c;
        if (c == '|')
        {
          break;
        }
      }
      Assert(!tok.empty() && tok.back() == '|');
      break;
    }
    else
    {
      tok += c;
    }
  }
  return tok;
}

/** Read one full top-level s-expression from '(' to matching ')'. */
std::string readFullCommand(std::istream& in)
{
  std::string result;
  int depth = 0;
  bool started = false;
  bool inString = false;
  bool inQuotedSymbol = false;
  char c;

  while (in.get(c))
  {
    if (!inString && !inQuotedSymbol && c == ';')
    {
      // Skip comments but retain a separator between the surrounding tokens.
      while (in.get(c) && c != '\n');
      result += '\n';
      continue;
    }
    result += c;
    if (inString)
    {
      if (c == '"')
      {
        if (in.peek() == '"')
        {
          in.get(c);
          result += c;
        }
        else
        {
          inString = false;
        }
      }
      continue;
    }
    if (inQuotedSymbol)
    {
      if (c == '|')
      {
        inQuotedSymbol = false;
      }
      continue;
    }
    if (c == '"')
    {
      inString = true;
    }
    else if (c == '|')
    {
      inQuotedSymbol = true;
    }
    else if (c == '(')
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

  Assert(depth == 0 && started && !inString && !inQuotedSymbol);
  return result;
}

SExpr parseSExpr(std::istream& in, const std::string& firstToken)
{
  SExpr expr;
  if (firstToken != "(")
  {
    Assert(firstToken != ")");
    expr.d_isString = !firstToken.empty() && firstToken[0] == '"';
    expr.d_value = firstToken;
    return expr;
  }

  expr.d_isList = true;
  while (true)
  {
    std::string tok = nextToken(in);
    Assert(!tok.empty());
    if (tok == ")")
    {
      break;
    }
    expr.d_children.push_back(parseSExpr(in, tok));
  }
  return expr;
}

bool getSymbol(const SExpr& expr, std::string& symbol)
{
  if (expr.d_isList || expr.d_isString || expr.d_value.empty())
  {
    return false;
  }
  symbol = expr.d_value;
  if (symbol.size() >= 2 && symbol.front() == '|' && symbol.back() == '|')
  {
    symbol = symbol.substr(1, symbol.size() - 2);
  }
  return true;
}

std::string unescapeString(const SExpr& expr)
{
  Assert(expr.d_isString && expr.d_value.size() >= 2);
  std::string value;
  for (size_t i = 1, n = expr.d_value.size() - 1; i < n; ++i)
  {
    value += expr.d_value[i];
    if (expr.d_value[i] == '"' && i + 1 < n && expr.d_value[i + 1] == '"')
    {
      ++i;
    }
  }
  return value;
}

void collectSymbols(const SExpr& expr, std::unordered_set<std::string>& symbols)
{
  std::string symbol;
  if (getSymbol(expr, symbol))
  {
    symbols.insert(symbol);
    return;
  }
  for (const SExpr& child : expr.d_children)
  {
    collectSymbols(child, symbols);
  }
}

void collectListHeadSymbols(const SExpr& expr,
                            std::unordered_set<std::string>& symbols)
{
  if (!expr.d_isList)
  {
    return;
  }
  for (const SExpr& child : expr.d_children)
  {
    if (!child.d_isList || child.d_children.empty())
    {
      continue;
    }
    std::string symbol;
    if (getSymbol(child.d_children[0], symbol))
    {
      symbols.insert(symbol);
    }
  }
}

void collectDatatypeSymbols(const SExpr& declaration,
                            std::unordered_set<std::string>& defined,
                            std::unordered_set<std::string>& bound)
{
  if (!declaration.d_isList)
  {
    return;
  }

  const SExpr* constructors = &declaration;
  std::string head;
  if (!declaration.d_children.empty()
      && getSymbol(declaration.d_children[0], head) && head == "par")
  {
    if (declaration.d_children.size() > 1)
    {
      const SExpr& params = declaration.d_children[1];
      if (params.d_isList)
      {
        for (const SExpr& param : params.d_children)
        {
          std::string symbol;
          if (getSymbol(param, symbol))
          {
            bound.insert(symbol);
          }
        }
      }
    }
    if (declaration.d_children.size() <= 2)
    {
      return;
    }
    constructors = &declaration.d_children[2];
  }

  if (!constructors->d_isList)
  {
    return;
  }
  for (const SExpr& constructor : constructors->d_children)
  {
    if (!constructor.d_isList || constructor.d_children.empty())
    {
      continue;
    }
    std::string symbol;
    if (getSymbol(constructor.d_children[0], symbol))
    {
      defined.insert(symbol);
    }
    for (size_t i = 1, n = constructor.d_children.size(); i < n; ++i)
    {
      const SExpr& selector = constructor.d_children[i];
      if (selector.d_isList && !selector.d_children.empty()
          && getSymbol(selector.d_children[0], symbol))
      {
        defined.insert(symbol);
      }
    }
  }
}

bool hasSortedVariables(const std::string& commandName)
{
  return commandName == "define" || commandName == "define-fun"
         || commandName == "program" || commandName == "declare-rule"
         || commandName == "declare-parameterized-const";
}

bool hasPrefix(const std::string& value, const std::string& prefix)
{
  return value.compare(0, prefix.size(), prefix) == 0;
}

/** Parse a command and collect all names it introduces and references. */
Command parseCommand(const std::string& s_expr_text)
{
  Command cmd;
  cmd.d_fullText = s_expr_text;

  std::istringstream in(s_expr_text);
  std::string first = nextToken(in);
  Assert(first == "(");
  SExpr root = parseSExpr(in, first);
  Assert(root.d_isList && !root.d_children.empty());
  Assert(getSymbol(root.d_children[0], cmd.d_cmdName));

  std::unordered_set<std::string> defined;
  std::unordered_set<std::string> bound;
  if (cmd.d_cmdName == "declare-datatype")
  {
    std::string symbol;
    if (root.d_children.size() > 1 && getSymbol(root.d_children[1], symbol))
    {
      defined.insert(symbol);
    }
    if (root.d_children.size() > 2)
    {
      collectDatatypeSymbols(root.d_children[2], defined, bound);
    }
  }
  else if (cmd.d_cmdName == "declare-datatypes")
  {
    if (root.d_children.size() > 1)
    {
      collectListHeadSymbols(root.d_children[1], defined);
    }
    if (root.d_children.size() > 2 && root.d_children[2].d_isList)
    {
      for (const SExpr& declaration : root.d_children[2].d_children)
      {
        collectDatatypeSymbols(declaration, defined, bound);
      }
    }
  }
  else if (cmd.d_cmdName != "echo" && cmd.d_cmdName != "include"
           && root.d_children.size() > 1)
  {
    std::string symbol;
    if (getSymbol(root.d_children[1], symbol))
    {
      defined.insert(symbol);
    }
  }

  if (hasSortedVariables(cmd.d_cmdName) && root.d_children.size() > 2)
  {
    collectListHeadSymbols(root.d_children[2], bound);
  }

  collectSymbols(root, cmd.d_bodySyms);
  cmd.d_bodySyms.erase(cmd.d_cmdName);
  for (const std::string& symbol : defined)
  {
    cmd.d_symbolNames.push_back(symbol);
    cmd.d_bodySyms.erase(symbol);
  }
  std::sort(cmd.d_symbolNames.begin(), cmd.d_symbolNames.end());
  for (const std::string& symbol : bound)
  {
    cmd.d_bodySyms.erase(symbol);
  }

  cmd.d_alwaysKeep =
      cmd.d_cmdName == "declare-consts" || cmd.d_cmdName == "echo";
  if (cmd.d_cmdName == "echo" && root.d_children.size() > 1
      && root.d_children[1].d_isString)
  {
    const std::string msg = unescapeString(root.d_children[1]);
    cmd.d_isTrimDirective =
        hasPrefix(msg, "trim-defs ") || hasPrefix(msg, "trim-defs-cmd ");
  }
  return cmd;
}

std::string normalizeSymbol(const std::string& symbol)
{
  if (!hasPrefix(symbol, "eo::"))
  {
    return symbol;
  }
  return "$eo_" + symbol.substr(4);
}

}  // namespace

// Main parser from istream
void TrimDefs::parseCommands(std::istream& in)
{
  while (in)
  {
    std::string tok = nextToken(in);
    if (tok == "(")
    {
      in.putback('(');
      std::string full = readFullCommand(in);
      Command cmd = parseCommand(full);
      processCommand(std::move(cmd));
    }
  }
}

void TrimDefs::processCommand(Command&& cmd)
{
  if (cmd.d_cmdName == "include" || cmd.d_isTrimDirective)
  {
    return;
  }

  const size_t cid = d_commands.size();
  std::unordered_set<size_t> defined;
  for (const std::string& symbol : cmd.d_symbolNames)
  {
    std::map<std::string, size_t>::iterator it = d_symToId.find(symbol);
    size_t id;
    if (it == d_symToId.end())
    {
      id = ++d_idCounter;
      d_symToId[symbol] = id;
    }
    else
    {
      id = it->second;
    }
    d_symCommands[id].insert(cid);
    defined.insert(id);
  }

  if (cmd.d_alwaysKeep)
  {
    d_alwaysKeepCmds.push_back(cid);
  }
  if (cmd.d_cmdName == "define"
      && std::any_of(
          cmd.d_symbolNames.begin(),
          cmd.d_symbolNames.end(),
          [](const std::string& name) { return isParseDefName(name); }))
  {
    d_parseDefCmds.push_back(cid);
  }
  d_commands.push_back(std::move(cmd));
  d_cmdDefinedSyms.push_back(std::move(defined));
  d_cmdSyms.emplace_back();
}

void TrimDefs::resolveDependencies()
{
  Assert(d_commands.size() == d_cmdDefinedSyms.size());
  Assert(d_commands.size() == d_cmdSyms.size());
  for (size_t cid = 0, ncommands = d_commands.size(); cid < ncommands; ++cid)
  {
    std::unordered_set<size_t>& dependencies = d_cmdSyms[cid];
    dependencies.clear();
    for (const std::string& symbol : d_commands[cid].d_bodySyms)
    {
      std::map<std::string, size_t>::const_iterator it =
          d_symToId.find(normalizeSymbol(symbol));
      if (it != d_symToId.end()
          && d_cmdDefinedSyms[cid].find(it->second)
                 == d_cmdDefinedSyms[cid].end())
      {
        dependencies.insert(it->second);
      }
    }
  }
}

std::vector<size_t> TrimDefs::getCommandOrder(
    const std::unordered_set<size_t>& retained) const
{
  // A DFS postorder puts each command after the retained definitions of the
  // symbols it references. Cycles have no topological order; encountering a
  // command already on the current path breaks the cycle deterministically.
  std::vector<unsigned char> state(d_commands.size(), 0);
  std::vector<size_t> order;
  std::function<void(size_t)> visit = [&](size_t cid) {
    if (state[cid] == 2)
    {
      return;
    }
    if (state[cid] == 1)
    {
      return;
    }
    state[cid] = 1;

    std::vector<size_t> dependencies;
    for (size_t symbol : d_cmdSyms[cid])
    {
      std::map<size_t, std::unordered_set<size_t>>::const_iterator it =
          d_symCommands.find(symbol);
      if (it == d_symCommands.end())
      {
        continue;
      }
      for (size_t dependency : it->second)
      {
        if (dependency != cid && retained.find(dependency) != retained.end())
        {
          dependencies.push_back(dependency);
        }
      }
    }
    std::sort(dependencies.begin(), dependencies.end());
    dependencies.erase(std::unique(dependencies.begin(), dependencies.end()),
                       dependencies.end());
    for (size_t dependency : dependencies)
    {
      visit(dependency);
    }

    state[cid] = 2;
    order.push_back(cid);
  };

  std::vector<size_t> roots(retained.begin(), retained.end());
  std::sort(roots.begin(), roots.end());
  for (size_t cid : roots)
  {
    visit(cid);
  }
  return order;
}

TrimDefs::TrimDefs(State& s) : StdPlugin(s) { d_idCounter = 0; }

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
  std::unique_ptr<Input> i = Input::mkFileInput(s.getRawPath());
  std::istream* is = i->getStream();
  parseCommands(*is);
}

bool TrimDefs::echo(const std::string& msg)
{
  if (msg.compare(0, 10, "trim-defs ") == 0)
  {
    d_defTargets.push_back(msg.substr(10));
    return false;
  }
  if (msg.compare(0, 14, "trim-defs-cmd ") == 0)
  {
    std::string msgr = msg.substr(14);
    Command cmd = parseCommand(msgr);
    processCommand(std::move(cmd));
    return false;
  }
  return true;
}

void TrimDefs::finalize()
{
  if (d_defTargets.empty())
  {
    EO_FATAL() << "Must set target with (echo \"trim-defs <symbol>\"), where "
                  "<symbol> is the name of the "
                  "symbol to trim with respect to."
               << std::endl;
  }
  resolveDependencies();

  std::vector<size_t> toVisit;
  for (const std::string& dt : d_defTargets)
  {
    std::map<std::string, size_t>::const_iterator it = d_symToId.find(dt);
    if (it == d_symToId.end())
    {
      EO_FATAL() << "Could not find target definition \"" << dt << "\"";
    }
    toVisit.push_back(it->second);
  }

  std::unordered_set<size_t> retained;
  auto retainCommand = [&](size_t cid) {
    if (retained.insert(cid).second)
    {
      const std::unordered_set<size_t>& dependencies = d_cmdSyms[cid];
      toVisit.insert(toVisit.end(), dependencies.begin(), dependencies.end());
    }
  };
  for (size_t cid : d_alwaysKeepCmds)
  {
    retainCommand(cid);
  }

  std::unordered_set<size_t> visited;
  while (!toVisit.empty())
  {
    size_t cur = toVisit.back();
    toVisit.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    std::map<size_t, std::unordered_set<size_t>>::const_iterator it =
        d_symCommands.find(cur);
    Assert(it != d_symCommands.end() && !it->second.empty());
    for (size_t cid : it->second)
    {
      retainCommand(cid);
    }
  }

  // Retain parse definitions to a fixpoint. A referenced symbol is available
  // exactly when at least one of its defining commands has been retained.
  bool changed;
  do
  {
    changed = false;
    for (size_t cid : d_parseDefCmds)
    {
      if (retained.find(cid) != retained.end())
      {
        continue;
      }
      bool keep = true;
      for (size_t symbol : d_cmdSyms[cid])
      {
        std::map<size_t, std::unordered_set<size_t>>::const_iterator it =
            d_symCommands.find(symbol);
        bool available =
            it != d_symCommands.end()
            && std::any_of(
                it->second.begin(), it->second.end(), [&](size_t dependency) {
                  return retained.find(dependency) != retained.end();
                });
        if (!available)
        {
          keep = false;
          break;
        }
      }
      if (keep)
      {
        retained.insert(cid);
        changed = true;
      }
    }
  } while (changed);

  std::stringstream ss;
  ss << "; trim-defs:";
  for (const std::string& dt : d_defTargets)
  {
    ss << " " << dt;
  }
  ss << std::endl;
  ss << "; #trim-defs: " << retained.size() << std::endl;
  for (size_t cid : getCommandOrder(retained))
  {
    if (d_commands[cid].d_cmdName == "depends")
    {
      continue;
    }
    ss << d_commands[cid].d_fullText;
    ss << std::endl;
  }

  // write the trimmed to file
  std::string outPath = getOutputPath("plugins/trim_defs/trim_gen.eo");
  std::ofstream out(outPath);
  if (!out.is_open())
  {
    EO_FATAL() << "TrimDefs: failed to open output " << outPath;
  }
  out << ss.str();
  out.close();
  if (out.fail())
  {
    EO_FATAL() << "TrimDefs: failed to write output " << outPath;
  }
  std::cout << "Write trim-defs " << outPath << std::endl;
}

}  // namespace ethos
