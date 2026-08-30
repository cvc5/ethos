/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "defs_reader.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <functional>
#include <sstream>

#include "base/check.h"

namespace ethos {

namespace {

/** True if c may occur in a name of the signature. */
bool isNameChar(char c)
{
  return !isspace(static_cast<unsigned char>(c)) && c != '(' && c != ')'
         && c != ';' && c != '"';
}

/**
 * The end of the parenthesised form of text that begins at i, i.e. one past
 * its closing parenthesis. Note a string is stepped over whole, so that a
 * parenthesis it holds is not counted.
 */
size_t formEnd(const std::string& text, size_t i)
{
  size_t depth = 0;
  for (size_t n = text.size(); i < n; i++)
  {
    if (text[i] == '"')
    {
      // an SMT-LIB string, in which a quote is written twice
      i++;
      while (i < n && !(text[i] == '"' && (i + 1 >= n || text[i + 1] != '"')))
      {
        i += (text[i] == '"' ? 2 : 1);
      }
      continue;
    }
    if (text[i] == ';')
    {
      while (i < n && text[i] != '\n')
      {
        i++;
      }
      continue;
    }
    if (text[i] == '(')
    {
      depth++;
    }
    else if (text[i] == ')')
    {
      depth--;
      if (depth == 0)
      {
        return i + 1;
      }
    }
  }
  return std::string::npos;
}

/** The top-level forms of text, in order. */
std::vector<std::string> forms(const std::string& text)
{
  std::vector<std::string> ret;
  for (size_t i = 0, n = text.size(); i < n; i++)
  {
    if (text[i] == ';')
    {
      while (i < n && text[i] != '\n')
      {
        i++;
      }
    }
    else if (text[i] == '(')
    {
      size_t e = formEnd(text, i);
      if (e == std::string::npos)
      {
        return ret;
      }
      ret.push_back(text.substr(i, e - i));
      i = e - 1;
    }
  }
  return ret;
}

/** The word of form that follows its keyword, i.e. the name it is of. */
std::string formName(const std::string& form)
{
  size_t i = form.find_first_of(" \t\n", 1);
  if (i == std::string::npos)
  {
    return "";
  }
  while (i < form.size() && isspace(static_cast<unsigned char>(form[i])))
  {
    i++;
  }
  size_t j = i;
  while (j < form.size() && isNameChar(form[j]))
  {
    j++;
  }
  return form.substr(i, j - i);
}

/** The keyword of form, e.g. program or define. */
std::string formKind(const std::string& form)
{
  size_t j = 1;
  while (j < form.size() && isNameChar(form[j]))
  {
    j++;
  }
  return form.substr(1, j - 1);
}

/**
 * Every dollar-prefixed word form uses. This deliberately over-approximates
 * dependencies: bound parameters such as $T are included as uses as well.
 * They normally have no owner and are therefore harmless; keeping them avoids
 * duplicating the parser's binding logic in this text-only reader.
 */
void namesOf(const std::string& form, std::set<std::string>& out)
{
  for (size_t i = 0, n = form.size(); i < n; i++)
  {
    if (form[i] == '"')
    {
      i++;
      while (i < n && !(form[i] == '"' && (i + 1 >= n || form[i + 1] != '"')))
      {
        i += (form[i] == '"' ? 2 : 1);
      }
      continue;
    }
    if (form[i] == ';')
    {
      while (i < n && form[i] != '\n')
      {
        i++;
      }
      continue;
    }
    if (form[i] == '$')
    {
      size_t j = i;
      while (j < n && isNameChar(form[j]))
      {
        j++;
      }
      out.insert(form.substr(i, j - i));
      i = j - 1;
    }
  }
}

/**
 * The cases of a program, i.e. the forms of the last form of its body, with
 * the head of each rewritten from name to agg.
 */
std::vector<std::string> casesOf(const std::string& prog,
                                 const std::string& name,
                                 const std::string& agg)
{
  std::vector<std::string> body = forms(prog.substr(1, prog.size() - 2));
  std::vector<std::string> ret;
  if (body.empty())
  {
    return ret;
  }
  const std::string& cl = body.back();
  for (const std::string& c : forms(cl.substr(1, cl.size() - 2)))
  {
    std::string cs = c;
    size_t p = cs.find(name);
    while (p != std::string::npos)
    {
      cs.replace(p, name.size(), agg);
      p = cs.find(name, p + agg.size());
    }
    ret.push_back(cs);
  }
  return ret;
}

/** The text with every occurrence of from replaced by to. */
std::string replaceAll(const std::string& text,
                       const std::string& from,
                       const std::string& to)
{
  std::string out = text;
  size_t pos = out.find(from);
  while (pos != std::string::npos)
  {
    out = out.substr(0, pos) + to + out.substr(pos + from.size());
    pos = out.find(from, pos + to.size());
  }
  return out;
}

/** The forward declaration of the program prog, which is named name. */
std::string fwdOf(const std::string& prog, const std::string& name)
{
  size_t s = prog.find(":signature");
  if (s == std::string::npos)
  {
    return "";
  }
  size_t e = prog.find('\n', s);
  std::stringstream ss;
  ss << "(program " << name << " () " << prog.substr(s, e - s) << ")";
  return ss.str();
}

}  // namespace

void DefsFile::addBlock(const std::string& sym, const std::string& text)
{
  DefsBlock b;
  b.d_sym = sym;
  // A block named after the constructor it declares is of something the
  // embedding builds itself rather than of a symbol written over it, see
  // DefsBlock::d_literal. A datatype whose constructors are the embedding's
  // own throughout says so instead, and those stand later; what is left is a
  // literal, i.e. one of the embedding's own among a datatype whose others
  // are the input's.
  // A block named after the constant it declares is one of the embedding's
  // own among a datatype a signature also builds, i.e. a literal; a type
  // names its block after the symbol instead, and is the embedding's own by
  // the datatype being so. See DefsBlock::d_own and DefsBlock::d_literal.
  const bool namedAfterConstant = embedDatatypeOf(sym) != nullptr;
  for (const std::string& f : forms(text))
  {
    const std::string kind = formKind(f);
    if (kind == "echo")
    {
      // A directive to a stage rather than something the model says. Most are
      // addressed elsewhere, e.g. one that leaves the symbol out of the
      // compilation altogether, see Desugar::echo; this one is addressed
      // here. Either way it names nothing.
      if (f.find("\"eoc-keep ") != std::string::npos)
      {
        b.d_keep = true;
      }
      continue;
    }
    const std::string name = formName(f);
    namesOf(f, b.d_uses);
    b.d_defs.insert(name);
    if (kind == "declare-const" || kind == "declare-parameterized-const"
        || kind == "define")
    {
      // The constructor of the embedding for the symbol, and the macro that
      // applies it. Which datatype it builds is what says where it is written
      // and whether it stands in the order the configuration gives, so this
      // stage holds the name of no datatype and adding one asks nothing of
      // it; see DefsEmbedDatatype.
      if (const DefsEmbedDatatype* dt = embedDatatypeOf(name))
      {
        b.d_own = dt->own() || namedAfterConstant;
        b.d_literal = namedAfterConstant && !dt->own();
        b.d_at[b.d_own ? dt->d_ownInto : dt->d_into].push_back(f);
        b.d_builds = dt;
      }
      else
      {
        // Not a constructor of any datatype, so it is a helper that happens
        // to be written as a define rather than as a program --
        // $smtx_map_update is one -- and belongs to whichever stream its name
        // says.
        classifyProgram(b, f, name);
      }
      continue;
    }
    if (kind != "program")
    {
      continue;
    }
    classifyProgram(b, f, name);
  }
  for (const std::string& d : b.d_defs)
  {
    b.d_uses.erase(d);
  }
  for (const std::string& d : b.d_defs)
  {
    d_owner[d] = d_blocks.size();
  }
  d_blocks.push_back(b);
}

const DefsAggregate* DefsFile::aggregateOf(const std::string& name) const
{
  // The aggregates stand longest case first, so the first that matches is the
  // longest that does.
  for (const DefsAggregate& a : d_aggregates)
  {
    if (name.size() > a.d_case.size()
        && name.compare(0, a.d_case.size(), a.d_case) == 0)
    {
      return &a;
    }
  }
  return nullptr;
}

const DefsHelper* DefsFile::helperOf(const std::string& name) const
{
  for (const DefsHelper& h : d_helpers)
  {
    if (name.size() > h.d_case.size()
        && name.compare(0, h.d_case.size(), h.d_case) == 0)
    {
      return &h;
    }
  }
  return nullptr;
}

const DefsEmbedDatatype* DefsFile::embedDatatypeOf(
    const std::string& name) const
{
  for (const DefsEmbedDatatype& dt : d_embedDatatypes)
  {
    if (name.compare(0, dt.d_cons.size(), dt.d_cons) == 0
        || name.compare(0, dt.d_macro.size(), dt.d_macro) == 0)
    {
      return &dt;
    }
  }
  return nullptr;
}

void DefsFile::classifyProgram(DefsBlock& b,
                               const std::string& f,
                               const std::string& name)
{
  // A program is either one of the per-symbol programs, whose cases the
  // aggregate it feeds takes, or an auxiliary one the cases call, which is
  // copied as it stands. Which aggregate a per-symbol program belongs to, and
  // where what is taken from it goes, is what the head of the file says.
  const DefsAggregate* a = aggregateOf(name);
  if (a != nullptr)
  {
    if (a->d_whole)
    {
      // Emitted whole rather than as cases of an aggregate, under the name
      // the head declares: what asks for it, the desugar stage, asks by name.
      b.d_at[a->d_into].push_back(replaceAll(f, a->d_case, a->d_name));
      return;
    }
    std::vector<std::string> cases = casesOf(f, name, a->d_name);
    std::vector<std::string>& out = b.d_at[a->d_into];
    out.insert(out.end(), cases.begin(), cases.end());
    return;
  }
  if (name.size() > 10
      && name.compare(name.size() - 10, 10, "_canonical") == 0)
  {
    // Whether a value of a shape is canonical, which is asked after the
    // programs over types that it calls, see DefsBlock::d_canonicalAux.
    b.d_canonicalAux.push_back(f);
    return;
  }
  const DefsHelper* h = helperOf(name);
  if (h != nullptr)
  {
    b.d_helperProgs.push_back(f);
    std::string fwd = fwdOf(f, name);
    if (!fwd.empty())
    {
      b.d_at[h->d_forward].push_back(fwd);
    }
    return;
  }
  if (name.size() > 10 && name.compare(0, 10, "$eo_to_smt") == 0)
  {
    b.d_eoAux.push_back(f);
    return;
  }
  // Any other helper of the symbol, e.g. the one that reads a sequence at an
  // index or the one that types a map value. It stands with the rest, in the
  // order the signature wrote them.
  b.d_helperProgs.push_back(f);
}

void DefsFile::readHead(const std::string& head)
{
  std::istringstream lines(head);
  std::string line;
  while (std::getline(lines, line))
  {
    std::istringstream words(line);
    std::string semi, kind;
    if (!(words >> semi >> kind) || semi != ";")
    {
      continue;
    }
    if (kind == "$eoc-aggregate")
    {
      DefsAggregate a;
      std::string whole;
      if (!(words >> a.d_name >> a.d_case >> a.d_into))
      {
        EO_FATAL() << "DefsFile: an aggregate is written `; $eoc-aggregate "
                      "<name> <case> <into> [whole]`, got: "
                   << line;
      }
      if (words >> whole)
      {
        if (whole != "whole")
        {
          EO_FATAL() << "DefsFile: an aggregate says `whole` or says nothing "
                        "after the marker, got: "
                     << line;
        }
        a.d_whole = true;
      }
      d_aggregates.push_back(a);
    }
    else if (kind == "$eoc-embed-datatype")
    {
      DefsEmbedDatatype dt;
      if (!(words >> dt.d_cons >> dt.d_macro >> dt.d_ownInto))
      {
        EO_FATAL() << "DefsFile: a datatype of the embedding is written `; "
                      "$eoc-embed-datatype <cons> <macro> <own-into> "
                      "[<into>]`, got: "
                   << line;
      }
      // A datatype a signature writes constructors of says where those go as
      // well; one that says nothing more is the embedding's throughout.
      words >> dt.d_into;
      d_embedDatatypes.push_back(dt);
    }
    else if (kind == "$eoc-helper")
    {
      DefsHelper h;
      if (!(words >> h.d_case >> h.d_forward))
      {
        EO_FATAL() << "DefsFile: a helper is written `; $eoc-helper <case> "
                      "<forward>`, got: "
                   << line;
      }
      d_helpers.push_back(h);
    }
  }
  // Longest case first, which is what aggregateOf takes the first match of.
  std::stable_sort(d_aggregates.begin(),
                   d_aggregates.end(),
                   [](const DefsAggregate& x, const DefsAggregate& y) {
                     return x.d_case.size() > y.d_case.size();
                   });
}

bool DefsFile::read(const std::string& path)
{
  d_blocks.clear();
  d_owner.clear();
  d_aggregates.clear();
  d_helpers.clear();
  std::ifstream in(path);
  if (!in.is_open())
  {
    return false;
  }
  std::stringstream ss;
  ss << in.rdbuf();
  if (in.bad())
  {
    return false;
  }
  // Prepending a newline lets the same marker recognize a block on line one.
  const std::string text = "\n" + ss.str();
  // A block runs from the line that names its symbol to the next one.
  const std::string mark = "\n; -- ";
  size_t i = text.find(mark);
  // Everything above the first block is the head, which is what says how the
  // blocks are to be taken apart, see DefsAggregate.
  readHead(text.substr(0, i == std::string::npos ? text.size() : i));
  if (d_aggregates.empty())
  {
    EO_FATAL() << "DefsFile: " << path
               << " declares no aggregates; it was written by an older "
                  "compiler, run tools/eoc/sem_compile.py";
  }
  while (i != std::string::npos)
  {
    size_t ns = i + mark.size();
    size_t ne = text.find('\n', ns);
    if (ne == std::string::npos)
    {
      return false;
    }
    size_t next = text.find(mark, ns);
    addBlock(text.substr(ns, ne - ns),
             text.substr(
                 ne + 1,
                 (next == std::string::npos ? text.size() : next) - (ne + 1)));
    i = next;
  }
  return !d_blocks.empty();
}

std::set<std::string> DefsFile::externalUses(
    const std::vector<const DefsBlock*>& blocks) const
{
  std::set<std::string> ret;
  for (const DefsBlock* b : blocks)
  {
    for (const std::string& u : b->d_uses)
    {
      if (d_owner.find(u) == d_owner.end())
      {
        ret.insert(u);
      }
    }
  }
  return ret;
}

std::vector<const DefsBlock*> DefsFile::select(
    const std::set<std::string>& syms, const std::set<std::string>& names) const
{
  std::set<size_t> keep;
  std::vector<size_t> todo;
  for (size_t i = 0, n = d_blocks.size(); i < n; i++)
  {
    bool wanted = d_blocks[i].d_keep || syms.count(d_blocks[i].d_sym) != 0;
    for (std::set<std::string>::const_iterator it = names.begin();
         !wanted && it != names.end();
         ++it)
    {
      wanted = d_blocks[i].d_defs.count(*it) != 0;
    }
    if (wanted)
    {
      keep.insert(i);
      todo.push_back(i);
    }
  }
  // what a block kept above names, and what that names in turn
  while (!todo.empty())
  {
    size_t i = todo.back();
    todo.pop_back();
    for (const std::string& u : d_blocks[i].d_uses)
    {
      std::map<std::string, size_t>::const_iterator it = d_owner.find(u);
      if (it != d_owner.end() && keep.insert(it->second).second)
      {
        todo.push_back(it->second);
      }
    }
  }
  std::vector<const DefsBlock*> ret;
  for (size_t i : keep)
  {
    ret.push_back(&d_blocks[i]);
  }
  return ret;
}

std::vector<const DefsBlock*> orderByDeclarations(
    const std::vector<const DefsBlock*>& blocks,
    const std::vector<std::string>& declarations)
{
  std::map<std::string, const DefsBlock*> owner;
  for (const DefsBlock* b : blocks)
  {
    for (const std::string& d : b->d_defs)
    {
      owner[d] = b;
    }
  }
  std::set<std::string> declared(declarations.begin(), declarations.end());
  std::vector<const DefsBlock*> ordered;
  std::set<const DefsBlock*> placed;
  std::function<void(const DefsBlock*)> placeDependencies =
      [&](const DefsBlock* b) {
        for (const std::string& u : b->d_uses)
        {
          std::map<std::string, const DefsBlock*>::const_iterator it =
              owner.find(u);
          if (it != owner.end() && declared.count(it->second->d_sym) == 0
              && placed.insert(it->second).second)
          {
            placeDependencies(it->second);
            ordered.push_back(it->second);
          }
        }
      };
  for (const std::string& declaration : declarations)
  {
    for (const DefsBlock* b : blocks)
    {
      if (b->d_sym != declaration || placed.count(b) != 0)
      {
        continue;
      }
      placeDependencies(b);
      placed.insert(b);
      ordered.push_back(b);
    }
  }
  for (const DefsBlock* b : blocks)
  {
    if (placed.insert(b).second)
    {
      ordered.push_back(b);
    }
  }
  return ordered;
}

}  // namespace ethos
