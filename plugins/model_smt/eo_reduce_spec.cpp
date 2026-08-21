/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "eo_reduce_spec.h"

#include <algorithm>
#include <cctype>
#include <set>
#include <sstream>

#include "base/check.h"

namespace ethos {

namespace {

/** The name of the program whose cases are the term-level reductions. */
const char* s_termProgram = "$eo_to_smt";
/** The name of the program whose cases are the type-level reductions. */
const char* s_typeProgram = "$eo_to_smt_type";

/** Is c a character that may occur in an (unquoted) Eunoia symbol? */
bool isSymbolChar(char c)
{
  return !std::isspace(static_cast<unsigned char>(c)) && c != '(' && c != ')'
         && c != ';' && c != '"' && c != '|';
}

/** Return the position of the first character of s at or after i that is not
 * whitespace and is not part of a comment. */
size_t skipWs(const std::string& s, size_t i)
{
  while (i < s.size())
  {
    if (std::isspace(static_cast<unsigned char>(s[i])))
    {
      i++;
    }
    else if (s[i] == ';')
    {
      while (i < s.size() && s[i] != '\n')
      {
        i++;
      }
    }
    else
    {
      break;
    }
  }
  return i;
}

/** Return the position just past the string or |...| symbol opened at i. */
size_t skipQuoted(const std::string& s, size_t i)
{
  char close = s[i];
  i++;
  while (i < s.size() && s[i] != close)
  {
    i++;
  }
  return i < s.size() ? i + 1 : i;
}

/**
 * Read the form beginning at or after i, that is, either a parenthesized form
 * or an atom. Sets start to the position of its first character and returns
 * the position just past its last character. If there is no further form,
 * i.e. the remainder of s is whitespace, comments, or a closing parenthesis,
 * this returns start.
 */
size_t readForm(const std::string& s, size_t i, size_t& start)
{
  i = skipWs(s, i);
  start = i;
  if (i >= s.size() || s[i] == ')')
  {
    return i;
  }
  if (s[i] == '"' || s[i] == '|')
  {
    return skipQuoted(s, i);
  }
  if (s[i] != '(')
  {
    while (i < s.size() && isSymbolChar(s[i]))
    {
      i++;
    }
    return i;
  }
  size_t depth = 0;
  while (i < s.size())
  {
    char c = s[i];
    if (c == '"' || c == '|')
    {
      i = skipQuoted(s, i);
      continue;
    }
    if (c == ';')
    {
      i = skipWs(s, i);
      continue;
    }
    i++;
    if (c == '(')
    {
      depth++;
    }
    else if (c == ')')
    {
      depth--;
      if (depth == 0)
      {
        return i;
      }
    }
  }
  // unbalanced; the caller reports this as a parse error
  return i;
}

/**
 * Return the positions of the children of the parenthesized form spanning
 * [start, end), i.e. the forms between its parentheses.
 */
std::vector<std::pair<size_t, size_t>> getChildren(const std::string& s,
                                                   size_t start,
                                                   size_t end)
{
  std::vector<std::pair<size_t, size_t>> children;
  Assert(s[start] == '(');
  size_t i = start + 1;
  while (i < end)
  {
    size_t cstart;
    size_t cend = readForm(s, i, cstart);
    if (cend == cstart || cstart >= end)
    {
      break;
    }
    children.emplace_back(cstart, cend);
    i = cend;
  }
  return children;
}

/** Return the verbatim text of the form spanning [start, end). */
std::string getText(const std::string& s, const std::pair<size_t, size_t>& f)
{
  return s.substr(f.first, f.second - f.first);
}

/**
 * Add to refs every name in names that occurs as a symbol in text. Note that
 * this treats a name occurring in a comment or a string literal as an
 * occurrence, which is harmless: at worst an auxiliary program that is not
 * needed is emitted.
 */
void addSymbolRefs(const std::string& text,
                   const std::set<std::string>& names,
                   std::set<std::string>& refs)
{
  size_t i = 0;
  while (i < text.size())
  {
    if (!isSymbolChar(text[i]))
    {
      i++;
      continue;
    }
    size_t start = i;
    while (i < text.size() && isSymbolChar(text[i]))
    {
      i++;
    }
    std::string tok = text.substr(start, i - start);
    if (names.find(tok) != names.end())
    {
      refs.insert(tok);
    }
  }
}

/**
 * Check that the parentheses of s are balanced, ignoring those in comments and
 * in quoted symbols and strings. Returns true if they are, and otherwise sets
 * err to a description naming the line at fault. Everything below assumes a
 * balanced file, which is why this runs first.
 */
bool checkBalanced(const std::string& s, std::string& err)
{
  std::vector<size_t> openLines;
  size_t line = 1;
  size_t i = 0;
  while (i < s.size())
  {
    char c = s[i];
    if (c == '\n')
    {
      line++;
      i++;
    }
    else if (c == ';')
    {
      i = skipWs(s, i);
    }
    else if (c == '"' || c == '|')
    {
      size_t next = skipQuoted(s, i);
      line += std::count(s.begin() + i, s.begin() + next, '\n');
      i = next;
    }
    else
    {
      if (c == '(')
      {
        openLines.push_back(line);
      }
      else if (c == ')')
      {
        if (openLines.empty())
        {
          err = "unmatched ) on line " + std::to_string(line);
          return false;
        }
        openLines.pop_back();
      }
      i++;
    }
  }
  if (!openLines.empty())
  {
    err = "unmatched ( on line " + std::to_string(openLines.back());
    return false;
  }
  return true;
}

}  // namespace

bool EoReduceSpec::parse(const std::string& s, std::string& err)
{
  if (!checkBalanced(s, err))
  {
    return false;
  }
  // The cases of the two reduction programs, paired with whether they belong
  // to the type-level one, in the order they occur in the file.
  std::vector<std::pair<std::pair<size_t, size_t>, bool>> caseForms;
  size_t i = 0;
  while (true)
  {
    size_t start;
    size_t end = readForm(s, i, start);
    if (end == start)
    {
      break;
    }
    i = end;
    if (s[start] != '(')
    {
      err = "expected a command, got " + getText(s, {start, end});
      return false;
    }
    std::vector<std::pair<size_t, size_t>> children = getChildren(s, start, end);
    if (children.size() < 2)
    {
      err = "expected a named command, got " + getText(s, {start, end});
      return false;
    }
    std::string name = getText(s, children[1]);
    if (name != s_termProgram && name != s_typeProgram)
    {
      // an auxiliary definition, which we carry along verbatim
      if (d_auxText.find(name) != d_auxText.end())
      {
        err = "auxiliary definition " + name + " is defined twice";
        return false;
      }
      d_auxText[name] = getText(s, {start, end});
      d_auxOrder.push_back(name);
      continue;
    }
    // The cases of a program are its final argument, e.g. in
    // (program $eo_to_smt (<params>) :signature (T) $smt_Term (<cases>)).
    const std::pair<size_t, size_t>& cases = children.back();
    if (s[cases.first] != '(')
    {
      err = name + " does not end in a list of cases";
      return false;
    }
    for (const std::pair<size_t, size_t>& c :
         getChildren(s, cases.first, cases.second))
    {
      caseForms.emplace_back(c, name == s_typeProgram);
    }
  }

  std::set<std::string> auxNames;
  for (const std::string& a : d_auxOrder)
  {
    auxNames.insert(a);
  }
  // The auxiliary definitions each auxiliary definition itself requires.
  std::map<std::string, std::set<std::string>> auxRefs;
  for (const std::string& a : d_auxOrder)
  {
    addSymbolRefs(d_auxText[a], auxNames, auxRefs[a]);
    auxRefs[a].erase(a);
  }

  for (const std::pair<std::pair<size_t, size_t>, bool>& cf : caseForms)
  {
    std::vector<std::pair<size_t, size_t>> parts;
    if (s[cf.first.first] == '(')
    {
      parts = getChildren(s, cf.first.first, cf.first.second);
    }
    if (parts.size() != 2)
    {
      err = "expected a (<pattern> <return>) case, got "
            + getText(s, cf.first);
      return false;
    }
    // The pattern is an application of the program to the term it reduces,
    // e.g. ($eo_to_smt (exists x1 x2)).
    std::vector<std::pair<size_t, size_t>> pat;
    if (s[parts[0].first] == '(')
    {
      pat = getChildren(s, parts[0].first, parts[0].second);
    }
    if (pat.size() != 2)
    {
      err = "expected a pattern applying the program to one term, got "
            + getText(s, parts[0]);
      return false;
    }
    EoReduceCase rc;
    rc.d_pattern = getText(s, pat[1]);
    rc.d_ret = getText(s, parts[1]);
    rc.d_isType = cf.second;
    std::vector<std::pair<size_t, size_t>> args =
        s[pat[1].first] == '('
            ? getChildren(s, pat[1].first, pat[1].second)
            : std::vector<std::pair<size_t, size_t>>{pat[1]};
    if (args.empty())
    {
      err = "the pattern " + getText(s, parts[0]) + " reduces no symbol";
      return false;
    }
    rc.d_symbol = getText(s, args[0]);
    rc.d_arity = args.size() - 1;
    // The case is generic, i.e. it applies to every application of the
    // symbol, if its arguments are exactly x1 ... xn.
    rc.d_generic = true;
    for (size_t a = 1, nargs = args.size(); a < nargs; a++)
    {
      std::stringstream expected;
      expected << "x" << a;
      if (getText(s, args[a]) != expected.str())
      {
        rc.d_generic = false;
        break;
      }
    }
    // Determine the auxiliary definitions this case requires, i.e. those it
    // mentions together with those they mention in turn.
    std::set<std::string> required;
    addSymbolRefs(rc.d_pattern, auxNames, required);
    addSymbolRefs(rc.d_ret, auxNames, required);
    for (bool changed = true; changed;)
    {
      changed = false;
      for (const std::string& r : std::set<std::string>(required))
      {
        for (const std::string& rr : auxRefs[r])
        {
          changed = required.insert(rr).second || changed;
        }
      }
    }
    for (const std::string& a : d_auxOrder)
    {
      if (required.find(a) != required.end())
      {
        rc.d_aux.push_back(a);
      }
    }
    d_cases.push_back(rc);
  }
  return true;
}

const std::vector<EoReduceCase>& EoReduceSpec::getCases() const
{
  return d_cases;
}

const std::string& EoReduceSpec::getAuxProgram(const std::string& name) const
{
  std::map<std::string, std::string>::const_iterator it = d_auxText.find(name);
  Assert(it != d_auxText.end()) << "no auxiliary definition " << name;
  return it->second;
}

}  // namespace ethos
