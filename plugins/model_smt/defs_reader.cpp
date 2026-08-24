#include "defs_reader.h"

#include <fstream>
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

/** Every name form uses, i.e. every word of it that begins with a dollar. */
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
    if (p != std::string::npos)
    {
      cs = cs.substr(0, p) + agg + cs.substr(p + name.size());
    }
    ret.push_back(cs);
  }
  return ret;
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
  for (const std::string& f : forms(text))
  {
    const std::string kind = formKind(f);
    if (kind == "echo")
    {
      // A directive to another stage of the compiler rather than something
      // the model says, e.g. one that leaves the symbol out of the
      // compilation altogether, see Desugar::echo. It names nothing here.
      continue;
    }
    const std::string name = formName(f);
    namesOf(f, b.d_uses);
    b.d_defs.insert(name);
    if (kind == "declare-const" || kind == "declare-parameterized-const"
        || kind == "define")
    {
      // the constructor of the embedding for the symbol, and its macro
      b.d_cons.push_back(f);
      continue;
    }
    if (kind != "program")
    {
      continue;
    }
    // A program is either one of the per-symbol programs, whose cases the
    // aggregate it feeds takes, or an auxiliary one the cases call, which is
    // copied as it stands.
    auto isPre = [&name](const char* p) {
      const std::string pre(p);
      return name.size() > pre.size() && name.compare(0, pre.size(), pre) == 0;
    };
    if (isPre("$eoc_is_list_nil_"))
    {
      // The nil of an n-ary symbol, which the desugar stage looks up by name.
      // It is written here as $eoc_ and emitted as $eo_, since it is the
      // program that stage calls rather than a case of an aggregate.
      const std::string from = "$eoc_is_list_nil_";
      const std::string to = "$eo_is_list_nil_";
      std::string out = f;
      size_t pos = out.find(from);
      while (pos != std::string::npos)
      {
        out = out.substr(0, pos) + to + out.substr(pos + from.size());
        pos = out.find(from, pos + to.size());
      }
      b.d_desugarAux.push_back(out);
    }
    else if (isPre("$eoc_eval_"))
    {
      b.d_evalCases = casesOf(f, name, "$smtx_model_eval");
    }
    else if (isPre("$eoc_typeof_"))
    {
      b.d_typeofCases = casesOf(f, name, "$smtx_typeof");
    }
    else if (isPre("$eoc_transform_type_"))
    {
      b.d_transTypeCases = casesOf(f, name, "$eo_to_smt_type");
    }
    else if (isPre("$eoc_transform_"))
    {
      b.d_transCases = casesOf(f, name, "$eo_to_smt");
    }
    else if (isPre("$smtx_typeof_"))
    {
      b.d_typeofAux.push_back(f);
    }
    else if (isPre("$smtx_model_eval_"))
    {
      b.d_evalProgs.push_back(f);
      std::string fwd = fwdOf(f, name);
      if (!fwd.empty())
      {
        b.d_evalFwd.push_back(fwd);
      }
    }
    else if (isPre("$eo_to_smt"))
    {
      b.d_eoAux.push_back(f);
    }
    else
    {
      // A method of the symbol that is neither of the two above, e.g. the one
      // that reads a sequence at an index. It goes with the evaluators, which
      // the generated file has before every case that may call one.
      b.d_evalProgs.push_back(f);
    }
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

bool DefsFile::read(const std::string& path)
{
  std::ifstream in(path);
  if (!in.is_open())
  {
    return false;
  }
  std::stringstream ss;
  ss << in.rdbuf();
  const std::string text = ss.str();
  // A block runs from the line that names its symbol to the next one.
  const std::string mark = "\n; -- ";
  size_t i = text.find(mark);
  while (i != std::string::npos)
  {
    size_t ns = i + mark.size();
    size_t ne = text.find('\n', ns);
    size_t next = text.find(mark, ns);
    addBlock(text.substr(ns, ne - ns),
             text.substr(ne + 1,
                         (next == std::string::npos ? text.size() : next)
                             - (ne + 1)));
    i = next;
  }
  return true;
}

bool DefsFile::hasSymbol(const std::string& sym) const
{
  for (const DefsBlock& b : d_blocks)
  {
    if (b.d_sym == sym)
    {
      return true;
    }
  }
  return false;
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
    const std::set<std::string>& syms,
    const std::set<std::string>& names) const
{
  std::set<size_t> keep;
  std::vector<size_t> todo;
  for (size_t i = 0, n = d_blocks.size(); i < n; i++)
  {
    bool wanted = syms.count(d_blocks[i].d_sym) != 0;
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

}  // namespace ethos
