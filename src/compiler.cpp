#include "compiler.h"

#include "state.h"

namespace alfc {

Compiler::Compiler(State& s) : d_state(s), d_nscopes(0), d_idCount(1) {

  d_decl << "std::map<Attr, Expr> _amap;" << std::endl;
  d_decl << "ExprInfo* _einfo;" << std::endl;
  d_init << "void State::initializeCompiled()" << std::endl;
  d_init << "{" << std::endl;
  d_initEnd << "}" << std::endl;
}

Compiler::~Compiler(){}

void Compiler::pushScope()
{
  d_nscopes++;
}
void Compiler::popScope()
{
  // Assert (d_nscopes>0);
  d_nscopes--;
}
void Compiler::includeFile(const std::string& s)
{
  if (d_nscopes>0)
  {
    return;
  }
}
void Compiler::addAssumption(const Expr& a)
{
  if (d_nscopes>0)
  {
    return;
  }
}
void Compiler::bind(const std::string& name, const Expr& e)
{
  if (d_nscopes>0)
  {
    return;
  }
  size_t id = writeExpr(d_init, e);
  d_init << "  bind(\"" << name << "\", _e" << id << ");" << std::endl;
  // TODO: type checker

}
void Compiler::markAttributes(const Expr& v, const std::map<Attr, Expr>& attrs)
{
  if (d_nscopes>0)
  {
    return;
  }
  d_init << "  _amap.clear();" << std::endl;
  for (const std::pair<const Attr, Expr>& p : attrs)
  {
    std::stringstream ssa;
    ssa << "Attr::" << p.first;
    if (p.second!=nullptr)
    {
      size_t id = writeExpr(d_init, p.second);
      d_init << "  _amap[" << ssa.str() << "] = _e" << id << ";" << std::endl;
    }
    else
    {

    }
  }
}
void Compiler::defineProgram(const Expr& v, const Expr& prog)
{
  if (d_nscopes>0)
  {
    return;
  }
}

size_t Compiler::writeExpr(std::ostream& os, const Expr& e)
{
  size_t ret = 0;
  size_t tid = 0;
  std::unordered_set<ExprValue*> visited;
  std::unordered_set<ExprValue*>::iterator it;
  std::vector<ExprValue*> visit;
  visit.emplace_back(e.get());
  std::map<ExprValue*, size_t>::iterator iti;
  ExprValue * cur;
  ExprInfo* curInfo;
  do
  {
    cur = visit.back();
    iti = d_idMap.find(cur);
    if (iti!=d_idMap.end())
    {
      ret = iti->second;
      visit.pop_back();
      continue;
    }
    it = visited.find(cur);
    std::vector<Expr>& children = cur->d_children;
    if (it==visited.end())
    {
      visited.insert(cur);
      for (Expr& c : children)
      {
        visit.push_back(c.get());
      }
    }
    else
    {
      visit.pop_back();
      // allocate an identifier
      ret = d_idCount;
      d_idCount++;
      d_idMap[cur] = ret;
      d_decl << "Expr _e" << ret << ";" << std::endl;
      os << "  _e" << ret << " = mkExprInternal(Kind::" << cur->getKind() << ", {";
      bool firstTime = true;
      for (Expr& c : children)
      {
        if (firstTime)
        {
          firstTime = false;
        }
        else
        {
          os << ", ";
        }
        iti = d_idMap.find(c.get());
        // Assert (iti!=d_idMap.end());
        os << "_e" << iti->second;
      }
      os << "});" << std::endl;
      // TODO: should hash?
      // allocate information if necessary
      curInfo = d_state.getInfo(cur);
      if (curInfo!=nullptr)
      {
        os << "  _einfo = &d_exprData[_e" << ret << "];" << std::endl;
        os << "  _einfo->d_str = std::string(\"" << curInfo->d_str << "\");" << std::endl;
      }
      // Write its type as well, separately. The recursion depth here is very limited.
      if (cur->d_type!=nullptr)
      {
        tid = writeExpr(os, cur->d_type);
        os << "  _e" << ret << "->d_type = _e" << tid << ";" << std::endl;
      }
    }
  }while(!visit.empty());
  // Assert (ret!=0);
  // return the identifier for the initial term
  return ret;
}

std::string Compiler::toString()
{
  std::stringstream ss;
  ss << "#include \"state.h\"" << std::endl;
  ss << "#include \"type_checker.h\"" << std::endl;
  ss << std::endl;
  ss << "namespace alfc {" << std::endl;
  ss << std::endl;
  ss << d_decl.str() << std::endl;
  ss << d_init.str();
  ss << d_initEnd.str() << std::endl;
  ss << d_tc.str();
  ss << d_tcEnd.str() << std::endl;
  ss << d_eval.str();
  ss << d_evalEnd.str() << std::endl;
  return ss.str();
}

}  // namespace alfc
