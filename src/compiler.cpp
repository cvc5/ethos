#include "compiler.h"

#include "state.h"
#include <iostream>

namespace alfc {

Compiler::Compiler(State& s) : d_state(s), d_nscopes(0), d_idCount(1) {

  d_decl << "std::map<Attr, Expr> _amap;" << std::endl;
  d_decl << "ExprInfo* _einfo;" << std::endl;
  d_decl << "std::map<Expr, size_t> _runId;" << std::endl;
  d_init << "void State::run_initialize()" << std::endl;
  d_init << "{" << std::endl;
  d_initEnd << "}" << std::endl;
  d_tc << "Expr TypeChecker::run_getTypeInternal(Expr& e, std::vector<Expr>& args, std::ostream* out)" << std::endl;
  d_tc << "{" << std::endl;
  d_tc << "  bool _matched = true;" << std::endl;
  d_tc << "  switch(_runId[e->d_type])" << std::endl;
  d_tc << "  {" << std::endl;
  d_tcEnd << "  default: break;" << std::endl;
  d_tcEnd << "  }" << std::endl;
  // TODO: write error?
  d_tcEnd << "  return nullptr;" << std::endl;
  d_tcEnd << "}" << std::endl;
  d_eval << "Expr TypeChecker::run_evaluate(Expr& e, std::vector<Expr>& args)" << std::endl;
  d_eval << "{" << std::endl;
  d_eval << "  switch(_runId[e])" << std::endl;
  d_eval << "  {" << std::endl;
  d_evalEnd << "  default: break;" << std::endl;
  d_evalEnd << "  }" << std::endl;
  // otherwise just return itself (unevaluated)
  d_evalEnd << "  std::vector<Expr> eargs;" << std::endl;
  d_evalEnd << "  eargs.push_back(e);" << std::endl;
  d_evalEnd << "  eargs.insert(eargs.end(), args.begin(), args.end());" << std::endl;
  d_evalEnd << "  return d_state.mkExprInternal(Kind::APPLY, eargs);" << std::endl;
  d_evalEnd << "}" << std::endl;
}

Compiler::~Compiler(){}

void Compiler::reset()
{
  // TODO?
}
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
  d_init << "  includeFileInternal(\"" << s << "\", true);" << std::endl;
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
  // write the code for constructing the expression
  size_t id = writeExpr(d_init, e);
  // bind the symbol
  d_init << "  bind(\"" << name << "\", _e" << id << ");" << std::endl;
  // write its type checker (if necessary)
  // Assert (e->d_type!=nullptr);
  writeTypeChecking(d_tc, e->d_type);
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
      d_init << "  _amap[" << ssa.str() << "] = nullptr;" << std::endl;
    }
  }
}
void Compiler::defineProgram(const Expr& v, const Expr& prog)
{
  if (d_nscopes>0)
  {
    return;
  }
  // for each case
  /*
  std::vector<Expr>& progChildren = it->second->d_children;
  for (Expr& c : progChildren)
  {

  }
  */
}

size_t Compiler::writeRunId(std::ostream& os, const Expr& e)
{
  std::map<ExprValue*, size_t>::iterator it = d_runIdMap.find(e.get());
  if (it!=d_runIdMap.end())
  {
    return it->second;
  }
  it = d_idMap.find(e.get());
  // Assert (it!=d_idMap.end());
  os << "  _runId[_e" << it->second << "] = " << it->second << ";" << std::endl;
  d_runIdMap[e.get()] = it->second;
  return it->second;
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
        os << "  _einfo = &d_exprData[_e" << ret << ".get()];" << std::endl;
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

void Compiler::writeTypeChecking(std::ostream& os, const Expr& t)
{
  // Assert (t!=nullptr);
  if (t->getKind()!=Kind::FUNCTION_TYPE)
  {
    // only function types need to be written here
    return;
  }
  if (d_tcWritten.find(t.get())!=d_tcWritten.end())
  {
    // already written
    return;
  }
  os << "  // type rule for " << t << std::endl;
  std::cout << "writeTypeChecking " << t << std::endl;
  d_tcWritten.insert(t.get());
  size_t id = writeRunId(d_init, t);
  std::stringstream osEnd;
  os << "  case " << id << ":" << std::endl;
  os << "  {" << std::endl;
  osEnd << "  }" << std::endl;
  osEnd << "  break;" << std::endl;

  // if the return type is ground, we don't need to build a context
  std::vector<Expr>& children = t->d_children;
  Expr& retType = children.back();
  bool isEval = retType->isEvaluatable();
  std::cout << "isEval=" << isEval << std::endl;
  if (isEval)
  {
    os << "  std::vector<Expr> evalArgs;" << std::endl;
  }
  std::vector<Expr> fvs;
  if (!t->isGround())
  {
    fvs = d_state.getTypeChecker().getFreeSymbols(retType);
  }
  std::cout << "#fvs=" << fvs.size() << std::endl;
  // write the free symbols of the return type as (local) variables
  std::stringstream tmp;
  for (const Expr& v : fvs)
  {
    size_t vid = writeExpr(tmp, v);
    os << "  Expr _e" << vid << ";" << std::endl;
  }
  // write the matching
  std::vector<std::string> reqs;
  std::vector<std::string> varAssign;
  std::map<ExprValue*, std::string> visited;
  for (size_t i=0, nargs=children.size()-1; i<nargs; i++)
  {
    std::vector<Expr> pats{children[i]};
    std::stringstream ss;
    ss << "args[" << i << "]";
    // write matching code
    writeMatching(os, pats, ss.str(), reqs, varAssign, visited);
  }
  if (!reqs.empty())
  {
    os << "  if (!(";
    bool firstTime = true;
    for (const std::string& r : reqs)
    {
      if (firstTime)
      {
        firstTime = false;
      }
      else
      {
        os << " && ";
      }
      os << r;
    }
    os << "))" << std::endl;
    os << "  {" << std::endl;
    os << "     return nullptr;" << std::endl;
    os << "  }" << std::endl;
  }
  for (const std::string& va : varAssign)
  {
    os << "  " << va << ";" << std::endl;
  }
  if (!isEval)
  {
    // if ground, write the construction of the return type statically in declarations
    // if non-ground, write the construction of the return type locally
    std::ostream& osr = retType->isGround() ? d_decl : os;
    std::cout << "retGround=" << retType->isGround() << std::endl;
    size_t retId = writeExpr(osr, retType);
    // just return the id computed above
    os << "  return _e" << retId << ";" << std::endl;
  }
  else
  {
    os << "  return run_evaluate();" << std::endl;;
  }
  os << osEnd.str();
}

void Compiler::writeMatching(std::ostream& os,
                             std::vector<Expr>& pats,
                             const std::string& t,
                             std::vector<std::string>& reqs,
                             std::vector<std::string>& varAssign,
                             std::map<ExprValue*, std::string>& visited)
{
  if (pats.size()>1)
  {
    // TODO: parallel matching?
    return;
  }
  Expr pat = pats[0];
  std::vector<std::pair<std::vector<size_t>, Expr>> toVisit;
  toVisit.emplace_back(std::pair<std::vector<size_t>, Expr>({}, pat));
  std::pair<std::vector<size_t>, Expr> curr;
  std::map<ExprValue*, size_t>::iterator it;
  std::map<ExprValue*, std::string>::iterator itv;
  do
  {
    curr = toVisit.back();
    toVisit.pop_back();
    std::string cterm = getNameForPath(t, curr.first);
    const Expr& p = curr.second;
    if (p->getKind()==Kind::VARIABLE)
    {
      // if we haven't visited yet
      itv = visited.find(p.get());
      if (itv==visited.end())
      {
        it = d_idMap.find(p.get());
        // Assert (it !=d_idMap.end());
        std::stringstream ssv;
        ssv << "_e" << it->second << " = " << cterm;
        varAssign.push_back(ssv.str());
        // map to the name we already bound
        visited[p.get()] = cterm;
      }
      else
      {
        // requires being equal to what we bound
        std::stringstream sseq;
        sseq << cterm << "==" << itv->second;
        reqs.push_back(sseq.str());
      }
    }
    else if (p->isGround())
    {
      size_t id = writeExpr(d_decl, p);
      std::stringstream ssg;
      ssg << cterm  << "==_e" << id;
      reqs.push_back(ssg.str());
      // nothing else is required
      continue;
    }
    // requires matching kind/number of children
    std::stringstream ssk;
    ssk << cterm << "->getKind()==Kind::" << p->getKind();
    reqs.push_back(ssk.str());
    std::stringstream ssnc;
    ssnc << cterm << "->getNumChildren()==" << p->getNumChildren();
    reqs.push_back(ssnc.str());
    std::vector<size_t> newPath = curr.first;
    newPath.push_back(0);
    for (size_t i=0, nchild = p->getNumChildren(); i<nchild; i++)
    {
      newPath[newPath.size()-1] = i;
      toVisit.emplace_back(std::pair<std::vector<size_t>, Expr>(newPath, (*p.get())[i]));
    }
  }while (!toVisit.empty());
}

size_t Compiler::writeEvaluation(std::ostream& os, const Expr& e)
{
  // Assert (e!=nullptr);
  if (!e->isEvaluatable())
  {
    // unevaluated types just return themselves
    return writeExpr(d_init, e);
  }
  //size_t id = writeRunId(d_init, e);

  return 0;
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
  ss << "}" << std::endl;
  return ss.str();
}

std::string Compiler::getNameForPath(const std::string& t, const std::vector<size_t>& path) const
{
  std::stringstream cterm;
  cterm << t;
  for (size_t i : path)
  {
    cterm << "[" << i << "]";
  }
  return cterm.str();
}

}  // namespace alfc
