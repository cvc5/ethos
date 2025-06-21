/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "smt_meta_reduce.h"

#include "state.h"

namespace ethos {

SmtMetaReduce::SmtMetaReduce(State& s) : d_state(s), d_tc(s.getTypeChecker()) {

}

SmtMetaReduce::~SmtMetaReduce() {}

void SmtMetaReduce::reset() {}

void SmtMetaReduce::pushScope() {}

void SmtMetaReduce::popScope() {}

void SmtMetaReduce::includeFile(const Filepath& s, bool isReference, const Expr& referenceNf) {}

void SmtMetaReduce::setLiteralTypeRule(Kind k, const Expr& t) {}

void SmtMetaReduce::bind(const std::string& name, const Expr& e) {}

void SmtMetaReduce::markConstructorKind(const Expr& v, Attr a, const Expr& cons) {}

void SmtMetaReduce::markOracleCmd(const Expr& v, const std::string& ocmd) {}

bool printAtomicTerm(const Expr& c, std::ostream& os)
{
  Kind k = c.getKind();
  if (k==Kind::CONST)
  {
    os << "sm." << c;
    return true;
  }
  else if (k==Kind::PROGRAM_CONST)
  {
    os << c;
    return true;
  }
  else if (k==Kind::TYPE)
  {
    os << "sm.Type";
    return true;
  }
  else if (k==Kind::BOOL_TYPE)
  {
    os << "sm.BoolType";
    return true;
  }
  const Literal* l = c.getValue()->asLiteral();
  if (l==nullptr)
  {
    return false;
  }
  if (k==Kind::BOOLEAN)
  {
    os << "sm." << (l->d_bool ? "True" : "False");
    return true;
  }
  else if (k==Kind::NUMERAL)
  {
    os << "(sm.Numeral " << c << ")";
    return true;
  }
  else if (k==Kind::RATIONAL)
  {
    os << "(sm.Rational " << c << ")";
    return true;
  }
  else if (k==Kind::BINARY)
  {
    const BitVector& bv = l->d_bv;
    const Integer& bvi = bv.getValue();
    os << "(sm.Binary " << bv.getSize() << " " << bvi.toString() << ")";
    return true;
  }
  else if (k==Kind::STRING)
  {
    os << "(sm.String " << c << ")";
    return true;
  }
  return false;
}

void SmtMetaReduce::defineProgram(const Expr& v, const Expr& prog) {
  std::cout << "; program " << v << std::endl;
  Expr vv = v;
  Expr vt = d_tc.getType(vv);
  std::cout << "(declare-const " << v << " (-> ";
  std::stringstream varList;
  Assert (vt.getKind()==Kind::PROGRAM_TYPE);
  size_t nargs = vt.getNumChildren();
  Assert (nargs>1);
  std::vector<std::string> args;
  std::stringstream appTerm;
  appTerm << "(" << v;
  for (size_t i=1; i<nargs; i++)
  {
    std::cout << "sm.Term ";
    if (i>1)
    {
      varList << " ";
    }
    std::stringstream ssArg;
    ssArg << "x" << i;
    appTerm << " " << ssArg.str();
    args.emplace_back(ssArg.str());
    varList << "(" << ssArg.str() << " sm.Term)";
  }
  appTerm << ")";
  std::cout << "sm.Term)";
  std::cout << ")" << std::endl;
  // compile the pattern matching
  std::stringstream cases;
  std::stringstream casesEnd;
  size_t ncases = prog.getNumChildren();
  for (size_t i=0; i<ncases; i++)
  {
    const Expr& c = prog[i];
    const Expr& hd = c[0];
    const Expr& body = c[1];
    std::map<Expr, std::string> paramToSelector;
    std::map<Expr, std::string>::iterator it;
    std::stringstream currCase;
    size_t nconj = 0;
    for (size_t j=1, nhdchild=hd.getNumChildren(); j<nhdchild; j++)
    {
      std::vector<std::pair<Expr, std::string>> visit;
      std::pair<Expr, std::string> cur;
      visit.emplace_back(hd[j], args[j-1]);
      do
      {
        cur = visit.back();
        visit.pop_back();
        Kind ck = cur.first.getKind();
        std::stringstream cname;
        bool printArgs = false;
        size_t printArgStart = 0;
        if (ck==Kind::APPLY)
        {
          cname << "sm.Apply";
          printArgs = true;
        }
        else if (ck==Kind::FUNCTION_TYPE)
        {
          cname << "sm.FunType";
          printArgs = true;
        }
        else if (ck==Kind::APPLY_OPAQUE)
        {
          cname << "sm." << cur.first[0];
          printArgStart = 1;
          printArgs = true;
        }
        if (printArgs)
        {
          // argument must be an apply
          currCase << (nconj>0 ? " " : "") << "((_ is " << cname.str() << ") " << cur.second << ")";
          nconj++;
          for (size_t i=printArgStart, nchild = cur.first.getNumChildren(); i<nchild; i++)
          {
            std::stringstream ssNext;
            ssNext << "(" << cname.str() << ".arg" << (i+1) << " " << cur.second << ")";
            visit.emplace_back(cur.first[i], ssNext.str());
          }
        }
        else if (ck==Kind::PARAM)
        {
          it = paramToSelector.find(cur.first);
          if (it==paramToSelector.end())
          {
            paramToSelector[cur.first] = cur.second;
          }
          else
          {
            currCase << (nconj>0 ? " " : "") << "(= " << cur.second << " " << it->second << ")";
            nconj++;
          }
        }
        else
        {
          std::stringstream atomTerm;
          if (printAtomicTerm(cur.first, atomTerm))
          {
            currCase << (nconj>0 ? " " : "") << "(= " << cur.second << " " << atomTerm.str() << ")";
            nconj++;
          }
          else
          {
            EO_FATAL() << "Unknown kind in case " << ck << std::endl;
          }
        }
      }
      while (!visit.empty());
    }
    // compile the return for this case
    std::stringstream currRet;
    std::stringstream currRetEnd;
    std::vector<Expr> ll;
    std::map<const ExprValue*, size_t> lbind = Expr::computeLetBinding(body, ll);
    std::map<const ExprValue*, size_t>::iterator itl;
    for (size_t i=0, nll=ll.size(); i<=nll; i++)
    {
      if (i>0)
      {
        currRet << " ";
      }
      if (i<nll)
      {
        currRet << "(let ((y" << i << " ";
        currRetEnd << ")";
      }
      Expr t = i<nll ? ll[i] : body;
      std::map<Expr, size_t>::iterator itv;
      std::vector<std::pair<Expr, size_t>> visit;
      std::pair<Expr, size_t> cur;
      visit.emplace_back(t, 0);
      do
      {
        cur = visit.back();
        if (cur.second==0)
        {
          itl = lbind.find(cur.first.getValue());
          if (itl!=lbind.end() && itl->second!=i)
          {
            currRet << "y" << itl->second;
            visit.pop_back();
            continue;
          }
          Kind ck = cur.first.getKind();
          if (ck==Kind::PARAM)
          {
            it = paramToSelector.find(cur.first);
            Assert (it!=paramToSelector.end());
            currRet << it->second;
            visit.pop_back();
            continue;
          }
          if (ck==Kind::VARIABLE)
          {
            visit.back().second++;
            currRet << "(sm.Var \"";
            currRet << cur.first;
            currRet << "\" ";
            Expr vt = d_tc.getType(cur.first);
            visit.emplace_back(vt, 0);
            continue;
          }
          else if (cur.first.getNumChildren() == 0)
          {
            if (!printAtomicTerm(cur.first, currRet))
            {
              EO_FATAL() << "Unknown atomic term in return " << ck << std::endl;
            }
            visit.pop_back();
            continue;
          }
          else
          {
            currRet << "(";
            if (ck==Kind::APPLY)
            {
              if (cur.first[0].getKind()!=Kind::PROGRAM_CONST)
              {
                Assert (cur.first.getNumChildren()==2);
                currRet << "sm.Apply ";
              }
            }
            else if (ck==Kind::FUNCTION_TYPE)
            {
              Assert (cur.first.getNumChildren()==2);
              currRet << "sm.FunType ";
            }
            else if (isLiteralOp(ck))
            {
              std::string kstr = kindToTerm(ck);
              if (kstr.compare(0, 4, "eo::") == 0)
              {
                currRet << "$eo_" << kstr.substr(4) << " ";
              }
              else
              {
                EO_FATAL() << "Bad name for literal kind " << ck << std::endl;
              }
            }
            else
            {
            }
            visit.back().second++;
            visit.emplace_back(cur.first[0], 0);
          }
        }
        else if (cur.second >= cur.first.getNumChildren())
        {
          currRet << ")";
          visit.pop_back();
        }
        else
        {
          Assert (cur.second<cur.first.getNumChildren());
          currRet << " ";
          visit.back().second++;
          visit.emplace_back(cur.first[cur.second], 0);
        }
      }
      while (!visit.empty());
      if (i<nll)
      {
        currRet << "))";
      }
    }
    currRet << currRetEnd.str();
    // now print the case/return
    cases << "  (ite ";
    if (nconj==0)
    {
      cases << "true";
    }
    else if (nconj>1)
    {
      cases << "(and ";
      cases << currCase.str();
      cases << ")";
    }
    else
    {
      cases << currCase.str();
    }
    cases << std::endl;
    cases << "    (= " << appTerm.str() << " " << currRet.str() << ")" << std::endl;
    casesEnd << ")";
  }
  // axiom
  std::cout << "(assert (forall (" << varList.str() << ")" << std::endl;
  std::cout << cases.str();
  std::cout << "    true";
  std::cout << casesEnd.str() << std::endl;
  std::cout << "))" << std::endl;
  std::cout << std::endl;

}

void SmtMetaReduce::finalize() {}

std::string toString() {
  std::stringstream ss;
  return ss.str();
}

}  // namespace ethos
