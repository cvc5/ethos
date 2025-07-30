/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "model_smt.h"

#include <fstream>
#include <sstream>
#include <string>

#include "state.h"

namespace ethos {

ModelSmt::ModelSmt(State& s) : StdPlugin(s)
{
  Kind kBool = Kind::BOOLEAN;
  Kind kInt = Kind::NUMERAL;
  Kind kReal = Kind::RATIONAL;
  Kind kString = Kind::STRING;
  Kind kBitVec = Kind::BINARY;
  Kind kT = Kind::PARAM;
  Kind kRegLan = Kind::EVAL_TO_STRING;
  d_kindToEoPrefix[kBool] = "bool";
  d_kindToEoPrefix[kInt] = "z";
  d_kindToEoPrefix[kReal] = "q";
  d_kindToEoPrefix[kString] = "str";
  d_kindToEoPrefix[kBitVec] = "bin";
  d_kindToType[kBool] = "Bool";
  d_kindToType[kInt] = "Int";
  d_kindToType[kReal] = "Real";
  d_kindToType[kString] = "String";
  d_kindToType[kBitVec] = "Binary";
  d_kindToType[kRegLan] = "RegLan";
  // All SMT-LIB symbols require having their semantics defined here.
  // Note that we model *SMT-LIB* not *CPC* here.
  // builtin
  addHardCodeSym("=", {kT, kT});
  addHardCodeSym("ite", {kBool, kT, kT});
  // Booleans
  addConstFoldSym("and", {kBool, kBool}, kBool);
  addConstFoldSym("or", {kBool, kBool}, kBool);
  addConstFoldSym("xor", {kBool, kBool}, kBool);
  addConstFoldSym("=>", {kBool, kBool}, kBool);
  addConstFoldSym("not", {kBool}, kBool);
  // arithmetic
  addTypeSym("Int", {}, "($vsm_term ($sm_mk_z n))", "Int");
  addTypeSym("Real", {}, "($vsm_term ($sm_mk_q r))", "Real");
  // use kT to stand for either Int or Real arithmetic (not mixed)
  addConstFoldSym("+", {kT, kT}, kT);
  addConstFoldSym("-", {kT, kT}, kT);
  addConstFoldSym("*", {kT, kT}, kT);
  // we expect "-" to be overloaded, we look for its desugared name and map it
  // back
  addConstFoldSym("$eoo_-.2", {kT}, kT);
  d_overloadRevert["$eoo_-.2"] = "-";
  addConstFoldSym("abs", {kInt}, kInt);
  addConstFoldSym(">=", {kT, kT}, kBool);
  addConstFoldSym("<=", {kT, kT}, kBool);
  addConstFoldSym(">", {kT, kT}, kBool);
  addConstFoldSym("<", {kT, kT}, kBool);
  addConstFoldSym("is_int", {kReal}, kBool);
  addConstFoldSym("/", {kReal, kReal}, kReal);
  addConstFoldSym("div", {kInt, kInt}, kInt);
  addConstFoldSym("mod", {kInt, kInt}, kInt);
  addConstFoldSym("to_int", {kReal}, kInt);
  addConstFoldSym("to_real", {kInt}, kReal);
  addTermReduceSym("divisible", {kInt, kInt}, "(= (mod x2 x1) 0)");
  // arrays
  addTypeSym(
      "Array",
      {kT, kT},
      "($vsm_map m)",
      "($smtx_builtin_requires ($smtx_map_has_type m x1 x2) (Array x1 x2))");
  addRecReduceSym("select", {kT, kT}, "($smtx_map_select e1 e2)");
  addRecReduceSym("store", {kT, kT, kT}, "($smtx_map_store e1 e2 e3)");
  // strings
  addTypeSym("Seq",
             {kT},
             "($vsm_seq sq)",
             "($smtx_builtin_requires ($smtx_seq_has_type sq x1) (Seq x1))");
  // string is represented as sequence of characters
  addTypeSym("(Seq Char)", {}, "($vsm_term ($sm_mk_str s))", "(Seq Char)");
  d_typeCase["Seq"].push_back("(Seq Char)");
  d_symIgnore["Char"] = true;
  d_symIgnore["RegLan"] = true;
  addConstFoldSym("str.++", {kString, kString}, kString);
  addConstFoldSym("str.len", {kString}, kInt);
  addConstFoldSym("str.substr", {kString, kInt, kInt}, kString);
  addConstFoldSym("str.at", {kString, kInt}, kString);
  addConstFoldSym("str.indexof", {kString, kString, kInt}, kInt);
  addConstFoldSym("str.replace", {kString, kString, kString}, kString);
  addConstFoldSym("str.replace_all", {kString, kString, kString}, kString);
  addConstFoldSym("str.from_code", {kInt}, kString);
  addConstFoldSym("str.to_code", {kString}, kInt);
  addConstFoldSym("str.from_int", {kInt}, kString);
  addConstFoldSym("str.to_int", {kString}, kInt);
  addConstFoldSym("str.is_digit", {kString}, kBool);
  addConstFoldSym("str.contains", {kString, kString}, kBool);
  addConstFoldSym("str.suffixof", {kString, kString}, kBool);
  addConstFoldSym("str.prefixof", {kString, kString}, kBool);
  addConstFoldSym("str.<=", {kString, kString}, kBool);
  addConstFoldSym("str.<", {kString, kString}, kBool);
#if 0
  addReduceSym("re.allchar", {}, "($vsm_re ($smt_apply_0 \"re.allchar\"))");
  addReduceSym("re.none", {}, "($vsm_re ($smt_apply_0 \"re.none\"))");
  addReduceSym("re.all", {}, "($vsm_re ($smt_apply_0 \"re.all\"))");
  addConstFoldSym("str.in_re", {kString, kRegLan}, kBool);
  addConstFoldSym("str.to_re", {kString}, kRegLan);
  addConstFoldSym("re.*", {kRegLan}, kRegLan);
  addConstFoldSym("re.+", {kRegLan}, kRegLan);
  addConstFoldSym("re.opt", {kRegLan}, kRegLan);
  addConstFoldSym("re.comp", {kRegLan}, kRegLan);
  addConstFoldSym("re.++", {kRegLan, kRegLan}, kRegLan);
  addConstFoldSym("re.inter", {kRegLan, kRegLan}, kRegLan);
  addConstFoldSym("re.union", {kRegLan, kRegLan}, kRegLan);
  addConstFoldSym("re.range", {kString, kString}, kRegLan);
#endif
  // bitvectors
  addTypeSym("BitVec",
             {kInt},
             "($vsm_term ($sm_binary w n))",
             "($eo_requires_eq x1 ($eo_mk_numeral w) (BitVec x1))");
  // the following are return terms of aux program cases of the form:
  // (($smtx_model_eval_f
  //    ($vsm_term ($sm_binary x1 x2)) ($vsm_term ($sm_binary x3 x4)))
  //    <return>)
  // where x1, x3 denote bitwidths and x2, x4 denote values.
  addLitBinSym("bvadd", {kBitVec, kBitVec}, "x1", "($smt_builtin_add x2 x4)");
  addLitBinSym("bvmul", {kBitVec, kBitVec}, "x1", "($smt_builtin_mul x2 x4)");
  addLitBinSym(
      "bvand", {kBitVec, kBitVec}, "x1", "($smtx_binary_and x1 x2 x4)");
  addLitBinSym("bvor", {kBitVec, kBitVec}, "x1", "($smtx_binary_or x1 x2 x4)");
  addLitBinSym(
      "bvxor", {kBitVec, kBitVec}, "x1", "($smtx_binary_xor x1 x2 x4)");
  addLitBinSym("bvnot", {kBitVec}, "x1", "($smtx_binary_not x1 x2)");
  addLitBinSym("bvneg", {kBitVec}, "x1", "($smt_builtin_neg x2)");
  addLitBinSym("extract",
               {kInt, kInt, kBitVec},
               "x3",
               "($smtx_binary_extract x3 x4 x1 x2)");
  addLitBinSym("concat",
               {kBitVec, kBitVec},
               "($smt_builtin_add x1 x3)",
               "($smtx_binary_concat x1 x2 x3 x4)");
  // the following are program cases in the main method of the form
  // (($smtx_model_eval (f x1 x2)) ($smtx_model_eval <return>))
  addTermReduceSym("bvsub", {kBitVec, kBitVec}, "(bvadd x1 (bvneg x2))");
  addTermReduceSym("bvsle", {kBitVec, kBitVec}, "(bvsge x2 x1)");
  addTermReduceSym("bvule", {kBitVec, kBitVec}, "(bvuge x2 x1)");
  addTermReduceSym("bvslt", {kBitVec, kBitVec}, "(bvsgt x2 x1)");
  addTermReduceSym("bvult", {kBitVec, kBitVec}, "(bvugt x2 x1)");
  addTermReduceSym("bvnand", {kBitVec, kBitVec}, "(bvnot (bvand x1 x2))");
  addTermReduceSym("bvnor", {kBitVec, kBitVec}, "(bvnot (bvor x1 x2))");
  addTermReduceSym("bvxnor", {kBitVec, kBitVec}, "(bvnot (bvxor x1 x2))");
  addTermReduceSym("bvuge", {kBitVec, kBitVec}, "(or (bvugt x1 x2) (= x1 x2))");
  addTermReduceSym("bvsge", {kBitVec, kBitVec}, "(or (bvsgt x1 x2) (= x1 x2))");
  // arith/BV conversions
  addLitSym("ubv_to_int", {kBitVec}, kInt, "x2");
  addLitBinSym("int_to_bv", {kInt, kInt}, "x1", "x2");
  // Quantifiers
  addQuantifier("exists", {Kind::ANY, kBool});
  addQuantifier("forall", {Kind::ANY, kBool});
  addReduceSym(
      "@quantifiers_skolemize", {kBool, kInt}, "($smtx_eval_choice_nth x1 x2)");

  ///----- non standard extensions and skolems
  // builtin
  addTermReduceSym("@purify", {kT}, "x1");
  // arithmetic
  // addConstFoldSym("^", {kT, kT}, kT);
  addConstFoldSym("/_total", {kT, kT}, kReal);
  addConstFoldSym("div_total", {kInt, kInt}, kInt);
  addConstFoldSym("mod_total", {kInt, kInt}, kInt);
  addConstFoldSym("int.pow2", {kInt}, kInt);
  addTermReduceSym("@int_div_by_zero", {kInt}, "(div x1 0)");
  addTermReduceSym("@mod_by_zero", {kInt}, "(mod x1 0)");
  addTermReduceSym("@div_by_zero", {kReal}, "(/ x1 0/1)");
  // TODO: is this right? if so, simplify CPC
  addTermReduceSym("int.log2", {kInt}, "(div x1 (int.pow2 x1))");
  addTermReduceSym("int.ispow2", {kInt}, "(= x1 (int.pow2 (int.log2 x1)))");
  // arrays
  addRecReduceSym("@array_deq_diff", {kT, kT}, "($smtx_map_diff e1 e2)");
  // strings
  addConstFoldSym("str.update", {kString, kInt, kString}, kString);
  addConstFoldSym("str.rev", {kString}, kString);
  addConstFoldSym("str.to_lower", {kString}, kString);
  addConstFoldSym("str.to_upper", {kString}, kString);
  addTermReduceSym("@strings_itos_result",
                   {kInt, kInt},
                   "(str.from_int (mod x1 (^ 10 x2)))");
  addTermReduceSym("@strings_stoi_result",
                   {kString, kInt},
                   "(str.to_int (str.substr x1 0 x2))");
  addTermReduceSym("@strings_stoi_non_digit",
                   {kString},
                   "(str.indexof_re x1 (re.comp (re.range \"0\" \"9\")) 0)");
  // sequences
  addReduceSym("seq.empty", {kT}, "$smtx_empty_seq");
  addRecReduceSym("seq.unit", {kT}, "($smtx_seq_unit e1)");
  addRecReduceSym("seq.nth", {kT, kInt}, "($smtx_seq_nth e1 e2)");
  // sets
  // (Set T) is modelled as (Array T Bool).
  addTypeSym(
      "Set",
      {kT},
      "($vsm_map m)",
      "($smtx_builtin_requires ($smtx_map_has_type m x1 Bool) (Set x1))");
  addReduceSym("set.empty", {kT}, "$smtx_empty_set");
  addRecReduceSym("set.singleton", {kT}, "($smtx_set_singleton e1)");
  addRecReduceSym("set.inter", {kT, kT}, "($smtx_set_inter e1 e2)");
  addRecReduceSym("set.minus", {kT, kT}, "($smtx_set_minus e1 e2)");
  addRecReduceSym("set.union", {kT, kT}, "($smtx_set_union e1 e2)");
  addRecReduceSym("set.member", {kT, kT}, "($smtx_map_select e2 e1)");
  addTermReduceSym("set.subset", {kT, kT}, "(= (set.inter x1 x2) x1)");
  addRecReduceSym("@sets_deq_diff", {kT, kT}, "($smtx_map_diff e1 e2)");
  addRecReduceSym(
      "set.is_empty",
      {kT},
      "($vsm_term ($sm_mk_bool ($smt_apply_= e1 $smtx_empty_set)))");
  // x1))");
  //   bitvectors
  addTermReduceSym(
      "bvite", {kBitVec, kBitVec, kBitVec}, "(ite (= x1 (@bv 1 1)) x2 x3)");
  addTermReduceSym(
      "bvcomp", {kBitVec, kBitVec}, "(ite (= x1 x2) (@bv 1 1) (@bv 0 1))");
  addTermReduceSym("bvultbv",
                   {kBitVec, kBitVec, kBitVec},
                   "(ite (bvult x1 x2) (@bv 1 1) (@bv 0 1))");
  addTermReduceSym("bvsltbv",
                   {kBitVec, kBitVec, kBitVec},
                   "(ite (bvslt x1 x2) (@bv 1 1) (@bv 0 1))");
  addLitSym("@bvsize", {kBitVec}, kInt, "x1");
  addLitBinSym("@bv", {kInt, kInt}, "x2", "x1");
  addTermReduceSym("@bit", {kInt, kBitVec}, "(extract x1 x1 x2)");
  // tuples
  // these allow Herbrand interpretations
  // addTypeSym("Tuple", {kT, kT});
  // addTypeSym("UnitTuple", {});
  d_symIgnore["Tuple"] = true;
  d_symIgnore["UnitTuple"] = true;
  addReduceSym("tuple", {}, "($vsm_apply ($vsm_term tuple) $vsm_not_value)");
  addReduceSym("tuple.unit", {}, "($vsm_term tuple.unit)");
}

ModelSmt::~ModelSmt() {}

void ModelSmt::addTypeSym(const std::string& sym,
                          const std::vector<Kind>& args,
                          const std::string& cpat,
                          const std::string& cret)
{
  d_symTypes[sym] =
      std::tuple<std::vector<Kind>, std::string, std::string>(args, cpat, cret);
}

void ModelSmt::addHardCodeSym(const std::string& sym,
                              const std::vector<Kind>& args)
{
  d_symHardCode[sym] = args;
}

void ModelSmt::addConstFoldSym(const std::string& sym,
                               const std::vector<Kind>& args,
                               Kind ret)
{
  d_symConstFold[sym] = std::pair<std::vector<Kind>, Kind>(args, ret);
}

void ModelSmt::addQuantifier(const std::string& sym,
                             const std::vector<Kind>& args)
{
  // always call hard-coded method, without pre-evaluation
  std::stringstream ret;
  ret << "($smtx_model_eval_" << sym << " (" << sym << " x1 x2 ))";
  addReduceSym(sym, args, ret.str());
}

void ModelSmt::addLitBinSym(const std::string& sym,
                            const std::vector<Kind>& args,
                            const std::string& retWidth,
                            const std::string& retNum)
{
  std::stringstream ssr;
  ssr << "($vsm_term ($sm_mk_binary " << retWidth << " " << retNum << "))";
  addLitSym(sym, args, Kind::ANY, ssr.str());
}

void ModelSmt::addLitSym(const std::string& sym,
                         const std::vector<Kind>& args,
                         Kind ret,
                         const std::string& retTerm)
{
  d_symLitReduce[sym] =
      std::tuple<std::vector<Kind>, Kind, std::string>(args, ret, retTerm);
}

void ModelSmt::addTermReduceSym(const std::string& sym,
                                const std::vector<Kind>& args,
                                const std::string& retTerm)
{
  std::cout << "(echo \"trim-defs-cmd (depends " << sym << " " << retTerm
            << ")\")" << std::endl;
  std::stringstream ssret;
  ssret << "($smtx_model_eval " << retTerm << ")";
  addReduceSym(sym, args, ssret.str());
}

void ModelSmt::addReduceSym(const std::string& sym,
                            const std::vector<Kind>& args,
                            const std::string& retTerm)
{
  d_symReduce[sym] = std::pair<std::vector<Kind>, std::string>(args, retTerm);
}

void ModelSmt::addRecReduceSym(const std::string& sym,
                               const std::vector<Kind>& args,
                               const std::string& retTerm)
{
  std::stringstream ss;
  std::stringstream ssend;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    ss << "(eo::define ((e" << i << " ($smtx_model_eval x" << i << "))) ";
    ssend << ")";
  }
  ss << retTerm << ssend.str();
  addReduceSym(sym, args, ss.str());
}

void ModelSmt::bind(const std::string& name, const Expr& e)
{
  if (e.getKind() != Kind::CONST)
  {
    return;
  }
  // internal declarations are ignored
  if (name.compare(0, 1, "$") == 0 || name.compare(0, 2, "@@") == 0)
  {
    return;
  }
  d_declSeen.emplace_back(name, e);
}

void ModelSmt::finalizeDecl(const std::string& name, const Expr& e)
{
  Attr attr =
      e.isNull() ? Attr::NONE : d_state.getConstructorKind(e.getValue());
  std::map<std::string,
           std::tuple<std::vector<Kind>, std::string, std::string>>::iterator
      itt = d_symTypes.find(name);
  if (itt != d_symTypes.end())
  {
    printType(name,
              std::get<0>(itt->second),
              std::get<1>(itt->second),
              std::get<2>(itt->second));
    return;
  }
  std::map<std::string, std::vector<Kind>>::iterator ith =
      d_symHardCode.find(name);
  if (ith != d_symHardCode.end())
  {
    printModelEvalCall(name, ith->second, attr);
    return;
  }
  // maybe a constant fold symbol
  std::map<std::string, std::pair<std::vector<Kind>, Kind>>::iterator it =
      d_symConstFold.find(name);
  if (it != d_symConstFold.end())
  {
    printModelEvalCall(name, it->second.first, attr);
    printConstFold(name, it->second.first, it->second.second);
    return;
  }
  std::map<std::string,
           std::tuple<std::vector<Kind>, Kind, std::string>>::iterator its =
      d_symLitReduce.find(name);
  if (its != d_symLitReduce.end())
  {
    std::vector<Kind>& args = std::get<0>(its->second);
    printModelEvalCall(name, args, attr);
    printLitReduce(
        name, args, std::get<1>(its->second), std::get<2>(its->second));
    return;
  }
  std::map<std::string, std::pair<std::vector<Kind>, std::string>>::iterator
      itst = d_symReduce.find(name);
  if (itst != d_symReduce.end())
  {
    printModelEvalCallBase(name, itst->second.first, itst->second.second, attr);
    return;
  }
  if (d_symIgnore.find(name) != d_symIgnore.end())
  {
    // intentionally ignored
    return;
  }
  // This assertion is critical for soundness: if we do not know how to
  // interpret the symbol, we cannot claim this verification condition
  // accurately models SMT-LIB semantics.
  EO_FATAL() << "ERROR: no model semantics found for " << name;
  Assert(false) << "No model semantics found for " << name;
}

void ModelSmt::printType(const std::string& name,
                         const std::vector<Kind>& args,
                         const std::string& cpat,
                         const std::string& cret)
{
  std::map<std::string, std::vector<std::string>>::iterator itc =
      d_typeCase.find(name);
  if (itc != d_typeCase.end())
  {
    // first print the special cases, e.g. String for Seq
    for (const std::string& cs : itc->second)
    {
      finalizeDecl(cs, d_null);
    }
  }
  d_constTypeof << "  (($smtx_typeof_const ";
  d_isInput << "  (($smtx_is_input ($eo_smt_term ($sm_Const ";
  if (args.empty())
  {
    d_constTypeof << name << " ";
    d_isInput << name << " ";
  }
  else
  {
    d_constTypeof << "(" << name;
    d_isInput << "(" << name;
    for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
    {
      d_constTypeof << " x" << i;
      d_isInput << " x" << i;
    }
    d_constTypeof << ") ";
    d_isInput << ") ";
  }
  d_constTypeof << cpat << ") " << cret << ")" << std::endl;
  d_isInput << cpat << "))) true)" << std::endl;
}

void ModelSmt::printModelEvalCallBase(const std::string& name,
                                      const std::vector<Kind>& args,
                                      const std::string& ret,
                                      Attr attr)
{
  d_eval << "  (($smtx_model_eval ";
  if (args.empty())
  {
    d_eval << name << ") " << ret << ")" << std::endl;
    return;
  }
  if (attr == Attr::AMB)
  {
    d_eval << "(as " << name;
  }
  else
  {
    d_eval << "(" << name;
  }
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    d_eval << " x" << i;
  }
  d_eval << ")) " << ret << ")" << std::endl;
}

void ModelSmt::printModelEvalCall(const std::string& name,
                                  const std::vector<Kind>& args,
                                  Attr attr)
{
  std::stringstream callArgs;
  callArgs << "($smtx_model_eval_" << name;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    callArgs << " ($smtx_model_eval x" << i << ")";
  }
  callArgs << ")";
  printModelEvalCallBase(name, args, callArgs.str(), attr);
}

void ModelSmt::printTermInternal(Kind k,
                                 const std::string& term,
                                 std::ostream& os)
{
  if (d_kindToEoPrefix.find(k) != d_kindToEoPrefix.end())
  {
    os << "($vsm_term ($sm_mk_" << d_kindToEoPrefix[k] << " " << term << "))";
  }
  else if (k == Kind::EVAL_TO_STRING)
  {
    os << "($vsm_re " << term << ")";
  }
  else
  {
    os << term;
  }
}

void ModelSmt::printConstFold(const std::string& name,
                              const std::vector<Kind>& args,
                              Kind kret)
{
  bool isOverloadArith = (args.size() > 0 && args[0] == Kind::PARAM);
  std::vector<Kind> argSchemas;
  if (isOverloadArith)
  {
    // will print conditions in two ways
    argSchemas.push_back(Kind::NUMERAL);
    argSchemas.push_back(Kind::RATIONAL);
  }
  else
  {
    argSchemas.push_back(Kind::NONE);
  }
  std::stringstream progName;
  progName << "$smtx_model_eval_" << name;
  std::stringstream progCases;
  std::stringstream progParams;
  size_t paramCount = 0;
  for (Kind kas : argSchemas)
  {
    // instantiate the arguments for the current schema and prepare the
    // argument list for the return term.
    std::vector<Kind> instArgs;
    std::stringstream retArgs;
    size_t tmpParamCount = paramCount;
    for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
    {
      Kind ka = args[i - 1];
      instArgs.push_back(ka == Kind::PARAM ? kas : ka);
      tmpParamCount++;
      retArgs << " x" << tmpParamCount;
    }
    // print the return term
    Kind kr = kret == Kind::PARAM ? kas : kret;
    std::stringstream ssret;
    ssret << "($smt_apply_" << args.size() << " \"";
    std::map<std::string, std::string>::iterator ito =
        d_overloadRevert.find(name);
    if (ito != d_overloadRevert.end())
    {
      // e.g. in spite of having name $eoo_-.2, we use "-" as the invocation.
      ssret << ito->second;
    }
    else
    {
      ssret << name;
    }
    ssret << "\"" << retArgs.str() << ")";
    // print the term with the right type
    std::stringstream fssret;
    printTermInternal(kr, ssret.str(), fssret);
    // then print it on cases
    printAuxProgramCase(progName.str(),
                        instArgs,
                        fssret.str(),
                        paramCount,
                        progCases,
                        progParams);
  }
  printAuxProgram(progName.str(), args, progCases, progParams);
}

void ModelSmt::printAuxProgram(const std::string& name,
                               const std::vector<Kind>& args,
                               std::stringstream& progCases,
                               std::stringstream& progParams)
{
  std::stringstream progSig;
  progSig << "(";
  // make the default case as well
  progCases << "  ((" << name;
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    if (i > 0)
    {
      progSig << " ";
    }
    progSig << "$smt_Value";
    progCases << " t" << (i + 1);
    progParams << " (t" << (i + 1) << " $smt_Value)";
  }
  progSig << ") $smt_Value";
  progCases << ") $vsm_not_value)" << std::endl;
  d_modelEvalProgs << "(program " << name << std::endl;
  d_modelEvalProgs << "  (" << progParams.str() << ")" << std::endl;
  d_modelEvalProgs << "  :signature " << progSig.str() << std::endl;
  d_modelEvalProgs << "  (" << std::endl;
  d_modelEvalProgs << progCases.str();
  d_modelEvalProgs << "  )" << std::endl << ")" << std::endl;
}

void ModelSmt::printAuxProgramCase(const std::string& name,
                                   const std::vector<Kind>& args,
                                   const std::string& ret,
                                   size_t& paramCount,
                                   std::ostream& progCases,
                                   std::ostream& progParams)
{
  progCases << "  ((" << name;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    Kind ka = args[i - 1];
    paramCount++;
    if (paramCount > 1)
    {
      progParams << " ";
    }
    if (ka == Kind::EVAL_TO_STRING)
    {
      progCases << "($vsm_re x" << paramCount << ")";
      progParams << "(x" << paramCount << " $smt_builtin_RegLan)";
      continue;
    }
    progCases << " ($vsm_term";
    if (ka == Kind::BINARY)
    {
      progCases << " ($sm_binary x" << paramCount << " x" << (paramCount + 1)
                << "))";
      progParams << "(x" << paramCount << " $smt_builtin_Int)";
      progParams << " (x" << (paramCount + 1) << " $smt_builtin_Int)";
      paramCount++;
      continue;
    }
    Assert(d_kindToEoPrefix.find(ka) != d_kindToEoPrefix.end());
    progCases << " ($sm_mk_" << d_kindToEoPrefix[ka] << " x" << paramCount
              << "))";
    progParams << "(x" << paramCount << " $smt_builtin_" << d_kindToType[ka]
               << ")";
  }
  progCases << ") ";
  progCases << ret << ")" << std::endl;
}

void ModelSmt::printLitReduce(const std::string& name,
                              const std::vector<Kind>& args,
                              Kind ret,
                              const std::string& reduce)
{
  std::stringstream progName;
  std::stringstream progCases;
  std::stringstream progParams;
  size_t paramCount = 0;
  progName << "$smtx_model_eval_" << name;
  // print the term with the right type
  std::stringstream ssret;
  printTermInternal(ret, reduce, ssret);
  // then print it on cases
  printAuxProgramCase(
      progName.str(), args, ssret.str(), paramCount, progCases, progParams);
  printAuxProgram(progName.str(), args, progCases, progParams);
}

void ModelSmt::finalize()
{
  for (std::pair<std::string, Expr>& d : d_declSeen)
  {
    finalizeDecl(d.first, d.second);
  }
  auto replace = [](std::string& txt,
                    const std::string& tag,
                    const std::string& replacement) {
    auto pos = txt.find(tag);
    if (pos != std::string::npos)
    {
      txt.replace(pos, tag.length(), replacement);
    }
  };

  // note that the deep embedding is *not* re-incorporated into
  // the final input to smt-meta.

  // now, go back and compile *.eo for the proof rules
  std::stringstream ssis;
  ssis << s_plugin_path << "plugins/model_smt/model_smt.eo";
  std::ifstream ins(ssis.str());
  std::ostringstream sss;
  sss << ins.rdbuf();
  std::string finalSmt = sss.str();
  replace(finalSmt, "$SMT_IS_VALUE_CASES$", d_typeIsValue.str());
  replace(finalSmt, "$SMT_CONST_TYPE_OF_CASES$", d_constTypeof.str());
  replace(finalSmt, "$SMT_IS_INPUT_CASES$", d_isInput.str());
  // plug in the evaluation cases handled by this plugin
  replace(finalSmt, "$SMT_EVAL_CASES$", d_eval.str());
  replace(finalSmt, "$SMT_EVAL_PROGS$", d_modelEvalProgs.str());

  std::stringstream ssoe;
  ssoe << s_plugin_path << "plugins/model_smt/model_smt_gen.eo";
  // std::cout << "Write smt-model    " << finalSmt.str() << std::endl;
  std::ofstream oute(ssoe.str());
  oute << finalSmt;
}

}  // namespace ethos
