/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "model_smt_new.h"

#include <fstream>
#include <sstream>
#include <string>

#include "state.h"

namespace ethos {
namespace mnew {

std::string sApply(const std::string& op, const std::string& args)
{
  std::stringstream ss;
  if (args.empty())
  {
    ss << op;
  }
  else
  {
    // assumes args starts with space
    ss << "(" << op << args << ")";
  }
  return ss.str();
}

std::string smtZEq(const std::string& c1, const std::string& c2)
{
  std::stringstream ss;
  ss << "($smt_builtin_z_= " << c1 << " " << c2 << ")";
  return ss.str();
}
std::string smtZAdd(const std::string& c1, const std::string& c2)
{
  std::stringstream ss;
  ss << "($smt_builtin_z_+ " << c1 << " " << c2 << ")";
  return ss.str();
}
std::string smtZSub(const std::string& c1, const std::string& c2)
{
  std::stringstream ss;
  ss << "($smt_builtin_z_- " << c1 << " " << c2 << ")";
  return ss.str();
}
std::string smtZLeq(const std::string& c1, const std::string& c2)
{
  std::stringstream ss;
  ss << "($smt_builtin_z_<= " << c1 << " " << c2 << ")";
  return ss.str();
}
std::string smtZLt(const std::string& c1, const std::string& c2)
{
  std::stringstream ss;
  ss << "($smt_builtin_z_< " << c1 << " " << c2 << ")";
  return ss.str();
}
std::string smtQEq(const std::string& c1, const std::string& c2)
{
  std::stringstream ss;
  ss << "($smt_builtin_q_= " << c1 << " " << c2 << ")";
  return ss.str();
}
std::string smtValueEq(const std::string& c1, const std::string& c2)
{
  std::stringstream ss;
  ss << "($smt_builtin_veq " << c1 << " " << c2 << ")";
  return ss.str();
}
std::string smtNot(const std::string& c1)
{
  std::stringstream ss;
  ss << "($smt_builtin_not " << c1 << ")";
  return ss.str();
}
std::string smtApp(const std::string& app,
                   const std::string& c1,
                   const std::string& c2)
{
  std::stringstream ss;
  ss << "($smt_apply_2 \"" << app << "\" " << c1 << " " << c2 << ")";
  return ss.str();
}
std::string smtIte(const std::string& guard,
                   const std::string& t,
                   const std::string& e)
{
  std::stringstream ss;
  ss << "($smt_builtin_ite " << guard << " " << t << " " << e << ")";
  return ss.str();
}
std::string smtGuard(const std::string& guard, const std::string& val)
{
  return smtIte(guard, val, "$vsm_not_value");
}

/**
 * Makes s and t be in the context of the return term, used to specify the
 * return term of binary operations on bitvectors.
 */
std::string ModelSmtNew::smtBinaryBinReturn(const std::string& term)
{
  std::stringstream ss;
  ss << "(eo::define ((s ($sm_binary x1 x2))) ";
  ss << "(eo::define ((t ($sm_binary x3 x4))) ";
  ss << term << "))";
  return ss.str();
}

std::string ModelSmtNew::smtToSmtEmbed(const std::string& s)
{
  std::string out;
  out.reserve(s.size());  // baseline; may grow
  for (size_t i = 0; i < s.size(); ++i)
  {
    if (s[i] == '(')
    {
      // don't replace if next char is '(' or '$'
      if (i + 1 < s.size() && (s[i + 1] == '(' || s[i + 1] == '$'))
      {
        out.push_back('(');
      }
      else
      {
        out += "($sm_";
      }
    }
    else
    {
      out.push_back(s[i]);
    }
  }
  // literal values used in reduction specifications
  out = replace_all(out, " 0/1", " $sm_q_zero");
  out = replace_all(out, " 0", " $sm_z_zero");
  out = replace_all(out, " 1", " $sm_z_one");
  // note that nullary SMT-LIB symbols (e.g. re.none) are not handled
  return out;
}

std::string ModelSmtNew::smtEval(const std::string& s)
{
  std::stringstream ss;
  ss << "($smtx_model_eval " << smtToSmtEmbed(s) << ")";
  return ss.str();
}
std::string eoDefine(const std::string& x,
                     const std::string& t,
                     const std::string& ret)
{
  std::stringstream ss;
  ss << "(eo::define ((" << x << " " << t << ")) " << ret << ")";
  return ss.str();
}

ModelSmtNew::ModelSmtNew(State& s) : StdPlugin(s)
{
  // This constructor is the main source of the specification of the semantics
  // of all possible operators defined in a Eunoia signature. For example, if
  // the user defines a symbol named "and", we assume its semantics is given
  // by invoking the SMT-LIB symbol named "and".
  // At a high level, each operator is either given a semantics which:
  // (1) reduces the semantics to another term,
  // (2) invokes an SMT-LIB operator (usually of the same name),
  // (3) invokes a custom procedure as defined in model_smt.eo.
  Kind kBool = Kind::BOOLEAN;
  Kind kInt = Kind::NUMERAL;
  Kind kReal = Kind::RATIONAL;
  Kind kString = Kind::STRING;
  Kind kBitVec = Kind::BINARY;
  Kind kT = Kind::PARAM;
  Kind kType = Kind::TYPE;
  Kind kRegLan = Kind::EVAL_TO_STRING;
  Kind kList = Kind::EVAL_CONS;
  Kind kVarList = Kind::VARIABLE;
  d_kindToEoPrefix[kBool] = "bool";
  d_kindToEoPrefix[kInt] = "numeral";
  d_kindToEoPrefix[kReal] = "rational";
  d_kindToEoPrefix[kString] = "string";
  d_kindToEoPrefix[kBitVec] = "binary";
  d_kindToType[kBool] = "Bool";
  d_kindToType[kInt] = "Int";
  d_kindToType[kReal] = "Real";
  d_kindToType[kString] = "String";
  d_kindToType[kBitVec] = "Binary";
  d_kindToType[kRegLan] = "RegLan";
  // All SMT-LIB symbols require having their semantics defined here.
  // Note that we model *SMT-LIB* not *CPC* here.
  // builtin
  // immediately include Bool, as it will not be defined
  // printDecl("Bool", {}, Kind::TYPE);
  addHardCodeSym("=", {kT, kT});
  addHardCodeSym("ite", {kBool, kT, kT});
  addTermReduceSym("distinct", {kT, kT}, "(not (= x1 x2))");
  // Booleans
  addConstFoldSym("and", {kBool, kBool}, kBool);
  addConstFoldSym("or", {kBool, kBool}, kBool);
  // addConstFoldSym("xor", {kBool, kBool}, kBool);
  // addConstFoldSym("=>", {kBool, kBool}, kBool);
  addTermReduceSym("xor", {kBool, kBool}, "(not (= x1 x2))");
  addTermReduceSym("=>", {kBool, kBool}, "(or (not x1) x2)");
  addConstFoldSym("not", {kBool}, kBool);
  // arithmetic
  addTypeSym("Int", {});
  addTypeSym("Real", {});
  // use kT to stand for either Int or Real arithmetic (not mixed)
  addConstFoldSym("+", {kT, kT}, kT);
  addConstFoldSym("-", {kT, kT}, kT);
  addConstFoldSym("*", {kT, kT}, kT);
  // we expect "-" to be overloaded, we look for its desugared name and map it
  // back
  addConstFoldSym("$eoo_-.2", {kT}, kT);
  d_overloadRevert["$eoo_-.2"] = "-";
  // addConstFoldSym("abs", {kInt}, kInt);
  addTermReduceSym("abs", {kInt}, "(ite (< x1 0) (- 0 x1) x1)");
  // addConstFoldSym(">=", {kT, kT}, kBool);
  addTermReduceSym(">=", {kT, kT}, "(<= x2 x1)");
  addConstFoldSym("<=", {kT, kT}, kBool);
  // addConstFoldSym(">", {kT, kT}, kBool);
  addTermReduceSym(">", {kT, kT}, "(< x2 x1)");
  addConstFoldSym("<", {kT, kT}, kBool);
  // addConstFoldSym("is_int", {kReal}, kBool);
  addTermReduceSym("is_int", {kReal}, "(= (to_real (to_int x1)) x1)");
  addConstFoldSym("/", {kReal, kReal}, kReal);
  d_evalGuard["/"] = smtNot(smtQEq("x2", "$smt_builtin_q_zero"));
  addConstFoldSym("div", {kInt, kInt}, kInt);
  d_evalGuard["div"] = smtNot(smtZEq("x2", "$smt_builtin_z_zero"));
  addConstFoldSym("mod", {kInt, kInt}, kInt);
  d_evalGuard["mod"] = smtNot(smtZEq("x2", "$smt_builtin_z_zero"));
  addConstFoldSym("to_int", {kReal}, kInt);
  addConstFoldSym("to_real", {kInt}, kReal);
  addTermReduceSym("divisible", {kInt, kInt}, "(= (mod x2 x1) 0)");
  // arrays
  addTypeSym("Array", {kType, kType});
  addRecReduceSym("select", {kT, kT}, "($smtx_map_select e1 e2)");
  addRecReduceSym("store", {kT, kT, kT}, "($smtx_map_store e1 e2 e3)");
  // array constants??
  // FIXME: needs to embed type
  // addReduceSym(
  //   "const", {kT, kT}, "($vsm_map ($msm_default ($smtx_model_eval x2)))");
  // strings
  addTypeSym("Seq", {kType});
  addTypeSym("Char", {});
  addTypeSym("RegLan", {});
  addConstFoldSym("str.++", {kString, kString}, kString);
  addConstFoldSym("str.len", {kString}, kInt);
  addConstFoldSym("str.substr", {kString, kInt, kInt}, kString);
  // addConstFoldSym("str.at", {kString, kInt}, kString);
  addTermReduceSym("str.at", {kString, kInt}, "(str.substr x1 x2 1)");
  addConstFoldSym("str.indexof", {kString, kString, kInt}, kInt);
  addConstFoldSym("str.replace", {kString, kString, kString}, kString);
  addConstFoldSym("str.replace_all", {kString, kString, kString}, kString);
  addConstFoldSym("str.from_code", {kInt}, kString);
  addConstFoldSym("str.to_code", {kString}, kInt);
  addConstFoldSym("str.from_int", {kInt}, kString);
  addConstFoldSym("str.to_int", {kString}, kInt);
  addConstFoldSym("str.is_digit", {kString}, kBool);  // TODO: term reduce
  addConstFoldSym("str.contains", {kString, kString}, kBool);
  // addConstFoldSym("str.suffixof", {kString, kString}, kBool); // TODO: term
  // reduce
  addTermReduceSym(
      "str.suffixof",
      {kString, kString},
      "(= x1 (str.substr x2 (- (str.len x2) (str.len x1)) (str.len x1)))");
  // addConstFoldSym("str.prefixof", {kString, kString}, kBool);
  addTermReduceSym("str.prefixof",
                   {kString, kString},
                   "(= x1 (str.substr x2 0 (str.len x1)))");
  // addConstFoldSym("str.<=", {kString, kString}, kBool);
  addTermReduceSym(
      "str.<=", {kString, kString}, "(or (= x1 x2) (str.< x1 x2))");
  addConstFoldSym("str.<", {kString, kString}, kBool);
  // regular expressions
  addReduceSym("re.allchar", {}, "($vsm_re ($smt_apply_0 \"re.allchar\"))");
  addReduceSym("re.none", {}, "($vsm_re ($smt_apply_0 \"re.none\"))");
  addReduceSym("re.all", {}, "($vsm_re ($smt_apply_0 \"re.all\"))");
  addConstFoldSym("str.to_re", {kString}, kRegLan);
  addConstFoldSym("re.*", {kRegLan}, kRegLan);
  addConstFoldSym("re.+", {kRegLan}, kRegLan);
  addConstFoldSym("re.opt", {kRegLan}, kRegLan);  // TODO: term reduce
  addConstFoldSym("re.comp", {kRegLan}, kRegLan);
  addConstFoldSym("re.++", {kRegLan, kRegLan}, kRegLan);
  addConstFoldSym("re.inter", {kRegLan, kRegLan}, kRegLan);
  addConstFoldSym("re.union", {kRegLan, kRegLan}, kRegLan);
  addConstFoldSym("re.diff", {kRegLan, kRegLan}, kRegLan);  // TODO: term reduce
  addConstFoldSym("re.range", {kString, kString}, kRegLan);
  std::stringstream ssReRepeatRet;
  ssReRepeatRet << "(ite (= x1 0)";
  ssReRepeatRet << " (str.to_re $sm_string_empty)";
  ssReRepeatRet << " (re.++ (re.^ (- x1 1) x2) x2))";
  addReduceSym("re.^",
               {kInt, kRegLan},
               smtGuard(smtValueEq(smtEval("(>= x1 0)"), "$vsm_true"),
                        smtEval(ssReRepeatRet.str())));
  std::stringstream ssReLoopRet;
  ssReLoopRet << "(ite (> x1 x2)";
  ssReLoopRet << " $sm_re.none (ite (= x1 x2)";
  ssReLoopRet << " (re.^ x1 x3)";
  ssReLoopRet << " (re.union (re.loop x1 (- x2 1) x3) (re.^ x2 x3))))";
  addReduceSym(
      "re.loop",
      {kInt, kInt, kRegLan},
      smtGuard(smtValueEq(smtEval("(and (>= x1 0) (>= x2 0))"), "$vsm_true"),
               smtEval(ssReLoopRet.str())));
  // RE operators
  addConstFoldSym("str.in_re", {kString, kRegLan}, kBool);
  addConstFoldSym("str.indexof_re", {kString, kRegLan, kInt}, kInt);
  addConstFoldSym("str.replace_re", {kString, kRegLan, kString}, kString);
  addConstFoldSym("str.replace_re_all", {kString, kRegLan, kString}, kString);
  // bitvectors
  addTypeSym("BitVec", {kInt});
  // the following are return terms of aux program cases of the form:
  // (($smtx_model_eval_f
  //    ($vsm_term ($eo_binary x1 x2)) ($vsm_term ($eo_binary x3 x4)))
  //    <return>)
  // where x1, x3 denote bitwidths and x2, x4 denote values.
  addLitBinSym("bvadd", {kBitVec, kBitVec}, "x1", smtZAdd("x2", "x4"));
  addLitBinSym("bvmul", {kBitVec, kBitVec}, "x1", "($smt_builtin_z_* x2 x4)");
  addLitBinSym("bvudiv",
               {kBitVec, kBitVec},
               "x1",
               smtIte(smtZEq("x3", "$smt_builtin_z_zero"),
                      "($smtx_binary_max x1)",
                      "($smt_builtin_div x2 x4)"));
  addLitBinSym("bvurem",
               {kBitVec, kBitVec},
               "x1",
               smtIte(smtZEq("x3", "$smt_builtin_z_zero"),
                      "x2",
                      "($smt_builtin_mod x2 x4)"));
  addLitBinSym(
      "bvand", {kBitVec, kBitVec}, "x1", "($smtx_binary_and x1 x2 x4)");
  addLitBinSym("bvor", {kBitVec, kBitVec}, "x1", "($smtx_binary_or x1 x2 x4)");
  addLitBinSym(
      "bvxor", {kBitVec, kBitVec}, "x1", "($smtx_binary_xor x1 x2 x4)");
  addLitBinSym("bvnot", {kBitVec}, "x1", "($smtx_binary_not x1 x2)");
  addLitBinSym("bvneg", {kBitVec}, "x1", "($smt_builtin_z_neg x2)");
  addLitBinSym("bvshl",
               {kBitVec, kBitVec},
               "x1",
               "($smt_builtin_z_* x2 ($smtx_pow2 x4))");
  addLitBinSym("bvlshr",
               {kBitVec, kBitVec},
               "x1",
               "($smt_builtin_div x2 ($smtx_pow2 x4))");
  std::stringstream ssExtractCond;
  ssExtractCond << smtApp(
      "and",
      smtZLeq("x2", "x1"),
      smtApp("and", smtZLeq("$smt_builtin_z_zero", "x2"), smtZLt("x1", "x3")));
  std::stringstream ssExtractRet;
  ssExtractRet << "($vsm_binary_mod_w ";
  ssExtractRet << smtZSub(smtZAdd("x1", "$smt_builtin_z_one"), "x2");
  ssExtractRet << " ($smtx_binary_extract x3 x4 x1 x2))";
  addLitSym("extract",
            {kInt, kInt, kBitVec},
            kT,
            smtGuard(ssExtractCond.str(), ssExtractRet.str()));
  addLitBinSym("concat",
               {kBitVec, kBitVec},
               smtZAdd("x1", "x3"),
               "($smtx_binary_concat x1 x2 x3 x4)",
               false);
  std::stringstream ssUgtRet;
  ssUgtRet << "($vsm_bool " << smtZLt("x4", "x2") << ")";
  addLitSym("bvugt",
            {kBitVec, kBitVec},
            kT,
            smtGuard(smtZEq("x1", "x3"), ssUgtRet.str()));
  // the following operators require a mix of literal evaluation and term
  // reduction
  std::stringstream ssSgtRet;
  ssSgtRet << "(eo::define ((msb_s ($sm_bool ($smtx_msb x1 x2)))) ";
  ssSgtRet << "(eo::define ((msb_t ($sm_bool ($smtx_msb x3 x4)))) ";
  ssSgtRet << smtEval(
      "(or (and (not msb_s) msb_t) (and (= msb_s msb_t) (bvugt s t)))");
  ssSgtRet << "))";
  addLitSym(
      "bvsgt", {kBitVec, kBitVec}, kT, smtBinaryBinReturn(ssSgtRet.str()));
  addLitSym("zero_extend",
            {kInt, kBitVec},
            kT,
            smtGuard(smtZLeq("$smt_builtin_z_zero", "x1"),
                     "($vsm_binary ($smt_builtin_z_+ x1 x2) x3)"));
  std::stringstream ssSExtRet;
  ssSExtRet << "(eo::define ((wm1 " << smtToSmtEmbed("(- ($sm_numeral x2) 1)")
            << ")) ";
  ssSExtRet << "(eo::define ((t ($sm_binary x2 x3))) ";
  ssSExtRet << smtEval(
      "(concat (repeat ($sm_numeral x1) (extract wm1 wm1 t)) t)");
  ssSExtRet << "))";
  addLitSym("sign_extend",
            {kInt, kBitVec},
            kT,
            smtGuard(smtZLeq("$smt_builtin_z_zero", "x1"),
                     smtIte(smtZEq("x1", "$smt_builtin_z_zero"),
                            "($vsm_binary x2 x3)",
                            ssSExtRet.str())));
  std::stringstream ssAshrRet;
  ssAshrRet << "(eo::define ((wm1 " << smtToSmtEmbed("(- ($sm_numeral x1) 1)")
            << ")) ";
  ssAshrRet << smtEval(
      "(ite (= (extract wm1 wm1 s) $sm_binary_bit_false) (bvlshr s t) (bvnot "
      "(bvlshr (bvnot s) t)))");
  ssAshrRet << ")";
  addLitSym(
      "bvashr", {kBitVec, kBitVec}, kT, smtBinaryBinReturn(ssAshrRet.str()));
  std::stringstream ssRLeftRet;
  ssRLeftRet << "(eo::define ((wm1 " << smtToSmtEmbed("(- ($sm_numeral x2) 1)")
             << ")) ";
  ssRLeftRet << "(eo::define ((t ($sm_binary x2 x3))) ";
  ssRLeftRet << smtEval(
      "(rotate_left (- ($sm_numeral x1) 1) (concat (extract (- wm1 1) 0 t) "
      "(extract wm1 wm1 t)))");
  ssRLeftRet << "))";
  addLitSym("rotate_left",
            {kInt, kBitVec},
            kT,
            smtGuard(smtZLeq("$smt_builtin_z_zero", "x1"),
                     smtIte(smtZEq("x1", "$smt_builtin_z_zero"),
                            "($vsm_binary x2 x3)",
                            ssRLeftRet.str())));
  std::stringstream ssRRightRet;
  ssRRightRet << "(eo::define ((wm1 " << smtToSmtEmbed("(- ($sm_numeral x2) 1)")
              << ")) ";
  ssRRightRet << smtEval(
      "(rotate_right (- ($sm_numeral x1) 1) (concat (extract 0 0 ($sm_binary "
      "x2 x3)) (extract wm1 1 ($sm_binary x2 x3))))");
  ssRRightRet << ")";
  addLitSym("rotate_right",
            {kInt, kBitVec},
            kT,
            smtGuard(smtZLeq("$smt_builtin_z_zero", "x1"),
                     smtIte(smtZEq("x1", "$smt_builtin_z_zero"),
                            "($vsm_binary x2 x3)",
                            ssRRightRet.str())));
  std::stringstream ssRepeatRet;
  ssRepeatRet << "(concat";
  ssRepeatRet << " (repeat (- ($sm_numeral x1) 1) ($sm_binary x2 x3))";
  ssRepeatRet << " ($sm_binary x2 x3))";
  addLitSym("repeat",
            {kInt, kBitVec},
            kT,
            smtGuard(smtZLeq("$smt_builtin_z_one", "x1"),
                     smtIte(smtZEq("x1", "$smt_builtin_z_one"),
                            "($vsm_binary x2 x3)",
                            smtEval(ssRepeatRet.str()))));
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
  // sdiv, srem, smod
  for (size_t i = 0; i < 3; i++)
  {
    std::stringstream ssRet;
    std::stringstream ssRetEnd;
    ssRet << "(eo::define ((msb_s ($sm_bool ($smtx_msb x1 x2)))) ";
    ssRet << "(eo::define ((msb_t ($sm_bool ($smtx_msb x3 x4)))) ";
    ssRetEnd << "))";
    std::string op;
    std::stringstream ssTermRet;
    if (i == 0)
    {
      op = "bvsdiv";
      ssTermRet << "(ite (and (not msb_s) (not msb_t)) (bvudiv s t)";
      ssTermRet << " (ite (and msb_s (not msb_t)) (bvneg (bvudiv (bvneg s) t))";
      ssTermRet << " (ite (and (not msb_s) msb_t) (bvneg (bvudiv s (bvneg t)))";
      ssTermRet << " (bvudiv (bvneg s) (bvneg t)))))";
    }
    else if (i == 1)
    {
      op = "bvsrem";
      ssTermRet << "(ite (and (not msb_s) (not msb_t)) (bvurem s t)";
      ssTermRet << " (ite (and msb_s (not msb_t)) (bvneg (bvurem (bvneg s) t))";
      ssTermRet << " (ite (and (not msb_s) msb_t) (bvneg (bvurem s (bvneg t)))";
      ssTermRet << " (bvurem (bvneg s) (bvneg t)))))";
    }
    else
    {
      op = "bvsmod";
      ssRet << "(eo::define ((abs_s "
            << smtToSmtEmbed("(ite msb_s s (bvneg s))") << ")) ";
      ssRet << "(eo::define ((abs_t "
            << smtToSmtEmbed("(ite msb_t t (bvneg t))") << ")) ";
      ssRet << "(eo::define ((u " << smtToSmtEmbed("(bvurem abs_s abs_t")
            << "))) ";
      ssRetEnd << ")))";
      ssTermRet << "(ite (= u ($sm_binary x1 $smt_builtin_z_zero)) u";
      ssTermRet << " (ite (and (not msb_s) (not msb_t)) u";
      ssTermRet << " (ite (and msb_s (not msb_t)) (bvadd (bvneg u) t)";
      ssTermRet << " (ite (and (not msb_s) msb_t) (bvadd u t)";
      ssTermRet << " (bvneg u)))))";
    }
    ssRet << smtEval(ssTermRet.str()) << ssRetEnd.str();
    addLitSym(op, {kBitVec, kBitVec}, kT, smtBinaryBinReturn(ssRet.str()));
  }
  // overflow predicates
  addLitSym("bvuaddo",
            {kBitVec, kBitVec},
            kBool,
            smtZLeq("($smtx_pow2 x1)", smtZAdd("x2", "x4")));
  addLitSym("bvumulo",
            {kBitVec, kBitVec},
            kBool,
            smtZLeq("($smtx_pow2 x1)", "($smt_builtin_z_* x2 x4)"));
  for (size_t i = 0; i < 2; i++)
  {
    std::string intOp = i == 0 ? "+" : "*";
    std::string bvOp = i == 0 ? "bvsaddo" : "bvsmulo";
    std::stringstream ssRet;
    ssRet << "(eo::define ((sret ($smt_apply_2 \"" << intOp << "\"";
    ssRet << " ($smtx_binary_uts x1 x2) ($smtx_binary_uts x3 x4)))) ";
    ssRet << "(eo::define ((p2wm1 ($smtx_pow2 ($smt_apply_2 \"-\" x1 "
             "$smt_builtin_z_one)))) ";
    ssRet << " ($smt_builtin_or " << smtZLeq("p2wm1", "sret");
    ssRet << " " << smtZLt("sret", "($smt_builtin_z_neg p2wm1)");
    ssRet << ")))";
    addLitSym(bvOp, {kBitVec, kBitVec}, kBool, ssRet.str());
  }
  addLitSym("bvnego",
            {kBitVec},
            kBool,
            smtZEq("x2", "($smtx_pow2 ($smt_builtin_z_dec x1))"));
  addTermReduceSym("bvusubo", {kBitVec, kBitVec}, "(bvult x1 x2)");
  addLitSym("bvssubo",
            {kBitVec, kBitVec},
            kT,
            smtBinaryBinReturn(
                smtEval("(ite (bvnego t) (bvsge s ($sm_binary x1 "
                        "$smt_builtin_z_zero)) (bvsaddo s (bvneg t)))")));
  addLitSym(
      "bvsdivo",
      {kBitVec, kBitVec},
      kT,
      smtBinaryBinReturn(smtEval("(and (bvnego s) (= t (bvnot "
                                 "($sm_binary x1 $smt_builtin_z_zero))))")));
  // arith/BV conversions
  addLitSym("ubv_to_int", {kBitVec}, kInt, "x2");
  addLitSym("sbv_to_int", {kBitVec}, kInt, "($smtx_binary_uts x1 x2)");
  addLitSym(
      "int_to_bv", {kInt, kInt}, kT, "($smtx_model_eval ($sm_binary x1 x2))");
  // Quantifiers
  // one variable at a time, $sm_exists is hardcoded
  addEunoiaReduceSym("exists",
                     {kVarList, kT},
                     "($sm_apply ($sm_exists s ($eo_to_smt_type T)) "
                     "($eo_to_smt (exists x1 x2)))");
  d_specialCases["exists"].emplace_back("(exists $eo_List_nil x1)",
                                        "($eo_to_smt x1)");
  addEunoiaReduceSym(
      "forall", {kT, kBool}, "($eo_to_smt (not (exists x1 (not x2))))");

  //===========================================================================
  ///----- non standard extensions and skolems
  // builtin
  // one variable at a time, $sm_lambda is hardcoded
  addEunoiaReduceSym("lambda",
                     {kVarList, kT},
                     "($sm_apply ($sm_lambda s ($eo_to_smt_type T)) "
                     "($eo_to_smt (lambda x1 x2)))");
  d_specialCases["lambda"].emplace_back("(lambda $eo_List_nil x1)",
                                        "($eo_to_smt x1)");
  addEunoiaReduceSym("@purify", {kT}, "($eo_to_smt x1)");
  // arithmetic
  addTermReduceSym("/_total", {kT, kT}, "(ite (= x2 0/1) 0/1 (/ x1 x2))");
  addTermReduceSym("div_total", {kInt, kInt}, "(ite (= x2 0) 0 (div x1 x2))");
  addTermReduceSym("mod_total", {kInt, kInt}, "(ite (= x2 0) x1 (mod x1 x2))");
  addConstFoldSym("int.pow2", {kInt}, kInt);
  addConstFoldSym("int.log2", {kInt}, kInt);
  addEunoiaReduceSym("@int_div_by_zero", {kInt}, "($eo_to_smt (div x1 0))");
  addEunoiaReduceSym("@mod_by_zero", {kInt}, "($eo_to_smt (mod x1 0))");
  addEunoiaReduceSym("@div_by_zero", {kReal}, "($eo_to_smt (/ x1 0/1))");
  addTermReduceSym(
      "int.ispow2", {kInt}, "(and (>= x1 0) (= x1 (int.pow2 (int.log2 x1))))");
  // arrays
  addRecReduceSym("@array_deq_diff", {kT, kT}, "($smtx_map_diff e1 e2)");
  // strings
  addConstFoldSym("str.update", {kString, kInt, kString}, kString);
  addConstFoldSym("str.rev", {kString}, kString);
  addConstFoldSym("str.to_lower", {kString}, kString);
  addConstFoldSym("str.to_upper", {kString}, kString);
  addEunoiaReduceSym("@strings_itos_result",
                     {kInt, kInt},
                     "($eo_to_smt (str.from_int (mod x1 (^ 10 x2))))");
  addEunoiaReduceSym("@strings_stoi_result",
                     {kString, kInt},
                     "($eo_to_smt (str.to_int (str.substr x1 0 x2)))");
  addEunoiaReduceSym("@strings_stoi_non_digit",
                     {kString},
                     "($eo_to_smt (str.indexof_re x1 (re.comp (re.range "
                     "$sm_string_c0 $sm_string_c9)) 0))");
  // sequences
  addReduceSym("seq.empty", {kType}, "($smtx_empty_seq x1)");
  d_specialCases["seq.empty"].emplace_back(
      "(seq.empty (Seq Char))", "($sm_string $smt_builtin_str_empty)");
  addRecReduceSym("seq.unit", {kT}, "($smtx_seq_unit e1)");
  addRecReduceSym("seq.nth", {kT, kInt}, "($smtx_seq_nth e1 e2)");
  // sets
  // (Set T) is modelled as (Array T Bool).
  addTypeSym("Set", {kType});
  addReduceSym("set.empty", {kType}, "($smtx_empty_set x1)");
  addRecReduceSym("set.singleton", {kT}, "($smtx_set_singleton e1)");
  addRecReduceSym("set.inter", {kT, kT}, "($smtx_set_inter e1 e2)");
  addRecReduceSym("set.minus", {kT, kT}, "($smtx_set_minus e1 e2)");
  addRecReduceSym("set.union", {kT, kT}, "($smtx_set_union e1 e2)");
  addRecReduceSym("set.member", {kT, kT}, "($smtx_map_select e2 e1)");
  addTermReduceSym("set.subset", {kT, kT}, "(= (set.inter x1 x2) x1)");
  addRecReduceSym("@sets_deq_diff", {kT, kT}, "($smtx_map_diff e1 e2)");
  std::stringstream ssIsEmptyRet;
  ssIsEmptyRet << "($vsm_bool "
               << smtValueEq("e1", "($smtx_empty_set ($smtx_typeof_value e1))")
               << ")";
  addRecReduceSym("set.is_empty", {kT}, ssIsEmptyRet.str());
  addEunoiaReduceSym(
      "set.insert",
      {kList, kT},
      "($eo_to_smt (set.union (set.singleton x1) (set.insert x2 x3)))");
  d_specialCases["set.insert"].emplace_back("(set.insert $eo_List_nil x1)",
                                            "($eo_to_smt x1)");
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
  addLitSym("bvredor",
            {kBitVec},
            kT,
            smtEval("(bvnot (bvcomp ($sm_binary x1 x2) ($sm_binary x1 "
                    "$smt_builtin_z_zero)))"));
  addLitSym("bvredand",
            {kBitVec},
            kT,
            smtEval("(bvcomp ($sm_binary x1 x2) (bvnot ($sm_binary x1 "
                    "$smt_builtin_z_zero)))"));
  // utility guards for negative widths, which do not evaluate
  addLitSym("@bv", {kInt, kInt}, kT, "($vsm_mk_binary x2 x1)");
  addEunoiaReduceSym(
      "@bit", {kInt, kBitVec}, "($eo_to_smt (extract x1 x1 x2))");
  addEunoiaReduceSym("@from_bools",
                     {kBool, kBitVec},
                     "($eo_to_smt (concat (ite x1 #b1 #b0) x2))");
  // tuples
  // these allow Herbrand interpretations
  addTypeSym("Tuple", {kType, kType});
  addTypeSym("UnitTuple", {});
  d_symIgnore["Tuple"] = true;
  d_symIgnore["UnitTuple"] = true;
  // addReduceSym("tuple", {}, "($vsm_apply ($vsm_term tuple) $vsm_not_value)");
  // addReduceSym("tuple.unit", {}, "($vsm_term tuple.unit)");
  //  FIXME
  d_symIgnore["tuple"] = true;
  d_symIgnore["tuple.unit"] = true;

  // for alethe
  addTermReduceSym("@cl", {kT, kT}, "(or x1 x2)");
}

ModelSmtNew::~ModelSmtNew() {}

void ModelSmtNew::addTypeSym(const std::string& sym,
                             const std::vector<Kind>& args)
{
  d_symIgnore[sym] = true;
  d_symTypes[sym] = args;
}

void ModelSmtNew::addHardCodeSym(const std::string& sym,
                                 const std::vector<Kind>& args)
{
  d_symHardCode[sym] = args;
}

void ModelSmtNew::addConstFoldSym(const std::string& sym,
                                  const std::vector<Kind>& args,
                                  Kind ret)
{
  d_symConstFold[sym] = std::pair<std::vector<Kind>, Kind>(args, ret);
}

void ModelSmtNew::addQuantifier(const std::string& sym,
                                const std::vector<Kind>& args)
{
  // always call hard-coded method, without pre-evaluation
  std::stringstream ret;
  ret << "($smtx_model_eval_" << sym << " (" << sym << " x1 x2 ))";
  addReduceSym(sym, args, ret.str());
}

void ModelSmtNew::addLitBinSym(const std::string& sym,
                               const std::vector<Kind>& args,
                               const std::string& retWidth,
                               const std::string& retNum,
                               bool reqSameWidth)
{
  std::stringstream ssr;
  ssr << "($vsm_binary_mod_w " << retWidth << " " << retNum << ")";
  std::string ssres = ssr.str();
  if (reqSameWidth && args.size() == 2 && args[0] == Kind::BINARY
      && args[1] == Kind::BINARY)
  {
    ssres = smtGuard(smtZEq("x1", "x3"), ssres);
  }
  addLitSym(sym, args, Kind::ANY, ssres);
}

void ModelSmtNew::addLitSym(const std::string& sym,
                            const std::vector<Kind>& args,
                            Kind ret,
                            const std::string& retTerm)
{
  d_symLitReduce[sym] =
      std::tuple<std::vector<Kind>, Kind, std::string>(args, ret, retTerm);
}

void ModelSmtNew::addTermReduceSym(const std::string& sym,
                                   const std::vector<Kind>& args,
                                   const std::string& retTerm)
{
  std::cout << "(echo \"trim-defs-cmd (depends " << sym << " " << retTerm
            << ")\")" << std::endl;
  // the specification is SMT syntax, convert to embedding names here
  addReduceSym(sym, args, smtEval(retTerm));
}

void ModelSmtNew::addEunoiaReduceSym(const std::string& sym,
                                     const std::vector<Kind>& args,
                                     const std::string& retTerm)
{
  std::cout << "(echo \"trim-defs-cmd (depends " << sym << " " << retTerm
            << ")\")" << std::endl;
  d_eoSymReduce[sym] = std::pair<std::vector<Kind>, std::string>(args, retTerm);
}

void ModelSmtNew::addReduceSym(const std::string& sym,
                               const std::vector<Kind>& args,
                               const std::string& retTerm)
{
  d_symReduce[sym] = std::pair<std::vector<Kind>, std::string>(args, retTerm);
}

void ModelSmtNew::addRecReduceSym(const std::string& sym,
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

void ModelSmtNew::bind(const std::string& name, const Expr& e)
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

void ModelSmtNew::finalizeDecl(const std::string& name, const Expr& e)
{
  size_t nopqArgs = 0;
  Attr attr = d_state.getConstructorKind(e.getValue());
  if (attr == Attr::OPAQUE)
  {
    Expr ct = e.getType();
    // opaque symbols are non-nullary constructors
    Assert(ct.getKind() == Kind::FUNCTION_TYPE);
    nopqArgs = ct.getNumChildren() - 1;
  }
  // check for special cases
  std::map<std::string,
           std::vector<std::pair<std::string, std::string>>>::iterator itsc =
      d_specialCases.find(name);
  if (itsc != d_specialCases.end())
  {
    for (size_t i = 0, ncases = itsc->second.size(); i < ncases; i++)
    {
      printEunoiaReduce(itsc->second[i].first, {}, itsc->second[i].second);
    }
  }
  std::map<std::string, std::vector<Kind>>::iterator ith =
      d_symHardCode.find(name);
  if (ith != d_symHardCode.end())
  {
    printDecl(name, ith->second, Kind::PARAM, nopqArgs);
    printModelEvalCall(name, ith->second);
    return;
  }
  // maybe a constant fold symbol
  std::map<std::string, std::pair<std::vector<Kind>, Kind>>::iterator it =
      d_symConstFold.find(name);
  if (it != d_symConstFold.end())
  {
    printDecl(name, it->second.first, Kind::PARAM, nopqArgs);
    printModelEvalCall(name, it->second.first);
    printConstFold(name, it->second.first, it->second.second);
    return;
  }
  std::map<std::string,
           std::tuple<std::vector<Kind>, Kind, std::string>>::iterator its =
      d_symLitReduce.find(name);
  if (its != d_symLitReduce.end())
  {
    std::vector<Kind>& args = std::get<0>(its->second);
    printDecl(name, args, Kind::PARAM, nopqArgs);
    printModelEvalCall(name, args);
    printLitReduce(
        name, args, std::get<1>(its->second), std::get<2>(its->second));
    return;
  }
  std::map<std::string, std::pair<std::vector<Kind>, std::string>>::iterator
      itst = d_symReduce.find(name);
  if (itst != d_symReduce.end())
  {
    printDecl(name, itst->second.first, Kind::PARAM, nopqArgs);
    printModelEvalCallBase(name, itst->second.first, itst->second.second);
    return;
  }
  std::map<std::string, std::pair<std::vector<Kind>, std::string>>::iterator
      itost = d_eoSymReduce.find(name);
  if (itost != d_eoSymReduce.end())
  {
    printEunoiaReduce(name, itost->second.first, itost->second.second);
    return;
  }
  std::map<std::string, std::vector<Kind>>::iterator itsty =
      d_symTypes.find(name);
  if (itsty != d_symTypes.end())
  {
    printDecl(name, itsty->second, Kind::TYPE, nopqArgs);
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

void ModelSmtNew::printDecl(const std::string& name,
                            const std::vector<Kind>& args,
                            Kind ret,
                            size_t nopqArgs)
{
  std::stringstream tmp;
  std::ostream* out;
  std::string prefix;
  if (ret == Kind::TYPE)
  {
    // note that if we are a builtin type, we don't need to print the embedding
    // declaration
    if (name == "Int" || name == "Real" || name == "String" || name == "BitVec"
        || name == "Seq")
    {
      out = &tmp;
    }
    else
    {
      out = &d_smtTypes;
    }
    prefix = "tsm";
  }
  else
  {
    out = &d_smtTerms;
    prefix = "sm";
  }
  std::stringstream cname;
  cname << "$emb_" << prefix << "." << name;
  (*out) << "(declare-parameterized-const " << cname.str() << " (";
  std::stringstream macroVarList;
  std::stringstream macroOpqApply;
  std::string sret = cname.str();
  std::stringstream eoToSmtPatArgs;
  std::stringstream eoToSmtRetArgs;
  bool printedOpq = false;
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    // We do not use a generic "Apply" for types, instead all arguments
    // should be opaque.
    std::stringstream stmp;
    stmp << (i > 0 ? " " : "") << "(x" << (i + 1) << " ";
    if (args[i] == Kind::TYPE)
    {
      Assert(!printedOpq);
      // type arguments are always opaque on the SMT level
      // this includes types as arguments to other types and types indexing
      // seq.empty and set.empty.
      stmp << "$smt_Type :opaque";
      macroOpqApply << " x" << (i + 1);
      eoToSmtPatArgs << " x" << (i + 1);
      eoToSmtRetArgs << " ($eo_to_smt_type x" << (i + 1) << ")";
    }
    else if (ret == Kind::TYPE && args[i] == Kind::NUMERAL)
    {
      Assert(!printedOpq);
      // integer index on types are opaque (i.e. BitVec)
      stmp << "$smt_builtin_Int :opaque";
      macroOpqApply << " x" << (i + 1);
      eoToSmtPatArgs << " ($eo_numeral n" << (i + 1) << ")";
      eoToSmtRetArgs << " n" << (i + 1);
    }
    else if (ret != Kind::TYPE)
    {
      if (!printedOpq)
      {
        printedOpq = true;
        sret = sApply(sret, macroOpqApply.str());
      }
      stmp << "$smt_Term";
      std::stringstream ssnext;
      ssnext << "($sm_apply " << sret << " x" << (i + 1) << ")";
      sret = ssnext.str();
      eoToSmtPatArgs << " x" << (i + 1);
      eoToSmtRetArgs << " ($eo_to_smt x" << (i + 1) << ")";
    }
    else
    {
      Assert(false) << "Unknown type kind " << args[i] << " for " << name;
    }
    stmp << ")";
    (*out) << stmp.str();
    // define doesn't take :opaque
    std::string marg = stmp.str();
    replace(marg, " :opaque", "");
    macroVarList << marg;
  }
  // if all arguments were opaque, print them now
  if (!printedOpq)
  {
    sret = sApply(sret, macroOpqApply.str());
  }
  (*out) << ") " << (ret == Kind::TYPE ? "$smt_Type" : "$smt_Term") << ")"
         << std::endl;
  std::stringstream macroName;
  macroName << "$" << prefix << "_" << name;
  (*out) << "(define " << macroName.str() << " (" << macroVarList.str();
  (*out) << ") " << sret << ")" << std::endl;
  std::string eoToSmtPat = sApply(name, eoToSmtPatArgs.str());
  std::string eoToSmtRet = sApply(macroName.str(), eoToSmtRetArgs.str());
  // if a term declaration, write the mapping in eo_to_smt
  if (ret == Kind::TYPE)
  {
    d_eoToSmtType << "  (($eo_to_smt_type " << eoToSmtPat << ") " << eoToSmtRet
                  << ")" << std::endl;
  }
  else
  {
    d_eoToSmt << "  (($eo_to_smt " << eoToSmtPat << ") " << eoToSmtRet << ")"
              << std::endl;
  }
}

void ModelSmtNew::printEvalCallBase(std::ostream& out,
                                    const std::string& mname,
                                    const std::string& name,
                                    const std::vector<Kind>& args,
                                    const std::string& ret)
{
  out << "  ((" << mname << " ";
  if (args.empty())
  {
    out << name << ") " << ret << ")" << std::endl;
    return;
  }
  size_t i = 1;
  size_t nargs = args.size();
  size_t icount = 1;
  out << "(" << name;
  for (; i <= nargs; i++)
  {
    Kind k = args[i - 1];
    if (k == Kind::VARIABLE)
    {
      // variable lists
      out << " ($eo_List_cons ($eo_Var s T) x" << icount << ")";
    }
    else if (k == Kind::EVAL_CONS)
    {
      // generic list
      out << " ($eo_List_cons x" << icount << " x" << (icount + 1) << ")";
      icount++;
    }
    else
    {
      out << " x" << icount;
    }
    icount++;
  }
  out << ")) " << ret << ")" << std::endl;
}

void ModelSmtNew::printModelEvalCallBase(const std::string& name,
                                         const std::vector<Kind>& args,
                                         const std::string& ret)
{
  std::stringstream ss;
  ss << "$sm_" << name;
  printEvalCallBase(d_eval, "$smtx_model_eval", ss.str(), args, ret);
}

void ModelSmtNew::printEunoiaReduce(const std::string& name,
                                    const std::vector<Kind>& args,
                                    const std::string& ret)
{
  // std::stringstream ss;
  // ss << "($eo_to_smt " << ret << ")";
  printEvalCallBase(d_eoToSmt, "$eo_to_smt", name, args, ret);
}

void ModelSmtNew::printModelEvalCall(const std::string& name,
                                     const std::vector<Kind>& args)
{
  std::stringstream callArgs;
  callArgs << "($smtx_model_eval_" << name;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    callArgs << " ($smtx_model_eval x" << i << ")";
  }
  callArgs << ")";
  printModelEvalCallBase(name, args, callArgs.str());
}

void ModelSmtNew::printTermInternal(Kind k,
                                    const std::string& term,
                                    std::ostream& os,
                                    const std::string& guard)
{
  std::stringstream ret;
  if (d_kindToEoPrefix.find(k) != d_kindToEoPrefix.end())
  {
    ret << "($vsm_" << d_kindToEoPrefix[k] << " " << term << ")";
  }
  else if (k == Kind::EVAL_TO_STRING)
  {
    ret << "($vsm_re " << term << ")";
  }
  else
  {
    ret << term;
  }
  std::string rets = ret.str();
  if (!guard.empty())
  {
    rets = smtGuard(guard, rets);
  }
  os << rets;
}

void ModelSmtNew::printConstFold(const std::string& name,
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
  std::stringstream opName;
  std::map<std::string, std::string>::iterator ito =
      d_overloadRevert.find(name);
  if (ito != d_overloadRevert.end())
  {
    // e.g. in spite of having name $eoo_-.2, we use "-" as the invocation.
    opName << ito->second;
  }
  else
  {
    opName << name;
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
    if (isOverloadArith)
    {
      ssret << "($smt_builtin_" << (kas == Kind::NUMERAL ? "z" : "q") << "_"
            << opName.str();
    }
    else
    {
      ssret << "($smt_apply_" << args.size() << " \"" << opName.str() << "\"";
    }
    ssret << retArgs.str() << ")";
    // print the term with the right type
    std::stringstream fssret;
    printTermInternal(kr, ssret.str(), fssret, d_evalGuard[name]);
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

void ModelSmtNew::printAuxProgram(const std::string& name,
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

void ModelSmtNew::printAuxProgramCase(const std::string& name,
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
      progCases << " ($vsm_re x" << paramCount << ")";
      progParams << "(x" << paramCount << " $smt_builtin_RegLan)";
      continue;
    }
    progCases << " ($vsm_";
    if (ka == Kind::BINARY)
    {
      progCases << "binary x" << paramCount << " x" << (paramCount + 1) << ")";
      progParams << "(x" << paramCount << " $smt_builtin_Int)";
      progParams << " (x" << (paramCount + 1) << " $smt_builtin_Int)";
      paramCount++;
      continue;
    }
    Assert(d_kindToEoPrefix.find(ka) != d_kindToEoPrefix.end());
    progCases << d_kindToEoPrefix[ka] << " x" << paramCount << ")";
    progParams << "(x" << paramCount << " $smt_builtin_" << d_kindToType[ka]
               << ")";
  }
  progCases << ") ";
  progCases << ret << ")" << std::endl;
}

void ModelSmtNew::printLitReduce(const std::string& name,
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
  printTermInternal(ret, reduce, ssret, d_evalGuard[name]);
  // then print it on cases
  printAuxProgramCase(
      progName.str(), args, ssret.str(), paramCount, progCases, progParams);
  printAuxProgram(progName.str(), args, progCases, progParams);
}

void ModelSmtNew::finalize()
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
  ssis << s_plugin_path << "plugins/model_smt/model_smt_new.eo";
  std::ifstream ins(ssis.str());
  std::ostringstream sss;
  sss << ins.rdbuf();
  std::string finalSmt = sss.str();
  // plug in the evaluation cases handled by this plugin
  replace(finalSmt, "$SMT_EVAL_CASES$", d_eval.str());
  replace(finalSmt, "$SMT_EVAL_PROGS$", d_modelEvalProgs.str());
  replace(finalSmt, "$EO_TO_SMT_CASES$", d_eoToSmt.str());
  replace(finalSmt, "$EO_TO_SMT_TYPE_CASES$", d_eoToSmtType.str());
  replace(finalSmt, "$SMT_TERM_CONSTRUCTORS$", d_smtTerms.str());
  replace(finalSmt, "$SMT_TYPE_CONSTRUCTORS$", d_smtTypes.str());

  std::stringstream ssoe;
  ssoe << s_plugin_path << "plugins/model_smt/model_smt_gen.eo";
  // std::cout << "Write smt-model    " << finalSmt.str() << std::endl;
  std::ofstream oute(ssoe.str());
  oute << finalSmt;
}

}  // namespace mnew
}  // namespace ethos
