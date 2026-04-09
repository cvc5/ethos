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
std::string smtZ(uint32_t n)
{
  std::stringstream ss;
  ss << "($smt_apply_0 \"" << n << "\")";
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
std::string smtApp0(const std::string& c1)
{
  std::stringstream ss;
  ss << "($smt_apply_0 \"" << c1 << "\")";
  return ss.str();
}
std::string smtApp1(const std::string& app, const std::string& c1)
{
  std::stringstream ss;
  ss << "($smt_apply_1 \"" << app << "\" " << c1 << ")";
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
  return smtIte(guard, val, "$sm_none");
}

std::string smtGuardType(const std::string& guard, const std::string& val)
{
  return smtIte(guard, val, "$tsm_none");
}
std::string smtGuardType1(const std::string& nonNullType, const std::string& val)
{
  std::stringstream ss;
  ss << "($smt_builtin_ite ($smt_builtin_Teq " <<nonNullType << " $tsm_none) $tsm_none " << val << ")";
  return ss.str();
}
std::string smtBvSizeofValue(const std::string& str)
{
  return "($smtx_bv_sizeof_value " + str + ")";
}

/**
 * Makes s and t be in the context of the return term, used to specify the
 * return term of binary operations on bitvectors.
 */
std::string ModelSmt::smtBinaryBinReturn(const std::string& term)
{
  std::stringstream ss;
  ss << "(eo::define ((s ($sm_binary x1 x2))) ";
  ss << "(eo::define ((t ($sm_binary x3 x4))) ";
  ss << term << "))";
  return ss.str();
}

std::string ModelSmt::smtToSmtEmbed(const std::string& s, bool isTerm)
{
  std::string out;
  out.reserve(s.size());  // baseline; may grow
  for (size_t i = 0; i < s.size(); ++i)
  {
    if (s[i] == '(')
    {
      // don't replace if next char is '(' or '$', or "eo:"
      if (i + 1 < s.size() && (s[i + 1] == '(' || s[i + 1] == '$'))
      {
        out.push_back('(');
      }
      else if (i + 3 < s.size() && s[i + 1] == 'e' && s[i + 2] == 'o'
               && s[i + 3] == ':')
      {
        out.push_back('(');
      }
      else
      {
        out += isTerm ? "($sm_" : "($smtx_model_eval_";
      }
    }
    else
    {
      out.push_back(s[i]);
    }
  }
  // literal values used in reduction specifications
  std::string prefix = isTerm ? " $sm_" : " $vsm_";
  out = replace_all(out, " 0/1", prefix + "q_zero");
  out = replace_all(out, " 0", prefix + "z_zero");
  out = replace_all(out, " 1", prefix + "z_one");
  out = replace_all(out, " #b0", prefix + "binary_bit_false");
  out = replace_all(out, " #b1", prefix + "binary_bit_true");
  // note that nullary SMT-LIB symbols (e.g. re.none) are not handled
  return out;
}

std::string ModelSmt::smtEval(const std::string& s)
{
  std::stringstream ss;
  ss << "($smtx_model_eval M " << smtToSmtEmbed(s) << ")";
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

ModelSmt::ModelSmt(State& s) : StdPlugin(s)
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
  Kind kAny = Kind::ANY;
  Kind kNone = Kind::NONE;
  Kind kType = Kind::TYPE;
  Kind kRegLan = Kind::EVAL_TO_STRING;
  Kind kList = Kind::EVAL_CONS;
  // these don't matter, just need a unique identifier
  d_kSet = Kind::EVAL_LIST_SETOF;
  d_kSeq = Kind::EVAL_LIST_LENGTH;
  d_kArray = Kind::EVAL_LIST_NTH;
  d_kBit = Kind::EVAL_EXTRACT;
  d_kIntQuote = Kind::QUOTE_TYPE;
  // Kind kVarList = Kind::VARIABLE;
  d_kindToEoPrefix[kBool] = "bool";
  d_kindToEoPrefix[kInt] = "numeral";
  d_kindToEoPrefix[d_kIntQuote] = "numeral";
  d_kindToEoPrefix[kReal] = "rational";
  d_kindToEoPrefix[kString] = "seq";
  d_kindToEoPrefix[d_kSeq] = "seq";
  d_kindToEoPrefix[kBitVec] = "binary";
  d_kindToEoPrefix[kRegLan] = "re";
  d_kindToType[kBool] = "Bool";
  d_kindToType[d_kIntQuote] = "Int";
  d_kindToType[kInt] = "Int";
  d_kindToType[kReal] = "Real";
  d_kindToType[kString] = "String";
  d_kindToType[d_kSeq] = "Seq";
  d_kindToType[kBitVec] = "Binary";
  d_kindToType[kRegLan] = "RegLan";
  // All SMT-LIB symbols require having their semantics defined here.
  // Note that we model *SMT-LIB* not *CPC* here.
  // builtin
  // immediately include Bool, as it will not be defined
  // printDecl("Bool", {}, Kind::TYPE);
  // $sm_= and $sm_ite are builtin, reduce them in eo_to_smt
  addEunoiaReduceSym(
      "=", {kAny, kAny}, "($sm_= ($eo_to_smt x1) ($eo_to_smt x2))");
  addEunoiaReduceSym(
      "ite",
      {kBool, kAny, kAny},
      "($sm_ite ($eo_to_smt x1) ($eo_to_smt x2) ($eo_to_smt x3))");
  // FIXME: distinct needs to handle arg list
  addTermReduceSym("distinct", {kAny, kAny}, kBool, "(not (= x1 x2))");
  d_typeFullCase["distinct"] = "($smtx_typeof_= ($smtx_typeof x1) ($smtx_typeof x2))";
  // Booleans
  addConstFoldSym("and", {kBool, kBool}, kBool);
  addConstFoldSym("or", {kBool, kBool}, kBool);
  addTermReduceSym("xor", {kBool, kBool}, kBool, "(not (= x1 x2))");
  addTermReduceSym("=>", {kBool, kBool}, kBool, "(or (not x1) x2)");
  addConstFoldSym("not", {kBool}, kBool);
  // arithmetic
  addTypeSym("Int", {});
  addTypeSym("Real", {});
  // use kT to stand for either Int or Real arithmetic (not mixed)
  addConstFoldSym("+", {kT, kT}, kT);
  addAuxIsListNil("+", "(eo::is_eq (eo::to_q x1) 0/1)");
  addConstFoldSym("-", {kT, kT}, kT);
  addConstFoldSym("*", {kT, kT}, kT);
  addAuxIsListNil("*", "(eo::is_eq (eo::to_q x1) 1/1)");
  // we expect "-" to be overloaded, we look for its desugared name and map it
  // back
  addConstFoldSym("$eoo_-.2", {kT}, kT);
  d_overloadRevert["$eoo_-.2"] = "-";
  // addConstFoldSym("abs", {kInt}, kInt);
  addTermReduceSym("abs", {kInt}, kInt, "(ite (< x1 0) (- 0 x1) x1)");
  // addConstFoldSym(">=", {kT, kT}, kBool);
  addTermReduceSym(">=", {kT, kT}, kBool, "(<= x2 x1)");
  addConstFoldSym("<=", {kT, kT}, kBool);
  // addConstFoldSym(">", {kT, kT}, kBool);
  addTermReduceSym(">", {kT, kT}, kBool, "(< x2 x1)");
  addConstFoldSym("<", {kT, kT}, kBool);
  // addConstFoldSym("is_int", {kReal}, kBool);
  addTermReduceSym("is_int", {kReal}, kBool, "(= (to_real (to_int x1)) x1)");
  addConstFoldSym("/_total", {kT, kT}, kReal);
  addConstFoldSym("div_total", {kInt, kInt}, kInt);
  addConstFoldSym("mod_total", {kInt, kInt}, kInt);
  std::stringstream ssQDiv;
  ssQDiv << "(ite (= e2 0/1) (apply ($smtx_model_lookup M "
         << smtApp0("/_by_zero_id")
         << "($tsm_Map $tsm_Real $tsm_Real)) e1) (/_total e1 e2))";
  addRecReduceSym("/", {kT, kT}, kReal, smtToSmtEmbed(ssQDiv.str()));
  std::stringstream ssDiv;
  ssDiv << "(ite (= e2 0) (apply ($smtx_model_lookup M "
        << smtApp0("div_by_zero_id")
        << "($tsm_Map $tsm_Int $tsm_Int)) e1) (div_total e1 e2))";
  addRecReduceSym("div", {kInt, kInt}, kInt, smtToSmtEmbed(ssDiv.str()));
  std::stringstream ssMod;
  ssMod << "(ite (= e2 0) (apply ($smtx_model_lookup M "
        << smtApp0("mod_by_zero_id")
        << "($tsm_Map $tsm_Int $tsm_Int)) e1) (mod_total e1 e2))";
  addRecReduceSym("mod", {kInt, kInt}, kInt, smtToSmtEmbed(ssMod.str()));
  std::stringstream ssZExp;
  ssZExp << "(ite (>= e2 0) (**_total e1 e2) (ite (= e1 0) (apply "
            "($smtx_model_lookup M "
         << smtApp0("div_by_zero_id")
         << "($tsm_Map $tsm_Int $tsm_Int)) 1) (div_total 1 (**_total e1 (- 0 "
            "e2)))))";
  addRecReduceSym("**", {kInt, kInt}, kInt, smtToSmtEmbed(ssZExp.str()));
  addConstFoldSym("**_total", {kInt, kInt}, kInt);
  addConstFoldSym("to_int", {kReal}, kInt);
  addConstFoldSym("to_real", {kT}, kReal);
  d_typeFullCase["to_real"] = "(eo::define ((T ($smtx_typeof x1))) ($smt_builtin_ite ($smt_builtin_Teq T $tsm_Int) $tsm_Real ($smt_builtin_ite ($smt_builtin_Teq T $tsm_Real) $tsm_Real $tsm_none)))";
  addTermReduceSym("divisible", {kInt, kInt}, kBool, "(= (mod_total x2 x1) 0)");
  // arrays
  addTypeSym("Array", {kType, kType});
  addTermReduceSym("select", {kAny, kAny}, kAny, "($smtx_map_select x1 x2)");
  addAuxTypeProgram("select",
                      {d_kArray, kAny},
                      "($smt_builtin_ite ($smt_builtin_Teq x1 x3) x2 $tsm_none)");
  addTermReduceSym(
      "store", {kAny, kAny, kAny}, kAny, "($smtx_map_store x1 x2 x3)");
  addAuxTypeProgram("store",
                      {d_kArray, kAny, kAny},
                      "($smt_builtin_ite ($smt_builtin_Teq x1 x3) ($smt_builtin_ite ($smt_builtin_Teq x2 x4) ($tsm_Array x1 x2) $tsm_none) $tsm_none)");
  // strings
  addTypeSym("Seq", {kType});
  addTypeSym("Char", {});
  addTypeSym("RegLan", {});
  addConstFoldSym("str.++", {d_kSeq, d_kSeq}, d_kSeq);
  // custom definition of is_list_nil recognizer
  if (optionFwdDeclIsListNilNground())
  {
    d_auxDesugar["str.++"] = R"(
(program $eo_is_list_nil_str.++ ((T Type) (t T)) 
  :signature (T) Bool
  (
  (($eo_is_list_nil_str.++ (seq.empty T)) true)
  (($eo_is_list_nil_str.++ t) (eo::eq t ""))
  )
))";
  }
  addConstFoldSym("str.len", {d_kSeq}, kInt);
  addConstFoldSym("str.substr", {d_kSeq, kInt, kInt}, d_kSeq);
  addAuxTypeProgram("str.substr",
                      {d_kSeq, kInt, kInt},
                      "($tsm_Seq x1)");
  // addConstFoldSym("str.at", {kString, kInt}, kString);
  addTermReduceSym("str.at", {d_kSeq, kInt}, kString, "(str.substr x1 x2 1)");
  addAuxTypeProgram("str.at",
                      {d_kSeq, kInt},
                      "($tsm_Seq x1)");
  addConstFoldSym("str.indexof", {d_kSeq, d_kSeq, kInt}, kInt);
  addAuxTypeProgram("str.indexof",
                      {d_kSeq, d_kSeq, kInt},
                      "($smt_builtin_ite ($smt_builtin_Teq x1 x2) $tsm_Int $tsm_none)");
  addConstFoldSym("str.replace", {d_kSeq, d_kSeq, d_kSeq}, d_kSeq);
  addConstFoldSym("str.replace_all", {d_kSeq, d_kSeq, d_kSeq}, d_kSeq);
  addConstFoldSym("str.from_code", {kInt}, kString);
  addConstFoldSym("str.to_code", {kString}, kInt);
  addConstFoldSym("str.from_int", {kInt}, kString);
  addConstFoldSym("str.to_int", {kString}, kInt);
  // addConstFoldSym("str.is_digit", {kString}, kBool);
  std::stringstream ssIsDigit;
  ssIsDigit << "(and (<= ($vsm_numeral " << smtZ(48) << ")"
            << " (str.to_code x1)) (<= (str.to_code x1) ($vsm_numeral "
            << smtZ(57) << ")))";
  addTermReduceSym("str.is_digit", {kString}, kBool, ssIsDigit.str());
  addConstFoldSym("str.contains", {d_kSeq, d_kSeq}, kBool);
  // addConstFoldSym("str.suffixof", {kString, kString}, kBool);
  // reduce
  addTermReduceSym(
      "str.suffixof",
      {kString, kString},
      kBool,
      "(= x1 (str.substr x2 (- (str.len x2) (str.len x1)) (str.len x1)))");
  // addConstFoldSym("str.prefixof", {kString, kString}, kBool);
  addTermReduceSym("str.prefixof",
                   {kString, kString},
                   kBool,
                   "(= x1 (str.substr x2 0 (str.len x1)))");
  // addConstFoldSym("str.<=", {kString, kString}, kBool);
  addTermReduceSym(
      "str.<=", {kString, kString}, kBool, "(or (= x1 x2) (str.< x1 x2))");
  addConstFoldSym("str.<", {kString, kString}, kBool);
  // regular expressions
  addReduceSym(
      "re.allchar", {}, kRegLan, "($vsm_re ($smt_apply_0 \"re.allchar\"))");
  addReduceSym("re.none", {}, kRegLan, "($vsm_re ($smt_apply_0 \"re.none\"))");
  addReduceSym("re.all", {}, kRegLan, "($vsm_re ($smt_apply_0 \"re.all\"))");
  addConstFoldSym("str.to_re", {kString}, kRegLan);
  addConstFoldSym("re.*", {kRegLan}, kRegLan);
  // addConstFoldSym("re.+", {kRegLan}, kRegLan);
  addTermReduceSym("re.+", {kRegLan}, kRegLan, "(re.++ x1 (re.* x1))");
  addTermReduceSym("re.opt",
                   {kRegLan},
                   kRegLan,
                   "(re.union x1 (str.to_re $vsm_string_empty))");
  addConstFoldSym("re.comp", {kRegLan}, kRegLan);
  addConstFoldSym("re.++", {kRegLan, kRegLan}, kRegLan);
  addConstFoldSym("re.inter", {kRegLan, kRegLan}, kRegLan);
  addConstFoldSym("re.union", {kRegLan, kRegLan}, kRegLan);
  addConstFoldSym("re.diff", {kRegLan, kRegLan}, kRegLan);  // TODO: term reduce
  addConstFoldSym("re.range", {kString, kString}, kRegLan);
  printAuxNatRecProgram(
      "re.^",
      {kNone},
      smtToSmtEmbed("(str.to_re $vsm_string_empty)"),
      smtToSmtEmbed("(re.++ ($smtx_model_eval_re.^_rec n x1) x1)"));
  addLitSym("re.^",
            {d_kIntQuote, kRegLan},
            kT,
            smtToSmtEmbed("($smtx_model_eval_re.^_rec "
                                   "($smt_builtin_z_to_n x1) ($vsm_re x2))"));
  addAuxTypeProgram("re.^", {d_kIntQuote, kRegLan}, smtGuardType(smtZLeq("$smt_builtin_z_zero", "x1"), "$tsm_RegLan"));
  std::stringstream ssReLoopRet;
  ssReLoopRet << "(ite (> ($vsm_numeral x1) ($vsm_numeral x2))";
  ssReLoopRet << " ($vsm_re ($smt_apply_0 \"re.none\"))";
  ssReLoopRet << " ($smtx_model_eval_re.loop_rec ($smt_builtin_z_to_n "
                 "($smt_builtin_z_- x2 x1)) ($vsm_numeral x1) ($vsm_numeral "
                 "x2) ($vsm_re x3)))";
  std::stringstream ssReLoopRetRec;
  ssReLoopRetRec
      << "(re.union ($smtx_model_eval_re.loop_rec n x1 ($vsm_numeral "
         "($smt_builtin_z_dec x2)) x3) (re.^ ($vsm_numeral x2) x3))";
  printAuxNatRecProgram("re.loop",
                        {kNone, kInt, kNone},
                        smtToSmtEmbed("(re.^ x1 x3)"),
                        smtToSmtEmbed(ssReLoopRetRec.str()));
  addLitSym("re.loop",
            {d_kIntQuote, d_kIntQuote, kRegLan},
            kT,
            smtToSmtEmbed(ssReLoopRet.str()));
  addAuxTypeProgram("re.loop", {d_kIntQuote, d_kIntQuote, kRegLan}, smtGuardType(smtZLeq("$smt_builtin_z_zero", "x1"), smtGuardType(smtZLeq("$smt_builtin_z_zero", "x2"), "$tsm_RegLan")));
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
  addAuxIsListNil("bvadd", "(eo::is_eq (eo::to_z x1) 0)");
  addLitBinSym("bvmul", {kBitVec, kBitVec}, "x1", "($smt_builtin_z_* x2 x4)");
  addAuxIsListNil("bvmul", "(eo::is_eq (eo::to_z x1) 1)");
  addLitBinSym("bvudiv",
               {kBitVec, kBitVec},
               "x1",
               smtIte(smtZEq("x4", "$smt_builtin_z_zero"),
                      "($smt_builtin_binary_max x1)",
                      "($smt_builtin_div_total x2 x4)"));
  addLitBinSym("bvurem",
               {kBitVec, kBitVec},
               "x1",
               smtIte(smtZEq("x4", "$smt_builtin_z_zero"),
                      "x2",
                      "($smt_builtin_mod_total x2 x4)"));
  addLitBinSym(
      "bvand", {kBitVec, kBitVec}, "x1", "($smt_builtin_binary_and x1 x2 x4)");
  addAuxIsListNil("bvand", "(eo::is_eq (eo::to_z (eo::not x1)) 0)");
  addLitBinSym(
      "bvor", {kBitVec, kBitVec}, "x1", "($smt_builtin_binary_or x1 x2 x4)");
  addAuxIsListNil("bvor", "(eo::is_eq (eo::to_z x1) 0)");
  addLitBinSym(
      "bvxor", {kBitVec, kBitVec}, "x1", "($smt_builtin_binary_xor x1 x2 x4)");
  addAuxIsListNil("bvxor", "(eo::is_eq (eo::to_z x1) 0)");
  addLitBinSym("bvnot", {kBitVec}, "x1", "($smt_builtin_binary_not x1 x2)");
  addLitBinSym("bvneg", {kBitVec}, "x1", "($smt_builtin_z_neg x2)");
  addLitBinSym("bvshl",
               {kBitVec, kBitVec},
               "x1",
               "($smt_builtin_z_* x2 ($smt_builtin_z_pow2 x4))");
  addLitBinSym("bvlshr",
               {kBitVec, kBitVec},
               "x1",
               "($smt_builtin_div_total x2 ($smt_builtin_z_pow2 x4))");
  std::stringstream ssExtractRet;
  ssExtractRet << "($vsm_binary_mod_w ";
  ssExtractRet << smtZSub(smtZAdd("x1", "$smt_builtin_z_one"), "x2");
  ssExtractRet << " ($smt_builtin_binary_extract x3 x4 x1 x2))";
  addLitSym("extract",
            {d_kIntQuote, d_kIntQuote, kBitVec},
            kT,
            ssExtractRet.str());
  std::string ssExtractType =
  smtGuardType("($smt_builtin_z_<= $smt_builtin_z_zero x2)",
  smtGuardType("($smt_builtin_z_<= x2 x1)",
  smtGuardType("($smt_builtin_z_< x1 x3)",
               "($tsm_BitVec ($smt_builtin_z_inc ($smt_builtin_z_- x1 x2)))")));
  addAuxTypeProgram("extract", {d_kIntQuote, d_kIntQuote, kBitVec}, ssExtractType);
  addLitBinSym("concat",
               {kBitVec, kBitVec},
               smtZAdd("x1", "x3"),
               "($smt_builtin_binary_concat x1 x2 x3 x4)",
               false);
  addAuxTypeProgram("concat",
                      {kBitVec, kBitVec},
                      "($tsm_BitVec ($smt_builtin_z_+ x1 x2))");
  std::stringstream ssUgtRet;
  ssUgtRet << "($vsm_bool " << smtZLt("x4", "x2") << ")";
  addLitSym("bvugt",
            {kBitVec, kBitVec},
            kT,
            ssUgtRet.str());
  d_typeRetCase["bvugt"] = "$tsm_Bool";
  // the following operators require a mix of literal evaluation and term
  // reduction
  std::stringstream ssSgtRet;
  ssSgtRet << "(eo::define (($wm1 (- ($vsm_numeral " << smtBvSizeofValue("x1") << ") 1))) ";
  ssSgtRet << "(eo::define (($msb1 (= (extract $wm1 $wm1 x1) #b1))) ";
  ssSgtRet << "(eo::define (($wm2 (- ($vsm_numeral " << smtBvSizeofValue("x2") << ") 1))) ";
  ssSgtRet << "(eo::define (($msb2 (= (extract $wm2 $wm2 x2) #b1))) ";
  ssSgtRet
      << "(or (and (not $msb1) $msb2) (and (= $msb1 $msb2) (bvugt x1 x2)))";
  ssSgtRet << "))))";
  addTermReduceSym("bvsgt", {kBitVec, kBitVec}, kBool, ssSgtRet.str());
  addLitSym("zero_extend",
            {d_kIntQuote, kBitVec},
            kT,
                     "($vsm_binary ($smt_builtin_z_+ x1 x2) x3)");
  addAuxTypeProgram("zero_extend",
                      {d_kIntQuote, kBitVec},
                      smtGuardType(smtZLeq("$smt_builtin_z_zero", "x1"),
                               "($tsm_BitVec ($smt_builtin_z_+ x1 x2))"));
  addLitSym("sign_extend",
            {d_kIntQuote, kBitVec},
            kT,
                     "($vsm_binary_mod_w ($smt_builtin_z_+ x1 x2) "
                     "($smt_builtin_binary_uts x2 x3))");
  addAuxTypeProgram("sign_extend",
                      {d_kIntQuote, kBitVec},
                      smtGuardType(smtZLeq("$smt_builtin_z_zero", "x1"),
                               "($tsm_BitVec ($smt_builtin_z_+ x1 x2))"));
  std::stringstream ssAshrRet;
  ssAshrRet << "(eo::define (($wm1 " << "(- ($vsm_numeral " << smtBvSizeofValue("x1") << ") 1)"
            << ")) ";
  ssAshrRet << "(ite (= (extract $wm1 $wm1 x1) #b0) (bvlshr "
               "x1 x2) (bvnot "
               "(bvlshr (bvnot x1) x2)))";
  ssAshrRet << ")";
  addTermReduceSym("bvashr", {kBitVec, kBitVec}, kBitVec, ssAshrRet.str());
  std::stringstream ssRLeftRet;
  ssRLeftRet << "(eo::define (($wm1 ($vsm_numeral ($smt_builtin_z_dec x1)))) ";
  ssRLeftRet << "(eo::define (($wm2 ($vsm_numeral ($smt_builtin_z_dec "
                "($smt_builtin_z_dec x1))))) ";
  ssRLeftRet << "($smtx_model_eval_rotate_left_rec n "
                "(concat (extract $wm2 $vsm_z_zero ($vsm_binary x1 x2)) "
                "(extract $wm1 $wm1 ($vsm_binary x1 x2))))))";
  printAuxNatRecProgram("rotate_left",
                        {kBitVec},
                        "($vsm_binary x1 x2)",
                        smtToSmtEmbed(ssRLeftRet.str()));
  addLitSym(
      "rotate_left",
      {d_kIntQuote, kT},
      kT,
          "($smtx_model_eval_rotate_left_rec ($smt_builtin_z_to_n x1) x2)");
  addAuxTypeProgram("rotate_left", {d_kIntQuote, kBitVec}, smtGuardType(
          smtZLeq("$smt_builtin_z_zero", "x1"), "($tsm_BitVec x2)"));
  std::stringstream ssRRightRet;
  ssRRightRet << "(eo::define (($wm1 ($vsm_numeral ($smt_builtin_z_dec x1)))) ";
  ssRRightRet << "($smtx_model_eval_rotate_right_rec n (concat (extract "
                 "$vsm_z_zero $vsm_z_zero ($vsm_binary x1 x2)) "
                 "(extract $wm1 $vsm_z_one ($vsm_binary x1 x2)))))";
  printAuxNatRecProgram("rotate_right",
                        {kBitVec},
                        "($vsm_binary x1 x2)",
                        smtToSmtEmbed(ssRRightRet.str()));
  addLitSym(
      "rotate_right",
      {d_kIntQuote, kT},
      kT,
          "($smtx_model_eval_rotate_right_rec ($smt_builtin_z_to_n x1) x2)");
  addAuxTypeProgram("rotate_right", {d_kIntQuote, kBitVec}, smtGuardType(
          smtZLeq("$smt_builtin_z_zero", "x1"), "($tsm_BitVec x2)"));
  printAuxNatRecProgram(
      "repeat",
      {kNone},
      "$vsm_binary_empty",
      smtToSmtEmbed("(concat x1 ($smtx_model_eval_repeat_rec n x1))"));
  addLitSym("repeat",
            {d_kIntQuote, kBitVec},
            kT,
                     "($smtx_model_eval_repeat_rec ($smt_builtin_z_to_n "
                     "x1) ($vsm_binary x2 x3))");
  addAuxTypeProgram("repeat",
                      {d_kIntQuote, kBitVec},
                      smtGuardType(smtZLeq("$smt_builtin_z_one", "x1"),
                               "($tsm_BitVec ($smt_builtin_z_* x1 x2))"));
  // the following are program cases in the main method of the form
  // (($smtx_model_eval (f x1 x2)) ($smtx_model_eval <return>))
  addTermReduceSym(
      "bvsub", {kBitVec, kBitVec}, kBitVec, "(bvadd x1 (bvneg x2))");
  addTermReduceSym("bvsle", {kBitVec, kBitVec}, kBool, "(bvsge x2 x1)");
  addTermReduceSym("bvule", {kBitVec, kBitVec}, kBool, "(bvuge x2 x1)");
  addTermReduceSym("bvslt", {kBitVec, kBitVec}, kBool, "(bvsgt x2 x1)");
  addTermReduceSym("bvult", {kBitVec, kBitVec}, kBool, "(bvugt x2 x1)");
  addTermReduceSym(
      "bvnand", {kBitVec, kBitVec}, kBitVec, "(bvnot (bvand x1 x2))");
  addTermReduceSym(
      "bvnor", {kBitVec, kBitVec}, kBitVec, "(bvnot (bvor x1 x2))");
  addTermReduceSym(
      "bvxnor", {kBitVec, kBitVec}, kBitVec, "(bvnot (bvxor x1 x2))");
  addTermReduceSym(
      "bvuge", {kBitVec, kBitVec}, kBool, "(or (bvugt x1 x2) (= x1 x2))");
  addTermReduceSym(
      "bvsge", {kBitVec, kBitVec}, kBool, "(or (bvsgt x1 x2) (= x1 x2))");
  // sdiv, srem, smod
  for (size_t i = 0; i < 3; i++)
  {
    std::stringstream ssRet;
    std::stringstream ssRetEnd;
    std::string op;
    std::stringstream ssTermRet;
    ssRet << "(eo::define (($wm1 (- ($vsm_numeral " << smtBvSizeofValue("x1") << ") 1))) ";
    ssRet << "(eo::define (($msb_s (= (extract $wm1 $wm1 x1) #b1))) ";
    ssRet << "(eo::define (($msb_t (= (extract $wm1 $wm1 x2) #b1))) ";
    ssRetEnd << ")))";
    if (i == 0)
    {
      op = "bvsdiv";
      ssTermRet << "(ite (and (not $msb_s) (not $msb_t)) (bvudiv x1 x2)";
      ssTermRet
          << " (ite (and $msb_s (not $msb_t)) (bvneg (bvudiv (bvneg x1) x2))";
      ssTermRet
          << " (ite (and (not $msb_s) $msb_t) (bvneg (bvudiv x1 (bvneg x2)))";
      ssTermRet << " (bvudiv (bvneg x1) (bvneg x2)))))";
    }
    else if (i == 1)
    {
      op = "bvsrem";
      ssTermRet << "(ite (and (not $msb_s) (not $msb_t)) (bvurem x1 x2)";
      ssTermRet
          << " (ite (and $msb_s (not $msb_t)) (bvneg (bvurem (bvneg x1) x2))";
      ssTermRet
          << " (ite (and (not $msb_s) $msb_t) (bvneg (bvurem x1 (bvneg x2)))";
      ssTermRet << " (bvurem (bvneg x1) (bvneg x2)))))";
    }
    else
    {
      op = "bvsmod";
      ssRet << "(eo::define (($abs_s "
            << "(ite $msb_s x1 (bvneg x1))" << ")) ";
      ssRet << "(eo::define (($abs_t "
            << "(ite $msb_t x2 (bvneg x2))" << ")) ";
      ssRet << "(eo::define (($u " << "(bvurem $abs_s $abs_t"
            << "))) ";
      ssRetEnd << ")))";
      ssTermRet << "(ite (= $u ($vsm_binary " << smtBvSizeofValue("x1") << " $smt_builtin_z_zero)) $u";
      ssTermRet << " (ite (and (not $msb_s) (not $msb_t)) $u";
      ssTermRet << " (ite (and $msb_s (not $msb_t)) (bvadd (bvneg $u) x2)";
      ssTermRet << " (ite (and (not $msb_s) $msb_t) (bvadd $u x2)";
      ssTermRet << " (bvneg $u)))))";
    }
    ssRet << ssTermRet.str() << ssRetEnd.str();
    addTermReduceSym(op, {kBitVec, kBitVec}, kBitVec, ssRet.str());
  }
  // overflow predicates
  addLitSym("bvuaddo",
            {kBitVec, kBitVec},
            kBool,
            smtZLeq("($smt_builtin_z_pow2 x1)", smtZAdd("x2", "x4")));
  addLitSym("bvumulo",
            {kBitVec, kBitVec},
            kBool,
            smtZLeq("($smt_builtin_z_pow2 x1)", "($smt_builtin_z_* x2 x4)"));
  for (size_t i = 0; i < 2; i++)
  {
    std::string intOp = i == 0 ? "+" : "*";
    std::string bvOp = i == 0 ? "bvsaddo" : "bvsmulo";
    std::stringstream ssRet;
    ssRet << "(eo::define ((sret ($smt_builtin_z_" << intOp;
    ssRet << " ($smt_builtin_binary_uts x1 x2) ($smt_builtin_binary_uts x3 "
             "x4)))) ";
    ssRet << "(eo::define ((p2wm1 ($smt_builtin_z_pow2 ($smt_builtin_z_- x1 "
             "$smt_builtin_z_one)))) ";
    ssRet << " ($smt_builtin_or " << smtZLeq("p2wm1", "sret");
    ssRet << " " << smtZLt("sret", "($smt_builtin_z_neg p2wm1)");
    ssRet << ")))";
    addLitSym(bvOp, {kBitVec, kBitVec}, kBool, ssRet.str());
  }
  addLitSym("bvnego",
            {kBitVec},
            kBool,
            smtZEq("x2", "($smt_builtin_z_pow2 ($smt_builtin_z_dec x1))"));
  addTermReduceSym("bvusubo", {kBitVec, kBitVec}, kBool, "(bvult x1 x2)");
  addTermReduceSym("bvssubo",
                   {kBitVec, kBitVec},
                   kBool,
                   "(ite (bvnego x2) (bvsge x1 ($vsm_binary " + smtBvSizeofValue("x1") + " $smt_builtin_z_zero)) "
                   "(bvsaddo x1 (bvneg x2)))");
  addTermReduceSym("bvsdivo",
                   {kBitVec, kBitVec},
                   kBool,
                   "(and (bvnego x1) (= x2 (bvnot ($vsm_binary " + smtBvSizeofValue("x1") + " $smt_builtin_z_zero))))");
  // arith/BV conversions
  addLitSym("ubv_to_int", {kBitVec}, kInt, "x2");
  addLitSym("sbv_to_int", {kBitVec}, kInt, "($smt_builtin_binary_uts x1 x2)");
  addLitSym("int_to_bv", {d_kIntQuote, kInt}, kT, "($vsm_binary_mod_w x1 x2)");
  addAuxTypeProgram("int_to_bv",
                      {d_kIntQuote, kInt},
                      smtGuardType("($smt_builtin_z_<= $smt_builtin_z_zero x1)", "($tsm_BitVec x1)"));
  // Quantifiers
  // one variable at a time, $sm_exists is hardcoded
  addEunoiaReduceSym(
      "exists", {kT, kT}, "($eo_to_smt_exists x1 ($eo_to_smt x2))");
  addEunoiaReduceSym(
      "forall",
      {kT, kBool},
      "($sm_not ($eo_to_smt_exists x1 ($sm_not ($eo_to_smt x2))))");

  //===========================================================================
  ///----- non standard extensions and skolems
  // builtin
  // one variable at a time, $sm_lambda is hardcoded
  //addEunoiaReduceSym(
  //    "lambda", {kT, kT}, "($eo_to_smt_lambda x1 ($eo_to_smt x2))");
  addEunoiaReduceSym("@purify", {kT}, "($eo_to_smt x1)");
  // arithmetic
  addConstFoldSym("int.pow2", {kInt}, kInt);
  addConstFoldSym("int.log2", {kInt}, kInt);
  addEunoiaReduceSym("@int_div_by_zero",
                     {kInt},
                     smtToSmtEmbed("(div ($eo_to_smt x1) 0)", true));
  addEunoiaReduceSym(
      "@mod_by_zero", {kInt}, smtToSmtEmbed("(mod ($eo_to_smt x1) 0)", true));
  addEunoiaReduceSym(
      "@div_by_zero", {kReal}, smtToSmtEmbed("(/ ($eo_to_smt x1) 0/1)", true));
  addEunoiaReduceSym(
      "int.ispow2",
      {kInt},
      smtToSmtEmbed("(eo::define (($e1 ($eo_to_smt x1))) (and (>= $e1 0) (= "
                    "$e1 (int.pow2 (int.log2 $e1)))))",
                    true));
  // arrays
  std::stringstream ssArrayDiffVar;
  ssArrayDiffVar << "($sm_Var $smt_builtin_str_vname T)";
  std::stringstream ssArrayDiff;
  ssArrayDiff << "(eo::define ((T ($eo_to_smt_type ($eo_typeof "
                 "(@array_deq_diff x1 x2))))) ";
  ssArrayDiff << "(eo::define ((i ($sm_Var $smt_builtin_str_vname T))) ";
  ssArrayDiff << "($sm_apply ($sm_choice $smt_builtin_str_vname T) ";
  ssArrayDiff << smtToSmtEmbed(
      "(not (= (select ($eo_to_smt x1) i) (select ($eo_to_smt x2) i)))", true)
              << ")))";
  addEunoiaReduceSym("@array_deq_diff", {kT, kT}, ssArrayDiff.str());
  // strings
  addConstFoldSym("str.update", {d_kSeq, kInt, d_kSeq}, d_kSeq);
  addAuxTypeProgram("str.update",
                      {d_kSeq, kInt, d_kSeq},
                      "($smt_builtin_ite ($smt_builtin_Teq x1 x2) ($tsm_Seq x1) $tsm_none)");
  addConstFoldSym("str.rev", {d_kSeq}, d_kSeq);
  addConstFoldSym("str.to_lower", {kString}, kString);
  addConstFoldSym("str.to_upper", {kString}, kString);
  std::stringstream ssItosRes;
  ssItosRes << "(str.from_int (mod ($eo_to_smt x1) (** (numeral " << smtZ(10)
            << ") ($eo_to_smt x2))))";
  addEunoiaReduceSym("@strings_itos_result",
                     {kInt, kInt},
                     smtToSmtEmbed(ssItosRes.str(), true));
  addEunoiaReduceSym(
      "@strings_stoi_result",
      {kString, kInt},
      smtToSmtEmbed(
          "(str.to_int (str.substr ($eo_to_smt x1) 0 ($eo_to_smt x2)))", true));
  addEunoiaReduceSym(
      "@strings_stoi_non_digit",
      {kString},
      smtToSmtEmbed("(str.indexof_re ($eo_to_smt x1) (re.comp (re.range "
                    "($sm_string $smt_builtin_str_c0) ($sm_string "
                    "$smt_builtin_str_c9))) 0)",
                    true));
  std::stringstream ssStringsDeqDiff;
  ssStringsDeqDiff
      << "(eo::define ((i ($sm_Var $smt_builtin_str_vname $tsm_Int))) ";
  ssStringsDeqDiff
      << "($sm_apply ($sm_choice $smt_builtin_str_vname $tsm_Int) ";
  ssStringsDeqDiff << smtToSmtEmbed(
      "(not (= (str.substr ($eo_to_smt x1) i 1) (str.substr "
      "($eo_to_smt x2) i 1)))",
      true) << "))";
  addEunoiaReduceSym("@strings_deq_diff", {kT, kT}, ssStringsDeqDiff.str());
  std::stringstream ssWitnessStringLength;
  ssWitnessStringLength << "(eo::define (($T ($eo_to_smt_type x1))) ";
  ssWitnessStringLength
      << "(eo::define (($i (Var $smt_builtin_str_vname $T))) ";
  ssWitnessStringLength << "(apply (choice $smt_builtin_str_vname $T) ";
  ssWitnessStringLength << "(= (str.len $i) ($eo_to_smt x2)))))";
  addEunoiaReduceSym("@witness_string_length",
                     {kType, kInt, kInt},
                     smtToSmtEmbed(ssWitnessStringLength.str(), true));
  // curried choice as an auxiliary program
  d_auxDef["@quantifiers_skolemize"] = R"(
(program $eo_to_smt_quantifiers_skolemize
  ((s $smt_builtin_String) (T $smt_Type) (F $smt_Term) (n $smt_builtin_Nat) (t $smt_Term))
  :signature ($smt_Term $smt_builtin_Nat) $smt_Term
  (
  (($eo_to_smt_quantifiers_skolemize ($sm_apply ($sm_exists s T) F) $smt_builtin_n_zero)
     ($sm_apply ($sm_choice s T) F))
  (($eo_to_smt_quantifiers_skolemize ($sm_apply ($sm_exists s T) F) ($smt_builtin_n_succ n))
     ($eo_to_smt_quantifiers_skolemize
       ($eo_to_smt_substitute s T ($eo_to_smt_quantifiers_skolemize ($sm_apply ($sm_exists s T) F) $smt_builtin_n_zero) F)
       n))
  (($eo_to_smt_quantifiers_skolemize F t) $sm_none)
  )
))";
  // note that negative indices are silently treated as 0 here
  d_specialCases["@quantifiers_skolemize"].emplace_back(
      "(@quantifiers_skolemize (forall x1 x2) x3)",
      smtGuard("($smt_builtin_teq ($eo_is_neg x3) false)", "($eo_to_smt_quantifiers_skolemize ($eo_to_smt_exists x1 ($sm_not "
      "($eo_to_smt x2))) "
      "($eo_to_smt_nat x3))"));
  d_symIgnore["@quantifiers_skolemize"] = true;

  // re pos unfold
  d_auxDef["@re_unfold_pos_component"] = R"(
(program $eo_to_smt_re_unfold_pos_component
  ((s $smt_Term) (r1 $smt_Term) (r2 $smt_Term) (n $smt_builtin_Nat) (t $smt_Term))
  :signature ($smt_Term $smt_Term $smt_builtin_Nat) $smt_Term
  (
  (($eo_to_smt_re_unfold_pos_component s ($sm_re.++ r1 r2) $smt_builtin_n_zero)
    (eo::define ((x ($sm_Var $smt_builtin_str_vname $tsm_String)))
    (eo::define ((xrem ($sm_str.substr s ($sm_str.len x) ($sm_- ($sm_str.len s) ($sm_str.len x)))))
      ($sm_apply ($sm_choice $smt_builtin_str_vname $tsm_String)
        ($sm_and ($sm_= s ($sm_str.++ x xrem)) ($sm_and ($sm_str.in_re x r1) ($sm_str.in_re xrem r2)))))))
  (($eo_to_smt_re_unfold_pos_component s ($sm_re.++ r1 r2) ($smt_builtin_n_succ n))
    (eo::define ((k ($eo_to_smt_re_unfold_pos_component s ($sm_re.++ r1 r2) $smt_builtin_n_zero)))
      ($eo_to_smt_re_unfold_pos_component
        ($sm_str.substr s ($sm_str.len k) ($sm_- ($sm_str.len s) ($sm_str.len k)))
        r2 n)))
  (($eo_to_smt_re_unfold_pos_component s r1 n) $sm_none)
  )
))";
  // note that negative indices are silently treated as 0 here
  addEunoiaReduceSym(
      "@re_unfold_pos_component",
      {kAny, kAny, kAny},
      smtGuard("($smt_builtin_teq ($eo_is_neg x3) false)", smtToSmtEmbed("($eo_to_smt_re_unfold_pos_component ($eo_to_smt x1) "
                    "($eo_to_smt x2) ($eo_to_smt_nat x3))",
                    true)));
  // sequences
  // for empty, that the Eunoia uses (Seq T) as an argument, whereas SMT uses T.
  addRecReduceSym("seq.empty", {kType}, kAny, "($smtx_empty_seq x1)");
  d_typeFullCase["seq.empty"] = "($smtx_typeof_guard_inhabited x1 ($tsm_Seq x1))";
  d_auxDef["seq.empty"] = R"(
(program $eo_to_smt_seq.empty ((T $smt_Type))
  :signature ($smt_Type) $smt_Term
  (
  (($eo_to_smt_seq.empty ($tsm_Seq T)) ($sm_seq.empty T))
  (($eo_to_smt_seq.empty T) $sm_none)
  )
))";
  d_eoToSmtFullCase["seq.empty"] = "($eo_to_smt_seq.empty ($eo_to_smt_type x1))";
  addRecReduceSym("seq.unit", {kAny}, d_kSeq, "($smtx_seq_unit e1)");
  d_typeFullCase["seq.unit"] = smtGuardType1("($smtx_typeof x1)", "($tsm_Seq ($smtx_typeof x1))");
  addRecReduceSym("seq.nth", {d_kSeq, kInt}, kAny, "($smtx_seq_nth M e1 e2)");
  addAuxTypeProgram("seq.nth", {d_kSeq, kInt}, "x1");
  // sets
  // (Set T) is modelled as (Array T Bool).
  addTypeSym("Set", {kType});
  // for empty, that the Eunoia uses (Set T) as an argument, whereas SMT uses T.
  addRecReduceSym("set.empty", {kType}, kAny, "($smtx_empty_set x1)");
  d_typeFullCase["set.empty"] = "($smtx_typeof_guard_inhabited x1 ($tsm_Set x1))";
  d_auxDef["set.empty"] = R"(
(program $eo_to_smt_set.empty ((T $smt_Type))
  :signature ($smt_Type) $smt_Term
  (
  (($eo_to_smt_set.empty ($tsm_Set T)) ($sm_set.empty T))
  (($eo_to_smt_set.empty T) $sm_none)
  )
))";
  d_eoToSmtFullCase["set.empty"] = "($eo_to_smt_set.empty ($eo_to_smt_type x1))";
  addTermReduceSym("set.singleton", {kAny}, d_kSet, "($smtx_set_singleton x1)");
  d_typeFullCase["set.singleton"] = smtGuardType1("($smtx_typeof x1)", "($tsm_Set ($smtx_typeof x1))");
  addTermReduceSym("set.inter", {d_kSet, d_kSet}, d_kSet, "($smtx_set_inter x1 x2)");
  addTermReduceSym("set.minus", {d_kSet, d_kSet}, d_kSet, "($smtx_set_minus x1 x2)");
  addTermReduceSym("set.union", {d_kSet, d_kSet}, d_kSet, "($smtx_set_union x1 x2)");
  addTermReduceSym(
      "set.member", {kAny, d_kSet}, kBool, "($smtx_map_select x2 x1)");
  addAuxTypeProgram("set.member", {kAny, d_kSet}, smtGuardType("($smt_builtin_Teq x1 x2)", "$tsm_Bool"));
  addTermReduceSym(
      "set.subset", {d_kSet, d_kSet}, kBool, "(= (set.inter x1 x2) x1)");
  std::stringstream ssSetsChoose;
  ssSetsChoose
      << "(eo::define ((T ($eo_to_smt_type ($eo_typeof (set.choose x1))))) ";
  ssSetsChoose << "(eo::define ((i ($sm_Var $smt_builtin_str_vname T))) ";
  ssSetsChoose << "($sm_apply ($sm_choice $smt_builtin_str_vname T) ";
  ssSetsChoose << smtToSmtEmbed("(set.member i ($eo_to_smt x1))", true)
               << ")))";
  addEunoiaReduceSym("set.choose", {kAny, kAny}, ssSetsChoose.str());
  std::stringstream ssSetsIsSingleton;
  ssSetsIsSingleton
      << "(eo::define (($T ($eo_to_smt_type ($eo_typeof (set.choose x1))))) ";
  ssSetsIsSingleton << "(eo::define ((i ($sm_Var $smt_builtin_str_vname $T))) ";
  ssSetsIsSingleton << "($sm_apply ($sm_exists $smt_builtin_str_vname $T) ";
  ssSetsIsSingleton << smtToSmtEmbed("(= ($eo_to_smt x1) (set.singleton i))",
                                     true)
                    << ")))";
  addEunoiaReduceSym("set.is_singleton", {kAny}, ssSetsIsSingleton.str());
  // more concise?
  // addEunoiaReduceSym("set.is_singleton", {kT}, "($eo_to_smt (= x1
  // (set.singleton (set.choose x1))))");
  std::stringstream ssSetsDiff;
  ssSetsDiff << "(eo::define ((T ($eo_to_smt_type ($eo_typeof (@sets_deq_diff "
                "x1 x2))))) ";
  ssSetsDiff << "(eo::define ((i ($sm_Var $smt_builtin_str_vname T))) ";
  ssSetsDiff << "($sm_apply ($sm_choice $smt_builtin_str_vname T) ";
  ssSetsDiff << smtToSmtEmbed(
      "(not (= (set.member i ($eo_to_smt x1)) (set.member i ($eo_to_smt x2))))",
      true) << ")))";
  addEunoiaReduceSym("@sets_deq_diff", {kAny, kAny}, ssSetsDiff.str());
  addEunoiaReduceSym("set.is_empty", {kAny},
                     smtToSmtEmbed("(= ($eo_to_smt x1) (set.empty ($smtx_typeof ($eo_to_smt x1))))", true));
  std::stringstream ssInsert;
  ssInsert << "(eo::define (($e ($eo_to_smt (set.insert x2 x3)))) ";
  ssInsert << smtToSmtEmbed("(set.union (set.singleton ($eo_to_smt x1)) $e)",
                            true)
           << ")";
  addEunoiaReduceSym("set.insert", {kList, kT}, ssInsert.str());
  d_specialCases["set.insert"].emplace_back("(set.insert $eo_List_nil x1)",
                                            "($eo_to_smt x1)");
  //   bitvectors
  addEunoiaReduceSym(
      "bvite",
      {kBitVec, kBitVec, kBitVec},
      smtToSmtEmbed(
          "(ite (= ($eo_to_smt x1) #b1) ($eo_to_smt x2) ($eo_to_smt x3))",
          true));
  addTermReduceSym("bvcomp", {kBitVec, kBitVec}, d_kBit, "(ite (= x1 x2) #b1 #b0)");
  addEunoiaReduceSym(
      "bvultbv",
      {kBitVec, kBitVec},
      smtToSmtEmbed("(ite (bvult ($eo_to_smt x1) ($eo_to_smt x2)) #b1 #b0)",
                    true));
  addEunoiaReduceSym(
      "bvsltbv",
      {kBitVec, kBitVec},
      smtToSmtEmbed("(ite (bvslt ($eo_to_smt x1) ($eo_to_smt x2)) #b1 #b0)",
                    true));
  //addLitSym("@bvsize", {kBitVec}, kInt, "x1");
  addEunoiaReduceSym("@bvsize", {kBitVec}, "($sm_numeral ($smtx_bv_sizeof_type ($smtx_typeof ($eo_to_smt x1))))");
  addEunoiaReduceSym(
      "bvredor",
      {kBitVec},
      smtToSmtEmbed(
          "(bvnot (bvcomp ($eo_to_smt x1) ($sm_binary ($smtx_bv_sizeof_type ($smtx_typeof ($eo_to_smt x1))) $smt_builtin_z_zero)))",
          true));
  addEunoiaReduceSym(
      "bvredand",
      {kBitVec},
      smtToSmtEmbed(
          "(bvcomp ($eo_to_smt x1) (bvnot ($sm_binary ($smtx_bv_sizeof_type ($smtx_typeof ($eo_to_smt x1))) $smt_builtin_z_zero)))",
          true));
  d_auxDef["@bv"] = R"(
(program $eo_to_smt_@bv
  ((x1 $smt_builtin_Int)(x2 $smt_builtin_Int) (t1 $smt_Term) (t2 $smt_Term))
  :signature ($smt_Term $smt_Term) $smt_Term
  (
  (($eo_to_smt_@bv ($sm_numeral x1) ($sm_numeral x2))
    ($smt_builtin_ite ($smt_builtin_z_<= $smt_builtin_z_zero x2) ($sm_binary_mod_w x2 x1) $sm_none))
  (($eo_to_smt_@bv t1 t2) $sm_none)
  )
))";
  addEunoiaReduceSym("@bv", {d_kIntQuote, d_kIntQuote}, "($eo_to_smt_@bv ($eo_to_smt x1) ($eo_to_smt x2))");
  addEunoiaReduceSym(
      "@bit",
      {kInt, kBitVec},
      smtToSmtEmbed("(extract ($eo_to_smt x1) ($eo_to_smt x1) ($eo_to_smt x2))",
                    true));
  addEunoiaReduceSym(
      "@from_bools",
      {kBool, kBitVec},
      smtToSmtEmbed("(concat (ite ($eo_to_smt x1) #b1 #b0) ($eo_to_smt x2))",
                    true));
  // datatypes
  addEunoiaReduceSym(
      "Tuple",
      {kT, kT},
      "($eo_to_smt_type_tuple ($eo_to_smt_type x1) ($eo_to_smt_type x2))",
      true);
  addEunoiaReduceSym("UnitTuple",
                     {},
                     "($tsm_Datatype $smt_builtin_str_tuple_name ($dt_sum "
                     "$dtc_unit $dt_null))",
                     true);
  addEunoiaReduceSym("tuple.select",
                     {kT, kT},
                     "($eo_to_smt_tuple_select ($eo_to_smt_type ($eo_typeof "
                     "x2)) ($eo_to_smt x1) ($eo_to_smt x2))");
  addEunoiaReduceSym("tuple.update",
                     {kInt, kT, kT},
                     "($eo_to_smt_tuple_update ($eo_to_smt_type ($eo_typeof "
                     "x2)) ($eo_to_smt x1) ($eo_to_smt x2) ($eo_to_smt x3))");
  addEunoiaReduceSym("tuple",
                     {kT, kT},
                     "($sm_apply ($eo_to_smt_tuple_app_extend ($eo_to_smt x1) "
                     "($eo_to_smt_type ($eo_typeof x2))) ($eo_to_smt x2))");
  addEunoiaReduceSym("tuple.unit",
                     {},
                     "($sm_DtCons $smt_builtin_str_tuple_name ($dt_sum "
                     "$dtc_unit $dt_null) $smt_builtin_n_zero)");
  addEunoiaReduceSym("is", {kT}, "($eo_to_smt_tester ($eo_to_smt x1))");
  addEunoiaReduceSym(
      "update",
      {kT, kT, kT},
      "($eo_to_smt_updater ($eo_to_smt x1) ($eo_to_smt x2) ($eo_to_smt x3))");
  addEunoiaReduceSym(
      "@strings_num_occur",
      {kT, kT},
      smtToSmtEmbed("(div (- (str.len ($eo_to_smt x1)) (str.len (str.replace_all ($eo_to_smt "
      "x1) ($eo_to_smt x2) (seq.empty $tsm_String)))) (str.len ($eo_to_smt x2)))", true));
  // ignore, not in proof rules (NOTE: could be SMT const?)
  d_symIgnore["@const"] = true;
  // FIXME: unhandled
  d_symIgnore["@strings_num_occur_re"] = true;
  d_symIgnore["@strings_occur_index"] = true;
  d_symIgnore["@strings_occur_index_re"] = true;
  d_symIgnore["@strings_replace_all_result"] = true;
  d_symIgnore["lambda"] = true;

  // for alethe
  addEunoiaReduceSym("@cl", {kT, kT}, "($eo_to_smt (or x1 x2))");
  addEunoiaReduceSym("@empty_cl", {kT, kT}, "($sm_bool $smt_builtin_false)");
  // alethe unhandled
  d_symIgnore["choice"] = true;
  d_symIgnore["@let"] = true;
  d_symIgnore["@ctx"] = true;
  d_symIgnore["@var"] = true;
  d_symIgnore["@Substitute"] = true;
  d_symIgnore["@substitute"] = true;
  d_symIgnore["@Substitution"] = true;
  d_symIgnore["@substitution.nil"] = true;
  d_symIgnore["@substitution"] = true;
}

ModelSmt::~ModelSmt() {}

void ModelSmt::addTypeSym(const std::string& sym, const std::vector<Kind>& args)
{
  d_symIgnore[sym] = true;
  d_symTypes[sym] = args;
}

void ModelSmt::addConstFoldSym(const std::string& sym,
                               const std::vector<Kind>& args,
                               Kind ret)
{
  d_symConstFold[sym] = std::pair<std::vector<Kind>, Kind>(args, ret);
}

void ModelSmt::addLitBinSym(const std::string& sym,
                            const std::vector<Kind>& args,
                            const std::string& retWidth,
                            const std::string& retNum,
                            bool reqSameWidth)
{
  std::stringstream ssr;
  ssr << "($vsm_binary_mod_w " << retWidth << " " << retNum << ")";
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

                                Kind ret,
                                const std::string& retTerm)
{
  std::cout << "(echo \"trim-defs-cmd (depends " << sym << " " << retTerm
            << ")\")" << std::endl;
  // the specification is SMT syntax, convert to embedding names here
  addReduceSym(sym, args, ret, smtToSmtEmbed(retTerm));
}

void ModelSmt::addEunoiaReduceSym(const std::string& sym,
                                  const std::vector<Kind>& args,
                                  const std::string& retTerm,
                                  bool isType)
{
  std::cout << "(echo \"trim-defs-cmd (depends " << sym << " " << retTerm
            << ")\")" << std::endl;
  d_eoSymReduce[sym] = std::pair<std::vector<Kind>, std::string>(args, retTerm);
  if (isType)
  {
    d_eoSymReduceTypes.insert(sym);
  }
}

void ModelSmt::addReduceSym(const std::string& sym,
                            const std::vector<Kind>& args,
                            Kind ret,
                            const std::string& retTerm)
{
  d_symReduce[sym] =
      std::tuple<std::vector<Kind>, Kind, std::string>(args, ret, retTerm);
}

void ModelSmt::addRecReduceSym(const std::string& sym,
                               const std::vector<Kind>& args,
                               Kind ret,
                               const std::string& retTerm)
{
  d_recReduce.insert(sym);
  std::stringstream ss;
  std::stringstream ssend;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    if (args[i-1]!=Kind::TYPE)
    {
      ss << "(eo::define ((e" << i << " ($smtx_model_eval M x" << i << "))) ";
      ssend << ")";
    }
  }
  ss << retTerm << ssend.str();
  addReduceSym(sym, args, ret, ss.str());
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
  std::map<std::string, std::string>::iterator itax = d_auxDesugar.find(name);
  if (itax != d_auxDesugar.end())
  {
    d_desugarAux << itax->second << std::endl;
  }
  itax = d_auxSmtEval.find(name);
  if (itax != d_auxSmtEval.end())
  {
    d_modelEvalProgs << itax->second << std::endl;
  }
  itax = d_auxDef.find(name);
  if (itax != d_auxDef.end())
  {
    // append to definitions
    d_eoToSmtAux << itax->second << std::endl;
  }
  // maybe a constant fold symbol
  std::map<std::string, std::pair<std::vector<Kind>, Kind>>::iterator it =
      d_symConstFold.find(name);
  if (it != d_symConstFold.end())
  {
    printDecl(name, it->second.first, Kind::PARAM, nopqArgs);
    printTypeof(name, it->second.first, it->second.second);
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
    Kind ret = std::get<1>(its->second);
    printTypeof(name, args, ret);
    printDecl(name, args, Kind::PARAM, nopqArgs);
    printModelEvalCall(name, args);
    printLitReduce(name, args, ret, std::get<2>(its->second));
    return;
  }
  std::map<std::string,
           std::tuple<std::vector<Kind>, Kind, std::string>>::iterator itst =
      d_symReduce.find(name);
  if (itst != d_symReduce.end())
  {
    std::vector<Kind>& args = std::get<0>(itst->second);
    Kind ret = std::get<1>(itst->second);
    printTypeof(name, args, ret);
    std::string sret = std::get<2>(itst->second);
    printDecl(name, args, Kind::PARAM, nopqArgs);
    if (d_recReduce.find(name) != d_recReduce.end() || args.empty())
    {
      printModelEvalCallBase(name, args, sret);
    }
    else
    {
      printModelEvalCall(name, args);
      printTermReduce(name, args, sret);
    }
    return;
  }
  std::map<std::string, std::pair<std::vector<Kind>, std::string>>::iterator
      itost = d_eoSymReduce.find(name);
  if (itost != d_eoSymReduce.end())
  {
    std::vector<Kind>& args = itost->second.first;
    std::string ret = itost->second.second;
    if (d_eoSymReduceTypes.find(name) != d_eoSymReduceTypes.end())
    {
      printEvalCallBase(d_eoToSmtType, "$eo_to_smt_type", name, args, ret);
    }
    else
    {
      printEvalCallBase(d_eoToSmt, "$eo_to_smt", name, args, ret);
    }
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
    // intentionally ignored, or handled as special cases only
    return;
  }
  // This assertion is critical for soundness: if we do not know how to
  // interpret the symbol, we cannot claim this verification condition
  // accurately models SMT-LIB semantics.
  EO_FATAL() << "ERROR: no model semantics found for " << name;
  Assert(false) << "No model semantics found for " << name;
}

void ModelSmt::printDecl(const std::string& name,
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
    if (name == "Int" || name == "Real" || name == "Char" || name == "BitVec"
        || name == "Seq" || name == "RegLan" || name == "Array"
        || name == "Set")
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
  std::stringstream eoToSmtRetReqBegin;
  std::stringstream eoToSmtRetReqEnd;
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
      std::stringstream currT;
      currT << "($eo_to_smt_type x" << (i + 1) << ")";
      // type arguments are always opaque on the SMT level
      // this includes types as arguments to other types and types indexing
      // seq.empty and set.empty.
      stmp << "$smt_Type :opaque";
      macroOpqApply << " x" << (i + 1);
      eoToSmtPatArgs << " x" << (i + 1);
      eoToSmtRetArgs << " " << currT.str();
      if (ret == Kind::TYPE)
      {
        eoToSmtRetReqBegin << "($smtx_typeof_guard " << currT.str() << " ";
        eoToSmtRetReqEnd << ")";
      }
    }
    else if (ret == Kind::TYPE && args[i] == Kind::NUMERAL)
    {
      Assert(!printedOpq);
      // integer index on types are opaque (i.e. BitVec)
      stmp << "$smt_builtin_Int :opaque";
      macroOpqApply << " x" << (i + 1);
      eoToSmtPatArgs << " ($eot_numeral n" << (i + 1) << ")";
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
  std::string eoToSmtRet;
  std::map<std::string, std::string>::iterator itf = d_eoToSmtFullCase.find(name);
  if (itf!=d_eoToSmtFullCase.end())
  {
    eoToSmtRet = itf->second;
  }
  else
  {
    eoToSmtRet = sApply(macroName.str(), eoToSmtRetArgs.str());
  }
  if (ret == Kind::TYPE)
  {
    d_eoToSmtType << "  (($eo_to_smt_type " << eoToSmtPat << ") " << eoToSmtRetReqBegin.str() << eoToSmtRet << eoToSmtRetReqEnd.str()
                  << ")" << std::endl;
  }
  else
  {
    // if a term declaration, write the mapping in eo_to_smt
    d_eoToSmt << "  (($eo_to_smt " << eoToSmtPat << ") " << eoToSmtRet << ")"
              << std::endl;
  }
}

void ModelSmt::printEvalCallBase(std::ostream& out,
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
      out << " ($eo_List_cons ($eot_Var s T) x" << icount << ")";
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

void ModelSmt::printModelEvalCallBase(const std::string& name,
                                      const std::vector<Kind>& args,
                                      const std::string& ret)
{
  std::stringstream ss;
  ss << "$sm_" << name;
  printEvalCallBase(d_eval, "$smtx_model_eval M", ss.str(), args, ret);
}

void ModelSmt::printEunoiaReduce(const std::string& name,
                                 const std::vector<Kind>& args,
                                 const std::string& ret)
{
  // std::stringstream ss;
  // ss << "($eo_to_smt " << ret << ")";
  printEvalCallBase(d_eoToSmt, "$eo_to_smt", name, args, ret);
}

void ModelSmt::printModelEvalCall(const std::string& name,
                                  const std::vector<Kind>& args)
{
  std::stringstream callArgs;
  callArgs << "($smtx_model_eval_" << name;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    callArgs << " ($smtx_model_eval M x" << i << ")";
  }
  callArgs << ")";
  printModelEvalCallBase(name, args, callArgs.str());
}

void ModelSmt::printTermInternal(Kind k,
                                 const std::string& term,
                                 std::ostream& os)
{
  std::stringstream ret;
  if (d_kindToEoPrefix.find(k) != d_kindToEoPrefix.end())
  {
    ret << "($vsm_" << d_kindToEoPrefix[k] << " " << term << ")";
  }
  else
  {
    ret << term;
  }
  os << ret.str();
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
  std::stringstream opName;
  std::map<std::string, std::string>::iterator ito =
      d_overloadRevert.find(name);
  if (ito != d_overloadRevert.end())
  {
    // e.g. in spite of having name $eoo_-.2, we use "-" as the invocation.
    opName << ito->second;
  }
  else if (name.compare(0, 4, "str.")==0 && args[0]==d_kSeq)
  {
    // mismatch str.substr vs seq.extract
    std::string oname = name.substr(4);
    opName << "seq." << (oname=="substr" ? "extract" : oname);
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
      if (ka==Kind::STRING || ka==d_kSeq)
      {
        retArgs << " ($smt_apply_1 \"unpack_";
        retArgs << (ka==Kind::STRING ? "string" : "seq") << "\" x" <<tmpParamCount << ")";
      }
      else
      {
        retArgs << " x" << tmpParamCount;
      }
    }
    // print the return term
    Kind kr = kret == Kind::PARAM ? kas : kret;
    std::stringstream ssret;
    std::stringstream ssretEnd;
    if (kr==Kind::STRING || kr==d_kSeq)
    {
      ssret << " ($smt_apply_" << (kr==d_kSeq ? 2 : 1) << " \"pack_";
      ssret << (kr==Kind::STRING ? "string" : "seq");
      ssret << "\" ";
      if (kr==d_kSeq)
      {
        ssret << "($smtx_elem_typeof_seq_value x1) ";
      }
      ssretEnd << ")";
    }
    if (isOverloadArith)
    {
      ssret << "($smt_builtin_" << (kas == Kind::NUMERAL ? "z" : "q") << "_"
            << opName.str();
    }
    else if (opName.str() == "**_total")
    {
      ssret << "($smt_builtin_z_**_total";
    }
    else
    {
      ssret << "($smt_apply_" << args.size() << " \"" << opName.str() << "\"";
    }
    ssret << retArgs.str() << ")" << ssretEnd.str();
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

void ModelSmt::printTermReduce(const std::string& name,
                               const std::vector<Kind>& args,
                               const std::string& ret)
{
  std::stringstream progName;
  progName << "$smtx_model_eval_" << name;
  std::stringstream progCases;
  std::stringstream progParams;
  size_t paramCount = 0;
  // instantiate the arguments for the current schema and prepare the
  // argument list for the return term.
  std::vector<Kind> instArgs;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    instArgs.push_back(Kind::NONE);
  }
  // then print it on cases
  printAuxProgramCase(
      progName.str(), instArgs, ret, paramCount, progCases, progParams);
  printAuxProgram(progName.str(), instArgs, progCases, progParams);
}

void ModelSmt::printAuxProgram(const std::string& name,
                               const std::vector<Kind>& args,
                               std::stringstream& progCases,
                               std::stringstream& progParams)
{
  std::stringstream progSig;
  progSig << "(";
  bool needsDefault = false;
  for (Kind k : args)
  {
    if (k != Kind::NONE)
    {
      needsDefault = true;
      break;
    }
  }
  // make the default case as well
  if (needsDefault)
  {
    progCases << "  ((" << name;
    for (size_t i = 0, nargs = args.size(); i < nargs; i++)
    {
      progCases << " t" << (i + 1);
      progParams << " (t" << (i + 1) << " $smt_Value)";
    }
    progCases << ") $vsm_not_value)" << std::endl;
  }
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    if (i > 0)
    {
      progSig << " ";
    }
    progSig << "$smt_Value";
  }
  progSig << ") $smt_Value";
  d_modelEvalProgs << "(program " << name << std::endl;
  d_modelEvalProgs << "  (" << progParams.str() << ")" << std::endl;
  d_modelEvalProgs << "  :signature " << progSig.str() << std::endl;
  d_modelEvalProgs << "  (" << std::endl;
  d_modelEvalProgs << progCases.str();
  d_modelEvalProgs << "  )" << std::endl << ")" << std::endl;
  d_modelEvalProgsFwd << "(program " << name << " () :signature "
                      << progSig.str() << ")" << std::endl;
}

void ModelSmt::printAuxTypeProgram(const std::string& name,
                                   const std::vector<Kind>& args,
                                   const std::string& retType,
                                   std::stringstream& out)
{
  std::stringstream progName;
  progName << "$smtx_typeof_" << name;
  std::stringstream outParams;
  std::stringstream outSig;
  std::vector<Kind> defaultArgs;
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    outSig << (i > 0 ? " " : "");
    outSig << (args[i]==d_kIntQuote ? "$smt_Term" : "$smt_Type");
    defaultArgs.push_back(Kind::NONE);
  }
  std::stringstream outCases;
  size_t paramCount = 0;
  printAuxProgramCase(
      progName.str(), args, retType, paramCount, outCases, outParams, true);
  printAuxProgramCase(progName.str(),
                      defaultArgs,
                      "$tsm_none",
                      paramCount,
                      outCases,
                      outParams,
                      true);
  out << "(program $smtx_typeof_" << name << " (" << outParams.str() << ")"
      << std::endl;
  out << "  :signature (" << outSig.str() << ") $smt_Type" << std::endl;
  out << "  (" << std::endl;
  out << outCases.str();
  out << "  )" << std::endl;
  out << ")" << std::endl;
}

void ModelSmt::addAuxTypeProgram(const std::string& name,
                           const std::vector<Kind>& args,
                           const std::string& retType)
{
  std::stringstream out;
  printAuxTypeProgram(name, args, retType, out);
  d_typeCase[name] = out.str();
}

void ModelSmt::addAuxIsListNil(const std::string& name, const std::string& ret)
{
  // if not using forward declarations for non-ground nil, return
  if (!optionFwdDeclIsListNilNground())
  {
    return;
  }
  std::stringstream ssp;
  ssp << "$eo_is_list_nil_" << name;
  std::stringstream ss;
  ss << "(program " << ssp.str() << " ((T Type) (x1 T))" << std::endl;
  ss << "  :signature (T) Bool" << std::endl;
  ss << "  (" << std::endl;
  ss << "  ((" << ssp.str() << " x1) " << ret << ")" << std::endl;
  ss << "  )" << std::endl;
  ss << ")" << std::endl;
  d_auxDesugar[name] = ss.str();
}

void ModelSmt::printAuxNatRecProgram(const std::string& name,
                                     const std::vector<Kind>& args,
                                     const std::string& zeroRet,
                                     const std::string& succRet)
{
  std::stringstream out;
  std::stringstream progName;
  progName << "$smtx_model_eval_" << name << "_rec";
  out << "(program " << progName.str() << " ((n $smt_builtin_Nat)";
  std::stringstream cases;
  for (size_t i = 0; i < 2; i++)
  {
    std::stringstream ssp;
    ssp << progName.str() << " "
        << (i == 0 ? "$smt_builtin_n_zero" : "($smt_builtin_n_succ n)");
    size_t paramCount = 0;
    std::string ret = (i == 0 ? zeroRet : succRet);
    printAuxProgramCase(ssp.str(), args, ret, paramCount, cases, out);
  }
  bool needsDefault = false;
  for (Kind k : args)
  {
    if (k != Kind::NONE)
    {
      needsDefault = true;
      break;
    }
  }
  if (needsDefault)
  {
    cases << "  ((" << progName.str() << " n";
    for (size_t i = 0, nargs = args.size(); i < nargs; i++)
    {
      cases << " t" << (i + 1);
      out << " (t" << (i + 1) << " $smt_Value)";
    }
    cases << ") $vsm_not_value)" << std::endl;
  }
  out << ")" << std::endl;
  out << "  :signature ($smt_builtin_Nat";
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    out << " $smt_Value";
  }
  out << ") $smt_Value" << std::endl;
  out << "(" << std::endl;
  out << cases.str();
  out << "  )" << std::endl << ")" << std::endl;
  d_auxSmtEval[name] = out.str();
}

bool ModelSmt::printTypeInternal(const std::string& name,
                                 Kind k,
                                 std::ostream& out)
{
  std::map<std::string, std::string>::iterator itc = d_typeRetCase.find(name);
  if (itc != d_typeRetCase.end())
  {
    out << itc->second;
    return true;
  }
  if (k == Kind::NUMERAL)
  {
    out << "$tsm_Int";
    return true;
  }
  else if (k == Kind::RATIONAL)
  {
    out << "$tsm_Real";
    return true;
  }
  else if (k == Kind::BOOLEAN)
  {
    out << "$tsm_Bool";
    return true;
  }
  else if (k == Kind::STRING)
  {
    out << "$tsm_String";
    return true;
  }
  else if (k == Kind::EVAL_TO_STRING)
  {
    out << "$tsm_RegLan";
    return true;
  }
  else if (k==d_kBit)
  {
    out << "($tsm_BitVec $smt_builtin_z_one)";
    return true;
  }
  return false;
}

void ModelSmt::printTypeof(const std::string& name,
                           const std::vector<Kind>& args,
                           Kind ret)
{
  d_smtTypeof << "  (($smtx_typeof " << (args.empty() ? "" : "(") << "$sm_" << name;
  std::stringstream ssArgs;
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    d_smtTypeof << " x" << (i + 1);
    if (args[i]==d_kIntQuote)
    {
      ssArgs << " x" << (i + 1);
    }
    else
    {
      ssArgs << " ($smtx_typeof x" << (i + 1) << ")";
    }
  }
  d_smtTypeof << (args.empty() ? "" : ")") << ") ";
  std::map<std::string, std::string>::iterator itc = d_typeFullCase.find(name);
  if (itc != d_typeFullCase.end())
  {
    d_smtTypeof << itc->second << ")" << std::endl;
    return;
  }
  itc = d_typeCase.find(name);
  if (itc != d_typeCase.end())
  {
    // print the auxiliary prgoram
    d_smtTypeofAux << itc->second << std::endl;
    // print the call to that program
    d_smtTypeof << " ($smtx_typeof_" << name;
    d_smtTypeof << ssArgs.str() << "))";
    return;
  }
  Kind kuniform = args.empty() ? Kind::NONE : args[0];
  for (Kind k : args)
  {
    if (k!=kuniform)
    {
      kuniform = Kind::NONE;
      break;
    }
  }
  if (kuniform == Kind::BINARY)
  {
    std::stringstream rets;
    if (ret == Kind::BINARY || ret == Kind::ANY)
    {
      d_smtTypeof << "($smtx_typeof_bv_op_" << args.size() << ssArgs.str() << "))"
                  << std::endl;
      return;
    }
    else if (printTypeInternal(name, ret, rets))
    {
      d_smtTypeof << "($smtx_typeof_bv_op_" << args.size() << "_ret" << ssArgs.str() << " "
                  << rets.str() << "))" << std::endl;
      return;
    }
  }
  else if (kuniform == d_kSet)
  {
    std::stringstream rets;
    if (ret == d_kSet || ret == Kind::ANY)
    {
      d_smtTypeof << "($smtx_typeof_sets_op_" << args.size() << ssArgs.str() << "))"
                  << std::endl;
      return;
    }
    else if (printTypeInternal(name, ret, rets))
    {
      d_smtTypeof << "($smtx_typeof_sets_op_" << args.size() << "_ret" << ssArgs.str() << " "
                  << rets.str() << "))" << std::endl;
      return;
    }
  }
  if (kuniform == d_kSeq)
  {
    if (ret == d_kSeq || ret == Kind::ANY)
    {
      d_smtTypeof << "($smtx_typeof_seq_op_" << args.size() << ssArgs.str() << "))"
                  << std::endl;
      return;
    }
    std::stringstream rets;
    if (printTypeInternal(name, ret, rets))
    {
      d_smtTypeof << "($smtx_typeof_seq_op_" << args.size() << "_ret" << ssArgs.str() << " "
                  << rets.str() << "))" << std::endl;
      return;
    }
  }
  if (args.size() == 2 && kuniform == Kind::PARAM)
  {
    std::stringstream rets;
    if (ret==Kind::PARAM)
    {
      // mixed arithmetic
      d_smtTypeof << "($smtx_typeof_arith_overload_op_2" << ssArgs.str() << "))"
                << std::endl;
      return;
    }
    else if (printTypeInternal(name, ret, rets))
    {
      d_smtTypeof << "($smtx_typeof_arith_overload_op_2_ret" << ssArgs.str() << " "
                  << rets.str() << "))" << std::endl;
      return;
    }
  }
  std::stringstream ssRet;
  std::stringstream ssRetEnd;
  bool success = true;
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    Kind k = args[i];
    ssRet << "($smt_builtin_ite ($smt_builtin_Teq ($smtx_typeof x" << (i + 1)
          << ") ";
    if (!printTypeInternal("", k, ssRet))
    {
      success = false;
      break;
    }
    ssRet << ") ";
    ssRetEnd << " $tsm_none)";
  }
  if (!printTypeInternal(name, ret, ssRet))
  {
    success = false;
  }
  if (success)
  {
    d_smtTypeof << ssRet.str() << ssRetEnd.str();
  }
  else
  {
    d_smtTypeof << "$tsm_none";
  }
  d_smtTypeof << ")" << std::endl;
}

void ModelSmt::printAuxProgramCase(const std::string& name,
                                   const std::vector<Kind>& args,
                                   const std::string& ret,
                                   size_t& paramCount,
                                   std::ostream& progCases,
                                   std::ostream& progParams,
                                   bool isTypeProg)
{
  progCases << "  ((" << name;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    Kind ka = args[i - 1];
    if (paramCount > 1)
    {
      progParams << " ";
    }     
    if (isTypeProg)
    {
      if (ka == Kind::BINARY)
      {
        progCases << " ($tsm_BitVec x" << (paramCount + 1) << ")";
        progParams << " (x" << (paramCount + 1) << " $smt_builtin_Int)";
        paramCount++;
        continue;
      }
      else if (ka==d_kSet || ka==d_kSeq)
      {
        progCases << " ($tsm_" << (ka==d_kSet ? "Set" : "Seq") << " x" << (paramCount + 1) << ")";
        progParams << " (x" << (paramCount + 1) << " $smt_Type)";
        paramCount++;
        continue;
      }
      else if (ka==d_kArray)
      {
        progCases << " ($tsm_Array x" << (paramCount + 1) << " x" << (paramCount + 2) << ")";
        progParams << " (x" << (paramCount + 1) << " $smt_Type)";
        progParams << " (x" << (paramCount + 2) << " $smt_Type)";
        paramCount = paramCount + 2;
        continue;
      }
      else  if (ka == d_kIntQuote)
      {
        progCases << " ($sm_numeral x" << (paramCount + 1) << ")";
        progParams << " (x" << (paramCount + 1) << " $smt_builtin_Int)";
        paramCount++;
        continue;
      }
      progCases << " ";
      if (!printTypeInternal("", ka, progCases))
      {
        progParams << " (x" << (paramCount + 1) << " $smt_Type)";
        progCases << "x" << (paramCount + 1);
        paramCount++;
      }
      continue;
    }
    if (d_kindToEoPrefix.find(ka) != d_kindToEoPrefix.end())
    {
      paramCount++;
      progCases << " ($vsm_";
      if (ka == Kind::BINARY)
      {
        progCases << "binary x" << paramCount << " x" << (paramCount + 1)
                  << ")";
        progParams << "(x" << paramCount << " $smt_builtin_Int)";
        progParams << " (x" << (paramCount + 1) << " $smt_builtin_Int)";
        paramCount++;
        continue;
      }
      progCases << d_kindToEoPrefix[ka] << " x" << paramCount << ")";
      progParams << "(x" << paramCount;
      if (ka==d_kSeq)
      {
        progParams << " $smt_Seq";
      }
      else
      {
        progParams << " $smt_builtin_" << d_kindToType[ka];
      }
      progParams << ")";
    }
    else
    {
      paramCount++;
      progCases << " x" << paramCount;
      progParams << "(x" << paramCount << " $smt_Value)";
    }
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
  std::ifstream ins(getResourcePath("plugins/model_smt/model_smt.eo"));
  std::ostringstream sss;
  sss << ins.rdbuf();
  std::string finalSmt = sss.str();
  // plug in the evaluation cases handled by this plugin
  replace(finalSmt, "$SMT_EVAL_CASES$", d_eval.str());
  replace(finalSmt, "$SMT_EVAL_PROGS_FWD_DECL$", d_modelEvalProgsFwd.str());
  replace(finalSmt, "$SMT_EVAL_PROGS$", d_modelEvalProgs.str());
  replace(finalSmt, "$EO_TO_SMT_AUX$", d_eoToSmtAux.str());
  replace(finalSmt, "$EO_DESUGAR_AUX$", d_desugarAux.str());
  replace(finalSmt, "$EO_TO_SMT_CASES$", d_eoToSmt.str());
  replace(finalSmt, "$EO_TO_SMT_TYPE_CASES$", d_eoToSmtType.str());
  replace(finalSmt, "$SMT_TERM_CONSTRUCTORS$", d_smtTerms.str());
  replace(finalSmt, "$SMT_TYPE_CONSTRUCTORS$", d_smtTypes.str());
  replace(finalSmt, "$SMT_TYPEOF_CASES$", d_smtTypeof.str());
  replace(finalSmt, "$SMT_TYPEOF_AUX$", d_smtTypeofAux.str());

  std::string outPath = getOutputPath("plugins/model_smt/model_smt_gen.eo");
  std::ofstream oute(outPath);
  oute << finalSmt;
}

}  // namespace ethos
