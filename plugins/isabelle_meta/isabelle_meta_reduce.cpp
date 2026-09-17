/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "isabelle_meta_reduce.h"

#include <algorithm>
#include <functional>
#include <iomanip>
#include <sstream>

#include "literal.h"

namespace ethos {
namespace {

std::string application(const std::string& head,
                        const std::vector<std::string>& args)
{
  if (args.empty()) return head;
  std::string result = "(" + head;
  for (const auto& arg : args) result += " " + arg;
  return result + ")";
}

std::string tuple(const std::vector<std::string>& args)
{
  if (args.empty()) return "()";
  if (args.size() == 1) return args[0];
  std::string result = "(";
  for (size_t i = 0; i < args.size(); ++i)
    result += (i == 0 ? "" : ", ") + args[i];
  return result + ")";
}

std::string some(const std::string& value) { return "(Some " + value + ")"; }

// Strings use the embedding's Unicode code points, not Isabelle's byte chars.
std::string stringValue(const std::vector<unsigned>& chars)
{
  std::string result = "[";
  for (size_t i = 0; i < chars.size(); ++i)
    result += (i == 0 ? "" : ", ") + std::to_string(chars[i]);
  return result + "]";
}

// Strongly connected components, with dependencies before their users.
// Edges outside the graph are native types, supplied by HOL.
std::vector<std::vector<std::string>> components(
    const std::map<std::string, std::set<std::string>>& graph)
{
  std::vector<std::vector<std::string>> result;
  std::map<std::string, size_t> index, low;
  std::vector<std::string> stack;
  std::set<std::string> active;
  size_t counter = 0;
  std::function<void(const std::string&)> visit = [&](const std::string& name) {
    index[name] = low[name] = ++counter;
    stack.push_back(name);
    active.insert(name);
    for (const auto& dep : graph.at(name))
    {
      if (!graph.count(dep)) continue;
      if (!index.count(dep))
      {
        visit(dep);
        low[name] = std::min(low[name], low[dep]);
      }
      else if (active.count(dep))
        low[name] = std::min(low[name], index[dep]);
    }
    if (low[name] != index[name]) return;
    std::vector<std::string> group;
    do
    {
      group.push_back(stack.back());
      active.erase(stack.back());
      stack.pop_back();
    } while (group.back() != name);
    std::sort(group.begin(), group.end());
    result.push_back(group);
  };
  for (const auto& entry : graph)
    if (!index.count(entry.first)) visit(entry.first);
  return result;
}

}  // namespace

IsabelleMetaReduce::IsabelleMetaReduce(State& s) : MetaReducePlugin(s)
{
  d_typeToMetaKind["$eo_Term"] = MetaKind::EUNOIA;
  d_typeToMetaKind["$eo_Proof"] = MetaKind::PROOF;
  d_typeToMetaKind["$eo_Rule"] = MetaKind::CHECKER_RULE;
  d_typeToMetaKind["$eo_Cmd"] = MetaKind::CHECKER_CMD;
  d_prefixToMetaKind["r"] = MetaKind::CHECKER_RULE;
  d_prefixToMetaKind["cmd"] = MetaKind::CHECKER_CMD;
  d_datatypes["Term"] = {
      "Term_Type", "Term_Bool", "Term_FunType", "Term_Apply Term Term"};
  d_datatypes["Proof"] = {"Proof_pf Term", "Proof_Stuck"};
  d_datatypes["CRule"] = {};
  d_datatypeDeps["Term"].insert("Term");
  d_datatypeDeps["Proof"].insert("Term");
}

std::string IsabelleMetaReduce::identifier(const std::string& name)
{
  // Escape underscores too, so the encoding is injective, including quoted
  // EO names and overloaded operators. Prefixes at call sites ensure that
  // identifiers cannot start with a digit or be an Isabelle keyword.
  if (name.empty()) return "_empty";
  std::ostringstream out;
  for (unsigned char c : name)
  {
    if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9'))
      out << c;
    else
      out << "_x" << std::hex << std::setw(2) << std::setfill('0')
          << static_cast<unsigned>(c);
  }
  return out.str();
}

bool IsabelleMetaReduce::isBuiltinMetaSymbol(const std::string& name) const
{
  return name.compare(0, 8, "$native_") == 0
         || d_typeToMetaKind.count(name) != 0;
}

std::string IsabelleMetaReduce::type(const Expr& t) const
{
  MetaKind k = getTypeMetaKindFor(t, MetaKind::EUNOIA, true);
  if (k == MetaKind::EO_EMBED || k == MetaKind::CHECKER_EMBED)
    return getEmbedTypeName(getEmbedTypeApp(t));
  switch (k)
  {
    case MetaKind::EUNOIA: return "Term";
    case MetaKind::PROOF: return "Proof";
    case MetaKind::CHECKER_RULE: return "CRule";
    case MetaKind::CHECKER_CMD: return "CCmd";
    case MetaKind::SMT_BUILTIN:
    {
      if (t.getKind() == Kind::APPLY_OPAQUE && t.getNumChildren() == 2)
      {
        const std::string n = getName(t[1]);
        if (n == "Bool") return "bool";
        if (n == "Int") return "int";
        if (n == "Nat") return "nat";
        if (n == "Rat") return "rat";
        if (n == "String") return "nat list";
        if (n == "Char") return "nat";
        if (n.compare(0, 6, "UserOp") == 0
            && n.find_first_not_of("0123456789", 6) == std::string::npos)
          return n;
      }
      break;
    }
    default: break;
  }
  EO_FATAL() << "IsabelleMetaReduce: unsupported type " << t;
  return "";
}

std::string IsabelleMetaReduce::constructor(const Expr& e) const
{
  if (getName(e) == "$eo_pf") return "Proof_pf";
  std::string name;
  getMetaKindFor(e, name);
  size_t arity = indexedArity(e);
  if (arity > 0)
  {
    std::string n = std::to_string(arity);
    return "Term_UOp" + n + " UserOp" + n + "_Op_" + identifier(name);
  }
  if (isUserOperator(e)) return "(Term_UOp UserOp_Op_" + identifier(name) + ")";
  // Ordinary function symbols are nullary Term constructors. Only opaque
  // arguments become fields, exactly as in lean-meta.
  return type(e.getType()) + (isEmbedCons(e) ? "_" : "_Op_") + identifier(name);
}

size_t IsabelleMetaReduce::indexedArity(const Expr& e) const
{
  // Indexed signature operators must use the same UOp constructors as the
  // embedding's generic closedness traversal, just as they do in lean-meta.
  return !isEmbedCons(e) && type(e.getType()) == "Term"
                 && d_state.getAttributeKind(e.getValue()) == Attr::OPAQUE
             ? e.getType().getNumChildren() - 1
             : 0;
}

bool IsabelleMetaReduce::isUserOperator(const Expr& e) const
{
  return !isEmbedCons(e) && type(e.getType()) == "Term"
         && d_state.getAttributeKind(e.getValue()) != Attr::OPAQUE;
}

void IsabelleMetaReduce::finalizeDecl(const Expr& e)
{
  if (!beginFinalizeDecl(e) || isBuiltinMetaSymbol(getName(e))
      || getName(e) == "$eo_pf")
    return;
  const std::string name = getName(e);
  if (name == "$emb_Type" || name == "$emb_Bool" || name == "$emb_FunType"
      || name == "$emb_Apply")
    return;
  Expr t = e.getType();
  if (isUserOperator(e))
  {
    if (!d_datatypes.count("UserOp"))
    {
      d_datatypes["Term"].push_back("Term_UOp \"UserOp\"");
      d_datatypeDeps["Term"].insert("UserOp");
    }
    d_datatypes["UserOp"].push_back("UserOp_Op_" + identifier(name));
    d_operatorAliases["Term_Op_" + identifier(name)] = constructor(e);
    return;
  }
  size_t arity = indexedArity(e);
  if (arity > 0)
  {
    std::string n = std::to_string(arity);
    d_datatypes["UserOp" + n].push_back("UserOp" + n + "_Op_" + identifier(name));
    // The generic traversal may have been trimmed away for a small input.
    // Ensure its constructor still exists for any indexed operator we emit.
    std::string cons = "Term_UOp" + n + " \"UserOp" + n + "\"";
    for (size_t i = 0; i < arity; ++i) cons += " \"Term\"";
    auto& terms = d_datatypes["Term"];
    if (std::find(terms.begin(), terms.end(), cons) == terms.end())
      terms.push_back(cons);
    d_datatypeDeps["Term"].insert("UserOp" + n);
    return;
  }
  std::string decl = constructor(e);
  if (d_state.getAttributeKind(e.getValue()) == Attr::OPAQUE)
  {
    for (size_t i = 0; i + 1 < t.getNumChildren(); ++i)
    {
      Expr arg = t[i];
      if (arg.getKind() == Kind::QUOTE_TYPE)
      {
        Expr quoted = arg[0];
        arg = d_tc.getType(quoted);
      }
      decl += " \"" + type(arg) + "\"";
      d_datatypeDeps[type(t)].insert(type(arg));
    }
  }
  auto& constructors = d_datatypes[type(t)];
  if (std::find(constructors.begin(), constructors.end(), decl) == constructors.end())
    constructors.push_back(decl);
}

void IsabelleMetaReduce::defineProgram(const Expr& v, const Expr& prog)
{
  if (!prog.isNull()) d_programs[getName(v)] = {v, prog, false};
}

void IsabelleMetaReduce::define(const std::string& name, const Expr& e)
{
  if (name.compare(0, 4, "$eo_") != 0 || !getEmbedTypeApp(e).isNull()) return;
  Expr symbol, prog;
  if (buildLambdaDefineProgram(name, e, symbol, prog))
    d_programs[name] = {symbol, prog, true};
  else
  {
    Expr value = e;
    symbol = d_state.mkSymbol(Kind::PROGRAM_CONST, name, d_tc.getType(value));
    d_programs[name] = {symbol, e, true};
  }
}

bool IsabelleMetaReduce::echo(const std::string& msg)
{
  if (msg.compare(0, 14, "isabelle-meta ") == 0)
  {
    std::istringstream in(msg.substr(14));
    std::string name;
    in >> name;
    d_rules.insert(name);
    return false;
  }
  return msg.compare(0, 12, "lean-parser-") != 0;
}

std::string IsabelleMetaReduce::atom(const Expr& e) const
{
  switch (e.getKind())
  {
    case Kind::PARAM: return "v_" + identifier(getName(e));
    case Kind::CONST: return constructor(e);
    case Kind::TYPE: return "Term_Type";
    case Kind::BOOL_TYPE: return "Term_Bool";
    default: break;
  }
  const Literal* l = e.getValue()->asLiteral();
  if (l != nullptr)
  {
    switch (e.getKind())
    {
      case Kind::BOOLEAN:
        return l->d_bool ? "(Term_Boolean True)" : "(Term_Boolean False)";
      case Kind::NUMERAL: return "(Term_Numeral (" + l->d_int.toString() + "))";
      case Kind::RATIONAL:
      {
        std::string value = l->toString();
        return "(Term_Rational (" + value + "))";
      }
      case Kind::STRING:
        return "(Term_String " + stringValue(l->d_str.getVec()) + ")";
      case Kind::BINARY:
        return "(Term_Binary " + std::to_string(l->d_bv.getSize()) + " "
               + l->d_bv.getValue().toString() + ")";
      default: break;
    }
  }
  EO_FATAL() << "IsabelleMetaReduce: unsupported atomic term " << e;
  return "";
}

std::string IsabelleMetaReduce::native(
    const std::string& name, const std::vector<std::string>& args) const
{
  if (args.empty())
  {
    if (name == "true") return "True";
    if (name == "false") return "False";
    if (name == "nat.zero") return "0";
    size_t digits = !name.empty() && name[0] == '-' ? 1 : 0;
    if (digits < name.size()
        && name.find_first_not_of("0123456789", digits) == std::string::npos)
      return "(" + name + ")";
    if (name.size() >= 2 && name.front() == '"' && name.back() == '"')
    {
      std::vector<unsigned> chars;
      for (size_t i = 1; i + 1 < name.size(); ++i)
      {
        if (static_cast<unsigned char>(name[i]) >= 128 || name[i] == '"'
            || name[i] == '\\')
          EO_FATAL() << "IsabelleMetaReduce: unsupported native string "
                     << name;
        chars.push_back(static_cast<unsigned char>(name[i]));
      }
      return stringValue(chars);
    }
  }
  const std::map<std::string, std::string> binary = {{"teq", "="},
                                                     {"streq", "="},
                                                     {"zeq", "="},
                                                     {"qeq", "="},
                                                     {"nateq", "="},
                                                     {"iff", "="},
                                                     {"and", "\\<and>"},
                                                     {"or", "\\<or>"},
                                                     {"zleq", "\\<le>"},
                                                     {"qleq", "\\<le>"},
                                                     {"zlt", "<"},
                                                     {"qlt", "<"},
                                                     {"zplus", "+"},
                                                     {"qplus", "+"},
                                                     {"zmult", "*"},
                                                     {"qmult", "*"},
                                                     {"qdiv_total", "/"},
                                                     {"mk_rational", "/"}};
  auto b = binary.find(name);
  if (b != binary.end() && args.size() == 2)
  {
    if (name == "mk_rational")
      return "(of_int " + args[0] + " / of_int " + args[1] + ")";
    return "(" + args[0] + " " + b->second + " " + args[1] + ")";
  }
  const std::map<std::string, std::string> unary = {{"not", "Not"},
                                                    {"zneg", "uminus"},
                                                    {"qneg", "uminus"},
                                                    {"zabs", "abs"},
                                                    {"qabs", "abs"},
                                                    {"nat.succ", "Suc"},
                                                    {"int.to_nat", "nat"},
                                                    {"nat.to_int", "int"},
                                                    {"to_real", "of_int"}};
  auto u = unary.find(name);
  if (u != unary.end() && args.size() == 1) return application(u->second, args);
  if (name == "int.pow2" && args.size() == 1)
    return application("eoc_pow2", args);
  if ((name == "zexp_total" || name == "qexp_total") && args.size() == 2)
    return "(if " + args[1] + " < 0 then 0 else " + args[0] + " ^ nat "
           + args[1] + ")";
  if (name == "int_log" && args.size() == 2)
    return application("eoc_int_log", args);
  if (name == "to_int" && args.size() == 1)
    return "(fst (quotient_of " + args[0] + ") div snd (quotient_of "
           + args[0] + "))";
  if (name == "str.len" && args.size() == 1)
    return "(int (length " + args[0] + "))";
  if (name == "str.++" && args.size() == 2)
    return "(" + args[0] + " @ " + args[1] + ")";
  if (name == "str.substr" && args.size() == 3)
    return "(if " + args[1] + " < 0 then [] else take (nat " + args[2]
           + ") (drop (nat " + args[1] + ") " + args[0] + "))";
  if (name == "str.indexof" && args.size() == 3)
    return application("eoc_str_indexof", args);
  if (name == "str.to_code" && args.size() == 1)
    return "(case " + args[0] + " of [c] => (if c < 196608 then int c else -1)"
           " | _ => -1)";
  if (name == "str.from_code" && args.size() == 1)
    return "(if 0 <= " + args[0] + " \\<and> " + args[0]
           + " < 196608 then [nat " + args[0] + "] else [])";
  if (name == "tcmp" && args.size() == 2)
    return "(eoc_key_less (key_Term " + args[0] + ") (key_Term " + args[1] + "))";
  // EO/Lean use Euclidean division, including with a negative divisor.
  if (name == "div_total" && args.size() == 2)
    return "(if " + args[1] + " < 0 then - (" + args[0] + " div (- " + args[1]
           + ")) else " + args[0] + " div " + args[1] + ")";
  if (name == "mod_total" && args.size() == 2)
    return "(" + args[0] + " mod abs " + args[1] + ")";
  if ((name == "binary_and" || name == "binary_or" || name == "binary_xor")
      && args.size() == 3)
  {
    const std::string op = name == "binary_and" ? "AND"
                          : name == "binary_or" ? "OR" : "XOR";
    return "((" + args[1] + " " + op + " " + args[2] + ") mod (2 ^ nat "
           + args[0] + "))";
  }
  if (name == "binary_not" && args.size() == 2)
    return "(eoc_pow2 " + args[0] + " - (1 + " + args[1] + "))";
  if (name == "binary_max" && args.size() == 1)
    return "(eoc_pow2 " + args[0] + " - 1)";
  if (name == "binary_concat" && args.size() == 4)
    return "(" + args[1] + " * eoc_pow2 " + args[2] + " + " + args[3] + ")";
  if (name == "binary_extract" && args.size() == 4)
    return "(" + args[1] + " div eoc_pow2 " + args[3] + ")";
  if (name == "ite" && args.size() == 3)
    return "(if " + args[0] + " then " + args[1] + " else " + args[2] + ")";
  EO_FATAL() << "IsabelleMetaReduce: unsupported native " << name << " in "
             << d_current;
  return "";
}

std::string IsabelleMetaReduce::call(const std::string& name,
                                     const std::vector<std::string>& args)
{
  if (d_programs.count(name) == 0)
    EO_FATAL() << "IsabelleMetaReduce: undefined program " << name
               << " called by " << d_current;
  d_calls[d_current].insert(name);
  return application("p_" + identifier(name) + " fuel", args);
}

std::string IsabelleMetaReduce::term(const Expr& e)
{
  if (e.getKind() == Kind::PROGRAM_CONST) return call(getName(e), {});
  if (e.getNumChildren() == 0) return some(atom(e));
  const bool nativeApp = isSmtApplyApp(e);
  const std::string nativeName = nativeApp ? getName(e[1]) : "";
  size_t start = nativeApp ? 2 : 0;
  std::string head;
  bool prog = false;
  if (!nativeApp)
  {
    if (isProgramApp(e))
    {
      head = getName(e[0]);
      start = 1;
      prog = true;
    }
    else if (e.getKind() == Kind::APPLY_OPAQUE)
    {
      head = atom(e[0]);
      start = 1;
    }
    else if (e.getKind() == Kind::APPLY)
    {
      head = e.isEvaluatable() ? "$eo_mk_apply" : "Term_Apply";
      prog = e.isEvaluatable();
    }
    else if (e.getKind() == Kind::FUNCTION_TYPE)
    { /* handled below */
    }
    else if (e.getKind() == Kind::VARIABLE)
      head = "Term_Var";
    else if (isLiteralOp(e.getKind()))
    {
      head = "$eo_" + kindToTerm(e.getKind()).substr(4);
      prog = true;
    }
    else
      EO_FATAL() << "IsabelleMetaReduce: unsupported expression " << e;
  }
  // The native ITE and EO's control forms evaluate only the selected branch.
  // In particular, exhaustion in an unselected branch must not reject a proof.
  if ((nativeApp && nativeName == "ite") || (prog && head == "$eo_ite"))
  {
    std::string cond = "tmp" + std::to_string(++d_fresh);
    std::string yes = term(e[start + 1]), no = term(e[start + 2]);
    std::string value =
        nativeApp ? "(if " + cond + " then " + yes + " else " + no + ")"
                  : "(if " + cond + " = Term_Boolean True then " + yes
                        + " else if " + cond + " = Term_Boolean False then "
                        + no + " else Some Term_Stuck)";
    return "(case " + term(e[start]) + " of None => None | Some " + cond
           + " => " + value + ")";
  }
  if (prog && head == "$eo_requires")
  {
    const std::string lhs = "tmp" + std::to_string(++d_fresh);
    const std::string rhs = "tmp" + std::to_string(++d_fresh);
    return "(case " + term(e[start]) + " of None => None | Some " + lhs
           + " => (case " + term(e[start + 1]) + " of None => None | Some "
           + rhs + " => (if " + lhs + " = " + rhs + " \\<and> " + lhs
           + " \\<noteq> Term_Stuck then " + term(e[start + 2])
           + " else Some Term_Stuck)))";
  }
  std::vector<std::string> args, values;
  for (size_t i = start; i < e.getNumChildren(); ++i)
  {
    std::string value = term(e[i]);
    if (value.compare(0, 6, "(Some ") == 0)
    {
      // Pure constructors, variables, and native applications cannot exhaust
      // fuel. Eliminating their option binds keeps large CPC rules tractable
      // for Isabelle's simplifier without changing the budget of any call.
      args.push_back(value.substr(6, value.size() - 7));
      values.emplace_back();
    }
    else
    {
      args.push_back("tmp" + std::to_string(++d_fresh));
      values.push_back(value);
    }
  }
  std::string result;
  if (nativeApp)
    result = some(native(nativeName, args));
  else if (e.getKind() == Kind::FUNCTION_TYPE)
  {
    if (args.size() != 2)
      EO_FATAL() << "IsabelleMetaReduce: non-curried type " << e;
    result = some("(Term_Apply (Term_Apply Term_FunType " + args[0] + ") "
                  + args[1] + ")");
  }
  else
    result = prog ? call(head, args) : some(application(head, args));
  for (size_t i = args.size(); i-- > 0;)
    if (!values[i].empty())
      result = "(case " + values[i] + " of None => None | Some " + args[i]
               + " => " + result + ")";
  return result;
}

std::string IsabelleMetaReduce::pattern(const Expr& e,
                                        std::set<Expr>& bound,
                                        std::vector<std::string>& guards)
{
  if (e.getKind() == Kind::PARAM)
  {
    std::string name = atom(e);
    if (bound.insert(e).second) return name;
    std::string fresh = "pat" + std::to_string(++d_fresh);
    guards.push_back(fresh + " = " + name);
    return fresh;
  }
  if (isSmtApplyApp(e))
  {
    std::string name = getName(e[1]);
    if (name == "true") return "True";
    if (name == "false") return "False";
    if (name == "nat.zero") return "0";
    if (name == "nat.succ" && e.getNumChildren() == 3)
      return "(Suc " + pattern(e[2], bound, guards) + ")";
    std::string fresh = "pat" + std::to_string(++d_fresh);
    // Numeric/string constants are tests, not constructor patterns in HOL.
    if (e.getNumChildren() != 2)
      EO_FATAL() << "IsabelleMetaReduce: unsupported native pattern " << e;
    guards.push_back(fresh + " = " + native(name, {}));
    return fresh;
  }
  if (e.getNumChildren() == 0)
  {
    if (e.getKind() == Kind::NUMERAL || e.getKind() == Kind::RATIONAL
        || e.getKind() == Kind::BINARY || e.getKind() == Kind::STRING)
    {
      std::string fresh = "pat" + std::to_string(++d_fresh);
      guards.push_back(fresh + " = " + atom(e));
      return fresh;
    }
    return atom(e);
  }
  std::string head;
  size_t start = 0;
  if (e.getKind() == Kind::APPLY)
    head = "Term_Apply";
  else if (e.getKind() == Kind::VARIABLE)
    head = "Term_Var";
  else if (e.getKind() == Kind::APPLY_OPAQUE)
  {
    head = atom(e[0]);
    start = 1;
  }
  else if (e.getKind() != Kind::FUNCTION_TYPE)
    EO_FATAL() << "IsabelleMetaReduce: unsupported pattern " << e;
  std::vector<std::string> args;
  for (size_t i = start; i < e.getNumChildren(); ++i)
    args.push_back(pattern(e[i], bound, guards));
  if (e.getKind() == Kind::FUNCTION_TYPE)
    return "(Term_Apply (Term_Apply Term_FunType " + args[0] + ") " + args[1]
           + ")";
  return application(head, args);
}

std::string IsabelleMetaReduce::programBody(const Program& p)
{
  const Expr& body = p.body;
  const Expr& t = p.symbol.getType();
  bool cases = body.getKind() == Kind::PROGRAM;
  size_t arity = cases ? t.getNumChildren() - 1 : 0;
  std::vector<std::string> args;
  bool checker = false;
  for (size_t i = 0; i < arity; ++i)
  {
    args.push_back("arg" + std::to_string(i));
    checker |=
        isCheckerMetaKind(getTypeMetaKindFor(t[i], MetaKind::EUNOIA, false));
  }
  std::string ret = type(cases ? t[arity] : t);
  std::string result =
      (ret == "Term" || ret == "Proof") ? some(ret + "_Stuck") : "None";
  if (!cases)
    result = term(body);
  else
    for (size_t i = body.getNumChildren(); i-- > 0;)
    {
      const Expr& hd = body[i][0];
      std::vector<std::string> pats, guards;
      std::set<Expr> bound;
      bool catchall = true;
      for (size_t j = 1; j < hd.getNumChildren(); ++j)
      {
        pats.push_back(pattern(hd[j], bound, guards));
        // Literal tests also become variables plus guards. Adding a wildcard
        // after such a variable is a redundant HOL case (an error in Isabelle).
        catchall &= pats.back().compare(0, 2, "v_") == 0
                    || pats.back().compare(0, 3, "pat") == 0;
      }
      std::string rhs = term(body[i][1]);
      bool totalMatch = catchall && guards.empty();
      // Keep fallthrough outside the pattern match. Otherwise Isabelle's
      // case compiler duplicates the remaining clauses across constructor
      // alternatives, making large rule dispatchers prohibitively expensive.
      // The outer option is matching success; Some None is exhaustion after
      // a successful match and must never try a later EO clause.
      if (!totalMatch) rhs = some(rhs);
      if (!guards.empty())
      {
        std::string guard;
        for (const auto& g : guards)
          guard += (guard.empty() ? "" : " \\<and> ") + g;
        rhs = "(if " + guard + " then " + rhs + " else None)";
      }
      std::string match =
          "(case " + tuple(args) + " of " + tuple(pats) + " => " + rhs;
      if (!catchall) match += " | _ => None";
      match += ")";
      result = totalMatch ? match
                          : "(case " + match + " of Some matched => matched"
                            " | None => " + result + ")";
    }
  if (ret == "Term" && !p.macro && !checker)
  {
    std::string guard;
    for (size_t i = 0; i < arity; ++i)
      if (type(t[i]) == "Term")
        guard += (guard.empty() ? "" : " \\<or> ") + args[i] + " = Term_Stuck";
    if (!guard.empty())
      result = "(if " + guard + " then Some Term_Stuck else " + result + ")";
  }
  return result;
}

void IsabelleMetaReduce::finalize()
{
  std::ostringstream datatypes, keys, defs, spec;
  if (d_datatypes["CRule"].empty())
    d_datatypes["CRule"].push_back("CRule_unused");
  // Isabelle generates quadratic constructor facts for a flat enumeration.
  // CPC has hundreds of rules and operators: use small finite chunks, with
  // abbreviations preserving the public names (also in generated patterns).
  std::map<std::string, std::string> enumAliases;
  std::vector<std::string> enums;
  constexpr size_t chunkSize = 24;
  for (const auto& entry : d_datatypes)
    if (entry.second.size() > chunkSize
        && std::all_of(entry.second.begin(), entry.second.end(),
                       [](const std::string& c) { return c.find(' ') == std::string::npos; }))
      enums.push_back(entry.first);
  for (const auto& t : enums)
  {
    auto old = d_datatypes[t];
    d_datatypes[t].clear();
    for (size_t i = 0; i < old.size(); ++i)
    {
      std::string chunk = t + "_chunk" + std::to_string(i / chunkSize);
      std::string branch = t + "_part" + std::to_string(i / chunkSize);
      std::string leaf = t + "_leaf" + std::to_string(i);
      if (i % chunkSize == 0)
      {
        d_datatypes[t].push_back(branch + " \"" + chunk + "\"");
        d_datatypeDeps[t].insert(chunk);
      }
      d_datatypes[chunk].push_back(leaf);
      enumAliases[old[i]] = "(" + branch + " " + leaf + ")";
    }
  }
  for (const auto& entry : d_datatypes) d_datatypeDeps[entry.first];
  std::set<std::string> orderedTypes;
  std::function<void(const std::string&)> orderType = [&](const std::string& t) {
    if (!d_datatypes.count(t) || !orderedTypes.insert(t).second) return;
    for (const auto& dep : d_datatypeDeps[t]) orderType(dep);
  };
  orderType("Term");
  for (const auto& group : components(d_datatypeDeps))
  {
    for (size_t i = 0; i < group.size(); ++i)
    {
      const auto& constructors = d_datatypes.at(group[i]);
      datatypes << (i == 0 ? "datatype " : "and ") << group[i] << " =\n  ";
      for (size_t j = 0; j < constructors.size(); ++j)
        datatypes << (j == 0 ? "" : "\n| ") << constructors[j];
      datatypes << "\n";
    }
    datatypes << "\n";
    if (!orderedTypes.count(group.front())) continue;
    // Prefix encodings are injective: the constructor determines its fields,
    // and variable-length native strings carry their length. This gives cmp
    // a deterministic structural order independent of the recursion budget.
    for (size_t i = 0; i < group.size(); ++i)
      keys << (i == 0 ? "primrec " : "and ") << "key_" << group[i]
           << " :: \"" << group[i] << " => int list\"\n";
    keys << "where\n";
    bool first = true;
    for (const auto& t : group)
    {
      size_t tag = 0;
      for (const auto& decl : d_datatypes.at(t))
      {
        std::istringstream in(decl);
        std::string cons, field;
        in >> cons;
        std::vector<std::string> args, fields;
        while (in >> std::quoted(field))
        {
          std::string arg = "x" + std::to_string(args.size());
          args.push_back(arg);
          if (field == "int") fields.push_back("[" + arg + "]");
          else if (field == "nat") fields.push_back("[int " + arg + "]");
          else if (field == "bool")
            fields.push_back("[if " + arg + " then 1 else 0]");
          else if (field == "rat")
            fields.push_back("[fst (quotient_of " + arg
                             + "), snd (quotient_of " + arg + ")]");
          else if (field == "nat list")
            fields.push_back("(int (length " + arg + ") # map int " + arg + ")");
          else fields.push_back("key_" + field + " " + arg);
        }
        keys << (first ? "  " : "| ") << "\"key_" << t << " "
             << application(cons, args) << " = [" << tag++ << "]";
        for (const auto& f : fields) keys << " @ " << f;
        keys << "\"\n";
        first = false;
      }
    }
    keys << "\n";
  }
  for (const auto& alias : enumAliases)
    datatypes << "abbreviation " << alias.first << " where\n  \""
              << alias.first << " \\<equiv> " << alias.second << "\"\n\n";
  for (const auto& alias : d_operatorAliases)
    datatypes << "abbreviation " << alias.first << " where\n  \""
              << alias.first << " \\<equiv> " << alias.second << "\"\n\n";
  // Render first to collect *all* calls, including eo:: primitives which are
  // not represented as PROGRAM_CONST nodes. Emit strongly connected groups
  // in dependency order so Isabelle only sees genuinely mutual recursion.
  std::map<std::string, std::string> bodies;
  for (const auto& entry : d_programs)
  {
    d_current = entry.first;
    d_calls[d_current];
    bodies[d_current] = programBody(entry.second);
  }
  size_t groupId = 0;
  for (const auto& group : components(d_calls))
  {
    std::vector<std::string> types, names;
    std::vector<std::vector<std::string>> args;
    for (size_t i = 0; i < group.size(); ++i)
    {
      const Program& p = d_programs.at(group[i]);
      const Expr& t = p.symbol.getType();
      bool cases = p.body.getKind() == Kind::PROGRAM;
      size_t arity = cases ? t.getNumChildren() - 1 : 0;
      names.push_back("p_" + identifier(group[i]));
      std::string typ;
      args.emplace_back();
      for (size_t j = 0; j < arity; ++j)
      {
        typ += "(" + type(t[j]) + ") => ";
        args.back().push_back("arg" + std::to_string(j));
      }
      types.push_back(typ + "(" + type(cases ? t[arity] : t) + ") option");
    }
    if (group.size() == 1)
      defs << "primrec " << names[0] << " :: \"nat => " << types[0] << "\"\nwhere\n"
           << "  \"" << application(names[0] + " 0", args[0]) << " = None\"\n| \""
           << application(names[0] + " (Suc fuel)", args[0]) << " = "
           << bodies.at(group[0]) << "\"\n";
    else
    {
      // Mutual recursion is primitive recursion on a tuple of functions.
      // Every recursive call projects from the preceding fuel's tuple. This
      // avoids the function package's domain/termination analysis of nested
      // option matches, which is both costly and fragile for CPC programs.
      const std::string mutual = "mutual_" + std::to_string(groupId++);
      std::vector<std::string> projections, zero, succ;
      for (size_t i = 0; i < group.size(); ++i)
      {
        std::string proj = "(" + mutual + " fuel)";
        for (size_t j = 0; j < i; ++j) proj = "(snd " + proj + ")";
        if (i + 1 < group.size()) proj = "(fst " + proj + ")";
        projections.push_back(proj);
      }
      defs << "primrec " << mutual << " :: \"nat => (";
      for (size_t i = 0; i < group.size(); ++i)
      {
        defs << (i == 0 ? "" : " * ") << "(" << types[i] << ")";
        std::string body = bodies.at(group[i]);
        for (size_t j = 0; j < group.size(); ++j)
        {
          std::string from = names[j] + " fuel";
          size_t pos = 0;
          while ((pos = body.find(from, pos)) != std::string::npos)
          {
            body.replace(pos, from.size(), projections[j]);
            pos += projections[j].size();
          }
        }
        std::string lambda;
        if (!args[i].empty())
        {
          lambda = "(\\<lambda>";
          for (const auto& arg : args[i]) lambda += " " + arg;
          lambda += ". ";
        }
        zero.push_back(lambda + "None" + (lambda.empty() ? "" : ")"));
        succ.push_back(lambda + body + (lambda.empty() ? "" : ")"));
      }
      defs << ")\"\nwhere\n  \"" << mutual << " 0 = " << tuple(zero)
           << "\"\n| \"" << mutual << " (Suc fuel) = " << tuple(succ) << "\"\n\n";
      for (size_t i = 0; i < group.size(); ++i)
        defs << "abbreviation " << names[i] << " where\n  \"" << names[i]
             << " fuel \\<equiv> " << projections[i] << "\"\n";
    }
    defs << "\n";
  }
  if (!d_programs.count("$eo_checker_is_refutation"))
    EO_FATAL()
        << "IsabelleMetaReduce: input must contain $eo_checker_is_refutation";
  for (const auto& rule : d_rules)
  {
    auto it = d_programs.find(rule);
    if (it == d_programs.end())
      EO_FATAL() << "IsabelleMetaReduce: unknown rule " << rule;
    const Program& p = it->second;
    size_t arity = p.body.getKind() == Kind::PROGRAM
                       ? p.symbol.getType().getNumChildren() - 1
                       : 0;
    std::vector<std::string> args;
    for (size_t i = 0; i < arity; ++i)
      args.push_back("arg" + std::to_string(i));
    // An explicit obligation over an interpretation supplied by iogos. This
    // is a definition, not an unproved claim of logical soundness.
    spec << "definition obligation_" << identifier(rule) << " where\n  \""
         << application("obligation_" + identifier(rule) + " valid fuel", args)
         << " = (\\<forall>result. "
         << application("p_" + identifier(rule) + " fuel", args)
         << " = Some result \\<longrightarrow> result \\<noteq> Term_Stuck"
         << " \\<longrightarrow> valid result)\"\n\n";
  }
  emitResourceFile(
      "plugins/isabelle_meta/isabelle_meta.thy",
      "plugins/isabelle_meta/isabelle_meta_gen.thy",
      {{"$DATATYPES$", datatypes.str()}, {"$ORDER_KEYS$", keys.str()},
       {"$PROGRAMS$", defs.str()}});
  emitResourceFile("plugins/isabelle_meta/isabelle_meta_spec.thy",
                   "plugins/isabelle_meta/isabelle_meta_spec_gen.thy",
                   {{"$OBLIGATIONS$", spec.str()}});
}

}  // namespace ethos
