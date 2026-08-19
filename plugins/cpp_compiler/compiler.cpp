/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "compiler.h"

#include <fstream>
#include <iomanip>
#include <utility>

#include "base/check.h"
#include "base/output.h"
#include "literal.h"
#include "state.h"

namespace ethos {

namespace {

bool isNamedExpr(Kind kind)
{
  return isSymbol(kind) || kind == Kind::BUILTIN_CONST
         || kind == Kind::VARIABLE;
}

const char* attrName(Attr attr)
{
  switch (attr)
  {
    case Attr::NONE: return "NONE";
    case Attr::IMPLICIT: return "IMPLICIT";
    case Attr::TYPE: return "TYPE";
    case Attr::IS_EQ: return "IS_EQ";
    case Attr::SORRY: return "SORRY";
    case Attr::LIST: return "LIST";
    case Attr::PROGRAM: return "PROGRAM";
    case Attr::BINDER: return "BINDER";
    case Attr::LET_BINDER: return "LET_BINDER";
    case Attr::OPAQUE: return "OPAQUE";
    case Attr::SYNTAX: return "SYNTAX";
    case Attr::RESTRICT: return "RESTRICT";
    case Attr::PROOF_RULE: return "PROOF_RULE";
    case Attr::RIGHT_ASSOC: return "RIGHT_ASSOC";
    case Attr::LEFT_ASSOC: return "LEFT_ASSOC";
    case Attr::RIGHT_ASSOC_NIL: return "RIGHT_ASSOC_NIL";
    case Attr::LEFT_ASSOC_NIL: return "LEFT_ASSOC_NIL";
    case Attr::RIGHT_ASSOC_NS_NIL: return "RIGHT_ASSOC_NS_NIL";
    case Attr::LEFT_ASSOC_NS_NIL: return "LEFT_ASSOC_NS_NIL";
    case Attr::CHAINABLE: return "CHAINABLE";
    case Attr::PAIRWISE: return "PAIRWISE";
    case Attr::ARG_LIST: return "ARG_LIST";
    case Attr::AMB: return "AMB";
    case Attr::DATATYPE: return "DATATYPE";
    case Attr::DATATYPE_CONSTRUCTOR: return "DATATYPE_CONSTRUCTOR";
    case Attr::AMB_DATATYPE_CONSTRUCTOR: return "AMB_DATATYPE_CONSTRUCTOR";
  }
  Unreachable();
}

}  // namespace

Compiler::Compiler(State& state) : d_state(state), d_nscopes(0), d_nextExprId(1)
{
}

Compiler::~Compiler() {}

bool Compiler::isRecording() const
{
  return !d_recordingStack.empty() && d_recordingStack.back();
}

void Compiler::reset()
{
  if (!isRecording())
  {
    return;
  }
  d_initialize << "  d_state.reset();\n";
  d_exprIds.clear();
  d_proofRules.clear();
  d_sorryRulesWritten.clear();
  d_nscopes = 0;
}

void Compiler::pushScope() { ++d_nscopes; }

void Compiler::popScope()
{
  Assert(d_nscopes > 0);
  --d_nscopes;
}

bool Compiler::includeFile(const Filepath& path,
                           bool isSignature,
                           bool isReference,
                           const Expr& referenceNf)
{
  (void)referenceNf;
  bool recording = isSignature && !isReference;
  d_recordingStack.push_back(recording);
  if (!recording)
  {
    return false;
  }
  const std::string& rawPath = path.getRawPath();
  d_config << "  ss << std::setw(15) << \" \" << " << quote(rawPath)
           << " << std::endl;\n";
  d_includes << "  {\n"
             << "    std::error_code ec;\n"
             << "    if (path.getRawPath() == " << quote(rawPath) << "\n"
             << "        || std::filesystem::equivalent(path.getRawPath(), "
             << quote(rawPath) << ", ec))\n"
             << "    {\n      return true;\n    }\n  }\n";
  // Compiler observes and records parsing; it never replaces it.
  return false;
}

void Compiler::finalizeIncludeFile(const Filepath& path,
                                   bool isSignature,
                                   bool isReference,
                                   const Expr& referenceNf)
{
  (void)path;
  (void)isSignature;
  (void)isReference;
  (void)referenceNf;
  Assert(!d_recordingStack.empty());
  if (isRecording())
  {
    writeProofRuleAttributes();
  }
  d_recordingStack.pop_back();
}

void Compiler::setLiteralTypeRule(Kind kind, const Expr& type)
{
  if (!isRecording())
  {
    return;
  }
  size_t id = writeExpr(type);
  d_initialize << "  d_state.setLiteralTypeRule(Kind::" << kind << ", _e" << id
               << ");\n";
}

void Compiler::bind(const std::string& name, const Expr& expr)
{
  if (!isRecording() || d_nscopes > 0)
  {
    return;
  }
  size_t id = writeExpr(expr);
  d_initialize << "  d_state.bind(" << quote(name) << ", _e" << id << ");\n";
  if (expr.getKind() == Kind::PROOF_RULE)
  {
    d_proofRules.push_back(expr);
  }
}

void Compiler::markConstructorKind(const Expr& expr,
                                   Attr attr,
                                   const Expr& constructor)
{
  if (!isRecording())
  {
    return;
  }
  // State::defineProgram records Attr::PROGRAM itself. Replaying this callback
  // as well would attempt to mark the same symbol twice.
  if (attr == Attr::PROGRAM)
  {
    return;
  }
  size_t exprId = writeExpr(expr);
  size_t constructorId = 0;
  if (!constructor.isNull())
  {
    constructorId = writeExpr(constructor);
  }
  d_initialize << "  d_state.markConstructorKind(_e" << exprId
               << ", Attr::" << attrName(attr) << ", ";
  if (constructor.isNull())
  {
    d_initialize << "Expr()";
  }
  else
  {
    d_initialize << "_e" << constructorId;
  }
  d_initialize << ");\n";
}

void Compiler::defineProgram(const Expr& symbol, const Expr& program)
{
  if (!isRecording() || d_nscopes > 0)
  {
    return;
  }
  size_t symbolId = writeExpr(symbol);
  size_t programId = 0;
  if (!program.isNull())
  {
    programId = writeExpr(program);
  }
  d_initialize << "  d_state.defineProgram(_e" << symbolId << ", ";
  if (program.isNull())
  {
    d_initialize << "Expr()";
  }
  else
  {
    d_initialize << "_e" << programId;
  }
  d_initialize << ");\n";
}

void Compiler::writeProofRuleAttributes()
{
  for (const Expr& rule : d_proofRules)
  {
    const ExprValue* value = rule.getValue();
    if (d_sorryRulesWritten.find(value) != d_sorryRulesWritten.end()
        || !d_state.isProofRuleSorry(value))
    {
      continue;
    }
    d_initialize << "  d_state.markProofRuleSorry(" << getName(rule)
                 << ".getValue());\n";
    d_sorryRulesWritten.insert(value);
  }
}

size_t Compiler::writeExpr(const Expr& expr)
{
  Assert(!expr.isNull());
  std::vector<std::pair<Expr, bool>> pending;
  pending.emplace_back(expr, false);

  while (!pending.empty())
  {
    Expr current = pending.back().first;
    bool ready = pending.back().second;
    pending.pop_back();
    const ExprValue* value = current.getValue();
    if (d_exprIds.find(value) != d_exprIds.end())
    {
      continue;
    }

    Kind kind = current.getKind();
    if (!ready)
    {
      pending.emplace_back(current, true);
      if (isNamedExpr(kind) && current != d_state.mkSelf()
          && current != d_state.mkListType() && current != d_state.mkListCons()
          && current != d_state.mkListNil() && current != d_state.mkProofType())
      {
        ExprValue* type = d_state.lookupType(value);
        if (type == nullptr)
        {
          EO_FATAL() << "Compiler: no type recorded for symbol " << current;
        }
        pending.emplace_back(Expr(type), false);
      }
      else
      {
        for (size_t i = current.getNumChildren(); i > 0; --i)
        {
          pending.emplace_back(current[i - 1], false);
        }
      }
      continue;
    }

    size_t id = d_nextExprId++;
    d_exprIds[value] = id;
    d_retainedExprs.push_back(current);
    d_declarations << "  Expr _e" << id << ";\n";
    d_initialize << "  _e" << id << " = ";

    if (current == d_state.mkSelf())
    {
      d_initialize << "d_state.mkSelf()";
    }
    else if (current == d_state.mkListType())
    {
      d_initialize << "d_state.mkListType()";
    }
    else if (current == d_state.mkListCons())
    {
      d_initialize << "d_state.mkListCons()";
    }
    else if (current == d_state.mkListNil())
    {
      d_initialize << "d_state.mkListNil()";
    }
    else if (current == d_state.mkProofType())
    {
      d_initialize << "d_state.mkProofType()";
    }
    else if (kind == Kind::TYPE)
    {
      d_initialize << "d_state.mkType()";
    }
    else if (kind == Kind::BOOL_TYPE)
    {
      d_initialize << "d_state.mkBoolType()";
    }
    else if (kind == Kind::ANY)
    {
      d_initialize << "d_state.mkAny()";
    }
    else if (isLiteral(kind))
    {
      const Literal* literal = value->asLiteral();
      Assert(literal != nullptr);
      d_initialize << "d_state.mkLiteral(Kind::" << kind << ", "
                   << quote(literal->toString()) << ")";
    }
    else if (isNamedExpr(kind))
    {
      const Literal* literal = value->asLiteral();
      Assert(literal != nullptr);
      ExprValue* type = d_state.lookupType(value);
      Assert(type != nullptr);
      d_initialize << "d_state.mkSymbol(Kind::" << kind << ", "
                   << quote(literal->toString()) << ", " << getName(Expr(type))
                   << ")";
    }
    else
    {
      d_initialize << "d_state.mkRawExpr(Kind::" << kind << ", {";
      for (size_t i = 0, size = current.getNumChildren(); i < size; ++i)
      {
        if (i > 0)
        {
          d_initialize << ", ";
        }
        d_initialize << getName(current[i]);
      }
      d_initialize << "})";
    }
    d_initialize << ";\n";
  }

  return d_exprIds.find(expr.getValue())->second;
}

std::string Compiler::getName(const Expr& expr) const
{
  std::map<const ExprValue*, size_t>::const_iterator it =
      d_exprIds.find(expr.getValue());
  Assert(it != d_exprIds.end());
  std::stringstream name;
  name << "_e" << it->second;
  return name.str();
}

std::string Compiler::quote(const std::string& text)
{
  std::stringstream quoted;
  quoted << '"';
  for (unsigned char ch : text)
  {
    switch (ch)
    {
      case '\\': quoted << "\\\\"; break;
      case '"': quoted << "\\\""; break;
      case '\n': quoted << "\\n"; break;
      case '\r': quoted << "\\r"; break;
      case '\t': quoted << "\\t"; break;
      default:
        if (ch >= 0x20 && ch <= 0x7e)
        {
          quoted << static_cast<char>(ch);
        }
        else
        {
          // A three-digit octal escape cannot consume a following digit,
          // unlike a C++ hexadecimal escape.
          quoted << '\\' << std::oct << std::setw(3) << std::setfill('0')
                 << static_cast<unsigned>(ch) << std::dec;
        }
        break;
    }
  }
  quoted << '"';
  return quoted.str();
}

void Compiler::finalize()
{
  writeProofRuleAttributes();
  std::ofstream output("compiled.out.cpp");
  if (!output.is_open())
  {
    EO_FATAL() << "Compiler: cannot write compiled.out.cpp";
  }
  output << "/** ================ AUTO GENERATED ============ */\n";
  output << toString();
  Trace("compile") << "GEN-COMPILE\n```\n" << toString() << "```\n";
}

std::string Compiler::toString() const
{
  std::stringstream source;
  source << "#include \"executor.h\"\n";
  source << "#include \"state.h\"\n\n";
  source << "#include <filesystem>\n";
  source << "#include <iomanip>\n";
  source << "#include <sstream>\n";
  source << "#include <system_error>\n\n";
  source << "namespace ethos {\n\n";
  source << "std::string Executor::showCompiledFiles()\n";
  source << "{\n";
  source << "  std::stringstream ss;\n";
  source << d_config.str();
  source << "  return ss.str();\n";
  source << "}\n\n";
  source << "bool Executor::includeFile(const Filepath& path,\n";
  source << "                           bool isSignature,\n";
  source << "                           bool isReference,\n";
  source << "                           const Expr& referenceNf)\n";
  source << "{\n";
  source << "  (void)referenceNf;\n";
  source << "  if (!isSignature || isReference)\n";
  source << "  {\n";
  source << "    return false;\n";
  source << "  }\n";
  source << d_includes.str();
  source << "  return false;\n";
  source << "}\n\n";
  source << "void Executor::initialize()\n";
  source << "{\n";
  source << d_declarations.str();
  source << d_initialize.str();
  source << "}\n\n";
  source << "}  // namespace ethos\n";
  return source.str();
}

}  // namespace ethos
