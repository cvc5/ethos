/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "attr.h"

namespace ethos {

std::ostream& operator<<(std::ostream& o, Attr a)
{
  switch (a)
  {
    case Attr::NONE: o << "NONE"; break;
    case Attr::IMPLICIT: o << "implicit"; break;
    case Attr::TYPE: o << "type"; break;
    case Attr::IS_EQ: o << "is_eq"; break;
    case Attr::SORRY: o << "sorry"; break;
    case Attr::LIST: o << "list"; break;
    case Attr::REQUIRES: o << "requires"; break;
    case Attr::PROOF_RULE: o << "proof_rule"; break;
    case Attr::PROGRAM: o << "program"; break;
    case Attr::BINDER: o << "binder"; break;
    case Attr::LET_BINDER: o << "let_binder"; break;
    case Attr::OPAQUE: o << "opaque"; break;
    case Attr::SYNTAX: o << "syntax"; break;
    case Attr::RESTRICT: o << "restrict"; break;
    case Attr::RIGHT_ASSOC: o << "right-assoc"; break;
    case Attr::LEFT_ASSOC: o << "left-assoc"; break;
    case Attr::RIGHT_ASSOC_NIL: o << "right-assoc-nil"; break;
    case Attr::LEFT_ASSOC_NIL: o << "left-assoc-nil"; break;
    case Attr::RIGHT_ASSOC_NS_NIL: o << "right-assoc-non-singleton-nil"; break;
    case Attr::LEFT_ASSOC_NS_NIL: o << "left-assoc-non-singleton-nil"; break;
    case Attr::CHAINABLE: o << "chainable"; break;
    case Attr::PAIRWISE: o << "pairwise"; break;
    case Attr::ARG_LIST: o << "arg-list"; break;
    case Attr::DATATYPE: o << "datatype"; break;
    case Attr::AMB: o << "amb"; break;
    case Attr::DATATYPE_CONSTRUCTOR: o << "datatype_constructor"; break;
    case Attr::AMB_DATATYPE_CONSTRUCTOR: o << "amb_datatype_constructor"; break;
    default: o << "UnknownAttr(" << unsigned(a) << ")"; break;
  }
  return o;
}

bool isNAryAttr(Attr a)
{
  switch (a)
  {
    case Attr::LEFT_ASSOC:
    case Attr::RIGHT_ASSOC:
    case Attr::LEFT_ASSOC_NIL:
    case Attr::RIGHT_ASSOC_NIL:
    case Attr::RIGHT_ASSOC_NS_NIL:
    case Attr::LEFT_ASSOC_NS_NIL:
    case Attr::CHAINABLE:
    case Attr::PAIRWISE:
    case Attr::ARG_LIST: return true;
    default:
      break;
  }
  return false;
}

bool isListNilAttr(Attr a)
{
  switch (a)
  {
    case Attr::LEFT_ASSOC_NIL:
    case Attr::RIGHT_ASSOC_NIL:
    case Attr::RIGHT_ASSOC_NS_NIL:
    case Attr::LEFT_ASSOC_NS_NIL: return true;
    default: break;
  }
  return false;
}

bool isConstructorKindAttr(Attr a)
{
  return isNAryAttr(a) || a==Attr::BINDER || a==Attr::LET_BINDER || a==Attr::LIST;
}

}  // namespace ethos
