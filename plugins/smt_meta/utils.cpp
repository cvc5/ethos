/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "utils.h"

#include <sstream>

namespace ethos {

std::string metaKindToString(MetaKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case MetaKind::EUNOIA: ss << "EUNOIA"; break;
    case MetaKind::SMT: ss << "SMT"; break;
    case MetaKind::SMT_BUILTIN: ss << "SMT_BUILTIN"; break;
    case MetaKind::SMT_TYPE: ss << "SMT_TYPE"; break;
    case MetaKind::SMT_VALUE: ss << "SMT_VALUE"; break;
    case MetaKind::SMT_MAP: ss << "SMT_MAP"; break;
    case MetaKind::SMT_SEQ: ss << "SMT_SEQ"; break;
    case MetaKind::PROGRAM: ss << "PROGRAM"; break;
    case MetaKind::PROOF: ss << "PROOF"; break;
    case MetaKind::DATATYPE: ss << "DATATYPE"; break;
    case MetaKind::DATATYPE_CONSTRUCTOR: ss << "DATATYPE_CONSTRUCTOR"; break;
    case MetaKind::CHECKER_STATE: ss << "CHECKER_STATE"; break;
    case MetaKind::CHECKER_STATE_OBJ: ss << "CHECKER_STATE_OBJ"; break;
    case MetaKind::CHECKER_CMD: ss << "CHECKER_CMD"; break;
    case MetaKind::CHECKER_CMD_LIST: ss << "CHECKER_CMD_LIST"; break;
    case MetaKind::CHECKER_INDEX: ss << "CHECKER_INDEX"; break;
    case MetaKind::CHECKER_INDEX_LIST: ss << "CHECKER_INDEX_LIST"; break;
    case MetaKind::NONE: ss << "NONE"; break;
    default: ss << "?MetaKind"; break;
  }
  return ss.str();
}
std::string metaKindToPrefix(MetaKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case MetaKind::EUNOIA: ss << "eo."; break;
    case MetaKind::SMT: ss << "sm."; break;
    case MetaKind::SMT_TYPE: ss << "tsm."; break;
    case MetaKind::SMT_VALUE: ss << "vsm."; break;
    case MetaKind::SMT_BUILTIN: ss << "?"; break;
    default: ss << "?MetaKindPrefix_" << metaKindToString(k); break;
  }
  return ss.str();
}
bool isCheckerMetaKind(MetaKind k)
{
  return k==MetaKind::CHECKER_STATE || k==MetaKind::CHECKER_STATE_OBJ || 
  k==MetaKind::CHECKER_CMD || k==MetaKind::CHECKER_INDEX || k==MetaKind::CHECKER_CMD_LIST || k==MetaKind::CHECKER_INDEX_LIST;
}

ConjPrint::ConjPrint() : d_npush(0) {}
void ConjPrint::push(const std::string& str)
{
  if (d_npush > 0)
  {
    d_ss << " ";
  }
  d_ss << str;
  d_npush++;
}

void ConjPrint::printConjunction(std::ostream& os, bool isDisj)
{
  if (d_npush == 0)
  {
    os << (isDisj ? "false" : "true");
  }
  else if (d_npush > 1)
  {
    os << "(" << (isDisj ? "or" : "and") << " " << d_ss.str() << ")";
  }
  else
  {
    os << d_ss.str();
  }
}

SelectorCtx::SelectorCtx() {}
void SelectorCtx::clear()
{
  d_ctx.clear();
  d_tctx.clear();
}

}  // namespace ethos
