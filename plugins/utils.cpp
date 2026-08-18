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
    case MetaKind::PROOF: ss << "PROOF"; break;
    case MetaKind::SMT: ss << "SMT"; break;
    case MetaKind::SMT_BUILTIN: ss << "SMT_BUILTIN"; break;
    case MetaKind::SMT_BUILTIN_DATATYPE: ss << "SMT_BUILTIN_DATATYPE"; break;
    case MetaKind::SMT_TYPE: ss << "SMT_TYPE"; break;
    case MetaKind::SMT_VALUE: ss << "SMT_VALUE"; break;
    case MetaKind::SMT_MAP: ss << "SMT_MAP"; break;
    case MetaKind::SMT_SEQ: ss << "SMT_SEQ"; break;
    case MetaKind::CHECKER_RULE: ss << "CHECKER_RULE"; break;
    case MetaKind::CHECKER_CMD: ss << "CHECKER_CMD"; break;
    case MetaKind::EO_EMBED: ss << "EO_EMBED"; break;
    case MetaKind::SMT_EMBED: ss << "SMT_EMBED"; break;
    case MetaKind::CHECKER_EMBED: ss << "CHECKER_EMBED"; break;
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
bool isSmtMetaKind(MetaKind k)
{
  return k == MetaKind::SMT_BUILTIN || k == MetaKind::SMT_BUILTIN_DATATYPE
         || k == MetaKind::SMT || k == MetaKind::SMT_TYPE
         || k == MetaKind::SMT_VALUE || k == MetaKind::SMT_MAP
         || k == MetaKind::SMT_SEQ || k == MetaKind::SMT_EMBED;
}
bool isCheckerMetaKind(MetaKind k)
{
  return k == MetaKind::CHECKER_RULE || k == MetaKind::CHECKER_CMD
         || k == MetaKind::CHECKER_EMBED;
}
bool isEmbedMetaKind(MetaKind k)
{
  return k == MetaKind::EO_EMBED || k == MetaKind::SMT_EMBED
         || k == MetaKind::CHECKER_EMBED;
}

}  // namespace ethos
