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
    case MetaKind::SMT_BUILTIN: ss << "SMT_BUILTIN"; break;
    case MetaKind::SMT_VALUE: ss << "SMT_VALUE"; break;
    case MetaKind::SMT_MAP: ss << "SMT_MAP"; break;
    case MetaKind::SMT_SEQ: ss << "SMT_SEQ"; break;
    case MetaKind::PROGRAM: ss << "PROGRAM"; break;
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
    case MetaKind::SMT_VALUE: ss << "vsm."; break;
    case MetaKind::SMT_BUILTIN: ss << "?"; break;
    default: ss << "?MetaKindPrefix_" << metaKindToString(k); break;
  }
  return ss.str();
}
std::string metaKindToCons(MetaKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case MetaKind::SMT_VALUE: ss << "SmtValue"; break;
    default: ss << "?MetaKindCons"; break;
  }
  return ss.str();
}

}  // namespace ethos
