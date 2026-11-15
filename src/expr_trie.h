/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef EXPR_TRIE_H
#define EXPR_TRIE_H

#include <map>
#include <string>
#include <vector>

#include "base/check.h"
#include "base/output.h"
#include "expr.h"

namespace ethos {

class ExprTrie
{
public:
  ExprTrie() : d_data(nullptr) {}
  /** The children */
  std::map<const ExprValue*, ExprTrie> d_children;
  /** The data at this node */
  ExprValue* d_data;
  /** */
  ExprTrie* get(const std::vector<ExprValue*>& children)
  {
    ExprTrie* et = this;
    for (const ExprValue* e : children)
    {
      et = &(et->d_children[e]);
    }
    return et;
  }
  /**
   * Remove the data stored for children, and prune the nodes on its path that
   * no longer store data or have children. Note that other terms may be stored
   * on this path, either at a node on the path (terms whose children are a
   * prefix of children) or below its leaf (terms whose children have children
   * as a prefix); these must be kept.
   */
  void remove(const std::vector<ExprValue*>& children)
  {
    // the nodes on the path, where path[i] is the parent of the node for
    // children[i]
    std::vector<ExprTrie*> path;
    ExprTrie* et = this;
    for (ExprValue* e : children)
    {
      std::map<const ExprValue*, ExprTrie>::iterator itet =
          et->d_children.find(e);
      Assert(itet != et->d_children.end());
      path.push_back(et);
      et = &itet->second;
    }
    et->d_data = nullptr;
    // prune from the leaf upwards, while the node is empty
    for (size_t i = children.size(); i > 0; i--)
    {
      ExprTrie* parent = path[i - 1];
      std::map<const ExprValue*, ExprTrie>::iterator itc =
          parent->d_children.find(children[i - 1]);
      if (itc->second.d_data != nullptr || !itc->second.d_children.empty())
      {
        break;
      }
      parent->d_children.erase(itc);
    }
  }
};

}  // namespace ethos

#endif /* EXPR_TRIE_H */
