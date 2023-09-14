#ifndef EXPR_TRIE_H
#define EXPR_TRIE_H

#include <string>
#include "expr.h"

namespace alfc {

class ExprTrie
{
public:
  ExprTrie() : d_data(nullptr) {}
  /** The children */
  std::map<const ExprValue*, ExprTrie> d_children;
  /** The data at this node */
  ExprValue* d_data;
};

}  // namespace alfc

#endif /* EXPR_TRIE_H */
