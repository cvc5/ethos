#ifndef EXPR_TRIE_H
#define EXPR_TRIE_H

#include <string>
#include "expr.h"

namespace alfc {

class ExprTrie
{
public:
  ExprTrie() {}
  std::map<const ExprValue*, ExprTrie> d_children;
  Expr d_data;
};

}  // namespace alfc

#endif /* EXPR_TRIE_H */
