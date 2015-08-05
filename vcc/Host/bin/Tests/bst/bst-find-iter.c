#include "dryad_bst.h"

_(logic \bool mutable_bst(BNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
BNode * bst_find_iter(BNode * x, int k)
  _(requires bst(x))

  _(ensures  bst(x))
  _(ensures  bst(\result))
  _(ensures  \result == NULL || \result->key == k)
{
  _(assume mutable_bst(x))
  BNode * curr = x;
  while(curr != NULL)
    _(invariant bst(x))
    _(invariant bst(curr))
    _(invariant \intset_in(k, bst_keys(x)) <==> \intset_in(k, bst_keys(curr)))
  {
    _(assume mutable_bst(curr))
    if (curr->key == k) {
      return curr;
    } else if (k < curr->key) {
      curr = curr->left;
    } else {
      curr = curr->right;
    }
  }
  
  return curr;
}

