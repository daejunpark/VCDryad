#include "dryad_bst.h"

_(logic \bool mutable_bst(BNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
BNode * bst_remove_root_rec(BNode * x)
  _(requires x != NULL)
  _(requires bst(x))
//_(requires \intset_lt(bst_keys(x->left), bst_keys(x->right)))
  _(ensures bst(\result))
  _(ensures bst_keys(\result) == \intset_diff(\old(bst_keys(x)), \intset_singleton(x->key)))
  _(ensures bst_keys(\result) == \intset_union(\old(bst_keys(x->left)), \old(bst_keys(x->right))))  
  _(ensures bst_min_key(\result) >= \old(bst_min_key(x)))
  _(ensures bst_max_key(\result) <= \old(bst_max_key(x)))
{
  _(assume mutable_bst(x))
  _(assume \malloc_root(x))

  if(x->left == NULL && x->right == NULL) {
    free(x);
    return NULL;
  } else if (x->left == NULL) {
    BNode * right = x->right;
    free(x);
    return right;
  } else if (x->right == NULL) {
    BNode * left = x->left;
    free(x);
    return left;
  } else {
    BNode * right = x->right;
    BNode * left = x->left;

    _(assume mutable_bst(right))
    BNode * right_left = right->left;
    BNode * right_right = right->right;

    x->right = right_left;

    BNode * tmp = bst_remove_root_rec(x);

    right->left = tmp;
    
    return right;

  }

}

