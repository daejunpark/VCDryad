#include "dryad_treap.h"

_(logic \bool mutable_treap(BNode * x) = x != NULL ==> \mutable(x) && \writable(x))
_(dryad)
BNode * treap_remove_root_rec(BNode * x)
  _(requires x != NULL)
  _(requires treap(x))
  _(requires \intset_lt(treap_keys(x->left), treap_keys(x->right)))
  _(requires \intset_disjoint(treap_prios(x->left), treap_prios(x->right)))
  _(requires \intset_disjoint(treap_keys(x->left), treap_keys(x->right)))
  _(ensures treap(\result))
  _(ensures \intset_subset(treap_prios(\result), \old(treap_prios(x))))
  _(ensures treap_reach(\result) == \oset_diff(\old(treap_reach(x)), \oset_singleton(x)))
  _(ensures treap_keys(\result) == \intset_diff(\old(treap_keys(x)), \intset_singleton(x->key)))
  _(ensures treap_keys(\result) == \intset_union(\old(treap_keys(x->left)), \old(treap_keys(x->right))))  
  _(ensures treap_prios(\result) == \intset_union(\old(treap_prios(x->left)), \old(treap_prios(x->right))))  
{
  _(assume mutable_treap(x))
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
    BNode * left  = x->left;

    _(assume mutable_treap(right))
    _(assume mutable_treap(left))

    if(left->prio <= right->prio) {
      BNode * right_left = right->left;
      BNode * right_right = right->right;
      BNode * left_left = left->left;
      BNode * left_right = left->right;
      x->right = right_left;
      BNode * tmp = treap_remove_root_rec(x);
      right->left = tmp;  
      return right;
    } else {
      BNode * right_left = right->left;
      BNode * right_right = right->right;
      BNode * left_left = left->left;
      BNode * left_right = left->right;

      x->left = left_right;

      BNode * tmp = treap_remove_root_rec(x);

      left->right = tmp;  
      return left;
    }
  }
}

