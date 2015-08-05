#include "dryad_rbt.h"

_(logic \bool mutable_rbt(RBTNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
RBTNode * rbt_insert_right_fixup(RBTNode * x)
  _(requires x != NULL)
  _(requires !\oset_in(x, rbt_reach(x->right)))
  _(requires !\oset_in(x, rbt_reach(x->left)))
  _(requires !\intset_in(x->key, \intset_union(rbt_keys(x->right), rbt_keys(x->left))))

  _(requires x->right != NULL)
  _(requires rbt(x->right->left))
  _(requires \intset_lt_one2(rbt_keys(x->right->left), x->right->key))
  _(requires rbt(x->right->right))
  _(requires \intset_lt_one1(x->right->key, rbt_keys(x->right->right)))
  _(requires \oset_disjoint(rbt_reach(x->right->left), rbt_reach(x->right->right)))
  _(requires !\oset_in(x->right, rbt_reach(x->right->right)))
  _(requires !\oset_in(x->right, rbt_reach(x->right->left)))
  _(requires !\oset_in(x->right, rbt_reach(x->left)))
  _(requires !\intset_in(x->right->key, \intset_union(rbt_keys(x->right->left), rbt_keys(x->right->right))))

  _(requires \intset_lt_one2(rbt_keys(x->left), x->key))
  _(requires rbt(x->left))
  _(requires \intset_lt_one1(x->key, rbt_keys(x->right)))

  _(requires rbt_bh(x->right->left) == rbt_bh(x->right->right))
  _(requires rbt_bh(x->right->right) == rbt_bh(x->left))

  _(requires x->right->color != 0)
  _(requires (x->color == 0 && (rbt_black(x->right->left) || rbt_black(x->right->right)))
      || (rbt_black(x->left) && rbt_black(x->right->left) && rbt_black(x->right->right)))
  _(requires \oset_disjoint(rbt_reach(x->left), rbt_reach(x->right->left)))
  _(requires \oset_disjoint(rbt_reach(x->left), rbt_reach(x->right->right)))
  
  _(ensures \result != NULL)
  _(ensures rbt_keys(\result) == \old(rbt_keys(x)))
  _(ensures rbt_bh(\result) == \old(rbt_bh(x)))

  _(ensures rbt(\result->left))
  _(ensures \intset_lt_one2(rbt_keys(\result->left), \result->key))
  _(ensures rbt(\result->right))
  _(ensures \intset_lt_one1(\result->key,  rbt_keys(\result->right)))
  _(ensures rbt_bh(\result->left) == rbt_bh(\result->right))
  _(ensures (\result->color == 0) 
    || ((rbt_black(\result->left) || rbt_black(\result->right))
      && (!\old(rbt_black(x)) || (rbt_black(\result->left) && rbt_black(\result->right))) ) )
  
{
  _(assume mutable_rbt(x))
  _(assume mutable_rbt(x->left))
  _(assume mutable_rbt(x->right))

  RBTNode * l = x->left;
  
  RBTNode * r = x->right;
  
  if (l != NULL && l->color != 0) {
    r->color = 0;

    l->color = 0;

    x->color = 1;
    return x;
  } else {
    
    RBTNode * rl = r->left;
    _(assume mutable_rbt(rl))
    RBTNode * rr = r->right;
    _(assume mutable_rbt(rr))

    if (rl != NULL && rl->color != 0) {
      
      RBTNode * rll = rl->left;

      RBTNode * rlr = rl->right;

      
      r->left  = rlr;

      x->right   = rll;

      x->color  = 1;

      rl->right  = r;
      rl->left = x;
      rl->color = 0;

      return rl;
    } else if (rr != NULL && rr->color != 0) {
      // left rotation

      x->right = rl;
      x->color = 1;

      r->left = x;
      r->color = 0;
      return r;
    } else {
      return x;
    }

  }

}

