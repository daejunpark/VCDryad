#include "dryad_rbt.h"

_(logic \bool mutable_rbt(RBTNode * x) = x != NULL ==> \mutable(x) && \writable(x))

RBTNode * rbt_insert_left_fixup(RBTNode * x)
	_(requires x != NULL)
	_(requires !\oset_in(x, rbt_reach(x->left)))
	_(requires !\oset_in(x, rbt_reach(x->right)))
	_(requires !\intset_in(x->key, \intset_union(rbt_keys(x->left), rbt_keys(x->right))))

	_(requires x->left != NULL)
	_(requires rbt(x->left->left))
	_(requires \intset_lt_one2(rbt_keys(x->left->left), x->left->key))
	_(requires rbt(x->left->right))
	_(requires \intset_lt_one1(x->left->key, rbt_keys(x->left->right)))
	_(requires \oset_disjoint(rbt_reach(x->left->left), rbt_reach(x->left->right)))
	_(requires !\oset_in(x->left, rbt_reach(x->left->right)))
	_(requires !\oset_in(x->left, rbt_reach(x->left->left)))
	_(requires !\oset_in(x->left, rbt_reach(x->right)))
	_(requires !\intset_in(x->left->key, \intset_union(rbt_keys(x->left->left), rbt_keys(x->left->right))))

	_(requires \intset_lt_one2(rbt_keys(x->left), x->key))
	_(requires rbt(x->right))
	_(requires \intset_lt_one1(x->key, rbt_keys(x->right)))

	_(requires rbt_bh(x->left->left) == rbt_bh(x->left->right))
	_(requires rbt_bh(x->left->right) == rbt_bh(x->right))

	_(requires x->left->color != 0)
	_(requires (x->color == 0 && (rbt_black(x->left->left) || rbt_black(x->left->right)))
			|| (rbt_black(x->right) && rbt_black(x->left->left) && rbt_black(x->left->right)))
	_(requires \oset_disjoint(rbt_reach(x->right), rbt_reach(x->left->left)))
	_(requires \oset_disjoint(rbt_reach(x->right), rbt_reach(x->left->right)))
	
  // ------------------------------------------------------------------------------------------
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
;

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
;
 
_(dryad)
RBTNode * rbt_insert(RBTNode * x, int k)
  _(requires rbt(x))
  _(requires !\intset_in(k, rbt_keys(x)))
  // -----------------------------------------
  _(ensures \result != NULL)
  _(ensures rbt_bh(  \result) == \old(rbt_bh(x)))
  _(ensures rbt(\result))

  _(ensures rbt(\result->left))
  _(ensures rbt(\result->right))
  _(ensures \intset_lt_one2(rbt_keys(\result->left), \result->key))
  _(ensures \intset_lt_one1(\result->key, rbt_keys(\result->right)))
  _(ensures rbt_keys(\result) == \intset_union_one1(k, \old(rbt_keys(x))))

  _(ensures rbt_bh(\result->left) == rbt_bh(\result->right))
  _(ensures x != NULL)
  _(ensures rbt_bh(x->left) == rbt_bh(x->right))
	_(ensures (\result->color == 0) 
		|| ((rbt_black(\result->left) || rbt_black(\result->right))
			&& (!\old(rbt_black(x)) || (rbt_black(\result->left) && rbt_black(\result->right))) ) )
{
  _(assume mutable_rbt(x))
  _(assume mutable_rbt(x->left))
  _(assume mutable_rbt(x->right))

  if (x == NULL) {
    RBTNode * leaf = (RBTNode *) malloc(sizeof(RBTNode));
    _(assume leaf != NULL)
    leaf->left  = NULL;
    leaf->right = NULL;
    leaf->key   = k;
    leaf->color = 1;
    return leaf;
  }
  
  if (k < x->key) { // left branch
    RBTNode * res = rbt_insert(x->left, k);

    x->left = res;

    RBTNode * tmp = rbt_insert_left_fixup(x);
    
    return tmp;

  } else {
    RBTNode * x_right = x->right;
    RBTNode * res = rbt_insert(x_right, k);

    x->right = res;
    
    RBTNode * tmp = rbt_insert_right_fixup(x);
    
    return tmp;
  }
}
