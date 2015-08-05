#include "dryad_rbt.h"

_(logic \bool mutable_rbt(RBTNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
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
	//_(ensures \intset_eq(rbt_keys(\result), \old(rbt_keys(x))))
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

	if (r != NULL && r->color != 0) {

		l->color = 0;

		r->color = 0;

		x->color = 1;

		return x;
	} else {
		
		RBTNode * ll = l->left;
		_(assume mutable_rbt(ll))
		RBTNode * lr = l->right;
		_(assume mutable_rbt(lr))

		if (lr != NULL && lr->color != 0) {
			
			RBTNode * lrl = lr->left;

			RBTNode * lrr = lr->right;
			
			l->right  = lrl;

			x->left   = lrr;
			x->color  = 1;

			lr->left  = l;
			lr->right = x;
			lr->color = 0;

			return lr;
		} else if (ll != NULL && ll->color != 0) {
			// right rotation

			x->left = lr;
			x->color = 1;

			l->right = x;
			l->color = 0;

			return l;
		} else {
			return x;
		}
	}
}
