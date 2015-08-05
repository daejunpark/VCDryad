#include "dryad_rbt.h"

_(logic \bool mutable_rbt(RBTNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
int rbt_find_smallest(RBTNode * x)
	_(requires x != NULL && rbt(x))
	_(ensures x != NULL && rbt(x))
	_(ensures rbt_reach(x) == \old(rbt_reach(x)))
	_(ensures rbt_keys(x) == \old(rbt_keys(x)))
	_(ensures rbt_bh(x) == \old(rbt_bh(x)))
	_(ensures rbt_black(x) == \old(rbt_black(x)))
	_(ensures \intset_in(\result, rbt_keys(x)))
  _(ensures \intset_le_one1(\result, rbt_keys(x)))
{
	_(assume mutable_rbt(x))
	
	if (x->left == NULL) {
		return x->key;
	} else {
		int r = rbt_find_smallest(x->left);
		return r;
	}
}

