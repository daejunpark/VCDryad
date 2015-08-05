#include "dryad_avl.h"

_(logic \bool mutable_avl(AVLNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
int avl_find_smallest(AVLNode * x)
	_(requires x != NULL && avl(x))
	_(ensures x != NULL)
	_(ensures avl(x))
	_(ensures avl_reach(x) == \old(avl_reach(x)))
	_(ensures avl_keys(x) == \old(avl_keys(x)))
	_(ensures avl_height(x) == \old(avl_height(x)))
	_(ensures \intset_le_one1(\result, avl_keys(x)))
	_(ensures \intset_in(\result, avl_keys(x)))
{
	_(assume mutable_avl(x))
	if (x->left == NULL) {
		return x->key;
	} else {
		int r = avl_find_smallest(x->left);
		return r;
	}
}

