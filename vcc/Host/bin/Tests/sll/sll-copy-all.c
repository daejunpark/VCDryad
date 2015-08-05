#include "dryad_sll.h"

_(dryad)
SNnode * sll_copy(SNnode *x, int k)
	_(requires sll(x))
  _(ensures sll(x))
  _(ensures sll_reach(x) == \old(sll_reach(x)))
	_(ensures sll(\result))
	_(ensures \oset_disjoint(sll_reach(\result), sll_reach(x)))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	if (x == NULL) {
		return x;
	} else {
		SNnode * tmp = sll_copy(x->next, k);
		SNnode * new_node = (SNnode *) malloc(sizeof(SNnode));
		_(assume new_node != NULL)
    int tmp_key = x->key;
		new_node->key = tmp_key;
		new_node->next = tmp;
		return new_node;
	}
}

