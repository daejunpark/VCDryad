#include "dryad_sll.h"

_(dryad)
SNnode * sll_delete_all(SNnode * x, int k)
	_(requires sll(x))
	_(ensures  sll(\result))
	_(ensures  \intset_in(k, \old(sll_keys(x))) ==> 
                (sll_keys(\result) == \intset_diff(\old(sll_keys(x)), \intset_singleton(k))))
	_(ensures !\intset_in(k, \old(sll_keys(x))) ==> (sll_keys(\result) == \old(sll_keys(x))))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	_(assume x != NULL ==> \malloc_root(x))
	if (x == NULL) {
		return x;
	} else if (x->key == k) {
		SNnode * tmp = sll_delete_all(x->next, k);
		free(x);
		return tmp;
	} else {
		SNnode * tmp = sll_delete_all(x->next, k);
		x->next = tmp;
		return x;
	}
}

