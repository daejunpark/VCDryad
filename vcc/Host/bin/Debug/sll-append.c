#include "dryad_sll.h"

_(dryad)
SNnode * sll_append(SNnode * x1, SNnode * x2)
	_(requires sll(x1))
	_(requires sll(x2))
	_(requires \oset_disjoint(sll_reach(x1), sll_reach(x2)))
  _(ensures sll(\result))
  _(ensures sll_keys(\result) == \intset_union(\old(sll_keys(x1)), \old(sll_keys(x2))))
{
	_(assume x1 != NULL ==> \mutable(x1) && \writable(x1))
	_(assume x2 != NULL ==> \mutable(x2) && \writable(x2))
	if (x1 == NULL) {
		return x2;
	} else {
    SNnode * x1_next = x1->next;
		SNnode * tmp = sll_append(x1_next, x2);
		x1->next = tmp;
		return x1;
	}
	
}
