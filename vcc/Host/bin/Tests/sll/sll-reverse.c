#include "dryad_sll.h"

_(dryad)
SNnode * sll_reverse(SNnode * x)
	_(requires sll(x))
  _(ensures  sll(\result))
	_(ensures  sll_keys(\result) == \old(sll_keys(x)))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	SNnode * y = NULL;

	while (x != NULL)
		_(invariant x != NULL ==> \writable(x) && \mutable(x))
		_(invariant sll(x))
		_(invariant sll(y))
		_(invariant \oset_disjoint(sll_reach(x), sll_reach(y)))
		_(invariant \intset_union(sll_keys(x), sll_keys(y)) == \old(sll_keys(x)))
	{
		SNnode * tmp = x->next;
		x->next = y;
		y = x;
		x = tmp;
		_(assume x != NULL ==> \writable(x) && \mutable(x))
	}
	return y;
}
