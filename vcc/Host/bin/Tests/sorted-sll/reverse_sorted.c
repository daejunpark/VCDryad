#include "dryad_srtl.h"

_(dryad)
SNnode * reverse_sorted(SNnode * l)
	_(requires srtl(l))
	_(ensures rsrtl(\result))
	_(ensures sll_keys(\result) == \old(sll_keys(l)))
{
	_(assume l != NULL ==> \mutable(l) && \writable(l))
	SNnode * r = NULL;

	while(l != NULL)
		_(invariant srtl(l))
		_(invariant rsrtl(r))
		_(invariant \oset_disjoint(sll_reach(l), sll_reach(r)))
		_(invariant l != NULL ==> \intset_le(sll_keys(r), \intset_singleton(l->key)))
		_(invariant \old(sll_keys(l)) == \intset_union(sll_keys(l), sll_keys(r)))
		_(invariant l != NULL ==> mutable_list(l))
	{
		SNnode * t = l->next;
		
		l->next = r;
		r = l;
		l = t;
  	_(assume l != NULL ==> \mutable(l) && \writable(l))
	}
	return r;
}

