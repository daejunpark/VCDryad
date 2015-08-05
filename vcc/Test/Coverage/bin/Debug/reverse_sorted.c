#include "sll.h"

Node * reverse_sorted(Node * l)
	_(requires _dryad_srtl(l))
	_(ensures _dryad_rsrtl(\result))
	_(ensures _dryad_keys(\result) == \old(_dryad_keys(l)))
{
	_(assume mutable_list(l))
	Node * r = NULL;

	while(l != NULL)
		_(invariant _dryad_srtl(l))
		_(invariant _dryad_rsrtl(r))
		_(invariant \disjoint(_dryad_N(l), _dryad_N(r)))
		_(invariant l != NULL ==> \intset_ge(l->key, _dryad_keys(r)))
		_(invariant \old(_dryad_keys(l)) == \intset_union(_dryad_keys(l), _dryad_keys(r)))
		_(invariant mutable_list(l))
	{
		_(assume unfoldMutable(l))
		Node * t = l->next;
		
		l->next = r;
		r = l;
		l = t;
	}
	return r;
}

