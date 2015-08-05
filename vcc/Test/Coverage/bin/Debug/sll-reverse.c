#include "sll.h"

Node * sll_reverse(Node * x)
	_(requires _dryad_sll(x))
  _(ensures  _dryad_sll(\result))
	_(ensures  _dryad_keys(\result) == \old(_dryad_keys(x)))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	Node * y = NULL;

	while (x != NULL)
		_(invariant x != NULL ==> \writable(x) && \mutable(x))
		_(invariant _dryad_sll(x))
		_(invariant _dryad_sll(y))
		_(invariant \disjoint(_dryad_N(x), _dryad_N(y)))
		_(invariant \intset_union(_dryad_keys(x), _dryad_keys(y)) == \old(_dryad_keys(x)))
	{
		Node * tmp = x->next;
		x->next = y;
//		_(assert \disjoint(_dryad_N(tmp), _dryad_N(y)))
		y = x;
		x = tmp;
		_(assume x != NULL ==> \writable(x) && \mutable(x))
	}
	return y;
}
