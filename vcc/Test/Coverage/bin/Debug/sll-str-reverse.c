#include "sll.h"

Node * sll_reverse(Node * x)
	_(requires _dryad_sll(x))
//	_(ensures  _dryad_sll(\result))
//	_(ensures  _dryad_keys(\result) == \old(keys(x)))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	Node * y = NULL;

	//while (x != NULL)
	//	_(invariant x != NULL ==> \writable(x) && \mutable(x))
	if (x != NULL)
	{
		Node * tmp = x->next;
		x->next = y;
		y = x;
		x = tmp;
		_(assume x != NULL ==> \writable(x) && \mutable(x))
	}
	return y;
}
