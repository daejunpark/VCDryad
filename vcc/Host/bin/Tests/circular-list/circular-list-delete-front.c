#include "dryad_circular_list.h"

_(logic \bool mutable_list(CNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
CNode * circular_list_delete_front(CNode * x)
	_(requires x != NULL)
	_(requires x->next != NULL)
	_(requires lseg(x->next, x))
	_(requires !\oset_in(x, lseg_reach(x->next, x)))

	_(ensures x == \old(x->next) ==> \result == NULL)
	_(ensures x != \old(x->next) ==> x->next == \result)
	_(ensures x != \old(x->next) ==> lseg(\result, x))
	_(ensures x != \old(x->next) ==> !\oset_in(x, lseg_reach(\result, x)))
{
	_(assume mutable_list(x))
	_(assume \malloc_root(x))
	CNode * next = x->next;

	if (next == x) {
		free(next);
		return NULL;
	} else {

		_(assume mutable_list(next))
		_(assume \malloc_root(next))
		CNode * next_next = next->next;

		free(next);

		x->next = next_next;

		return next_next;
	}
}

