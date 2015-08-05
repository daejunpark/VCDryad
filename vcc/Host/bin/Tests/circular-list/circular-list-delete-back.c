#include "dryad_circular_list.h"

_(logic \bool mutable_list(CNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
CNode * lseg_delete_back(CNode * hd, CNode * tl)
	_(requires hd != NULL)
	_(requires tl != NULL)
	_(requires hd != tl)
	_(requires lseg(hd, tl))
	_(requires !\oset_in(tl, lseg_reach(hd, tl)))

	_(ensures hd->next != NULL ==> \result != NULL)
	_(ensures lseg(\result, tl))
	_(ensures !\oset_in(tl, lseg_reach(\result, tl)))
{
	_(assume mutable_list(hd))
	_(assume \malloc_root(hd))

	CNode * next = hd->next;

	if (next == NULL) return next;
	if (next == tl) {
		free(hd);
		return next;
	} else {

		CNode * hd_next = lseg_delete_back(next, tl);

		hd->next = hd_next;

		return hd;
	}
}

_(dryad)
CNode * circular_list_delete_back(CNode * x)
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

		CNode * hd_next = lseg_delete_back(next, x);

		x->next = hd_next;

		return hd_next;
	}
}
