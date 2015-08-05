#include "dryad_circular_list.h"

_(logic \bool mutable_list(CNode * x) = x != NULL ==> \mutable(x) && \writable(x))

CNode * lseg_insert_back(CNode * hd, CNode * tl)
	_(requires hd != NULL && tl != NULL)
	_(requires lseg(hd, tl))
	_(requires !\oset_in(tl, lseg_reach(hd, tl)))

	_(ensures \result != tl)
	_(ensures lseg(\result, tl))
	_(ensures !\oset_in(tl, lseg_reach(\result, tl)))
;

_(dryad)
CNode * circular_list_insert_back(CNode * x)
	_(requires x != NULL)
	_(requires x->next != NULL)
	_(requires lseg(x->next, x))
	_(requires !\oset_in(x, lseg_reach(x->next, x)))

	_(ensures \result != x)
	_(ensures \result == x->next)
	_(ensures lseg(\result, x))
	_(ensures !\oset_in(x, lseg_reach(\result, x)))
{
	_(assume mutable_list(x))
	CNode * next = x->next;

	if (next == x) {
		CNode * tl = (CNode *) malloc(sizeof(CNode));
		_(assume tl != NULL)

		tl->next = x;

		x->next = tl;
		
		return tl;
	} else {
		CNode * tl = lseg_insert_back(next, x);

		x->next = tl;

		return tl;
	}
}

