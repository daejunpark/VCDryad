#include "dryad_circular_list.h"

_(logic \bool mutable_list(CNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
CNode * circular_list_insert_front(CNode * x)
	_(requires x != NULL)
	_(requires x->next != NULL)
	_(requires lseg(x->next, x))
	_(requires !\oset_in(x, lseg_reach(x->next, x)))

	_(ensures \result != x)
	_(ensures \result == x->next)
  _(ensures \result != NULL)
  _(ensures lseg(\result, x))
  _(ensures !\oset_in(x, lseg_reach(\result, x)))
{
  
	_(assume mutable_list(x))
	CNode * tmp = x->next;


	CNode * hd = (CNode *) malloc(sizeof(CNode)) ;
	_(assume hd != NULL)

	hd->next = tmp;

	x->next = hd; 

	return hd;
}
