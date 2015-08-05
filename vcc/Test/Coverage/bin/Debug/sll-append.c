#include "sll.h"

Node * sll_append(Node * x1, Node * x2)
	_(requires _dryad_sll(x1))
	_(requires _dryad_sll(x2))
	_(requires \disjoint(_dryad_N(x1), _dryad_N(x2)))
{
	_(assume x1 != NULL ==> \mutable(x1) && \writable(x1))
	_(assume x2 != NULL ==> \mutable(x2) && \writable(x2))
	if (x1 == NULL) {
		return x2;
	} else {
		Node * tmp = sll_append(x1->next, x2);
		x1->next = x2;
		return x1;
	}
	
}
