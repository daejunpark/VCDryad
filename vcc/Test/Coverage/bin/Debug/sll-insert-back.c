#include "sll.h"

Node * sll_insert_back(Node * x, int k)
//	_(requires _dryad_sll(x))
//	_(ensures  _dryad_sll(\result))
//	_(ensures  _dryad_keys(\result) == \intset_union(\old(_dryad_keys(x)), \intset_singleton(k)))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	if (x == NULL) {
		Node * tail = (Node *) malloc(sizeof(Node));
		_(assume tail != NULL)
		tail->key  = k;	
		tail->next = NULL;
		return tail;
	} else {
		Node * tmp = sll_insert_back(x->next, k);
		x->next = tmp;
		return x;
	}
}
