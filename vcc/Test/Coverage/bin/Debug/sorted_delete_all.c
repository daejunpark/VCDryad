#include "sll.h"

Node * sorted_delete_all(Node * x, int k)
	_(requires _dryad_srtl(x))
	_(ensures  _dryad_srtl(\result))
	_(ensures  \intset_in(k, \old(_dryad_keys(x))) ==> (_dryad_keys(\result) == \intset_diff(\old(_dryad_keys(x)), \intset_singleton(k))))
	_(ensures !\intset_in(k, \old(_dryad_keys(x))) ==> (_dryad_keys(\result) == \old(_dryad_keys(x))))
{
	_(assume mutable_list(x))
	_(assume x != NULL ==> \malloc_root(x))
		
	if (x == NULL) {
		return x;
	} else if (x->key == k) {
		Node * tmp = sorted_delete_all(x->next, k);
		free(x);
		return tmp;
	} else {
		Node * tmp = sorted_delete_all(x->next, k);
		x->next = tmp;
		return x;
	}
}

