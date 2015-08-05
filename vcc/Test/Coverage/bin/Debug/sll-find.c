#include "sll.h"

int sll_find(Node * x, int k)
	_(requires _dryad_sll(x))
	_(ensures  _dryad_sll(x) && _dryad_N(x) == \old(_dryad_N(x)))
	_(ensures  \intset_in(k, _dryad_keys(x)) <==> \result == 0)
	_(ensures !\intset_in(k, _dryad_keys(x)) <==> \result ==-1)
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))

	if (x == NULL) {
		return -1;
	} else if (k == x->key) {
		return 0;
	}	else {
		int res = sll_find(x->next, k);
		return res;
	}	
}
