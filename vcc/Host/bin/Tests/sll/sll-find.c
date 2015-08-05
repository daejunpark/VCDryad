#include "dryad_sll.h"

_(dryad)
int sll_find(SNnode * x, int k)
	_(requires sll(x))
	_(ensures  sll(x)) 
	_(ensures  \intset_in(k, sll_keys(x)) <==> \result == 0)
	_(ensures !\intset_in(k, sll_keys(x)) <==> \result ==-1)
{
  _(assume x != NULL ==> \mutable(x) && \writable(x)) 

	if (x == NULL) {
		return -1;
	} else if (k == x->key) {
		return 0;
	}	else {
    SNnode * y = x->next;
		int res = sll_find(y, k);
		return res;
	}	
}
