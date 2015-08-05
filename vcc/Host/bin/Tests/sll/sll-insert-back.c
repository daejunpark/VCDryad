#include "dryad_sll.h"
//#include "sll-dryad.h"

_(dryad)
SNnode * sll_insert_back(SNnode * x, int k)
	_(requires sll(x))
  _(requires \assume(glob_reach() == \oset_union(sll_reach(x), sll_keys_reach(x))))
	_(ensures  sll(\result)) 
	_(ensures  sll_keys(\result) == \intset_union(\old(sll_keys(x)), \intset_singleton(k))) 
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	if (x == NULL) {
		SNnode * tail = (SNnode *) malloc(sizeof(SNnode));
		_(assume tail != NULL)
		tail->key  = k;	
		tail->next = NULL;
		return tail;
	} else {
		SNnode * tmp = sll_insert_back(x->next, k);
		x->next = tmp;
		return x;
	}
}
