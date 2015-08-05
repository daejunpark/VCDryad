#include "dryad_sll.h"
//#include "sll-dryad.h"

_(dryad)
SNnode * sll_insert(SNnode * x, int k)
	_(requires sll(x))
	_(ensures  sll(\result))
	_(ensures  sll_keys(\result) == \intset_union(\old(sll_keys(x)), \intset_singleton(k)))
{
	
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	if (x == NULL) {
		_(assert \false)
		SNnode * leaf = (SNnode *) malloc(sizeof(SNnode));
		//_(assert \false)
		//_(assert leaf != NULL)
		//_(assume leaf != NULL)
		//_(assert \false)

		leaf->key = k;
		leaf->next = NULL;
		return leaf;

	} else if (k > x->key) {
		SNnode * tmp = sll_insert(x->next, k);
		x->next = tmp;
		return x;
	}	else {	
		SNnode * new_root = (SNnode *) malloc(sizeof(SNnode));
		_(assume new_root != NULL)

		new_root->key = k;
		new_root->next = x;
		return new_root;
	}
}


