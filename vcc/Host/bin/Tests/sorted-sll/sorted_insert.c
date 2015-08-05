#include "dryad_srtl.h"

_(dryad)
SNnode * sorted_insert(SNnode *x, int k)
	_(requires srtl(x))
  _(requires !\intset_in(k, sll_keys(x)))
	_(ensures srtl(\result))
	_(ensures sll(\result))
	_(ensures sll_keys(\result) == \intset_union(\old(sll_keys(x)), \intset_singleton(k)))
{
	_(assume mutable_list(x))

	if (x == NULL) {
		SNnode * tail = (SNnode *) malloc(sizeof(SNnode));
		_(assume tail != NULL)

		tail->key = k;
		tail->next = NULL;

		return tail;
	} 
	else if (k > x->key) {
		SNnode * tmp = sorted_insert(x->next, k);

		x->next = tmp;

		return x;
	} 
	else {

		SNnode * head = (SNnode *) malloc(sizeof(SNnode));
		_(assume head != NULL)

		head->key = k;
		head->next = x;

		return head;
	}
}

