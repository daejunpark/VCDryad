#include "dryad_sll.h"

_(dryad)
SNnode * sll_insert_front(SNnode * x, int k)
	_(requires sll(x))
	_(ensures  sll(\result))
	_(ensures  sll_keys(\result) == \intset_union(\old(sll_keys(x)), \intset_singleton(k)))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
		SNnode * head = (SNnode *) malloc(sizeof(SNnode));
		_(assume head != NULL)
		head->key = k;
		head->next = x;
		return head;
}
