#include "sll.h"

Node * sll_insert_front(Node * x, int k)
	_(requires _dryad_sll(x))
	_(ensures  _dryad_sll(x))
	_(ensures  _dryad_sll(\result))
	_(ensures  _dryad_keys(\result) == \intset_union(\old(_dryad_keys(x)), \intset_singleton(k)))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	if (x == NULL) {	
		Node * head = (Node *) malloc(sizeof(Node));
		_(assume head != NULL)
		head->key = k;
		head->next = NULL;
    _(assert _dryad_sll(head))
		return head;
	} else {
		Node * head = (Node *) malloc(sizeof(Node));
		_(assume head != NULL)
		head->key = k;
		head->next = x;
    _(assert _dryad_sll(x))
    _(assert _dryad_sll(head))
		return head;
	}
}
