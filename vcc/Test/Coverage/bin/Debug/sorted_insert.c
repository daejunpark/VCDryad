#include "sll.h"

Node * sorted_insert(Node *x, int k)
	_(requires _dryad_srtl(x))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_sll(\result))
	_(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(x)), \intset_singleton(k)))
{
	_(assume mutable_list(x))

	if (x == NULL) {
		Node * tail = (Node *) malloc(sizeof(Node));
		_(assume tail != NULL)

		tail->key = k;
		tail->next = NULL;

		return tail;
	} 
	else if (k > x->key) {
		Node * tmp = sorted_insert(x->next, k);

		x->next = tmp;

		return x;
	} 
	else {

		Node * head = (Node *) malloc(sizeof(Node));
		_(assume head != NULL)

		head->key = k;
		head->next = x;
		return head;
	}
}

