#include "sll.h"

Node * sll_insert(Node * x, int k)
	_(requires _dryad_sll(x))
	_(ensures  _dryad_sll(\result))
	_(ensures  _dryad_keys(\result) == \intset_union(\old(_dryad_keys(x)), \intset_singleton(k)))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	if (x == NULL) {
		Node * leaf = (Node *) malloc(sizeof(Node));
		_(assume leaf != NULL)
		leaf->key = k;
		leaf->next = NULL;
		return leaf;
	} else if (k > x->key) {
		Node * tmp = sll_insert(x->next, k);
		x->next = tmp;
		return x;
	}	else {	
		Node * new_root = (Node *) malloc(sizeof(Node));
		_(assume new_root != NULL)

		new_root->key = k;
		new_root->next = x;
		return new_root;
	}
}


