#include "sll.h"

Node * insert_sorted(Node *x, int k)
	_(requires _dryad_srtl(x))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_sll(\result))
	_(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(x)), \intset_singleton(k)))
;

Node * insertion_sort_copy(Node * l)
	_(requires _dryad_sll(l))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_keys(\result) == \old(_dryad_keys(l)))
{
	_(assume mutable_list(l))
	if (l == NULL) {
		return l;
	} else {
		Node * tl = insertion_sort_copy(l->next);

		Node * nl = insert_sorted(tl, l->key);
		//free(tl); // complicates verification, client should decide
		return nl;
	}
}

