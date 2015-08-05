#include "sll.h"

Node * merge_sort_copy(Node * l1, Node * l2)
	_(requires _dryad_srtl(l1))
	_(requires _dryad_srtl(l2))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(l1)), \old(_dryad_keys(l2))))
{
	_(assume mutable_list(l1))
	_(assume mutable_list(l2))

	if (l1 == NULL) {
		return l2;
	} else if (l2 == NULL) {
		return l1;
	} else {
		if (l1->key <= l2->key) {
			Node * tl = merge_sort_copy(l1->next, l2);
			Node * nl = (Node *) malloc(sizeof(Node));
      _(assume nl != NULL)
      int l1_key = l1->key;
			nl->key  = l1_key;
			nl->next = tl;
			return nl;	
		} else {
			Node * tl = merge_sort_copy(l1, l2->next);
			Node * nl = (Node *) malloc(sizeof(Node));
      _(assume nl != NULL)
      
      int l2_key = l2->key;
			nl->key = l2_key;
			nl->next = tl;

			return nl;
		}
	}
}
