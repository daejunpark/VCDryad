#include "sll.h"

Node * g_slist_reverse(Node * list)
	_(requires _dryad_sll(list))
	_(ensures _dryad_sll(\result))
	_(ensures _dryad_keys(\result) == \old(_dryad_keys(list)))
{
	_(assume mutable_list(list))
	Node * prev = NULL;
	while(list != NULL) 
		_(invariant \sllStar(list, prev))
		_(invariant mutable_list(list))
		_(invariant \intset_union(_dryad_keys(list), _dryad_keys(prev)) == \old(_dryad_keys(list)))
	{
		_(assume unfoldMutable(list))

		Node * next = list->next;
		list->next = prev;
		prev = list;
		list = next;
	}
	return prev;
}
