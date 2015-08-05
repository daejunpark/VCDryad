#include "sll.h"

Node * g_slist_find(Node * list, int data)
	_(requires _dryad_sll(list))
	_(ensures  _dryad_sll(\result))
	_(ensures \lsegStar(list, \result))
	_(ensures \result == NULL || \result->key == data)
{
	_(assume mutable_list(list))
  _(ghost Node * old_list = \old(list))
	while(list != NULL)
		_(invariant _dryad_sll(list))
		_(invariant \lsegStar(old_list, list))
		_(invariant mutable_list(list))
	{
		_(assume unfoldMutable(list))
		if (list->key == data) {
			break;
		}
		list = list->next;
		_(ghost LemmaSkip(\old(list), list))

	}
	return list;
}

