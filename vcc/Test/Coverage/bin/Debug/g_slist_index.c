#include "sll.h"

int g_slist_index(Node * list, int data _(out Node *ret_list))
	_(requires _dryad_sll(list))
	_(requires _dryad_llen(list) < INT_MAX)
	_(ensures _dryad_sll(list))
	_(ensures \intset_in(data, _dryad_keys(list)) <==> \result >= 0)
	_(ensures !\intset_in(data, _dryad_keys(list)) <==> \result == -1)
	_(ensures \lsegStar(list, ret_list))
	_(ensures ret_list != NULL ==> _dryad_lseglen(list, ret_list) == (\natural) \result)
	_(ensures ret_list != NULL ==> ret_list->key == data)
{
	_(assume mutable_list(list))
	_(ghost ret_list = list ;)
	int i; 

	i = 0;
  _(ghost Node * old_list = \old(list) ;)
	while(list != NULL)
		_(invariant _dryad_sll(list))
		_(invariant _dryad_sll(old_list))
		_(invariant \lsegStar(old_list, list))
		_(invariant _dryad_llen(old_list) - _dryad_llen(list) == (\natural) i)
		_(invariant !\intset_in(data, _dryad_lsegk(old_list, list)))
		_(invariant _dryad_lseglen(old_list, list) == (\natural) i)
		_(invariant i < INT_MAX)
		_(invariant i >= 0)
		_(invariant mutable_list(list))
		_(invariant ret_list == list)
	{
		_(assume unfoldMutable(list))
		if(list->key == data) {
			return i;
		}
		i ++;
		list = list->next;
		_(ghost ret_list = list ;)
		_(ghost LemmaSkip(\old(list), list))
	}
	return -1;
}

