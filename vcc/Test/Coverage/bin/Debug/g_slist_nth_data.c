#include "sll.h"

int g_slist_nth_data(Node * list, int n _(out Node * ret_list))
	_(requires _dryad_sll(list))
	_(requires n >= 0)
	_(ensures _dryad_sll(list))
	_(ensures _dryad_sll(ret_list))
	_(ensures \lsegStar(list, ret_list))
	_(ensures (\natural)n >= _dryad_llen(list) ==> \result == -1)
	_(ensures ret_list != NULL ==> \result == ret_list->key)
	_(ensures ret_list != NULL ==> (_dryad_lseglen(list, ret_list) == (\natural)n))
{
	_(ghost ret_list = list ;)
	_(assume mutable_list(list))
	int res;
  _(ghost Node * old_list = \old(list) ;)
  _(ghost int old_n = \old(n) ;)
	while(n > 0 && list != NULL)
		_(invariant _dryad_sll(list))
		_(invariant _dryad_sll(ret_list))
		_(invariant \lsegStar(old_list, list))
		_(invariant mutable_list(list))
		_(invariant n >= 0)
		_(invariant list == NULL ==> (\natural) old_n >= _dryad_llen(old_list))
		_(invariant list != NULL ==> (_dryad_llen(old_list) - _dryad_llen(list)) == (\natural) (old_n - n))
		_(invariant list != NULL ==> (_dryad_lseglen(old_list, list) == (\natural) (old_n - n)))
		_(invariant ret_list == list)
	{
		_(assume unfoldMutable(list))
		n--;
		list = list->next;
    _(ghost ret_list = list ;)
		_(ghost LemmaSkip(old_list, list))
	}
	if (list != NULL) {
		res = list->key;
	} else {
		res = -1;
	}
	return res;
}
