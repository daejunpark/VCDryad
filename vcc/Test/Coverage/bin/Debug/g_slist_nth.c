#include "sll.h"

Node * g_slist_nth(Node * list, int n)
	_(requires _dryad_sll(list))
	_(requires n >= 0)
	_(ensures _dryad_sll(list))
	_(ensures _dryad_sll(\result))
	_(ensures \result == NULL ==> ((\natural) n >= _dryad_llen(list)))
	_(ensures \result != NULL ==> ((_dryad_llen(list) - _dryad_llen(\result)) == (\natural) n))
	_(ensures \result != NULL ==> (_dryad_lseglen(list, \result) == (\natural) n))
	_(ensures \lsegStar(list, \result))
{
	_(assume mutable_list(list))
  _(ghost Node * old_list = \old(list) ;)
  _(ghost int old_n = \old(n))

	while(n > 0 && list != NULL)
		_(invariant _dryad_sll(list))
		_(invariant \lsegStar(old_list, list))
		_(invariant mutable_list(list))
		_(invariant n >= 0)
		_(invariant list == NULL ==> ((\natural)old_n >= _dryad_llen(old_list)))
		_(invariant list != NULL ==> (\natural)(old_n - n) == (_dryad_llen(old_list) - _dryad_llen(list)))
		_(invariant _dryad_llen(old_list) == (_dryad_lseglen(old_list, list) + _dryad_llen(list)))
		_(invariant list != NULL ==> (_dryad_lseglen(old_list, list) == (\natural)(old_n - n)))
	{
		_(assume unfoldMutable(list))
		n--;
		list = list->next; 
		_(ghost LemmaSkip(old_list, list))
	}
	return list;
}

