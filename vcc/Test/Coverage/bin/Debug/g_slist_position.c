#include "sll.h"

int g_slist_position(Node * list, Node * link)
	_(requires _dryad_sll(list))
	_(requires _dryad_llen(list) < INT_MAX)
	_(ensures _dryad_sll(list))
	_(ensures \result == -1 ==> !(link \in _dryad_N(list)))
	_(ensures (link \in _dryad_N(list)) ==> \result >= 0)
	_(ensures \result >= 0 ==> \lsegStar(list, link))
	_(ensures \result >= 0 ==> _dryad_lseglen(list, link) == (\natural)\result)
{
	_(assume mutable_list(list))
	int i;

	i = 0;
  _(ghost Node * old_list = \old(list) ;)
	while(list != NULL)
		_(invariant _dryad_sll(list))
		_(invariant \lsegStar(old_list, list))
		_(invariant !(link \in _dryad_lsegN(old_list, list)))
		_(invariant mutable_list(list))
		_(invariant _dryad_llen(old_list) - _dryad_llen(list) == (\natural)i)
		_(invariant _dryad_lseglen(old_list, list) == (\natural) i)
		_(invariant i < INT_MAX)
		_(invariant i >= 0)
	{
		_(assume unfoldMutable(list))

		if (list == link) {
			return i;
		}
		i ++;
		list = list->next;
		_(ghost LemmaSkip(\old(list), list))
	}
	return -1;
}

