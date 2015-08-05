#include "sll.h"

uint g_slist_length(Node * list)
	_(requires _dryad_sll(list))
	_(requires _dryad_llen(list) < UINT_MAX)
	_(ensures  _dryad_sll(list))
	_(ensures \result == _dryad_llen(list))
{
	_(assume mutable_list(list))
	uint length;

	length = 0;
  _(ghost Node * old_list = \old(list) ;)
	while(list != NULL)
		_(invariant _dryad_sll(list))
		_(invariant _dryad_sll(old_list))
		_(invariant \lsegStar(old_list, list))
		_(invariant _dryad_llen(old_list) - _dryad_llen(list) == (\natural) length) 
		_(invariant length < UINT_MAX) 
		_(invariant mutable_list(list))
	{
		_(assume unfoldMutable(list))
		length++; 
		list = list->next;
		_(ghost LemmaSkip(\old(list), list))
	}
	return length;
}

