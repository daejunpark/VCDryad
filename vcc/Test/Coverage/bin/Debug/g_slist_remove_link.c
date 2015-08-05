#include "sll.h"

Node * g_slist_remove_link(Node * list, Node * link)
	_(requires _dryad_sll(list))
	_(requires _dryad_sll(link) && \malloc_root(link)) 
	_(ensures _dryad_sll(\result)) 
	_(ensures _dryad_sll(link) && \malloc_root(link)) 
	_(ensures !(link \in \old(_dryad_N(list))) ==> \old(_dryad_N(list)) == _dryad_N(\result)) 
	_(ensures   link \in \old(_dryad_N(list)) ==> (_dryad_N(\result) == (\old(_dryad_N(list)) \diff {link}))) 
{
	_(assume mutable_list(list))
	Node * tmp;
	Node * prev;

	prev = NULL;
	tmp = list;

	while(tmp != NULL)
		_(invariant _dryad_sll(prev))
		_(invariant _dryad_sll(tmp))
		_(invariant _dryad_sll(list))
		_(invariant \lsegStar(list, prev)) 
		_(invariant \lsegStar(list, tmp))
		_(invariant _dryad_N(list) == _dryad_lsegN(list, prev) \union _dryad_N(prev))
		_(invariant _dryad_N(list) == _dryad_lsegN(list, tmp) \union _dryad_N(tmp))
		_(invariant _dryad_N(list) == \old(_dryad_N(list)))
		_(invariant \subset(_dryad_N(prev), _dryad_N(list)))
		_(invariant \subset(_dryad_N(tmp), _dryad_N(list))) 
		_(invariant !(link \in _dryad_lsegN(list, tmp))) 
		_(invariant prev == NULL ==> tmp == list)
		_(invariant prev != NULL ==> prev->next == tmp)
		_(invariant mutable_list(prev))
		_(invariant mutable_list(tmp))
		_(invariant \malloc_root(link))
	{
		if (tmp == link)
		{
			Node * tmp_next = tmp->next;

			if (prev != NULL) {

				prev->next = tmp_next;
				_(ghost LemmaSkip(list, prev))

			} else {
				list = tmp_next;
			}

			tmp->next = NULL;
			break;	
		}
		prev = tmp;
		tmp = tmp->next;
		_(assume mutable_list(tmp))
	}
	return list;
}

