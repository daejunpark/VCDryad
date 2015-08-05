#include "sll.h"


Node * g_slist_remove (Node * list, int data)
	_(requires _dryad_sll(list))
	_(ensures  _dryad_sll(\result))
	// a bag (multiset) is needed to to prove the stronger property
	_(ensures !\intbag_in(data, \old(_dryad_keyb(list))) ==> (_dryad_keyb(\result) == \old(_dryad_keyb(list))))
	_(ensures  \intbag_in(data, \old(_dryad_keyb(list))) ==> (_dryad_keyb(\result) == \intbag_diff(\old(_dryad_keyb(list)), \intbag_singleton(data))))
{
	_(assume mutable_list(list))
	_(assume list != NULL ==> \malloc_root(list))

	Node *tmp;
  Node *prev = NULL;
	tmp = list;

	while(tmp != NULL)
		_(invariant _dryad_sll(tmp))
		_(invariant _dryad_sll(prev))
		_(invariant \lsegStar(list, tmp))  
		_(invariant \lsegStar(list, prev)) //
		_(invariant \subset(_dryad_N(tmp), _dryad_N(list)))
		_(invariant \subset(_dryad_N(prev), _dryad_N(list)))
		_(invariant prev == NULL ==> tmp == list)
		_(invariant prev != NULL ==> prev->next == tmp)
		_(invariant _dryad_N(list) == _dryad_lsegN(list, tmp) \union _dryad_N(tmp))
		_(invariant _dryad_keyb(list) == \old(_dryad_keyb(list)))
		_(invariant !\intbag_in(data, _dryad_lsegb(list, tmp)))
		_(invariant tmp  != NULL ==> \malloc_root(tmp))
		_(invariant mutable_list(tmp))
		_(invariant mutable_list(prev))
	{
		if (tmp->key == data)
		{
			Node * tmp_next = tmp->next;
			
			if (prev != NULL) {

				prev->next = tmp_next;
			} else {
				
				list = tmp_next;
			}
			free(tmp);
			break;
		}
		
		prev = tmp;
		tmp = prev->next;

		_(assume tmp != NULL ==> \malloc_root(tmp))
		_(assume tmp != NULL ==> \mutable(tmp) && \writable(tmp))
	}
	return list;
}

