#include "sll.h"

Node * g_slist_remove_all(Node * list, int data)
	_(requires _dryad_sll(list))
	_(ensures  _dryad_sll(\result))
	_(ensures !\intset_in(data, \old(_dryad_keys(list))) ==> (_dryad_keys(\result) == \old(_dryad_keys(list))))
	_(ensures !\intset_in(data, _dryad_keys(\result)))
	//_(ensures  \intset_in(data, \old(keys(list))) ==> (keys(\result) == \intset_diff(\old(keys(list)), \intset_singleton(data))))

{
	_(assume list != NULL ==> \mutable(list) && \writable(list) && \malloc_root(list))
	Node *tmp, *prev = NULL;
	tmp = list;

	while(tmp != NULL)
		_(invariant _dryad_sll(tmp) && _dryad_sll(prev) && _dryad_sll(list))
		_(invariant \lsegStar(list, tmp))
		_(invariant \lsegStar(list, prev))
		_(invariant !\intset_in(data, \old(_dryad_keys(list))) ==> (_dryad_keys(list) == \old(_dryad_keys(list))))
		_(invariant !\intset_in(data, _dryad_lsegk(list, tmp)))
		_(invariant \intset_in(data, \old(_dryad_keys(list))) ==> (\intset_in(data, _dryad_keys(list)) || !\intset_in(data, _dryad_keys(list)))) 

		_(invariant \intset_in(data, _dryad_keys(tmp)) <==> \intset_in(data, _dryad_keys(list)))
		_(invariant _dryad_keys(list) == \intset_union(_dryad_lsegk(list, tmp), _dryad_keys(tmp)))
		_(invariant prev != NULL ==> prev->next == tmp)
		_(invariant tmp  != NULL ==> \mutable(tmp) && \writable(tmp) && \malloc_root(tmp))
		_(invariant prev != NULL ==> \mutable(prev) && \writable(prev))
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

			tmp = tmp_next;

		} else {
			prev = tmp;
			tmp = prev->next;
		}
		
		_(assume tmp != NULL ==> \mutable(tmp) && \writable(tmp) && \malloc_root(tmp))
	}
	return list;
}

