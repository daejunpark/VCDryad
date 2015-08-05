#include "sll.h"

Node * find_last_sorted(Node * l)
	_(requires _dryad_srtl(l))
	_(ensures _dryad_srtl(l))
	_(ensures \srtlsegStar(l, \result)) 
	_(ensures  _dryad_srtl(\result))
	_(ensures \result == NULL || \result->next == NULL)
	_(ensures \subset(_dryad_N(\result), _dryad_N(l)))
	_(ensures \subset(_dryad_lsegN(l, \result), _dryad_N(l))) 
	_(ensures \intset_ge(\result->key, _dryad_keys(l)))
	_(ensures _dryad_N(l) == \old(_dryad_N(l)))
	_(ensures _dryad_keys(l) == \old(_dryad_keys(l)))
	_(ensures l != NULL ==> \result != NULL)
	_(ensures l != NULL ==> _dryad_N(\result) == {\result})
	_(ensures l != NULL ==> \intset_in(\result->key, _dryad_keys(l)))
	_(ensures l != NULL ==> _dryad_keys(\result) == \intset_singleton(\result->key))
;

Node * concat_sorted(Node * l1, Node * l2)
	_(requires _dryad_srtl(l1) && _dryad_srtl(l2) && \disjoint(_dryad_N(l1), _dryad_N(l2)))
	_(requires l2 != NULL ==> \intset_ge(l2->key, _dryad_keys(l1)))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_N(\result) == (\old(_dryad_N(l1)) \union \old(_dryad_N(l2))))
	_(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(l1)), \old(_dryad_keys(l2))))
{

	if (l2 != NULL) {
		if (l1 != NULL) {

			Node * last = find_last_sorted(l1);
			_(assume mutable_list(last))
			last->next = l2;
			_(ghost LemmaSkipSort(l1, last) ;)
		} else {
			l1 = l2;
		}
	} 
	return l1;
}

