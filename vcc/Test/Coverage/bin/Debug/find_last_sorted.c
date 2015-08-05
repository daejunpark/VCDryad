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

{
	_(assume mutable_list(l))
	if (l != NULL) {

    _(ghost Node * old_l = \old(l))
	  while (l->next != NULL)
			_(invariant _dryad_srtl(l))
			_(invariant _dryad_srtl(old_l))
			_(invariant \subset(_dryad_N(l), _dryad_N(old_l)))
			_(invariant \subset(_dryad_lsegN(old_l, l), _dryad_N(old_l)))
			_(invariant \srtlsegStar(old_l, l))
			_(invariant \intset_ge(l->key, _dryad_lsegk(\old(l), l)))
			_(invariant \intset_in(l->key, _dryad_keys(l)))
			_(invariant l != NULL && mutable_list(l))
			_(invariant _dryad_keys(l) == \intset_union(\intset_singleton(l->key), _dryad_keys(l->next)))
		{ 
			_(assume unfoldMutable(l))
			l = l->next;
		}
	}
	return l;
}
