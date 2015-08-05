#include "dryad_srtl.h"

SNnode * find_last_sorted(SNnode * l)
	_(requires srtl(l))
	_(ensures srtl(l))
	_(ensures srtl_lseg(l, \result) && \oset_disjoint(srtl_lseg_reach(l, \result), srtl_reach(\result))) //	_(ensures \srtlsegStar(l, \result)) 
  _(ensures srtl_reach(l) == \oset_union(srtl_lseg_reach(l, \result), \oset_singleton(\result)))
	_(ensures  srtl(\result))
	_(ensures \result == NULL || \result->next == NULL)
	_(ensures \oset_subset(srtl_reach(\result), srtl_reach(l)))
	_(ensures \oset_subset(srtl_lseg_reach(l, \result), srtl_reach(l))) 
	_(ensures \intset_le_one2(sll_keys(l), \result->key))
	_(ensures srtl_reach(l) == \old(srtl_reach(l)))
	_(ensures sll_keys(l) == \old(sll_keys(l)))
	_(ensures l != NULL ==> \result != NULL)
	_(ensures l != NULL ==> srtl_reach(\result) == \oset_singleton(\result))
	_(ensures l != NULL ==> \intset_in(\result->key, sll_keys(l)))
	_(ensures l != NULL ==> sll_keys(\result) == \intset_singleton(\result->key))
;

_(dryad)
SNnode * concat_sorted(SNnode * l1, SNnode * l2)
	_(requires srtl(l1) && srtl(l2) && \oset_disjoint(sll_reach(l1), sll_reach(l2)))
	_(requires l2 != NULL ==> \intset_le_one2(sll_keys(l1), l2->key))
	_(ensures srtl(\result))
	_(ensures sll_keys(\result) == \intset_union(\old(sll_keys(l1)), \old(sll_keys(l2))))
{

	if (l2 != NULL) {
		if (l1 != NULL) {

			SNnode * last = find_last_sorted(l1);
			_(assume mutable_list(last))
			last->next = l2;
		} else {
			l1 = l2;
		}
	} 
	return l1;
}

