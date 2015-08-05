#include "dryad_srtl.h"

_(dryad)
int sorted_find(SNnode * l, int k)
	_(requires srtl(l))
	_(ensures  srtl(l) == \old(srtl(l)))
  _(ensures  srtl_reach(l) == \old(srtl_reach(l)))
  _(ensures  sll_keys(l) == \old(sll_keys(l)))
	_(ensures  \intset_in(k, sll_keys(l)) <==> \result == 0)
	_(ensures !\intset_in(k, sll_keys(l)) <==> \result == -1)
{
	_(assume mutable_list(l))
	if (l == NULL) {
		return -1;
	} else if (l->key == k) {
		return 0;
	} else { // l != NULL && l->key != k
		int res = sorted_find(l->next, k);
		return res;
	}
}

