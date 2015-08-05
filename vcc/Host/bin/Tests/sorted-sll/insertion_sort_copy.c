#include "dryad_srtl.h"

SNnode * insert_sorted(SNnode *x, int k)
	_(requires srtl(x))
	_(ensures srtl(\result))
	_(ensures sll(\result))
	_(ensures sll_keys(\result) == \intset_union(\old(sll_keys(x)), \intset_singleton(k)))
;

_(dryad)
SNnode * insertion_sort_copy(SNnode * l)
	_(requires sll(l))
	_(ensures srtl(\result))
	_(ensures sll(\result))
	_(ensures sll_keys(\result) == \old(sll_keys(l)))
{
	_(assume mutable_list(l))
	if (l == NULL) {
		return l;
	} else {
		SNnode * tl = insertion_sort_copy(l->next);

		SNnode * nl = insert_sorted(tl, l->key);
		return nl;
	}
}

