#include "sll.h"

int sorted_find(Node * l, int k)
	_(requires _dryad_srtl(l))
	_(ensures  \unchangedSrtl(l))
	_(ensures  \intset_in(k, _dryad_keys(l)) <==> \result == 0)
	_(ensures !\intset_in(k, _dryad_keys(l)) <==> \result == -1)
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

