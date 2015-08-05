#include "sll.h"

Node * g_slist_sort_merge(Node * l1, Node * l2)
	_(requires \srtlStar(l1, l2))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(l1)), \old(_dryad_keys(l2))))
	_(ensures _dryad_keys(\result) == \intset_union(_dryad_keys(l1), _dryad_keys(l2)))
	_(ensures _dryad_N(\result) == (\old(_dryad_N(l1)) \union \old(_dryad_N(l2))))
	;

Node * g_slist_sort_real(Node * list)
	_(requires _dryad_sll(list))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_keys(\result) == \old(_dryad_keys(list)))
{
  _(ghost \objset INIT_REACH = _dryad_N(list) ;)
	Node * l1, * l2;
	_(assume mutable_list(list))

	if (list == NULL) {
		return list;
	}
	if (list->next == NULL) {
		return list;
	}
	l1 = list;
  // TODO: see also SillyLemma
  _(assert \lsegStar(list, l1))
	l2 = list->next;

	_(assume unfoldMutable(list))
	_(assume unfoldMutable(l2))
	l2 = l2->next;

	while(l2 != NULL)
		_(invariant \old(_dryad_keys(list)) == \intset_union(_dryad_lsegk(list, l1), \intset_union(_dryad_lsegk(l1, l2), _dryad_keys(l2))))
		_(invariant _dryad_sll(l1))
		_(invariant _dryad_sll(l2))
		_(invariant \lsegStar(list, l1))
		_(invariant \lsegStar(list, l2))
    _(invariant \lsegStar(l1, l2))
		_(invariant l1 != NULL)
		_(invariant INIT_REACH == (_dryad_lsegN(list, l1) \union _dryad_lsegN(l1, l2) \union _dryad_N(l2)))
		_(invariant mutable_list(l2))
		_(invariant mutable_list(l1))
	{
		_(assume unfoldMutable(l2))
		l2 = l2->next;
		if(l2 == NULL) {
			break;
		}
		_(assume unfoldMutable(l1))
		l1 = l1->next;

		_(assume unfoldMutable(l2))
		l2 = l2->next;
		_(ghost LemmaSkip(list, l1) ;)
		_(ghost LemmaSkip(l1, l2) ;)
		_(ghost LemmaSkip(list, l2) ;)
	}
	_(assume unfoldMutable(l1))
	l2 = l1->next;
	l1->next = NULL;

	Node * t1 = g_slist_sort_real(list);

	if (l2 == NULL) {
		return t1;
	}

	Node * t2 = g_slist_sort_real(l2);

	return g_slist_sort_merge(t1, t2);

	//return res;
}
