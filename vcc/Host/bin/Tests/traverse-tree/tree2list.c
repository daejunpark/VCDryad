#include "dryad_bst2list.h"

_(logic \bool mutable_bst(BNode * x) = x != NULL ==> \mutable(x) && \writable(x))
_(logic \bool mutable_sortedl(LNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
LNode * tree2list_rec(BNode * t, LNode * l)
	_(requires bst(t))
	_(requires sortl(l))
	_(requires \oset_disjoint(bst_reach(t), sortl_reach(l)))
	_(requires \intset_lt(bst_keys(t), sortl_keys(l)))

	_(ensures sortl(\result))
	_(ensures sortl_keys(\result) == \intset_union(\old(bst_keys(t)), \old(sortl_keys(l))))
{
	_(assume \malloc_root(t))
	_(assume mutable_bst(t))
	_(assume mutable_sortedl(l))
	
	if (t == NULL) {
		return l;
	} else {

		LNode * lnode = (LNode *) malloc(sizeof(LNode));
		_(assume lnode != NULL)

		int tkey = t->key;

		lnode->key = tkey;
		lnode->next = NULL;
  
    BNode * tright = t->right;
		BNode * tleft = t->left;

		LNode * tmp_list1 = tree2list_rec(tright, l);

		lnode->next = tmp_list1;

		free(t);

		LNode * tmp_list2 = tree2list_rec(tleft, lnode);
		
		return tmp_list2;
	}
}


