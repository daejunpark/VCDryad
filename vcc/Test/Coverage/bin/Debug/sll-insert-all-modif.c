#include <vcc.h>
#include <stdlib.h>
_(ghost typedef \bool \intset[int]);
_(logic \intset \intset_empty =    (\lambda int k; \false))
_(logic \intset \intest_universe = (\lambda int k; \true))
_(logic \intset \intset_singleton(int el) = (\lambda int k; el == k ? \true : \false))
_(logic \intset \intset_union(\intset is1, \intset is2) = (\lambda int k; is1[k] || is2[k]))
_(logic \intset \intset_union0(int el, \intset is) = (\lambda int k; el == k || is[k]))
_(logic \bool \intset_in(int el, \intset is) = is[el])
_(logic \bool \intset_disjoint(\intset is1, \intset is2) = (\forall int k; !is1[k] || !is2[k]))
_(logic \bool \intset_subset(\intset is1, \intset is2) = (\forall int k; is1[k] ==> is2[k]))
_(logic \intset \intset_intersect(\intset is1, \intset is2) = (\lambda int k; is1[k] && is2[k]))
_(logic \intset \intset_diff(\intset is1, \intset is2) = (\lambda int k; is1[k] && !is2[k]))

_(axiom \forall int k; !\intset_in(k, \intset_empty))


_(def int _dryad_getKey(struct node * x) {
	return x == NULL ? INT_MAX : x->key;
})

_(def int _dryad_getMinKey(int x, int y) {
	return y <= x ? y : x;
})

_(abstract \objset _dryad_N(struct node * root)
	_(reads \universe())
	_(ensures root != NULL ==> root \in \result)
	_(ensures root == NULL ==> \result == {})
;)

_(abstract \intset _dryad_keys(struct node * root)
	_(reads \universe())
	_(ensures (root != NULL ==> \intset_in(root->key, \result)))
	_(ensures (root == NULL ==> (\result == \intset_empty)))
	;)

_(abstract \bool _dryad_sll(struct node * root)
	_(reads \universe())
	_(ensures root == NULL ==> \result)
;)

_(pure \bool _dryad_unfoldN(struct node * root)
	_(reads \universe())
	_(ensures \result == (root != NULL ==>
			(_dryad_N(root) == (_dryad_N(root->next) \union {root}))
	))
;)

_(pure \bool _dryad_unfoldKeys(struct node * root)
	_(reads \universe())
	_(ensures \result == 
		(root != NULL ==> (_dryad_keys(root) == (\intset_union(_dryad_keys(root->next), 
							 \intset_singleton(root->key)))))
	 )
;)


_(pure \bool _dryad_unfoldSll(struct node * root)
	_(reads \universe())
	_(ensures \result == (root != NULL ==>
		(_dryad_sll(root) <==>
			(_dryad_sll(root->next) && (! (root \in _dryad_N(root->next)))) 
		&& _dryad_getKey(root) <= _dryad_getKey(root->next)
	)))
;)

_(pure \bool _dryad_unfoldMinKey(struct node * root)
	_(reads \universe())
	_(ensures \result == (root != NULL ==>
			_dryad_getKey(root) == _dryad_getMinKey(_dryad_getKey(root), _dryad_getKey(root->next))
		))
;)

_(abstract \bool _dryad_unfoldAll(\object o)
	_(reads \universe())
	_(ensures _dryad_unfoldN(o))
	_(ensures _dryad_unfoldSll(o))
	_(ensures _dryad_unfoldKeys(o))
	_(ensures _dryad_unfoldMinKey(o))
;)

_(logic \bool _dryad_maintainsAcross(struct node * x, struct node * y, \state enter, \state exit) =
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_N(y)) == \at(exit, _dryad_N(y))) &&
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_sll(y)) == \at(exit, _dryad_sll(y))) &&
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_keys(y)) == \at(exit, _dryad_keys(y))) &&
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_getKey(y)) == \at(exit, _dryad_getKey(y)))
)

_(logic \bool _dryad_disjointMaintainsAcross(struct node * x, struct node * y, \state enter, \state exit) =
	(\disjoint(\at(enter, _dryad_N(x)), \at(enter, _dryad_N(y))) ==> 
 		   \at(enter, _dryad_N(x)) == \at(exit, _dryad_N(x))) &&
	(\disjoint(\at(enter, _dryad_N(x)), \at(enter, _dryad_N(y))) ==>
		   \at(enter, _dryad_sll(x)) == \at(enter, _dryad_sll(x))) &&
	(\disjoint(\at(enter, _dryad_N(x)), \at(enter, _dryad_N(y))) ==>
		   \at(enter, _dryad_keys(x)) == \at(enter, _dryad_keys(x))) &&
	(\disjoint(\at(enter, _dryad_N(x)), \at(enter, _dryad_N(y))) ==>
		   \at(enter, _dryad_getKey(x)) == \at(exit, _dryad_getKey(x)))
)

typedef 
struct node {
	int key;
	struct node * next;
} Node;


Node * sll_insert(Node * x, int k)
	_(requires _dryad_sll(x))
	_(ensures  _dryad_sll(\result))
	_(ensures  _dryad_keys(\result) == \intset_union(\old(_dryad_keys(x)), \intset_singleton(k)))
	_(ensures  _dryad_getKey(\result) == _dryad_getMinKey(\old(_dryad_getKey(x)), k))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	if (x == NULL) {
		Node * leaf = (Node *) malloc(sizeof(Node));
		_(assume leaf != NULL)
		leaf->key = k;
		leaf->next = NULL;
		return leaf;
	} else if (k > x->key) {
		Node * tmp = sll_insert(x->next, k);
		x->next = tmp;
		return x;
	}	else {	
		Node * new_root = (Node *) malloc(sizeof(Node));
		_(assume new_root != NULL)

		new_root->key = k;
		new_root->next = x;
		return new_root;
	}
}


