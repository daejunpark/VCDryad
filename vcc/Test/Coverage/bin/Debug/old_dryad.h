#ifndef DRYAD_LIST_DEFS_H
#define DRYAD_LIST_DEFS_H

#include <stdlib.h>
#include "intset_defs.h"

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
_(axiom \forall \objset os1, os2; \forall \object o; (os1 == (os2 \union {o})) ==> \subset(os2, os1))
#endif
