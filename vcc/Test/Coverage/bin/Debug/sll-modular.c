#include <vcc.h>
#include <stdlib.h>

typedef 
struct node {
	int key;
	struct node * next;
} Node;

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
	_(ensures _dryad_unfoldMinKey(o))
;)

_(logic \bool _dryad_maintainsAcross(struct node * x, struct node * y, \state enter, \state exit) =
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_N(y)) == \at(exit, _dryad_N(y))) &&
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_sll(y)) == \at(exit, _dryad_sll(y))) &&
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_getKey(y)) == \at(exit, _dryad_getKey(y)))
)

_(logic \bool _dryad_disjointMaintainsAcross(struct node * x, struct node * y, \state enter, \state exit) =
	(\disjoint(\at(enter, _dryad_N(x)), \at(enter, _dryad_N(y))) ==> 
						 \at(enter, _dryad_N(x)) == \at(exit, _dryad_N(x))) &&
	(\disjoint(\at(enter, _dryad_N(x)), \at(enter, _dryad_N(y))) ==>
						 \at(enter, _dryad_sll(x)) == \at(enter, _dryad_sll(x))) &&
	(\disjoint(\at(enter, _dryad_N(x)), \at(enter, _dryad_N(y))) ==>
						 \at(enter, _dryad_getKey(x)) == \at(exit, _dryad_getKey(x)))
)

Node * node_init(int k)
{
	// leaf is a location
	Node * leaf = (Node *) malloc(sizeof(Node));
	_(assume leaf != NULL)
	// leaf is a dereferenced location
	// key is field [to be represented as mapping from locations to ints]
	leaf->key = k;
	// next is a field [to be represented as mapping from locations to locations]
	leaf->next = NULL;
	return leaf;
}

Node * node_prepend(Node * old_root, int k)
{
	Node * new_root = (Node *) malloc(sizeof(Node));
	_(assume new_root != NULL)
	new_root->key = k;
	new_root->next = old_root;
	return new_root;
}

Node * node_insert(Node * x, int k)
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	if (x == NULL) {
		return node_init(k);
	} else if (k > x->key) {
		Node * tmp = node_insert(x->next, k);
		x->next = tmp;
		return x;
	}	else {	
		return node_prepend(x, k);
	}

}


