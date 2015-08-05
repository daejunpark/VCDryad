#include "sll.h"

Node * sll_copy(Node *x, int k)
	_(requires _dryad_sll(x))
  _(ensures _dryad_sll(x))
  _(ensures  _dryad_N(x) == \old(_dryad_N(x)))
	_(ensures  _dryad_sll(\result))
	_(ensures  \disjoint(_dryad_N(\result), _dryad_N(x)))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	if (x == NULL) {
		return x;
	} else {
		Node * tmp = sll_copy(x->next, k);
    _(assert _dryad_sll(x))
		Node * new_node = (Node *) malloc(sizeof(Node));
		_(assume new_node != NULL)
    _(assert _dryad_sll(x))
    _(assert _dryad_sll(tmp))
    int tmp_key = x->key;
		new_node->key = tmp_key;
		new_node->next = tmp;
		return new_node;
	}
}

