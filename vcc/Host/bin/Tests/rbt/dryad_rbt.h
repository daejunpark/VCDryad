#ifndef DRYAD_RBT_DEFS_H
#define DRYAD_RBT_DEFS_H

#include <vcc.h>
#include <stdlib.h>

typedef 
_(dryad "rbt:rbt_R:rbt_keys:rbt_bh:rbt_black")
struct r_node {
	struct r_node * left;
	struct r_node * right;
	int key;
	int color;
} RBTNode;

// -------------------------- base ------------------------------------------
_(abstract _(dryad "base:rbt") \bool rbt(struct r_node * root)
	_(reads \universe())
	_(ensures (root == NULL) ==> \result)
;)
_(abstract _(dryad "base:rbt_R") \oset rbt_reach(struct r_node * root)
	_(reads \universe())
	_(ensures (root != NULL) ==> \oset_in(root, \result))
	_(ensures (root == NULL) ==> (\result == \oset_empty()))
;)
_(abstract _(dryad "base:rbt_keys") \intset rbt_keys(struct r_node * root)
	_(reads \universe())
	_(ensures root != NULL ==> \intset_in(root->key, \result))
	_(ensures root == NULL ==> (\result == \intset_empty()))
;)

_(abstract _(dryad "base:rbt_bh") \integer rbt_bh(struct r_node * root)
	_(reads \universe())
	_(ensures root == NULL ==> \result == 1)
	_(ensures root != NULL ==> (\result >= 1))
;)

_(abstract _(dryad "base:rbt_black") \bool rbt_black(struct r_node * root)
	_(reads \universe())
	_(ensures root == NULL ==> \result)
;)

// --------------------------- logic def ------------------------------------
//_(logic \bool rbt_black(struct r_node * x) = ((x == NULL) || (x->color == 0)))

// ---------------------------- unfold --------------------------------------
_(logic _(dryad "unfold:rbt") \bool unfold_rbt(struct r_node * root)  =
  (root != NULL ==>
		(rbt(root) <==>
			(rbt(root->left) && rbt(root->right) 
			&& (! \oset_in(root, \oset_union(rbt_reach(root->left), rbt_reach(root->right)))) 
			&& !\intset_in(root->key, \intset_union(rbt_keys(root->left), rbt_keys(root->right)))
			&& \oset_disjoint(rbt_reach(root->left), rbt_reach(root->right)) 
			&& \intset_disjoint(rbt_keys(root->left), rbt_keys(root->right))
			&& \intset_lt_one2(rbt_keys(root->left), root->key) 
			&& \intset_lt_one1(root->key, rbt_keys(root->right)) 
			&& (rbt_bh(root->left) == rbt_bh(root->right))
			&& ((root->color == 0) || (rbt_black(root->left) && rbt_black(root->right))) ) ) ) 
;)

_(logic _(dryad "unfold:rbt_R") \bool unfold_rbt_reach(struct r_node * root) =
	(root != NULL ==>
		(rbt_reach(root) == \oset_union(\oset_singleton(root),
                                    \oset_union(rbt_reach(root->left), rbt_reach(root->right)))))
;)
_(logic _(dryad "unfold:rbt_keys") \bool unfold_rbt_keys(struct r_node * root) =
	(root != NULL ==>
		(rbt_keys(root) == \intset_union(\intset_singleton(root->key), 
										 \intset_union(rbt_keys(root->left), 
													  rbt_keys(root->right)))) //)
    )
;)

_(logic _(dryad "unfold:rbt_bh") \bool unfold_rbt_bh(struct r_node * root) =
	(root != NULL ==>  (
			((rbt_bh(root->left) <  rbt_bh(root->right) && root->color == 0) 
			==> (rbt_bh(root) == (rbt_bh(root->right) + 1)) ) 
		&&	((rbt_bh(root->left) <  rbt_bh(root->right) && root->color != 0)
			==> (rbt_bh(root) == rbt_bh(root->right)))
		&&	((rbt_bh(root->left) >= rbt_bh(root->right) && root->color == 0)
			==> (rbt_bh(root) == (rbt_bh(root->left) + 1)))
		&&	((rbt_bh(root->left) >= rbt_bh(root->right) && root->color != 0)
			==> (rbt_bh(root) == rbt_bh(root->left))) ))
;)

_(logic _(dryad "unfold:rbt_black") \bool unfold_rbt_black(struct r_node * root) =
	(root != NULL ==> (rbt_black(root) <==> root->color == 0))
;)				

_(logic \bool unfold_rbt_all(struct r_node * x) =
	unfold_rbt(x)
	&& unfold_rbt_reach(x)
	&& unfold_rbt_keys(x)
	&& unfold_rbt_bh(x)
	&& unfold_rbt_black(x)
;)

// -------------------------------- same --------------------------------------------------
_(logic _(dryad "same:rbt") \bool same_rbt(struct r_node * x, \state enter, \state exit) =
	\at(enter, rbt(x)) == \at(exit, rbt(x))
;)
_(logic _(dryad "same:rbt_R") \bool same_rbt_reach(struct r_node * x, \state enter, \state exit) =
	\at(enter, rbt_reach(x)) == \at(exit, rbt_reach(x))
;)
_(logic _(dryad "same:rbt_keys") \bool same_rbt_keys(struct r_node * x, \state enter, \state exit) =
	\at(enter, rbt_keys(x)) == \at(exit, rbt_keys(x))
;)
_(logic _(dryad "same:rbt_bh") \bool same_rbt_bh(struct r_node * x, \state enter, \state exit) =
	\at(enter, rbt_bh(x)) == \at(exit, rbt_bh(x))
;)
_(logic _(dryad "same:rbt_black") \bool same_rbt_black(struct r_node * x, \state enter, \state exit) =
	\at(enter, rbt_black(x)) == \at(exit, rbt_black(x))
;)
_(logic \bool same_rbt_all(struct r_node * x, \state enter, \state exit) =
	same_rbt(x, enter, exit)
	&& same_rbt_reach(x, enter, exit)
	&& same_rbt_keys(x, enter, exit)
	&& same_rbt_bh(x, enter, exit)
	&& same_rbt_black(x, enter, exit)
;)

// ----------------------------  cond same  ------------------------------------------------
_(logic _(dryad "cond:rbt") \bool cond_same_rbt(struct r_node * x, struct r_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, rbt_reach(y))) ==> \at(enter, rbt(y)) == \at(exit, rbt(y)))
;)
_(logic _(dryad "cond:rbt_R") \bool cond_same_rbt_reach(struct r_node * x, struct r_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, rbt_reach(y))) ==> \at(enter, rbt_reach(y)) == \at(exit, rbt_reach(y)))
;)
_(logic _(dryad "cond:rbt_keys") \bool cond_same_rbt_keys(struct r_node * x, struct r_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, rbt_reach(y))) ==> \at(enter, rbt_keys(y)) == \at(exit, rbt_keys(y)))
;)
_(logic _(dryad "cond:rbt_bh") \bool cond_same_rbt_bh(struct r_node * x, struct r_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, rbt_reach(y))) ==> \at(enter, rbt_bh(y)) == \at(exit, rbt_bh(y)))
;)
_(logic _(dryad "cond:rbt_black") \bool cond_same_rbt_black(struct r_node * x, struct r_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, rbt_reach(y))) ==> \at(enter, rbt_black(y)) == \at(exit, rbt_black(y)))
;)

// ----------------------------  disj same  ------------------------------------------------
_(logic _(dryad "disj:rbt") \bool disj_same_rbt(\oset heaplet, struct r_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, rbt_reach(y))) ==> \at(enter, rbt(y)) == \at(exit, rbt(y)))
;)
_(logic _(dryad "disj:rbt_R") \bool disj_same_rbt_reach(\oset heaplet, struct r_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, rbt_reach(y))) ==> \at(enter, rbt_reach(y)) == \at(exit, rbt_reach(y)))
;)
_(logic _(dryad "disj:rbt_keys") \bool disj_same_rbt_keys(\oset heaplet, struct r_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, rbt_reach(y))) ==> \at(enter, rbt_keys(y)) == \at(exit, rbt_keys(y)))
;)
_(logic _(dryad "disj:rbt_bh") \bool disj_same_rbt_bh(\oset heaplet, struct r_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, rbt_reach(y))) ==> \at(enter, rbt_bh(y)) == \at(exit, rbt_bh(y)))
;)
_(logic _(dryad "disj:rbt_black") \bool disj_same_rbt_black(\oset heaplet, struct r_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, rbt_reach(y))) ==> \at(enter, rbt_black(y)) == \at(exit, rbt_black(y)))
;)
_(logic \bool disj_same_rbt_all(\oset heaplet, struct r_node * y, \state enter, \state exit) =
	disj_same_rbt(\at(enter, heaplet), y, enter, exit)
	&& disj_same_rbt_reach(\at(enter, heaplet), y, enter, exit)
	&& disj_same_rbt_keys(\at(enter, heaplet), y, enter, exit)
	&& disj_same_rbt_bh(\at(enter, heaplet), y, enter, exit)
	&& disj_same_rbt_black(\at(enter, heaplet), y, enter, exit)
;)

// -------------------------------- dummy abstract function --------------------------------
_(abstract _(dryad "end") void end_r_node_defs(struct r_node * x) ;)

#endif
