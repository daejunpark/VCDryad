#ifndef DRYAD_AVL_DEFS_H
#define DRYAD_AVL_DEFS_H

#include <vcc.h>
#include <stdlib.h>

typedef 
_(dryad "avl:avl_R:avl_keys:avl_height")
struct a_node {
	struct a_node * left;
	struct a_node * right;
	int key;
	int height;
} AVLNode;

// -------------------------- base ------------------------------------------
_(abstract _(dryad "base:avl") \bool avl(struct a_node * root)
	_(reads \universe())
	_(ensures (root == NULL) ==> \result)
;)
_(abstract _(dryad "base:avl_R") \oset avl_reach(struct a_node * root)
	_(reads \universe())
	_(ensures (root != NULL) ==> \oset_in(root, \result))
	_(ensures (root == NULL) ==> (\result == \oset_empty()))
;)
_(abstract _(dryad "base:avl_keys") \intset avl_keys(struct a_node * root)
	_(reads \universe())
	_(ensures root != NULL ==> \intset_in(root->key, \result))
	_(ensures root == NULL ==> (\result == \intset_empty()))
;)

_(abstract _(dryad "base:avl_height") \integer avl_height(struct a_node * root)
	_(reads \universe())
	_(ensures root == NULL ==> \result == -1)
	_(ensures root != NULL ==> (\result >= 0))
;)

// ---------------------------- unfold --------------------------------------
_(logic _(dryad "unfold:avl") \bool unfold_avl(struct a_node * root) =
  (root != NULL ==>
		(avl(root) <==>
			(avl(root->left) && avl(root->right) 
			&& (! \oset_in(root, \oset_union(avl_reach(root->left), avl_reach(root->right)))) 
			&& !\intset_in(root->key, \intset_union(avl_keys(root->left), avl_keys(root->right)))
			&& \oset_disjoint(avl_reach(root->left), avl_reach(root->right)) 
			&& \intset_disjoint(avl_keys(root->left), avl_keys(root->right))
			&& \intset_lt_one2(avl_keys(root->left), root->key) 
			&& \intset_lt_one1(root->key, avl_keys(root->right)) 
			&& ((avl_height(root->left) == avl_height(root->right) 
					&& ((\integer) root->height == (avl_height(root->left) + 1)))
			 || (avl_height(root->left) == avl_height(root->right) + 1
					&& ((\integer)root->height == (avl_height(root->left) + 1)))
			 || (avl_height(root->right) == avl_height(root->left) + 1
					&& ((\integer)root->height == (avl_height(root->right) + 1)) ) ) ) ) )
;)

_(logic  _(dryad "unfold:avl_R") \bool unfold_avl_reach(struct a_node * root) =
	(root != NULL ==>
		(avl_reach(root) == \oset_union_one1(root, \oset_union(avl_reach(root->left),
									                                     avl_reach(root->right)))))
;)
_(logic _(dryad "unfold:avl_keys") \bool unfold_avl_keys(struct a_node * root) =
  (root != NULL ==>
		(avl_keys(root) == \intset_union(\intset_singleton(root->key), 
										                 \intset_union(avl_keys(root->left), 
                      													  avl_keys(root->right))))
    ) 
;)
_(logic _(dryad "unfold:avl_height") \bool unfold_avl_height(struct a_node * root) =
   (root != NULL ==> 
		(avl_height(root) == ((avl_height(root->left) > avl_height(root->right)) ?
							   avl_height(root->left) + 1 : avl_height(root->right) + 1 ))
		)

;)
_(logic \bool unfold_avl_all(struct a_node * x) =
  unfold_avl(x)
	&& unfold_avl_reach(x)
	&& unfold_avl_keys(x)
	&& unfold_avl_height(x)
;)

// -------------------------------- same --------------------------------------------------
_(logic _(dryad "same:avl") \bool same_avl(struct a_node * x, \state enter, \state exit) =
	\at(enter, avl(x)) == \at(exit, avl(x))
;)
_(logic _(dryad "same:avl_R") \bool same_avl_reach(struct a_node * x, \state enter, \state exit) =
	\at(enter, avl_reach(x)) == \at(exit, avl_reach(x))
;)
_(logic _(dryad "same:avl_keys") \bool same_avl_keys(struct a_node * x, \state enter, \state exit) =
	\at(enter, avl_keys(x)) == \at(exit, avl_keys(x))
;)
_(logic _(dryad "same:avl_height") \bool same_avl_height(struct a_node * x, \state enter, \state exit) =
	\at(enter, avl_height(x)) == \at(exit, avl_height(x))
;)
_(logic \bool same_avl_all(struct a_node * x, \state enter, \state exit) =
	same_avl(x, enter, exit)
	&& same_avl_reach(x, enter, exit)
	&& same_avl_keys(x, enter, exit)
	&& same_avl_height(x, enter, exit)
;)

// ----------------------------  cond same  ------------------------------------------------
_(logic _(dryad "cond:avl") \bool cond_same_avl(struct a_node * x, struct a_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, avl_reach(y))) ==> \at(enter, avl(y)) == \at(exit, avl(y)))
;)
_(logic _(dryad "cond:avl_R") \bool cond_same_avl_reach(struct a_node * x, struct a_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, avl_reach(y))) ==> \at(enter, avl_reach(y)) == \at(exit, avl_reach(y)))
;)
_(logic _(dryad "cond:avl_keys") \bool cond_same_avl_keys(struct a_node * x, struct a_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, avl_reach(y))) ==> \at(enter, avl_keys(y)) == \at(exit, avl_keys(y)))
;)
_(logic _(dryad "cond:avl_height") \bool cond_same_avl_height(struct a_node * x, struct a_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, avl_reach(y))) ==> \at(enter, avl_height(y)) == \at(exit, avl_height(y)))
;)
_(logic \bool cond_same_avl_all(struct a_node * x, struct a_node * y, \state enter, \state exit) =
	cond_same_avl(x, y, enter, exit)
	&& cond_same_avl_reach(x, y, enter, exit)
	&& cond_same_avl_keys(x, y, enter, exit)
	&& cond_same_avl_height(x, y, enter, exit)
;)
// ----------------------------  disj same  ------------------------------------------------
_(logic _(dryad "disj:avl") \bool disj_same_avl(\oset heaplet, struct a_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, avl_reach(y))) ==> \at(enter, avl(y)) == \at(exit, avl(y)))
;)
_(logic _(dryad "disj:avl_R") \bool disj_same_avl_reach(\oset heaplet, struct a_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, avl_reach(y))) ==> \at(enter, avl_reach(y)) == \at(exit, avl_reach(y)))
;)
_(logic _(dryad "disj:avl_keys") \bool disj_same_avl_keys(\oset heaplet, struct a_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, avl_reach(y))) ==> \at(enter, avl_keys(y)) == \at(exit, avl_keys(y)))
;)
_(logic _(dryad "disj:avl_height") \bool disj_same_avl_height(\oset heaplet, struct a_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, avl_reach(y))) ==> \at(enter, avl_height(y)) == \at(exit, avl_height(y)))
;)
_(logic \bool disj_same_avl_all(\oset heaplet, struct a_node * y, \state enter, \state exit) =
	disj_same_avl(\at(enter, heaplet), y, enter, exit)
	&& disj_same_avl_reach(\at(enter, heaplet), y, enter, exit)
	&& disj_same_avl_keys(\at(enter, heaplet), y, enter, exit)
	&& disj_same_avl_height(\at(enter, heaplet), y, enter, exit)
;)


// -------------------------------- dummy abstract function --------------------------------
_(abstract _(dryad "end") void end_a_node_defs(struct a_node * x) ;)

#endif
