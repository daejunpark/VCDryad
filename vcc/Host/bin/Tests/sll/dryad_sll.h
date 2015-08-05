#ifndef DRYAD_SLL_DEFS_H
#define DRYAD_SLL_DEFS_H

#include <vcc.h>
#include <stdlib.h>

typedef
_(dryad "sll:sll_R:keys:keys_R")
struct s_node {
  int key;
  struct s_node * next;
} SNnode;


_(pure  _(dryad "base:sll") \bool sll(struct s_node * hd)
	_(reads \universe()) 
//  _(ensures hd == NULL ==> \result)
//  _(ensures hd != NULL ==> sll(hd->next) && !\oset_in(hd, sll_reach(hd->next)))
;)

_(pure _(dryad "base:sll_R") \oset sll_reach(struct s_node * hd)
	_(reads \universe()) 
;)

_(abstract _(dryad "base:keys") \intset sll_keys(struct s_node * hd)
	_(reads \universe()) 
//  _(ensures hd == NULL ==> \result == \intset_empty())
  ;)

_(pure _(dryad "base:keys_R") \oset sll_keys_reach(struct s_node * hd)
	_(reads \universe()) 
  ;)

// ----------------------------------------------------------------------------------------------------------------------------
_(logic _(dryad "unfold:sll") \bool unfold_sll(struct s_node * hd) = 
  (hd == NULL ==> sll(hd)) 
  &&
	(hd != NULL ==>
		(sll(hd) <==> 
			(sll(hd->next) && 
			(! \oset_in(hd, sll_reach(hd->next))) ) ) ) 
	;)
_(logic _(dryad "unfold:sll_R")  \bool unfold_sll_reach(struct s_node * hd) = 
	((hd == NULL) ==> (sll_reach(hd) == \oset_empty()))
  &&
	(hd != NULL ==>
		  (sll_reach(hd) == \oset_union(sll_reach(hd->next), \oset_singleton(hd))) ) 
	;)

_(logic _(dryad "unfold:keys") \bool unfold_keys(struct s_node * hd) = // depends on: [next, key]
	  (hd == NULL ==> (sll_keys(hd) == \intset_empty()))
    &&
		(hd != NULL ==> (sll_keys(hd) == (\intset_union(sll_keys(hd->next), \intset_singleton(hd->key)))))
	;)

_(logic _(dryad "unfold:keys_R")  \bool unfold_keys_reach(struct s_node * hd) = 
	((hd == NULL) ==> (sll_keys_reach(hd) == \oset_empty()))
  &&
	(hd != NULL ==>
		  (sll_keys_reach(hd) == \oset_union(sll_keys_reach(hd->next), \oset_singleton(hd))) ) 
	;)

_(logic \bool unfold_sll_all_un(struct s_node * x) = 
	unfold_sll(x)
	&& unfold_sll_reach(x)
	&& unfold_keys(x)
	;)

// -----------------------------------------------------------------------------------------------------
_(logic _(dryad "same:sll") \bool same_sll(struct s_node * x, \state enter, \state exit) =
	\at(enter, sll(x)) == \at(exit, sll(x))
;)
_(logic _(dryad "same:sll_R") \bool same_sll_reach(struct s_node * x, \state enter, \state exit) = 
	(\at(enter, sll_reach(x)) == \at(exit, sll_reach(x)))
;)
_(logic _(dryad "same:keys") \bool same_sll_keys(struct s_node * x, \state enter, \state exit) =
	(\at(enter, sll_keys(x)) == \at(exit, sll_keys(x)))
;)
_(logic _(dryad "same:keys_R") \bool same_sll_keys_reach(struct s_node * x, \state enter, \state exit) =
	(\at(enter, sll_keys_reach(x)) == \at(exit, sll_keys_reach(x)))
;)
_(logic \bool same_sll_all_un(struct s_node * x, \state enter, \state exit) = 
	same_sll(x, enter, exit) 
	&& same_sll_reach(x, enter, exit)
	&& same_sll_keys(x, enter, exit)
;)


// ------------------------------------------------------------------------------------------------------

_(logic _(dryad "cond:sll") 
  \bool cond_same_sll(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, sll_reach(y)))) ==> \at(enter, sll(y)) == \at(exit, sll(y)) ;)

_(logic _(dryad "cond:sll_R") 
  \bool cond_same_sll_reach(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, sll_reach(y)))) ==> (\at(enter, sll_reach(y)) == \at(exit, sll_reach(y))) ;)

_(logic _(dryad "cond:keys") 
  \bool cond_same_sll_keys(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, sll_reach(y)))) ==> (\at(enter, sll_keys(y)) == \at(exit, sll_keys(y))) ;)

_(logic _(dryad "cond:keys_R") 
  \bool cond_same_sll_keys_reach(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, sll_keys_reach(y)))) ==> (\at(enter, sll_keys_reach(y)) == \at(exit, sll_keys_reach(y))) ;)

_(logic 
  \bool cond_same_sll_all_un(struct s_node * x, struct s_node * y, \state enter, \state exit) =
  	cond_same_sll(x, y, enter, exit) 
  	&& cond_same_sll_reach(x, y, enter, exit)
  	&& cond_same_sll_keys(x, y, enter, exit) 
;)
// --------------------------------------------------------------------------------------------------------
_(logic _(dryad "disj:sll")
  \bool disj_same_sll(\oset heaplet, struct s_node * y, \state enter, \state exit) =
    \oset_disjoint(\at(enter, heaplet), \at(enter, sll_reach(y))) ==> \at(enter, sll(y)) == \at(exit, sll(y)) ;)
_(logic _(dryad "disj:sll_R")
  \bool disj_same_sll_reach(\oset heaplet, struct s_node * y, \state enter, \state exit) =
    \oset_disjoint(\at(enter, heaplet), \at(enter, sll_reach(y))) ==> \at(enter, sll_reach(y)) == \at(exit, sll_reach(y)) ;)
_(logic _(dryad "disj:keys")
  \bool disj_same_sll_keys(\oset heaplet, struct s_node * y, \state enter, \state exit) =
    \oset_disjoint(\at(enter, heaplet), \at(enter, sll_reach(y))) ==> \at(enter, sll_keys(y)) == \at(exit, sll_keys(y)) ;)
_(logic _(dryad "disj:keys_R")
  \bool disj_same_sll_keys_reach(\oset heaplet, struct s_node * y, \state enter, \state exit) =
    \oset_disjoint(\at(enter, heaplet), \at(enter, sll_keys_reach(y))) ==> \at(enter, sll_keys_reach(y)) == \at(exit, sll_keys_reach(y)) ;)

// dummy function denoting the end of sll s_node defs
_(abstract _(dryad "end") void end_dl_s_node_defs(struct s_node * x) ;)
// ---------------------------------------------------------------------------------------------------------
#endif
