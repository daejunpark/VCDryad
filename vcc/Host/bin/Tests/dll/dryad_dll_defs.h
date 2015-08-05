#ifndef DRYAD_DLL_DEFS_H
#define DRYAD_DLL_DEFS_H

#include <vcc.h>
// ------------------------
#include <stdlib.h>

typedef
_(dryad "dll:dll_R:keys")
struct d_node {
  int key;
  struct d_node * prev;
  struct d_node * next;
} DLNode;


_(abstract _(dryad "base:dll") \bool dll(struct d_node * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
	;)

_(abstract _(dryad "base:dll_R") \oset dll_reach(struct d_node * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
			&& ((hd == NULL) ==> (\result == \oset_empty())))
	;)

_(abstract _(dryad "base:keys") \intset dll_keys(struct d_node * hd) // [key]
	_(reads \universe())
	_(ensures (hd != NULL ==> \intset_in(hd->key, \result)))
	_(ensures (hd == NULL ==> (\result == \intset_empty())))
	;)

// ----------------------------------------------------------------------------------------------------------------------------
_(logic _(dryad "unfold:dll") \bool unfold_dll(struct d_node * hd) =
	(hd != NULL ==>
		(dll(hd) <==> 
			(dll(hd->next) && 
			(hd->next != NULL ==> hd->next->prev == hd) &&
			(! \oset_in(hd, dll_reach(hd->next))) ) ) ) 
	;)

_(logic _(dryad "unfold:dll_R")  \bool unfold_dll_reach(struct d_node * hd) =
	(hd != NULL ==>	(dll_reach(hd) == \oset_union(dll_reach(hd->next), \oset_singleton(hd))) ) ;)


_(logic _(dryad "unfold:keys") \bool unfold_dll_keys(struct d_node * hd) =
		(hd != NULL ==> (dll_keys(hd) == (\intset_union(dll_keys(hd->next), \intset_singleton(hd->key))))) 
	;)

_(logic \bool unfold_dll_all(struct d_node * x) =
   unfold_dll(x)
   && unfold_dll_reach(x)
	 && unfold_dll_keys(x)
;)

// ----------------------------------------------------------------------------------------------------------------------------

_(logic _(dryad "same:dll") \bool same_dll(struct d_node * x, \state enter, \state exit) =
	\at(enter, dll(x)) == \at(exit, dll(x))
;)
_(logic _(dryad "same:dll_R") \bool same_dll_reach(struct d_node * x, \state enter, \state exit) = 
	\at(enter, dll_reach(x)) == \at(exit, dll_reach(x)) 
;)
_(logic _(dryad "same:keys") \bool same_dll_keys(struct d_node * x, \state enter, \state exit) =
	\at(enter, dll_keys(x)) == \at(exit, dll_keys(x))
;)
_(logic \bool same_dll_all(struct d_node * x, \state enter, \state exit) = 
	same_dll(x, enter, exit) 
	&& same_dll_reach(x, enter, exit)
	&& same_dll_keys(x, enter, exit)
;)
// ------------------------------------------------------------------------------------------------------

_(logic _(dryad "cond:dll") \bool cond_same_dll(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dll_reach(y)))) ==> \at(enter, dll(y)) == \at(exit, dll(y))
;)
_(logic _(dryad "cond:dll_R") \bool cond_same_dll_reach(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dll_reach(y)))) ==> \at(enter, dll_reach(y)) == \at(exit, dll_reach(y))
;)
_(logic _(dryad "cond:keys") \bool cond_same_dll_keys(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dll_reach(y)))) ==> \at(enter, dll_keys(y)) == \at(exit, dll_keys(y))
;)
_(logic \bool cond_same_dll_all(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	cond_same_dll(x, y, enter, exit) 
	&& cond_same_dll_reach(x, y, enter, exit)
	&& cond_same_dll_keys(x, y, enter, exit)
;)
// ------------------------------------------------------------------------------------------------------

_(logic _(dryad "disj:dll") \bool disj_same_dll(\oset heaplet, struct d_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, dll_reach(y)))) ==> \at(enter, dll(y)) == \at(exit, dll(y))
;)
_(logic _(dryad "disj:dll_R") \bool disj_same_dll_reach(\oset heaplet, struct d_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, dll_reach(y)))) ==> \at(enter, dll_reach(y)) == \at(exit, dll_reach(y))
;)
_(logic _(dryad "disj:keys") \bool disj_same_dll_keys(\oset heaplet, struct d_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, dll_reach(y)))) ==> \at(enter, dll_keys(y)) == \at(exit, dll_keys(y))
;)
_(logic \bool disj_same_dll_all(\oset heaplet, struct d_node * y, \state enter, \state exit) =
	disj_same_dll(\at(enter, heaplet), y, enter, exit) 
	&& disj_same_dll_reach(\at(enter, heaplet), y, enter, exit)
	&& disj_same_dll_keys(\at(enter, heaplet), y, enter, exit)
;)


// dummy function denoting the end of dl_node defs
_(abstract _(dryad "end") void end_dl_node_defs(struct d_node * x) ;)
// ---------------------------------------------------------------------------------------------------------

#endif
