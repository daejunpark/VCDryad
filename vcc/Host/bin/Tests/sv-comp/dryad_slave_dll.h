#ifndef DRYAD_SLAVE_DLL_DEFS_H
#define DRYAD_SLAVE_DLL_DEFS_H

#include <vcc.h>
// ------------------------
#include <stdlib.h>

typedef
_(dryad "slave_dll:slave_dll_R")
struct slave_item {
  struct slave_item * prev;
  struct slave_item * next;
};


_(abstract _(dryad "base:slave_dll") \bool slave_dll(struct slave_item * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
	;)

_(abstract _(dryad "base:slave_dll_R") \oset slave_dll_reach(struct slave_item * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
			&& ((hd == NULL) ==> (\result == \oset_empty())))
	;)

// ----------------------------------------------------------------------------------------------------------------------------
_(logic _(dryad "unfold:slave_dll") \bool unfold_slave_dll(struct slave_item * hd) =
	(hd != NULL ==>
		(slave_dll(hd) <==> 
			(slave_dll(hd->next) && 
			(hd->next != NULL ==> hd->next->prev == hd) &&
			(! \oset_in(hd, slave_dll_reach(hd->next))) ) ) ) 
	;)

_(logic _(dryad "unfold:slave_dll_R")  \bool unfold_slave_dll_reach(struct slave_item * hd) =
	(hd != NULL ==>	(slave_dll_reach(hd) == \oset_union(slave_dll_reach(hd->next), \oset_singleton(hd))) ) ;)


_(logic \bool unfold_slave_dll_all(struct slave_item * x) =
   unfold_slave_dll(x)
   && unfold_slave_dll_reach(x)
;)

// ----------------------------------------------------------------------------------------------------------------------------

_(logic _(dryad "same:slave_dll") \bool same_slave_dll(struct slave_item * x, \state enter, \state exit) =
	\at(enter, slave_dll(x)) == \at(exit, slave_dll(x))
;)
_(logic _(dryad "same:slave_dll_R") \bool same_slave_dll_reach(struct slave_item * x, \state enter, \state exit) = 
	\at(enter, slave_dll_reach(x)) == \at(exit, slave_dll_reach(x)) 
;)
_(logic \bool same_slave_dll_all(struct slave_item * x, \state enter, \state exit) = 
	same_slave_dll(x, enter, exit) 
	&& same_slave_dll_reach(x, enter, exit)
;)
// ------------------------------------------------------------------------------------------------------

_(logic _(dryad "cond:slave_dll") \bool cond_same_slave_dll(struct slave_item * x, struct slave_item * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, slave_dll_reach(y)))) ==> \at(enter, slave_dll(y)) == \at(exit, slave_dll(y))
;)
_(logic _(dryad "cond:slave_dll_R") \bool cond_same_slave_dll_reach(struct slave_item * x, struct slave_item * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, slave_dll_reach(y)))) ==> \at(enter, slave_dll_reach(y)) == \at(exit, slave_dll_reach(y))
;)
_(logic \bool cond_same_slave_dll_all(struct slave_item * x, struct slave_item * y, \state enter, \state exit) =
	cond_same_slave_dll(x, y, enter, exit) 
	&& cond_same_slave_dll_reach(x, y, enter, exit)
;)

// ------------------------------------------------------------------------------------------------------
_(logic _(dryad "disj:slave_dll") \bool disj_same_slave_dll(\oset heaplet, struct slave_item * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, slave_dll_reach(y)))) ==> \at(enter, slave_dll(y)) == \at(exit, slave_dll(y))
;)
_(logic _(dryad "disj:slave_dll_R") \bool disj_same_slave_dll_reach(\oset heaplet, struct slave_item * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, slave_dll_reach(y)))) ==> \at(enter, slave_dll_reach(y)) == \at(exit, slave_dll_reach(y))
;)
_(logic \bool disj_same_slave_dll_all(\oset heaplet, struct slave_item * y, \state enter, \state exit) =
	disj_same_slave_dll(\at(enter, heaplet), y, enter, exit) 
	&& disj_same_slave_dll_reach(\at(enter, heaplet), y, enter, exit)
;)


// dummy function denoting the end of dl_node defs
_(abstract _(dryad "end") void end_slave_dl_node_defs(struct slave_item * x) ;)
// ---------------------------------------------------------------------------------------------------------

#endif
