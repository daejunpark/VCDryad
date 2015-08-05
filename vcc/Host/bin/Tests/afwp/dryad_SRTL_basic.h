#ifndef DRYAD_SRTL_DEFS_H
#define DRYAD_SRTL_DEFS_H

#include <vcc.h>
// ------------------------
#include <stdlib.h>
//#include "intset_defs.h"
//#include "intbag_defs.h"

typedef
_(dryad "srtl:srtl_R:keys:slseg:slseg_R:lseg_keys")
struct s_node {
  int key;
  struct s_node * next;
} Node;


_(abstract _(dryad "base:srtl") \bool srtl(struct s_node * hd)
	_(reads \universe())
	//_(ensures (hd == NULL) ==> \result)
;)


_(abstract _(dryad "base:srtl_R") \oset srtl_reach(struct s_node * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
			&& ((hd == NULL) ==> (\result == \oset_empty())))
;)
_(abstract _(dryad "base:keys") \intset sll_keys(struct s_node * hd) // [key]
	_(reads \universe())
	_(ensures (hd != NULL ==> \intset_in(hd->key, \result)))
	_(ensures (hd == NULL ==> (\result == \intset_empty())))
	;)

_(abstract _(dryad "base:slseg") \bool srtl_lseg(struct s_node * hd, struct s_node * tl)
  _(reads \universe())
  _(ensures hd == NULL ==> \result)
  _(ensures hd == tl ==> \result)
  _(ensures tl == NULL ==> (\result == srtl(hd)))
  _(ensures (srtl(tl) && \oset_disjoint(srtl_reach(tl), srtl_lseg_reach(hd, tl))) ==>
             (srtl(hd) 
						  && (sll_keys(hd) == \intset_union(sll_keys(tl), sll_lseg_keys(hd, tl)))
//						  && _dryad_keyb(hd) == \intbag_union(_dryad_keyb(tl), _dryad_lsegb(hd, tl))
						 ) ) 
  _(ensures (tl != NULL && srtl(tl->next) 
         && \oset_disjoint(srtl_reach(tl->next), srtl_lseg_reach(hd, tl)) 
		     && (! \oset_in(tl, srtl_reach(tl->next)) ) 
		     && (! \oset_in(tl, srtl_lseg_reach(hd, tl)))   ) ==>
                   (  srtl_lseg (hd, tl->next) 
				   && (sll_lseg_keys(hd, tl->next) == \intset_union(\intset_singleton(tl->key), sll_lseg_keys(hd, tl)))
//				   && _dryad_lsegb(hd, tl->next) == \intbag_union(\intbag_singleton(tl->key), _dryad_lsegb(hd, tl))
				   && (srtl_lseg_reach(hd, tl->next) == \oset_union(\oset_singleton(tl), srtl_lseg_reach(hd, tl)))   ) )
  ;)

_(abstract _(dryad "base:slseg_R") \oset srtl_lseg_reach(struct s_node * hd, struct s_node * tl)
	_(reads \universe())
	_(ensures hd == NULL ==> (\result == \oset_empty()))
	_(ensures hd == tl ==>   (\result == \oset_empty()))
	_(ensures hd != tl ==> \oset_in(hd, \result))
	_(ensures tl == NULL ==> (\result == srtl_reach(hd)))
;)

_(abstract _(dryad "base:lseg_keys") \intset sll_lseg_keys(struct s_node * hd, struct s_node * tl)
  _(reads \universe())
  _(ensures hd != tl   ==> \intset_in(hd->key, \result))
  _(ensures hd == NULL ==> (\result == \intset_empty()))
  _(ensures hd == tl   ==> (\result == \intset_empty()))
  _(ensures tl == NULL ==> (\result == sll_keys(hd)))
;)

// ----------------------------------------------------------------------------------------------------------------------------
_(logic _(dryad "unfold:srtl") \bool unfold_srtl(struct s_node * hd) = {:split}
  (hd == NULL ==> srtl(hd))
	&& (hd != NULL ==>
		(srtl(hd) <==> 
			(srtl(hd->next) 
        && (! \oset_in(hd, srtl_reach(hd->next)))
        &&    \intset_lt_one1(hd->key, sll_keys(hd->next)) ) ) ) 
;)
_(logic _(dryad "unfold:srtl_R") \bool unfold_srtl_reach(struct s_node * hd) =
	(hd != NULL ==>
		(srtl_reach(hd) == \oset_union(srtl_reach(hd->next), \oset_singleton(hd))) ) 
;)

_(logic _(dryad "unfold:keys") \bool unfold_sll_keys(struct s_node * hd) =
		(hd != NULL ==> (sll_keys(hd) == (\intset_union(sll_keys(hd->next), \intset_singleton(hd->key)))))
;)

_(logic \bool unfold_srtl_all_un(struct s_node * x) =
  unfold_srtl(x)
	&& unfold_srtl_reach(x)
	&& unfold_sll_keys(x)
;)


_(logic _(dryad "unfold:slseg") \bool unfold_srtl_lseg(struct s_node * hd, struct s_node * tl) =
  ((hd != NULL && hd != tl) ==>
      (srtl_lseg(hd,tl) <==> 
        (srtl_lseg(hd->next,tl) 
        && (! \oset_in(hd, srtl_lseg_reach(hd->next,tl))) 
        && \intset_lt_one1(hd->key, sll_lseg_keys(hd->next, tl)) ) ) ) 
  ;)

_(logic _(dryad "unfold:slseg_R") \bool unfold_srtl_lseg_reach(struct s_node * hd, struct s_node * tl) =
  ((hd != NULL && hd != tl) ==> 
       ((srtl_lseg_reach(hd, tl) == \oset_union(srtl_lseg_reach(hd->next, tl), \oset_singleton(hd))) ) )
 ;)

_(logic _(dryad "unfold:lseg_keys") \bool unfold_sll_lseg_keys(struct s_node * hd, struct s_node * tl) =
      ((hd != NULL && hd != tl) ==> (sll_lseg_keys(hd, tl) ==
          \intset_union(sll_lseg_keys(hd->next, tl), \intset_singleton(hd->key)) ) )
;)

_(logic \bool unfold_srtl_all_bin(struct s_node * hd, struct s_node *  tl) =
  unfold_srtl_lseg(hd, tl)
  && unfold_srtl_lseg_reach(hd, tl)
  && unfold_sll_lseg_keys(hd, tl)
;)

// ----------------------------------------------------------------------------------------------------------------------------

// -----------------------------------------------------------------------------------------------------
_(logic _(dryad "same:srtl") \bool same_srtl(struct s_node * x, \state enter, \state exit) =
	\at(enter, srtl(x)) == \at(exit, srtl(x))
;)
_(logic _(dryad "same:srtl_R") \bool same_srtl_reach(struct s_node * x, \state enter, \state exit) = 
	(\at(enter, srtl_reach(x)) == \at(exit, srtl_reach(x)))
;)
_(logic _(dryad "same:keys") \bool same_sll_keys(struct s_node * x, \state enter, \state exit) =
	(\at(enter, sll_keys(x)) == \at(exit, sll_keys(x)))
;)
_(logic \bool same_srtl_all_un(struct s_node * x, \state enter, \state exit) = 
	same_srtl(x, enter, exit) 
	&& same_srtl_reach(x, enter, exit)
	&& same_sll_keys(x, enter, exit)
;)

_(logic _(dryad "same:slseg") 
  \bool same_srtl_lseg(struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
    \at(enter, srtl_lseg(hd, tl)) == \at(exit, srtl_lseg(hd, tl)) ;)

_(logic _(dryad "same:slseg_R") 
  \bool same_srtl_lseg_reach(struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
    (\at(enter, srtl_lseg_reach(hd, tl) == \at(exit, srtl_lseg_reach(hd, tl)))) ;)

_(logic _(dryad "same:lseg_keys")
  \bool same_sll_lseg_keys(struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
    (\at(enter, sll_lseg_keys(hd, tl)) == \at(exit, sll_lseg_keys(hd, tl))) ;)

_(logic \bool same_srtl_all_bin(struct s_node * hd, struct s_node * tl, \state enter, \state exit) = 
	same_srtl_lseg(hd, tl, enter, exit) 
	&& same_srtl_lseg_reach(hd, tl, enter, exit)
	&& same_sll_lseg_keys(hd, tl, enter, exit)
;)


// ------------------------------------------------------------------------------------------------------

_(logic _(dryad "cond:srtl") 
  \bool cond_same_srtl(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, srtl_reach(y)))) ==> \at(enter, srtl(y)) == \at(exit, srtl(y)) ;)

_(logic _(dryad "cond:srtl_R") 
  \bool cond_same_srtl_reach(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, srtl_reach(y)))) ==> (\at(enter, srtl_reach(y)) == \at(exit, srtl_reach(y))) ;)

_(logic _(dryad "cond:keys") 
  \bool cond_same_sll_keys(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, srtl_reach(y)))) ==> (\at(enter, sll_keys(y)) == \at(exit, sll_keys(y))) ;)
_(logic
  \bool cond_same_srtl_all_un(struct s_node * x, struct s_node * y, \state enter, \state exit) =
  	cond_same_srtl(x, y, enter, exit) 
  	&& cond_same_srtl_reach(x, y, enter, exit)
  	&& cond_same_sll_keys(x, y, enter, exit) 
;)

_(logic _(dryad "cond:slseg") 
  \bool cond_same_srtl_lseg(struct s_node * x, struct s_node * hd, struct s_node * tl, 
                      \state enter, \state exit) = 
    ((! \oset_in(x, \at(enter, srtl_lseg_reach(hd, tl)))) ==> 
      \at(enter, srtl_lseg(hd, tl)) == \at(exit, srtl_lseg(hd, tl)) ) ;)

_(logic _(dryad "cond:slseg_R") 
  \bool cond_same_srtl_lseg_reach(struct s_node * x, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) = 
    ((! \oset_in(x, \at(enter, srtl_lseg_reach(hd, tl)))) ==> 
        (\at(enter, srtl_lseg_reach(hd, tl)) == \at(exit, srtl_lseg_reach(hd, tl)) )) ;)

_(logic _(dryad "cond:lseg_keys")
  \bool cond_same_sll_lseg_keys(struct s_node * x, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) =
    ((! \oset_in(x, \at(enter, srtl_lseg_reach(hd, tl)))) ==>
      (\at(enter, sll_lseg_keys(hd, tl)) == \at(exit, sll_lseg_keys(hd, tl)))) ;)
_(logic 
  \bool cond_same_srtl_all_bin(struct s_node * x, struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
	  cond_same_srtl_lseg(x, hd, tl, enter, exit) 
  	&& cond_same_srtl_lseg_reach(x, hd, tl, enter, exit)
  	&& cond_same_sll_lseg_keys(x, hd, tl, enter, exit)
;)


// ------------------------------------------------------------------------------------------------------

_(logic _(dryad "disj:srtl") 
  \bool disj_same_srtl(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, srtl_reach(y)))) ==> \at(enter, srtl(y)) == \at(exit, srtl(y)) ;)

_(logic _(dryad "disj:srtl_R") 
  \bool disj_same_srtl_reach(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, srtl_reach(y)))) ==> (\at(enter, srtl_reach(y)) == \at(exit, srtl_reach(y))) ;)

_(logic _(dryad "disj:keys") 
  \bool disj_same_sll_keys(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, srtl_reach(y)))) ==> (\at(enter, sll_keys(y)) == \at(exit, sll_keys(y))) ;)
_(logic
  \bool disj_same_srtl_all_un(\oset heaplet, struct s_node * y, \state enter, \state exit) =
  	disj_same_srtl(\at(enter, heaplet), y, enter, exit) 
  	&& disj_same_srtl_reach(\at(enter, heaplet), y, enter, exit)
  	&& disj_same_sll_keys(\at(enter, heaplet), y, enter, exit) 
;)

_(logic _(dryad "disj:slseg") 
  \bool disj_same_srtl_lseg(\oset heaplet, struct s_node * hd, struct s_node * tl, 
                      \state enter, \state exit) = 
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, srtl_lseg_reach(hd, tl)))) ==> 
      \at(enter, srtl_lseg(hd, tl)) == \at(exit, srtl_lseg(hd, tl)) ) ;)

_(logic _(dryad "disj:slseg_R") 
  \bool disj_same_srtl_lseg_reach(\oset heaplet, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) = 
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, srtl_lseg_reach(hd, tl)))) ==> 
        (\at(enter, srtl_lseg_reach(hd, tl)) == \at(exit, srtl_lseg_reach(hd, tl)) )) ;)

_(logic _(dryad "disj:lseg_keys")
  \bool disj_same_sll_lseg_keys(\oset heaplet, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) =
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, srtl_lseg_reach(hd, tl)))) ==>
      (\at(enter, sll_lseg_keys(hd, tl)) == \at(exit, sll_lseg_keys(hd, tl)))) ;)
_(logic 
  \bool disj_same_srtl_all_bin(\oset heaplet, struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
	  disj_same_srtl_lseg(\at(enter, heaplet), hd, tl, enter, exit) 
  	&& disj_same_srtl_lseg_reach(\at(enter, heaplet), hd, tl, enter, exit)
  	&& disj_same_sll_lseg_keys(\at(enter, heaplet), hd, tl, enter, exit)
;)


// dummy function denoting the end of sll s_node defs
_(abstract _(dryad "end") void end_dl_s_node_defs(struct s_node * x) ;)


_(logic \bool unfold_mutable_list(struct s_node * x) =
  ((x != NULL && x->next != NULL)
  ==> (\mutable(x) == \mutable(x->next) &&
       \writable(x) == \writable(x->next)) ) )

// ---------------------------------------------------------------------------------------------------------
/*
_(logic \bool maintainsAcross(struct s_node * x, struct s_node * y, \state enter, \state exit) = 
	((! (x \in \at(enter, sllN(y)))) ==> \at(enter, sllN(y)) == \at(exit, sllN(y))) &&
	((! (x \in \at(enter, sllN(y)))) ==> \at(enter, sll(y)) == \at(exit, sll(y))) &&
	((! (x \in \at(enter, sllN(y)))) ==> \at(enter, sllKeys(y)) == \at(exit, sllKeys(y)))
	;)
	*/
/*
_(logic \bool disjointMaintainsAcross(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	(\disjoint(\at(enter, N(x)), \at(enter, N(y))) ==> 
             \at(enter, N(x)) == \at(exit, N(x))) &&
	(\disjoint(\at(enter, N(x)), \at(enter, N(y))) ==> 
             \at(enter, sll(x)) == \at(exit, sll(x))) &&
	(\disjoint(\at(enter, N(x)), \at(enter, N(y))) ==> 
             \at(enter, keys(x)) == \at(exit, keys(x))) 
	;)
*/

/*
_(logic \bool maintainsAcrossLseg(struct s_node * x, struct s_node * y, \state enter, \state exit) = 
	((! (x \in \at(enter, lsegN(y, x)))) ==> \at(enter, lsegN(y, x)) == \at(exit, lsegN(y, x))) &&
	((! (x \in \at(enter, lsegN(y, x)))) ==> \at(enter, lseg (y, x)) == \at(exit, lseg (y, x))) &&
	((! (x \in \at(enter, lsegN(y, x)))) ==> \at(enter, lsegk(y, x)) == \at(exit, lsegk(y, x))) 
	;)
*/


#endif
