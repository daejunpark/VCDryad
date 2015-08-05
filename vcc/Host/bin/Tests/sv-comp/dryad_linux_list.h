#ifndef DRYAD_LINUX_LIST_DEFS_H
#define DRYAD_LINUX_LIST_DEFS_H

#include <vcc.h>
// ------------------------
#include <stdlib.h>

typedef
_(dryad "dllnext:dllnext_R:dllnext_values:dllnext_list_len:dllnext_lseg:dllnext_lseg_R:dllnext_lseg_values:dllnext_lseg_len:dllprev:dllprev_R:dllprev_values:dllprev_list_len:dllprev_lseg:dllprev_lseg_R:dllprev_lseg_values:dllprev_lseg_len")
struct list_head {
  int value;
  struct list_head * prev;
  struct list_head * next;
};


_(abstract _(dryad "base:dllnext") \bool dllnext(struct list_head * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
	;)

_(abstract _(dryad "base:dllnext_R") \oset dllnext_reach(struct list_head * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
	   		&& ((hd == NULL)  ==> (\result == \oset_empty())))
	;)

_(abstract _(dryad "base:dllnext_values") \intset dllnext_values(struct list_head * hd) // [value]
	_(reads \universe())
	_(ensures (hd != NULL ==> \intset_in(hd->value, \result)))
	_(ensures (hd == NULL ==> (\result == \intset_empty())))
	;)

_(abstract _(dryad "base:dllnext_list_len") \natural dllnext_list_len(struct list_head * x)
  _(reads \universe())
  _(ensures x != NULL ==> \result > 0)
  _(ensures x == NULL ==> \result == 0)
  ;)

_(abstract _(dryad "base:dllnext_lseg") \bool dllnext_lseg(struct list_head * hd, struct list_head * tl)
  _(reads \universe())
  _(ensures (hd == NULL && hd != tl) ==> \result)
  _(ensures hd == tl ==> \result)
  _(ensures tl == NULL ==> (\result == dllnext(hd)))
  _(ensures (dllnext(tl) && \oset_disjoint(dllnext_reach(tl), dllnext_lseg_reach(hd, tl))) ==>
             (dllnext(hd) 
						  && dllnext_values(hd) == \intset_union(dllnext_values(tl), dllnext_lseg_values(hd, tl))
//						  && _dryad_valueb(hd) == \intbag_union(_dryad_valueb(tl), _dryad_lsegb(hd, tl))
              && dllnext_list_len(hd) == (dllnext_lseg_len(hd, tl) + dllnext_list_len(tl)) 
						 ) )
  _(ensures (hd != NULL /*&& hd != tl */ && dllnext(tl->next) 
         && \oset_disjoint(dllnext_reach(tl->next), dllnext_lseg_reach(hd, tl)) 
		     && (! \oset_in(tl, dllnext_reach(tl->next)) ) 
		     && (! \oset_in(tl, dllnext_lseg_reach(hd, tl)))   ) ==>
                   (  dllnext_lseg (hd, tl->next) 
				   && dllnext_lseg_values(hd, tl->next) == \intset_union(\intset_singleton(tl->value), dllnext_lseg_values(hd, tl)) 
//				   && _dryad_lsegb(hd, tl->next) == \intbag_union(\intbag_singleton(tl->value), _dryad_lsegb(hd, tl))
				   && dllnext_lseg_reach(hd, tl->next) == \oset_union(\oset_singleton(tl), dllnext_lseg_reach(hd, tl))   ) 
           && dllnext_lseg_len(hd, tl->next) == (dllnext_lseg_len(hd, tl) + 1) ) 
  ;)

_(abstract _(dryad "base:dllnext_lseg_R") \oset dllnext_lseg_reach(struct list_head * hd, struct list_head * tl)
	_(reads \universe())
	_(ensures (hd == NULL && hd != tl) ==> \result == \oset_empty())
	_(ensures hd == tl ==> \result == \oset_empty())
	_(ensures (hd != NULL && hd != tl) ==> \oset_in(hd, \result))
	_(ensures tl == NULL ==> (\result == dllnext_reach(hd)))
  ;)

_(abstract _(dryad "base:dllnext_lseg_values") \intset dllnext_lseg_values(struct list_head * hd, struct list_head * tl)
  _(reads \universe())
  _(ensures (hd != NULL && hd != tl) ==> \intset_in(hd->value, \result))
  _(ensures (hd == NULL && hd != tl) ==> (\result == \intset_empty()))
  _(ensures hd == tl   ==> (\result == \intset_empty()))
  _(ensures tl == NULL ==> (\result == dllnext_values(hd)))
;)

_(abstract _(dryad "base:dllnext_lseg_len") \natural dllnext_lseg_len(struct list_head * hd, struct list_head * tl)
  _(reads \universe())
  _(ensures hd == tl   ==> \result == 0)
  _(ensures hd == NULL ==> \result == 0)
  _(ensures hd != tl   ==> \result > 0)
  _(ensures tl == NULL ==> \result == dllnext_lseg_len(hd, tl))
;)

// ======================================================================================================

_(abstract _(dryad "base:dllprev") \bool dllprev(struct list_head * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
	;)

_(abstract _(dryad "base:dllprev_R") \oset dllprev_reach(struct list_head * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
	   		&& ((hd == NULL)  ==> (\result == \oset_empty())))
	;)

_(abstract _(dryad "base:dllprev_values") \intset dllprev_values(struct list_head * hd) // [value]
	_(reads \universe())
	_(ensures (hd != NULL ==> \intset_in(hd->value, \result)))
	_(ensures (hd == NULL ==> (\result == \intset_empty())))
	;)

_(abstract _(dryad "base:dllprev_list_len") \natural dllprev_list_len(struct list_head * x)
  _(reads \universe())
  _(ensures x != NULL ==> \result > 0)
  _(ensures x == NULL ==> \result == 0)
  ;)

_(abstract _(dryad "base:dllprev_lseg") \bool dllprev_lseg(struct list_head * hd, struct list_head * tl)
  _(reads \universe())
  _(ensures (hd == NULL && hd != tl) ==> \result)
  _(ensures hd == tl ==> \result)
  _(ensures tl == NULL ==> (\result == dllprev(hd)))
  _(ensures (dllprev(tl) && \oset_disjoint(dllprev_reach(tl), dllprev_lseg_reach(hd, tl))) ==>
             (dllprev(hd) 
						  && dllprev_values(hd) == \intset_union(dllprev_values(tl), dllprev_lseg_values(hd, tl))
//						  && _dryad_valueb(hd) == \intbag_union(_dryad_valueb(tl), _dryad_lsegb(hd, tl))
              && dllprev_list_len(hd) == (dllprev_lseg_len(hd, tl) + dllprev_list_len(tl)) 
						 ) )
  _(ensures (hd != NULL /*&& hd != tl */ && dllprev(tl->prev) 
         && \oset_disjoint(dllprev_reach(tl->prev), dllprev_lseg_reach(hd, tl)) 
		     && (! \oset_in(tl, dllprev_reach(tl->prev)) ) 
		     && (! \oset_in(tl, dllprev_lseg_reach(hd, tl)))   ) ==>
                   (  dllprev_lseg (hd, tl->prev) 
				   && dllprev_lseg_values(hd, tl->prev) == \intset_union(\intset_singleton(tl->value), dllprev_lseg_values(hd, tl)) 
//				   && _dryad_lsegb(hd, tl->prev) == \intbag_union(\intbag_singleton(tl->value), _dryad_lsegb(hd, tl))
				   && dllprev_lseg_reach(hd, tl->prev) == \oset_union(\oset_singleton(tl), dllprev_lseg_reach(hd, tl))   ) 
           && dllprev_lseg_len(hd, tl->prev) == (dllprev_lseg_len(hd, tl) + 1) ) 
  ;)

_(abstract _(dryad "base:dllprev_lseg_R") \oset dllprev_lseg_reach(struct list_head * hd, struct list_head * tl)
	_(reads \universe())
	_(ensures (hd == NULL && hd != tl) ==> \result == \oset_empty())
	_(ensures hd == tl ==> \result == \oset_empty())
	_(ensures (hd != NULL && hd != tl) ==> \oset_in(hd, \result))
	_(ensures tl == NULL ==> (\result == dllprev_reach(hd)))
  ;)

_(abstract _(dryad "base:dllprev_lseg_values") \intset dllprev_lseg_values(struct list_head * hd, struct list_head * tl)
  _(reads \universe())
  _(ensures (hd != NULL && hd != tl) ==> \intset_in(hd->value, \result))
  _(ensures (hd == NULL && hd != tl) ==> (\result == \intset_empty()))
  _(ensures hd == tl   ==> (\result == \intset_empty()))
  _(ensures tl == NULL ==> (\result == dllprev_values(hd)))
;)

_(abstract _(dryad "base:dllprev_lseg_len") \natural dllprev_lseg_len(struct list_head * hd, struct list_head * tl)
  _(reads \universe())
  _(ensures hd == tl   ==> \result == 0)
  _(ensures hd == NULL ==> \result == 0)
  _(ensures hd != tl   ==> \result > 0)
  _(ensures tl == NULL ==> \result == dllprev_lseg_len(hd, tl))
;)


// ----------------------------------------------------------------------------------------------------------------------------
_(logic _(dryad "unfold:dllnext") \bool unfold_dllnext(struct list_head * hd) =
	(hd != NULL ==>
		(dllnext(hd) <==> 
			(dllnext(hd->next) && 
			(hd->next != NULL ==> hd->next->prev == hd) &&
			(! \oset_in(hd, dllnext_reach(hd->next))) ) ) ) 
	;)

_(logic _(dryad "unfold:dllnext_R")  \bool unfold_dllnext_reach(struct list_head * hd) =
	(hd != NULL ==>	(dllnext_reach(hd) == \oset_union(dllnext_reach(hd->next), \oset_singleton(hd))) ) 	;)

_(logic _(dryad "unfold:dllnext_values") \bool unfold_dllnext_values(struct list_head * hd) =
	(hd != NULL ==> (dllnext_values(hd) == (\intset_union(dllnext_values(hd->next), \intset_singleton(hd->value))))) ;)

_(logic _(dryad "unfold:dllnext_list_len") \bool unfold_dllnext_list_len(struct list_head * hd) =
    (hd != NULL ==> (dllnext_list_len(hd) == dllnext_list_len(hd->next) + 1)) ;)

_(logic \bool unfold_dllnext_all_un(struct list_head * x) =
	 unfold_dllnext(x)
    && unfold_dllnext_reach(x)
    && unfold_dllnext_values(x)
    && unfold_dllnext_list_len(x)
	;)


_(logic _(dryad "unfold:dllnext_lseg") \bool unfold_dllnext_lseg(struct list_head * hd, struct list_head * tl) =
  (hd != tl ==>
      (dllnext_lseg(hd,tl) <==> 
        (dllnext_lseg(hd->next,tl) && (! \oset_in(hd, dllnext_lseg_reach(hd->next,tl))) ) ) ) 
  ;)

_(logic _(dryad "unfold:dllnext_lseg_R") \bool unfold_dllnext_lseg_reach(struct list_head * hd, struct list_head * tl) =
	(hd != tl ==> (dllnext_lseg_reach(hd, tl) == \oset_union(dllnext_lseg_reach(hd->next, tl), \oset_singleton(hd))) ) ;)

_(logic _(dryad "unfold:dllnext_lseg_values") \bool unfold_dllnext_lseg_values(struct list_head * hd, struct list_head * tl) =
  (hd != tl ==> dllnext_lseg_values(hd, tl) == 
          \intset_union(dllnext_lseg_values(hd->next, tl), \intset_singleton(hd->value)) ) ;)

_(logic _(dryad "unfold:dllnext_lseg_len") \bool unfold_dllnext_lseg_len(struct list_head * hd, struct list_head * tl) =
      (hd != tl ==> (dllnext_lseg_len(hd, tl) == (dllnext_lseg_len(hd->next, tl) + 1)))  ;)

_(logic \bool unfold_dllnext_all_bin(struct list_head * hd, struct list_head *  tl) =
  unfold_dllnext_lseg(hd, tl)
  && unfold_dllnext_lseg_reach(hd, tl)
  && unfold_dllnext_lseg_values(hd, tl)
  && unfold_dllnext_lseg_len(hd, tl)
;)

// ===============================================================================================================

_(logic _(dryad "unfold:dllprev") \bool unfold_dllprev(struct list_head * hd) =
	(hd != NULL ==>
		(dllprev(hd) <==> 
			(dllprev(hd->prev) && 
			(hd->prev != NULL ==> hd->prev->next == hd) &&
			(! \oset_in(hd, dllprev_reach(hd->prev))) ) ) ) 
	;)

_(logic _(dryad "unfold:dllprev_R")  \bool unfold_dllprev_reach(struct list_head * hd) =
	(hd != NULL ==>	(dllprev_reach(hd) == \oset_union(dllprev_reach(hd->prev), \oset_singleton(hd))) ) 	;)

_(logic _(dryad "unfold:dllprev_values") \bool unfold_dllprev_values(struct list_head * hd) =
	(hd != NULL ==> (dllprev_values(hd) == (\intset_union(dllprev_values(hd->prev), \intset_singleton(hd->value))))) ;)

_(logic _(dryad "unfold:dllprev_list_len") \bool unfold_dllprev_list_len(struct list_head * hd) =
    (hd != NULL ==> (dllprev_list_len(hd) == dllprev_list_len(hd->prev) + 1)) ;)

_(logic \bool unfold_dllprev_all_un(struct list_head * x) =
	 unfold_dllprev(x)
    && unfold_dllprev_reach(x)
    && unfold_dllprev_values(x)
    && unfold_dllprev_list_len(x)
	;)


_(logic _(dryad "unfold:dllprev_lseg") \bool unfold_dllprev_lseg(struct list_head * hd, struct list_head * tl) =
  (hd != tl ==>
      (dllprev_lseg(hd,tl) <==> 
        (dllprev_lseg(hd->prev,tl) && (! \oset_in(hd, dllprev_lseg_reach(hd->prev,tl))) ) ) ) 
  ;)

_(logic _(dryad "unfold:dllprev_lseg_R") \bool unfold_dllprev_lseg_reach(struct list_head * hd, struct list_head * tl) =
	(hd != tl ==> (dllprev_lseg_reach(hd, tl) == \oset_union(dllprev_lseg_reach(hd->prev, tl), \oset_singleton(hd))) ) ;)

_(logic _(dryad "unfold:dllprev_lseg_values") \bool unfold_dllprev_lseg_values(struct list_head * hd, struct list_head * tl) =
  (hd != tl ==> dllprev_lseg_values(hd, tl) == 
          \intset_union(dllprev_lseg_values(hd->prev, tl), \intset_singleton(hd->value)) ) ;)

_(logic _(dryad "unfold:dllprev_lseg_len") \bool unfold_dllprev_lseg_len(struct list_head * hd, struct list_head * tl) =
      (hd != tl ==> (dllprev_lseg_len(hd, tl) == (dllprev_lseg_len(hd->prev, tl) + 1)))  ;)

_(logic \bool unfold_dllprev_all_bin(struct list_head * hd, struct list_head *  tl) =
  unfold_dllprev_lseg(hd, tl)
  && unfold_dllprev_lseg_reach(hd, tl)
  && unfold_dllprev_lseg_values(hd, tl)
  && unfold_dllprev_lseg_len(hd, tl)
;)


// ----------------------------------------------------------------------------------------------------------------------------

_(logic _(dryad "same:dllnext") \bool same_dllnext(struct list_head * x, \state enter, \state exit) =
	\at(enter, dllnext(x)) == \at(exit, dllnext(x))
;)
_(logic _(dryad "same:dllnext_R") \bool same_dllnext_reach(struct list_head * x, \state enter, \state exit) = 
	\at(enter, dllnext_reach(x)) == \at(exit, dllnext_reach(x)) 
;)
_(logic _(dryad "same:dllnext_values") \bool same_dllnext_values(struct list_head * x, \state enter, \state exit) =
	\at(enter, dllnext_values(x)) == \at(exit, dllnext_values(x))
;)
_(logic _(dryad "same:dllnext_list_len") \bool same_dllnext_list_len(struct list_head * x, \state enter, \state exit) =
	\at(enter, dllnext_list_len(x)) == \at(exit, dllnext_list_len(x))
;)
_(logic \bool same_dllnext_all_un(struct list_head * x, \state enter, \state exit) = 
	same_dllnext(x, enter, exit) 
	&& same_dllnext_reach(x, enter, exit)
	&& same_dllnext_values(x, enter, exit)
	&& same_dllnext_list_len(x, enter, exit)
;)

_(logic _(dryad "same:dllnext_lseg") 
  \bool same_dllnext_lseg(struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
    \at(enter, dllnext_lseg(hd, tl)) == \at(exit, dllnext_lseg(hd, tl)) ;)

_(logic _(dryad "same:dllnext_lseg_R") 
  \bool same_dllnext_lseg_reach(struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
    \at(enter, dllnext_lseg_reach(hd, tl)) == \at(exit, dllnext_lseg_reach(hd, tl)) ;)

_(logic _(dryad "same:dllnext_lseg_values")
  \bool same_dllnext_lseg_values(struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
    \at(enter, dllnext_lseg_values(hd, tl)) == \at(exit, dllnext_lseg_values(hd, tl)) ;)
_(logic _(dryad "same:dllnext_lseg_len")
  \bool same_dllnext_lseg_len(struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
    \at(enter, dllnext_lseg_len(hd, tl)) == \at(exit, dllnext_lseg_len(hd, tl)) ;)

_(logic \bool same_dllnext_all_bin(struct list_head * hd, struct list_head * tl, \state enter, \state exit) = 
	same_dllnext_lseg(hd, tl, enter, exit) 
	&& same_dllnext_lseg_reach(hd, tl, enter, exit)
	&& same_dllnext_lseg_values(hd, tl, enter, exit)
	&& same_dllnext_lseg_len(hd, tl, enter, exit)
;)

// ======================================================================================================
_(logic _(dryad "same:dllprev") \bool same_dllprev(struct list_head * x, \state enter, \state exit) =
	\at(enter, dllprev(x)) == \at(exit, dllprev(x))
;)
_(logic _(dryad "same:dllprev_R") \bool same_dllprev_reach(struct list_head * x, \state enter, \state exit) = 
	\at(enter, dllprev_reach(x)) == \at(exit, dllprev_reach(x)) 
;)
_(logic _(dryad "same:dllprev_values") \bool same_dllprev_values(struct list_head * x, \state enter, \state exit) =
	\at(enter, dllprev_values(x)) == \at(exit, dllprev_values(x))
;)
_(logic _(dryad "same:dllprev_list_len") \bool same_dllprev_list_len(struct list_head * x, \state enter, \state exit) =
	\at(enter, dllprev_list_len(x)) == \at(exit, dllprev_list_len(x))
;)
_(logic \bool same_dllprev_all_un(struct list_head * x, \state enter, \state exit) = 
	same_dllprev(x, enter, exit) 
	&& same_dllprev_reach(x, enter, exit)
	&& same_dllprev_values(x, enter, exit)
	&& same_dllprev_list_len(x, enter, exit)
;)

_(logic _(dryad "same:dllprev_lseg") 
  \bool same_dllprev_lseg(struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
    \at(enter, dllprev_lseg(hd, tl)) == \at(exit, dllprev_lseg(hd, tl)) ;)

_(logic _(dryad "same:dllprev_lseg_R") 
  \bool same_dllprev_lseg_reach(struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
    \at(enter, dllprev_lseg_reach(hd, tl)) == \at(exit, dllprev_lseg_reach(hd, tl)) ;)

_(logic _(dryad "same:dllprev_lseg_values")
  \bool same_dllprev_lseg_values(struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
    \at(enter, dllprev_lseg_values(hd, tl)) == \at(exit, dllprev_lseg_values(hd, tl)) ;)
_(logic _(dryad "same:dllprev_lseg_len")
  \bool same_dllprev_lseg_len(struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
    \at(enter, dllprev_lseg_len(hd, tl)) == \at(exit, dllprev_lseg_len(hd, tl)) ;)

_(logic \bool same_dllprev_all_bin(struct list_head * hd, struct list_head * tl, \state enter, \state exit) = 
	same_dllprev_lseg(hd, tl, enter, exit) 
	&& same_dllprev_lseg_reach(hd, tl, enter, exit)
	&& same_dllprev_lseg_values(hd, tl, enter, exit)
	&& same_dllprev_lseg_len(hd, tl, enter, exit)
;)


// ------------------------------------------------------------------------------------------------------

_(logic _(dryad "cond:dllnext") 
  \bool cond_same_dllnext(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, dllnext_reach(y)))) ==> \at(enter, dllnext(y)) == \at(exit, dllnext(y)) ;)

_(logic _(dryad "cond:dllnext_R") 
  \bool cond_same_dllnext_reach(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, dllnext_reach(y)))) ==> \at(enter, dllnext_reach(y)) == \at(exit, dllnext_reach(y)) ;)

_(logic _(dryad "cond:dllnext_values") 
  \bool cond_same_dllnext_values(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, dllnext_reach(y)))) ==> \at(enter, dllnext_values(y)) == \at(exit, dllnext_values(y)) ;)
_(logic _(dryad "cond:dllnext_list_len") 
  \bool cond_same_dllnext_list_len(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, dllnext_reach(y)))) ==> \at(enter, dllnext_list_len(y)) == \at(exit, dllnext_list_len(y)) 
;)

_(logic
  \bool cond_same_dllnext_all_un(struct list_head * x, struct list_head * y, \state enter, \state exit) =
  	cond_same_dllnext(x, y, enter, exit) 
  	&& cond_same_dllnext_reach(x, y, enter, exit)
  	&& cond_same_dllnext_values(x, y, enter, exit) 
  	&& cond_same_dllnext_list_len(x, y, enter, exit) ;)

_(logic _(dryad "cond:dllnext_lseg") 
  \bool cond_same_dllnext_lseg(struct list_head * x, struct list_head * hd, struct list_head * tl, 
                      \state enter, \state exit) = 
    ((! \oset_in(x, \at(enter, dllnext_lseg_reach(hd, tl)))) ==> 
      \at(enter, dllnext_lseg(hd, tl)) == \at(exit, dllnext_lseg(hd, tl)) ) ;)

_(logic _(dryad "cond:dllnext_lseg_R") 
  \bool cond_same_dllnext_lseg_reach(struct list_head * x, struct list_head * hd, struct list_head * tl, 
                            \state enter, \state exit) = 
    ((! \oset_in(x, \at(enter, dllnext_lseg_reach(hd, tl)))) ==> 
      \at(enter, dllnext_lseg_reach(hd, tl)) == \at(exit, dllnext_lseg_reach(hd, tl)) ) ;)
_(logic _(dryad "cond:dllnext_lseg_values")
  \bool cond_same_dllnext_lseg_values(struct list_head * x, struct list_head * hd, struct list_head * tl, 
                            \state enter, \state exit) =
    ((! \oset_in(x, \at(enter, dllnext_lseg_reach(hd, tl)))) ==>
      \at(enter, dllnext_lseg_values(hd, tl)) == \at(exit, dllnext_lseg_values(hd, tl))) ;)
_(logic _(dryad "cond:dllnext_lseg_len")
  \bool cond_same_dllnext_lseg_len(struct list_head * x, struct list_head * hd, struct list_head * tl, 
                            \state enter, \state exit) =
    ((! \oset_in(x, \at(enter, dllnext_lseg_reach(hd, tl)))) ==>
      \at(enter, dllnext_lseg_len(hd, tl)) == \at(exit, dllnext_lseg_len(hd, tl))) ;)

_(logic 
  \bool cond_same_dllnext_all_bin(struct list_head * x, struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
	  cond_same_dllnext_lseg(x, hd, tl, enter, exit) 
  	&& cond_same_dllnext_lseg_reach(x, hd, tl, enter, exit)
  	&& cond_same_dllnext_lseg_values(x, hd, tl, enter, exit)
  	&& cond_same_dllnext_lseg_len(x, hd, tl, enter, exit)
;)

// ==============================================================================================================
_(logic _(dryad "cond:dllprev") 
  \bool cond_same_dllprev(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev(y)) == \at(exit, dllprev(y)) ;)

_(logic _(dryad "cond:dllprev_R") 
  \bool cond_same_dllprev_reach(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev_reach(y)) == \at(exit, dllprev_reach(y)) ;)

_(logic _(dryad "cond:dllprev_values") 
  \bool cond_same_dllprev_values(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev_values(y)) == \at(exit, dllprev_values(y)) ;)
_(logic _(dryad "cond:dllprev_list_len") 
  \bool cond_same_dllprev_list_len(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev_list_len(y)) == \at(exit, dllprev_list_len(y)) 
;)

_(logic
  \bool cond_same_dllprev_all_un(struct list_head * x, struct list_head * y, \state enter, \state exit) =
  	cond_same_dllprev(x, y, enter, exit) 
  	&& cond_same_dllprev_reach(x, y, enter, exit)
  	&& cond_same_dllprev_values(x, y, enter, exit) 
  	&& cond_same_dllprev_list_len(x, y, enter, exit) ;)

_(logic _(dryad "cond:dllprev_lseg") 
  \bool cond_same_dllprev_lseg(struct list_head * x, struct list_head * hd, struct list_head * tl, 
                      \state enter, \state exit) = 
    ((! \oset_in(x, \at(enter, dllprev_lseg_reach(hd, tl)))) ==> 
      \at(enter, dllprev_lseg(hd, tl)) == \at(exit, dllprev_lseg(hd, tl)) ) ;)

_(logic _(dryad "cond:dllprev_lseg_R") 
  \bool cond_same_dllprev_lseg_reach(struct list_head * x, struct list_head * hd, struct list_head * tl, 
                            \state enter, \state exit) = 
    ((! \oset_in(x, \at(enter, dllprev_lseg_reach(hd, tl)))) ==> 
      \at(enter, dllprev_lseg_reach(hd, tl)) == \at(exit, dllprev_lseg_reach(hd, tl)) ) ;)
_(logic _(dryad "cond:dllprev_lseg_values")
  \bool cond_same_dllprev_lseg_values(struct list_head * x, struct list_head * hd, struct list_head * tl, 
                            \state enter, \state exit) =
    ((! \oset_in(x, \at(enter, dllprev_lseg_reach(hd, tl)))) ==>
      \at(enter, dllprev_lseg_values(hd, tl)) == \at(exit, dllprev_lseg_values(hd, tl))) ;)
_(logic _(dryad "cond:dllprev_lseg_len")
  \bool cond_same_dllprev_lseg_len(struct list_head * x, struct list_head * hd, struct list_head * tl, 
                            \state enter, \state exit) =
    ((! \oset_in(x, \at(enter, dllprev_lseg_reach(hd, tl)))) ==>
      \at(enter, dllprev_lseg_len(hd, tl)) == \at(exit, dllprev_lseg_len(hd, tl))) ;)

_(logic 
  \bool cond_same_dllprev_all_bin(struct list_head * x, struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
	  cond_same_dllprev_lseg(x, hd, tl, enter, exit) 
  	&& cond_same_dllprev_lseg_reach(x, hd, tl, enter, exit)
  	&& cond_same_dllprev_lseg_values(x, hd, tl, enter, exit)
  	&& cond_same_dllprev_lseg_len(x, hd, tl, enter, exit)
;)

// ================ disjoint ============================================================
_(logic _(dryad "disj:dllprev") 
  \bool disj_same_dllprev(\oset heaplet, struct list_head * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev(y)) == \at(exit, dllprev(y)) ;)

_(logic _(dryad "disj:dllprev_R") 
  \bool disj_same_dllprev_reach(\oset heaplet, struct list_head * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev_reach(y)) == \at(exit, dllprev_reach(y)) ;)

_(logic _(dryad "disj:dllprev_values") 
  \bool disj_same_dllprev_values(\oset heaplet, struct list_head * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev_values(y)) == \at(exit, dllprev_values(y)) ;)
_(logic _(dryad "disj:dllprev_list_len") 
  \bool disj_same_dllprev_list_len(\oset heaplet, struct list_head * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev_list_len(y)) == \at(exit, dllprev_list_len(y)) 
;)

_(logic
  \bool disj_same_dllprev_all_un(\oset heaplet, struct list_head * y, \state enter, \state exit) =
  	disj_same_dllprev(\at(enter, heaplet), y, enter, exit) 
  	&& disj_same_dllprev_reach(\at(enter, heaplet), y, enter, exit)
  	&& disj_same_dllprev_values(\at(enter, heaplet), y, enter, exit) 
  	&& disj_same_dllprev_list_len(\at(enter, heaplet), y, enter, exit) ;)

_(logic _(dryad "disj:dllprev_lseg") 
  \bool disj_same_dllprev_lseg(\oset heaplet, struct list_head * hd, struct list_head * tl, 
                      \state enter, \state exit) = 
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, dllprev_lseg_reach(hd, tl)))) ==> 
      \at(enter, dllprev_lseg(hd, tl)) == \at(exit, dllprev_lseg(hd, tl)) ) ;)

_(logic _(dryad "disj:dllprev_lseg_R") 
  \bool disj_same_dllprev_lseg_reach(\oset heaplet, struct list_head * hd, struct list_head * tl, 
                            \state enter, \state exit) = 
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, dllprev_lseg_reach(hd, tl)))) ==> 
      \at(enter, dllprev_lseg_reach(hd, tl)) == \at(exit, dllprev_lseg_reach(hd, tl)) ) ;)
_(logic _(dryad "disj:dllprev_lseg_values")
  \bool disj_same_dllprev_lseg_values(\oset heaplet, struct list_head * hd, struct list_head * tl, 
                            \state enter, \state exit) =
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, dllprev_lseg_reach(hd, tl)))) ==>
      \at(enter, dllprev_lseg_values(hd, tl)) == \at(exit, dllprev_lseg_values(hd, tl))) ;)
_(logic _(dryad "disj:dllprev_lseg_len")
  \bool disj_same_dllprev_lseg_len(\oset heaplet, struct list_head * hd, struct list_head * tl, 
                            \state enter, \state exit) =
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, dllprev_lseg_reach(hd, tl)))) ==>
      \at(enter, dllprev_lseg_len(hd, tl)) == \at(exit, dllprev_lseg_len(hd, tl))) ;)

_(logic 
  \bool disj_same_dllprev_all_bin(\oset heaplet, struct list_head * hd, struct list_head * tl, \state enter, \state exit) =
	  disj_same_dllprev_lseg(\at(enter, heaplet), hd, tl, enter, exit) 
  	&& disj_same_dllprev_lseg_reach(\at(enter, heaplet), hd, tl, enter, exit)
  	&& disj_same_dllprev_lseg_values(\at(enter, heaplet), hd, tl, enter, exit)
  	&& disj_same_dllprev_lseg_len(\at(enter, heaplet), hd, tl, enter, exit)
;)


// dummy function denoting the end of dllnext node defs
_(abstract _(dryad "end") void end_dl_node_defs(struct list_head * x) ;)
// ---------------------------------------------------------------------------------------------------------

#endif
