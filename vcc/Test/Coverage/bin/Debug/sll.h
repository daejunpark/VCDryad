#ifndef SLL_H
#define SLL_H
#include <vcc.h>
#include "dryad.h"

typedef 
struct node {
	int key;
	struct node * next;
} Node;
typedef unsigned uint;

_(logic \bool mutable_list(Node * x) =
  x != NULL ==> \mutable(x) && \writable(x))

_(logic \bool unfoldMutable(Node * x) =
  ((x != NULL && x->next != NULL)
  ==> (\mutable(x) == \mutable(x->next) &&
       \writable(x) == \writable(x->next)) ) )

_(logic \bool \unchangedSll(\object o) = 
  {:split} _dryad_sll(o) && _dryad_N(o) == \old(_dryad_N(o)) && _dryad_keys(o) == \old(_dryad_keys(o)) ;)
_(logic \bool \unchangedSrtl(\object o) = 
  {:split} _dryad_srtl(o) && _dryad_N(o) == \old(_dryad_N(o)) && _dryad_keys(o) == \old(_dryad_keys(o)) ;)
_(logic \bool \sllStar (\object o1, \object o2) = {:split} 
    _dryad_sll(o1) && _dryad_sll(o2)  && \disjoint(_dryad_N(o1), _dryad_N(o2)) ;)

_(logic \bool \srtlStar(\object o1, \object o2) = 
        {:split} _dryad_srtl(o1) && _dryad_srtl(o2) && \disjoint(_dryad_N(o1), _dryad_N(o2)) ;)
_(logic \bool \lsegStar(\object b,  \object  e) = 
        {:split} _dryad_lseg(b, e) && \disjoint(_dryad_lsegN(b, e), _dryad_N(e)) ;)
_(logic \bool \srtlsegStar(\object b,  \object  e) = 
        {:split} _dryad_srtlseg(b, e) && \disjoint(_dryad_lsegN(b, e), _dryad_N(e)) ;)

_(logic \bool \nnHeadSrtlsegStar(Node * b, Node * e) =
    (b != NULL ==> _dryad_srtlseg(b, e) && \disjoint(_dryad_lsegN(b, e), _dryad_N(e))) ;)


_(def void LemmaSkip(Node * b, Node * e)
	_(requires _dryad_sll(b) && _dryad_sll(e) && _dryad_lseg(b, e))
	_(ensures _dryad_N(b) == _dryad_lsegN(b, e) \union _dryad_N(e))
	_(ensures _dryad_llen(b) == (_dryad_lseglen(b, e) + _dryad_llen(e)))
	_(decreases _dryad_llen(b))
{
	if (b == e) {
		return;
	} else {
		_(assume _dryad_unfoldAll(b))
		_(assume _dryad_unfoldAllLseg(b, e))
		LemmaSkip(b->next, e);
	}
})

_(def void LemmaSkipSort(Node * b, Node * e)
	_(requires _dryad_srtl(b) && _dryad_srtl(e) && _dryad_srtlseg(b, e))
	_(ensures _dryad_N(b) == _dryad_lsegN(b, e) \union _dryad_N(e))
	_(ensures _dryad_llen(b) == (_dryad_lseglen(b, e) + _dryad_llen(e)))
	_(decreases _dryad_llen(b))
{
	if (b == e) {
		return;
	} else {
		_(assume _dryad_unfoldAllSort(b))
		_(assume _dryad_unfoldAllSrtlseg(b, e))
		LemmaSkipSort(b->next, e);
	}
} ;)


/*
_(def void LemmaSrtlImplSll(Node * x)
	_(reads \universe())
	_(requires _dryad_srtl(x))
	_(ensures  _dryad_srtl(x) && _dryad_sll(x))
	_(decreases _dryad_llen(x))
	{ 
		if (x != NULL) {
			_(assume _dryad_unfoldAllSort(x))
			LemmaSrtlImplSll(x->next);
		}
	}
;)
*/

_(def void SillyLemma(Node * x)
  _(reads \universe())
  _(requires _dryad_srtlseg(x, x))
  _(ensures _dryad_srtlseg(x, x))
{  }
)

_(def \bool \uselseg(\object b, \object e)
  _(reads \universe())
  //_(requires _dryad_srtLseg(b, e) && \disjoint(_dryad_N(e), _dryad_lsegN(b, e)))
  {/* notifies dryad transformer about the list segment */\bool ret = \true; return ret; }
  ;)

_(axiom \forall Node * x; _dryad_srtl(x) ==> _dryad_sll(x))
//_(axiom \forall Node * x, y; _dryad_srtlseg(x, y) ==> _dryad_lseg(x,y))
//_(axiom \forall Node * x; x != NULL ==> _dryad_srtlseg(x, x->next))

#endif

