#include "dryad_sls.h"

Node * split(Node * x)
  _(requires sll(x))
  _(ensures \old(sll(x)))
  _(ensures sll(\result))
  _(ensures sll(x))
  _(ensures \oset_disjoint(sll_reach(\result), sll_reach(x)))
  
;
_(dryad)
Node * merge(Node * a, Node * b) 
  _(requires srtl(a))
  _(requires srtl(b))
  _(requires \oset_disjoint(srtl_reach(a), srtl_reach(b)))
  _(ensures srtl(\result))
;
_(dryad)
Node * merge_sort(Node * lst) 
  _(requires sll(lst))
  _(ensures sll(\result))
  _(ensures srtl(\result))
{
  _(assume mutable_list(lst))
  Node * lst1 = split(lst);
  Node * a = merge_sort(lst1);
  Node * b = merge_sort(lst);
  return merge(a, b);
}
