#include "dryad_linux_list.h"

_(dryad)
void init_list_head(struct list_head * hd)
  _(requires hd != NULL)
  _(ensures hd->next == hd)
  _(ensures hd->prev == hd)
  _(ensures dllnext_lseg(hd->next, hd))
  _(ensures dllprev_lseg(hd->prev, hd))
  _(ensures dllnext_reach(hd) == dllprev_reach(hd))
  _(ensures dllnext_reach(hd) == \oset_singleton(hd))
{
  hd->next = hd;
  hd->prev = hd;
}

_(dryad)
void __list_add(struct list_head * elem, 
                struct list_head * prev, 
                struct list_head * next)
  _(requires prev != NULL)
  _(requires next != NULL)
  _(requires dllnext_lseg(next, prev))
  _(requires dllprev_lseg(prev, next))
{
  
}
