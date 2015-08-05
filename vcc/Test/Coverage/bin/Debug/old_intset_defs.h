#ifndef INTSET_DEFS_H
#define INTSET_DEFS_H

_(ghost typedef \bool \intset[int]);
_(logic \intset \intset_empty =    (\lambda int k; \false))
_(logic \intset \intest_universe = (\lambda int k; \true))
_(logic \intset \intset_singleton(int el) = (\lambda int k; el == k ? \true : \false))
_(logic \intset \intset_union(\intset is1, \intset is2) = (\lambda int k; is1[k] || is2[k]))
_(logic \intset \intset_union0(int el, \intset is) = (\lambda int k; el == k || is[k]))
_(logic \bool \intset_in(int el, \intset is) = is[el])
_(logic \bool \intset_disjoint(\intset is1, \intset is2) = (\forall int k; !is1[k] || !is2[k]))
_(logic \bool \intset_subset(\intset is1, \intset is2) = (\forall int k; is1[k] ==> is2[k]))
_(logic \intset \intset_intersect(\intset is1, \intset is2) = (\lambda int k; is1[k] && is2[k]))
_(logic \intset \intset_diff(\intset is1, \intset is2) = (\lambda int k; is1[k] && !is2[k]))

_(axiom \forall int k; !\intset_in(k, \intset_empty))

#endif
