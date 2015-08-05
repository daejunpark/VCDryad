#ifndef INTBAG_DEFS_H
#define INTBAG_DEFS_H

_(ghost typedef \natural \intbag[int]);
_(logic \intbag \intbag_empty =    (\lambda int k; (\natural) 0))
//_(logic \intset \intmset_universe = (\lambda int k; \true))
_(logic \intbag \intbag_singleton(int el) = (\lambda int k; el == k ? (\natural) 1 : (\natural) 0))
_(logic \intbag \intbag_union(\intbag ib1, \intbag ib2) = (\lambda int k; ib1[k] + ib2[k]))
_(logic \intbag \intbag_union0(int el, \intbag ib) = (\lambda int k; el == k ? (1 + ib[k]) : ib[k] ))
_(logic \bool \intbag_in(int el, \intbag ib) = ib[el] > 0)
_(logic \bool \intbag_disjoint(\intbag ib1, \intbag ib2) = (\forall int k; (ib1[k] == 0) || (ib2[k] == 0)))
_(logic \bool \intbag_subset(\intbag ib1, \intbag ib2) = (\forall int k; ib1[k] <= ib2[k]))
//_(logic \bool \intset_eq(\intset is1, \intset is2) = (\forall int k; is1[k] <==> is2[k]))
_(logic \intbag \intbag_intersect(\intbag ib1, \intbag ib2) = (\lambda int k; ib1[k] < ib2[k] ? ib1[k] : ib2[k]))
_(logic \intbag \intbag_diff(\intbag ib1, \intbag ib2) = (\lambda int k; ib1[k] > ib2[k] ? (ib1[k] - ib2[k]) : (\natural)0 ))

_(axiom \forall int k; !\intbag_in(k, \intbag_empty))
//_(axiom \forall int k; \intset_in(k, \intset_universe))

#endif