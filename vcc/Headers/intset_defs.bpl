type $intset = [int]bool;

function $intset_in(i:int, s:$intset): bool
  { s[i] }

function $intset_empty() : $intset
  { (lambda i:int :: false) }

function $intset_universe() : $intset
  { (lambda i:int :: true) }

function $intset_singleton(i:int) : $intset
  { (lambda j:int :: i == j) }

function $intset_union(S:$intset, P:$intset) : $intset
  { (lambda i:int :: S[i] || P[i]) }

function $intset_union_one1(el:int, S:$intset) : $intset
  { (lambda i:int :: (i == el) || S[i]) }
function $intset_union_one2(S:$intset, el:int) : $intset
  { (lambda i:int :: (i == el) || S[i]) }

function $intset_intersect(S:$intset, P:$intset) : $intset
  { (lambda i:int :: S[i] && P[i]) }

function $intset_diff(S:$intset, P:$intset) : $intset
  { (lambda i:int :: S[i] && !P[i]) }

function $intset_eq($intset, $intset) : bool;
// extensionality axiom
axiom(forall S: $intset, P: $intset :: { $intset_eq(S,P) }
  $intset_eq(S,P) <==> (forall i: int :: {S[i]} {P[i]} S[i] <==> P[i]));
axiom(forall S: $intset, P: $intset :: { $intset_eq(S,P) }
  $intset_eq(S,P) ==> S == P);

function $intset_subset(S:$intset, P:$intset): bool
  { $intset_eq($intset_intersect(S,P), S)  }

function $intset_disjoint(S:$intset, P:$intset): bool
  { $intset_eq($intset_intersect(S, P), $intset_empty()) }

function $intset_lt_one1(el:int, S:$intset) : bool
  { (forall i:int :: i <= el ==> !S[i]) }
function $intset_lt_one2(S:$intset, el:int) : bool
  { (forall i:int :: el <= i ==> !S[i]) }

function $intset_lt(S:$intset, P:$intset): bool
  { (forall i:int, j:int :: i <= j ==> (!P[i] || !S[j])) }

function $intset_le_one1(el:int, S:$intset) : bool
  { (forall i:int :: i < el ==> !S[i]) }
function $intset_le_one2(S:$intset, el:int) : bool
  { (forall i:int :: el < i ==> !S[i]) }

function $intset_le(S:$intset, P:$intset): bool
  { (forall i:int, j:int :: i < j ==> (!P[i] || !S[j])) }


