type $oset = [$ptr]bool;

function $oset_in(i:$ptr, s:$oset): bool
  { s[i] }

function $oset_empty() : $oset
  { (lambda i:$ptr :: false) }

function $oset_universe() : $oset
  { (lambda i:$ptr :: true) }

function $oset_singleton(i:$ptr) : $oset
  { (lambda j:$ptr :: i == j) }

function $oset_union(S:$oset, P:$oset) : $oset
  { (lambda i:$ptr :: S[i] || P[i]) }

function $oset_union_one1(el:$ptr, S:$oset) : $oset
  { (lambda i:$ptr :: (i == el) || S[i]) }
function $oset_union_one2(S:$oset, el:$ptr) : $oset
  { (lambda i:$ptr :: (i == el) || S[i]) }

function $oset_$ptrersect(S:$oset, P:$oset) : $oset
  { (lambda i:$ptr :: S[i] && P[i]) }

function $oset_diff(S:$oset, P:$oset) : $oset
  { (lambda i:$ptr :: S[i] && !P[i]) }

function $oset_eq($oset, $oset) : bool;
// extensionality axiom
axiom(forall S: $oset, P: $oset :: { $oset_eq(S,P) }
  $oset_eq(S,P) <==> (forall i: $ptr :: {S[i]} {P[i]} S[i] <==> P[i]));
axiom(forall S: $oset, P: $oset :: { $oset_eq(S,P) }
  $oset_eq(S,P) ==> S == P);

function $oset_subset(S:$oset, P:$oset): bool
  { $oset_eq($oset_$ptrersect(S,P), S)  }

function $oset_disjo$ptr(S:$oset, P:$oset): bool
  { $oset_eq($oset_$ptrersect(S, P), $oset_empty()) }
