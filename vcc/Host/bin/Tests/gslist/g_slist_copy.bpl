axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

const unique ^$##thread_id: $ctype;

axiom $def_math_type(^$##thread_id);

type $##thread_id;

const unique ^$##club: $ctype;

axiom $def_math_type(^$##club);

type $##club;

const unique ^s_node: $ctype;

axiom $is_span_sequential(^s_node);

axiom $def_struct_type(^s_node, 16, false, false);

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2(#s1, #s2, #p, ^s_node) } $inv2(#s1, #s2, #p, ^s_node) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2_without_lemmas(#s1, #s2, #p, ^s_node) } $inv2_without_lemmas(#s1, #s2, #p, ^s_node) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall p: $ptr, q: $ptr, s: $state :: { $in(q, $composite_extent(s, p, ^s_node)) } $in(q, $composite_extent(s, p, ^s_node)) == (q == p));

const unique s_node.key: $field;

axiom $def_phys_field(^s_node, s_node.key, ^^i4, false, 0);

const unique s_node.next: $field;

axiom $def_phys_field(^s_node, s_node.next, $ptr_to(^s_node), false, 8);

function F#glob_reach() : $oset;

const unique cf#glob_reach: $pure_function;

axiom $function_arg_type(cf#glob_reach, 0, ^$#oset);

procedure glob_reach() returns ($result: $oset);
  free ensures $result == F#glob_reach();
  free ensures $call_transition(old($s), $s);



const unique ^$#_purecall_handler#1: $ctype;

axiom $def_fnptr_type(^$#_purecall_handler#1);

type $#_purecall_handler#1;

const unique ^$#_invalid_parameter_handler#2: $ctype;

axiom $def_fnptr_type(^$#_invalid_parameter_handler#2);

type $#_invalid_parameter_handler#2;

const unique ^$#g_slist_copy.c..36263#3: $ctype;

axiom $def_fnptr_type(^$#g_slist_copy.c..36263#3);

type $#g_slist_copy.c..36263#3;

const unique ^$#_PtFuncCompare#4: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#4);

type $#_PtFuncCompare#4;

const unique ^$#_PtFuncCompare#5: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#5);

type $#_PtFuncCompare#5;

const unique ^$#_PtFuncCompare#6: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#6);

type $#_PtFuncCompare#6;

const unique ^$#_PtFuncCompare#7: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#7);

type $#_PtFuncCompare#7;

const unique ^$#_onexit_t#8: $ctype;

axiom $def_fnptr_type(^$#_onexit_t#8);

type $#_onexit_t#8;

function F#sll(#s: $state, SP#hd: $ptr) : bool;

const unique cf#sll: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr :: { F#sll(#s, SP#hd) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#sll(#s, SP#hd));

axiom $function_arg_type(cf#sll, 0, ^^bool);

axiom $function_arg_type(cf#sll, 1, $ptr_to(^s_node));

procedure sll(SP#hd: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result;
  free ensures $result == F#sll($s, SP#hd);
  free ensures $call_transition(old($s), $s);



function F#sll_reach(#s: $state, SP#hd: $ptr) : $oset;

const unique cf#sll_reach: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr :: { F#sll_reach(#s, SP#hd) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), F#sll_reach(#s, SP#hd))) && ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#sll_reach(#s, SP#hd) == $oset_empty()));

axiom $function_arg_type(cf#sll_reach, 0, ^$#oset);

axiom $function_arg_type(cf#sll_reach, 1, $ptr_to(^s_node));

procedure sll_reach(SP#hd: $ptr) returns ($result: $oset);
  ensures ($non_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), $result)) && ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result == $oset_empty());
  free ensures $result == F#sll_reach($s, SP#hd);
  free ensures $call_transition(old($s), $s);



function F#sll_keys(#s: $state, SP#hd: $ptr) : $intset;

const unique cf#sll_keys: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr :: { F#sll_keys(#s, SP#hd) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $intset_in($rd_inv(#s, s_node.key, $phys_ptr_cast(SP#hd, ^s_node)), F#sll_keys(#s, SP#hd))) && ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#sll_keys(#s, SP#hd) == $intset_empty()));

axiom $function_arg_type(cf#sll_keys, 0, ^$#intset);

axiom $function_arg_type(cf#sll_keys, 1, $ptr_to(^s_node));

procedure sll_keys(SP#hd: $ptr) returns ($result: $intset);
  ensures $non_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $intset_in($rd_inv($s, s_node.key, $phys_ptr_cast(SP#hd, ^s_node)), $result);
  ensures $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result == $intset_empty();
  free ensures $result == F#sll_keys($s, SP#hd);
  free ensures $call_transition(old($s), $s);



function F#sll_list_len_next(#s: $state, SP#x: $ptr) : int;

const unique cf#sll_list_len_next: $pure_function;

axiom (forall #s: $state, SP#x: $ptr :: { F#sll_list_len_next(#s, SP#x) } 1 < $decreases_level ==> $in_range_nat(F#sll_list_len_next(#s, SP#x)) && ($non_null($phys_ptr_cast(SP#x, ^s_node)) ==> F#sll_list_len_next(#s, SP#x) > 0) && ($is_null($phys_ptr_cast(SP#x, ^s_node)) ==> F#sll_list_len_next(#s, SP#x) == 0));

axiom $function_arg_type(cf#sll_list_len_next, 0, ^^nat);

axiom $function_arg_type(cf#sll_list_len_next, 1, $ptr_to(^s_node));

procedure sll_list_len_next(SP#x: $ptr) returns ($result: int);
  free ensures $in_range_nat($result);
  ensures $non_null($phys_ptr_cast(SP#x, ^s_node)) ==> $result > 0;
  ensures $is_null($phys_ptr_cast(SP#x, ^s_node)) ==> $result == 0;
  free ensures $result == F#sll_list_len_next($s, SP#x);
  free ensures $call_transition(old($s), $s);



function F#sll_lseg(#s: $state, SP#hd: $ptr, SP#tl: $ptr) : bool;

const unique cf#sll_lseg: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr, SP#tl: $ptr :: { F#sll_lseg(#s, SP#hd, SP#tl) } 1 < $decreases_level ==> ($is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> F#sll_lseg(#s, SP#hd, SP#tl) == F#sll(#s, $phys_ptr_cast(SP#hd, ^s_node))) && ($phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg(#s, SP#hd, SP#tl)) && (F#sll_lseg(#s, SP#hd, SP#tl) ==> $oset_disjoint(F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), $oset_singleton($phys_ptr_cast(SP#tl, ^s_node)))) && (F#sll_lseg(#s, SP#hd, SP#tl) && F#sll(#s, $phys_ptr_cast(SP#tl, ^s_node)) ==> F#sll(#s, $phys_ptr_cast(SP#hd, ^s_node)) && F#sll_reach(#s, $phys_ptr_cast(SP#hd, ^s_node)) == $oset_union(F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_reach(#s, $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_keys(#s, $phys_ptr_cast(SP#hd, ^s_node)) == $intset_union(F#sll_lseg_keys(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_keys(#s, $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_list_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_list_len_next(#s, $phys_ptr_cast(SP#tl, ^s_node)))) && (F#sll_lseg(#s, SP#hd, SP#tl) && $non_null($phys_ptr_cast(SP#tl, ^s_node)) && $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) && $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node) != $phys_ptr_cast(SP#hd, ^s_node) && !$oset_in($rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node), F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) ==> F#sll_lseg(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) && F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $oset_union(F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), $oset_singleton($phys_ptr_cast(SP#tl, ^s_node))) && F#sll_lseg_keys(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $intset_union(F#sll_lseg_keys(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), $intset_singleton($rd_inv(#s, s_node.key, $phys_ptr_cast(SP#tl, ^s_node)))) && F#sll_lseg_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), 1)));

axiom $function_arg_type(cf#sll_lseg, 0, ^^bool);

axiom $function_arg_type(cf#sll_lseg, 1, $ptr_to(^s_node));

axiom $function_arg_type(cf#sll_lseg, 2, $ptr_to(^s_node));

procedure sll_lseg(SP#hd: $ptr, SP#tl: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> $result == F#sll($s, $phys_ptr_cast(SP#hd, ^s_node));
  ensures $phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> $result;
  ensures $result ==> $oset_disjoint(F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), $oset_singleton($phys_ptr_cast(SP#tl, ^s_node)));
  ensures $result && F#sll($s, $phys_ptr_cast(SP#tl, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SP#hd, ^s_node)) && F#sll_reach($s, $phys_ptr_cast(SP#hd, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_reach($s, $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_keys($s, $phys_ptr_cast(SP#hd, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_keys($s, $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_list_len_next($s, $phys_ptr_cast(SP#hd, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_list_len_next($s, $phys_ptr_cast(SP#tl, ^s_node)));
  ensures $result && $non_null($phys_ptr_cast(SP#tl, ^s_node)) && $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) && $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node) != $phys_ptr_cast(SP#hd, ^s_node) && !$oset_in($rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node), F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) ==> F#sll_lseg($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) && F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $oset_union(F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), $oset_singleton($phys_ptr_cast(SP#tl, ^s_node))) && F#sll_lseg_keys($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $intset_union(F#sll_lseg_keys($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SP#tl, ^s_node)))) && F#sll_lseg_len_next($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), 1);
  free ensures $result == F#sll_lseg($s, SP#hd, SP#tl);
  free ensures $call_transition(old($s), $s);



function F#sll_lseg_reach(#s: $state, SP#hd: $ptr, SP#tl: $ptr) : $oset;

const unique cf#sll_lseg_reach: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr, SP#tl: $ptr :: { F#sll_lseg_reach(#s, SP#hd, SP#tl) } 1 < $decreases_level ==> ($is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> F#sll_lseg_reach(#s, SP#hd, SP#tl) == F#sll_reach(#s, $phys_ptr_cast(SP#hd, ^s_node))) && ($phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg_reach(#s, SP#hd, SP#tl) == $oset_empty()) && ($non_null($phys_ptr_cast(SP#hd, ^s_node)) && $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), F#sll_lseg_reach(#s, SP#hd, SP#tl))));

axiom $function_arg_type(cf#sll_lseg_reach, 0, ^$#oset);

axiom $function_arg_type(cf#sll_lseg_reach, 1, $ptr_to(^s_node));

axiom $function_arg_type(cf#sll_lseg_reach, 2, $ptr_to(^s_node));

procedure sll_lseg_reach(SP#hd: $ptr, SP#tl: $ptr) returns ($result: $oset);
  ensures $is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> $result == F#sll_reach($s, $phys_ptr_cast(SP#hd, ^s_node));
  ensures $phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> $result == $oset_empty();
  ensures $non_null($phys_ptr_cast(SP#hd, ^s_node)) && $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), $result);
  free ensures $result == F#sll_lseg_reach($s, SP#hd, SP#tl);
  free ensures $call_transition(old($s), $s);



function F#sll_lseg_keys(#s: $state, SP#hd: $ptr, SP#tl: $ptr) : $intset;

const unique cf#sll_lseg_keys: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr, SP#tl: $ptr :: { F#sll_lseg_keys(#s, SP#hd, SP#tl) } 1 < $decreases_level ==> ($is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> F#sll_lseg_keys(#s, SP#hd, SP#tl) == F#sll_keys(#s, $phys_ptr_cast(SP#hd, ^s_node))) && ($phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg_keys(#s, SP#hd, SP#tl) == $intset_empty()) && ($non_null($phys_ptr_cast(SP#hd, ^s_node)) && $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $intset_in($rd_inv(#s, s_node.key, $phys_ptr_cast(SP#hd, ^s_node)), F#sll_lseg_keys(#s, SP#hd, SP#tl))));

axiom $function_arg_type(cf#sll_lseg_keys, 0, ^$#intset);

axiom $function_arg_type(cf#sll_lseg_keys, 1, $ptr_to(^s_node));

axiom $function_arg_type(cf#sll_lseg_keys, 2, $ptr_to(^s_node));

procedure sll_lseg_keys(SP#hd: $ptr, SP#tl: $ptr) returns ($result: $intset);
  ensures $is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> $result == F#sll_keys($s, $phys_ptr_cast(SP#hd, ^s_node));
  ensures $phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> $result == $intset_empty();
  ensures $non_null($phys_ptr_cast(SP#hd, ^s_node)) && $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $intset_in($rd_inv($s, s_node.key, $phys_ptr_cast(SP#hd, ^s_node)), $result);
  free ensures $result == F#sll_lseg_keys($s, SP#hd, SP#tl);
  free ensures $call_transition(old($s), $s);



function F#sll_lseg_len_next(#s: $state, SP#hd: $ptr, SP#tl: $ptr) : int;

const unique cf#sll_lseg_len_next: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr, SP#tl: $ptr :: { F#sll_lseg_len_next(#s, SP#hd, SP#tl) } 1 < $decreases_level ==> $in_range_nat(F#sll_lseg_len_next(#s, SP#hd, SP#tl)) && ($is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> F#sll_lseg_len_next(#s, SP#hd, SP#tl) == F#sll_list_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node))) && ($phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg_len_next(#s, SP#hd, SP#tl) == 0) && ($non_null($phys_ptr_cast(SP#hd, ^s_node)) && $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg_len_next(#s, SP#hd, SP#tl) > 0));

axiom $function_arg_type(cf#sll_lseg_len_next, 0, ^^nat);

axiom $function_arg_type(cf#sll_lseg_len_next, 1, $ptr_to(^s_node));

axiom $function_arg_type(cf#sll_lseg_len_next, 2, $ptr_to(^s_node));

procedure sll_lseg_len_next(SP#hd: $ptr, SP#tl: $ptr) returns ($result: int);
  free ensures $in_range_nat($result);
  ensures $is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> $result == F#sll_list_len_next($s, $phys_ptr_cast(SP#hd, ^s_node));
  ensures $phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> $result == 0;
  ensures $non_null($phys_ptr_cast(SP#hd, ^s_node)) && $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $result > 0;
  free ensures $result == F#sll_lseg_len_next($s, SP#hd, SP#tl);
  free ensures $call_transition(old($s), $s);



procedure g_slist_copy(P#list: $ptr) returns ($result: $ptr);
  requires F#sll($s, $phys_ptr_cast(P#list, ^s_node));
  modifies $s, $cev_pc;
  ensures F#sll($s, $phys_ptr_cast(P#list, ^s_node)) && F#sll($s, $phys_ptr_cast($result, ^s_node)) && $oset_disjoint(F#sll_reach($s, $phys_ptr_cast(P#list, ^s_node)), F#sll_reach($s, $phys_ptr_cast($result, ^s_node)));
  ensures F#sll_keys($s, $phys_ptr_cast($result, ^s_node)) == F#sll_keys($s, $phys_ptr_cast(P#list, ^s_node));
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation g_slist_copy(P#list: $ptr) returns ($result: $ptr)
{
  var stmtexpr11#13: $ptr;
  var SL#list9: $ptr;
  var stmtexpr10#12: $ptr;
  var SL#last8: $ptr;
  var stmtexpr9#11: $state;
  var SL#_dryad_S13: $state;
  var stmtexpr8#10: $state;
  var SL#_dryad_S12: $state;
  var stmtexpr7#9: $state;
  var SL#_dryad_S11: $state;
  var stmtexpr6#8: $state;
  var SL#_dryad_S10: $state;
  var stmtexpr5#7: $state;
  var SL#_dryad_S9: $state;
  var stmtexpr4#6: $state;
  var SL#_dryad_S8: $state;
  var stmtexpr3#5: $ptr;
  var SL#list4: $ptr;
  var stmtexpr2#4: $state;
  var SL#_dryad_S7: $state;
  var stmtexpr1#3: $oset;
  var stmtexpr0#2: $state;
  var SL#_dryad_S6: $state;
  var L#tail: $ptr;
  var list_key#0: int where $in_range_i4(list_key#0);
  var loopState#0: $state;
  var stmtexpr8#22: $ptr;
  var SL#list3: $ptr;
  var stmtexpr7#21: $state;
  var SL#_dryad_S5: $state;
  var stmtexpr6#20: $state;
  var SL#_dryad_S4: $state;
  var stmtexpr5#19: $state;
  var SL#_dryad_S3: $state;
  var stmtexpr4#18: $state;
  var SL#_dryad_S2: $state;
  var stmtexpr3#17: $ptr;
  var SL#list0: $ptr;
  var stmtexpr2#16: $state;
  var SL#_dryad_S1: $state;
  var stmtexpr1#15: $oset;
  var stmtexpr0#14: $state;
  var SL#_dryad_S0: $state;
  var L#last: $ptr;
  var L#list_key: int where $in_range_i4(L#list_key);
  var SL#ALL_REACH: $oset;
  var L#new_list: $ptr;
  var stmtexpr1#24: $oset;
  var stmtexpr0#23: $oset;
  var SL#_dryad_G1: $oset;
  var SL#_dryad_G0: $oset;
  var local.list: $ptr;
  var #wrTime$3^3.3: int;
  var #stackframe: int;

// INV:PTR: P#list, L#new_list, L#last, local.list
// INV:INT: L#list_key

  anon7:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$3^3.3, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$3^3.3 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$3^3.3, (lambda #p: $ptr :: false));
    // assume true
    // assume @decreases_level_is(2147483647); 
    assume 2147483647 == $decreases_level;
    // struct s_node* local.list; 
    // local.list := list; 
    local.list := $phys_ptr_cast(P#list, ^s_node);
    // assume true
    //  --- Dryad annotated function --- 
    // _math \oset _dryad_G0; 
    // _math \oset _dryad_G1; 
    // _dryad_G0 := sll_reach(local.list); 
    call SL#_dryad_G0 := sll_reach($phys_ptr_cast(local.list, ^s_node));
    assume $full_stop_ext(#tok$4^0.0, $s);
    // _math \oset stmtexpr0#23; 
    // stmtexpr0#23 := _dryad_G0; 
    stmtexpr0#23 := SL#_dryad_G0;
    // _dryad_G1 := _dryad_G0; 
    SL#_dryad_G1 := SL#_dryad_G0;
    // _math \oset stmtexpr1#24; 
    // stmtexpr1#24 := _dryad_G1; 
    stmtexpr1#24 := SL#_dryad_G1;
    // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
    assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
    // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
    assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
    // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
    assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
    // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
    assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
    // struct s_node* new_list; 
    // _math \oset ALL_REACH; 
    // assume ==>(@_vcc_ptr_neq_null(local.list), &&(@_vcc_mutable(@state, local.list), @writes_check(local.list))); 
    assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> $mutable($s, $phys_ptr_cast(local.list, ^s_node)) && $top_writable($s, #wrTime$3^3.3, $phys_ptr_cast(local.list, ^s_node));
    // ALL_REACH := sll_reach(local.list); 
    call SL#ALL_REACH := sll_reach($phys_ptr_cast(local.list, ^s_node));
    assume $full_stop_ext(#tok$3^11.29, $s);
    // new_list := (struct s_node*)@null; 
    L#new_list := $phys_ptr_cast($null, ^s_node);
    // assert sll_lseg(new_list, new_list); 
    assert F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#new_list, ^s_node));
    // assume sll_lseg(new_list, new_list); 
    assume F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#new_list, ^s_node));
    // assert sll_lseg(local.list, local.list); 
    assert F#sll_lseg($s, $phys_ptr_cast(local.list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
    // assume sll_lseg(local.list, local.list); 
    assume F#sll_lseg($s, $phys_ptr_cast(local.list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
    // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
    assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
    // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_list_len_next(new_list), unchecked+(sll_list_len_next(*((new_list->next))), 1))); 
    assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#new_list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), 1);
    // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll(new_list), &&(sll(*((new_list->next))), unchecked!(@_vcc_oset_in(new_list, sll_reach(*((new_list->next)))))))); 
    assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))));
    // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_reach(new_list), @_vcc_oset_union(sll_reach(*((new_list->next))), @_vcc_oset_singleton(new_list)))); 
    assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
    assume true;
    // if (@_vcc_ptr_neq_null(local.list)) ...
    if ($non_null($phys_ptr_cast(local.list, ^s_node)))
    {
      anon4:
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_list_len_next(new_list), unchecked+(sll_list_len_next(*((new_list->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#new_list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll(new_list), &&(sll(*((new_list->next))), unchecked!(@_vcc_oset_in(new_list, sll_reach(*((new_list->next)))))))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_reach(new_list), @_vcc_oset_union(sll_reach(*((new_list->next))), @_vcc_oset_singleton(new_list)))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
        // int32_t list_key; 
        // struct s_node* last; 
        // last := (struct s_node*)@null; 
        L#last := $phys_ptr_cast($null, ^s_node);
        // assert sll_lseg(last, last); 
        assert F#sll_lseg($s, $phys_ptr_cast(L#last, ^s_node), $phys_ptr_cast(L#last, ^s_node));
        // assume sll_lseg(last, last); 
        assume F#sll_lseg($s, $phys_ptr_cast(L#last, ^s_node), $phys_ptr_cast(L#last, ^s_node));
        // assert sll_lseg(new_list, new_list); 
        assert F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#new_list, ^s_node));
        // assume sll_lseg(new_list, new_list); 
        assume F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#new_list, ^s_node));
        // assert sll_lseg(local.list, local.list); 
        assert F#sll_lseg($s, $phys_ptr_cast(local.list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
        // assume sll_lseg(local.list, local.list); 
        assume F#sll_lseg($s, $phys_ptr_cast(local.list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
        // _math \state _dryad_S0; 
        // _dryad_S0 := @_vcc_current_state(@state); 
        SL#_dryad_S0 := $current_state($s);
        // _math \state stmtexpr0#14; 
        // stmtexpr0#14 := _dryad_S0; 
        stmtexpr0#14 := SL#_dryad_S0;
        // new_list := _vcc_alloc(@_vcc_typeof((struct s_node*)@null)); 
        call L#new_list := $alloc(^s_node);
        assume $full_stop_ext(#tok$3^17.14, $s);
        // assume !(@_vcc_oset_in(new_list, @_vcc_oset_union(_dryad_G0, _dryad_G1))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), $oset_union(SL#_dryad_G0, SL#_dryad_G1));
        // _dryad_G1 := @_vcc_oset_union(_dryad_G0, @_vcc_oset_singleton(new_list)); 
        SL#_dryad_G1 := $oset_union(SL#_dryad_G0, $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
        // _math \oset stmtexpr1#15; 
        // stmtexpr1#15 := _dryad_G1; 
        stmtexpr1#15 := SL#_dryad_G1;
        // assume ==(glob_reach(), _dryad_G1); 
        assume F#glob_reach() == SL#_dryad_G1;
        // _math \state _dryad_S1; 
        // _dryad_S1 := @_vcc_current_state(@state); 
        SL#_dryad_S1 := $current_state($s);
        // _math \state stmtexpr2#16; 
        // stmtexpr2#16 := _dryad_S1; 
        stmtexpr2#16 := SL#_dryad_S1;
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_list_len_next(new_list), unchecked+(sll_list_len_next(*((new_list->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#new_list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll(new_list), &&(sll(*((new_list->next))), unchecked!(@_vcc_oset_in(new_list, sll_reach(*((new_list->next)))))))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_reach(new_list), @_vcc_oset_union(sll_reach(*((new_list->next))), @_vcc_oset_singleton(new_list)))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S0, sll_reach(last)))), ==(old(_dryad_S0, sll_keys(last)), old(_dryad_S1, sll_keys(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_keys(SL#_dryad_S0, $phys_ptr_cast(L#last, ^s_node)) == F#sll_keys(SL#_dryad_S1, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S0, sll_reach(last)))), ==(old(_dryad_S0, sll_list_len_next(last)), old(_dryad_S1, sll_list_len_next(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S0, $phys_ptr_cast(L#last, ^s_node)) == F#sll_list_len_next(SL#_dryad_S1, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S0, sll_reach(last)))), ==(old(_dryad_S0, sll(last)), old(_dryad_S1, sll(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll(SL#_dryad_S0, $phys_ptr_cast(L#last, ^s_node)) == F#sll(SL#_dryad_S1, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S0, sll_reach(last)))), ==(old(_dryad_S0, sll_reach(last)), old(_dryad_S1, sll_reach(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(L#last, ^s_node)) == F#sll_reach(SL#_dryad_S1, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S0, sll_reach(local.list)))), ==(old(_dryad_S0, sll_keys(local.list)), old(_dryad_S1, sll_keys(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_keys(SL#_dryad_S0, $phys_ptr_cast(local.list, ^s_node)) == F#sll_keys(SL#_dryad_S1, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S0, sll_reach(local.list)))), ==(old(_dryad_S0, sll_list_len_next(local.list)), old(_dryad_S1, sll_list_len_next(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S0, $phys_ptr_cast(local.list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S1, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S0, sll_reach(local.list)))), ==(old(_dryad_S0, sll(local.list)), old(_dryad_S1, sll(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll(SL#_dryad_S0, $phys_ptr_cast(local.list, ^s_node)) == F#sll(SL#_dryad_S1, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S0, sll_reach(local.list)))), ==(old(_dryad_S0, sll_reach(local.list)), old(_dryad_S1, sll_reach(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(local.list, ^s_node)) == F#sll_reach(SL#_dryad_S1, $phys_ptr_cast(local.list, ^s_node));
        // assume @_vcc_ptr_neq_null(new_list); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node));
        // assume unchecked!(@_vcc_oset_in(new_list, ALL_REACH)); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), SL#ALL_REACH);
        // ALL_REACH := @_vcc_oset_union(ALL_REACH, @_vcc_oset_singleton(new_list)); 
        SL#ALL_REACH := $oset_union(SL#ALL_REACH, $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
        // struct s_node* list0; 
        // list0 := local.list; 
        SL#list0 := $phys_ptr_cast(local.list, ^s_node);
        // struct s_node* stmtexpr3#17; 
        // stmtexpr3#17 := list0; 
        stmtexpr3#17 := $phys_ptr_cast(SL#list0, ^s_node);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // assert @reads_check_normal((local.list->key)); 
        assert $thread_local($s, $phys_ptr_cast(local.list, ^s_node));
        // list_key := *((local.list->key)); 
        L#list_key := $rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // _math \state _dryad_S2; 
        // _dryad_S2 := @_vcc_current_state(@state); 
        SL#_dryad_S2 := $current_state($s);
        // _math \state stmtexpr4#18; 
        // stmtexpr4#18 := _dryad_S2; 
        stmtexpr4#18 := SL#_dryad_S2;
        // assert @prim_writes_check((new_list->key)); 
        assert $writable_prim($s, #wrTime$3^3.3, $dot($phys_ptr_cast(L#new_list, ^s_node), s_node.key));
        // *(new_list->key) := list_key; 
        call $write_int(s_node.key, $phys_ptr_cast(L#new_list, ^s_node), L#list_key);
        assume $full_stop_ext(#tok$3^23.3, $s);
        // _math \state _dryad_S3; 
        // _dryad_S3 := @_vcc_current_state(@state); 
        SL#_dryad_S3 := $current_state($s);
        // _math \state stmtexpr5#19; 
        // stmtexpr5#19 := _dryad_S3; 
        stmtexpr5#19 := SL#_dryad_S3;
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(*((new_list->next)))))), ==(old(_dryad_S2, sll_keys(*((new_list->next)))), old(_dryad_S3, sll_keys(*((new_list->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))) ==> F#sll_keys(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) == F#sll_keys(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(*((new_list->next)))))), ==(old(_dryad_S2, sll_list_len_next(*((new_list->next)))), old(_dryad_S3, sll_list_len_next(*((new_list->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(*((new_list->next)))))), ==(old(_dryad_S2, sll(*((new_list->next)))), old(_dryad_S3, sll(*((new_list->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))) ==> F#sll(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) == F#sll(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(*((new_list->next)))))), ==(old(_dryad_S2, sll_reach(*((new_list->next)))), old(_dryad_S3, sll_reach(*((new_list->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))) ==> F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) == F#sll_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node));
        // assume ==(old(_dryad_S2, sll_list_len_next(list0)), old(_dryad_S3, sll_list_len_next(list0))); 
        assume F#sll_list_len_next(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==(old(_dryad_S2, sll(list0)), old(_dryad_S3, sll(list0))); 
        assume F#sll(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==(old(_dryad_S2, sll_reach(list0)), old(_dryad_S3, sll_reach(list0))); 
        assume F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==(old(_dryad_S2, sll_list_len_next(last)), old(_dryad_S3, sll_list_len_next(last))); 
        assume F#sll_list_len_next(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $phys_ptr_cast(L#last, ^s_node));
        // assume ==(old(_dryad_S2, sll(last)), old(_dryad_S3, sll(last))); 
        assume F#sll(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(L#last, ^s_node));
        // assume ==(old(_dryad_S2, sll_reach(last)), old(_dryad_S3, sll_reach(last))); 
        assume F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(L#last, ^s_node));
        // assume ==(old(_dryad_S2, sll_list_len_next(new_list)), old(_dryad_S3, sll_list_len_next(new_list))); 
        assume F#sll_list_len_next(SL#_dryad_S2, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $phys_ptr_cast(L#new_list, ^s_node));
        // assume ==(old(_dryad_S2, sll(new_list)), old(_dryad_S3, sll(new_list))); 
        assume F#sll(SL#_dryad_S2, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(L#new_list, ^s_node));
        // assume ==(old(_dryad_S2, sll_reach(new_list)), old(_dryad_S3, sll_reach(new_list))); 
        assume F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(L#new_list, ^s_node));
        // assume ==(old(_dryad_S2, sll_list_len_next(local.list)), old(_dryad_S3, sll_list_len_next(local.list))); 
        assume F#sll_list_len_next(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $phys_ptr_cast(local.list, ^s_node));
        // assume ==(old(_dryad_S2, sll(local.list)), old(_dryad_S3, sll(local.list))); 
        assume F#sll(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(local.list, ^s_node));
        // assume ==(old(_dryad_S2, sll_reach(local.list)), old(_dryad_S3, sll_reach(local.list))); 
        assume F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(list0)))), ==(old(_dryad_S2, sll_keys(list0)), old(_dryad_S3, sll_keys(list0)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_keys(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_keys(SL#_dryad_S3, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(list0)))), ==(old(_dryad_S2, sll_list_len_next(list0)), old(_dryad_S3, sll_list_len_next(list0)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(list0)))), ==(old(_dryad_S2, sll(list0)), old(_dryad_S3, sll(list0)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(list0)))), ==(old(_dryad_S2, sll_reach(list0)), old(_dryad_S3, sll_reach(list0)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(last)))), ==(old(_dryad_S2, sll_keys(last)), old(_dryad_S3, sll_keys(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_keys(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node)) == F#sll_keys(SL#_dryad_S3, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(last)))), ==(old(_dryad_S2, sll_list_len_next(last)), old(_dryad_S3, sll_list_len_next(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(last)))), ==(old(_dryad_S2, sll(last)), old(_dryad_S3, sll(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(last)))), ==(old(_dryad_S2, sll_reach(last)), old(_dryad_S3, sll_reach(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(L#last, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(local.list)))), ==(old(_dryad_S2, sll_keys(local.list)), old(_dryad_S3, sll_keys(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_keys(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node)) == F#sll_keys(SL#_dryad_S3, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(local.list)))), ==(old(_dryad_S2, sll_list_len_next(local.list)), old(_dryad_S3, sll_list_len_next(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(local.list)))), ==(old(_dryad_S2, sll(local.list)), old(_dryad_S3, sll(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S2, sll_reach(local.list)))), ==(old(_dryad_S2, sll_reach(local.list)), old(_dryad_S3, sll_reach(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(local.list, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, list0)), ==(*((list0->key)), old(_dryad_S2, *((list0->key))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(SL#list0, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node)) == $rd_inv(SL#_dryad_S2, s_node.key, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, list0)), @_vcc_ptr_eq_pure(*((list0->next)), old(_dryad_S2, *((list0->next))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(SL#list0, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node);
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, last)), ==(*((last->key)), old(_dryad_S2, *((last->key))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(L#last, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node)) == $rd_inv(SL#_dryad_S2, s_node.key, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, last)), @_vcc_ptr_eq_pure(*((last->next)), old(_dryad_S2, *((last->next))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(L#last, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node);
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, local.list)), ==(*((local.list->key)), old(_dryad_S2, *((local.list->key))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(local.list, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node)) == $rd_inv(SL#_dryad_S2, s_node.key, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, local.list)), @_vcc_ptr_eq_pure(*((local.list->next)), old(_dryad_S2, *((local.list->next))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(local.list, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node);
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_keys(list0), @_vcc_intset_union(sll_keys(*((list0->next))), @_vcc_intset_singleton(*((list0->key)))))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list0, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_list_len_next(list0), unchecked+(sll_list_len_next(*((list0->next))), 1))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list0, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll(list0), &&(sll(*((list0->next))), unchecked!(@_vcc_oset_in(list0, sll_reach(*((list0->next)))))))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list0, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list0, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_reach(list0), @_vcc_oset_union(sll_reach(*((list0->next))), @_vcc_oset_singleton(list0)))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list0, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list0, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
        // _math \state _dryad_S4; 
        // _dryad_S4 := @_vcc_current_state(@state); 
        SL#_dryad_S4 := $current_state($s);
        // _math \state stmtexpr6#20; 
        // stmtexpr6#20 := _dryad_S4; 
        stmtexpr6#20 := SL#_dryad_S4;
        // assert @prim_writes_check((new_list->next)); 
        assert $writable_prim($s, #wrTime$3^3.3, $dot($phys_ptr_cast(L#new_list, ^s_node), s_node.next));
        // *(new_list->next) := (struct s_node*)@null; 
        call $write_int(s_node.next, $phys_ptr_cast(L#new_list, ^s_node), $ptr_to_int($phys_ptr_cast($null, ^s_node)));
        assume $full_stop_ext(#tok$3^24.3, $s);
        // _math \state _dryad_S5; 
        // _dryad_S5 := @_vcc_current_state(@state); 
        SL#_dryad_S5 := $current_state($s);
        // _math \state stmtexpr7#21; 
        // stmtexpr7#21 := _dryad_S5; 
        stmtexpr7#21 := SL#_dryad_S5;
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(list0)))), ==(old(_dryad_S4, sll_keys(list0)), old(_dryad_S5, sll_keys(list0)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_keys(SL#_dryad_S4, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_keys(SL#_dryad_S5, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(list0)))), ==(old(_dryad_S4, sll_list_len_next(list0)), old(_dryad_S5, sll_list_len_next(list0)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S4, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_list_len_next(SL#_dryad_S5, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(list0)))), ==(old(_dryad_S4, sll(list0)), old(_dryad_S5, sll(list0)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll(SL#_dryad_S4, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll(SL#_dryad_S5, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(list0)))), ==(old(_dryad_S4, sll_reach(list0)), old(_dryad_S5, sll_reach(list0)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_reach(SL#_dryad_S5, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(last)))), ==(old(_dryad_S4, sll_keys(last)), old(_dryad_S5, sll_keys(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_keys(SL#_dryad_S4, $phys_ptr_cast(L#last, ^s_node)) == F#sll_keys(SL#_dryad_S5, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(last)))), ==(old(_dryad_S4, sll_list_len_next(last)), old(_dryad_S5, sll_list_len_next(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S4, $phys_ptr_cast(L#last, ^s_node)) == F#sll_list_len_next(SL#_dryad_S5, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(last)))), ==(old(_dryad_S4, sll(last)), old(_dryad_S5, sll(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll(SL#_dryad_S4, $phys_ptr_cast(L#last, ^s_node)) == F#sll(SL#_dryad_S5, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(last)))), ==(old(_dryad_S4, sll_reach(last)), old(_dryad_S5, sll_reach(last)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(L#last, ^s_node)) == F#sll_reach(SL#_dryad_S5, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(local.list)))), ==(old(_dryad_S4, sll_keys(local.list)), old(_dryad_S5, sll_keys(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_keys(SL#_dryad_S4, $phys_ptr_cast(local.list, ^s_node)) == F#sll_keys(SL#_dryad_S5, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(local.list)))), ==(old(_dryad_S4, sll_list_len_next(local.list)), old(_dryad_S5, sll_list_len_next(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S4, $phys_ptr_cast(local.list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S5, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(local.list)))), ==(old(_dryad_S4, sll(local.list)), old(_dryad_S5, sll(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll(SL#_dryad_S4, $phys_ptr_cast(local.list, ^s_node)) == F#sll(SL#_dryad_S5, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(new_list, old(_dryad_S4, sll_reach(local.list)))), ==(old(_dryad_S4, sll_reach(local.list)), old(_dryad_S5, sll_reach(local.list)))); 
        assume !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(local.list, ^s_node)) == F#sll_reach(SL#_dryad_S5, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, list0)), ==(*((list0->key)), old(_dryad_S4, *((list0->key))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(SL#list0, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node)) == $rd_inv(SL#_dryad_S4, s_node.key, $phys_ptr_cast(SL#list0, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, list0)), @_vcc_ptr_eq_pure(*((list0->next)), old(_dryad_S4, *((list0->next))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(SL#list0, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S4, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node);
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, last)), ==(*((last->key)), old(_dryad_S4, *((last->key))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(L#last, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node)) == $rd_inv(SL#_dryad_S4, s_node.key, $phys_ptr_cast(L#last, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, last)), @_vcc_ptr_eq_pure(*((last->next)), old(_dryad_S4, *((last->next))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(L#last, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S4, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node);
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, local.list)), ==(*((local.list->key)), old(_dryad_S4, *((local.list->key))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(local.list, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node)) == $rd_inv(SL#_dryad_S4, s_node.key, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(new_list, local.list)), @_vcc_ptr_eq_pure(*((local.list->next)), old(_dryad_S4, *((local.list->next))))); 
        assume !($phys_ptr_cast(L#new_list, ^s_node) == $phys_ptr_cast(local.list, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S4, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node);
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_keys(list0), @_vcc_intset_union(sll_keys(*((list0->next))), @_vcc_intset_singleton(*((list0->key)))))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list0, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_list_len_next(list0), unchecked+(sll_list_len_next(*((list0->next))), 1))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list0, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll(list0), &&(sll(*((list0->next))), unchecked!(@_vcc_oset_in(list0, sll_reach(*((list0->next)))))))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list0, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list0, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_reach(list0), @_vcc_oset_union(sll_reach(*((list0->next))), @_vcc_oset_singleton(list0)))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list0, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list0, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_list_len_next(new_list), unchecked+(sll_list_len_next(*((new_list->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#new_list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll(new_list), &&(sll(*((new_list->next))), unchecked!(@_vcc_oset_in(new_list, sll_reach(*((new_list->next)))))))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_reach(new_list), @_vcc_oset_union(sll_reach(*((new_list->next))), @_vcc_oset_singleton(new_list)))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
        // last := new_list; 
        L#last := $phys_ptr_cast(L#new_list, ^s_node);
        // assert sll_lseg(list0, list0); 
        assert F#sll_lseg($s, $phys_ptr_cast(SL#list0, ^s_node), $phys_ptr_cast(SL#list0, ^s_node));
        // assume sll_lseg(list0, list0); 
        assume F#sll_lseg($s, $phys_ptr_cast(SL#list0, ^s_node), $phys_ptr_cast(SL#list0, ^s_node));
        // assert sll_lseg(last, last); 
        assert F#sll_lseg($s, $phys_ptr_cast(L#last, ^s_node), $phys_ptr_cast(L#last, ^s_node));
        // assume sll_lseg(last, last); 
        assume F#sll_lseg($s, $phys_ptr_cast(L#last, ^s_node), $phys_ptr_cast(L#last, ^s_node));
        // assert sll_lseg(new_list, new_list); 
        assert F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#new_list, ^s_node));
        // assume sll_lseg(new_list, new_list); 
        assume F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#new_list, ^s_node));
        // assert sll_lseg(local.list, local.list); 
        assert F#sll_lseg($s, $phys_ptr_cast(local.list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
        // assume sll_lseg(local.list, local.list); 
        assume F#sll_lseg($s, $phys_ptr_cast(local.list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(@_vcc_ptr_neq_null(local.list), &&(@_vcc_mutable(@state, local.list), @writes_check(local.list))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> $mutable($s, $phys_ptr_cast(local.list, ^s_node)) && $top_writable($s, #wrTime$3^3.3, $phys_ptr_cast(local.list, ^s_node));
        // struct s_node* list3; 
        // list3 := local.list; 
        SL#list3 := $phys_ptr_cast(local.list, ^s_node);
        // struct s_node* stmtexpr8#22; 
        // stmtexpr8#22 := list3; 
        stmtexpr8#22 := $phys_ptr_cast(SL#list3, ^s_node);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
        // assume ==>(&&(@_vcc_ptr_neq_null(local.list), @_vcc_ptr_neq_pure(local.list, *((local.list->next)))), ==(sll_lseg(local.list, *((local.list->next))), &&(sll_lseg(*((local.list->next)), *((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_lseg_reach(*((local.list->next)), *((local.list->next)))))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) && $phys_ptr_cast(local.list, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(local.list, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
        // assume ==>(&&(@_vcc_ptr_neq_null(local.list), @_vcc_ptr_neq_pure(local.list, *((local.list->next)))), ==(sll_lseg_reach(local.list, *((local.list->next))), @_vcc_oset_union(sll_lseg_reach(*((local.list->next)), *((local.list->next))), @_vcc_oset_singleton(local.list)))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) && $phys_ptr_cast(local.list, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(local.list, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
        // assume ==>(&&(@_vcc_ptr_neq_null(local.list), @_vcc_ptr_neq_pure(local.list, *((local.list->next)))), ==(sll_lseg_keys(local.list, *((local.list->next))), @_vcc_intset_union(sll_lseg_keys(*((local.list->next)), *((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) && $phys_ptr_cast(local.list, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(local.list, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // assume ==>(&&(@_vcc_ptr_neq_null(local.list), @_vcc_ptr_neq_pure(local.list, *((local.list->next)))), ==(sll_lseg_len_next(local.list, *((local.list->next))), unchecked+(sll_lseg_len_next(*((local.list->next)), *((local.list->next))), 1))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) && $phys_ptr_cast(local.list, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(local.list, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
        // assert @reads_check_normal((local.list->next)); 
        assert $thread_local($s, $phys_ptr_cast(local.list, ^s_node));
        // local.list := *((local.list->next)); 
        local.list := $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(local.list), &&(@_vcc_mutable(@state, local.list), @writes_check(local.list))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> $mutable($s, $phys_ptr_cast(local.list, ^s_node)) && $top_writable($s, #wrTime$3^3.3, $phys_ptr_cast(local.list, ^s_node));
        // assume ==>(@_vcc_ptr_neq_null(last), &&(@_vcc_mutable(@state, last), @writes_check(last))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> $mutable($s, $phys_ptr_cast(L#last, ^s_node)) && $top_writable($s, #wrTime$3^3.3, $phys_ptr_cast(L#last, ^s_node));
        loopState#0 := $s;
        assume true;
        while (true)
// INV:BEGIN
          invariant F#sll($s, $phys_ptr_cast(P#list, ^s_node));
          invariant F#sll($s, $phys_ptr_cast(L#new_list, ^s_node));
          invariant $oset_disjoint(F#sll_reach($s, $phys_ptr_cast(P#list, ^s_node)), F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)));
          invariant F#sll($s, $phys_ptr_cast(local.list, ^s_node));
          invariant F#sll($s, $phys_ptr_cast(L#new_list, ^s_node));
          invariant $oset_disjoint(F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)), F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)));
          invariant F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
          invariant $oset_disjoint(F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)), F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)));
          invariant F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
          invariant $oset_disjoint(F#sll_lseg_reach($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)), F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)));
          invariant $oset_disjoint(F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)), F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)));
          invariant $oset_disjoint(F#sll_reach($s, $phys_ptr_cast(P#list, ^s_node)), F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)));
          invariant $is_null($rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node));
          invariant F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
// INV:END
          invariant $oset_subset(F#sll_reach($s, $phys_ptr_cast(P#list, ^s_node)), SL#ALL_REACH);
          invariant $oset_subset(F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)), SL#ALL_REACH);
          invariant $oset_subset(F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)), SL#ALL_REACH);
          invariant $non_null($phys_ptr_cast(local.list, ^s_node)) ==> $mutable($s, $phys_ptr_cast(local.list, ^s_node));
          invariant $non_null($phys_ptr_cast(local.list, ^s_node)) ==> $top_writable($s, #wrTime$3^3.3, $phys_ptr_cast(local.list, ^s_node));
          invariant $non_null($phys_ptr_cast(L#last, ^s_node));
          invariant $non_null($phys_ptr_cast(L#last, ^s_node)) ==> $mutable($s, $phys_ptr_cast(L#last, ^s_node));
          invariant $non_null($phys_ptr_cast(L#last, ^s_node)) ==> $top_writable($s, #wrTime$3^3.3, $phys_ptr_cast(L#last, ^s_node));
        {
          anon3:
            assume $writes_nothing(old($s), $s);
            assume $timestamp_post(loopState#0, $s);
            assume $full_stop_ext(#tok$3^33.3, $s);
            // assume @_vcc_meta_eq(old(@prestate, @state), @state); 
            assume $meta_eq(loopState#0, $s);
            assume true;
            // if (@_vcc_ptr_neq_null(local.list)) ...
            if ($non_null($phys_ptr_cast(local.list, ^s_node)))
            {
              anon1:
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_keys(list3), @_vcc_intset_union(sll_keys(*((list3->next))), @_vcc_intset_singleton(*((list3->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list3, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list3, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_list_len_next(list3), unchecked+(sll_list_len_next(*((list3->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list3, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll(list3), &&(sll(*((list3->next))), unchecked!(@_vcc_oset_in(list3, sll_reach(*((list3->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list3, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list3, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_reach(list3), @_vcc_oset_union(sll_reach(*((list3->next))), @_vcc_oset_singleton(list3)))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list3, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list3, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_keys(list0), @_vcc_intset_union(sll_keys(*((list0->next))), @_vcc_intset_singleton(*((list0->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list0, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_list_len_next(list0), unchecked+(sll_list_len_next(*((list0->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list0, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll(list0), &&(sll(*((list0->next))), unchecked!(@_vcc_oset_in(list0, sll_reach(*((list0->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list0, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list0, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_reach(list0), @_vcc_oset_union(sll_reach(*((list0->next))), @_vcc_oset_singleton(list0)))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list0, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list0, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_list_len_next(new_list), unchecked+(sll_list_len_next(*((new_list->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#new_list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll(new_list), &&(sll(*((new_list->next))), unchecked!(@_vcc_oset_in(new_list, sll_reach(*((new_list->next)))))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_reach(new_list), @_vcc_oset_union(sll_reach(*((new_list->next))), @_vcc_oset_singleton(new_list)))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg(new_list, last), &&(sll_lseg(*((new_list->next)), last), unchecked!(@_vcc_oset_in(new_list, sll_lseg_reach(*((new_list->next)), last)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_reach(new_list, last), @_vcc_oset_union(sll_lseg_reach(*((new_list->next)), last), @_vcc_oset_singleton(new_list)))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_keys(new_list, last), @_vcc_intset_union(sll_lseg_keys(*((new_list->next)), last), @_vcc_intset_singleton(*((new_list->key)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_len_next(new_list, last), unchecked+(sll_lseg_len_next(*((new_list->next)), last), 1))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), 1);
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg(list, local.list), &&(sll_lseg(*((list->next)), local.list), unchecked!(@_vcc_oset_in(list, sll_lseg_reach(*((list->next)), local.list)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)) && !$oset_in($phys_ptr_cast(P#list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_reach(list, local.list), @_vcc_oset_union(sll_lseg_reach(*((list->next)), local.list), @_vcc_oset_singleton(list)))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $oset_singleton($phys_ptr_cast(P#list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_keys(list, local.list), @_vcc_intset_union(sll_lseg_keys(*((list->next)), local.list), @_vcc_intset_singleton(*((list->key)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_len_next(list, local.list), unchecked+(sll_lseg_len_next(*((list->next)), local.list), 1))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), 1);
                // int32_t list_key#0; 
                // struct s_node* tail; 
                // _math \state _dryad_S6; 
                // _dryad_S6 := @_vcc_current_state(@state); 
                SL#_dryad_S6 := $current_state($s);
                // _math \state stmtexpr0#2; 
                // stmtexpr0#2 := _dryad_S6; 
                stmtexpr0#2 := SL#_dryad_S6;
                // tail := _vcc_alloc(@_vcc_typeof((struct s_node*)@null)); 
                call L#tail := $alloc(^s_node);
                assume $full_stop_ext(#tok$3^49.18, $s);
                // assume !(@_vcc_oset_in(tail, @_vcc_oset_union(_dryad_G0, _dryad_G1))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), $oset_union(SL#_dryad_G0, SL#_dryad_G1));
                // _dryad_G1 := @_vcc_oset_union(_dryad_G0, @_vcc_oset_singleton(tail)); 
                SL#_dryad_G1 := $oset_union(SL#_dryad_G0, $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
                // _math \oset stmtexpr1#3; 
                // stmtexpr1#3 := _dryad_G1; 
                stmtexpr1#3 := SL#_dryad_G1;
                // assume ==(glob_reach(), _dryad_G1); 
                assume F#glob_reach() == SL#_dryad_G1;
                // _math \state _dryad_S7; 
                // _dryad_S7 := @_vcc_current_state(@state); 
                SL#_dryad_S7 := $current_state($s);
                // _math \state stmtexpr2#4; 
                // stmtexpr2#4 := _dryad_S7; 
                stmtexpr2#4 := SL#_dryad_S7;
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_keys(tail), @_vcc_intset_union(sll_keys(*((tail->next))), @_vcc_intset_singleton(*((tail->key)))))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tail, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_list_len_next(tail), unchecked+(sll_list_len_next(*((tail->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#tail, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll(tail), &&(sll(*((tail->next))), unchecked!(@_vcc_oset_in(tail, sll_reach(*((tail->next)))))))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_reach(tail), @_vcc_oset_union(sll_reach(*((tail->next))), @_vcc_oset_singleton(tail)))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tail, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_keys(list3), @_vcc_intset_union(sll_keys(*((list3->next))), @_vcc_intset_singleton(*((list3->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list3, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list3, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_list_len_next(list3), unchecked+(sll_list_len_next(*((list3->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list3, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll(list3), &&(sll(*((list3->next))), unchecked!(@_vcc_oset_in(list3, sll_reach(*((list3->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list3, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list3, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_reach(list3), @_vcc_oset_union(sll_reach(*((list3->next))), @_vcc_oset_singleton(list3)))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list3, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list3, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_keys(list0), @_vcc_intset_union(sll_keys(*((list0->next))), @_vcc_intset_singleton(*((list0->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list0, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_list_len_next(list0), unchecked+(sll_list_len_next(*((list0->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list0, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll(list0), &&(sll(*((list0->next))), unchecked!(@_vcc_oset_in(list0, sll_reach(*((list0->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list0, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list0, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_reach(list0), @_vcc_oset_union(sll_reach(*((list0->next))), @_vcc_oset_singleton(list0)))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list0, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list0, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_list_len_next(new_list), unchecked+(sll_list_len_next(*((new_list->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#new_list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll(new_list), &&(sll(*((new_list->next))), unchecked!(@_vcc_oset_in(new_list, sll_reach(*((new_list->next)))))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_reach(new_list), @_vcc_oset_union(sll_reach(*((new_list->next))), @_vcc_oset_singleton(new_list)))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg(new_list, last), &&(sll_lseg(*((new_list->next)), last), unchecked!(@_vcc_oset_in(new_list, sll_lseg_reach(*((new_list->next)), last)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_reach(new_list, last), @_vcc_oset_union(sll_lseg_reach(*((new_list->next)), last), @_vcc_oset_singleton(new_list)))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_keys(new_list, last), @_vcc_intset_union(sll_lseg_keys(*((new_list->next)), last), @_vcc_intset_singleton(*((new_list->key)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_len_next(new_list, last), unchecked+(sll_lseg_len_next(*((new_list->next)), last), 1))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), 1);
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg(list, local.list), &&(sll_lseg(*((list->next)), local.list), unchecked!(@_vcc_oset_in(list, sll_lseg_reach(*((list->next)), local.list)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)) && !$oset_in($phys_ptr_cast(P#list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_reach(list, local.list), @_vcc_oset_union(sll_lseg_reach(*((list->next)), local.list), @_vcc_oset_singleton(list)))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $oset_singleton($phys_ptr_cast(P#list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_keys(list, local.list), @_vcc_intset_union(sll_lseg_keys(*((list->next)), local.list), @_vcc_intset_singleton(*((list->key)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_len_next(list, local.list), unchecked+(sll_lseg_len_next(*((list->next)), local.list), 1))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), 1);
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(list3)))), ==(old(_dryad_S6, sll_keys(list3)), old(_dryad_S7, sll_keys(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_keys(SL#_dryad_S6, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_keys(SL#_dryad_S7, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(list3)))), ==(old(_dryad_S6, sll_list_len_next(list3)), old(_dryad_S7, sll_list_len_next(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S6, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_list_len_next(SL#_dryad_S7, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(list3)))), ==(old(_dryad_S6, sll(list3)), old(_dryad_S7, sll(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll(SL#_dryad_S6, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll(SL#_dryad_S7, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(list3)))), ==(old(_dryad_S6, sll_reach(list3)), old(_dryad_S7, sll_reach(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_reach(SL#_dryad_S7, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(list0)))), ==(old(_dryad_S6, sll_keys(list0)), old(_dryad_S7, sll_keys(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_keys(SL#_dryad_S6, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_keys(SL#_dryad_S7, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(list0)))), ==(old(_dryad_S6, sll_list_len_next(list0)), old(_dryad_S7, sll_list_len_next(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S6, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_list_len_next(SL#_dryad_S7, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(list0)))), ==(old(_dryad_S6, sll(list0)), old(_dryad_S7, sll(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll(SL#_dryad_S6, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll(SL#_dryad_S7, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(list0)))), ==(old(_dryad_S6, sll_reach(list0)), old(_dryad_S7, sll_reach(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_reach(SL#_dryad_S7, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(last)))), ==(old(_dryad_S6, sll_keys(last)), old(_dryad_S7, sll_keys(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_keys(SL#_dryad_S6, $phys_ptr_cast(L#last, ^s_node)) == F#sll_keys(SL#_dryad_S7, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(last)))), ==(old(_dryad_S6, sll_list_len_next(last)), old(_dryad_S7, sll_list_len_next(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S6, $phys_ptr_cast(L#last, ^s_node)) == F#sll_list_len_next(SL#_dryad_S7, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(last)))), ==(old(_dryad_S6, sll(last)), old(_dryad_S7, sll(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll(SL#_dryad_S6, $phys_ptr_cast(L#last, ^s_node)) == F#sll(SL#_dryad_S7, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(last)))), ==(old(_dryad_S6, sll_reach(last)), old(_dryad_S7, sll_reach(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(L#last, ^s_node)) == F#sll_reach(SL#_dryad_S7, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(new_list)))), ==(old(_dryad_S6, sll_keys(new_list)), old(_dryad_S7, sll_keys(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_keys(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_keys(SL#_dryad_S7, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(new_list)))), ==(old(_dryad_S6, sll_list_len_next(new_list)), old(_dryad_S7, sll_list_len_next(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S7, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(new_list)))), ==(old(_dryad_S6, sll(new_list)), old(_dryad_S7, sll(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll(SL#_dryad_S7, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(new_list)))), ==(old(_dryad_S6, sll_reach(new_list)), old(_dryad_S7, sll_reach(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_reach(SL#_dryad_S7, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(local.list)))), ==(old(_dryad_S6, sll_keys(local.list)), old(_dryad_S7, sll_keys(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_keys(SL#_dryad_S6, $phys_ptr_cast(local.list, ^s_node)) == F#sll_keys(SL#_dryad_S7, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(local.list)))), ==(old(_dryad_S6, sll_list_len_next(local.list)), old(_dryad_S7, sll_list_len_next(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S6, $phys_ptr_cast(local.list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S7, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(local.list)))), ==(old(_dryad_S6, sll(local.list)), old(_dryad_S7, sll(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll(SL#_dryad_S6, $phys_ptr_cast(local.list, ^s_node)) == F#sll(SL#_dryad_S7, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_reach(local.list)))), ==(old(_dryad_S6, sll_reach(local.list)), old(_dryad_S7, sll_reach(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_reach(SL#_dryad_S6, $phys_ptr_cast(local.list, ^s_node)) == F#sll_reach(SL#_dryad_S7, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S6, sll_lseg(new_list, last)), old(_dryad_S7, sll_lseg(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg(SL#_dryad_S7, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S6, sll_lseg_reach(new_list, last)), old(_dryad_S7, sll_lseg_reach(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S7, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S6, sll_lseg_keys(new_list, last)), old(_dryad_S7, sll_lseg_keys(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S7, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S6, sll_lseg_len_next(new_list, last)), old(_dryad_S7, sll_lseg_len_next(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S6, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S7, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S6, sll_lseg(list, local.list)), old(_dryad_S7, sll_lseg(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S6, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg(SL#_dryad_S6, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg(SL#_dryad_S7, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S6, sll_lseg_reach(list, local.list)), old(_dryad_S7, sll_lseg_reach(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S6, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S6, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S7, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S6, sll_lseg_keys(list, local.list)), old(_dryad_S7, sll_lseg_keys(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S6, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S6, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S7, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S6, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S6, sll_lseg_len_next(list, local.list)), old(_dryad_S7, sll_lseg_len_next(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S6, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S6, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S7, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume @_vcc_ptr_neq_null(tail); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node));
                // assume unchecked!(@_vcc_oset_in(tail, ALL_REACH)); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), SL#ALL_REACH);
                // ALL_REACH := @_vcc_oset_union(ALL_REACH, @_vcc_oset_singleton(tail)); 
                SL#ALL_REACH := $oset_union(SL#ALL_REACH, $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
                // struct s_node* list4; 
                // list4 := local.list; 
                SL#list4 := $phys_ptr_cast(local.list, ^s_node);
                // struct s_node* stmtexpr3#5; 
                // stmtexpr3#5 := list4; 
                stmtexpr3#5 := $phys_ptr_cast(SL#list4, ^s_node);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // assert @reads_check_normal((local.list->key)); 
                assert $thread_local($s, $phys_ptr_cast(local.list, ^s_node));
                // list_key#0 := *((local.list->key)); 
                list_key#0 := $rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // _math \state _dryad_S8; 
                // _dryad_S8 := @_vcc_current_state(@state); 
                SL#_dryad_S8 := $current_state($s);
                // _math \state stmtexpr4#6; 
                // stmtexpr4#6 := _dryad_S8; 
                stmtexpr4#6 := SL#_dryad_S8;
                // assert @prim_writes_check((tail->key)); 
                assert $writable_prim($s, #wrTime$3^3.3, $dot($phys_ptr_cast(L#tail, ^s_node), s_node.key));
                // *(tail->key) := list_key#0; 
                call $write_int(s_node.key, $phys_ptr_cast(L#tail, ^s_node), list_key#0);
                assume $full_stop_ext(#tok$3^55.5, $s);
                // _math \state _dryad_S9; 
                // _dryad_S9 := @_vcc_current_state(@state); 
                SL#_dryad_S9 := $current_state($s);
                // _math \state stmtexpr5#7; 
                // stmtexpr5#7 := _dryad_S9; 
                stmtexpr5#7 := SL#_dryad_S9;
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(*((tail->next)))))), ==(old(_dryad_S8, sll_keys(*((tail->next)))), old(_dryad_S9, sll_keys(*((tail->next)))))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#sll_keys(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#sll_keys(SL#_dryad_S9, $rd_phys_ptr(SL#_dryad_S9, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(*((tail->next)))))), ==(old(_dryad_S8, sll_list_len_next(*((tail->next)))), old(_dryad_S9, sll_list_len_next(*((tail->next)))))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $rd_phys_ptr(SL#_dryad_S9, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(*((tail->next)))))), ==(old(_dryad_S8, sll(*((tail->next)))), old(_dryad_S9, sll(*((tail->next)))))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#sll(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#sll(SL#_dryad_S9, $rd_phys_ptr(SL#_dryad_S9, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(*((tail->next)))))), ==(old(_dryad_S8, sll_reach(*((tail->next)))), old(_dryad_S9, sll_reach(*((tail->next)))))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#sll_reach(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#sll_reach(SL#_dryad_S9, $rd_phys_ptr(SL#_dryad_S9, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
                // assume ==(old(_dryad_S8, sll_list_len_next(list4)), old(_dryad_S9, sll_list_len_next(list4))); 
                assume F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==(old(_dryad_S8, sll(list4)), old(_dryad_S9, sll(list4))); 
                assume F#sll(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==(old(_dryad_S8, sll_reach(list4)), old(_dryad_S9, sll_reach(list4))); 
                assume F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==(old(_dryad_S8, sll_list_len_next(tail)), old(_dryad_S9, sll_list_len_next(tail))); 
                assume F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(L#tail, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(L#tail, ^s_node));
                // assume ==(old(_dryad_S8, sll(tail)), old(_dryad_S9, sll(tail))); 
                assume F#sll(SL#_dryad_S8, $phys_ptr_cast(L#tail, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(L#tail, ^s_node));
                // assume ==(old(_dryad_S8, sll_reach(tail)), old(_dryad_S9, sll_reach(tail))); 
                assume F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#tail, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(L#tail, ^s_node));
                // assume ==(old(_dryad_S8, sll_list_len_next(list3)), old(_dryad_S9, sll_list_len_next(list3))); 
                assume F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==(old(_dryad_S8, sll(list3)), old(_dryad_S9, sll(list3))); 
                assume F#sll(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==(old(_dryad_S8, sll_reach(list3)), old(_dryad_S9, sll_reach(list3))); 
                assume F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==(old(_dryad_S8, sll_list_len_next(list0)), old(_dryad_S9, sll_list_len_next(list0))); 
                assume F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==(old(_dryad_S8, sll(list0)), old(_dryad_S9, sll(list0))); 
                assume F#sll(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==(old(_dryad_S8, sll_reach(list0)), old(_dryad_S9, sll_reach(list0))); 
                assume F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==(old(_dryad_S8, sll_list_len_next(last)), old(_dryad_S9, sll_list_len_next(last))); 
                assume F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(L#last, ^s_node));
                // assume ==(old(_dryad_S8, sll(last)), old(_dryad_S9, sll(last))); 
                assume F#sll(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(L#last, ^s_node));
                // assume ==(old(_dryad_S8, sll_reach(last)), old(_dryad_S9, sll_reach(last))); 
                assume F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(L#last, ^s_node));
                // assume ==(old(_dryad_S8, sll_list_len_next(new_list)), old(_dryad_S9, sll_list_len_next(new_list))); 
                assume F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==(old(_dryad_S8, sll(new_list)), old(_dryad_S9, sll(new_list))); 
                assume F#sll(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==(old(_dryad_S8, sll_reach(new_list)), old(_dryad_S9, sll_reach(new_list))); 
                assume F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==(old(_dryad_S8, sll_list_len_next(local.list)), old(_dryad_S9, sll_list_len_next(local.list))); 
                assume F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(local.list, ^s_node));
                // assume ==(old(_dryad_S8, sll(local.list)), old(_dryad_S9, sll(local.list))); 
                assume F#sll(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(local.list, ^s_node));
                // assume ==(old(_dryad_S8, sll_reach(local.list)), old(_dryad_S9, sll_reach(local.list))); 
                assume F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list4)))), ==(old(_dryad_S8, sll_keys(list4)), old(_dryad_S9, sll_keys(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll_keys(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_keys(SL#_dryad_S9, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list4)))), ==(old(_dryad_S8, sll_list_len_next(list4)), old(_dryad_S9, sll_list_len_next(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list4)))), ==(old(_dryad_S8, sll(list4)), old(_dryad_S9, sll(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list4)))), ==(old(_dryad_S8, sll_reach(list4)), old(_dryad_S9, sll_reach(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list3)))), ==(old(_dryad_S8, sll_keys(list3)), old(_dryad_S9, sll_keys(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_keys(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_keys(SL#_dryad_S9, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list3)))), ==(old(_dryad_S8, sll_list_len_next(list3)), old(_dryad_S9, sll_list_len_next(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list3)))), ==(old(_dryad_S8, sll(list3)), old(_dryad_S9, sll(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list3)))), ==(old(_dryad_S8, sll_reach(list3)), old(_dryad_S9, sll_reach(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list0)))), ==(old(_dryad_S8, sll_keys(list0)), old(_dryad_S9, sll_keys(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_keys(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_keys(SL#_dryad_S9, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list0)))), ==(old(_dryad_S8, sll_list_len_next(list0)), old(_dryad_S9, sll_list_len_next(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list0)))), ==(old(_dryad_S8, sll(list0)), old(_dryad_S9, sll(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(list0)))), ==(old(_dryad_S8, sll_reach(list0)), old(_dryad_S9, sll_reach(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(last)))), ==(old(_dryad_S8, sll_keys(last)), old(_dryad_S9, sll_keys(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_keys(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node)) == F#sll_keys(SL#_dryad_S9, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(last)))), ==(old(_dryad_S8, sll_list_len_next(last)), old(_dryad_S9, sll_list_len_next(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(last)))), ==(old(_dryad_S8, sll(last)), old(_dryad_S9, sll(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(last)))), ==(old(_dryad_S8, sll_reach(last)), old(_dryad_S9, sll_reach(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#last, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(new_list)))), ==(old(_dryad_S8, sll_keys(new_list)), old(_dryad_S9, sll_keys(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_keys(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_keys(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(new_list)))), ==(old(_dryad_S8, sll_list_len_next(new_list)), old(_dryad_S9, sll_list_len_next(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(new_list)))), ==(old(_dryad_S8, sll(new_list)), old(_dryad_S9, sll(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(new_list)))), ==(old(_dryad_S8, sll_reach(new_list)), old(_dryad_S9, sll_reach(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(local.list)))), ==(old(_dryad_S8, sll_keys(local.list)), old(_dryad_S9, sll_keys(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_keys(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node)) == F#sll_keys(SL#_dryad_S9, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(local.list)))), ==(old(_dryad_S8, sll_list_len_next(local.list)), old(_dryad_S9, sll_list_len_next(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S9, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(local.list)))), ==(old(_dryad_S8, sll(local.list)), old(_dryad_S9, sll(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node)) == F#sll(SL#_dryad_S9, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_reach(local.list)))), ==(old(_dryad_S8, sll_reach(local.list)), old(_dryad_S9, sll_reach(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_reach(SL#_dryad_S8, $phys_ptr_cast(local.list, ^s_node)) == F#sll_reach(SL#_dryad_S9, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S8, sll_lseg(new_list, last)), old(_dryad_S9, sll_lseg(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S8, sll_lseg_reach(new_list, last)), old(_dryad_S9, sll_lseg_reach(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S8, sll_lseg_keys(new_list, last)), old(_dryad_S9, sll_lseg_keys(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S8, sll_lseg_len_next(new_list, last)), old(_dryad_S9, sll_lseg_len_next(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S8, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S9, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S8, sll_lseg(list, local.list)), old(_dryad_S9, sll_lseg(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg(SL#_dryad_S9, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S8, sll_lseg_reach(list, local.list)), old(_dryad_S9, sll_lseg_reach(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S9, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S8, sll_lseg_keys(list, local.list)), old(_dryad_S9, sll_lseg_keys(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S9, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S8, sll_lseg_len_next(list, local.list)), old(_dryad_S9, sll_lseg_len_next(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S9, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S8, sll_lseg(list, local.list)), old(_dryad_S9, sll_lseg(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg(SL#_dryad_S9, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S8, sll_lseg_reach(list, local.list)), old(_dryad_S9, sll_lseg_reach(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S9, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S8, sll_lseg_keys(list, local.list)), old(_dryad_S9, sll_lseg_keys(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S9, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S8, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S8, sll_lseg_len_next(list, local.list)), old(_dryad_S9, sll_lseg_len_next(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S8, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S9, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list4)), ==(*((list4->key)), old(_dryad_S8, *((list4->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list4, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list4, ^s_node)) == $rd_inv(SL#_dryad_S8, s_node.key, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list4)), @_vcc_ptr_eq_pure(*((list4->next)), old(_dryad_S8, *((list4->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list4, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list3)), ==(*((list3->key)), old(_dryad_S8, *((list3->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list3, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list3, ^s_node)) == $rd_inv(SL#_dryad_S8, s_node.key, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list3)), @_vcc_ptr_eq_pure(*((list3->next)), old(_dryad_S8, *((list3->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list3, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list0)), ==(*((list0->key)), old(_dryad_S8, *((list0->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list0, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node)) == $rd_inv(SL#_dryad_S8, s_node.key, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list0)), @_vcc_ptr_eq_pure(*((list0->next)), old(_dryad_S8, *((list0->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list0, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, last)), ==(*((last->key)), old(_dryad_S8, *((last->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(L#last, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node)) == $rd_inv(SL#_dryad_S8, s_node.key, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, last)), @_vcc_ptr_eq_pure(*((last->next)), old(_dryad_S8, *((last->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(L#last, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, new_list)), ==(*((new_list->key)), old(_dryad_S8, *((new_list->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(L#new_list, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node)) == $rd_inv(SL#_dryad_S8, s_node.key, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, new_list)), @_vcc_ptr_eq_pure(*((new_list->next)), old(_dryad_S8, *((new_list->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(L#new_list, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, local.list)), ==(*((local.list->key)), old(_dryad_S8, *((local.list->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(local.list, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node)) == $rd_inv(SL#_dryad_S8, s_node.key, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, local.list)), @_vcc_ptr_eq_pure(*((local.list->next)), old(_dryad_S8, *((local.list->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(local.list, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S8, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node);
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll_keys(list4), @_vcc_intset_union(sll_keys(*((list4->next))), @_vcc_intset_singleton(*((list4->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list4, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list4, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll_list_len_next(list4), unchecked+(sll_list_len_next(*((list4->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list4, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll(list4), &&(sll(*((list4->next))), unchecked!(@_vcc_oset_in(list4, sll_reach(*((list4->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list4, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list4, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll_reach(list4), @_vcc_oset_union(sll_reach(*((list4->next))), @_vcc_oset_singleton(list4)))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list4, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list4, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_keys(list3), @_vcc_intset_union(sll_keys(*((list3->next))), @_vcc_intset_singleton(*((list3->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list3, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list3, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_list_len_next(list3), unchecked+(sll_list_len_next(*((list3->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list3, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll(list3), &&(sll(*((list3->next))), unchecked!(@_vcc_oset_in(list3, sll_reach(*((list3->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list3, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list3, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_reach(list3), @_vcc_oset_union(sll_reach(*((list3->next))), @_vcc_oset_singleton(list3)))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list3, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list3, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_keys(list0), @_vcc_intset_union(sll_keys(*((list0->next))), @_vcc_intset_singleton(*((list0->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list0, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_list_len_next(list0), unchecked+(sll_list_len_next(*((list0->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list0, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll(list0), &&(sll(*((list0->next))), unchecked!(@_vcc_oset_in(list0, sll_reach(*((list0->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list0, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list0, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_reach(list0), @_vcc_oset_union(sll_reach(*((list0->next))), @_vcc_oset_singleton(list0)))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list0, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list0, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_list_len_next(new_list), unchecked+(sll_list_len_next(*((new_list->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#new_list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll(new_list), &&(sll(*((new_list->next))), unchecked!(@_vcc_oset_in(new_list, sll_reach(*((new_list->next)))))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_reach(new_list), @_vcc_oset_union(sll_reach(*((new_list->next))), @_vcc_oset_singleton(new_list)))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_keys(tail), @_vcc_intset_union(sll_keys(*((tail->next))), @_vcc_intset_singleton(*((tail->key)))))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tail, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg(new_list, last), &&(sll_lseg(*((new_list->next)), last), unchecked!(@_vcc_oset_in(new_list, sll_lseg_reach(*((new_list->next)), last)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_reach(new_list, last), @_vcc_oset_union(sll_lseg_reach(*((new_list->next)), last), @_vcc_oset_singleton(new_list)))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_keys(new_list, last), @_vcc_intset_union(sll_lseg_keys(*((new_list->next)), last), @_vcc_intset_singleton(*((new_list->key)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_len_next(new_list, last), unchecked+(sll_lseg_len_next(*((new_list->next)), last), 1))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), 1);
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg(list, local.list), &&(sll_lseg(*((list->next)), local.list), unchecked!(@_vcc_oset_in(list, sll_lseg_reach(*((list->next)), local.list)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)) && !$oset_in($phys_ptr_cast(P#list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_reach(list, local.list), @_vcc_oset_union(sll_lseg_reach(*((list->next)), local.list), @_vcc_oset_singleton(list)))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $oset_singleton($phys_ptr_cast(P#list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_keys(list, local.list), @_vcc_intset_union(sll_lseg_keys(*((list->next)), local.list), @_vcc_intset_singleton(*((list->key)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_len_next(list, local.list), unchecked+(sll_lseg_len_next(*((list->next)), local.list), 1))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), 1);
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg(list, local.list), &&(sll_lseg(*((list->next)), local.list), unchecked!(@_vcc_oset_in(list, sll_lseg_reach(*((list->next)), local.list)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)) && !$oset_in($phys_ptr_cast(P#list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_reach(list, local.list), @_vcc_oset_union(sll_lseg_reach(*((list->next)), local.list), @_vcc_oset_singleton(list)))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $oset_singleton($phys_ptr_cast(P#list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_keys(list, local.list), @_vcc_intset_union(sll_lseg_keys(*((list->next)), local.list), @_vcc_intset_singleton(*((list->key)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_len_next(list, local.list), unchecked+(sll_lseg_len_next(*((list->next)), local.list), 1))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), 1);
                // _math \state _dryad_S10; 
                // _dryad_S10 := @_vcc_current_state(@state); 
                SL#_dryad_S10 := $current_state($s);
                // _math \state stmtexpr6#8; 
                // stmtexpr6#8 := _dryad_S10; 
                stmtexpr6#8 := SL#_dryad_S10;
                // assert @prim_writes_check((tail->next)); 
                assert $writable_prim($s, #wrTime$3^3.3, $dot($phys_ptr_cast(L#tail, ^s_node), s_node.next));
                // *(tail->next) := (struct s_node*)@null; 
                call $write_int(s_node.next, $phys_ptr_cast(L#tail, ^s_node), $ptr_to_int($phys_ptr_cast($null, ^s_node)));
                assume $full_stop_ext(#tok$3^56.4, $s);
                // _math \state _dryad_S11; 
                // _dryad_S11 := @_vcc_current_state(@state); 
                SL#_dryad_S11 := $current_state($s);
                // _math \state stmtexpr7#9; 
                // stmtexpr7#9 := _dryad_S11; 
                stmtexpr7#9 := SL#_dryad_S11;
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list4)))), ==(old(_dryad_S10, sll_keys(list4)), old(_dryad_S11, sll_keys(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll_keys(SL#_dryad_S10, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_keys(SL#_dryad_S11, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list4)))), ==(old(_dryad_S10, sll_list_len_next(list4)), old(_dryad_S11, sll_list_len_next(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S10, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_list_len_next(SL#_dryad_S11, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list4)))), ==(old(_dryad_S10, sll(list4)), old(_dryad_S11, sll(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll(SL#_dryad_S10, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll(SL#_dryad_S11, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list4)))), ==(old(_dryad_S10, sll_reach(list4)), old(_dryad_S11, sll_reach(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_reach(SL#_dryad_S11, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list3)))), ==(old(_dryad_S10, sll_keys(list3)), old(_dryad_S11, sll_keys(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_keys(SL#_dryad_S10, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_keys(SL#_dryad_S11, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list3)))), ==(old(_dryad_S10, sll_list_len_next(list3)), old(_dryad_S11, sll_list_len_next(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S10, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_list_len_next(SL#_dryad_S11, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list3)))), ==(old(_dryad_S10, sll(list3)), old(_dryad_S11, sll(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll(SL#_dryad_S10, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll(SL#_dryad_S11, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list3)))), ==(old(_dryad_S10, sll_reach(list3)), old(_dryad_S11, sll_reach(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_reach(SL#_dryad_S11, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list0)))), ==(old(_dryad_S10, sll_keys(list0)), old(_dryad_S11, sll_keys(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_keys(SL#_dryad_S10, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_keys(SL#_dryad_S11, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list0)))), ==(old(_dryad_S10, sll_list_len_next(list0)), old(_dryad_S11, sll_list_len_next(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S10, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_list_len_next(SL#_dryad_S11, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list0)))), ==(old(_dryad_S10, sll(list0)), old(_dryad_S11, sll(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll(SL#_dryad_S10, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll(SL#_dryad_S11, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(list0)))), ==(old(_dryad_S10, sll_reach(list0)), old(_dryad_S11, sll_reach(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_reach(SL#_dryad_S11, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(last)))), ==(old(_dryad_S10, sll_keys(last)), old(_dryad_S11, sll_keys(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_keys(SL#_dryad_S10, $phys_ptr_cast(L#last, ^s_node)) == F#sll_keys(SL#_dryad_S11, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(last)))), ==(old(_dryad_S10, sll_list_len_next(last)), old(_dryad_S11, sll_list_len_next(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S10, $phys_ptr_cast(L#last, ^s_node)) == F#sll_list_len_next(SL#_dryad_S11, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(last)))), ==(old(_dryad_S10, sll(last)), old(_dryad_S11, sll(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll(SL#_dryad_S10, $phys_ptr_cast(L#last, ^s_node)) == F#sll(SL#_dryad_S11, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(last)))), ==(old(_dryad_S10, sll_reach(last)), old(_dryad_S11, sll_reach(last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(L#last, ^s_node)) == F#sll_reach(SL#_dryad_S11, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(new_list)))), ==(old(_dryad_S10, sll_keys(new_list)), old(_dryad_S11, sll_keys(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_keys(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_keys(SL#_dryad_S11, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(new_list)))), ==(old(_dryad_S10, sll_list_len_next(new_list)), old(_dryad_S11, sll_list_len_next(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S11, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(new_list)))), ==(old(_dryad_S10, sll(new_list)), old(_dryad_S11, sll(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll(SL#_dryad_S11, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(new_list)))), ==(old(_dryad_S10, sll_reach(new_list)), old(_dryad_S11, sll_reach(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_reach(SL#_dryad_S11, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(local.list)))), ==(old(_dryad_S10, sll_keys(local.list)), old(_dryad_S11, sll_keys(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_keys(SL#_dryad_S10, $phys_ptr_cast(local.list, ^s_node)) == F#sll_keys(SL#_dryad_S11, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(local.list)))), ==(old(_dryad_S10, sll_list_len_next(local.list)), old(_dryad_S11, sll_list_len_next(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S10, $phys_ptr_cast(local.list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S11, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(local.list)))), ==(old(_dryad_S10, sll(local.list)), old(_dryad_S11, sll(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll(SL#_dryad_S10, $phys_ptr_cast(local.list, ^s_node)) == F#sll(SL#_dryad_S11, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_reach(local.list)))), ==(old(_dryad_S10, sll_reach(local.list)), old(_dryad_S11, sll_reach(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_reach(SL#_dryad_S10, $phys_ptr_cast(local.list, ^s_node)) == F#sll_reach(SL#_dryad_S11, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S10, sll_lseg(new_list, last)), old(_dryad_S11, sll_lseg(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg(SL#_dryad_S11, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S10, sll_lseg_reach(new_list, last)), old(_dryad_S11, sll_lseg_reach(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S11, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S10, sll_lseg_keys(new_list, last)), old(_dryad_S11, sll_lseg_keys(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S11, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S10, sll_lseg_len_next(new_list, last)), old(_dryad_S11, sll_lseg_len_next(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S10, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S11, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S10, sll_lseg(list, local.list)), old(_dryad_S11, sll_lseg(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg(SL#_dryad_S11, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S10, sll_lseg_reach(list, local.list)), old(_dryad_S11, sll_lseg_reach(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S11, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S10, sll_lseg_keys(list, local.list)), old(_dryad_S11, sll_lseg_keys(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S11, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S10, sll_lseg_len_next(list, local.list)), old(_dryad_S11, sll_lseg_len_next(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S11, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S10, sll_lseg(list, local.list)), old(_dryad_S11, sll_lseg(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg(SL#_dryad_S11, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S10, sll_lseg_reach(list, local.list)), old(_dryad_S11, sll_lseg_reach(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S11, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S10, sll_lseg_keys(list, local.list)), old(_dryad_S11, sll_lseg_keys(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S11, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S10, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S10, sll_lseg_len_next(list, local.list)), old(_dryad_S11, sll_lseg_len_next(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_lseg_reach(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S10, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S11, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list4)), ==(*((list4->key)), old(_dryad_S10, *((list4->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list4, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list4, ^s_node)) == $rd_inv(SL#_dryad_S10, s_node.key, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list4)), @_vcc_ptr_eq_pure(*((list4->next)), old(_dryad_S10, *((list4->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list4, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S10, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list3)), ==(*((list3->key)), old(_dryad_S10, *((list3->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list3, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list3, ^s_node)) == $rd_inv(SL#_dryad_S10, s_node.key, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list3)), @_vcc_ptr_eq_pure(*((list3->next)), old(_dryad_S10, *((list3->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list3, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S10, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list0)), ==(*((list0->key)), old(_dryad_S10, *((list0->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list0, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node)) == $rd_inv(SL#_dryad_S10, s_node.key, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, list0)), @_vcc_ptr_eq_pure(*((list0->next)), old(_dryad_S10, *((list0->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(SL#list0, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S10, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, last)), ==(*((last->key)), old(_dryad_S10, *((last->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(L#last, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node)) == $rd_inv(SL#_dryad_S10, s_node.key, $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, last)), @_vcc_ptr_eq_pure(*((last->next)), old(_dryad_S10, *((last->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(L#last, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S10, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, new_list)), ==(*((new_list->key)), old(_dryad_S10, *((new_list->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(L#new_list, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node)) == $rd_inv(SL#_dryad_S10, s_node.key, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, new_list)), @_vcc_ptr_eq_pure(*((new_list->next)), old(_dryad_S10, *((new_list->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(L#new_list, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S10, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, local.list)), ==(*((local.list->key)), old(_dryad_S10, *((local.list->key))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(local.list, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node)) == $rd_inv(SL#_dryad_S10, s_node.key, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(tail, local.list)), @_vcc_ptr_eq_pure(*((local.list->next)), old(_dryad_S10, *((local.list->next))))); 
                assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(local.list, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S10, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node);
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll_keys(list4), @_vcc_intset_union(sll_keys(*((list4->next))), @_vcc_intset_singleton(*((list4->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list4, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list4, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll_list_len_next(list4), unchecked+(sll_list_len_next(*((list4->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list4, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll(list4), &&(sll(*((list4->next))), unchecked!(@_vcc_oset_in(list4, sll_reach(*((list4->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list4, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list4, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll_reach(list4), @_vcc_oset_union(sll_reach(*((list4->next))), @_vcc_oset_singleton(list4)))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list4, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list4, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_keys(list3), @_vcc_intset_union(sll_keys(*((list3->next))), @_vcc_intset_singleton(*((list3->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list3, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list3, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_list_len_next(list3), unchecked+(sll_list_len_next(*((list3->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list3, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll(list3), &&(sll(*((list3->next))), unchecked!(@_vcc_oset_in(list3, sll_reach(*((list3->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list3, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list3, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_reach(list3), @_vcc_oset_union(sll_reach(*((list3->next))), @_vcc_oset_singleton(list3)))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list3, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list3, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_keys(list0), @_vcc_intset_union(sll_keys(*((list0->next))), @_vcc_intset_singleton(*((list0->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list0, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_list_len_next(list0), unchecked+(sll_list_len_next(*((list0->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list0, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll(list0), &&(sll(*((list0->next))), unchecked!(@_vcc_oset_in(list0, sll_reach(*((list0->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list0, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list0, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_reach(list0), @_vcc_oset_union(sll_reach(*((list0->next))), @_vcc_oset_singleton(list0)))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list0, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list0, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_list_len_next(new_list), unchecked+(sll_list_len_next(*((new_list->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#new_list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll(new_list), &&(sll(*((new_list->next))), unchecked!(@_vcc_oset_in(new_list, sll_reach(*((new_list->next)))))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_reach(new_list), @_vcc_oset_union(sll_reach(*((new_list->next))), @_vcc_oset_singleton(new_list)))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_keys(tail), @_vcc_intset_union(sll_keys(*((tail->next))), @_vcc_intset_singleton(*((tail->key)))))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tail, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_list_len_next(tail), unchecked+(sll_list_len_next(*((tail->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#tail, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll(tail), &&(sll(*((tail->next))), unchecked!(@_vcc_oset_in(tail, sll_reach(*((tail->next)))))))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_reach(tail), @_vcc_oset_union(sll_reach(*((tail->next))), @_vcc_oset_singleton(tail)))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tail, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg(new_list, last), &&(sll_lseg(*((new_list->next)), last), unchecked!(@_vcc_oset_in(new_list, sll_lseg_reach(*((new_list->next)), last)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_reach(new_list, last), @_vcc_oset_union(sll_lseg_reach(*((new_list->next)), last), @_vcc_oset_singleton(new_list)))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_keys(new_list, last), @_vcc_intset_union(sll_lseg_keys(*((new_list->next)), last), @_vcc_intset_singleton(*((new_list->key)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_len_next(new_list, last), unchecked+(sll_lseg_len_next(*((new_list->next)), last), 1))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), 1);
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg(list, local.list), &&(sll_lseg(*((list->next)), local.list), unchecked!(@_vcc_oset_in(list, sll_lseg_reach(*((list->next)), local.list)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)) && !$oset_in($phys_ptr_cast(P#list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_reach(list, local.list), @_vcc_oset_union(sll_lseg_reach(*((list->next)), local.list), @_vcc_oset_singleton(list)))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $oset_singleton($phys_ptr_cast(P#list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_keys(list, local.list), @_vcc_intset_union(sll_lseg_keys(*((list->next)), local.list), @_vcc_intset_singleton(*((list->key)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_len_next(list, local.list), unchecked+(sll_lseg_len_next(*((list->next)), local.list), 1))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), 1);
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg(list, local.list), &&(sll_lseg(*((list->next)), local.list), unchecked!(@_vcc_oset_in(list, sll_lseg_reach(*((list->next)), local.list)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)) && !$oset_in($phys_ptr_cast(P#list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_reach(list, local.list), @_vcc_oset_union(sll_lseg_reach(*((list->next)), local.list), @_vcc_oset_singleton(list)))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $oset_singleton($phys_ptr_cast(P#list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_keys(list, local.list), @_vcc_intset_union(sll_lseg_keys(*((list->next)), local.list), @_vcc_intset_singleton(*((list->key)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_len_next(list, local.list), unchecked+(sll_lseg_len_next(*((list->next)), local.list), 1))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), 1);
                // _math \state _dryad_S12; 
                // _dryad_S12 := @_vcc_current_state(@state); 
                SL#_dryad_S12 := $current_state($s);
                // _math \state stmtexpr8#10; 
                // stmtexpr8#10 := _dryad_S12; 
                stmtexpr8#10 := SL#_dryad_S12;
                // assert @prim_writes_check((last->next)); 
                assert $writable_prim($s, #wrTime$3^3.3, $dot($phys_ptr_cast(L#last, ^s_node), s_node.next));
                // *(last->next) := tail; 
                call $write_int(s_node.next, $phys_ptr_cast(L#last, ^s_node), $ptr_to_int($phys_ptr_cast(L#tail, ^s_node)));
                assume $full_stop_ext(#tok$3^58.4, $s);
                // _math \state _dryad_S13; 
                // _dryad_S13 := @_vcc_current_state(@state); 
                SL#_dryad_S13 := $current_state($s);
                // _math \state stmtexpr9#11; 
                // stmtexpr9#11 := _dryad_S13; 
                stmtexpr9#11 := SL#_dryad_S13;
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list4)))), ==(old(_dryad_S12, sll_keys(list4)), old(_dryad_S13, sll_keys(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll_keys(SL#_dryad_S12, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_keys(SL#_dryad_S13, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list4)))), ==(old(_dryad_S12, sll_list_len_next(list4)), old(_dryad_S13, sll_list_len_next(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S12, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_list_len_next(SL#_dryad_S13, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list4)))), ==(old(_dryad_S12, sll(list4)), old(_dryad_S13, sll(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll(SL#_dryad_S12, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll(SL#_dryad_S13, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list4)))), ==(old(_dryad_S12, sll_reach(list4)), old(_dryad_S13, sll_reach(list4)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list4, ^s_node))) ==> F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list4, ^s_node)) == F#sll_reach(SL#_dryad_S13, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(tail)))), ==(old(_dryad_S12, sll_keys(tail)), old(_dryad_S13, sll_keys(tail)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(L#tail, ^s_node))) ==> F#sll_keys(SL#_dryad_S12, $phys_ptr_cast(L#tail, ^s_node)) == F#sll_keys(SL#_dryad_S13, $phys_ptr_cast(L#tail, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(tail)))), ==(old(_dryad_S12, sll_list_len_next(tail)), old(_dryad_S13, sll_list_len_next(tail)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(L#tail, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S12, $phys_ptr_cast(L#tail, ^s_node)) == F#sll_list_len_next(SL#_dryad_S13, $phys_ptr_cast(L#tail, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(tail)))), ==(old(_dryad_S12, sll(tail)), old(_dryad_S13, sll(tail)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(L#tail, ^s_node))) ==> F#sll(SL#_dryad_S12, $phys_ptr_cast(L#tail, ^s_node)) == F#sll(SL#_dryad_S13, $phys_ptr_cast(L#tail, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(tail)))), ==(old(_dryad_S12, sll_reach(tail)), old(_dryad_S13, sll_reach(tail)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(L#tail, ^s_node))) ==> F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(L#tail, ^s_node)) == F#sll_reach(SL#_dryad_S13, $phys_ptr_cast(L#tail, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list3)))), ==(old(_dryad_S12, sll_keys(list3)), old(_dryad_S13, sll_keys(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_keys(SL#_dryad_S12, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_keys(SL#_dryad_S13, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list3)))), ==(old(_dryad_S12, sll_list_len_next(list3)), old(_dryad_S13, sll_list_len_next(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S12, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_list_len_next(SL#_dryad_S13, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list3)))), ==(old(_dryad_S12, sll(list3)), old(_dryad_S13, sll(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll(SL#_dryad_S12, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll(SL#_dryad_S13, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list3)))), ==(old(_dryad_S12, sll_reach(list3)), old(_dryad_S13, sll_reach(list3)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list3, ^s_node))) ==> F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list3, ^s_node)) == F#sll_reach(SL#_dryad_S13, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list0)))), ==(old(_dryad_S12, sll_keys(list0)), old(_dryad_S13, sll_keys(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_keys(SL#_dryad_S12, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_keys(SL#_dryad_S13, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list0)))), ==(old(_dryad_S12, sll_list_len_next(list0)), old(_dryad_S13, sll_list_len_next(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S12, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_list_len_next(SL#_dryad_S13, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list0)))), ==(old(_dryad_S12, sll(list0)), old(_dryad_S13, sll(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll(SL#_dryad_S12, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll(SL#_dryad_S13, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(list0)))), ==(old(_dryad_S12, sll_reach(list0)), old(_dryad_S13, sll_reach(list0)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list0, ^s_node))) ==> F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(SL#list0, ^s_node)) == F#sll_reach(SL#_dryad_S13, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(new_list)))), ==(old(_dryad_S12, sll_keys(new_list)), old(_dryad_S13, sll_keys(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_keys(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_keys(SL#_dryad_S13, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(new_list)))), ==(old(_dryad_S12, sll_list_len_next(new_list)), old(_dryad_S13, sll_list_len_next(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S13, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(new_list)))), ==(old(_dryad_S12, sll(new_list)), old(_dryad_S13, sll(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll(SL#_dryad_S13, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(new_list)))), ==(old(_dryad_S12, sll_reach(new_list)), old(_dryad_S13, sll_reach(new_list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node))) ==> F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node)) == F#sll_reach(SL#_dryad_S13, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(local.list)))), ==(old(_dryad_S12, sll_keys(local.list)), old(_dryad_S13, sll_keys(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_keys(SL#_dryad_S12, $phys_ptr_cast(local.list, ^s_node)) == F#sll_keys(SL#_dryad_S13, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(local.list)))), ==(old(_dryad_S12, sll_list_len_next(local.list)), old(_dryad_S13, sll_list_len_next(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S12, $phys_ptr_cast(local.list, ^s_node)) == F#sll_list_len_next(SL#_dryad_S13, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(local.list)))), ==(old(_dryad_S12, sll(local.list)), old(_dryad_S13, sll(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll(SL#_dryad_S12, $phys_ptr_cast(local.list, ^s_node)) == F#sll(SL#_dryad_S13, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_reach(local.list)))), ==(old(_dryad_S12, sll_reach(local.list)), old(_dryad_S13, sll_reach(local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_reach(SL#_dryad_S12, $phys_ptr_cast(local.list, ^s_node)) == F#sll_reach(SL#_dryad_S13, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S12, sll_lseg(new_list, last)), old(_dryad_S13, sll_lseg(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg(SL#_dryad_S13, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S12, sll_lseg_reach(new_list, last)), old(_dryad_S13, sll_lseg_reach(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S13, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S12, sll_lseg_keys(new_list, last)), old(_dryad_S13, sll_lseg_keys(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S13, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(new_list, last)))), ==(old(_dryad_S12, sll_lseg_len_next(new_list, last)), old(_dryad_S13, sll_lseg_len_next(new_list, last)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S12, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S13, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S12, sll_lseg(list, local.list)), old(_dryad_S13, sll_lseg(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg(SL#_dryad_S13, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S12, sll_lseg_reach(list, local.list)), old(_dryad_S13, sll_lseg_reach(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S13, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S12, sll_lseg_keys(list, local.list)), old(_dryad_S13, sll_lseg_keys(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S13, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S12, sll_lseg_len_next(list, local.list)), old(_dryad_S13, sll_lseg_len_next(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S13, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S12, sll_lseg(list, local.list)), old(_dryad_S13, sll_lseg(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg(SL#_dryad_S13, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S12, sll_lseg_reach(list, local.list)), old(_dryad_S13, sll_lseg_reach(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_reach(SL#_dryad_S13, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S12, sll_lseg_keys(list, local.list)), old(_dryad_S13, sll_lseg_keys(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_keys(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_keys(SL#_dryad_S13, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(unchecked!(@_vcc_oset_in(last, old(_dryad_S12, sll_lseg_reach(list, local.list)))), ==(old(_dryad_S12, sll_lseg_len_next(list, local.list)), old(_dryad_S13, sll_lseg_len_next(list, local.list)))); 
                assume !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node))) ==> F#sll_lseg_len_next(SL#_dryad_S12, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == F#sll_lseg_len_next(SL#_dryad_S13, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(last, list4)), ==(*((list4->key)), old(_dryad_S12, *((list4->key))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(SL#list4, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list4, ^s_node)) == $rd_inv(SL#_dryad_S12, s_node.key, $phys_ptr_cast(SL#list4, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(last, list4)), @_vcc_ptr_eq_pure(*((list4->next)), old(_dryad_S12, *((list4->next))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(SL#list4, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S12, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(last, tail)), ==(*((tail->key)), old(_dryad_S12, *((tail->key))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(L#tail, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node)) == $rd_inv(SL#_dryad_S12, s_node.key, $phys_ptr_cast(L#tail, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(last, tail)), @_vcc_ptr_eq_pure(*((tail->next)), old(_dryad_S12, *((tail->next))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(L#tail, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S12, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(last, list3)), ==(*((list3->key)), old(_dryad_S12, *((list3->key))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(SL#list3, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list3, ^s_node)) == $rd_inv(SL#_dryad_S12, s_node.key, $phys_ptr_cast(SL#list3, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(last, list3)), @_vcc_ptr_eq_pure(*((list3->next)), old(_dryad_S12, *((list3->next))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(SL#list3, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S12, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(last, list0)), ==(*((list0->key)), old(_dryad_S12, *((list0->key))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(SL#list0, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node)) == $rd_inv(SL#_dryad_S12, s_node.key, $phys_ptr_cast(SL#list0, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(last, list0)), @_vcc_ptr_eq_pure(*((list0->next)), old(_dryad_S12, *((list0->next))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(SL#list0, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S12, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(last, new_list)), ==(*((new_list->key)), old(_dryad_S12, *((new_list->key))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(L#new_list, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node)) == $rd_inv(SL#_dryad_S12, s_node.key, $phys_ptr_cast(L#new_list, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(last, new_list)), @_vcc_ptr_eq_pure(*((new_list->next)), old(_dryad_S12, *((new_list->next))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(L#new_list, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S12, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node);
                // assume ==>(!(@_vcc_ptr_eq_pure(last, local.list)), ==(*((local.list->key)), old(_dryad_S12, *((local.list->key))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(local.list, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node)) == $rd_inv(SL#_dryad_S12, s_node.key, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(!(@_vcc_ptr_eq_pure(last, local.list)), @_vcc_ptr_eq_pure(*((local.list->next)), old(_dryad_S12, *((local.list->next))))); 
                assume !($phys_ptr_cast(L#last, ^s_node) == $phys_ptr_cast(local.list, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S12, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node);
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll_keys(list4), @_vcc_intset_union(sll_keys(*((list4->next))), @_vcc_intset_singleton(*((list4->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list4, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list4, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll_list_len_next(list4), unchecked+(sll_list_len_next(*((list4->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list4, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll(list4), &&(sll(*((list4->next))), unchecked!(@_vcc_oset_in(list4, sll_reach(*((list4->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list4, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list4, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list4), ==(sll_reach(list4), @_vcc_oset_union(sll_reach(*((list4->next))), @_vcc_oset_singleton(list4)))); 
                assume $non_null($phys_ptr_cast(SL#list4, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list4, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list4, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list4, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_keys(tail), @_vcc_intset_union(sll_keys(*((tail->next))), @_vcc_intset_singleton(*((tail->key)))))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tail, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_list_len_next(tail), unchecked+(sll_list_len_next(*((tail->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#tail, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll(tail), &&(sll(*((tail->next))), unchecked!(@_vcc_oset_in(tail, sll_reach(*((tail->next)))))))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_reach(tail), @_vcc_oset_union(sll_reach(*((tail->next))), @_vcc_oset_singleton(tail)))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tail, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_keys(list3), @_vcc_intset_union(sll_keys(*((list3->next))), @_vcc_intset_singleton(*((list3->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list3, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list3, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_list_len_next(list3), unchecked+(sll_list_len_next(*((list3->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list3, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll(list3), &&(sll(*((list3->next))), unchecked!(@_vcc_oset_in(list3, sll_reach(*((list3->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list3, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list3, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_reach(list3), @_vcc_oset_union(sll_reach(*((list3->next))), @_vcc_oset_singleton(list3)))); 
                assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list3, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list3, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_keys(list0), @_vcc_intset_union(sll_keys(*((list0->next))), @_vcc_intset_singleton(*((list0->key)))))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list0, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_list_len_next(list0), unchecked+(sll_list_len_next(*((list0->next))), 1))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list0, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll(list0), &&(sll(*((list0->next))), unchecked!(@_vcc_oset_in(list0, sll_reach(*((list0->next)))))))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list0, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list0, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_reach(list0), @_vcc_oset_union(sll_reach(*((list0->next))), @_vcc_oset_singleton(list0)))); 
                assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list0, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list0, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_list_len_next(new_list), unchecked+(sll_list_len_next(*((new_list->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#new_list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll(new_list), &&(sll(*((new_list->next))), unchecked!(@_vcc_oset_in(new_list, sll_reach(*((new_list->next)))))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_reach(new_list), @_vcc_oset_union(sll_reach(*((new_list->next))), @_vcc_oset_singleton(new_list)))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_keys(tail), @_vcc_intset_union(sll_keys(*((tail->next))), @_vcc_intset_singleton(*((tail->key)))))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tail, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_list_len_next(tail), unchecked+(sll_list_len_next(*((tail->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#tail, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll(tail), &&(sll(*((tail->next))), unchecked!(@_vcc_oset_in(tail, sll_reach(*((tail->next)))))))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_reach(tail), @_vcc_oset_union(sll_reach(*((tail->next))), @_vcc_oset_singleton(tail)))); 
                assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tail, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg(list, local.list), &&(sll_lseg(*((list->next)), local.list), unchecked!(@_vcc_oset_in(list, sll_lseg_reach(*((list->next)), local.list)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)) && !$oset_in($phys_ptr_cast(P#list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_reach(list, local.list), @_vcc_oset_union(sll_lseg_reach(*((list->next)), local.list), @_vcc_oset_singleton(list)))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $oset_singleton($phys_ptr_cast(P#list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_keys(list, local.list), @_vcc_intset_union(sll_lseg_keys(*((list->next)), local.list), @_vcc_intset_singleton(*((list->key)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_len_next(list, local.list), unchecked+(sll_lseg_len_next(*((list->next)), local.list), 1))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), 1);
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg(list, local.list), &&(sll_lseg(*((list->next)), local.list), unchecked!(@_vcc_oset_in(list, sll_lseg_reach(*((list->next)), local.list)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)) && !$oset_in($phys_ptr_cast(P#list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_reach(list, local.list), @_vcc_oset_union(sll_lseg_reach(*((list->next)), local.list), @_vcc_oset_singleton(list)))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $oset_singleton($phys_ptr_cast(P#list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_keys(list, local.list), @_vcc_intset_union(sll_lseg_keys(*((list->next)), local.list), @_vcc_intset_singleton(*((list->key)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_len_next(list, local.list), unchecked+(sll_lseg_len_next(*((list->next)), local.list), 1))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), 1);
                // struct s_node* last8; 
                // last8 := last; 
                SL#last8 := $phys_ptr_cast(L#last, ^s_node);
                // struct s_node* stmtexpr10#12; 
                // stmtexpr10#12 := last8; 
                stmtexpr10#12 := $phys_ptr_cast(SL#last8, ^s_node);
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(last), @_vcc_ptr_neq_pure(last, *((last->next)))), ==(sll_lseg(last, *((last->next))), &&(sll_lseg(*((last->next)), *((last->next))), unchecked!(@_vcc_oset_in(last, sll_lseg_reach(*((last->next)), *((last->next)))))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) && $phys_ptr_cast(L#last, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(L#last, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(last), @_vcc_ptr_neq_pure(last, *((last->next)))), ==(sll_lseg_reach(last, *((last->next))), @_vcc_oset_union(sll_lseg_reach(*((last->next)), *((last->next))), @_vcc_oset_singleton(last)))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) && $phys_ptr_cast(L#last, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(L#last, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(last), @_vcc_ptr_neq_pure(last, *((last->next)))), ==(sll_lseg_keys(last, *((last->next))), @_vcc_intset_union(sll_lseg_keys(*((last->next)), *((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) && $phys_ptr_cast(L#last, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(L#last, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(last), @_vcc_ptr_neq_pure(last, *((last->next)))), ==(sll_lseg_len_next(last, *((last->next))), unchecked+(sll_lseg_len_next(*((last->next)), *((last->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) && $phys_ptr_cast(L#last, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(L#last, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
                // assert @reads_check_normal((last->next)); 
                assert $thread_local($s, $phys_ptr_cast(L#last, ^s_node));
                // last := *((last->next)); 
                L#last := $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node);
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg(new_list, last), &&(sll_lseg(*((new_list->next)), last), unchecked!(@_vcc_oset_in(new_list, sll_lseg_reach(*((new_list->next)), last)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_reach(new_list, last), @_vcc_oset_union(sll_lseg_reach(*((new_list->next)), last), @_vcc_oset_singleton(new_list)))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_keys(new_list, last), @_vcc_intset_union(sll_lseg_keys(*((new_list->next)), last), @_vcc_intset_singleton(*((new_list->key)))))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(new_list), @_vcc_ptr_neq_pure(new_list, last)), ==(sll_lseg_len_next(new_list, last), unchecked+(sll_lseg_len_next(*((new_list->next)), last), 1))); 
                assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) && $phys_ptr_cast(L#new_list, ^s_node) != $phys_ptr_cast(L#last, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(L#new_list, ^s_node), $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node), $phys_ptr_cast(L#last, ^s_node)), 1);
                // assume ==>(&&(@_vcc_ptr_neq_null(local.list), @_vcc_ptr_neq_null(*((local.list->next)))), &&(==(@_vcc_mutable(@state, local.list), @_vcc_mutable(@state, *((local.list->next)))), ==(@writes_check(local.list), @writes_check(*((local.list->next)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) && $non_null($rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) ==> $mutable($s, $phys_ptr_cast(local.list, ^s_node)) == $mutable($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && $top_writable($s, #wrTime$3^3.3, $phys_ptr_cast(local.list, ^s_node)) == $top_writable($s, #wrTime$3^3.3, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node));
                // struct s_node* list9; 
                // list9 := local.list; 
                SL#list9 := $phys_ptr_cast(local.list, ^s_node);
                // struct s_node* stmtexpr11#13; 
                // stmtexpr11#13 := list9; 
                stmtexpr11#13 := $phys_ptr_cast(SL#list9, ^s_node);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(local.list), @_vcc_ptr_neq_pure(local.list, *((local.list->next)))), ==(sll_lseg(local.list, *((local.list->next))), &&(sll_lseg(*((local.list->next)), *((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_lseg_reach(*((local.list->next)), *((local.list->next)))))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) && $phys_ptr_cast(local.list, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(local.list, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(local.list), @_vcc_ptr_neq_pure(local.list, *((local.list->next)))), ==(sll_lseg_reach(local.list, *((local.list->next))), @_vcc_oset_union(sll_lseg_reach(*((local.list->next)), *((local.list->next))), @_vcc_oset_singleton(local.list)))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) && $phys_ptr_cast(local.list, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(local.list, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(local.list), @_vcc_ptr_neq_pure(local.list, *((local.list->next)))), ==(sll_lseg_keys(local.list, *((local.list->next))), @_vcc_intset_union(sll_lseg_keys(*((local.list->next)), *((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) && $phys_ptr_cast(local.list, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(local.list, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(local.list), @_vcc_ptr_neq_pure(local.list, *((local.list->next)))), ==(sll_lseg_len_next(local.list, *((local.list->next))), unchecked+(sll_lseg_len_next(*((local.list->next)), *((local.list->next))), 1))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) && $phys_ptr_cast(local.list, ^s_node) != $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(local.list, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
                // assert @reads_check_normal((local.list->next)); 
                assert $thread_local($s, $phys_ptr_cast(local.list, ^s_node));
                // local.list := *((local.list->next)); 
                local.list := $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
                // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg(list, local.list), &&(sll_lseg(*((list->next)), local.list), unchecked!(@_vcc_oset_in(list, sll_lseg_reach(*((list->next)), local.list)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)) && !$oset_in($phys_ptr_cast(P#list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_reach(list, local.list), @_vcc_oset_union(sll_lseg_reach(*((list->next)), local.list), @_vcc_oset_singleton(list)))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $oset_singleton($phys_ptr_cast(P#list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_keys(list, local.list), @_vcc_intset_union(sll_lseg_keys(*((list->next)), local.list), @_vcc_intset_singleton(*((list->key)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_len_next(list, local.list), unchecked+(sll_lseg_len_next(*((list->next)), local.list), 1))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), 1);
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg(list, local.list), &&(sll_lseg(*((list->next)), local.list), unchecked!(@_vcc_oset_in(list, sll_lseg_reach(*((list->next)), local.list)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == (F#sll_lseg($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)) && !$oset_in($phys_ptr_cast(P#list, ^s_node), F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_reach(list, local.list), @_vcc_oset_union(sll_lseg_reach(*((list->next)), local.list), @_vcc_oset_singleton(list)))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_reach($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $oset_singleton($phys_ptr_cast(P#list, ^s_node)));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_keys(list, local.list), @_vcc_intset_union(sll_lseg_keys(*((list->next)), local.list), @_vcc_intset_singleton(*((list->key)))))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_keys($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_lseg_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#list, ^s_node))));
                // assume ==>(&&(@_vcc_ptr_neq_null(list), @_vcc_ptr_neq_pure(list, local.list)), ==(sll_lseg_len_next(list, local.list), unchecked+(sll_lseg_len_next(*((list->next)), local.list), 1))); 
                assume $non_null($phys_ptr_cast(P#list, ^s_node)) && $phys_ptr_cast(P#list, ^s_node) != $phys_ptr_cast(local.list, ^s_node) ==> F#sll_lseg_len_next($s, $phys_ptr_cast(P#list, ^s_node), $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#list, ^s_node), ^s_node), $phys_ptr_cast(local.list, ^s_node)), 1);
                // assume ==>(@_vcc_ptr_neq_null(local.list), &&(@_vcc_mutable(@state, local.list), @writes_check(local.list))); 
                assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> $mutable($s, $phys_ptr_cast(local.list, ^s_node)) && $top_writable($s, #wrTime$3^3.3, $phys_ptr_cast(local.list, ^s_node));
                // assume ==>(@_vcc_ptr_neq_null(last), &&(@_vcc_mutable(@state, last), @writes_check(last))); 
                assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> $mutable($s, $phys_ptr_cast(L#last, ^s_node)) && $top_writable($s, #wrTime$3^3.3, $phys_ptr_cast(L#last, ^s_node));
            }
            else
            {
              anon2:
                // assert @_vcc_possibly_unreachable; 
                assert {:PossiblyUnreachable true} true;
                // goto #break_1; 
                goto #break_1;
            }

          #continue_1:
            assume true;
        }

      anon5:
        assume $full_stop_ext(#tok$3^33.3, $s);

      #break_1:
        // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_keys(list3), @_vcc_intset_union(sll_keys(*((list3->next))), @_vcc_intset_singleton(*((list3->key)))))); 
        assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list3, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list3, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_list_len_next(list3), unchecked+(sll_list_len_next(*((list3->next))), 1))); 
        assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list3, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll(list3), &&(sll(*((list3->next))), unchecked!(@_vcc_oset_in(list3, sll_reach(*((list3->next)))))))); 
        assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list3, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list3, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(list3), ==(sll_reach(list3), @_vcc_oset_union(sll_reach(*((list3->next))), @_vcc_oset_singleton(list3)))); 
        assume $non_null($phys_ptr_cast(SL#list3, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list3, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list3, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list3, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_keys(list0), @_vcc_intset_union(sll_keys(*((list0->next))), @_vcc_intset_singleton(*((list0->key)))))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(SL#list0, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SL#list0, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_list_len_next(list0), unchecked+(sll_list_len_next(*((list0->next))), 1))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(SL#list0, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll(list0), &&(sll(*((list0->next))), unchecked!(@_vcc_oset_in(list0, sll_reach(*((list0->next)))))))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll($s, $phys_ptr_cast(SL#list0, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(SL#list0, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(list0), ==(sll_reach(list0), @_vcc_oset_union(sll_reach(*((list0->next))), @_vcc_oset_singleton(list0)))); 
        assume $non_null($phys_ptr_cast(SL#list0, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(SL#list0, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SL#list0, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(SL#list0, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_keys(last), @_vcc_intset_union(sll_keys(*((last->next))), @_vcc_intset_singleton(*((last->key)))))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#last, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#last, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_list_len_next(last), unchecked+(sll_list_len_next(*((last->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#last, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll(last), &&(sll(*((last->next))), unchecked!(@_vcc_oset_in(last, sll_reach(*((last->next)))))))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#last, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#last, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(last), ==(sll_reach(last), @_vcc_oset_union(sll_reach(*((last->next))), @_vcc_oset_singleton(last)))); 
        assume $non_null($phys_ptr_cast(L#last, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#last, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#last, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#last, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_keys(new_list), @_vcc_intset_union(sll_keys(*((new_list->next))), @_vcc_intset_singleton(*((new_list->key)))))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_list_len_next(new_list), unchecked+(sll_list_len_next(*((new_list->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#new_list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll(new_list), &&(sll(*((new_list->next))), unchecked!(@_vcc_oset_in(new_list, sll_reach(*((new_list->next)))))))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(new_list), ==(sll_reach(new_list), @_vcc_oset_union(sll_reach(*((new_list->next))), @_vcc_oset_singleton(new_list)))); 
        assume $non_null($phys_ptr_cast(L#new_list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_list, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_keys(local.list), @_vcc_intset_union(sll_keys(*((local.list->next))), @_vcc_intset_singleton(*((local.list->key)))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(local.list, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(local.list, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_list_len_next(local.list), unchecked+(sll_list_len_next(*((local.list->next))), 1))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(local.list, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll(local.list), &&(sll(*((local.list->next))), unchecked!(@_vcc_oset_in(local.list, sll_reach(*((local.list->next)))))))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll($s, $phys_ptr_cast(local.list, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(local.list, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(local.list), ==(sll_reach(local.list), @_vcc_oset_union(sll_reach(*((local.list->next))), @_vcc_oset_singleton(local.list)))); 
        assume $non_null($phys_ptr_cast(local.list, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(local.list, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(local.list, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(local.list, ^s_node)));
    }
    else
    {
      anon6:
        // assert @_vcc_possibly_unreachable; 
        assert {:PossiblyUnreachable true} true;
    }

  anon8:
    // return new_list; 
    $result := $phys_ptr_cast(L#new_list, ^s_node);
    assume true;
    assert $position_marker();
    goto #exit;

  anon9:
    // skip

  #exit:
}



const unique l#public: $label;

const unique #tok$3^58.4: $token;

const unique #tok$3^56.4: $token;

const unique #tok$3^55.5: $token;

const unique #tok$3^49.18: $token;

const unique #tok$3^33.3: $token;

const unique #tok$3^24.3: $token;

const unique #tok$3^23.3: $token;

const unique #tok$3^17.14: $token;

const unique #tok$3^11.29: $token;

const unique #tok$4^0.0: $token;

const unique #file^?3Cno?20file?3E: $token;

axiom $file_name_is(4, #file^?3Cno?20file?3E);

const unique #tok$3^3.3: $token;

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Cgslist?5Cg_slist_copy.c: $token;

axiom $file_name_is(3, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Cgslist?5Cg_slist_copy.c);

const unique #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Cgslist?5Cdryad_gslist_sll.h: $token;

axiom $file_name_is(2, #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Cgslist?5Cdryad_gslist_sll.h);

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?2Dbin?5CHeaders?5Cvccp.h: $token;

axiom $file_name_is(1, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?2Dbin?5CHeaders?5Cvccp.h);

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^s_node);
