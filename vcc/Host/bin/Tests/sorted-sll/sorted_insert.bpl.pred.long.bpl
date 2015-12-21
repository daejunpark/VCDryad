
const {:existential true} b0000 : bool;
const {:existential true} b0001 : bool;
const {:existential true} b0002 : bool;
const {:existential true} b0003 : bool;
const {:existential true} b0004 : bool;
const {:existential true} b0005 : bool;
const {:existential true} b0006 : bool;
const {:existential true} b0007 : bool;
const {:existential true} b0008 : bool;
const {:existential true} b0009 : bool;
const {:existential true} b0010 : bool;
const {:existential true} b0011 : bool;
const {:existential true} b0012 : bool;
const {:existential true} b0013 : bool;
const {:existential true} b0014 : bool;
const {:existential true} b0015 : bool;
const {:existential true} b0016 : bool;
const {:existential true} b0017 : bool;
const {:existential true} b0018 : bool;
const {:existential true} b0019 : bool;
const {:existential true} b0020 : bool;
const {:existential true} b0021 : bool;
const {:existential true} b0022 : bool;
const {:existential true} b0023 : bool;
const {:existential true} b0024 : bool;
const {:existential true} b0025 : bool;
const {:existential true} b0026 : bool;
const {:existential true} b0027 : bool;
const {:existential true} b0028 : bool;
const {:existential true} b0029 : bool;
const {:existential true} b0030 : bool;
const {:existential true} b0031 : bool;
const {:existential true} b0032 : bool;
const {:existential true} b0033 : bool;
const {:existential true} b0034 : bool;
const {:existential true} b0035 : bool;
const {:existential true} b0036 : bool;
const {:existential true} b0037 : bool;
const {:existential true} b0038 : bool;
const {:existential true} b0039 : bool;
const {:existential true} b0040 : bool;
const {:existential true} b0041 : bool;
const {:existential true} b0042 : bool;
const {:existential true} b0043 : bool;
const {:existential true} b0044 : bool;
const {:existential true} b0045 : bool;
const {:existential true} b0046 : bool;
const {:existential true} b0047 : bool;
const {:existential true} b0048 : bool;
const {:existential true} b0049 : bool;
const {:existential true} b0050 : bool;
const {:existential true} b0051 : bool;
const {:existential true} b0052 : bool;
const {:existential true} b0053 : bool;
const {:existential true} b0054 : bool;
const {:existential true} b0055 : bool;
const {:existential true} b0056 : bool;
const {:existential true} b0057 : bool;
const {:existential true} b0058 : bool;
const {:existential true} b0059 : bool;
const {:existential true} b0060 : bool;
const {:existential true} b0061 : bool;
const {:existential true} b0062 : bool;
const {:existential true} b0063 : bool;
const {:existential true} b0064 : bool;
const {:existential true} b0065 : bool;
const {:existential true} b0066 : bool;
const {:existential true} b0067 : bool;
const {:existential true} b0068 : bool;
const {:existential true} b0069 : bool;
const {:existential true} b0070 : bool;
const {:existential true} b0071 : bool;
const {:existential true} b0072 : bool;
const {:existential true} b0073 : bool;
const {:existential true} b0074 : bool;
const {:existential true} b0075 : bool;

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

const unique ^$#sorted_insert.c..36263#3: $ctype;

axiom $def_fnptr_type(^$#sorted_insert.c..36263#3);

type $#sorted_insert.c..36263#3;

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



function F#srtl(#s: $state, SP#hd: $ptr) : bool;

const unique cf#srtl: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr :: { F#srtl(#s, SP#hd) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#srtl(#s, SP#hd));

axiom $function_arg_type(cf#srtl, 0, ^^bool);

axiom $function_arg_type(cf#srtl, 1, $ptr_to(^s_node));

procedure srtl(SP#hd: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result;
  free ensures $result == F#srtl($s, SP#hd);
  free ensures $call_transition(old($s), $s);



function F#rsrtl(#s: $state, SP#hd: $ptr) : bool;

const unique cf#rsrtl: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr :: { F#rsrtl(#s, SP#hd) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#rsrtl(#s, SP#hd));

axiom $function_arg_type(cf#rsrtl, 0, ^^bool);

axiom $function_arg_type(cf#rsrtl, 1, $ptr_to(^s_node));

procedure rsrtl(SP#hd: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result;
  free ensures $result == F#rsrtl($s, SP#hd);
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



function F#srtl_reach(#s: $state, SP#hd: $ptr) : $oset;

const unique cf#srtl_reach: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr :: { F#srtl_reach(#s, SP#hd) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), F#srtl_reach(#s, SP#hd))) && ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#srtl_reach(#s, SP#hd) == $oset_empty()));

axiom $function_arg_type(cf#srtl_reach, 0, ^$#oset);

axiom $function_arg_type(cf#srtl_reach, 1, $ptr_to(^s_node));

procedure srtl_reach(SP#hd: $ptr) returns ($result: $oset);
  ensures ($non_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), $result)) && ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result == $oset_empty());
  free ensures $result == F#srtl_reach($s, SP#hd);
  free ensures $call_transition(old($s), $s);



function F#rsrtl_reach(#s: $state, SP#hd: $ptr) : $oset;

const unique cf#rsrtl_reach: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr :: { F#rsrtl_reach(#s, SP#hd) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), F#rsrtl_reach(#s, SP#hd))) && ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#rsrtl_reach(#s, SP#hd) == $oset_empty()));

axiom $function_arg_type(cf#rsrtl_reach, 0, ^$#oset);

axiom $function_arg_type(cf#rsrtl_reach, 1, $ptr_to(^s_node));

procedure rsrtl_reach(SP#hd: $ptr) returns ($result: $oset);
  ensures ($non_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), $result)) && ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result == $oset_empty());
  free ensures $result == F#rsrtl_reach($s, SP#hd);
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

axiom (forall #s: $state, SP#hd: $ptr, SP#tl: $ptr :: { F#sll_lseg(#s, SP#hd, SP#tl) } 1 < $decreases_level ==> ($is_null($phys_ptr_cast(SP#hd, ^s_node)) && $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg(#s, SP#hd, SP#tl)) && ($phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg(#s, SP#hd, SP#tl)) && ($is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> F#sll_lseg(#s, SP#hd, SP#tl) == F#sll(#s, $phys_ptr_cast(SP#hd, ^s_node))) && ($non_null($phys_ptr_cast(SP#hd, ^s_node)) && F#sll(#s, $phys_ptr_cast(SP#tl, ^s_node)) && $oset_disjoint(F#sll_reach(#s, $phys_ptr_cast(SP#tl, ^s_node)), F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) ==> F#sll(#s, $phys_ptr_cast(SP#hd, ^s_node)) && F#sll_reach(#s, $phys_ptr_cast(SP#hd, ^s_node)) == $oset_union(F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_reach(#s, $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_keys(#s, $phys_ptr_cast(SP#hd, ^s_node)) == $intset_union(F#sll_keys(#s, $phys_ptr_cast(SP#tl, ^s_node)), F#sll_lseg_keys(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_list_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_list_len_next(#s, $phys_ptr_cast(SP#tl, ^s_node)))) && ($non_null($phys_ptr_cast(SP#hd, ^s_node)) && $non_null($phys_ptr_cast(SP#tl, ^s_node)) && F#sll(#s, $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) && F#sll_lseg(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)) && $oset_disjoint(F#sll_reach(#s, $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)), F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && !$oset_in($phys_ptr_cast(SP#tl, ^s_node), F#sll_reach(#s, $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node))) && !$oset_in($phys_ptr_cast(SP#tl, ^s_node), F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) ==> $oset_in($phys_ptr_cast(SP#tl, ^s_node), F#sll_reach(#s, $phys_ptr_cast(SP#hd, ^s_node))) && F#sll_lseg(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) && F#sll_lseg_keys(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $intset_union($intset_singleton($rd_inv(#s, s_node.key, $phys_ptr_cast(SP#tl, ^s_node))), F#sll_lseg_keys(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $oset_union_one1($phys_ptr_cast(SP#tl, ^s_node), F#sll_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_lseg_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), 1)));

axiom $function_arg_type(cf#sll_lseg, 0, ^^bool);

axiom $function_arg_type(cf#sll_lseg, 1, $ptr_to(^s_node));

axiom $function_arg_type(cf#sll_lseg, 2, $ptr_to(^s_node));

procedure sll_lseg(SP#hd: $ptr, SP#tl: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#hd, ^s_node)) && $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $result;
  ensures $phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> $result;
  ensures $is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> $result == F#sll($s, $phys_ptr_cast(SP#hd, ^s_node));
  ensures $non_null($phys_ptr_cast(SP#hd, ^s_node)) && F#sll($s, $phys_ptr_cast(SP#tl, ^s_node)) && $oset_disjoint(F#sll_reach($s, $phys_ptr_cast(SP#tl, ^s_node)), F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) ==> F#sll($s, $phys_ptr_cast(SP#hd, ^s_node)) && F#sll_reach($s, $phys_ptr_cast(SP#hd, ^s_node)) == $oset_union(F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_reach($s, $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_keys($s, $phys_ptr_cast(SP#hd, ^s_node)) == $intset_union(F#sll_keys($s, $phys_ptr_cast(SP#tl, ^s_node)), F#sll_lseg_keys($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_list_len_next($s, $phys_ptr_cast(SP#hd, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_list_len_next($s, $phys_ptr_cast(SP#tl, ^s_node)));
  ensures $non_null($phys_ptr_cast(SP#hd, ^s_node)) && $non_null($phys_ptr_cast(SP#tl, ^s_node)) && F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) && F#sll_lseg($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)) && $oset_disjoint(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)), F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && !$oset_in($phys_ptr_cast(SP#tl, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node))) && !$oset_in($phys_ptr_cast(SP#tl, ^s_node), F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) ==> $oset_in($phys_ptr_cast(SP#tl, ^s_node), F#sll_reach($s, $phys_ptr_cast(SP#hd, ^s_node))) && F#sll_lseg($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) && F#sll_lseg_keys($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $intset_union($intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SP#tl, ^s_node))), F#sll_lseg_keys($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $oset_union_one1($phys_ptr_cast(SP#tl, ^s_node), F#sll_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_lseg_len_next($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), 1);
  free ensures $result == F#sll_lseg($s, SP#hd, SP#tl);
  free ensures $call_transition(old($s), $s);



function F#srtl_lseg(#s: $state, SP#hd: $ptr, SP#tl: $ptr) : bool;

const unique cf#srtl_lseg: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr, SP#tl: $ptr :: { F#srtl_lseg(#s, SP#hd, SP#tl) } 1 < $decreases_level ==> ($is_null($phys_ptr_cast(SP#hd, ^s_node)) && $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> F#srtl_lseg(#s, SP#hd, SP#tl)) && ($phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> F#srtl_lseg(#s, SP#hd, SP#tl)) && ($is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> F#srtl_lseg(#s, SP#hd, SP#tl) == F#srtl(#s, $phys_ptr_cast(SP#hd, ^s_node))) && (F#srtl(#s, $phys_ptr_cast(SP#tl, ^s_node)) && $oset_disjoint(F#srtl_reach(#s, $phys_ptr_cast(SP#tl, ^s_node)), F#srtl_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) ==> F#srtl(#s, $phys_ptr_cast(SP#hd, ^s_node)) && F#srtl_reach(#s, $phys_ptr_cast(SP#hd, ^s_node)) == $oset_union(F#srtl_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#srtl_reach(#s, $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_keys(#s, $phys_ptr_cast(SP#hd, ^s_node)) == $intset_union(F#sll_keys(#s, $phys_ptr_cast(SP#tl, ^s_node)), F#sll_lseg_keys(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_list_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_list_len_next(#s, $phys_ptr_cast(SP#tl, ^s_node)))) && ($non_null($phys_ptr_cast(SP#hd, ^s_node)) && $non_null($phys_ptr_cast(SP#tl, ^s_node)) && F#srtl(#s, $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) && F#srtl_lseg(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)) && $oset_disjoint(F#srtl_reach(#s, $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)), F#srtl_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && !$oset_in($phys_ptr_cast(SP#tl, ^s_node), F#srtl_reach(#s, $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node))) && !$oset_in($phys_ptr_cast(SP#tl, ^s_node), F#srtl_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && $intset_le($intset_singleton($rd_inv(#s, s_node.key, $phys_ptr_cast(SP#tl, ^s_node))), F#sll_keys(#s, $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node))) ==> $oset_in($phys_ptr_cast(SP#tl, ^s_node), F#srtl_reach(#s, $phys_ptr_cast(SP#hd, ^s_node))) && F#srtl_lseg(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) && F#sll_lseg_keys(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $intset_union($intset_singleton($rd_inv(#s, s_node.key, $phys_ptr_cast(SP#tl, ^s_node))), F#sll_lseg_keys(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#srtl_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $oset_union_one1($phys_ptr_cast(SP#tl, ^s_node), F#srtl_lseg_reach(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_lseg_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr(#s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), 1)));

axiom $function_arg_type(cf#srtl_lseg, 0, ^^bool);

axiom $function_arg_type(cf#srtl_lseg, 1, $ptr_to(^s_node));

axiom $function_arg_type(cf#srtl_lseg, 2, $ptr_to(^s_node));

procedure srtl_lseg(SP#hd: $ptr, SP#tl: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#hd, ^s_node)) && $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $result;
  ensures $phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> $result;
  ensures $is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> $result == F#srtl($s, $phys_ptr_cast(SP#hd, ^s_node));
  ensures F#srtl($s, $phys_ptr_cast(SP#tl, ^s_node)) && $oset_disjoint(F#srtl_reach($s, $phys_ptr_cast(SP#tl, ^s_node)), F#srtl_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) ==> F#srtl($s, $phys_ptr_cast(SP#hd, ^s_node)) && F#srtl_reach($s, $phys_ptr_cast(SP#hd, ^s_node)) == $oset_union(F#srtl_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#srtl_reach($s, $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_keys($s, $phys_ptr_cast(SP#hd, ^s_node)) == $intset_union(F#sll_keys($s, $phys_ptr_cast(SP#tl, ^s_node)), F#sll_lseg_keys($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_list_len_next($s, $phys_ptr_cast(SP#hd, ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), F#sll_list_len_next($s, $phys_ptr_cast(SP#tl, ^s_node)));
  ensures $non_null($phys_ptr_cast(SP#hd, ^s_node)) && $non_null($phys_ptr_cast(SP#tl, ^s_node)) && F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) && F#srtl_lseg($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)) && $oset_disjoint(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)), F#srtl_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && !$oset_in($phys_ptr_cast(SP#tl, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node))) && !$oset_in($phys_ptr_cast(SP#tl, ^s_node), F#srtl_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && $intset_le($intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SP#tl, ^s_node))), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node))) ==> $oset_in($phys_ptr_cast(SP#tl, ^s_node), F#srtl_reach($s, $phys_ptr_cast(SP#hd, ^s_node))) && F#srtl_lseg($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) && F#sll_lseg_keys($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $intset_union($intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(SP#tl, ^s_node))), F#sll_lseg_keys($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#srtl_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $oset_union_one1($phys_ptr_cast(SP#tl, ^s_node), F#srtl_lseg_reach($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))) && F#sll_lseg_len_next($s, $phys_ptr_cast(SP#hd, ^s_node), $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(SP#tl, ^s_node), ^s_node)) == $unchk_add(^^nat, F#sll_lseg_len_next($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node)), 1);
  free ensures $result == F#srtl_lseg($s, SP#hd, SP#tl);
  free ensures $call_transition(old($s), $s);



function F#sll_lseg_reach(#s: $state, SP#hd: $ptr, SP#tl: $ptr) : $oset;

const unique cf#sll_lseg_reach: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr, SP#tl: $ptr :: { F#sll_lseg_reach(#s, SP#hd, SP#tl) } 1 < $decreases_level ==> ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#sll_lseg_reach(#s, SP#hd, SP#tl) == $oset_empty()) && ($phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg_reach(#s, SP#hd, SP#tl) == $oset_empty()) && ($phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), F#sll_lseg_reach(#s, SP#hd, SP#tl))) && ($is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> F#sll_lseg_reach(#s, SP#hd, SP#tl) == F#sll_reach(#s, $phys_ptr_cast(SP#hd, ^s_node))));

axiom $function_arg_type(cf#sll_lseg_reach, 0, ^$#oset);

axiom $function_arg_type(cf#sll_lseg_reach, 1, $ptr_to(^s_node));

axiom $function_arg_type(cf#sll_lseg_reach, 2, $ptr_to(^s_node));

procedure sll_lseg_reach(SP#hd: $ptr, SP#tl: $ptr) returns ($result: $oset);
  ensures $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result == $oset_empty();
  ensures $phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> $result == $oset_empty();
  ensures $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), $result);
  ensures $is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> $result == F#sll_reach($s, $phys_ptr_cast(SP#hd, ^s_node));
  free ensures $result == F#sll_lseg_reach($s, SP#hd, SP#tl);
  free ensures $call_transition(old($s), $s);



function F#srtl_lseg_reach(#s: $state, SP#hd: $ptr, SP#tl: $ptr) : $oset;

const unique cf#srtl_lseg_reach: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr, SP#tl: $ptr :: { F#srtl_lseg_reach(#s, SP#hd, SP#tl) } 1 < $decreases_level ==> ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#srtl_lseg_reach(#s, SP#hd, SP#tl) == $oset_empty()) && ($phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> F#srtl_lseg_reach(#s, SP#hd, SP#tl) == $oset_empty()) && ($phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), F#srtl_lseg_reach(#s, SP#hd, SP#tl))) && ($is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> F#srtl_lseg_reach(#s, SP#hd, SP#tl) == F#srtl_reach(#s, $phys_ptr_cast(SP#hd, ^s_node))));

axiom $function_arg_type(cf#srtl_lseg_reach, 0, ^$#oset);

axiom $function_arg_type(cf#srtl_lseg_reach, 1, $ptr_to(^s_node));

axiom $function_arg_type(cf#srtl_lseg_reach, 2, $ptr_to(^s_node));

procedure srtl_lseg_reach(SP#hd: $ptr, SP#tl: $ptr) returns ($result: $oset);
  ensures $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result == $oset_empty();
  ensures $phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> $result == $oset_empty();
  ensures $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $oset_in($phys_ptr_cast(SP#hd, ^s_node), $result);
  ensures $is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> $result == F#srtl_reach($s, $phys_ptr_cast(SP#hd, ^s_node));
  free ensures $result == F#srtl_lseg_reach($s, SP#hd, SP#tl);
  free ensures $call_transition(old($s), $s);



function F#sll_lseg_keys(#s: $state, SP#hd: $ptr, SP#tl: $ptr) : $intset;

const unique cf#sll_lseg_keys: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr, SP#tl: $ptr :: { F#sll_lseg_keys(#s, SP#hd, SP#tl) } 1 < $decreases_level ==> ($phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $intset_in($rd_inv(#s, s_node.key, $phys_ptr_cast(SP#hd, ^s_node)), F#sll_lseg_keys(#s, SP#hd, SP#tl))) && ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#sll_lseg_keys(#s, SP#hd, SP#tl) == $intset_empty()) && ($phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg_keys(#s, SP#hd, SP#tl) == $intset_empty()) && ($is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> F#sll_lseg_keys(#s, SP#hd, SP#tl) == F#sll_keys(#s, $phys_ptr_cast(SP#hd, ^s_node))));

axiom $function_arg_type(cf#sll_lseg_keys, 0, ^$#intset);

axiom $function_arg_type(cf#sll_lseg_keys, 1, $ptr_to(^s_node));

axiom $function_arg_type(cf#sll_lseg_keys, 2, $ptr_to(^s_node));

procedure sll_lseg_keys(SP#hd: $ptr, SP#tl: $ptr) returns ($result: $intset);
  ensures $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $intset_in($rd_inv($s, s_node.key, $phys_ptr_cast(SP#hd, ^s_node)), $result);
  ensures $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result == $intset_empty();
  ensures $phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> $result == $intset_empty();
  ensures $is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> $result == F#sll_keys($s, $phys_ptr_cast(SP#hd, ^s_node));
  free ensures $result == F#sll_lseg_keys($s, SP#hd, SP#tl);
  free ensures $call_transition(old($s), $s);



function F#sll_lseg_len_next(#s: $state, SP#hd: $ptr, SP#tl: $ptr) : int;

const unique cf#sll_lseg_len_next: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr, SP#tl: $ptr :: { F#sll_lseg_len_next(#s, SP#hd, SP#tl) } 1 < $decreases_level ==> $in_range_nat(F#sll_lseg_len_next(#s, SP#hd, SP#tl)) && ($phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg_len_next(#s, SP#hd, SP#tl) == 0) && ($is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> F#sll_lseg_len_next(#s, SP#hd, SP#tl) == 0) && ($phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> F#sll_lseg_len_next(#s, SP#hd, SP#tl) > 0) && ($is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> F#sll_lseg_len_next(#s, SP#hd, SP#tl) == F#sll_lseg_len_next(#s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node))));

axiom $function_arg_type(cf#sll_lseg_len_next, 0, ^^nat);

axiom $function_arg_type(cf#sll_lseg_len_next, 1, $ptr_to(^s_node));

axiom $function_arg_type(cf#sll_lseg_len_next, 2, $ptr_to(^s_node));

procedure sll_lseg_len_next(SP#hd: $ptr, SP#tl: $ptr) returns ($result: int);
  free ensures $in_range_nat($result);
  ensures $phys_ptr_cast(SP#hd, ^s_node) == $phys_ptr_cast(SP#tl, ^s_node) ==> $result == 0;
  ensures $is_null($phys_ptr_cast(SP#hd, ^s_node)) ==> $result == 0;
  ensures $phys_ptr_cast(SP#hd, ^s_node) != $phys_ptr_cast(SP#tl, ^s_node) ==> $result > 0;
  ensures $is_null($phys_ptr_cast(SP#tl, ^s_node)) ==> $result == F#sll_lseg_len_next($s, $phys_ptr_cast(SP#hd, ^s_node), $phys_ptr_cast(SP#tl, ^s_node));
  free ensures $result == F#sll_lseg_len_next($s, SP#hd, SP#tl);
  free ensures $call_transition(old($s), $s);



procedure sorted_insert(P#x: $ptr, P#k: int) returns ($result: $ptr);
  requires F#srtl($s, $phys_ptr_cast(P#x, ^s_node));
  requires !$intset_in(P#k, F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)));
  modifies $s, $cev_pc;
  ensures F#srtl($s, $phys_ptr_cast($result, ^s_node));
  ensures F#sll($s, $phys_ptr_cast($result, ^s_node));
ensures b0000 ==> (F#srtl($s,$phys_ptr_cast(P#x,^s_node)));
ensures b0001 ==> (F#srtl($s,$phys_ptr_cast($result,^s_node)));
ensures b0002 ==> (F#srtl_lseg($s,$phys_ptr_cast(P#x,^s_node),$phys_ptr_cast($result,^s_node)));
ensures b0003 ==> (F#srtl_lseg($s,$phys_ptr_cast($result,^s_node),$phys_ptr_cast(P#x,^s_node)));
ensures b0004 ==> (((F#srtl($s,$phys_ptr_cast(P#x,^s_node)) && F#srtl($s,$phys_ptr_cast($result,^s_node))) ==> $oset_disjoint(F#srtl_reach($s,$phys_ptr_cast(P#x,^s_node)),F#srtl_reach($s,$phys_ptr_cast($result,^s_node)))));
ensures b0005 ==> (((F#srtl($s,$phys_ptr_cast($result,^s_node)) && F#srtl($s,$phys_ptr_cast(P#x,^s_node))) ==> $oset_disjoint(F#srtl_reach($s,$phys_ptr_cast($result,^s_node)),F#srtl_reach($s,$phys_ptr_cast(P#x,^s_node)))));
ensures b0006 ==> (((F#srtl_lseg($s,$phys_ptr_cast(P#x,^s_node),$phys_ptr_cast($result,^s_node)) && F#srtl($s,$phys_ptr_cast($result,^s_node))) ==> $oset_disjoint(F#srtl_lseg_reach($s,$phys_ptr_cast(P#x,^s_node),$phys_ptr_cast($result,^s_node)),F#srtl_reach($s,$phys_ptr_cast($result,^s_node)))));
ensures b0007 ==> (((F#srtl_lseg($s,$phys_ptr_cast($result,^s_node),$phys_ptr_cast(P#x,^s_node)) && F#srtl($s,$phys_ptr_cast(P#x,^s_node))) ==> $oset_disjoint(F#srtl_lseg_reach($s,$phys_ptr_cast($result,^s_node),$phys_ptr_cast(P#x,^s_node)),F#srtl_reach($s,$phys_ptr_cast(P#x,^s_node)))));
ensures b0008 ==> ((F#srtl($s,$phys_ptr_cast($result,^s_node)) ==> $oset_disjoint($oset_singleton($phys_ptr_cast(P#x,^s_node)),F#srtl_reach($s,$phys_ptr_cast($result,^s_node)))));
ensures b0009 ==> ((F#srtl($s,$phys_ptr_cast(P#x,^s_node)) ==> $oset_disjoint($oset_singleton($phys_ptr_cast($result,^s_node)),F#srtl_reach($s,$phys_ptr_cast(P#x,^s_node)))));
ensures b0010 ==> ((F#srtl_reach($s,$phys_ptr_cast(P#x,^s_node)) == F#srtl_reach($s,$phys_ptr_cast($result,^s_node))));
ensures b0011 ==> ((F#srtl_reach($s,$phys_ptr_cast($result,^s_node)) == F#srtl_reach($s,$phys_ptr_cast(P#x,^s_node))));
ensures b0012 ==> ((F#srtl_reach($s,$phys_ptr_cast(P#x,^s_node)) == F#srtl_reach(old($s),$phys_ptr_cast(P#x,^s_node))));
ensures b0013 ==> ((F#srtl_reach($s,$phys_ptr_cast($result,^s_node)) == F#srtl_reach(old($s),$phys_ptr_cast($result,^s_node))));
ensures b0014 ==> ($non_null($phys_ptr_cast(P#x,^s_node)));
ensures b0015 ==> ($non_null($phys_ptr_cast($result,^s_node)));
ensures b0016 ==> ($is_null($phys_ptr_cast(P#x,^s_node)));
ensures b0017 ==> ($is_null($phys_ptr_cast($result,^s_node)));
ensures b0018 ==> (($phys_ptr_cast(P#x,^s_node) == $phys_ptr_cast($result,^s_node)));
ensures b0019 ==> (($phys_ptr_cast($result,^s_node) == $phys_ptr_cast(P#x,^s_node)));
ensures b0020 ==> (($non_null($phys_ptr_cast(P#x,^s_node)) ==> $non_null($rd_phys_ptr($s,s_node.next,$phys_ptr_cast(P#x,^s_node),^s_node))));
ensures b0021 ==> (($non_null($phys_ptr_cast($result,^s_node)) ==> $non_null($rd_phys_ptr($s,s_node.next,$phys_ptr_cast($result,^s_node),^s_node))));
ensures b0022 ==> (($non_null($phys_ptr_cast(P#x,^s_node)) ==> $is_null($rd_phys_ptr($s,s_node.next,$phys_ptr_cast(P#x,^s_node),^s_node))));
ensures b0023 ==> (($non_null($phys_ptr_cast($result,^s_node)) ==> $is_null($rd_phys_ptr($s,s_node.next,$phys_ptr_cast($result,^s_node),^s_node))));
ensures b0024 ==> (($non_null($phys_ptr_cast(P#x,^s_node)) ==> ($rd_phys_ptr($s,s_node.next,$phys_ptr_cast(P#x,^s_node),^s_node) == $phys_ptr_cast($result,^s_node))));
ensures b0025 ==> (($non_null($phys_ptr_cast($result,^s_node)) ==> ($rd_phys_ptr($s,s_node.next,$phys_ptr_cast($result,^s_node),^s_node) == $phys_ptr_cast(P#x,^s_node))));
ensures b0026 ==> ((!($intset_in(P#k,F#sll_keys($s,$phys_ptr_cast(P#x,^s_node))))));
ensures b0027 ==> ((!($intset_in(P#k,F#sll_keys($s,$phys_ptr_cast($result,^s_node))))));
ensures b0028 ==> ((!($intset_in(P#k,F#sll_lseg_keys($s,$phys_ptr_cast(P#x,^s_node),$phys_ptr_cast($result,^s_node))))));
ensures b0029 ==> ((!($intset_in(P#k,F#sll_lseg_keys($s,$phys_ptr_cast($result,^s_node),$phys_ptr_cast(P#x,^s_node))))));
ensures b0030 ==> ($intset_in(P#k,F#sll_keys($s,$phys_ptr_cast(P#x,^s_node))));
ensures b0031 ==> ($intset_in(P#k,F#sll_keys($s,$phys_ptr_cast($result,^s_node))));
ensures b0032 ==> ($intset_in(P#k,F#sll_lseg_keys($s,$phys_ptr_cast(P#x,^s_node),$phys_ptr_cast($result,^s_node))));
ensures b0033 ==> ($intset_in(P#k,F#sll_lseg_keys($s,$phys_ptr_cast($result,^s_node),$phys_ptr_cast(P#x,^s_node))));
ensures b0034 ==> ((F#sll_keys($s,$phys_ptr_cast(P#x,^s_node)) == F#sll_keys($s,$phys_ptr_cast($result,^s_node))));
ensures b0035 ==> ((F#sll_keys($s,$phys_ptr_cast($result,^s_node)) == F#sll_keys($s,$phys_ptr_cast(P#x,^s_node))));
ensures b0036 ==> ((F#sll_keys($s,$phys_ptr_cast(P#x,^s_node)) == F#sll_keys(old($s),$phys_ptr_cast($result,^s_node))));
ensures b0037 ==> ((F#sll_keys($s,$phys_ptr_cast($result,^s_node)) == F#sll_keys(old($s),$phys_ptr_cast(P#x,^s_node))));
ensures b0038 ==> ((F#sll_keys($s,$phys_ptr_cast(P#x,^s_node)) == $intset_union(F#sll_keys(old($s),$phys_ptr_cast($result,^s_node)),$intset_singleton(P#k))));
ensures b0039 ==> ((F#sll_keys($s,$phys_ptr_cast($result,^s_node)) == $intset_union(F#sll_keys(old($s),$phys_ptr_cast(P#x,^s_node)),$intset_singleton(P#k))));
ensures b0040 ==> ((F#sll_keys($s,$phys_ptr_cast(P#x,^s_node)) == F#sll_keys($s,$phys_ptr_cast($result,^s_node))));
ensures b0041 ==> ((F#sll_keys($s,$phys_ptr_cast($result,^s_node)) == F#sll_keys($s,$phys_ptr_cast(P#x,^s_node))));
ensures b0042 ==> ((F#sll_keys(old($s),$phys_ptr_cast(P#x,^s_node)) == $intset_union(F#sll_keys($s,$phys_ptr_cast(P#x,^s_node)),F#sll_keys($s,$phys_ptr_cast($result,^s_node)))));
ensures b0043 ==> ((F#sll_keys(old($s),$phys_ptr_cast($result,^s_node)) == $intset_union(F#sll_keys($s,$phys_ptr_cast($result,^s_node)),F#sll_keys($s,$phys_ptr_cast(P#x,^s_node)))));
ensures b0044 ==> ((F#sll_keys($s,$phys_ptr_cast(P#x,^s_node)) == $intset_union(F#sll_keys(old($s),$phys_ptr_cast(P#x,^s_node)),F#sll_keys($s,$phys_ptr_cast($result,^s_node)))));
ensures b0045 ==> ((F#sll_keys($s,$phys_ptr_cast($result,^s_node)) == $intset_union(F#sll_keys(old($s),$phys_ptr_cast($result,^s_node)),F#sll_keys($s,$phys_ptr_cast(P#x,^s_node)))));
ensures b0046 ==> ((P#k < 2147483647));
ensures b0047 ==> ((P#k < 2147483647));
ensures b0048 ==> ((P#k < 4294967295));
ensures b0049 ==> ((P#k < 4294967295));
ensures b0050 ==> ((P#k >= 0));
ensures b0051 ==> ((P#k >= 0));
ensures b0052 ==> (($rd_inv($s,s_node.key,$phys_ptr_cast(P#x,^s_node)) < P#k));
ensures b0053 ==> (($rd_inv($s,s_node.key,$phys_ptr_cast($result,^s_node)) < P#k));
ensures b0054 ==> (($rd_inv($s,s_node.key,$phys_ptr_cast(P#x,^s_node)) <= $rd_inv($s,s_node.key,$phys_ptr_cast($result,^s_node))));
ensures b0055 ==> (($rd_inv($s,s_node.key,$phys_ptr_cast($result,^s_node)) <= $rd_inv($s,s_node.key,$phys_ptr_cast(P#x,^s_node))));
ensures b0056 ==> (($rd_inv($s,s_node.key,$phys_ptr_cast(P#x,^s_node)) == $rd_inv($s,s_node.key,$phys_ptr_cast($result,^s_node))));
ensures b0057 ==> (($rd_inv($s,s_node.key,$phys_ptr_cast($result,^s_node)) == $rd_inv($s,s_node.key,$phys_ptr_cast(P#x,^s_node))));
ensures b0058 ==> ((F#sll_lseg_len_next($s,$phys_ptr_cast(P#x,^s_node),$phys_ptr_cast($result,^s_node)) == P#k));
ensures b0059 ==> ((F#sll_lseg_len_next($s,$phys_ptr_cast($result,^s_node),$phys_ptr_cast(P#x,^s_node)) == P#k));
ensures b0060 ==> ($intset_le(F#sll_keys($s,$phys_ptr_cast(P#x,^s_node)),$intset_singleton(P#k)));
ensures b0061 ==> ($intset_le(F#sll_keys($s,$phys_ptr_cast($result,^s_node)),$intset_singleton(P#k)));
ensures b0062 ==> ($intset_le($intset_singleton(P#k),F#sll_keys($s,$phys_ptr_cast(P#x,^s_node))));
ensures b0063 ==> ($intset_le($intset_singleton(P#k),F#sll_keys($s,$phys_ptr_cast($result,^s_node))));
ensures b0064 ==> ($intset_le(F#sll_lseg_keys($s,$phys_ptr_cast(P#x,^s_node),$phys_ptr_cast($result,^s_node)),$intset_singleton(P#k)));
ensures b0065 ==> ($intset_le(F#sll_lseg_keys($s,$phys_ptr_cast($result,^s_node),$phys_ptr_cast(P#x,^s_node)),$intset_singleton(P#k)));
ensures b0066 ==> ($intset_le($intset_singleton(P#k),F#sll_lseg_keys($s,$phys_ptr_cast(P#x,^s_node),$phys_ptr_cast($result,^s_node))));
ensures b0067 ==> ($intset_le($intset_singleton(P#k),F#sll_lseg_keys($s,$phys_ptr_cast($result,^s_node),$phys_ptr_cast(P#x,^s_node))));
ensures b0068 ==> ($intset_le(F#sll_keys($s,$phys_ptr_cast($result,^s_node)),$intset_singleton($rd_inv($s,s_node.key,$phys_ptr_cast(P#x,^s_node)))));
ensures b0069 ==> ($intset_le(F#sll_keys($s,$phys_ptr_cast(P#x,^s_node)),$intset_singleton($rd_inv($s,s_node.key,$phys_ptr_cast($result,^s_node)))));
ensures b0070 ==> ($intset_le($intset_singleton($rd_inv($s,s_node.key,$phys_ptr_cast(P#x,^s_node))),F#sll_keys($s,$phys_ptr_cast(P#x,^s_node))));
ensures b0071 ==> ($intset_le($intset_singleton($rd_inv($s,s_node.key,$phys_ptr_cast($result,^s_node))),F#sll_keys($s,$phys_ptr_cast($result,^s_node))));
ensures b0072 ==> ($intset_le(F#sll_lseg_keys($s,$phys_ptr_cast($result,^s_node),$phys_ptr_cast(P#x,^s_node)),$intset_singleton($rd_inv($s,s_node.key,$phys_ptr_cast(P#x,^s_node)))));
ensures b0073 ==> ($intset_le(F#sll_lseg_keys($s,$phys_ptr_cast(P#x,^s_node),$phys_ptr_cast($result,^s_node)),$intset_singleton($rd_inv($s,s_node.key,$phys_ptr_cast($result,^s_node)))));
ensures b0074 ==> ($intset_le($intset_singleton($rd_inv($s,s_node.key,$phys_ptr_cast(P#x,^s_node))),F#sll_lseg_keys($s,$phys_ptr_cast(P#x,^s_node),$phys_ptr_cast($result,^s_node))));
ensures b0075 ==> ($intset_le($intset_singleton($rd_inv($s,s_node.key,$phys_ptr_cast($result,^s_node))),F#sll_lseg_keys($s,$phys_ptr_cast($result,^s_node),$phys_ptr_cast(P#x,^s_node))));

  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);

// INV:PTR: P#x, $result
// INV:INT: P#k
// INV:LST: srtl
// INV:OLD: old($s)

implementation sorted_insert(P#x: $ptr, P#k: int) returns ($result: $ptr)
{
  var stmtexpr6#22: $state;
  var _dryad_S5#9: $state;
  var stmtexpr5#21: $state;
  var _dryad_S4#8: $state;
  var stmtexpr4#20: $state;
  var _dryad_S3#7: $state;
  var stmtexpr3#19: $state;
  var _dryad_S2#6: $state;
  var stmtexpr2#18: $state;
  var _dryad_S1#5: $state;
  var stmtexpr1#17: $oset;
  var stmtexpr0#16: $state;
  var _dryad_S0#4: $state;
  var L#head: $ptr;
  var stmtexpr5#15: $state;
  var _dryad_S3#3: $state;
  var stmtexpr4#14: $state;
  var _dryad_S2#2: $state;
  var stmtexpr3#13: $oset;
  var res_sll_reach#2: $oset;
  var stmtexpr2#12: $oset;
  var res_srtl_reach#1: $oset;
  var stmtexpr1#11: $state;
  var _dryad_S1#1: $state;
  var stmtexpr0#10: $state;
  var _dryad_S0#0: $state;
  var L#tmp: $ptr;
  var stmtexpr6#9: $state;
  var SL#_dryad_S5: $state;
  var stmtexpr5#8: $state;
  var SL#_dryad_S4: $state;
  var stmtexpr4#7: $state;
  var SL#_dryad_S3: $state;
  var stmtexpr3#6: $state;
  var SL#_dryad_S2: $state;
  var stmtexpr2#5: $state;
  var SL#_dryad_S1: $state;
  var stmtexpr1#4: $oset;
  var stmtexpr0#3: $state;
  var SL#_dryad_S0: $state;
  var L#tail: $ptr;
  var stmtexpr1#24: $oset;
  var stmtexpr0#23: $oset;
  var SL#_dryad_G1: $oset;
  var SL#_dryad_G0: $oset;
  var #wrTime$3^3.3: int;
  var #stackframe: int;

  anon5:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$3^3.3, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$3^3.3 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$3^3.3, (lambda #p: $ptr :: false));
    // assume true
    // assume @in_range_i4(k); 
    assume $in_range_i4(P#k);
    // assume @decreases_level_is(2147483647); 
    assume 2147483647 == $decreases_level;
    // assume true
    //  --- Dryad annotated function --- 
    // _math \oset _dryad_G0; 
    // _math \oset _dryad_G1; 
    // _dryad_G0 := srtl_reach(x); 
    call SL#_dryad_G0 := srtl_reach($phys_ptr_cast(P#x, ^s_node));
    assume $full_stop_ext(#tok$4^0.0, $s);
    // _math \oset stmtexpr0#23; 
    // stmtexpr0#23 := _dryad_G0; 
    stmtexpr0#23 := SL#_dryad_G0;
    // _dryad_G1 := _dryad_G0; 
    SL#_dryad_G1 := SL#_dryad_G0;
    // _math \oset stmtexpr1#24; 
    // stmtexpr1#24 := _dryad_G1; 
    stmtexpr1#24 := SL#_dryad_G1;
    // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
    assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
    assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
    // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
    assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
    assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
    assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
    assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
    // assume ==>(@_vcc_ptr_neq_null(x), &&(@_vcc_mutable(@state, x), @writes_check(x))); 
    assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> $mutable($s, $phys_ptr_cast(P#x, ^s_node)) && $top_writable($s, #wrTime$3^3.3, $phys_ptr_cast(P#x, ^s_node));
    assume true;
    // if (@_vcc_ptr_eq_null(x)) ...
    if ($is_null($phys_ptr_cast(P#x, ^s_node)))
    {
      anon1:
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // struct s_node* tail; 
        // _math \state _dryad_S0; 
        // _dryad_S0 := @_vcc_current_state(@state); 
        SL#_dryad_S0 := $current_state($s);
        // _math \state stmtexpr0#3; 
        // stmtexpr0#3 := _dryad_S0; 
        stmtexpr0#3 := SL#_dryad_S0;
        // tail := _vcc_alloc(@_vcc_typeof((struct s_node*)@null)); 
        call L#tail := $alloc(^s_node);
        assume $full_stop_ext(#tok$3^14.19, $s);
        // assume !(@_vcc_oset_in(tail, @_vcc_oset_union(_dryad_G0, _dryad_G1))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), $oset_union(SL#_dryad_G0, SL#_dryad_G1));
        // _dryad_G1 := @_vcc_oset_union(_dryad_G0, @_vcc_oset_singleton(tail)); 
        SL#_dryad_G1 := $oset_union(SL#_dryad_G0, $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
        // _math \oset stmtexpr1#4; 
        // stmtexpr1#4 := _dryad_G1; 
        stmtexpr1#4 := SL#_dryad_G1;
        // assume ==(glob_reach(), _dryad_G1); 
        assume F#glob_reach() == SL#_dryad_G1;
        // _math \state _dryad_S1; 
        // _dryad_S1 := @_vcc_current_state(@state); 
        SL#_dryad_S1 := $current_state($s);
        // _math \state stmtexpr2#5; 
        // stmtexpr2#5 := _dryad_S1; 
        stmtexpr2#5 := SL#_dryad_S1;
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_keys(tail), @_vcc_intset_union(sll_keys(*((tail->next))), @_vcc_intset_singleton(*((tail->key)))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tail, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_list_len_next(tail), unchecked+(sll_list_len_next(*((tail->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#tail, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(rsrtl(tail), &&(&&(rsrtl(*((tail->next))), unchecked!(@_vcc_oset_in(tail, rsrtl_reach(*((tail->next)))))), @_vcc_intset_le_one2(sll_keys(*((tail->next))), *((tail->key)))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(rsrtl_reach(tail), @_vcc_oset_union(rsrtl_reach(*((tail->next))), @_vcc_oset_singleton(tail)))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(L#tail, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll(tail), &&(sll(*((tail->next))), unchecked!(@_vcc_oset_in(tail, sll_reach(*((tail->next)))))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_reach(tail), @_vcc_oset_union(sll_reach(*((tail->next))), @_vcc_oset_singleton(tail)))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tail, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(srtl(tail), &&(&&(srtl(*((tail->next))), unchecked!(@_vcc_oset_in(tail, srtl_reach(*((tail->next)))))), @_vcc_intset_le_one1(*((tail->key)), sll_keys(*((tail->next))))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(srtl_reach(tail), @_vcc_oset_union(srtl_reach(*((tail->next))), @_vcc_oset_singleton(tail)))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(L#tail, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S0, sll_reach(x)))), ==(old(_dryad_S0, sll_keys(x)), old(_dryad_S1, sll_keys(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S0, sll_reach(x)))), ==(old(_dryad_S0, sll_list_len_next(x)), old(_dryad_S1, sll_list_len_next(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_list_len_next(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S0, rsrtl_reach(x)))), ==(old(_dryad_S0, rsrtl(x)), old(_dryad_S1, rsrtl(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S0, rsrtl_reach(x)))), ==(old(_dryad_S0, rsrtl_reach(x)), old(_dryad_S1, rsrtl_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S0, sll_reach(x)))), ==(old(_dryad_S0, sll(x)), old(_dryad_S1, sll(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#sll(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S0, sll_reach(x)))), ==(old(_dryad_S0, sll_reach(x)), old(_dryad_S1, sll_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S0, srtl_reach(x)))), ==(old(_dryad_S0, srtl(x)), old(_dryad_S1, srtl(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#srtl(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S0, srtl_reach(x)))), ==(old(_dryad_S0, srtl_reach(x)), old(_dryad_S1, srtl_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#srtl_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume @_vcc_ptr_neq_null(tail); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node));
        // _math \state _dryad_S2; 
        // _dryad_S2 := @_vcc_current_state(@state); 
        SL#_dryad_S2 := $current_state($s);
        // _math \state stmtexpr3#6; 
        // stmtexpr3#6 := _dryad_S2; 
        stmtexpr3#6 := SL#_dryad_S2;
        // assert @prim_writes_check((tail->key)); 
        assert $writable_prim($s, #wrTime$3^3.3, $dot($phys_ptr_cast(L#tail, ^s_node), s_node.key));
        // *(tail->key) := k; 
        call $write_int(s_node.key, $phys_ptr_cast(L#tail, ^s_node), P#k);
        assume $full_stop_ext(#tok$3^17.3, $s);
        // _math \state _dryad_S3; 
        // _dryad_S3 := @_vcc_current_state(@state); 
        SL#_dryad_S3 := $current_state($s);
        // _math \state stmtexpr4#7; 
        // stmtexpr4#7 := _dryad_S3; 
        stmtexpr4#7 := SL#_dryad_S3;
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, sll_reach(*((tail->next)))))), ==(old(_dryad_S2, sll_keys(*((tail->next)))), old(_dryad_S3, sll_keys(*((tail->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#sll_keys(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#sll_keys(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, sll_reach(*((tail->next)))))), ==(old(_dryad_S2, sll_list_len_next(*((tail->next)))), old(_dryad_S3, sll_list_len_next(*((tail->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, rsrtl_reach(*((tail->next)))))), ==(old(_dryad_S2, rsrtl(*((tail->next)))), old(_dryad_S3, rsrtl(*((tail->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#rsrtl(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#rsrtl(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, rsrtl_reach(*((tail->next)))))), ==(old(_dryad_S2, rsrtl_reach(*((tail->next)))), old(_dryad_S3, rsrtl_reach(*((tail->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#rsrtl_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#rsrtl_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, sll_reach(*((tail->next)))))), ==(old(_dryad_S2, sll(*((tail->next)))), old(_dryad_S3, sll(*((tail->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#sll(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#sll(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, sll_reach(*((tail->next)))))), ==(old(_dryad_S2, sll_reach(*((tail->next)))), old(_dryad_S3, sll_reach(*((tail->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#sll_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, srtl_reach(*((tail->next)))))), ==(old(_dryad_S2, srtl(*((tail->next)))), old(_dryad_S3, srtl(*((tail->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#srtl(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#srtl(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, srtl_reach(*((tail->next)))))), ==(old(_dryad_S2, srtl_reach(*((tail->next)))), old(_dryad_S3, srtl_reach(*((tail->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) ==> F#srtl_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) == F#srtl_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node));
        // assume ==(old(_dryad_S2, sll_list_len_next(tail)), old(_dryad_S3, sll_list_len_next(tail))); 
        assume F#sll_list_len_next(SL#_dryad_S2, $phys_ptr_cast(L#tail, ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $phys_ptr_cast(L#tail, ^s_node));
        // assume ==(old(_dryad_S2, rsrtl_reach(tail)), old(_dryad_S3, rsrtl_reach(tail))); 
        assume F#rsrtl_reach(SL#_dryad_S2, $phys_ptr_cast(L#tail, ^s_node)) == F#rsrtl_reach(SL#_dryad_S3, $phys_ptr_cast(L#tail, ^s_node));
        // assume ==(old(_dryad_S2, sll(tail)), old(_dryad_S3, sll(tail))); 
        assume F#sll(SL#_dryad_S2, $phys_ptr_cast(L#tail, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(L#tail, ^s_node));
        // assume ==(old(_dryad_S2, sll_reach(tail)), old(_dryad_S3, sll_reach(tail))); 
        assume F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(L#tail, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(L#tail, ^s_node));
        // assume ==(old(_dryad_S2, srtl_reach(tail)), old(_dryad_S3, srtl_reach(tail))); 
        assume F#srtl_reach(SL#_dryad_S2, $phys_ptr_cast(L#tail, ^s_node)) == F#srtl_reach(SL#_dryad_S3, $phys_ptr_cast(L#tail, ^s_node));
        // assume ==(old(_dryad_S2, sll_list_len_next(x)), old(_dryad_S3, sll_list_len_next(x))); 
        assume F#sll_list_len_next(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==(old(_dryad_S2, rsrtl_reach(x)), old(_dryad_S3, rsrtl_reach(x))); 
        assume F#rsrtl_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==(old(_dryad_S2, sll(x)), old(_dryad_S3, sll(x))); 
        assume F#sll(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==(old(_dryad_S2, sll_reach(x)), old(_dryad_S3, sll_reach(x))); 
        assume F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==(old(_dryad_S2, srtl_reach(x)), old(_dryad_S3, srtl_reach(x))); 
        assume F#srtl_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#srtl_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, sll_reach(x)))), ==(old(_dryad_S2, sll_keys(x)), old(_dryad_S3, sll_keys(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, sll_reach(x)))), ==(old(_dryad_S2, sll_list_len_next(x)), old(_dryad_S3, sll_list_len_next(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll_list_len_next(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, rsrtl_reach(x)))), ==(old(_dryad_S2, rsrtl(x)), old(_dryad_S3, rsrtl(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, rsrtl_reach(x)))), ==(old(_dryad_S2, rsrtl_reach(x)), old(_dryad_S3, rsrtl_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, sll_reach(x)))), ==(old(_dryad_S2, sll(x)), old(_dryad_S3, sll(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, sll_reach(x)))), ==(old(_dryad_S2, sll_reach(x)), old(_dryad_S3, sll_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, srtl_reach(x)))), ==(old(_dryad_S2, srtl(x)), old(_dryad_S3, srtl(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#srtl(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S2, srtl_reach(x)))), ==(old(_dryad_S2, srtl_reach(x)), old(_dryad_S3, srtl_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#srtl_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(tail, x)), ==(*((x->key)), old(_dryad_S2, *((x->key))))); 
        assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)) == $rd_inv(SL#_dryad_S2, s_node.key, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(tail, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S2, *((x->next))))); 
        assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node);
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_keys(tail), @_vcc_intset_union(sll_keys(*((tail->next))), @_vcc_intset_singleton(*((tail->key)))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tail, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(rsrtl(tail), &&(&&(rsrtl(*((tail->next))), unchecked!(@_vcc_oset_in(tail, rsrtl_reach(*((tail->next)))))), @_vcc_intset_le_one2(sll_keys(*((tail->next))), *((tail->key)))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(srtl(tail), &&(&&(srtl(*((tail->next))), unchecked!(@_vcc_oset_in(tail, srtl_reach(*((tail->next)))))), @_vcc_intset_le_one1(*((tail->key)), sll_keys(*((tail->next))))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))));
        // _math \state _dryad_S4; 
        // _dryad_S4 := @_vcc_current_state(@state); 
        SL#_dryad_S4 := $current_state($s);
        // _math \state stmtexpr5#8; 
        // stmtexpr5#8 := _dryad_S4; 
        stmtexpr5#8 := SL#_dryad_S4;
        // assert @prim_writes_check((tail->next)); 
        assert $writable_prim($s, #wrTime$3^3.3, $dot($phys_ptr_cast(L#tail, ^s_node), s_node.next));
        // *(tail->next) := (struct s_node*)@null; 
        call $write_int(s_node.next, $phys_ptr_cast(L#tail, ^s_node), $ptr_to_int($phys_ptr_cast($null, ^s_node)));
        assume $full_stop_ext(#tok$3^18.3, $s);
        // _math \state _dryad_S5; 
        // _dryad_S5 := @_vcc_current_state(@state); 
        SL#_dryad_S5 := $current_state($s);
        // _math \state stmtexpr6#9; 
        // stmtexpr6#9 := _dryad_S5; 
        stmtexpr6#9 := SL#_dryad_S5;
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S4, sll_reach(x)))), ==(old(_dryad_S4, sll_keys(x)), old(_dryad_S5, sll_keys(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S4, sll_reach(x)))), ==(old(_dryad_S4, sll_list_len_next(x)), old(_dryad_S5, sll_list_len_next(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_list_len_next(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_list_len_next(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S4, rsrtl_reach(x)))), ==(old(_dryad_S4, rsrtl(x)), old(_dryad_S5, rsrtl(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S4, rsrtl_reach(x)))), ==(old(_dryad_S4, rsrtl_reach(x)), old(_dryad_S5, rsrtl_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl_reach(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S4, sll_reach(x)))), ==(old(_dryad_S4, sll(x)), old(_dryad_S5, sll(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#sll(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S4, sll_reach(x)))), ==(old(_dryad_S4, sll_reach(x)), old(_dryad_S5, sll_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S4, srtl_reach(x)))), ==(old(_dryad_S4, srtl(x)), old(_dryad_S5, srtl(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#srtl(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(tail, old(_dryad_S4, srtl_reach(x)))), ==(old(_dryad_S4, srtl_reach(x)), old(_dryad_S5, srtl_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#srtl_reach(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(tail, x)), ==(*((x->key)), old(_dryad_S4, *((x->key))))); 
        assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)) == $rd_inv(SL#_dryad_S4, s_node.key, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(tail, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S4, *((x->next))))); 
        assume !($phys_ptr_cast(L#tail, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S4, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node);
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_keys(tail), @_vcc_intset_union(sll_keys(*((tail->next))), @_vcc_intset_singleton(*((tail->key)))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tail, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_list_len_next(tail), unchecked+(sll_list_len_next(*((tail->next))), 1))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#tail, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), 1);
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(rsrtl(tail), &&(&&(rsrtl(*((tail->next))), unchecked!(@_vcc_oset_in(tail, rsrtl_reach(*((tail->next)))))), @_vcc_intset_le_one2(sll_keys(*((tail->next))), *((tail->key)))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(rsrtl_reach(tail), @_vcc_oset_union(rsrtl_reach(*((tail->next))), @_vcc_oset_singleton(tail)))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(L#tail, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll(tail), &&(sll(*((tail->next))), unchecked!(@_vcc_oset_in(tail, sll_reach(*((tail->next)))))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(sll_reach(tail), @_vcc_oset_union(sll_reach(*((tail->next))), @_vcc_oset_singleton(tail)))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tail, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(srtl(tail), &&(&&(srtl(*((tail->next))), unchecked!(@_vcc_oset_in(tail, srtl_reach(*((tail->next)))))), @_vcc_intset_le_one1(*((tail->key)), sll_keys(*((tail->next))))))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(L#tail, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tail, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(L#tail, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node))));
        // assume ==>(@_vcc_ptr_neq_null(tail), ==(srtl_reach(tail), @_vcc_oset_union(srtl_reach(*((tail->next))), @_vcc_oset_singleton(tail)))); 
        assume $non_null($phys_ptr_cast(L#tail, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(L#tail, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tail, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tail, ^s_node)));
        // return tail; 
        $result := $phys_ptr_cast(L#tail, ^s_node);
        assume true;
        assert $position_marker();
        goto #exit;
    }
    else
    {
      anon4:
        // assert @reads_check_normal((x->key)); 
        assert $thread_local($s, $phys_ptr_cast(P#x, ^s_node));
        assume true;
        // if (>(k, *((x->key)))) ...
        if (P#k > $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))
        {
          anon2:
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // struct s_node* tmp; 
            // _math \state _dryad_S0#0; 
            // _dryad_S0#0 := @_vcc_current_state(@state); 
            _dryad_S0#0 := $current_state($s);
            // _math \state stmtexpr0#10; 
            // stmtexpr0#10 := _dryad_S0#0; 
            stmtexpr0#10 := _dryad_S0#0;
            // non-pure function
            // assert @reads_check_normal((x->next)); 
            assert $thread_local($s, $phys_ptr_cast(P#x, ^s_node));
            // tmp := sorted_insert(*((x->next)), k); 
            call L#tmp := sorted_insert($rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node), P#k);
            assume $full_stop_ext(#tok$3^23.18, $s);
            // _math \state _dryad_S1#1; 
            // _dryad_S1#1 := @_vcc_current_state(@state); 
            _dryad_S1#1 := $current_state($s);
            // _math \state stmtexpr1#11; 
            // stmtexpr1#11 := _dryad_S1#1; 
            stmtexpr1#11 := _dryad_S1#1;
            // assume @_vcc_oset_disjoint(srtl_reach(tmp), @_vcc_oset_diff(_dryad_G1, old(_dryad_S0#0, srtl_reach(*((x->next)))))); 
            assume $oset_disjoint(F#srtl_reach($s, $phys_ptr_cast(L#tmp, ^s_node)), $oset_diff(SL#_dryad_G1, F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume @_vcc_oset_disjoint(sll_reach(tmp), @_vcc_oset_diff(_dryad_G1, old(_dryad_S0#0, srtl_reach(*((x->next)))))); 
            assume $oset_disjoint(F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)), $oset_diff(SL#_dryad_G1, F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // _math \oset res_srtl_reach#1; 
            // res_srtl_reach#1 := srtl_reach(tmp); 
            call res_srtl_reach#1 := srtl_reach($phys_ptr_cast(L#tmp, ^s_node));
            assume $full_stop_ext(#tok$4^0.0, $s);
            // _dryad_G1 := @_vcc_oset_union(res_srtl_reach#1, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S0#0, srtl_reach(*((x->next))))))); 
            SL#_dryad_G1 := $oset_union(res_srtl_reach#1, $oset_diff(SL#_dryad_G1, F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // _math \oset stmtexpr2#12; 
            // stmtexpr2#12 := _dryad_G1; 
            stmtexpr2#12 := SL#_dryad_G1;
            // _math \oset res_sll_reach#2; 
            // res_sll_reach#2 := sll_reach(tmp); 
            call res_sll_reach#2 := sll_reach($phys_ptr_cast(L#tmp, ^s_node));
            assume $full_stop_ext(#tok$4^0.0, $s);
            // _dryad_G1 := @_vcc_oset_union(res_sll_reach#2, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S0#0, srtl_reach(*((x->next))))))); 
            SL#_dryad_G1 := $oset_union(res_sll_reach#2, $oset_diff(SL#_dryad_G1, F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // _math \oset stmtexpr3#13; 
            // stmtexpr3#13 := _dryad_G1; 
            stmtexpr3#13 := SL#_dryad_G1;
            // assume ==(glob_reach(), _dryad_G1); 
            assume F#glob_reach() == SL#_dryad_G1;
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, srtl_reach(*((x->next)))), old(_dryad_S0#0, sll_reach(x))), ==(old(_dryad_S0#0, sll_keys(x)), old(_dryad_S1#1, sll_keys(x)))); 
            assume $oset_disjoint(F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#sll_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, srtl_reach(*((x->next)))), old(_dryad_S0#0, sll_reach(x))), ==(old(_dryad_S0#0, sll_list_len_next(x)), old(_dryad_S1#1, sll_list_len_next(x)))); 
            assume $oset_disjoint(F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#sll_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_list_len_next(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_list_len_next(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, srtl_reach(*((x->next)))), old(_dryad_S0#0, rsrtl_reach(x))), ==(old(_dryad_S0#0, rsrtl(x)), old(_dryad_S1#1, rsrtl(x)))); 
            assume $oset_disjoint(F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#rsrtl_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, srtl_reach(*((x->next)))), old(_dryad_S0#0, rsrtl_reach(x))), ==(old(_dryad_S0#0, rsrtl_reach(x)), old(_dryad_S1#1, rsrtl_reach(x)))); 
            assume $oset_disjoint(F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#rsrtl_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl_reach(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, srtl_reach(*((x->next)))), old(_dryad_S0#0, sll_reach(x))), ==(old(_dryad_S0#0, sll(x)), old(_dryad_S1#1, sll(x)))); 
            assume $oset_disjoint(F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#sll_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#sll(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, srtl_reach(*((x->next)))), old(_dryad_S0#0, sll_reach(x))), ==(old(_dryad_S0#0, sll_reach(x)), old(_dryad_S1#1, sll_reach(x)))); 
            assume $oset_disjoint(F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#sll_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, srtl_reach(*((x->next)))), old(_dryad_S0#0, srtl_reach(x))), ==(old(_dryad_S0#0, srtl(x)), old(_dryad_S1#1, srtl(x)))); 
            assume $oset_disjoint(F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#srtl_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#srtl(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, srtl_reach(*((x->next)))), old(_dryad_S0#0, srtl_reach(x))), ==(old(_dryad_S0#0, srtl_reach(x)), old(_dryad_S1#1, srtl_reach(x)))); 
            assume $oset_disjoint(F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#srtl_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#srtl_reach(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll_keys(tmp), @_vcc_intset_union(sll_keys(*((tmp->next))), @_vcc_intset_singleton(*((tmp->key)))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tmp, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll_list_len_next(tmp), unchecked+(sll_list_len_next(*((tmp->next))), 1))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#tmp, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(rsrtl(tmp), &&(&&(rsrtl(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, rsrtl_reach(*((tmp->next)))))), @_vcc_intset_le_one2(sll_keys(*((tmp->next))), *((tmp->key)))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(rsrtl_reach(tmp), @_vcc_oset_union(rsrtl_reach(*((tmp->next))), @_vcc_oset_singleton(tmp)))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll(tmp), &&(sll(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, sll_reach(*((tmp->next)))))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll_reach(tmp), @_vcc_oset_union(sll_reach(*((tmp->next))), @_vcc_oset_singleton(tmp)))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(srtl(tmp), &&(&&(srtl(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, srtl_reach(*((tmp->next)))))), @_vcc_intset_le_one1(*((tmp->key)), sll_keys(*((tmp->next))))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(srtl_reach(tmp), @_vcc_oset_union(srtl_reach(*((tmp->next))), @_vcc_oset_singleton(tmp)))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0#0, srtl_reach(*((x->next)))))), ==(*((x->key)), old(_dryad_S0#0, *((x->key))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)) == $rd_inv(_dryad_S0#0, s_node.key, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0#0, srtl_reach(*((x->next)))))), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S0#0, *((x->next))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node) == $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node);
            // _math \state _dryad_S2#2; 
            // _dryad_S2#2 := @_vcc_current_state(@state); 
            _dryad_S2#2 := $current_state($s);
            // _math \state stmtexpr4#14; 
            // stmtexpr4#14 := _dryad_S2#2; 
            stmtexpr4#14 := _dryad_S2#2;
            // assert @prim_writes_check((x->next)); 
            assert $writable_prim($s, #wrTime$3^3.3, $dot($phys_ptr_cast(P#x, ^s_node), s_node.next));
            // *(x->next) := tmp; 
            call $write_int(s_node.next, $phys_ptr_cast(P#x, ^s_node), $ptr_to_int($phys_ptr_cast(L#tmp, ^s_node)));
            assume $full_stop_ext(#tok$3^25.3, $s);
            // _math \state _dryad_S3#3; 
            // _dryad_S3#3 := @_vcc_current_state(@state); 
            _dryad_S3#3 := $current_state($s);
            // _math \state stmtexpr5#15; 
            // stmtexpr5#15 := _dryad_S3#3; 
            stmtexpr5#15 := _dryad_S3#3;
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, sll_reach(tmp)))), ==(old(_dryad_S2#2, sll_keys(tmp)), old(_dryad_S3#3, sll_keys(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#sll_keys(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#sll_keys(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, sll_reach(tmp)))), ==(old(_dryad_S2#2, sll_list_len_next(tmp)), old(_dryad_S3#3, sll_list_len_next(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#sll_list_len_next(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#sll_list_len_next(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, rsrtl_reach(tmp)))), ==(old(_dryad_S2#2, rsrtl(tmp)), old(_dryad_S3#3, rsrtl(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#rsrtl(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#rsrtl(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, rsrtl_reach(tmp)))), ==(old(_dryad_S2#2, rsrtl_reach(tmp)), old(_dryad_S3#3, rsrtl_reach(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#rsrtl_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#rsrtl_reach(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, sll_reach(tmp)))), ==(old(_dryad_S2#2, sll(tmp)), old(_dryad_S3#3, sll(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#sll(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#sll(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, sll_reach(tmp)))), ==(old(_dryad_S2#2, sll_reach(tmp)), old(_dryad_S3#3, sll_reach(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#sll_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#sll_reach(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, srtl_reach(tmp)))), ==(old(_dryad_S2#2, srtl(tmp)), old(_dryad_S3#3, srtl(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#srtl(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#srtl(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, srtl_reach(tmp)))), ==(old(_dryad_S2#2, srtl_reach(tmp)), old(_dryad_S3#3, srtl_reach(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#srtl_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#srtl_reach(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, tmp)), ==(*((tmp->key)), old(_dryad_S2#2, *((tmp->key))))); 
            assume !($phys_ptr_cast(P#x, ^s_node) == $phys_ptr_cast(L#tmp, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node)) == $rd_inv(_dryad_S2#2, s_node.key, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, tmp)), @_vcc_ptr_eq_pure(*((tmp->next)), old(_dryad_S2#2, *((tmp->next))))); 
            assume !($phys_ptr_cast(P#x, ^s_node) == $phys_ptr_cast(L#tmp, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node) == $rd_phys_ptr(_dryad_S2#2, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node);
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll_keys(tmp), @_vcc_intset_union(sll_keys(*((tmp->next))), @_vcc_intset_singleton(*((tmp->key)))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tmp, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll_list_len_next(tmp), unchecked+(sll_list_len_next(*((tmp->next))), 1))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#tmp, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(rsrtl(tmp), &&(&&(rsrtl(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, rsrtl_reach(*((tmp->next)))))), @_vcc_intset_le_one2(sll_keys(*((tmp->next))), *((tmp->key)))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(rsrtl_reach(tmp), @_vcc_oset_union(rsrtl_reach(*((tmp->next))), @_vcc_oset_singleton(tmp)))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll(tmp), &&(sll(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, sll_reach(*((tmp->next)))))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll_reach(tmp), @_vcc_oset_union(sll_reach(*((tmp->next))), @_vcc_oset_singleton(tmp)))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(srtl(tmp), &&(&&(srtl(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, srtl_reach(*((tmp->next)))))), @_vcc_intset_le_one1(*((tmp->key)), sll_keys(*((tmp->next))))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(srtl_reach(tmp), @_vcc_oset_union(srtl_reach(*((tmp->next))), @_vcc_oset_singleton(tmp)))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll_keys(tmp), @_vcc_intset_union(sll_keys(*((tmp->next))), @_vcc_intset_singleton(*((tmp->key)))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tmp, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll_list_len_next(tmp), unchecked+(sll_list_len_next(*((tmp->next))), 1))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#tmp, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(rsrtl(tmp), &&(&&(rsrtl(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, rsrtl_reach(*((tmp->next)))))), @_vcc_intset_le_one2(sll_keys(*((tmp->next))), *((tmp->key)))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(rsrtl_reach(tmp), @_vcc_oset_union(rsrtl_reach(*((tmp->next))), @_vcc_oset_singleton(tmp)))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll(tmp), &&(sll(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, sll_reach(*((tmp->next)))))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(sll_reach(tmp), @_vcc_oset_union(sll_reach(*((tmp->next))), @_vcc_oset_singleton(tmp)))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(srtl(tmp), &&(&&(srtl(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, srtl_reach(*((tmp->next)))))), @_vcc_intset_le_one1(*((tmp->key)), sll_keys(*((tmp->next))))))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(tmp), ==(srtl_reach(tmp), @_vcc_oset_union(srtl_reach(*((tmp->next))), @_vcc_oset_singleton(tmp)))); 
            assume $non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node)));
            // return x; 
            $result := $phys_ptr_cast(P#x, ^s_node);
            assume true;
            assert $position_marker();
            goto #exit;
        }
        else
        {
          anon3:
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // struct s_node* head; 
            // _math \state _dryad_S0#4; 
            // _dryad_S0#4 := @_vcc_current_state(@state); 
            _dryad_S0#4 := $current_state($s);
            // _math \state stmtexpr0#16; 
            // stmtexpr0#16 := _dryad_S0#4; 
            stmtexpr0#16 := _dryad_S0#4;
            // head := _vcc_alloc(@_vcc_typeof((struct s_node*)@null)); 
            call L#head := $alloc(^s_node);
            assume $full_stop_ext(#tok$3^31.19, $s);
            // assume !(@_vcc_oset_in(head, @_vcc_oset_union(_dryad_G0, _dryad_G1))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), $oset_union(SL#_dryad_G0, SL#_dryad_G1));
            // _dryad_G1 := @_vcc_oset_union(_dryad_G0, @_vcc_oset_singleton(head)); 
            SL#_dryad_G1 := $oset_union(SL#_dryad_G0, $oset_singleton($phys_ptr_cast(L#head, ^s_node)));
            // _math \oset stmtexpr1#17; 
            // stmtexpr1#17 := _dryad_G1; 
            stmtexpr1#17 := SL#_dryad_G1;
            // assume ==(glob_reach(), _dryad_G1); 
            assume F#glob_reach() == SL#_dryad_G1;
            // _math \state _dryad_S1#5; 
            // _dryad_S1#5 := @_vcc_current_state(@state); 
            _dryad_S1#5 := $current_state($s);
            // _math \state stmtexpr2#18; 
            // stmtexpr2#18 := _dryad_S1#5; 
            stmtexpr2#18 := _dryad_S1#5;
            // assume ==>(@_vcc_ptr_neq_null(head), ==(sll_keys(head), @_vcc_intset_union(sll_keys(*((head->next))), @_vcc_intset_singleton(*((head->key)))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#head, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#head, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(sll_list_len_next(head), unchecked+(sll_list_len_next(*((head->next))), 1))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#head, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(head), ==(rsrtl(head), &&(&&(rsrtl(*((head->next))), unchecked!(@_vcc_oset_in(head, rsrtl_reach(*((head->next)))))), @_vcc_intset_le_one2(sll_keys(*((head->next))), *((head->key)))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(L#head, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(L#head, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(rsrtl_reach(head), @_vcc_oset_union(rsrtl_reach(*((head->next))), @_vcc_oset_singleton(head)))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(L#head, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#head, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(sll(head), &&(sll(*((head->next))), unchecked!(@_vcc_oset_in(head, sll_reach(*((head->next)))))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#head, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(sll_reach(head), @_vcc_oset_union(sll_reach(*((head->next))), @_vcc_oset_singleton(head)))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#head, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#head, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(srtl(head), &&(&&(srtl(*((head->next))), unchecked!(@_vcc_oset_in(head, srtl_reach(*((head->next)))))), @_vcc_intset_le_one1(*((head->key)), sll_keys(*((head->next))))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(L#head, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(L#head, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(srtl_reach(head), @_vcc_oset_union(srtl_reach(*((head->next))), @_vcc_oset_singleton(head)))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(L#head, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#head, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S0#4, sll_reach(x)))), ==(old(_dryad_S0#4, sll_keys(x)), old(_dryad_S1#5, sll_keys(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S0#4, sll_reach(x)))), ==(old(_dryad_S0#4, sll_list_len_next(x)), old(_dryad_S1#5, sll_list_len_next(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_list_len_next(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_list_len_next(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S0#4, rsrtl_reach(x)))), ==(old(_dryad_S0#4, rsrtl(x)), old(_dryad_S1#5, rsrtl(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S0#4, rsrtl_reach(x)))), ==(old(_dryad_S0#4, rsrtl_reach(x)), old(_dryad_S1#5, rsrtl_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl_reach(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S0#4, sll_reach(x)))), ==(old(_dryad_S0#4, sll(x)), old(_dryad_S1#5, sll(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#sll(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S0#4, sll_reach(x)))), ==(old(_dryad_S0#4, sll_reach(x)), old(_dryad_S1#5, sll_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S0#4, srtl_reach(x)))), ==(old(_dryad_S0#4, srtl(x)), old(_dryad_S1#5, srtl(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#srtl(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S0#4, srtl_reach(x)))), ==(old(_dryad_S0#4, srtl_reach(x)), old(_dryad_S1#5, srtl_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#srtl_reach(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume @_vcc_ptr_neq_null(head); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node));
            // _math \state _dryad_S2#6; 
            // _dryad_S2#6 := @_vcc_current_state(@state); 
            _dryad_S2#6 := $current_state($s);
            // _math \state stmtexpr3#19; 
            // stmtexpr3#19 := _dryad_S2#6; 
            stmtexpr3#19 := _dryad_S2#6;
            // assert @prim_writes_check((head->key)); 
            assert $writable_prim($s, #wrTime$3^3.3, $dot($phys_ptr_cast(L#head, ^s_node), s_node.key));
            // *(head->key) := k; 
            call $write_int(s_node.key, $phys_ptr_cast(L#head, ^s_node), P#k);
            assume $full_stop_ext(#tok$3^34.3, $s);
            // _math \state _dryad_S3#7; 
            // _dryad_S3#7 := @_vcc_current_state(@state); 
            _dryad_S3#7 := $current_state($s);
            // _math \state stmtexpr4#20; 
            // stmtexpr4#20 := _dryad_S3#7; 
            stmtexpr4#20 := _dryad_S3#7;
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, sll_reach(*((head->next)))))), ==(old(_dryad_S2#6, sll_keys(*((head->next)))), old(_dryad_S3#7, sll_keys(*((head->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) ==> F#sll_keys(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) == F#sll_keys(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, sll_reach(*((head->next)))))), ==(old(_dryad_S2#6, sll_list_len_next(*((head->next)))), old(_dryad_S3#7, sll_list_len_next(*((head->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) ==> F#sll_list_len_next(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) == F#sll_list_len_next(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, rsrtl_reach(*((head->next)))))), ==(old(_dryad_S2#6, rsrtl(*((head->next)))), old(_dryad_S3#7, rsrtl(*((head->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) ==> F#rsrtl(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) == F#rsrtl(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, rsrtl_reach(*((head->next)))))), ==(old(_dryad_S2#6, rsrtl_reach(*((head->next)))), old(_dryad_S3#7, rsrtl_reach(*((head->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) ==> F#rsrtl_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) == F#rsrtl_reach(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, sll_reach(*((head->next)))))), ==(old(_dryad_S2#6, sll(*((head->next)))), old(_dryad_S3#7, sll(*((head->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) ==> F#sll(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) == F#sll(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, sll_reach(*((head->next)))))), ==(old(_dryad_S2#6, sll_reach(*((head->next)))), old(_dryad_S3#7, sll_reach(*((head->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) ==> F#sll_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) == F#sll_reach(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, srtl_reach(*((head->next)))))), ==(old(_dryad_S2#6, srtl(*((head->next)))), old(_dryad_S3#7, srtl(*((head->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) ==> F#srtl(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) == F#srtl(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, srtl_reach(*((head->next)))))), ==(old(_dryad_S2#6, srtl_reach(*((head->next)))), old(_dryad_S3#7, srtl_reach(*((head->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) ==> F#srtl_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) == F#srtl_reach(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node));
            // assume ==(old(_dryad_S2#6, sll_list_len_next(head)), old(_dryad_S3#7, sll_list_len_next(head))); 
            assume F#sll_list_len_next(_dryad_S2#6, $phys_ptr_cast(L#head, ^s_node)) == F#sll_list_len_next(_dryad_S3#7, $phys_ptr_cast(L#head, ^s_node));
            // assume ==(old(_dryad_S2#6, rsrtl_reach(head)), old(_dryad_S3#7, rsrtl_reach(head))); 
            assume F#rsrtl_reach(_dryad_S2#6, $phys_ptr_cast(L#head, ^s_node)) == F#rsrtl_reach(_dryad_S3#7, $phys_ptr_cast(L#head, ^s_node));
            // assume ==(old(_dryad_S2#6, sll(head)), old(_dryad_S3#7, sll(head))); 
            assume F#sll(_dryad_S2#6, $phys_ptr_cast(L#head, ^s_node)) == F#sll(_dryad_S3#7, $phys_ptr_cast(L#head, ^s_node));
            // assume ==(old(_dryad_S2#6, sll_reach(head)), old(_dryad_S3#7, sll_reach(head))); 
            assume F#sll_reach(_dryad_S2#6, $phys_ptr_cast(L#head, ^s_node)) == F#sll_reach(_dryad_S3#7, $phys_ptr_cast(L#head, ^s_node));
            // assume ==(old(_dryad_S2#6, srtl_reach(head)), old(_dryad_S3#7, srtl_reach(head))); 
            assume F#srtl_reach(_dryad_S2#6, $phys_ptr_cast(L#head, ^s_node)) == F#srtl_reach(_dryad_S3#7, $phys_ptr_cast(L#head, ^s_node));
            // assume ==(old(_dryad_S2#6, sll_list_len_next(x)), old(_dryad_S3#7, sll_list_len_next(x))); 
            assume F#sll_list_len_next(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll_list_len_next(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==(old(_dryad_S2#6, rsrtl_reach(x)), old(_dryad_S3#7, rsrtl_reach(x))); 
            assume F#rsrtl_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl_reach(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==(old(_dryad_S2#6, sll(x)), old(_dryad_S3#7, sll(x))); 
            assume F#sll(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==(old(_dryad_S2#6, sll_reach(x)), old(_dryad_S3#7, sll_reach(x))); 
            assume F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==(old(_dryad_S2#6, srtl_reach(x)), old(_dryad_S3#7, srtl_reach(x))); 
            assume F#srtl_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#srtl_reach(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, sll_reach(x)))), ==(old(_dryad_S2#6, sll_keys(x)), old(_dryad_S3#7, sll_keys(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, sll_reach(x)))), ==(old(_dryad_S2#6, sll_list_len_next(x)), old(_dryad_S3#7, sll_list_len_next(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_list_len_next(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll_list_len_next(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, rsrtl_reach(x)))), ==(old(_dryad_S2#6, rsrtl(x)), old(_dryad_S3#7, rsrtl(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, rsrtl_reach(x)))), ==(old(_dryad_S2#6, rsrtl_reach(x)), old(_dryad_S3#7, rsrtl_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl_reach(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, sll_reach(x)))), ==(old(_dryad_S2#6, sll(x)), old(_dryad_S3#7, sll(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, sll_reach(x)))), ==(old(_dryad_S2#6, sll_reach(x)), old(_dryad_S3#7, sll_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, srtl_reach(x)))), ==(old(_dryad_S2#6, srtl(x)), old(_dryad_S3#7, srtl(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#srtl(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S2#6, srtl_reach(x)))), ==(old(_dryad_S2#6, srtl_reach(x)), old(_dryad_S3#7, srtl_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#srtl_reach(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(head, x)), ==(*((x->key)), old(_dryad_S2#6, *((x->key))))); 
            assume !($phys_ptr_cast(L#head, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)) == $rd_inv(_dryad_S2#6, s_node.key, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(head, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S2#6, *((x->next))))); 
            assume !($phys_ptr_cast(L#head, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node) == $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(sll_keys(head), @_vcc_intset_union(sll_keys(*((head->next))), @_vcc_intset_singleton(*((head->key)))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#head, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#head, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(rsrtl(head), &&(&&(rsrtl(*((head->next))), unchecked!(@_vcc_oset_in(head, rsrtl_reach(*((head->next)))))), @_vcc_intset_le_one2(sll_keys(*((head->next))), *((head->key)))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(L#head, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(L#head, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(srtl(head), &&(&&(srtl(*((head->next))), unchecked!(@_vcc_oset_in(head, srtl_reach(*((head->next)))))), @_vcc_intset_le_one1(*((head->key)), sll_keys(*((head->next))))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(L#head, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(L#head, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))));
            // _math \state _dryad_S4#8; 
            // _dryad_S4#8 := @_vcc_current_state(@state); 
            _dryad_S4#8 := $current_state($s);
            // _math \state stmtexpr5#21; 
            // stmtexpr5#21 := _dryad_S4#8; 
            stmtexpr5#21 := _dryad_S4#8;
            // assert @prim_writes_check((head->next)); 
            assert $writable_prim($s, #wrTime$3^3.3, $dot($phys_ptr_cast(L#head, ^s_node), s_node.next));
            // *(head->next) := x; 
            call $write_int(s_node.next, $phys_ptr_cast(L#head, ^s_node), $ptr_to_int($phys_ptr_cast(P#x, ^s_node)));
            assume $full_stop_ext(#tok$3^35.3, $s);
            // _math \state _dryad_S5#9; 
            // _dryad_S5#9 := @_vcc_current_state(@state); 
            _dryad_S5#9 := $current_state($s);
            // _math \state stmtexpr6#22; 
            // stmtexpr6#22 := _dryad_S5#9; 
            stmtexpr6#22 := _dryad_S5#9;
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S4#8, sll_reach(x)))), ==(old(_dryad_S4#8, sll_keys(x)), old(_dryad_S5#9, sll_keys(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S4#8, sll_reach(x)))), ==(old(_dryad_S4#8, sll_list_len_next(x)), old(_dryad_S5#9, sll_list_len_next(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_list_len_next(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#sll_list_len_next(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S4#8, rsrtl_reach(x)))), ==(old(_dryad_S4#8, rsrtl(x)), old(_dryad_S5#9, rsrtl(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S4#8, rsrtl_reach(x)))), ==(old(_dryad_S4#8, rsrtl_reach(x)), old(_dryad_S5#9, rsrtl_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#rsrtl_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#rsrtl_reach(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S4#8, sll_reach(x)))), ==(old(_dryad_S4#8, sll(x)), old(_dryad_S5#9, sll(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#sll(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S4#8, sll_reach(x)))), ==(old(_dryad_S4#8, sll_reach(x)), old(_dryad_S5#9, sll_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S4#8, srtl_reach(x)))), ==(old(_dryad_S4#8, srtl(x)), old(_dryad_S5#9, srtl(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#srtl(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(head, old(_dryad_S4#8, srtl_reach(x)))), ==(old(_dryad_S4#8, srtl_reach(x)), old(_dryad_S5#9, srtl_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#srtl_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#srtl_reach(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(head, x)), ==(*((x->key)), old(_dryad_S4#8, *((x->key))))); 
            assume !($phys_ptr_cast(L#head, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)) == $rd_inv(_dryad_S4#8, s_node.key, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(head, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S4#8, *((x->next))))); 
            assume !($phys_ptr_cast(L#head, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node) == $rd_phys_ptr(_dryad_S4#8, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(sll_keys(head), @_vcc_intset_union(sll_keys(*((head->next))), @_vcc_intset_singleton(*((head->key)))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#head, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#head, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(sll_list_len_next(head), unchecked+(sll_list_len_next(*((head->next))), 1))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(L#head, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(head), ==(rsrtl(head), &&(&&(rsrtl(*((head->next))), unchecked!(@_vcc_oset_in(head, rsrtl_reach(*((head->next)))))), @_vcc_intset_le_one2(sll_keys(*((head->next))), *((head->key)))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(L#head, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#head, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(L#head, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(rsrtl_reach(head), @_vcc_oset_union(rsrtl_reach(*((head->next))), @_vcc_oset_singleton(head)))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(L#head, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#head, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(sll(head), &&(sll(*((head->next))), unchecked!(@_vcc_oset_in(head, sll_reach(*((head->next)))))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#head, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#head, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(sll_reach(head), @_vcc_oset_union(sll_reach(*((head->next))), @_vcc_oset_singleton(head)))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#head, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#head, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(srtl(head), &&(&&(srtl(*((head->next))), unchecked!(@_vcc_oset_in(head, srtl_reach(*((head->next)))))), @_vcc_intset_le_one1(*((head->key)), sll_keys(*((head->next))))))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(L#head, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#head, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(L#head, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(head), ==(srtl_reach(head), @_vcc_oset_union(srtl_reach(*((head->next))), @_vcc_oset_singleton(head)))); 
            assume $non_null($phys_ptr_cast(L#head, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(L#head, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#head, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#head, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_list_len_next(x), unchecked+(sll_list_len_next(*((x->next))), 1))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_list_len_next($s, $phys_ptr_cast(P#x, ^s_node)) == $unchk_add(^^nat, F#sll_list_len_next($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), 1);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl(x), &&(&&(rsrtl(*((x->next))), unchecked!(@_vcc_oset_in(x, rsrtl_reach(*((x->next)))))), @_vcc_intset_le_one2(sll_keys(*((x->next))), *((x->key)))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#rsrtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one2(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(rsrtl_reach(x), @_vcc_oset_union(rsrtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#rsrtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#rsrtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next)))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl(x), &&(&&(srtl(*((x->next))), unchecked!(@_vcc_oset_in(x, srtl_reach(*((x->next)))))), @_vcc_intset_le_one1(*((x->key)), sll_keys(*((x->next))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl($s, $phys_ptr_cast(P#x, ^s_node)) == (F#srtl($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) && $intset_le_one1($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)), F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(srtl_reach(x), @_vcc_oset_union(srtl_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
            assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#srtl_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#srtl_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node)));
            // return head; 
            $result := $phys_ptr_cast(L#head, ^s_node);
            assume true;
            assert $position_marker();
            goto #exit;
        }
    }

  anon6:
    // skip

  #exit:
}



axiom (forall Q#__vcc_state$2^527.9#tc2#1550: $state, Q#x$2^527.9#dt1#1484: $ptr :: {:weight 10} { F#srtl(Q#__vcc_state$2^527.9#tc2#1550, $phys_ptr_cast(Q#x$2^527.9#dt1#1484, ^s_node)) } { F#sll(Q#__vcc_state$2^527.9#tc2#1550, $phys_ptr_cast(Q#x$2^527.9#dt1#1484, ^s_node)) } $good_state(Q#__vcc_state$2^527.9#tc2#1550) && true ==> F#srtl(Q#__vcc_state$2^527.9#tc2#1550, $phys_ptr_cast(Q#x$2^527.9#dt1#1484, ^s_node)) ==> F#sll(Q#__vcc_state$2^527.9#tc2#1550, $phys_ptr_cast(Q#x$2^527.9#dt1#1484, ^s_node)));

axiom (forall Q#__vcc_state$2^528.9#tc2#1551: $state, Q#x$2^528.9#dt1#1485: $ptr :: {:weight 10} { F#rsrtl(Q#__vcc_state$2^528.9#tc2#1551, $phys_ptr_cast(Q#x$2^528.9#dt1#1485, ^s_node)) } { F#sll(Q#__vcc_state$2^528.9#tc2#1551, $phys_ptr_cast(Q#x$2^528.9#dt1#1485, ^s_node)) } $good_state(Q#__vcc_state$2^528.9#tc2#1551) && true ==> F#rsrtl(Q#__vcc_state$2^528.9#tc2#1551, $phys_ptr_cast(Q#x$2^528.9#dt1#1485, ^s_node)) ==> F#sll(Q#__vcc_state$2^528.9#tc2#1551, $phys_ptr_cast(Q#x$2^528.9#dt1#1485, ^s_node)));

axiom (forall Q#__vcc_state$2^529.9#tc2#1552: $state, Q#x$2^529.9#dt1#1486: $ptr :: {:weight 10} { F#sll_reach(Q#__vcc_state$2^529.9#tc2#1552, $phys_ptr_cast(Q#x$2^529.9#dt1#1486, ^s_node)) } { F#srtl_reach(Q#__vcc_state$2^529.9#tc2#1552, $phys_ptr_cast(Q#x$2^529.9#dt1#1486, ^s_node)) } $good_state(Q#__vcc_state$2^529.9#tc2#1552) && true ==> F#sll_reach(Q#__vcc_state$2^529.9#tc2#1552, $phys_ptr_cast(Q#x$2^529.9#dt1#1486, ^s_node)) == F#srtl_reach(Q#__vcc_state$2^529.9#tc2#1552, $phys_ptr_cast(Q#x$2^529.9#dt1#1486, ^s_node)));

axiom (forall Q#__vcc_state$2^530.9#tc2#1553: $state, Q#x$2^530.9#dt1#1487: $ptr :: {:weight 10} { F#srtl_reach(Q#__vcc_state$2^530.9#tc2#1553, $phys_ptr_cast(Q#x$2^530.9#dt1#1487, ^s_node)) } { F#rsrtl_reach(Q#__vcc_state$2^530.9#tc2#1553, $phys_ptr_cast(Q#x$2^530.9#dt1#1487, ^s_node)) } $good_state(Q#__vcc_state$2^530.9#tc2#1553) && true ==> F#srtl_reach(Q#__vcc_state$2^530.9#tc2#1553, $phys_ptr_cast(Q#x$2^530.9#dt1#1487, ^s_node)) == F#rsrtl_reach(Q#__vcc_state$2^530.9#tc2#1553, $phys_ptr_cast(Q#x$2^530.9#dt1#1487, ^s_node)));

axiom (forall Q#__vcc_state$2^531.9#tc2#1554: $state, Q#x$2^531.9#dt1#1488: $ptr, Q#y$2^531.9#dt1#1489: $ptr :: {:weight 10} { F#sll_lseg_reach(Q#__vcc_state$2^531.9#tc2#1554, $phys_ptr_cast(Q#x$2^531.9#dt1#1488, ^s_node), $phys_ptr_cast(Q#y$2^531.9#dt1#1489, ^s_node)) } { F#srtl_lseg_reach(Q#__vcc_state$2^531.9#tc2#1554, $phys_ptr_cast(Q#x$2^531.9#dt1#1488, ^s_node), $phys_ptr_cast(Q#y$2^531.9#dt1#1489, ^s_node)) } $good_state(Q#__vcc_state$2^531.9#tc2#1554) && true ==> F#sll_lseg_reach(Q#__vcc_state$2^531.9#tc2#1554, $phys_ptr_cast(Q#x$2^531.9#dt1#1488, ^s_node), $phys_ptr_cast(Q#y$2^531.9#dt1#1489, ^s_node)) == F#srtl_lseg_reach(Q#__vcc_state$2^531.9#tc2#1554, $phys_ptr_cast(Q#x$2^531.9#dt1#1488, ^s_node), $phys_ptr_cast(Q#y$2^531.9#dt1#1489, ^s_node)));

const unique l#public: $label;

axiom $type_code_is(2, ^$#state_t);

const unique #tok$3^35.3: $token;

const unique #tok$3^34.3: $token;

const unique #tok$3^31.19: $token;

const unique #tok$3^25.3: $token;

const unique #tok$3^23.18: $token;

const unique #tok$3^18.3: $token;

const unique #tok$3^17.3: $token;

const unique #tok$3^14.19: $token;

const unique #tok$4^0.0: $token;

const unique #file^?3Cno?20file?3E: $token;

axiom $file_name_is(4, #file^?3Cno?20file?3E);

const unique #tok$3^3.3: $token;

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Csorted?2Dsll?5Csorted_insert.c: $token;

axiom $file_name_is(3, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Csorted?2Dsll?5Csorted_insert.c);

const unique #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Csorted?2Dsll?5Cdryad_srtl.h: $token;

axiom $file_name_is(2, #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Csorted?2Dsll?5Cdryad_srtl.h);

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?2Dbin?5CHeaders?5Cvccp.h: $token;

axiom $file_name_is(1, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?2Dbin?5CHeaders?5Cvccp.h);

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^s_node);

