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

const unique ^$#sll_insert.c..36261#3: $ctype;

axiom $def_fnptr_type(^$#sll_insert.c..36261#3);

type $#sll_insert.c..36261#3;

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

axiom $function_arg_type(cf#sll, 0, ^^bool);

axiom $function_arg_type(cf#sll, 1, $ptr_to(^s_node));

procedure sll(SP#hd: $ptr) returns ($result: bool);
  free ensures $result == F#sll($s, SP#hd);
  free ensures $call_transition(old($s), $s);



function F#sll_reach(#s: $state, SP#hd: $ptr) : $oset;

const unique cf#sll_reach: $pure_function;

axiom $function_arg_type(cf#sll_reach, 0, ^$#oset);

axiom $function_arg_type(cf#sll_reach, 1, $ptr_to(^s_node));

procedure sll_reach(SP#hd: $ptr) returns ($result: $oset);
  free ensures $result == F#sll_reach($s, SP#hd);
  free ensures $call_transition(old($s), $s);



function F#sll_keys(#s: $state, SP#hd: $ptr) : $intset;

const unique cf#sll_keys: $pure_function;

axiom $function_arg_type(cf#sll_keys, 0, ^$#intset);

axiom $function_arg_type(cf#sll_keys, 1, $ptr_to(^s_node));

procedure sll_keys(SP#hd: $ptr) returns ($result: $intset);
  free ensures $result == F#sll_keys($s, SP#hd);
  free ensures $call_transition(old($s), $s);



function F#sll_keys_reach(#s: $state, SP#hd: $ptr) : $oset;

const unique cf#sll_keys_reach: $pure_function;

axiom $function_arg_type(cf#sll_keys_reach, 0, ^$#oset);

axiom $function_arg_type(cf#sll_keys_reach, 1, $ptr_to(^s_node));

procedure sll_keys_reach(SP#hd: $ptr) returns ($result: $oset);
  free ensures $result == F#sll_keys_reach($s, SP#hd);
  free ensures $call_transition(old($s), $s);



procedure sll_insert(P#x: $ptr, P#k: int) returns ($result: $ptr);
  requires F#sll($s, $phys_ptr_cast(P#x, ^s_node));
  modifies $s, $cev_pc;
  ensures F#sll($s, $phys_ptr_cast($result, ^s_node));
// INV:BEGIN
  ensures F#sll_keys($s, $phys_ptr_cast($result, ^s_node)) == $intset_union(F#sll_keys(old($s), $phys_ptr_cast(P#x, ^s_node)), $intset_singleton(P#k));
// INV:END
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);

// INV:PTR: P#x, $result
// INV:INT: P#k
// INV:LST: sll
// INV:OLD:

implementation sll_insert(P#x: $ptr, P#k: int) returns ($result: $ptr)
{
  var stmtexpr6#20: $state;
  var _dryad_S5#9: $state;
  var stmtexpr5#19: $state;
  var _dryad_S4#8: $state;
  var stmtexpr4#18: $state;
  var _dryad_S3#7: $state;
  var stmtexpr3#17: $state;
  var _dryad_S2#6: $state;
  var stmtexpr2#16: $state;
  var _dryad_S1#5: $state;
  var stmtexpr1#15: $oset;
  var stmtexpr0#14: $state;
  var _dryad_S0#4: $state;
  var L#new_root: $ptr;
  var stmtexpr4#13: $state;
  var _dryad_S3#3: $state;
  var stmtexpr3#12: $state;
  var _dryad_S2#2: $state;
  var stmtexpr2#11: $oset;
  var res_sll_reach#1: $oset;
  var stmtexpr1#10: $state;
  var _dryad_S1#1: $state;
  var stmtexpr0#9: $state;
  var _dryad_S0#0: $state;
  var L#tmp: $ptr;
  var stmtexpr6#8: $state;
  var SL#_dryad_S5: $state;
  var stmtexpr5#7: $state;
  var SL#_dryad_S4: $state;
  var stmtexpr4#6: $state;
  var SL#_dryad_S3: $state;
  var stmtexpr3#5: $state;
  var SL#_dryad_S2: $state;
  var stmtexpr2#4: $state;
  var SL#_dryad_S1: $state;
  var stmtexpr1#3: $oset;
  var stmtexpr0#2: $state;
  var SL#_dryad_S0: $state;
  var L#leaf: $ptr;
  var stmtexpr1#22: $oset;
  var stmtexpr0#21: $oset;
  var SL#_dryad_G1: $oset;
  var SL#_dryad_G0: $oset;
  var #wrTime$3^4.3: int;
  var #stackframe: int;

  anon5:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$3^4.3, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$3^4.3 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$3^4.3, (lambda #p: $ptr :: false));
    // assume true
    // assume @in_range_i4(k); 
    assume $in_range_i4(P#k);
    // assume @decreases_level_is(2147483647); 
    assume 2147483647 == $decreases_level;
    // assume true
    // assume true
    //  --- Dryad annotated function --- 
    // _math \oset _dryad_G0; 
    // _math \oset _dryad_G1; 
    // _dryad_G0 := sll_reach(x); 
    call SL#_dryad_G0 := sll_reach($phys_ptr_cast(P#x, ^s_node));
    assume $full_stop_ext(#tok$4^0.0, $s);
    // _math \oset stmtexpr0#21; 
    // stmtexpr0#21 := _dryad_G0; 
    stmtexpr0#21 := SL#_dryad_G0;
    // _dryad_G1 := _dryad_G0; 
    SL#_dryad_G1 := SL#_dryad_G0;
    // _math \oset stmtexpr1#22; 
    // stmtexpr1#22 := _dryad_G1; 
    stmtexpr1#22 := SL#_dryad_G1;
    // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
    assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
    // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
    assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
    // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
    assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
    // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
    assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), &&(@writes_check(x), @_vcc_mutable(@state, x))); 
    assume $non_null($phys_ptr_cast(P#x, ^s_node)) ==> $top_writable($s, #wrTime$3^4.3, $phys_ptr_cast(P#x, ^s_node)) && $mutable($s, $phys_ptr_cast(P#x, ^s_node));
    assume true;
    // if (@_vcc_ptr_eq_null(x)) ...
    if ($is_null($phys_ptr_cast(P#x, ^s_node)))
    {
      anon1:
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
        // struct s_node* leaf; 
        // assert false; 
        assert false;
        // assume false; 
        assume false;
        // _math \state _dryad_S0; 
        // _dryad_S0 := @_vcc_current_state(@state); 
        SL#_dryad_S0 := $current_state($s);
        // _math \state stmtexpr0#2; 
        // stmtexpr0#2 := _dryad_S0; 
        stmtexpr0#2 := SL#_dryad_S0;
        // leaf := _vcc_alloc(@_vcc_typeof((struct s_node*)@null)); 
        call L#leaf := $alloc(^s_node);
        assume $full_stop_ext(#tok$3^14.19, $s);
        // assume !(@_vcc_oset_in(leaf, @_vcc_oset_union(_dryad_G0, _dryad_G1))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), $oset_union(SL#_dryad_G0, SL#_dryad_G1));
        // _dryad_G1 := @_vcc_oset_union(_dryad_G0, @_vcc_oset_singleton(leaf)); 
        SL#_dryad_G1 := $oset_union(SL#_dryad_G0, $oset_singleton($phys_ptr_cast(L#leaf, ^s_node)));
        // _math \oset stmtexpr1#3; 
        // stmtexpr1#3 := _dryad_G1; 
        stmtexpr1#3 := SL#_dryad_G1;
        // assume ==(glob_reach(), _dryad_G1); 
        assume F#glob_reach() == SL#_dryad_G1;
        // _math \state _dryad_S1; 
        // _dryad_S1 := @_vcc_current_state(@state); 
        SL#_dryad_S1 := $current_state($s);
        // _math \state stmtexpr2#4; 
        // stmtexpr2#4 := _dryad_S1; 
        stmtexpr2#4 := SL#_dryad_S1;
        // assume &&(==>(@_vcc_ptr_eq_null(leaf), ==(sll_keys(leaf), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(leaf), ==(sll_keys(leaf), @_vcc_intset_union(sll_keys(*((leaf->next))), @_vcc_intset_singleton(*((leaf->key))))))); 
        assume ($is_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#leaf, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#leaf, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#leaf, ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(leaf), ==(sll_keys_reach(leaf), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(leaf), ==(sll_keys_reach(leaf), @_vcc_oset_union(sll_keys_reach(*((leaf->next))), @_vcc_oset_singleton(leaf))))); 
        assume ($is_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#leaf, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#leaf, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#leaf, ^s_node))));
        // assume &&(==>(@_vcc_ptr_eq_null(leaf), sll(leaf)), ==>(@_vcc_ptr_neq_null(leaf), ==(sll(leaf), &&(sll(*((leaf->next))), unchecked!(@_vcc_oset_in(leaf, sll_reach(*((leaf->next))))))))); 
        assume ($is_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#leaf, ^s_node))) && ($non_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#leaf, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(leaf), ==(sll_reach(leaf), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(leaf), ==(sll_reach(leaf), @_vcc_oset_union(sll_reach(*((leaf->next))), @_vcc_oset_singleton(leaf))))); 
        assume ($is_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#leaf, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#leaf, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#leaf, ^s_node))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S0, sll_reach(x)))), ==(old(_dryad_S0, sll_keys(x)), old(_dryad_S1, sll_keys(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S0, sll_keys_reach(x)))), ==(old(_dryad_S0, sll_keys_reach(x)), old(_dryad_S1, sll_keys_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_keys_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S0, sll_reach(x)))), ==(old(_dryad_S0, sll(x)), old(_dryad_S1, sll(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#sll(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S0, sll_reach(x)))), ==(old(_dryad_S0, sll_reach(x)), old(_dryad_S1, sll_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^s_node));
        // _math \state _dryad_S2; 
        // _dryad_S2 := @_vcc_current_state(@state); 
        SL#_dryad_S2 := $current_state($s);
        // _math \state stmtexpr3#5; 
        // stmtexpr3#5 := _dryad_S2; 
        stmtexpr3#5 := SL#_dryad_S2;
        // assert @prim_writes_check((leaf->key)); 
        assert $writable_prim($s, #wrTime$3^4.3, $dot($phys_ptr_cast(L#leaf, ^s_node), s_node.key));
        // *(leaf->key) := k; 
        call $write_int(s_node.key, $phys_ptr_cast(L#leaf, ^s_node), P#k);
        assume $full_stop_ext(#tok$3^20.3, $s);
        // _math \state _dryad_S3; 
        // _dryad_S3 := @_vcc_current_state(@state); 
        SL#_dryad_S3 := $current_state($s);
        // _math \state stmtexpr4#6; 
        // stmtexpr4#6 := _dryad_S3; 
        stmtexpr4#6 := SL#_dryad_S3;
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S2, sll_reach(*((leaf->next)))))), ==(old(_dryad_S2, sll_keys(*((leaf->next)))), old(_dryad_S3, sll_keys(*((leaf->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node))) ==> F#sll_keys(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)) == F#sll_keys(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S2, sll_keys_reach(*((leaf->next)))))), ==(old(_dryad_S2, sll_keys_reach(*((leaf->next)))), old(_dryad_S3, sll_keys_reach(*((leaf->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_keys_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node))) ==> F#sll_keys_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)) == F#sll_keys_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S2, sll_reach(*((leaf->next)))))), ==(old(_dryad_S2, sll(*((leaf->next)))), old(_dryad_S3, sll(*((leaf->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node))) ==> F#sll(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)) == F#sll(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S2, sll_reach(*((leaf->next)))))), ==(old(_dryad_S2, sll_reach(*((leaf->next)))), old(_dryad_S3, sll_reach(*((leaf->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node))) ==> F#sll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)) == F#sll_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node));
        // assume ==(old(_dryad_S2, sll_keys_reach(leaf)), old(_dryad_S3, sll_keys_reach(leaf))); 
        assume F#sll_keys_reach(SL#_dryad_S2, $phys_ptr_cast(L#leaf, ^s_node)) == F#sll_keys_reach(SL#_dryad_S3, $phys_ptr_cast(L#leaf, ^s_node));
        // assume ==(old(_dryad_S2, sll(leaf)), old(_dryad_S3, sll(leaf))); 
        assume F#sll(SL#_dryad_S2, $phys_ptr_cast(L#leaf, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(L#leaf, ^s_node));
        // assume ==(old(_dryad_S2, sll_reach(leaf)), old(_dryad_S3, sll_reach(leaf))); 
        assume F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(L#leaf, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(L#leaf, ^s_node));
        // assume ==(old(_dryad_S2, sll_keys_reach(x)), old(_dryad_S3, sll_keys_reach(x))); 
        assume F#sll_keys_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==(old(_dryad_S2, sll(x)), old(_dryad_S3, sll(x))); 
        assume F#sll(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==(old(_dryad_S2, sll_reach(x)), old(_dryad_S3, sll_reach(x))); 
        assume F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S2, sll_reach(x)))), ==(old(_dryad_S2, sll_keys(x)), old(_dryad_S3, sll_keys(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S2, sll_keys_reach(x)))), ==(old(_dryad_S2, sll_keys_reach(x)), old(_dryad_S3, sll_keys_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_keys_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S2, sll_reach(x)))), ==(old(_dryad_S2, sll(x)), old(_dryad_S3, sll(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S2, sll_reach(x)))), ==(old(_dryad_S2, sll_reach(x)), old(_dryad_S3, sll_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(leaf, x)), ==(*((x->key)), old(_dryad_S2, *((x->key))))); 
        assume !($phys_ptr_cast(L#leaf, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)) == $rd_inv(SL#_dryad_S2, s_node.key, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(leaf, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S2, *((x->next))))); 
        assume !($phys_ptr_cast(L#leaf, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S2, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node);
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
        // assume &&(==>(@_vcc_ptr_eq_null(leaf), ==(sll_keys(leaf), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(leaf), ==(sll_keys(leaf), @_vcc_intset_union(sll_keys(*((leaf->next))), @_vcc_intset_singleton(*((leaf->key))))))); 
        assume ($is_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#leaf, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#leaf, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#leaf, ^s_node)))));
        // _math \state _dryad_S4; 
        // _dryad_S4 := @_vcc_current_state(@state); 
        SL#_dryad_S4 := $current_state($s);
        // _math \state stmtexpr5#7; 
        // stmtexpr5#7 := _dryad_S4; 
        stmtexpr5#7 := SL#_dryad_S4;
        // assert @prim_writes_check((leaf->next)); 
        assert $writable_prim($s, #wrTime$3^4.3, $dot($phys_ptr_cast(L#leaf, ^s_node), s_node.next));
        // *(leaf->next) := (struct s_node*)@null; 
        call $write_int(s_node.next, $phys_ptr_cast(L#leaf, ^s_node), $ptr_to_int($phys_ptr_cast($null, ^s_node)));
        assume $full_stop_ext(#tok$3^21.3, $s);
        // _math \state _dryad_S5; 
        // _dryad_S5 := @_vcc_current_state(@state); 
        SL#_dryad_S5 := $current_state($s);
        // _math \state stmtexpr6#8; 
        // stmtexpr6#8 := _dryad_S5; 
        stmtexpr6#8 := SL#_dryad_S5;
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S4, sll_reach(x)))), ==(old(_dryad_S4, sll_keys(x)), old(_dryad_S5, sll_keys(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S4, sll_keys_reach(x)))), ==(old(_dryad_S4, sll_keys_reach(x)), old(_dryad_S5, sll_keys_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_keys_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys_reach(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S4, sll_reach(x)))), ==(old(_dryad_S4, sll(x)), old(_dryad_S5, sll(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#sll(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(unchecked!(@_vcc_oset_in(leaf, old(_dryad_S4, sll_reach(x)))), ==(old(_dryad_S4, sll_reach(x)), old(_dryad_S5, sll_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(SL#_dryad_S5, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(leaf, x)), ==(*((x->key)), old(_dryad_S4, *((x->key))))); 
        assume !($phys_ptr_cast(L#leaf, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)) == $rd_inv(SL#_dryad_S4, s_node.key, $phys_ptr_cast(P#x, ^s_node));
        // assume ==>(!(@_vcc_ptr_eq_pure(leaf, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S4, *((x->next))))); 
        assume !($phys_ptr_cast(L#leaf, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node) == $rd_phys_ptr(SL#_dryad_S4, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node);
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
        assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
        // assume &&(==>(@_vcc_ptr_eq_null(leaf), ==(sll_keys(leaf), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(leaf), ==(sll_keys(leaf), @_vcc_intset_union(sll_keys(*((leaf->next))), @_vcc_intset_singleton(*((leaf->key))))))); 
        assume ($is_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#leaf, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#leaf, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#leaf, ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(leaf), ==(sll_keys_reach(leaf), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(leaf), ==(sll_keys_reach(leaf), @_vcc_oset_union(sll_keys_reach(*((leaf->next))), @_vcc_oset_singleton(leaf))))); 
        assume ($is_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#leaf, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#leaf, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#leaf, ^s_node))));
        // assume &&(==>(@_vcc_ptr_eq_null(leaf), sll(leaf)), ==>(@_vcc_ptr_neq_null(leaf), ==(sll(leaf), &&(sll(*((leaf->next))), unchecked!(@_vcc_oset_in(leaf, sll_reach(*((leaf->next))))))))); 
        assume ($is_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#leaf, ^s_node))) && ($non_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#leaf, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#leaf, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)))));
        // assume &&(==>(@_vcc_ptr_eq_null(leaf), ==(sll_reach(leaf), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(leaf), ==(sll_reach(leaf), @_vcc_oset_union(sll_reach(*((leaf->next))), @_vcc_oset_singleton(leaf))))); 
        assume ($is_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#leaf, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#leaf, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#leaf, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#leaf, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#leaf, ^s_node))));
        // return leaf; 
        $result := $phys_ptr_cast(L#leaf, ^s_node);
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
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // struct s_node* tmp; 
            // _math \state _dryad_S0#0; 
            // _dryad_S0#0 := @_vcc_current_state(@state); 
            _dryad_S0#0 := $current_state($s);
            // _math \state stmtexpr0#9; 
            // stmtexpr0#9 := _dryad_S0#0; 
            stmtexpr0#9 := _dryad_S0#0;
            // non-pure function
            // assert @reads_check_normal((x->next)); 
            assert $thread_local($s, $phys_ptr_cast(P#x, ^s_node));
            // tmp := sll_insert(*((x->next)), k); 
            call L#tmp := sll_insert($rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node), P#k);
            assume $full_stop_ext(#tok$3^25.18, $s);
            // _math \state _dryad_S1#1; 
            // _dryad_S1#1 := @_vcc_current_state(@state); 
            _dryad_S1#1 := $current_state($s);
            // _math \state stmtexpr1#10; 
            // stmtexpr1#10 := _dryad_S1#1; 
            stmtexpr1#10 := _dryad_S1#1;
            // assume @_vcc_oset_disjoint(sll_reach(tmp), @_vcc_oset_diff(_dryad_G1, old(_dryad_S0#0, sll_reach(*((x->next)))))); 
            assume $oset_disjoint(F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)), $oset_diff(SL#_dryad_G1, F#sll_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // _math \oset res_sll_reach#1; 
            // res_sll_reach#1 := sll_reach(tmp); 
            call res_sll_reach#1 := sll_reach($phys_ptr_cast(L#tmp, ^s_node));
            assume $full_stop_ext(#tok$4^0.0, $s);
            // _dryad_G1 := @_vcc_oset_union(res_sll_reach#1, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S0#0, sll_reach(*((x->next))))))); 
            SL#_dryad_G1 := $oset_union(res_sll_reach#1, $oset_diff(SL#_dryad_G1, F#sll_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))));
            // _math \oset stmtexpr2#11; 
            // stmtexpr2#11 := _dryad_G1; 
            stmtexpr2#11 := SL#_dryad_G1;
            // assume ==(glob_reach(), _dryad_G1); 
            assume F#glob_reach() == SL#_dryad_G1;
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, sll_reach(*((x->next)))), old(_dryad_S0#0, sll_reach(x))), ==(old(_dryad_S0#0, sll_keys(x)), old(_dryad_S1#1, sll_keys(x)))); 
            assume $oset_disjoint(F#sll_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#sll_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, sll_reach(*((x->next)))), old(_dryad_S0#0, sll_keys_reach(x))), ==(old(_dryad_S0#0, sll_keys_reach(x)), old(_dryad_S1#1, sll_keys_reach(x)))); 
            assume $oset_disjoint(F#sll_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#sll_keys_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys_reach(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, sll_reach(*((x->next)))), old(_dryad_S0#0, sll_reach(x))), ==(old(_dryad_S0#0, sll(x)), old(_dryad_S1#1, sll(x)))); 
            assume $oset_disjoint(F#sll_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#sll_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#sll(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, sll_reach(*((x->next)))), old(_dryad_S0#0, sll_reach(x))), ==(old(_dryad_S0#0, sll_reach(x)), old(_dryad_S1#1, sll_reach(x)))); 
            assume $oset_disjoint(F#sll_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), F#sll_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(_dryad_S1#1, $phys_ptr_cast(P#x, ^s_node));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), ==(sll_keys(tmp), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll_keys(tmp), @_vcc_intset_union(sll_keys(*((tmp->next))), @_vcc_intset_singleton(*((tmp->key))))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tmp, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tmp, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), ==(sll_keys_reach(tmp), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll_keys_reach(tmp), @_vcc_oset_union(sll_keys_reach(*((tmp->next))), @_vcc_oset_singleton(tmp))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), sll(tmp)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll(tmp), &&(sll(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, sll_reach(*((tmp->next))))))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tmp, ^s_node))) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), ==(sll_reach(tmp), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll_reach(tmp), @_vcc_oset_union(sll_reach(*((tmp->next))), @_vcc_oset_singleton(tmp))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0#0, sll_reach(*((x->next)))))), ==(*((x->key)), old(_dryad_S0#0, *((x->key))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)) == $rd_inv(_dryad_S0#0, s_node.key, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0#0, sll_reach(*((x->next)))))), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S0#0, *((x->next))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach(_dryad_S0#0, $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node))) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node) == $rd_phys_ptr(_dryad_S0#0, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node);
            // _math \state _dryad_S2#2; 
            // _dryad_S2#2 := @_vcc_current_state(@state); 
            _dryad_S2#2 := $current_state($s);
            // _math \state stmtexpr3#12; 
            // stmtexpr3#12 := _dryad_S2#2; 
            stmtexpr3#12 := _dryad_S2#2;
            // assert @prim_writes_check((x->next)); 
            assert $writable_prim($s, #wrTime$3^4.3, $dot($phys_ptr_cast(P#x, ^s_node), s_node.next));
            // *(x->next) := tmp; 
            call $write_int(s_node.next, $phys_ptr_cast(P#x, ^s_node), $ptr_to_int($phys_ptr_cast(L#tmp, ^s_node)));
            assume $full_stop_ext(#tok$3^26.3, $s);
            // _math \state _dryad_S3#3; 
            // _dryad_S3#3 := @_vcc_current_state(@state); 
            _dryad_S3#3 := $current_state($s);
            // _math \state stmtexpr4#13; 
            // stmtexpr4#13 := _dryad_S3#3; 
            stmtexpr4#13 := _dryad_S3#3;
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, sll_reach(tmp)))), ==(old(_dryad_S2#2, sll_keys(tmp)), old(_dryad_S3#3, sll_keys(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#sll_keys(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#sll_keys(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, sll_keys_reach(tmp)))), ==(old(_dryad_S2#2, sll_keys_reach(tmp)), old(_dryad_S3#3, sll_keys_reach(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_keys_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#sll_keys_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#sll_keys_reach(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, sll_reach(tmp)))), ==(old(_dryad_S2#2, sll(tmp)), old(_dryad_S3#3, sll(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#sll(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#sll(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#2, sll_reach(tmp)))), ==(old(_dryad_S2#2, sll_reach(tmp)), old(_dryad_S3#3, sll_reach(tmp)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node))) ==> F#sll_reach(_dryad_S2#2, $phys_ptr_cast(L#tmp, ^s_node)) == F#sll_reach(_dryad_S3#3, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, tmp)), ==(*((tmp->key)), old(_dryad_S2#2, *((tmp->key))))); 
            assume !($phys_ptr_cast(P#x, ^s_node) == $phys_ptr_cast(L#tmp, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node)) == $rd_inv(_dryad_S2#2, s_node.key, $phys_ptr_cast(L#tmp, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, tmp)), @_vcc_ptr_eq_pure(*((tmp->next)), old(_dryad_S2#2, *((tmp->next))))); 
            assume !($phys_ptr_cast(P#x, ^s_node) == $phys_ptr_cast(L#tmp, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node) == $rd_phys_ptr(_dryad_S2#2, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node);
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), ==(sll_keys(tmp), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll_keys(tmp), @_vcc_intset_union(sll_keys(*((tmp->next))), @_vcc_intset_singleton(*((tmp->key))))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tmp, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tmp, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), ==(sll_keys_reach(tmp), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll_keys_reach(tmp), @_vcc_oset_union(sll_keys_reach(*((tmp->next))), @_vcc_oset_singleton(tmp))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), sll(tmp)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll(tmp), &&(sll(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, sll_reach(*((tmp->next))))))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tmp, ^s_node))) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), ==(sll_reach(tmp), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll_reach(tmp), @_vcc_oset_union(sll_reach(*((tmp->next))), @_vcc_oset_singleton(tmp))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), ==(sll_keys(tmp), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll_keys(tmp), @_vcc_intset_union(sll_keys(*((tmp->next))), @_vcc_intset_singleton(*((tmp->key))))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tmp, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#tmp, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#tmp, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), ==(sll_keys_reach(tmp), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll_keys_reach(tmp), @_vcc_oset_union(sll_keys_reach(*((tmp->next))), @_vcc_oset_singleton(tmp))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), sll(tmp)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll(tmp), &&(sll(*((tmp->next))), unchecked!(@_vcc_oset_in(tmp, sll_reach(*((tmp->next))))))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tmp, ^s_node))) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#tmp, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#tmp, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(tmp), ==(sll_reach(tmp), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(tmp), ==(sll_reach(tmp), @_vcc_oset_union(sll_reach(*((tmp->next))), @_vcc_oset_singleton(tmp))))); 
            assume ($is_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#tmp, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#tmp, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#tmp, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#tmp, ^s_node))));
            // return x; 
            $result := $phys_ptr_cast(P#x, ^s_node);
            assume true;
            assert $position_marker();
            goto #exit;
        }
        else
        {
          anon3:
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // struct s_node* new_root; 
            // _math \state _dryad_S0#4; 
            // _dryad_S0#4 := @_vcc_current_state(@state); 
            _dryad_S0#4 := $current_state($s);
            // _math \state stmtexpr0#14; 
            // stmtexpr0#14 := _dryad_S0#4; 
            stmtexpr0#14 := _dryad_S0#4;
            // new_root := _vcc_alloc(@_vcc_typeof((struct s_node*)@null)); 
            call L#new_root := $alloc(^s_node);
            assume $full_stop_ext(#tok$3^29.23, $s);
            // assume !(@_vcc_oset_in(new_root, @_vcc_oset_union(_dryad_G0, _dryad_G1))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), $oset_union(SL#_dryad_G0, SL#_dryad_G1));
            // _dryad_G1 := @_vcc_oset_union(_dryad_G0, @_vcc_oset_singleton(new_root)); 
            SL#_dryad_G1 := $oset_union(SL#_dryad_G0, $oset_singleton($phys_ptr_cast(L#new_root, ^s_node)));
            // _math \oset stmtexpr1#15; 
            // stmtexpr1#15 := _dryad_G1; 
            stmtexpr1#15 := SL#_dryad_G1;
            // assume ==(glob_reach(), _dryad_G1); 
            assume F#glob_reach() == SL#_dryad_G1;
            // _math \state _dryad_S1#5; 
            // _dryad_S1#5 := @_vcc_current_state(@state); 
            _dryad_S1#5 := $current_state($s);
            // _math \state stmtexpr2#16; 
            // stmtexpr2#16 := _dryad_S1#5; 
            stmtexpr2#16 := _dryad_S1#5;
            // assume &&(==>(@_vcc_ptr_eq_null(new_root), ==(sll_keys(new_root), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(new_root), ==(sll_keys(new_root), @_vcc_intset_union(sll_keys(*((new_root->next))), @_vcc_intset_singleton(*((new_root->key))))))); 
            assume ($is_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_root, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_root, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_root, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(new_root), ==(sll_keys_reach(new_root), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(new_root), ==(sll_keys_reach(new_root), @_vcc_oset_union(sll_keys_reach(*((new_root->next))), @_vcc_oset_singleton(new_root))))); 
            assume ($is_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#new_root, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#new_root, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_root, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(new_root), sll(new_root)), ==>(@_vcc_ptr_neq_null(new_root), ==(sll(new_root), &&(sll(*((new_root->next))), unchecked!(@_vcc_oset_in(new_root, sll_reach(*((new_root->next))))))))); 
            assume ($is_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_root, ^s_node))) && ($non_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_root, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(new_root), ==(sll_reach(new_root), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(new_root), ==(sll_reach(new_root), @_vcc_oset_union(sll_reach(*((new_root->next))), @_vcc_oset_singleton(new_root))))); 
            assume ($is_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_root, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_root, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_root, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S0#4, sll_reach(x)))), ==(old(_dryad_S0#4, sll_keys(x)), old(_dryad_S1#5, sll_keys(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S0#4, sll_keys_reach(x)))), ==(old(_dryad_S0#4, sll_keys_reach(x)), old(_dryad_S1#5, sll_keys_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_keys_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys_reach(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S0#4, sll_reach(x)))), ==(old(_dryad_S0#4, sll(x)), old(_dryad_S1#5, sll(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#sll(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S0#4, sll_reach(x)))), ==(old(_dryad_S0#4, sll_reach(x)), old(_dryad_S1#5, sll_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(_dryad_S0#4, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(_dryad_S1#5, $phys_ptr_cast(P#x, ^s_node));
            // assume @_vcc_ptr_neq_null(new_root); 
            assume $non_null($phys_ptr_cast(L#new_root, ^s_node));
            // _math \state _dryad_S2#6; 
            // _dryad_S2#6 := @_vcc_current_state(@state); 
            _dryad_S2#6 := $current_state($s);
            // _math \state stmtexpr3#17; 
            // stmtexpr3#17 := _dryad_S2#6; 
            stmtexpr3#17 := _dryad_S2#6;
            // assert @prim_writes_check((new_root->key)); 
            assert $writable_prim($s, #wrTime$3^4.3, $dot($phys_ptr_cast(L#new_root, ^s_node), s_node.key));
            // *(new_root->key) := k; 
            call $write_int(s_node.key, $phys_ptr_cast(L#new_root, ^s_node), P#k);
            assume $full_stop_ext(#tok$3^32.3, $s);
            // _math \state _dryad_S3#7; 
            // _dryad_S3#7 := @_vcc_current_state(@state); 
            _dryad_S3#7 := $current_state($s);
            // _math \state stmtexpr4#18; 
            // stmtexpr4#18 := _dryad_S3#7; 
            stmtexpr4#18 := _dryad_S3#7;
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S2#6, sll_reach(*((new_root->next)))))), ==(old(_dryad_S2#6, sll_keys(*((new_root->next)))), old(_dryad_S3#7, sll_keys(*((new_root->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node))) ==> F#sll_keys(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)) == F#sll_keys(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S2#6, sll_keys_reach(*((new_root->next)))))), ==(old(_dryad_S2#6, sll_keys_reach(*((new_root->next)))), old(_dryad_S3#7, sll_keys_reach(*((new_root->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_keys_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node))) ==> F#sll_keys_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)) == F#sll_keys_reach(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S2#6, sll_reach(*((new_root->next)))))), ==(old(_dryad_S2#6, sll(*((new_root->next)))), old(_dryad_S3#7, sll(*((new_root->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node))) ==> F#sll(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)) == F#sll(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S2#6, sll_reach(*((new_root->next)))))), ==(old(_dryad_S2#6, sll_reach(*((new_root->next)))), old(_dryad_S3#7, sll_reach(*((new_root->next)))))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node))) ==> F#sll_reach(_dryad_S2#6, $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)) == F#sll_reach(_dryad_S3#7, $rd_phys_ptr(_dryad_S3#7, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node));
            // assume ==(old(_dryad_S2#6, sll_keys_reach(new_root)), old(_dryad_S3#7, sll_keys_reach(new_root))); 
            assume F#sll_keys_reach(_dryad_S2#6, $phys_ptr_cast(L#new_root, ^s_node)) == F#sll_keys_reach(_dryad_S3#7, $phys_ptr_cast(L#new_root, ^s_node));
            // assume ==(old(_dryad_S2#6, sll(new_root)), old(_dryad_S3#7, sll(new_root))); 
            assume F#sll(_dryad_S2#6, $phys_ptr_cast(L#new_root, ^s_node)) == F#sll(_dryad_S3#7, $phys_ptr_cast(L#new_root, ^s_node));
            // assume ==(old(_dryad_S2#6, sll_reach(new_root)), old(_dryad_S3#7, sll_reach(new_root))); 
            assume F#sll_reach(_dryad_S2#6, $phys_ptr_cast(L#new_root, ^s_node)) == F#sll_reach(_dryad_S3#7, $phys_ptr_cast(L#new_root, ^s_node));
            // assume ==(old(_dryad_S2#6, sll_keys_reach(x)), old(_dryad_S3#7, sll_keys_reach(x))); 
            assume F#sll_keys_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys_reach(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==(old(_dryad_S2#6, sll(x)), old(_dryad_S3#7, sll(x))); 
            assume F#sll(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==(old(_dryad_S2#6, sll_reach(x)), old(_dryad_S3#7, sll_reach(x))); 
            assume F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S2#6, sll_reach(x)))), ==(old(_dryad_S2#6, sll_keys(x)), old(_dryad_S3#7, sll_keys(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S2#6, sll_keys_reach(x)))), ==(old(_dryad_S2#6, sll_keys_reach(x)), old(_dryad_S3#7, sll_keys_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_keys_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys_reach(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S2#6, sll_reach(x)))), ==(old(_dryad_S2#6, sll(x)), old(_dryad_S3#7, sll(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S2#6, sll_reach(x)))), ==(old(_dryad_S2#6, sll_reach(x)), old(_dryad_S3#7, sll_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(_dryad_S2#6, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(_dryad_S3#7, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(new_root, x)), ==(*((x->key)), old(_dryad_S2#6, *((x->key))))); 
            assume !($phys_ptr_cast(L#new_root, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)) == $rd_inv(_dryad_S2#6, s_node.key, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(new_root, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S2#6, *((x->next))))); 
            assume !($phys_ptr_cast(L#new_root, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node) == $rd_phys_ptr(_dryad_S2#6, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node);
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(new_root), ==(sll_keys(new_root), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(new_root), ==(sll_keys(new_root), @_vcc_intset_union(sll_keys(*((new_root->next))), @_vcc_intset_singleton(*((new_root->key))))))); 
            assume ($is_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_root, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_root, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_root, ^s_node)))));
            // _math \state _dryad_S4#8; 
            // _dryad_S4#8 := @_vcc_current_state(@state); 
            _dryad_S4#8 := $current_state($s);
            // _math \state stmtexpr5#19; 
            // stmtexpr5#19 := _dryad_S4#8; 
            stmtexpr5#19 := _dryad_S4#8;
            // assert @prim_writes_check((new_root->next)); 
            assert $writable_prim($s, #wrTime$3^4.3, $dot($phys_ptr_cast(L#new_root, ^s_node), s_node.next));
            // *(new_root->next) := x; 
            call $write_int(s_node.next, $phys_ptr_cast(L#new_root, ^s_node), $ptr_to_int($phys_ptr_cast(P#x, ^s_node)));
            assume $full_stop_ext(#tok$3^33.3, $s);
            // _math \state _dryad_S5#9; 
            // _dryad_S5#9 := @_vcc_current_state(@state); 
            _dryad_S5#9 := $current_state($s);
            // _math \state stmtexpr6#20; 
            // stmtexpr6#20 := _dryad_S5#9; 
            stmtexpr6#20 := _dryad_S5#9;
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S4#8, sll_reach(x)))), ==(old(_dryad_S4#8, sll_keys(x)), old(_dryad_S5#9, sll_keys(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S4#8, sll_keys_reach(x)))), ==(old(_dryad_S4#8, sll_keys_reach(x)), old(_dryad_S5#9, sll_keys_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_keys_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_keys_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#sll_keys_reach(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S4#8, sll_reach(x)))), ==(old(_dryad_S4#8, sll(x)), old(_dryad_S5#9, sll(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#sll(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(unchecked!(@_vcc_oset_in(new_root, old(_dryad_S4#8, sll_reach(x)))), ==(old(_dryad_S4#8, sll_reach(x)), old(_dryad_S5#9, sll_reach(x)))); 
            assume !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node))) ==> F#sll_reach(_dryad_S4#8, $phys_ptr_cast(P#x, ^s_node)) == F#sll_reach(_dryad_S5#9, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(new_root, x)), ==(*((x->key)), old(_dryad_S4#8, *((x->key))))); 
            assume !($phys_ptr_cast(L#new_root, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)) == $rd_inv(_dryad_S4#8, s_node.key, $phys_ptr_cast(P#x, ^s_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(new_root, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S4#8, *((x->next))))); 
            assume !($phys_ptr_cast(L#new_root, ^s_node) == $phys_ptr_cast(P#x, ^s_node)) ==> $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node) == $rd_phys_ptr(_dryad_S4#8, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node);
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(new_root), ==(sll_keys(new_root), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(new_root), ==(sll_keys(new_root), @_vcc_intset_union(sll_keys(*((new_root->next))), @_vcc_intset_singleton(*((new_root->key))))))); 
            assume ($is_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_root, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(L#new_root, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(L#new_root, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(new_root), ==(sll_keys_reach(new_root), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(new_root), ==(sll_keys_reach(new_root), @_vcc_oset_union(sll_keys_reach(*((new_root->next))), @_vcc_oset_singleton(new_root))))); 
            assume ($is_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#new_root, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(L#new_root, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_root, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(new_root), sll(new_root)), ==>(@_vcc_ptr_neq_null(new_root), ==(sll(new_root), &&(sll(*((new_root->next))), unchecked!(@_vcc_oset_in(new_root, sll_reach(*((new_root->next))))))))); 
            assume ($is_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_root, ^s_node))) && ($non_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll($s, $phys_ptr_cast(L#new_root, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(L#new_root, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(new_root), ==(sll_reach(new_root), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(new_root), ==(sll_reach(new_root), @_vcc_oset_union(sll_reach(*((new_root->next))), @_vcc_oset_singleton(new_root))))); 
            assume ($is_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_root, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(L#new_root, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(L#new_root, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(L#new_root, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(L#new_root, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys(x), @_vcc_intset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys(x), @_vcc_intset_union(sll_keys(*((x->next))), @_vcc_intset_singleton(*((x->key))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys($s, $phys_ptr_cast(P#x, ^s_node)) == $intset_union(F#sll_keys($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $intset_singleton($rd_inv($s, s_node.key, $phys_ptr_cast(P#x, ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_keys_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_keys_reach(x), @_vcc_oset_union(sll_keys_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_keys_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_keys_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), sll(x)), ==>(@_vcc_ptr_neq_null(x), ==(sll(x), &&(sll(*((x->next))), unchecked!(@_vcc_oset_in(x, sll_reach(*((x->next))))))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node))) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll($s, $phys_ptr_cast(P#x, ^s_node)) == (F#sll($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)) && !$oset_in($phys_ptr_cast(P#x, ^s_node), F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)))));
            // assume &&(==>(@_vcc_ptr_eq_null(x), ==(sll_reach(x), @_vcc_oset_empty)), ==>(@_vcc_ptr_neq_null(x), ==(sll_reach(x), @_vcc_oset_union(sll_reach(*((x->next))), @_vcc_oset_singleton(x))))); 
            assume ($is_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_empty()) && ($non_null($phys_ptr_cast(P#x, ^s_node)) ==> F#sll_reach($s, $phys_ptr_cast(P#x, ^s_node)) == $oset_union(F#sll_reach($s, $rd_phys_ptr($s, s_node.next, $phys_ptr_cast(P#x, ^s_node), ^s_node)), $oset_singleton($phys_ptr_cast(P#x, ^s_node))));
            // return new_root; 
            $result := $phys_ptr_cast(L#new_root, ^s_node);
            assume true;
            assert $position_marker();
            goto #exit;
        }
    }

  anon6:
    // skip

  #exit:
}



const unique l#public: $label;

const unique #tok$3^33.3: $token;

const unique #tok$3^32.3: $token;

const unique #tok$3^29.23: $token;

const unique #tok$3^26.3: $token;

const unique #tok$3^25.18: $token;

const unique #tok$3^21.3: $token;

const unique #tok$3^20.3: $token;

const unique #tok$3^14.19: $token;

const unique #tok$4^0.0: $token;

const unique #file^?3Cno?20file?3E: $token;

axiom $file_name_is(4, #file^?3Cno?20file?3E);

const unique #tok$3^4.3: $token;

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Csll?5Csll?2Dinsert.c: $token;

axiom $file_name_is(3, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Csll?5Csll?2Dinsert.c);

const unique #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Csll?5Cdryad_sll.h: $token;

axiom $file_name_is(2, #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Csll?5Cdryad_sll.h);

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?2Dbin?5CHeaders?5Cvccp.h: $token;

axiom $file_name_is(1, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?2Dbin?5CHeaders?5Cvccp.h);

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^s_node);
