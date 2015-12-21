
const {:existential true} b0000 : bool;
const {:existential true} b0001 : bool;
const {:existential true} b0002 : bool;
const {:existential true} b0003 : bool;
const {:existential true} b0004 : bool;

axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

const unique ^$##thread_id: $ctype;

axiom $def_math_type(^$##thread_id);

type $##thread_id;

const unique ^$##club: $ctype;

axiom $def_math_type(^$##club);

type $##club;

const unique ^slave_item: $ctype;

axiom $is_span_sequential(^slave_item);

axiom $def_struct_type(^slave_item, 16, false, false);

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2(#s1, #s2, #p, ^slave_item) } $inv2(#s1, #s2, #p, ^slave_item) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2_without_lemmas(#s1, #s2, #p, ^slave_item) } $inv2_without_lemmas(#s1, #s2, #p, ^slave_item) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall p: $ptr, q: $ptr, s: $state :: { $in(q, $composite_extent(s, p, ^slave_item)) } $in(q, $composite_extent(s, p, ^slave_item)) == (q == p));

const unique slave_item.prev: $field;

axiom $def_phys_field(^slave_item, slave_item.prev, $ptr_to(^slave_item), false, 0);

const unique slave_item.next: $field;

axiom $def_phys_field(^slave_item, slave_item.next, $ptr_to(^slave_item), false, 8);

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

const unique ^$#dll_create_slave.c..36263#3: $ctype;

axiom $def_fnptr_type(^$#dll_create_slave.c..36263#3);

type $#dll_create_slave.c..36263#3;

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

function F#slave_dll(#s: $state, SP#hd: $ptr) : bool;

const unique cf#slave_dll: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr :: { F#slave_dll(#s, SP#hd) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#hd, ^slave_item)) ==> F#slave_dll(#s, SP#hd));

axiom $function_arg_type(cf#slave_dll, 0, ^^bool);

axiom $function_arg_type(cf#slave_dll, 1, $ptr_to(^slave_item));

procedure slave_dll(SP#hd: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#hd, ^slave_item)) ==> $result;
  free ensures $result == F#slave_dll($s, SP#hd);
  free ensures $call_transition(old($s), $s);



function F#slave_dll_reach(#s: $state, SP#hd: $ptr) : $oset;

const unique cf#slave_dll_reach: $pure_function;

axiom (forall #s: $state, SP#hd: $ptr :: { F#slave_dll_reach(#s, SP#hd) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#hd, ^slave_item)) ==> $oset_in($phys_ptr_cast(SP#hd, ^slave_item), F#slave_dll_reach(#s, SP#hd))) && ($is_null($phys_ptr_cast(SP#hd, ^slave_item)) ==> F#slave_dll_reach(#s, SP#hd) == $oset_empty()));

axiom $function_arg_type(cf#slave_dll_reach, 0, ^$#oset);

axiom $function_arg_type(cf#slave_dll_reach, 1, $ptr_to(^slave_item));

procedure slave_dll_reach(SP#hd: $ptr) returns ($result: $oset);
  ensures ($non_null($phys_ptr_cast(SP#hd, ^slave_item)) ==> $oset_in($phys_ptr_cast(SP#hd, ^slave_item), $result)) && ($is_null($phys_ptr_cast(SP#hd, ^slave_item)) ==> $result == $oset_empty());
  free ensures $result == F#slave_dll_reach($s, SP#hd);
  free ensures $call_transition(old($s), $s);



procedure abort_();
  ensures false;
  free ensures $call_transition(old($s), $s);



procedure dll_insert_slave(P#x: $ptr) returns ($result: $ptr);
  requires F#slave_dll($s, $phys_ptr_cast(P#x, ^slave_item));
  modifies $s, $cev_pc;
  ensures F#slave_dll($s, $phys_ptr_cast(P#x, ^slave_item));
  ensures F#slave_dll($s, $phys_ptr_cast($result, ^slave_item));
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation dll_insert_slave(P#x: $ptr) returns ($result: $ptr)
{
  var stmtexpr1#9: $state;
  var SL#_dryad_S9: $state;
  var stmtexpr0#8: $state;
  var SL#_dryad_S8: $state;
  var stmtexpr10#20: $state;
  var SL#_dryad_S7: $state;
  var stmtexpr9#19: $state;
  var SL#_dryad_S6: $state;
  var stmtexpr8#18: $state;
  var SL#_dryad_S5: $state;
  var stmtexpr7#17: $state;
  var SL#_dryad_S4: $state;
  var stmtexpr6#16: $state;
  var SL#_dryad_S3: $state;
  var stmtexpr5#15: $state;
  var SL#_dryad_S2: $state;
  var stmtexpr4#14: $state;
  var SL#_dryad_S1: $state;
  var stmtexpr3#13: $oset;
  var stmtexpr2#12: $state;
  var SL#_dryad_S0: $state;
  var L#item: $ptr;
  var L#next: $ptr;
  var stmtexpr1#11: $oset;
  var stmtexpr0#10: $oset;
  var SL#_dryad_G1: $oset;
  var SL#_dryad_G0: $oset;
  var #wrTime$3^8.3: int;
  var #stackframe: int;

  anon5:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$3^8.3, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$3^8.3 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$3^8.3, (lambda #p: $ptr :: false));
    // assume true
    // assume @decreases_level_is(2147483647); 
    assume 2147483647 == $decreases_level;
    // assume true
    //  --- Dryad annotated function --- 
    // _math \oset _dryad_G0; 
    // _math \oset _dryad_G1; 
    // _dryad_G0 := slave_dll_reach(x); 
    call SL#_dryad_G0 := slave_dll_reach($phys_ptr_cast(P#x, ^slave_item));
    assume $full_stop_ext(#tok$4^0.0, $s);
    // _math \oset stmtexpr0#10; 
    // stmtexpr0#10 := _dryad_G0; 
    stmtexpr0#10 := SL#_dryad_G0;
    // _dryad_G1 := _dryad_G0; 
    SL#_dryad_G1 := SL#_dryad_G0;
    // _math \oset stmtexpr1#11; 
    // stmtexpr1#11 := _dryad_G1; 
    stmtexpr1#11 := SL#_dryad_G1;
    // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll(x), &&(&&(slave_dll(*((x->next))), ==>(@_vcc_ptr_neq_null(*((x->next))), @_vcc_ptr_eq_pure(*((*((x->next))->prev)), x))), unchecked!(@_vcc_oset_in(x, slave_dll_reach(*((x->next)))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(P#x, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) && !$oset_in($phys_ptr_cast(P#x, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll_reach(x), @_vcc_oset_union(slave_dll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
    assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(P#x, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(P#x, ^slave_item)));
    // struct slave_item* next; 
    // struct slave_item* item; 
    // _math \state _dryad_S0; 
    // _dryad_S0 := @_vcc_current_state(@state); 
    SL#_dryad_S0 := $current_state($s);
    // _math \state stmtexpr2#12; 
    // stmtexpr2#12 := _dryad_S0; 
    stmtexpr2#12 := SL#_dryad_S0;
    // item := _vcc_alloc(@_vcc_typeof((struct slave_item*)@null)); 
    call L#item := $alloc(^slave_item);
    assume $full_stop_ext(#tok$3^14.30, $s);
    // assume !(@_vcc_oset_in(item, @_vcc_oset_union(_dryad_G0, _dryad_G1))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), $oset_union(SL#_dryad_G0, SL#_dryad_G1));
    // _dryad_G1 := @_vcc_oset_union(_dryad_G0, @_vcc_oset_singleton(item)); 
    SL#_dryad_G1 := $oset_union(SL#_dryad_G0, $oset_singleton($phys_ptr_cast(L#item, ^slave_item)));
    // _math \oset stmtexpr3#13; 
    // stmtexpr3#13 := _dryad_G1; 
    stmtexpr3#13 := SL#_dryad_G1;
    // assume ==(glob_reach(), _dryad_G1); 
    assume F#glob_reach() == SL#_dryad_G1;
    // _math \state _dryad_S1; 
    // _dryad_S1 := @_vcc_current_state(@state); 
    SL#_dryad_S1 := $current_state($s);
    // _math \state stmtexpr4#14; 
    // stmtexpr4#14 := _dryad_S1; 
    stmtexpr4#14 := SL#_dryad_S1;
    // assume ==>(@_vcc_ptr_neq_null(item), ==(slave_dll(item), &&(&&(slave_dll(*((item->next))), ==>(@_vcc_ptr_neq_null(*((item->next))), @_vcc_ptr_eq_pure(*((*((item->next))->prev)), item))), unchecked!(@_vcc_oset_in(item, slave_dll_reach(*((item->next)))))))); 
    assume $non_null($phys_ptr_cast(L#item, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#item, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#item, ^slave_item)) && !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(item), ==(slave_dll_reach(item), @_vcc_oset_union(slave_dll_reach(*((item->next))), @_vcc_oset_singleton(item)))); 
    assume $non_null($phys_ptr_cast(L#item, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#item, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#item, ^slave_item)));
    // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll(next), &&(&&(slave_dll(*((next->next))), ==>(@_vcc_ptr_neq_null(*((next->next))), @_vcc_ptr_eq_pure(*((*((next->next))->prev)), next))), unchecked!(@_vcc_oset_in(next, slave_dll_reach(*((next->next)))))))); 
    assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#next, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) && !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll_reach(next), @_vcc_oset_union(slave_dll_reach(*((next->next))), @_vcc_oset_singleton(next)))); 
    assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#next, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#next, ^slave_item)));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll(x), &&(&&(slave_dll(*((x->next))), ==>(@_vcc_ptr_neq_null(*((x->next))), @_vcc_ptr_eq_pure(*((*((x->next))->prev)), x))), unchecked!(@_vcc_oset_in(x, slave_dll_reach(*((x->next)))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(P#x, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) && !$oset_in($phys_ptr_cast(P#x, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll_reach(x), @_vcc_oset_union(slave_dll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
    assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(P#x, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(P#x, ^slave_item)));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S0, slave_dll_reach(next)))), ==(old(_dryad_S0, slave_dll(next)), old(_dryad_S1, slave_dll(next)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(L#next, ^slave_item))) ==> F#slave_dll(SL#_dryad_S0, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll(SL#_dryad_S1, $phys_ptr_cast(L#next, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S0, slave_dll_reach(next)))), ==(old(_dryad_S0, slave_dll_reach(next)), old(_dryad_S1, slave_dll_reach(next)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(L#next, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S1, $phys_ptr_cast(L#next, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S0, slave_dll_reach(x)))), ==(old(_dryad_S0, slave_dll(x)), old(_dryad_S1, slave_dll(x)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^slave_item))) ==> F#slave_dll(SL#_dryad_S0, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll(SL#_dryad_S1, $phys_ptr_cast(P#x, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S0, slave_dll_reach(x)))), ==(old(_dryad_S0, slave_dll_reach(x)), old(_dryad_S1, slave_dll_reach(x)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^slave_item));
    assume true;
    // if (unchecked!(@_vcc_ptr_neq_null(item))) ...
    if (!$non_null($phys_ptr_cast(L#item, ^slave_item)))
    {
      anon1:
        // void function
        // stmt abort_(); 
        call abort_();
        assume $full_stop_ext(#tok$3^16.5, $s);
    }
    else
    {
      anon2:
        // assert @_vcc_possibly_unreachable; 
        assert {:PossiblyUnreachable true} true;
    }

  anon6:
    // _math \state _dryad_S2; 
    // _dryad_S2 := @_vcc_current_state(@state); 
    SL#_dryad_S2 := $current_state($s);
    // _math \state stmtexpr5#15; 
    // stmtexpr5#15 := _dryad_S2; 
    stmtexpr5#15 := SL#_dryad_S2;
    // assert @prim_writes_check((item->next)); 
    assert $writable_prim($s, #wrTime$3^8.3, $dot($phys_ptr_cast(L#item, ^slave_item), slave_item.next));
    // *(item->next) := (struct slave_item*)@null; 
    call $write_int(slave_item.next, $phys_ptr_cast(L#item, ^slave_item), $ptr_to_int($phys_ptr_cast($null, ^slave_item)));
    assume $full_stop_ext(#tok$3^18.3, $s);
    // _math \state _dryad_S3; 
    // _dryad_S3 := @_vcc_current_state(@state); 
    SL#_dryad_S3 := $current_state($s);
    // _math \state stmtexpr6#16; 
    // stmtexpr6#16 := _dryad_S3; 
    stmtexpr6#16 := SL#_dryad_S3;
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S2, slave_dll_reach(*((item->prev)))))), ==(old(_dryad_S2, slave_dll(*((item->prev)))), old(_dryad_S3, slave_dll(*((item->prev)))))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))) ==> F#slave_dll(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) == F#slave_dll(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S2, slave_dll_reach(*((item->prev)))))), ==(old(_dryad_S2, slave_dll_reach(*((item->prev)))), old(_dryad_S3, slave_dll_reach(*((item->prev)))))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) == F#slave_dll_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S2, slave_dll_reach(next)))), ==(old(_dryad_S2, slave_dll(next)), old(_dryad_S3, slave_dll(next)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S2, $phys_ptr_cast(L#next, ^slave_item))) ==> F#slave_dll(SL#_dryad_S2, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll(SL#_dryad_S3, $phys_ptr_cast(L#next, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S2, slave_dll_reach(next)))), ==(old(_dryad_S2, slave_dll_reach(next)), old(_dryad_S3, slave_dll_reach(next)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S2, $phys_ptr_cast(L#next, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S2, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S3, $phys_ptr_cast(L#next, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S2, slave_dll_reach(x)))), ==(old(_dryad_S2, slave_dll(x)), old(_dryad_S3, slave_dll(x)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^slave_item))) ==> F#slave_dll(SL#_dryad_S2, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll(SL#_dryad_S3, $phys_ptr_cast(P#x, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S2, slave_dll_reach(x)))), ==(old(_dryad_S2, slave_dll_reach(x)), old(_dryad_S3, slave_dll_reach(x)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^slave_item));
    // assume ==>(!(@_vcc_ptr_eq_pure(item, next)), @_vcc_ptr_eq_pure(*((next->prev)), old(_dryad_S2, *((next->prev))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $phys_ptr_cast(L#next, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S2, slave_item.prev, $phys_ptr_cast(L#next, ^slave_item), ^slave_item);
    // assume ==>(!(@_vcc_ptr_eq_pure(item, next)), @_vcc_ptr_eq_pure(*((next->next)), old(_dryad_S2, *((next->next))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S2, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item);
    // assume ==>(!(@_vcc_ptr_eq_pure(item, x)), @_vcc_ptr_eq_pure(*((x->prev)), old(_dryad_S2, *((x->prev))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $phys_ptr_cast(P#x, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S2, slave_item.prev, $phys_ptr_cast(P#x, ^slave_item), ^slave_item);
    // assume ==>(!(@_vcc_ptr_eq_pure(item, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S2, *((x->next))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S2, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item);
    // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll(next), &&(&&(slave_dll(*((next->next))), ==>(@_vcc_ptr_neq_null(*((next->next))), @_vcc_ptr_eq_pure(*((*((next->next))->prev)), next))), unchecked!(@_vcc_oset_in(next, slave_dll_reach(*((next->next)))))))); 
    assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#next, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) && !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll_reach(next), @_vcc_oset_union(slave_dll_reach(*((next->next))), @_vcc_oset_singleton(next)))); 
    assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#next, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#next, ^slave_item)));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll(x), &&(&&(slave_dll(*((x->next))), ==>(@_vcc_ptr_neq_null(*((x->next))), @_vcc_ptr_eq_pure(*((*((x->next))->prev)), x))), unchecked!(@_vcc_oset_in(x, slave_dll_reach(*((x->next)))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(P#x, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) && !$oset_in($phys_ptr_cast(P#x, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll_reach(x), @_vcc_oset_union(slave_dll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
    assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(P#x, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(P#x, ^slave_item)));
    // assume ==>(@_vcc_ptr_neq_null(item), ==(slave_dll(item), &&(&&(slave_dll(*((item->next))), ==>(@_vcc_ptr_neq_null(*((item->next))), @_vcc_ptr_eq_pure(*((*((item->next))->prev)), item))), unchecked!(@_vcc_oset_in(item, slave_dll_reach(*((item->next)))))))); 
    assume $non_null($phys_ptr_cast(L#item, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#item, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#item, ^slave_item)) && !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(item), ==(slave_dll_reach(item), @_vcc_oset_union(slave_dll_reach(*((item->next))), @_vcc_oset_singleton(item)))); 
    assume $non_null($phys_ptr_cast(L#item, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#item, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#item, ^slave_item)));
    // _math \state _dryad_S4; 
    // _dryad_S4 := @_vcc_current_state(@state); 
    SL#_dryad_S4 := $current_state($s);
    // _math \state stmtexpr7#17; 
    // stmtexpr7#17 := _dryad_S4; 
    stmtexpr7#17 := SL#_dryad_S4;
    // assert @prim_writes_check((item->prev)); 
    assert $writable_prim($s, #wrTime$3^8.3, $dot($phys_ptr_cast(L#item, ^slave_item), slave_item.prev));
    // *(item->prev) := (struct slave_item*)@null; 
    call $write_int(slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), $ptr_to_int($phys_ptr_cast($null, ^slave_item)));
    assume $full_stop_ext(#tok$3^19.3, $s);
    // _math \state _dryad_S5; 
    // _dryad_S5 := @_vcc_current_state(@state); 
    SL#_dryad_S5 := $current_state($s);
    // _math \state stmtexpr8#18; 
    // stmtexpr8#18 := _dryad_S5; 
    stmtexpr8#18 := SL#_dryad_S5;
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S4, slave_dll_reach(*((item->next)))))), ==(old(_dryad_S4, slave_dll(*((item->next)))), old(_dryad_S5, slave_dll(*((item->next)))))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))) ==> F#slave_dll(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) == F#slave_dll(SL#_dryad_S5, $rd_phys_ptr(SL#_dryad_S5, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S4, slave_dll_reach(*((item->next)))))), ==(old(_dryad_S4, slave_dll_reach(*((item->next)))), old(_dryad_S5, slave_dll_reach(*((item->next)))))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) == F#slave_dll_reach(SL#_dryad_S5, $rd_phys_ptr(SL#_dryad_S5, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item));
    // assume ==(old(_dryad_S4, slave_dll(item)), old(_dryad_S5, slave_dll(item))); 
    assume F#slave_dll(SL#_dryad_S4, $phys_ptr_cast(L#item, ^slave_item)) == F#slave_dll(SL#_dryad_S5, $phys_ptr_cast(L#item, ^slave_item));
    // assume ==(old(_dryad_S4, slave_dll_reach(item)), old(_dryad_S5, slave_dll_reach(item))); 
    assume F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(L#item, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S5, $phys_ptr_cast(L#item, ^slave_item));
    // assume ==(old(_dryad_S4, slave_dll(next)), old(_dryad_S5, slave_dll(next))); 
    assume F#slave_dll(SL#_dryad_S4, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll(SL#_dryad_S5, $phys_ptr_cast(L#next, ^slave_item));
    // assume ==(old(_dryad_S4, slave_dll_reach(next)), old(_dryad_S5, slave_dll_reach(next))); 
    assume F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S5, $phys_ptr_cast(L#next, ^slave_item));
    // assume ==(old(_dryad_S4, slave_dll(x)), old(_dryad_S5, slave_dll(x))); 
    assume F#slave_dll(SL#_dryad_S4, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll(SL#_dryad_S5, $phys_ptr_cast(P#x, ^slave_item));
    // assume ==(old(_dryad_S4, slave_dll_reach(x)), old(_dryad_S5, slave_dll_reach(x))); 
    assume F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S5, $phys_ptr_cast(P#x, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S4, slave_dll_reach(next)))), ==(old(_dryad_S4, slave_dll(next)), old(_dryad_S5, slave_dll(next)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(L#next, ^slave_item))) ==> F#slave_dll(SL#_dryad_S4, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll(SL#_dryad_S5, $phys_ptr_cast(L#next, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S4, slave_dll_reach(next)))), ==(old(_dryad_S4, slave_dll_reach(next)), old(_dryad_S5, slave_dll_reach(next)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(L#next, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S5, $phys_ptr_cast(L#next, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S4, slave_dll_reach(x)))), ==(old(_dryad_S4, slave_dll(x)), old(_dryad_S5, slave_dll(x)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^slave_item))) ==> F#slave_dll(SL#_dryad_S4, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll(SL#_dryad_S5, $phys_ptr_cast(P#x, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S4, slave_dll_reach(x)))), ==(old(_dryad_S4, slave_dll_reach(x)), old(_dryad_S5, slave_dll_reach(x)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S5, $phys_ptr_cast(P#x, ^slave_item));
    // assume ==>(!(@_vcc_ptr_eq_pure(item, next)), @_vcc_ptr_eq_pure(*((next->prev)), old(_dryad_S4, *((next->prev))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $phys_ptr_cast(L#next, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S4, slave_item.prev, $phys_ptr_cast(L#next, ^slave_item), ^slave_item);
    // assume ==>(!(@_vcc_ptr_eq_pure(item, next)), @_vcc_ptr_eq_pure(*((next->next)), old(_dryad_S4, *((next->next))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S4, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item);
    // assume ==>(!(@_vcc_ptr_eq_pure(item, x)), @_vcc_ptr_eq_pure(*((x->prev)), old(_dryad_S4, *((x->prev))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $phys_ptr_cast(P#x, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S4, slave_item.prev, $phys_ptr_cast(P#x, ^slave_item), ^slave_item);
    // assume ==>(!(@_vcc_ptr_eq_pure(item, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S4, *((x->next))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S4, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item);
    // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll(next), &&(&&(slave_dll(*((next->next))), ==>(@_vcc_ptr_neq_null(*((next->next))), @_vcc_ptr_eq_pure(*((*((next->next))->prev)), next))), unchecked!(@_vcc_oset_in(next, slave_dll_reach(*((next->next)))))))); 
    assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#next, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) && !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll_reach(next), @_vcc_oset_union(slave_dll_reach(*((next->next))), @_vcc_oset_singleton(next)))); 
    assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#next, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#next, ^slave_item)));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll(x), &&(&&(slave_dll(*((x->next))), ==>(@_vcc_ptr_neq_null(*((x->next))), @_vcc_ptr_eq_pure(*((*((x->next))->prev)), x))), unchecked!(@_vcc_oset_in(x, slave_dll_reach(*((x->next)))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(P#x, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) && !$oset_in($phys_ptr_cast(P#x, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll_reach(x), @_vcc_oset_union(slave_dll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
    assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(P#x, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(P#x, ^slave_item)));
    // next := x; 
    L#next := $phys_ptr_cast(P#x, ^slave_item);
    // _math \state _dryad_S6; 
    // _dryad_S6 := @_vcc_current_state(@state); 
    SL#_dryad_S6 := $current_state($s);
    // _math \state stmtexpr9#19; 
    // stmtexpr9#19 := _dryad_S6; 
    stmtexpr9#19 := SL#_dryad_S6;
    // assert @prim_writes_check((item->next)); 
    assert $writable_prim($s, #wrTime$3^8.3, $dot($phys_ptr_cast(L#item, ^slave_item), slave_item.next));
    // *(item->next) := next; 
    call $write_int(slave_item.next, $phys_ptr_cast(L#item, ^slave_item), $ptr_to_int($phys_ptr_cast(L#next, ^slave_item)));
    assume $full_stop_ext(#tok$3^22.3, $s);
    // _math \state _dryad_S7; 
    // _dryad_S7 := @_vcc_current_state(@state); 
    SL#_dryad_S7 := $current_state($s);
    // _math \state stmtexpr10#20; 
    // stmtexpr10#20 := _dryad_S7; 
    stmtexpr10#20 := SL#_dryad_S7;
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S6, slave_dll_reach(*((item->prev)))))), ==(old(_dryad_S6, slave_dll(*((item->prev)))), old(_dryad_S7, slave_dll(*((item->prev)))))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S6, $rd_phys_ptr(SL#_dryad_S6, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))) ==> F#slave_dll(SL#_dryad_S6, $rd_phys_ptr(SL#_dryad_S6, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) == F#slave_dll(SL#_dryad_S7, $rd_phys_ptr(SL#_dryad_S7, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S6, slave_dll_reach(*((item->prev)))))), ==(old(_dryad_S6, slave_dll_reach(*((item->prev)))), old(_dryad_S7, slave_dll_reach(*((item->prev)))))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S6, $rd_phys_ptr(SL#_dryad_S6, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S6, $rd_phys_ptr(SL#_dryad_S6, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) == F#slave_dll_reach(SL#_dryad_S7, $rd_phys_ptr(SL#_dryad_S7, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S6, slave_dll_reach(next)))), ==(old(_dryad_S6, slave_dll(next)), old(_dryad_S7, slave_dll(next)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S6, $phys_ptr_cast(L#next, ^slave_item))) ==> F#slave_dll(SL#_dryad_S6, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll(SL#_dryad_S7, $phys_ptr_cast(L#next, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S6, slave_dll_reach(next)))), ==(old(_dryad_S6, slave_dll_reach(next)), old(_dryad_S7, slave_dll_reach(next)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S6, $phys_ptr_cast(L#next, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S6, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S7, $phys_ptr_cast(L#next, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S6, slave_dll_reach(x)))), ==(old(_dryad_S6, slave_dll(x)), old(_dryad_S7, slave_dll(x)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S6, $phys_ptr_cast(P#x, ^slave_item))) ==> F#slave_dll(SL#_dryad_S6, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll(SL#_dryad_S7, $phys_ptr_cast(P#x, ^slave_item));
    // assume ==>(unchecked!(@_vcc_oset_in(item, old(_dryad_S6, slave_dll_reach(x)))), ==(old(_dryad_S6, slave_dll_reach(x)), old(_dryad_S7, slave_dll_reach(x)))); 
    assume !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach(SL#_dryad_S6, $phys_ptr_cast(P#x, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S6, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S7, $phys_ptr_cast(P#x, ^slave_item));
    // assume ==>(!(@_vcc_ptr_eq_pure(item, next)), @_vcc_ptr_eq_pure(*((next->prev)), old(_dryad_S6, *((next->prev))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $phys_ptr_cast(L#next, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S6, slave_item.prev, $phys_ptr_cast(L#next, ^slave_item), ^slave_item);
    // assume ==>(!(@_vcc_ptr_eq_pure(item, next)), @_vcc_ptr_eq_pure(*((next->next)), old(_dryad_S6, *((next->next))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S6, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item);
    // assume ==>(!(@_vcc_ptr_eq_pure(item, x)), @_vcc_ptr_eq_pure(*((x->prev)), old(_dryad_S6, *((x->prev))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $phys_ptr_cast(P#x, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S6, slave_item.prev, $phys_ptr_cast(P#x, ^slave_item), ^slave_item);
    // assume ==>(!(@_vcc_ptr_eq_pure(item, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S6, *((x->next))))); 
    assume !($phys_ptr_cast(L#item, ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S6, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item);
    // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll(next), &&(&&(slave_dll(*((next->next))), ==>(@_vcc_ptr_neq_null(*((next->next))), @_vcc_ptr_eq_pure(*((*((next->next))->prev)), next))), unchecked!(@_vcc_oset_in(next, slave_dll_reach(*((next->next)))))))); 
    assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#next, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) && !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll_reach(next), @_vcc_oset_union(slave_dll_reach(*((next->next))), @_vcc_oset_singleton(next)))); 
    assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#next, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#next, ^slave_item)));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll(x), &&(&&(slave_dll(*((x->next))), ==>(@_vcc_ptr_neq_null(*((x->next))), @_vcc_ptr_eq_pure(*((*((x->next))->prev)), x))), unchecked!(@_vcc_oset_in(x, slave_dll_reach(*((x->next)))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(P#x, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) && !$oset_in($phys_ptr_cast(P#x, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll_reach(x), @_vcc_oset_union(slave_dll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
    assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(P#x, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(P#x, ^slave_item)));
    // assume ==>(@_vcc_ptr_neq_null(item), ==(slave_dll(item), &&(&&(slave_dll(*((item->next))), ==>(@_vcc_ptr_neq_null(*((item->next))), @_vcc_ptr_eq_pure(*((*((item->next))->prev)), item))), unchecked!(@_vcc_oset_in(item, slave_dll_reach(*((item->next)))))))); 
    assume $non_null($phys_ptr_cast(L#item, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#item, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#item, ^slave_item)) && !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(item), ==(slave_dll_reach(item), @_vcc_oset_union(slave_dll_reach(*((item->next))), @_vcc_oset_singleton(item)))); 
    assume $non_null($phys_ptr_cast(L#item, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#item, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#item, ^slave_item)));
    // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll(next), &&(&&(slave_dll(*((next->next))), ==>(@_vcc_ptr_neq_null(*((next->next))), @_vcc_ptr_eq_pure(*((*((next->next))->prev)), next))), unchecked!(@_vcc_oset_in(next, slave_dll_reach(*((next->next)))))))); 
    assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#next, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) && !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll_reach(next), @_vcc_oset_union(slave_dll_reach(*((next->next))), @_vcc_oset_singleton(next)))); 
    assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#next, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#next, ^slave_item)));
    assume true;
    // if (@_vcc_ptr_neq_null(next)) ...
    if ($non_null($phys_ptr_cast(L#next, ^slave_item)))
    {
      anon3:
        // _math \state _dryad_S8; 
        // _dryad_S8 := @_vcc_current_state(@state); 
        SL#_dryad_S8 := $current_state($s);
        // _math \state stmtexpr0#8; 
        // stmtexpr0#8 := _dryad_S8; 
        stmtexpr0#8 := SL#_dryad_S8;
        // assert @prim_writes_check((next->prev)); 
        assert $writable_prim($s, #wrTime$3^8.3, $dot($phys_ptr_cast(L#next, ^slave_item), slave_item.prev));
        // *(next->prev) := item; 
        call $write_int(slave_item.prev, $phys_ptr_cast(L#next, ^slave_item), $ptr_to_int($phys_ptr_cast(L#item, ^slave_item)));
        assume $full_stop_ext(#tok$3^24.5, $s);
        // _math \state _dryad_S9; 
        // _dryad_S9 := @_vcc_current_state(@state); 
        SL#_dryad_S9 := $current_state($s);
        // _math \state stmtexpr1#9; 
        // stmtexpr1#9 := _dryad_S9; 
        stmtexpr1#9 := SL#_dryad_S9;
        // assume ==>(unchecked!(@_vcc_oset_in(next, old(_dryad_S8, slave_dll_reach(*((next->next)))))), ==(old(_dryad_S8, slave_dll(*((next->next)))), old(_dryad_S9, slave_dll(*((next->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item))) ==> F#slave_dll(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) == F#slave_dll(SL#_dryad_S9, $rd_phys_ptr(SL#_dryad_S9, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item));
        // assume ==>(unchecked!(@_vcc_oset_in(next, old(_dryad_S8, slave_dll_reach(*((next->next)))))), ==(old(_dryad_S8, slave_dll_reach(*((next->next)))), old(_dryad_S9, slave_dll_reach(*((next->next)))))); 
        assume !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S8, $rd_phys_ptr(SL#_dryad_S8, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) == F#slave_dll_reach(SL#_dryad_S9, $rd_phys_ptr(SL#_dryad_S9, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item));
        // assume ==(old(_dryad_S8, slave_dll(next)), old(_dryad_S9, slave_dll(next))); 
        assume F#slave_dll(SL#_dryad_S8, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll(SL#_dryad_S9, $phys_ptr_cast(L#next, ^slave_item));
        // assume ==(old(_dryad_S8, slave_dll_reach(next)), old(_dryad_S9, slave_dll_reach(next))); 
        assume F#slave_dll_reach(SL#_dryad_S8, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S9, $phys_ptr_cast(L#next, ^slave_item));
        // assume ==>(unchecked!(@_vcc_oset_in(next, old(_dryad_S8, slave_dll_reach(item)))), ==(old(_dryad_S8, slave_dll(item)), old(_dryad_S9, slave_dll(item)))); 
        assume !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach(SL#_dryad_S8, $phys_ptr_cast(L#item, ^slave_item))) ==> F#slave_dll(SL#_dryad_S8, $phys_ptr_cast(L#item, ^slave_item)) == F#slave_dll(SL#_dryad_S9, $phys_ptr_cast(L#item, ^slave_item));
        // assume ==>(unchecked!(@_vcc_oset_in(next, old(_dryad_S8, slave_dll_reach(item)))), ==(old(_dryad_S8, slave_dll_reach(item)), old(_dryad_S9, slave_dll_reach(item)))); 
        assume !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach(SL#_dryad_S8, $phys_ptr_cast(L#item, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S8, $phys_ptr_cast(L#item, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S9, $phys_ptr_cast(L#item, ^slave_item));
        // assume ==>(unchecked!(@_vcc_oset_in(next, old(_dryad_S8, slave_dll_reach(x)))), ==(old(_dryad_S8, slave_dll(x)), old(_dryad_S9, slave_dll(x)))); 
        assume !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach(SL#_dryad_S8, $phys_ptr_cast(P#x, ^slave_item))) ==> F#slave_dll(SL#_dryad_S8, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll(SL#_dryad_S9, $phys_ptr_cast(P#x, ^slave_item));
        // assume ==>(unchecked!(@_vcc_oset_in(next, old(_dryad_S8, slave_dll_reach(x)))), ==(old(_dryad_S8, slave_dll_reach(x)), old(_dryad_S9, slave_dll_reach(x)))); 
        assume !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach(SL#_dryad_S8, $phys_ptr_cast(P#x, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S8, $phys_ptr_cast(P#x, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S9, $phys_ptr_cast(P#x, ^slave_item));
        // assume ==>(!(@_vcc_ptr_eq_pure(next, item)), @_vcc_ptr_eq_pure(*((item->prev)), old(_dryad_S8, *((item->prev))))); 
        assume !($phys_ptr_cast(L#next, ^slave_item) == $phys_ptr_cast(L#item, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S8, slave_item.prev, $phys_ptr_cast(L#item, ^slave_item), ^slave_item);
        // assume ==>(!(@_vcc_ptr_eq_pure(next, item)), @_vcc_ptr_eq_pure(*((item->next)), old(_dryad_S8, *((item->next))))); 
        assume !($phys_ptr_cast(L#next, ^slave_item) == $phys_ptr_cast(L#item, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S8, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item);
        // assume ==>(!(@_vcc_ptr_eq_pure(next, x)), @_vcc_ptr_eq_pure(*((x->prev)), old(_dryad_S8, *((x->prev))))); 
        assume !($phys_ptr_cast(L#next, ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $phys_ptr_cast(P#x, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S8, slave_item.prev, $phys_ptr_cast(P#x, ^slave_item), ^slave_item);
        // assume ==>(!(@_vcc_ptr_eq_pure(next, x)), @_vcc_ptr_eq_pure(*((x->next)), old(_dryad_S8, *((x->next))))); 
        assume !($phys_ptr_cast(L#next, ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) ==> $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item) == $rd_phys_ptr(SL#_dryad_S8, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item);
        // assume ==>(@_vcc_ptr_neq_null(item), ==(slave_dll(item), &&(&&(slave_dll(*((item->next))), ==>(@_vcc_ptr_neq_null(*((item->next))), @_vcc_ptr_eq_pure(*((*((item->next))->prev)), item))), unchecked!(@_vcc_oset_in(item, slave_dll_reach(*((item->next)))))))); 
        assume $non_null($phys_ptr_cast(L#item, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#item, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#item, ^slave_item)) && !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))));
        // assume ==>(@_vcc_ptr_neq_null(item), ==(slave_dll_reach(item), @_vcc_oset_union(slave_dll_reach(*((item->next))), @_vcc_oset_singleton(item)))); 
        assume $non_null($phys_ptr_cast(L#item, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#item, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#item, ^slave_item)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll(x), &&(&&(slave_dll(*((x->next))), ==>(@_vcc_ptr_neq_null(*((x->next))), @_vcc_ptr_eq_pure(*((*((x->next))->prev)), x))), unchecked!(@_vcc_oset_in(x, slave_dll_reach(*((x->next)))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(P#x, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(P#x, ^slave_item)) && !$oset_in($phys_ptr_cast(P#x, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(slave_dll_reach(x), @_vcc_oset_union(slave_dll_reach(*((x->next))), @_vcc_oset_singleton(x)))); 
        assume $non_null($phys_ptr_cast(P#x, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(P#x, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#x, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(P#x, ^slave_item)));
        // assume ==>(@_vcc_ptr_neq_null(item), ==(slave_dll(item), &&(&&(slave_dll(*((item->next))), ==>(@_vcc_ptr_neq_null(*((item->next))), @_vcc_ptr_eq_pure(*((*((item->next))->prev)), item))), unchecked!(@_vcc_oset_in(item, slave_dll_reach(*((item->next)))))))); 
        assume $non_null($phys_ptr_cast(L#item, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#item, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#item, ^slave_item)) && !$oset_in($phys_ptr_cast(L#item, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item))));
        // assume ==>(@_vcc_ptr_neq_null(item), ==(slave_dll_reach(item), @_vcc_oset_union(slave_dll_reach(*((item->next))), @_vcc_oset_singleton(item)))); 
        assume $non_null($phys_ptr_cast(L#item, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#item, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#item, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#item, ^slave_item)));
    }
    else
    {
      anon4:
        // assert @_vcc_possibly_unreachable; 
        assert {:PossiblyUnreachable true} true;
    }

  anon7:
    // return item; 
    $result := $phys_ptr_cast(L#item, ^slave_item);
    assume true;
    assert $position_marker();
    goto #exit;

  anon8:
    // skip

  #exit:
}



procedure dll_create_slave(P#n: int) returns ($result: $ptr);
  modifies $s, $cev_pc;
  ensures F#slave_dll($s, $phys_ptr_cast($result, ^slave_item));
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation dll_create_slave(P#n: int) returns ($result: $ptr)
{
  var stmtexpr3#24: $oset;
  var res_slave_dll_reach#7: $oset;
  var stmtexpr2#23: $oset;
  var res_slave_dll_reach#6: $oset;
  var stmtexpr1#22: $state;
  var SL#_dryad_S5: $state;
  var stmtexpr0#21: $state;
  var SL#_dryad_S4: $state;
  var loopState#0: $state;
  var stmtexpr9#34: $oset;
  var res_slave_dll_reach#5: $oset;
  var stmtexpr8#33: $oset;
  var res_slave_dll_reach#4: $oset;
  var stmtexpr7#32: $state;
  var SL#_dryad_S3: $state;
  var stmtexpr6#31: $state;
  var SL#_dryad_S2: $state;
  var stmtexpr5#30: $oset;
  var res_slave_dll_reach#3: $oset;
  var stmtexpr4#29: $oset;
  var res_slave_dll_reach#2: $oset;
  var stmtexpr3#28: $state;
  var SL#_dryad_S1: $state;
  var stmtexpr2#27: $state;
  var SL#_dryad_S0: $state;
  var L#dll: $ptr;
  var stmtexpr1#26: $oset;
  var stmtexpr0#25: $oset;
  var SL#_dryad_G1: $oset;
  var SL#_dryad_G0: $oset;
  var #wrTime$3^29.3: int;
  var #stackframe: int;

// INV:PTR: L#dll
// INV:INT: P#n
// INV:LST: slave_dll
// INV:OLD: loopState#0


  anon12:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$3^29.3, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$3^29.3 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$3^29.3, (lambda #p: $ptr :: false));
    // assume @in_range_i4(n); 
    assume $in_range_i4(P#n);
    // assume @decreases_level_is(2147483647); 
    assume 2147483647 == $decreases_level;
    //  --- Dryad annotated function --- 
    // _math \oset _dryad_G0; 
    // _math \oset _dryad_G1; 
    // _dryad_G0 := @_vcc_oset_empty; 
    SL#_dryad_G0 := $oset_empty();
    // _math \oset stmtexpr0#25; 
    // stmtexpr0#25 := _dryad_G0; 
    stmtexpr0#25 := SL#_dryad_G0;
    // _dryad_G1 := _dryad_G0; 
    SL#_dryad_G1 := SL#_dryad_G0;
    // _math \oset stmtexpr1#26; 
    // stmtexpr1#26 := _dryad_G1; 
    stmtexpr1#26 := SL#_dryad_G1;
    // struct slave_item* dll; 
    // dll := (struct slave_item*)@null; 
    L#dll := $phys_ptr_cast($null, ^slave_item);
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll(dll), &&(&&(slave_dll(*((dll->next))), ==>(@_vcc_ptr_neq_null(*((dll->next))), @_vcc_ptr_eq_pure(*((*((dll->next))->prev)), dll))), unchecked!(@_vcc_oset_in(dll, slave_dll_reach(*((dll->next)))))))); 
    assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#dll, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#dll, ^slave_item)) && !$oset_in($phys_ptr_cast(L#dll, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll_reach(dll), @_vcc_oset_union(slave_dll_reach(*((dll->next))), @_vcc_oset_singleton(dll)))); 
    assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#dll, ^slave_item)));
    // _math \state _dryad_S0; 
    // _dryad_S0 := @_vcc_current_state(@state); 
    SL#_dryad_S0 := $current_state($s);
    // _math \state stmtexpr2#27; 
    // stmtexpr2#27 := _dryad_S0; 
    stmtexpr2#27 := SL#_dryad_S0;
    // non-pure function
    // dll := dll_insert_slave(dll); 
    call L#dll := dll_insert_slave($phys_ptr_cast(L#dll, ^slave_item));
    assume $full_stop_ext(#tok$3^34.9, $s);
    // _math \state _dryad_S1; 
    // _dryad_S1 := @_vcc_current_state(@state); 
    SL#_dryad_S1 := $current_state($s);
    // _math \state stmtexpr3#28; 
    // stmtexpr3#28 := _dryad_S1; 
    stmtexpr3#28 := SL#_dryad_S1;
    // assume @_vcc_oset_disjoint(slave_dll_reach(dll), @_vcc_oset_diff(_dryad_G1, old(_dryad_S0, slave_dll_reach(dll)))); 
    assume $oset_disjoint(F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)), $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(L#dll, ^slave_item))));
    // assume @_vcc_oset_disjoint(slave_dll_reach(dll), @_vcc_oset_diff(_dryad_G1, old(_dryad_S0, slave_dll_reach(dll)))); 
    assume $oset_disjoint(F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)), $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(L#dll, ^slave_item))));
    // _math \oset res_slave_dll_reach#2; 
    // res_slave_dll_reach#2 := slave_dll_reach(dll); 
    call res_slave_dll_reach#2 := slave_dll_reach($phys_ptr_cast(L#dll, ^slave_item));
    assume $full_stop_ext(#tok$4^0.0, $s);
    // _dryad_G1 := @_vcc_oset_union(res_slave_dll_reach#2, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S0, slave_dll_reach(dll))))); 
    SL#_dryad_G1 := $oset_union(res_slave_dll_reach#2, $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(L#dll, ^slave_item))));
    // _math \oset stmtexpr4#29; 
    // stmtexpr4#29 := _dryad_G1; 
    stmtexpr4#29 := SL#_dryad_G1;
    // _math \oset res_slave_dll_reach#3; 
    // res_slave_dll_reach#3 := slave_dll_reach(dll); 
    call res_slave_dll_reach#3 := slave_dll_reach($phys_ptr_cast(L#dll, ^slave_item));
    assume $full_stop_ext(#tok$4^0.0, $s);
    // _dryad_G1 := @_vcc_oset_union(res_slave_dll_reach#3, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S0, slave_dll_reach(dll))))); 
    SL#_dryad_G1 := $oset_union(res_slave_dll_reach#3, $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(L#dll, ^slave_item))));
    // _math \oset stmtexpr5#30; 
    // stmtexpr5#30 := _dryad_G1; 
    stmtexpr5#30 := SL#_dryad_G1;
    // assume ==(glob_reach(), _dryad_G1); 
    assume F#glob_reach() == SL#_dryad_G1;
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll(dll), &&(&&(slave_dll(*((dll->next))), ==>(@_vcc_ptr_neq_null(*((dll->next))), @_vcc_ptr_eq_pure(*((*((dll->next))->prev)), dll))), unchecked!(@_vcc_oset_in(dll, slave_dll_reach(*((dll->next)))))))); 
    assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#dll, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#dll, ^slave_item)) && !$oset_in($phys_ptr_cast(L#dll, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll_reach(dll), @_vcc_oset_union(slave_dll_reach(*((dll->next))), @_vcc_oset_singleton(dll)))); 
    assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#dll, ^slave_item)));
    // _math \state _dryad_S2; 
    // _dryad_S2 := @_vcc_current_state(@state); 
    SL#_dryad_S2 := $current_state($s);
    // _math \state stmtexpr6#31; 
    // stmtexpr6#31 := _dryad_S2; 
    stmtexpr6#31 := SL#_dryad_S2;
    // non-pure function
    // dll := dll_insert_slave(dll); 
    call L#dll := dll_insert_slave($phys_ptr_cast(L#dll, ^slave_item));
    assume $full_stop_ext(#tok$3^35.9, $s);
    // _math \state _dryad_S3; 
    // _dryad_S3 := @_vcc_current_state(@state); 
    SL#_dryad_S3 := $current_state($s);
    // _math \state stmtexpr7#32; 
    // stmtexpr7#32 := _dryad_S3; 
    stmtexpr7#32 := SL#_dryad_S3;
    // assume @_vcc_oset_disjoint(slave_dll_reach(dll), @_vcc_oset_diff(_dryad_G1, old(_dryad_S2, slave_dll_reach(dll)))); 
    assume $oset_disjoint(F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)), $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S2, $phys_ptr_cast(L#dll, ^slave_item))));
    // assume @_vcc_oset_disjoint(slave_dll_reach(dll), @_vcc_oset_diff(_dryad_G1, old(_dryad_S2, slave_dll_reach(dll)))); 
    assume $oset_disjoint(F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)), $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S2, $phys_ptr_cast(L#dll, ^slave_item))));
    // _math \oset res_slave_dll_reach#4; 
    // res_slave_dll_reach#4 := slave_dll_reach(dll); 
    call res_slave_dll_reach#4 := slave_dll_reach($phys_ptr_cast(L#dll, ^slave_item));
    assume $full_stop_ext(#tok$4^0.0, $s);
    // _dryad_G1 := @_vcc_oset_union(res_slave_dll_reach#4, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S2, slave_dll_reach(dll))))); 
    SL#_dryad_G1 := $oset_union(res_slave_dll_reach#4, $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S2, $phys_ptr_cast(L#dll, ^slave_item))));
    // _math \oset stmtexpr8#33; 
    // stmtexpr8#33 := _dryad_G1; 
    stmtexpr8#33 := SL#_dryad_G1;
    // _math \oset res_slave_dll_reach#5; 
    // res_slave_dll_reach#5 := slave_dll_reach(dll); 
    call res_slave_dll_reach#5 := slave_dll_reach($phys_ptr_cast(L#dll, ^slave_item));
    assume $full_stop_ext(#tok$4^0.0, $s);
    // _dryad_G1 := @_vcc_oset_union(res_slave_dll_reach#5, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S2, slave_dll_reach(dll))))); 
    SL#_dryad_G1 := $oset_union(res_slave_dll_reach#5, $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S2, $phys_ptr_cast(L#dll, ^slave_item))));
    // _math \oset stmtexpr9#34; 
    // stmtexpr9#34 := _dryad_G1; 
    stmtexpr9#34 := SL#_dryad_G1;
    // assume ==(glob_reach(), _dryad_G1); 
    assume F#glob_reach() == SL#_dryad_G1;
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll(dll), &&(&&(slave_dll(*((dll->next))), ==>(@_vcc_ptr_neq_null(*((dll->next))), @_vcc_ptr_eq_pure(*((*((dll->next))->prev)), dll))), unchecked!(@_vcc_oset_in(dll, slave_dll_reach(*((dll->next)))))))); 
    assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#dll, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#dll, ^slave_item)) && !$oset_in($phys_ptr_cast(L#dll, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll_reach(dll), @_vcc_oset_union(slave_dll_reach(*((dll->next))), @_vcc_oset_singleton(dll)))); 
    assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#dll, ^slave_item)));
    loopState#0 := $s;
    assume true;
    while (true)
invariant b0000 ==> (F#slave_dll($s,$phys_ptr_cast(L#dll,^slave_item)));
invariant b0001 ==> ($non_null($phys_ptr_cast(L#dll,^slave_item)));
invariant b0002 ==> ($is_null($phys_ptr_cast(L#dll,^slave_item)));
invariant b0003 ==> (($non_null($phys_ptr_cast(L#dll,^slave_item)) ==> $non_null($rd_phys_ptr($s,slave_item.next,$phys_ptr_cast(L#dll,^slave_item),^slave_item))));
invariant b0004 ==> (($non_null($phys_ptr_cast(L#dll,^slave_item)) ==> $is_null($rd_phys_ptr($s,slave_item.next,$phys_ptr_cast(L#dll,^slave_item),^slave_item))));

    {
      anon11:
        assume $writes_nothing(old($s), $s);
        assume $timestamp_post(loopState#0, $s);
        assume $full_stop_ext(#tok$3^36.3, $s);
        // assume @_vcc_mutable_increases(old(@prestate, @state), @state); 
        assume $mutable_increases(loopState#0, $s);
        assume true;
        // if (>(n, 0)) ...
        if (P#n > 0)
        {
          anon9:
            // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll(dll), &&(&&(slave_dll(*((dll->next))), ==>(@_vcc_ptr_neq_null(*((dll->next))), @_vcc_ptr_eq_pure(*((*((dll->next))->prev)), dll))), unchecked!(@_vcc_oset_in(dll, slave_dll_reach(*((dll->next)))))))); 
            assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#dll, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#dll, ^slave_item)) && !$oset_in($phys_ptr_cast(L#dll, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item))));
            // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll_reach(dll), @_vcc_oset_union(slave_dll_reach(*((dll->next))), @_vcc_oset_singleton(dll)))); 
            assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#dll, ^slave_item)));
            // _math \state _dryad_S4; 
            // _dryad_S4 := @_vcc_current_state(@state); 
            SL#_dryad_S4 := $current_state($s);
            // _math \state stmtexpr0#21; 
            // stmtexpr0#21 := _dryad_S4; 
            stmtexpr0#21 := SL#_dryad_S4;
            // non-pure function
            // dll := dll_insert_slave(dll); 
            call L#dll := dll_insert_slave($phys_ptr_cast(L#dll, ^slave_item));
            assume $full_stop_ext(#tok$3^39.11, $s);
            // _math \state _dryad_S5; 
            // _dryad_S5 := @_vcc_current_state(@state); 
            SL#_dryad_S5 := $current_state($s);
            // _math \state stmtexpr1#22; 
            // stmtexpr1#22 := _dryad_S5; 
            stmtexpr1#22 := SL#_dryad_S5;
            // assume @_vcc_oset_disjoint(slave_dll_reach(dll), @_vcc_oset_diff(_dryad_G1, old(_dryad_S4, slave_dll_reach(dll)))); 
            assume $oset_disjoint(F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)), $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(L#dll, ^slave_item))));
            // assume @_vcc_oset_disjoint(slave_dll_reach(dll), @_vcc_oset_diff(_dryad_G1, old(_dryad_S4, slave_dll_reach(dll)))); 
            assume $oset_disjoint(F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)), $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(L#dll, ^slave_item))));
            // _math \oset res_slave_dll_reach#6; 
            // res_slave_dll_reach#6 := slave_dll_reach(dll); 
            call res_slave_dll_reach#6 := slave_dll_reach($phys_ptr_cast(L#dll, ^slave_item));
            assume $full_stop_ext(#tok$4^0.0, $s);
            // _dryad_G1 := @_vcc_oset_union(res_slave_dll_reach#6, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S4, slave_dll_reach(dll))))); 
            SL#_dryad_G1 := $oset_union(res_slave_dll_reach#6, $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(L#dll, ^slave_item))));
            // _math \oset stmtexpr2#23; 
            // stmtexpr2#23 := _dryad_G1; 
            stmtexpr2#23 := SL#_dryad_G1;
            // _math \oset res_slave_dll_reach#7; 
            // res_slave_dll_reach#7 := slave_dll_reach(dll); 
            call res_slave_dll_reach#7 := slave_dll_reach($phys_ptr_cast(L#dll, ^slave_item));
            assume $full_stop_ext(#tok$4^0.0, $s);
            // _dryad_G1 := @_vcc_oset_union(res_slave_dll_reach#7, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S4, slave_dll_reach(dll))))); 
            SL#_dryad_G1 := $oset_union(res_slave_dll_reach#7, $oset_diff(SL#_dryad_G1, F#slave_dll_reach(SL#_dryad_S4, $phys_ptr_cast(L#dll, ^slave_item))));
            // _math \oset stmtexpr3#24; 
            // stmtexpr3#24 := _dryad_G1; 
            stmtexpr3#24 := SL#_dryad_G1;
            // assume ==(glob_reach(), _dryad_G1); 
            assume F#glob_reach() == SL#_dryad_G1;
            // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll(dll), &&(&&(slave_dll(*((dll->next))), ==>(@_vcc_ptr_neq_null(*((dll->next))), @_vcc_ptr_eq_pure(*((*((dll->next))->prev)), dll))), unchecked!(@_vcc_oset_in(dll, slave_dll_reach(*((dll->next)))))))); 
            assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#dll, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#dll, ^slave_item)) && !$oset_in($phys_ptr_cast(L#dll, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item))));
            // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll_reach(dll), @_vcc_oset_union(slave_dll_reach(*((dll->next))), @_vcc_oset_singleton(dll)))); 
            assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#dll, ^slave_item)));
        }
        else
        {
          anon10:
            // assert @_vcc_possibly_unreachable; 
            assert {:PossiblyUnreachable true} true;
            // goto #break_1; 
            goto #break_1;
        }

      #continue_1:
        assume true;
    }

  anon13:
    assume $full_stop_ext(#tok$3^36.3, $s);

  #break_1:
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll(dll), &&(&&(slave_dll(*((dll->next))), ==>(@_vcc_ptr_neq_null(*((dll->next))), @_vcc_ptr_eq_pure(*((*((dll->next))->prev)), dll))), unchecked!(@_vcc_oset_in(dll, slave_dll_reach(*((dll->next)))))))); 
    assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#dll, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#dll, ^slave_item)) && !$oset_in($phys_ptr_cast(L#dll, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll_reach(dll), @_vcc_oset_union(slave_dll_reach(*((dll->next))), @_vcc_oset_singleton(dll)))); 
    assume $non_null($phys_ptr_cast(L#dll, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#dll, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#dll, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#dll, ^slave_item)));
    // return dll; 
    $result := $phys_ptr_cast(L#dll, ^slave_item);
    assume true;
    assert $position_marker();
    goto #exit;

  anon14:
    // skip

  #exit:
}



const unique l#public: $label;

const unique #tok$3^39.11: $token;

const unique #tok$3^36.3: $token;

const unique #tok$3^35.9: $token;

const unique #tok$3^34.9: $token;

const unique #tok$3^29.3: $token;

const unique #tok$3^24.5: $token;

const unique #tok$3^22.3: $token;

const unique #tok$3^19.3: $token;

const unique #tok$3^18.3: $token;

const unique #tok$3^16.5: $token;

const unique #tok$3^14.30: $token;

const unique #tok$4^0.0: $token;

const unique #file^?3Cno?20file?3E: $token;

axiom $file_name_is(4, #file^?3Cno?20file?3E);

const unique #tok$3^8.3: $token;

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Csv?2Dcomp?5Cdll_create_slave.c: $token;

axiom $file_name_is(3, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Csv?2Dcomp?5Cdll_create_slave.c);

const unique #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Csv?2Dcomp?5Cdryad_slave_dll.h: $token;

axiom $file_name_is(2, #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Csv?2Dcomp?5Cdryad_slave_dll.h);

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?2Dbin?5CHeaders?5Cvccp.h: $token;

axiom $file_name_is(1, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?2Dbin?5CHeaders?5Cvccp.h);

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^slave_item);

