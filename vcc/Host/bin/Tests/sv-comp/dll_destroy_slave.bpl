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

const unique ^$#_purecall_handler#1: $ctype;

axiom $def_fnptr_type(^$#_purecall_handler#1);

type $#_purecall_handler#1;

const unique ^$#_invalid_parameter_handler#2: $ctype;

axiom $def_fnptr_type(^$#_invalid_parameter_handler#2);

type $#_invalid_parameter_handler#2;

const unique ^$#dll_destroy_slave.c..36263#3: $ctype;

axiom $def_fnptr_type(^$#dll_destroy_slave.c..36263#3);

type $#dll_destroy_slave.c..36263#3;

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



procedure dll_destroy_slave(P#dll: $ptr) returns (OP#ALL_REACH: $oset);
  requires F#slave_dll($s, $phys_ptr_cast(P#dll, ^slave_item));
  modifies $s, $cev_pc;
  ensures OP#ALL_REACH == $oset_empty();
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation dll_destroy_slave(P#dll: $ptr) returns (OP#ALL_REACH: $oset)
{
  var stmtexpr2#4: $state;
  var SL#_dryad_S1: $state;
  var stmtexpr1#3: $state;
  var SL#_dryad_S0: $state;
  var stmtexpr0#2: $ptr;
  var SL#d0: $ptr;
  var L#next: $ptr;
  var loopState#0: $state;
  var L#d: $ptr;
  var stmtexpr1#6: $oset;
  var stmtexpr0#5: $oset;
  var SL#_dryad_G1: $oset;
  var SL#_dryad_G0: $oset;
  var #wrTime$2^8.3: int;
  var #stackframe: int;

// INV:PTR: P#dll, L#d
// INV:INT:
// INV:LST: slave_dll
// INV:OLD: loopState#0

  anon4:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$2^8.3, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$2^8.3 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$2^8.3, (lambda #p: $ptr :: false));
    // assume true
    // assume @decreases_level_is(2147483647); 
    assume 2147483647 == $decreases_level;
    //  --- Dryad annotated function --- 
    // _math \oset _dryad_G0; 
    // _math \oset _dryad_G1; 
    // _dryad_G0 := slave_dll_reach(dll); 
    call SL#_dryad_G0 := slave_dll_reach($phys_ptr_cast(P#dll, ^slave_item));
    assume $full_stop_ext(#tok$3^0.0, $s);
    // _math \oset stmtexpr0#5; 
    // stmtexpr0#5 := _dryad_G0; 
    stmtexpr0#5 := SL#_dryad_G0;
    // _dryad_G1 := _dryad_G0; 
    SL#_dryad_G1 := SL#_dryad_G0;
    // _math \oset stmtexpr1#6; 
    // stmtexpr1#6 := _dryad_G1; 
    stmtexpr1#6 := SL#_dryad_G1;
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll(dll), &&(&&(slave_dll(*((dll->next))), ==>(@_vcc_ptr_neq_null(*((dll->next))), @_vcc_ptr_eq_pure(*((*((dll->next))->prev)), dll))), unchecked!(@_vcc_oset_in(dll, slave_dll_reach(*((dll->next)))))))); 
    assume $non_null($phys_ptr_cast(P#dll, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(P#dll, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(P#dll, ^slave_item)) && !$oset_in($phys_ptr_cast(P#dll, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll_reach(dll), @_vcc_oset_union(slave_dll_reach(*((dll->next))), @_vcc_oset_singleton(dll)))); 
    assume $non_null($phys_ptr_cast(P#dll, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(P#dll, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(P#dll, ^slave_item)));
    // struct slave_item* d; 
    // assume ==>(@_vcc_ptr_neq_null(dll), &&(@_vcc_mutable(@state, dll), @writes_check(dll))); 
    assume $non_null($phys_ptr_cast(P#dll, ^slave_item)) ==> $mutable($s, $phys_ptr_cast(P#dll, ^slave_item)) && $top_writable($s, #wrTime$2^8.3, $phys_ptr_cast(P#dll, ^slave_item));
    // assume ==>(@_vcc_ptr_neq_null(dll), @_vcc_is_malloc_root(@state, dll)); 
    assume $non_null($phys_ptr_cast(P#dll, ^slave_item)) ==> $is_malloc_root($s, $phys_ptr_cast(P#dll, ^slave_item));
    // ALL_REACH := slave_dll_reach(dll); 
    call OP#ALL_REACH := slave_dll_reach($phys_ptr_cast(P#dll, ^slave_item));
    assume $full_stop_ext(#tok$2^15.23, $s);
    // d := dll; 
    L#d := $phys_ptr_cast(P#dll, ^slave_item);
    loopState#0 := $s;
    assume true;
    while (true)
// INV:BEGIN
      invariant F#slave_dll($s, $phys_ptr_cast(L#d, ^slave_item));
// INV:END
      invariant $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> $mutable($s, $phys_ptr_cast(L#d, ^slave_item));
      invariant $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> $top_writable($s, #wrTime$2^8.3, $phys_ptr_cast(L#d, ^slave_item));
      invariant $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> $is_malloc_root($s, $phys_ptr_cast(L#d, ^slave_item));
      invariant OP#ALL_REACH == F#slave_dll_reach($s, $phys_ptr_cast(L#d, ^slave_item));
    {
      anon3:
        assume $writes_nothing(old($s), $s);
        assume $timestamp_post(loopState#0, $s);
        assume $full_stop_ext(#tok$2^18.3, $s);
        assume true;
        // if (@_vcc_ptr_neq_null(d)) ...
        if ($non_null($phys_ptr_cast(L#d, ^slave_item)))
        {
          anon1:
            // assume ==>(@_vcc_ptr_neq_null(d), ==(slave_dll(d), &&(&&(slave_dll(*((d->next))), ==>(@_vcc_ptr_neq_null(*((d->next))), @_vcc_ptr_eq_pure(*((*((d->next))->prev)), d))), unchecked!(@_vcc_oset_in(d, slave_dll_reach(*((d->next)))))))); 
            assume $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#d, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#d, ^slave_item)) && !$oset_in($phys_ptr_cast(L#d, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item))));
            // assume ==>(@_vcc_ptr_neq_null(d), ==(slave_dll_reach(d), @_vcc_oset_union(slave_dll_reach(*((d->next))), @_vcc_oset_singleton(d)))); 
            assume $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#d, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#d, ^slave_item)));
            // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll(dll), &&(&&(slave_dll(*((dll->next))), ==>(@_vcc_ptr_neq_null(*((dll->next))), @_vcc_ptr_eq_pure(*((*((dll->next))->prev)), dll))), unchecked!(@_vcc_oset_in(dll, slave_dll_reach(*((dll->next)))))))); 
            assume $non_null($phys_ptr_cast(P#dll, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(P#dll, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(P#dll, ^slave_item)) && !$oset_in($phys_ptr_cast(P#dll, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item))));
            // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll_reach(dll), @_vcc_oset_union(slave_dll_reach(*((dll->next))), @_vcc_oset_singleton(dll)))); 
            assume $non_null($phys_ptr_cast(P#dll, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(P#dll, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(P#dll, ^slave_item)));
            // struct slave_item* next; 
            // assume ==>(&&(@_vcc_ptr_neq_null(d), @_vcc_ptr_neq_null(*((d->next)))), ==(@_vcc_is_malloc_root(@state, *((d->next))), @_vcc_is_malloc_root(@state, d))); 
            assume $non_null($phys_ptr_cast(L#d, ^slave_item)) && $non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) ==> $is_malloc_root($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) == $is_malloc_root($s, $phys_ptr_cast(L#d, ^slave_item));
            // assume ==>(&&(@_vcc_ptr_neq_null(d), @_vcc_ptr_neq_null(*((d->next)))), ==(==>(@_vcc_ptr_neq_null(*((d->next))), &&(@_vcc_mutable(@state, *((d->next))), @writes_check(*((d->next))))), ==>(@_vcc_ptr_neq_null(d), &&(@_vcc_mutable(@state, d), @writes_check(d))))); 
            assume $non_null($phys_ptr_cast(L#d, ^slave_item)) && $non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) ==> ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) ==> $mutable($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) && $top_writable($s, #wrTime$2^8.3, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item))) == ($non_null($phys_ptr_cast(L#d, ^slave_item)) ==> $mutable($s, $phys_ptr_cast(L#d, ^slave_item)) && $top_writable($s, #wrTime$2^8.3, $phys_ptr_cast(L#d, ^slave_item)));
            // struct slave_item* d0; 
            // d0 := d; 
            SL#d0 := $phys_ptr_cast(L#d, ^slave_item);
            // struct slave_item* stmtexpr0#2; 
            // stmtexpr0#2 := d0; 
            stmtexpr0#2 := $phys_ptr_cast(SL#d0, ^slave_item);
            // assume ==>(@_vcc_ptr_neq_null(d), ==(slave_dll(d), &&(&&(slave_dll(*((d->next))), ==>(@_vcc_ptr_neq_null(*((d->next))), @_vcc_ptr_eq_pure(*((*((d->next))->prev)), d))), unchecked!(@_vcc_oset_in(d, slave_dll_reach(*((d->next)))))))); 
            assume $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#d, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#d, ^slave_item)) && !$oset_in($phys_ptr_cast(L#d, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item))));
            // assume ==>(@_vcc_ptr_neq_null(d), ==(slave_dll_reach(d), @_vcc_oset_union(slave_dll_reach(*((d->next))), @_vcc_oset_singleton(d)))); 
            assume $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#d, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#d, ^slave_item)));
            // assert @reads_check_normal((d->next)); 
            assert $thread_local($s, $phys_ptr_cast(L#d, ^slave_item));
            // next := *((d->next)); 
            L#next := $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item);
            // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll(next), &&(&&(slave_dll(*((next->next))), ==>(@_vcc_ptr_neq_null(*((next->next))), @_vcc_ptr_eq_pure(*((*((next->next))->prev)), next))), unchecked!(@_vcc_oset_in(next, slave_dll_reach(*((next->next)))))))); 
            assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#next, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#next, ^slave_item)) && !$oset_in($phys_ptr_cast(L#next, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item))));
            // assume ==>(@_vcc_ptr_neq_null(next), ==(slave_dll_reach(next), @_vcc_oset_union(slave_dll_reach(*((next->next))), @_vcc_oset_singleton(next)))); 
            assume $non_null($phys_ptr_cast(L#next, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#next, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#next, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#next, ^slave_item)));
            // assume ==>(@_vcc_ptr_neq_null(d), ==(slave_dll(d), &&(&&(slave_dll(*((d->next))), ==>(@_vcc_ptr_neq_null(*((d->next))), @_vcc_ptr_eq_pure(*((*((d->next))->prev)), d))), unchecked!(@_vcc_oset_in(d, slave_dll_reach(*((d->next)))))))); 
            assume $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#d, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#d, ^slave_item)) && !$oset_in($phys_ptr_cast(L#d, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item))));
            // assume ==>(@_vcc_ptr_neq_null(d), ==(slave_dll_reach(d), @_vcc_oset_union(slave_dll_reach(*((d->next))), @_vcc_oset_singleton(d)))); 
            assume $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#d, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#d, ^slave_item)));
            // _math \state _dryad_S0; 
            // _dryad_S0 := @_vcc_current_state(@state); 
            SL#_dryad_S0 := $current_state($s);
            // _math \state stmtexpr1#3; 
            // stmtexpr1#3 := _dryad_S0; 
            stmtexpr1#3 := SL#_dryad_S0;
            // void function
            // assert @writes_check(d); 
            assert $top_writable($s, #wrTime$2^8.3, $phys_ptr_cast(L#d, ^slave_item));
            // assert @writes_check(@_vcc_extent(@state, d)); 
            assert (forall #writes$2^27.5: $ptr :: { $dont_instantiate(#writes$2^27.5) } $set_in(#writes$2^27.5, $extent($s, $phys_ptr_cast(L#d, ^slave_item))) ==> $top_writable($s, #wrTime$2^8.3, #writes$2^27.5));
            // stmt _vcc_free(d); 
            call $free($phys_ptr_cast(L#d, ^slave_item));
            assume $full_stop_ext(#tok$2^27.5, $s);
            // _math \state _dryad_S1; 
            // _dryad_S1 := @_vcc_current_state(@state); 
            SL#_dryad_S1 := $current_state($s);
            // _math \state stmtexpr2#4; 
            // stmtexpr2#4 := _dryad_S1; 
            stmtexpr2#4 := SL#_dryad_S1;
            // assume ==>(unchecked!(@_vcc_oset_in(d, old(_dryad_S0, slave_dll_reach(d0)))), ==(old(_dryad_S0, slave_dll(d0)), old(_dryad_S1, slave_dll(d0)))); 
            assume !$oset_in($phys_ptr_cast(L#d, ^slave_item), F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(SL#d0, ^slave_item))) ==> F#slave_dll(SL#_dryad_S0, $phys_ptr_cast(SL#d0, ^slave_item)) == F#slave_dll(SL#_dryad_S1, $phys_ptr_cast(SL#d0, ^slave_item));
            // assume ==>(unchecked!(@_vcc_oset_in(d, old(_dryad_S0, slave_dll_reach(d0)))), ==(old(_dryad_S0, slave_dll_reach(d0)), old(_dryad_S1, slave_dll_reach(d0)))); 
            assume !$oset_in($phys_ptr_cast(L#d, ^slave_item), F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(SL#d0, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(SL#d0, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S1, $phys_ptr_cast(SL#d0, ^slave_item));
            // assume ==>(unchecked!(@_vcc_oset_in(d, old(_dryad_S0, slave_dll_reach(next)))), ==(old(_dryad_S0, slave_dll(next)), old(_dryad_S1, slave_dll(next)))); 
            assume !$oset_in($phys_ptr_cast(L#d, ^slave_item), F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(L#next, ^slave_item))) ==> F#slave_dll(SL#_dryad_S0, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll(SL#_dryad_S1, $phys_ptr_cast(L#next, ^slave_item));
            // assume ==>(unchecked!(@_vcc_oset_in(d, old(_dryad_S0, slave_dll_reach(next)))), ==(old(_dryad_S0, slave_dll_reach(next)), old(_dryad_S1, slave_dll_reach(next)))); 
            assume !$oset_in($phys_ptr_cast(L#d, ^slave_item), F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(L#next, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(L#next, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S1, $phys_ptr_cast(L#next, ^slave_item));
            // assume ==>(unchecked!(@_vcc_oset_in(d, old(_dryad_S0, slave_dll_reach(dll)))), ==(old(_dryad_S0, slave_dll(dll)), old(_dryad_S1, slave_dll(dll)))); 
            assume !$oset_in($phys_ptr_cast(L#d, ^slave_item), F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(P#dll, ^slave_item))) ==> F#slave_dll(SL#_dryad_S0, $phys_ptr_cast(P#dll, ^slave_item)) == F#slave_dll(SL#_dryad_S1, $phys_ptr_cast(P#dll, ^slave_item));
            // assume ==>(unchecked!(@_vcc_oset_in(d, old(_dryad_S0, slave_dll_reach(dll)))), ==(old(_dryad_S0, slave_dll_reach(dll)), old(_dryad_S1, slave_dll_reach(dll)))); 
            assume !$oset_in($phys_ptr_cast(L#d, ^slave_item), F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(P#dll, ^slave_item))) ==> F#slave_dll_reach(SL#_dryad_S0, $phys_ptr_cast(P#dll, ^slave_item)) == F#slave_dll_reach(SL#_dryad_S1, $phys_ptr_cast(P#dll, ^slave_item));
            // ALL_REACH := @_vcc_oset_diff(ALL_REACH, @_vcc_oset_singleton(d)); 
            OP#ALL_REACH := $oset_diff(OP#ALL_REACH, $oset_singleton($phys_ptr_cast(L#d, ^slave_item)));
            // d := next; 
            L#d := $phys_ptr_cast(L#next, ^slave_item);
            // assume ==>(@_vcc_ptr_neq_null(d), &&(@_vcc_mutable(@state, d), @writes_check(d))); 
            assume $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> $mutable($s, $phys_ptr_cast(L#d, ^slave_item)) && $top_writable($s, #wrTime$2^8.3, $phys_ptr_cast(L#d, ^slave_item));
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
    assume $full_stop_ext(#tok$2^18.3, $s);

  #break_1:
    // assume ==>(@_vcc_ptr_neq_null(d), ==(slave_dll(d), &&(&&(slave_dll(*((d->next))), ==>(@_vcc_ptr_neq_null(*((d->next))), @_vcc_ptr_eq_pure(*((*((d->next))->prev)), d))), unchecked!(@_vcc_oset_in(d, slave_dll_reach(*((d->next)))))))); 
    assume $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(L#d, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(L#d, ^slave_item)) && !$oset_in($phys_ptr_cast(L#d, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(d), ==(slave_dll_reach(d), @_vcc_oset_union(slave_dll_reach(*((d->next))), @_vcc_oset_singleton(d)))); 
    assume $non_null($phys_ptr_cast(L#d, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(L#d, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(L#d, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(L#d, ^slave_item)));
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll(dll), &&(&&(slave_dll(*((dll->next))), ==>(@_vcc_ptr_neq_null(*((dll->next))), @_vcc_ptr_eq_pure(*((*((dll->next))->prev)), dll))), unchecked!(@_vcc_oset_in(dll, slave_dll_reach(*((dll->next)))))))); 
    assume $non_null($phys_ptr_cast(P#dll, ^slave_item)) ==> F#slave_dll($s, $phys_ptr_cast(P#dll, ^slave_item)) == (F#slave_dll($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item)) && ($non_null($rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item)) ==> $rd_phys_ptr($s, slave_item.prev, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item), ^slave_item) == $phys_ptr_cast(P#dll, ^slave_item)) && !$oset_in($phys_ptr_cast(P#dll, ^slave_item), F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item))));
    // assume ==>(@_vcc_ptr_neq_null(dll), ==(slave_dll_reach(dll), @_vcc_oset_union(slave_dll_reach(*((dll->next))), @_vcc_oset_singleton(dll)))); 
    assume $non_null($phys_ptr_cast(P#dll, ^slave_item)) ==> F#slave_dll_reach($s, $phys_ptr_cast(P#dll, ^slave_item)) == $oset_union(F#slave_dll_reach($s, $rd_phys_ptr($s, slave_item.next, $phys_ptr_cast(P#dll, ^slave_item), ^slave_item)), $oset_singleton($phys_ptr_cast(P#dll, ^slave_item)));
    // return; 
    assume true;
    assert $position_marker();
    goto #exit;

  #exit:
}



const unique l#public: $label;

const unique #tok$2^27.5: $token;

const unique #tok$2^18.3: $token;

const unique #tok$2^15.23: $token;

const unique #tok$3^0.0: $token;

const unique #file^?3Cno?20file?3E: $token;

axiom $file_name_is(3, #file^?3Cno?20file?3E);

const unique #tok$2^8.3: $token;

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Csv?2Dcomp?5Cdll_destroy_slave.c: $token;

axiom $file_name_is(2, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Csv?2Dcomp?5Cdll_destroy_slave.c);

const unique #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Csv?2Dcomp?5Cdryad_slave_dll.h: $token;

axiom $file_name_is(1, #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Csv?2Dcomp?5Cdryad_slave_dll.h);

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^slave_item);
