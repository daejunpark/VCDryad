axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

const unique ^$##thread_id: $ctype;

axiom $def_math_type(^$##thread_id);

type $##thread_id;

const unique ^$##club: $ctype;

axiom $def_math_type(^$##club);

type $##club;

const unique ^r_node: $ctype;

axiom $is_span_sequential(^r_node);

axiom $def_struct_type(^r_node, 24, false, false);

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2(#s1, #s2, #p, ^r_node) } $inv2(#s1, #s2, #p, ^r_node) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2_without_lemmas(#s1, #s2, #p, ^r_node) } $inv2_without_lemmas(#s1, #s2, #p, ^r_node) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall p: $ptr, q: $ptr, s: $state :: { $in(q, $composite_extent(s, p, ^r_node)) } $in(q, $composite_extent(s, p, ^r_node)) == (q == p));

const unique r_node.left: $field;

axiom $def_phys_field(^r_node, r_node.left, $ptr_to(^r_node), false, 0);

const unique r_node.right: $field;

axiom $def_phys_field(^r_node, r_node.right, $ptr_to(^r_node), false, 8);

const unique r_node.key: $field;

axiom $def_phys_field(^r_node, r_node.key, ^^i4, false, 16);

const unique r_node.color: $field;

axiom $def_phys_field(^r_node, r_node.color, ^^i4, false, 20);

const unique ^$#_purecall_handler#1: $ctype;

axiom $def_fnptr_type(^$#_purecall_handler#1);

type $#_purecall_handler#1;

const unique ^$#_invalid_parameter_handler#2: $ctype;

axiom $def_fnptr_type(^$#_invalid_parameter_handler#2);

type $#_invalid_parameter_handler#2;

const unique ^$#rbt_find_smallest.c..36261#3: $ctype;

axiom $def_fnptr_type(^$#rbt_find_smallest.c..36261#3);

type $#rbt_find_smallest.c..36261#3;

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

function F#rbt(#s: $state, SP#root: $ptr) : bool;

const unique cf#rbt: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#rbt(#s, SP#root) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#root, ^r_node)) ==> F#rbt(#s, SP#root));

axiom $function_arg_type(cf#rbt, 0, ^^bool);

axiom $function_arg_type(cf#rbt, 1, $ptr_to(^r_node));

procedure rbt(SP#root: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#root, ^r_node)) ==> $result;
  free ensures $result == F#rbt($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#rbt_reach(#s: $state, SP#root: $ptr) : $oset;

const unique cf#rbt_reach: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#rbt_reach(#s, SP#root) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#root, ^r_node)) ==> $oset_in($phys_ptr_cast(SP#root, ^r_node), F#rbt_reach(#s, SP#root))) && ($is_null($phys_ptr_cast(SP#root, ^r_node)) ==> F#rbt_reach(#s, SP#root) == $oset_empty()));

axiom $function_arg_type(cf#rbt_reach, 0, ^$#oset);

axiom $function_arg_type(cf#rbt_reach, 1, $ptr_to(^r_node));

procedure rbt_reach(SP#root: $ptr) returns ($result: $oset);
  ensures $non_null($phys_ptr_cast(SP#root, ^r_node)) ==> $oset_in($phys_ptr_cast(SP#root, ^r_node), $result);
  ensures $is_null($phys_ptr_cast(SP#root, ^r_node)) ==> $result == $oset_empty();
  free ensures $result == F#rbt_reach($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#rbt_keys(#s: $state, SP#root: $ptr) : $intset;

const unique cf#rbt_keys: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#rbt_keys(#s, SP#root) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#root, ^r_node)) ==> $intset_in($rd_inv(#s, r_node.key, $phys_ptr_cast(SP#root, ^r_node)), F#rbt_keys(#s, SP#root))) && ($is_null($phys_ptr_cast(SP#root, ^r_node)) ==> F#rbt_keys(#s, SP#root) == $intset_empty()));

axiom $function_arg_type(cf#rbt_keys, 0, ^$#intset);

axiom $function_arg_type(cf#rbt_keys, 1, $ptr_to(^r_node));

procedure rbt_keys(SP#root: $ptr) returns ($result: $intset);
  ensures $non_null($phys_ptr_cast(SP#root, ^r_node)) ==> $intset_in($rd_inv($s, r_node.key, $phys_ptr_cast(SP#root, ^r_node)), $result);
  ensures $is_null($phys_ptr_cast(SP#root, ^r_node)) ==> $result == $intset_empty();
  free ensures $result == F#rbt_keys($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#rbt_bh(#s: $state, SP#root: $ptr) : int;

const unique cf#rbt_bh: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#rbt_bh(#s, SP#root) } 1 < $decreases_level ==> ($is_null($phys_ptr_cast(SP#root, ^r_node)) ==> F#rbt_bh(#s, SP#root) == 1) && ($non_null($phys_ptr_cast(SP#root, ^r_node)) ==> F#rbt_bh(#s, SP#root) >= 1));

axiom $function_arg_type(cf#rbt_bh, 0, ^^mathint);

axiom $function_arg_type(cf#rbt_bh, 1, $ptr_to(^r_node));

procedure rbt_bh(SP#root: $ptr) returns ($result: int);
  ensures $is_null($phys_ptr_cast(SP#root, ^r_node)) ==> $result == 1;
  ensures $non_null($phys_ptr_cast(SP#root, ^r_node)) ==> $result >= 1;
  free ensures $result == F#rbt_bh($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#rbt_black(#s: $state, SP#root: $ptr) : bool;

const unique cf#rbt_black: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#rbt_black(#s, SP#root) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#root, ^r_node)) ==> F#rbt_black(#s, SP#root));

axiom $function_arg_type(cf#rbt_black, 0, ^^bool);

axiom $function_arg_type(cf#rbt_black, 1, $ptr_to(^r_node));

procedure rbt_black(SP#root: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#root, ^r_node)) ==> $result;
  free ensures $result == F#rbt_black($s, SP#root);
  free ensures $call_transition(old($s), $s);



procedure rbt_find_smallest(P#x: $ptr) returns ($result: int);
  requires $non_null($phys_ptr_cast(P#x, ^r_node));
  requires F#rbt($s, $phys_ptr_cast(P#x, ^r_node));
  modifies $s, $cev_pc;
  free ensures $in_range_i4($result);
// INV:BEGIN
  ensures $non_null($phys_ptr_cast(P#x, ^r_node)) && F#rbt($s, $phys_ptr_cast(P#x, ^r_node));
  ensures F#rbt_reach($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_reach(old($s), $phys_ptr_cast(P#x, ^r_node));
  ensures F#rbt_keys($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_keys(old($s), $phys_ptr_cast(P#x, ^r_node));
  ensures $intset_in($result, F#rbt_keys($s, $phys_ptr_cast(P#x, ^r_node)));
// INV:END
  ensures F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh(old($s), $phys_ptr_cast(P#x, ^r_node));
  ensures F#rbt_black($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_black(old($s), $phys_ptr_cast(P#x, ^r_node));
  ensures $intset_le_one1($result, F#rbt_keys($s, $phys_ptr_cast(P#x, ^r_node)));
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);

// INV:PTR: P#x
// INV:INT: $result
// INV:LST: rbt


implementation rbt_find_smallest(P#x: $ptr) returns ($result: int)
{
  var stmtexpr1#2: $state;
  var SL#_dryad_S1: $state;
  var stmtexpr0#1: $state;
  var SL#_dryad_S0: $state;
  var L#r: int where $in_range_i4(L#r);
  var stmtexpr1#4: $oset;
  var stmtexpr0#3: $oset;
  var SL#_dryad_G1: $oset;
  var SL#_dryad_G0: $oset;
  var #wrTime$2^5.3: int;
  var #stackframe: int;

  anon3:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$2^5.3, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$2^5.3 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$2^5.3, (lambda #p: $ptr :: false));
    // assume true
    // assume @decreases_level_is(2147483647); 
    assume 2147483647 == $decreases_level;
    //  --- Dryad annotated function --- 
    // _math \oset _dryad_G0; 
    // _math \oset _dryad_G1; 
    // _dryad_G0 := rbt_reach(x); 
    call SL#_dryad_G0 := rbt_reach($phys_ptr_cast(P#x, ^r_node));
    assume $full_stop_ext(#tok$3^0.0, $s);
    // _math \oset stmtexpr0#3; 
    // stmtexpr0#3 := _dryad_G0; 
    stmtexpr0#3 := SL#_dryad_G0;
    // _dryad_G1 := _dryad_G0; 
    SL#_dryad_G1 := SL#_dryad_G0;
    // _math \oset stmtexpr1#4; 
    // stmtexpr1#4 := _dryad_G1; 
    stmtexpr1#4 := SL#_dryad_G1;
    // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt(x), &&(&&(&&(&&(&&(&&(&&(&&(&&(rbt(*((x->left))), rbt(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(rbt_reach(*((x->left))), rbt_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(rbt_keys(*((x->left))), rbt_keys(*((x->right))))))), @_vcc_oset_disjoint(rbt_reach(*((x->left))), rbt_reach(*((x->right))))), @_vcc_intset_disjoint(rbt_keys(*((x->left))), rbt_keys(*((x->right))))), @_vcc_intset_lt_one2(rbt_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), rbt_keys(*((x->right))))), ==(rbt_bh(*((x->left))), rbt_bh(*((x->right))))), ||(==(*((x->color)), 0), &&(rbt_black(*((x->left))), rbt_black(*((x->right)))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt($s, $phys_ptr_cast(P#x, ^r_node)) == (F#rbt($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && F#rbt($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && !$oset_in($phys_ptr_cast(P#x, ^r_node), $oset_union(F#rbt_reach($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_reach($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)))) && !$intset_in($rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node)), $intset_union(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)))) && $oset_disjoint(F#rbt_reach($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_reach($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && $intset_disjoint(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && $intset_lt_one2(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), $rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node))) && $intset_lt_one1($rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && ($rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0 || (F#rbt_black($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && F#rbt_black($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(rbt_reach(*((x->left))), rbt_reach(*((x->right))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt_reach($s, $phys_ptr_cast(P#x, ^r_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^r_node)), $oset_union(F#rbt_reach($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_reach($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), &&(&&(&&(==>(&&(<(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), ==(*((x->color)), 0)), ==(rbt_bh(x), +(rbt_bh(*((x->right))), 1))), ==>(&&(<(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), !=(*((x->color)), 0)), ==(rbt_bh(x), rbt_bh(*((x->right)))))), ==>(&&(>=(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), ==(*((x->color)), 0)), ==(rbt_bh(x), +(rbt_bh(*((x->left))), 1)))), ==>(&&(>=(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), !=(*((x->color)), 0)), ==(rbt_bh(x), rbt_bh(*((x->left))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) < F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) + 1) && (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) < F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) != 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) >= F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) + 1) && (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) >= F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) != 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt_black(x), ==(*((x->color)), 0))); 
    assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt_black($s, $phys_ptr_cast(P#x, ^r_node)) == ($rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0);
    // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(rbt_keys(*((x->left))), rbt_keys(*((x->right))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt_keys($s, $phys_ptr_cast(P#x, ^r_node)) == $intset_union($intset_singleton($rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node))), $intset_union(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), &&(@_vcc_mutable(@state, x), @writes_check(x))); 
    assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> $mutable($s, $phys_ptr_cast(P#x, ^r_node)) && $top_writable($s, #wrTime$2^5.3, $phys_ptr_cast(P#x, ^r_node));
    // assert @reads_check_normal((x->left)); 
    assert $thread_local($s, $phys_ptr_cast(P#x, ^r_node));
    assume true;
    // if (@_vcc_ptr_eq_null(*((x->left)))) ...
    if ($is_null($rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)))
    {
      anon1:
        // assert @reads_check_normal((x->key)); 
        assert $thread_local($s, $phys_ptr_cast(P#x, ^r_node));
        // return *((x->key)); 
        $result := $rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node));
        assume true;
        assert $position_marker();
        goto #exit;
    }
    else
    {
      anon2:
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt(x), &&(&&(&&(&&(&&(&&(&&(&&(&&(rbt(*((x->left))), rbt(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(rbt_reach(*((x->left))), rbt_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(rbt_keys(*((x->left))), rbt_keys(*((x->right))))))), @_vcc_oset_disjoint(rbt_reach(*((x->left))), rbt_reach(*((x->right))))), @_vcc_intset_disjoint(rbt_keys(*((x->left))), rbt_keys(*((x->right))))), @_vcc_intset_lt_one2(rbt_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), rbt_keys(*((x->right))))), ==(rbt_bh(*((x->left))), rbt_bh(*((x->right))))), ||(==(*((x->color)), 0), &&(rbt_black(*((x->left))), rbt_black(*((x->right)))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt($s, $phys_ptr_cast(P#x, ^r_node)) == (F#rbt($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && F#rbt($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && !$oset_in($phys_ptr_cast(P#x, ^r_node), $oset_union(F#rbt_reach($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_reach($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)))) && !$intset_in($rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node)), $intset_union(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)))) && $oset_disjoint(F#rbt_reach($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_reach($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && $intset_disjoint(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && $intset_lt_one2(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), $rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node))) && $intset_lt_one1($rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && ($rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0 || (F#rbt_black($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && F#rbt_black($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(rbt_reach(*((x->left))), rbt_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt_reach($s, $phys_ptr_cast(P#x, ^r_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^r_node)), $oset_union(F#rbt_reach($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_reach($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), &&(&&(&&(==>(&&(<(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), ==(*((x->color)), 0)), ==(rbt_bh(x), +(rbt_bh(*((x->right))), 1))), ==>(&&(<(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), !=(*((x->color)), 0)), ==(rbt_bh(x), rbt_bh(*((x->right)))))), ==>(&&(>=(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), ==(*((x->color)), 0)), ==(rbt_bh(x), +(rbt_bh(*((x->left))), 1)))), ==>(&&(>=(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), !=(*((x->color)), 0)), ==(rbt_bh(x), rbt_bh(*((x->left))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) < F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) + 1) && (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) < F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) != 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) >= F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) + 1) && (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) >= F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) != 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt_black(x), ==(*((x->color)), 0))); 
        assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt_black($s, $phys_ptr_cast(P#x, ^r_node)) == ($rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0);
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(rbt_keys(*((x->left))), rbt_keys(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt_keys($s, $phys_ptr_cast(P#x, ^r_node)) == $intset_union($intset_singleton($rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node))), $intset_union(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))));
        // int32_t r; 
        // _math \state _dryad_S0; 
        // _dryad_S0 := @_vcc_current_state(@state); 
        SL#_dryad_S0 := $current_state($s);
        // _math \state stmtexpr0#1; 
        // stmtexpr0#1 := _dryad_S0; 
        stmtexpr0#1 := SL#_dryad_S0;
        // non-pure function
        // assert @reads_check_normal((x->left)); 
        assert $thread_local($s, $phys_ptr_cast(P#x, ^r_node));
        // r := rbt_find_smallest(*((x->left))); 
        call L#r := rbt_find_smallest($rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node));
        assume $full_stop_ext(#tok$2^21.11, $s);
        // _math \state _dryad_S1; 
        // _dryad_S1 := @_vcc_current_state(@state); 
        SL#_dryad_S1 := $current_state($s);
        // _math \state stmtexpr1#2; 
        // stmtexpr1#2 := _dryad_S1; 
        stmtexpr1#2 := SL#_dryad_S1;
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt(x), &&(&&(&&(&&(&&(&&(&&(&&(&&(rbt(*((x->left))), rbt(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(rbt_reach(*((x->left))), rbt_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(rbt_keys(*((x->left))), rbt_keys(*((x->right))))))), @_vcc_oset_disjoint(rbt_reach(*((x->left))), rbt_reach(*((x->right))))), @_vcc_intset_disjoint(rbt_keys(*((x->left))), rbt_keys(*((x->right))))), @_vcc_intset_lt_one2(rbt_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), rbt_keys(*((x->right))))), ==(rbt_bh(*((x->left))), rbt_bh(*((x->right))))), ||(==(*((x->color)), 0), &&(rbt_black(*((x->left))), rbt_black(*((x->right)))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt($s, $phys_ptr_cast(P#x, ^r_node)) == (F#rbt($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && F#rbt($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && !$oset_in($phys_ptr_cast(P#x, ^r_node), $oset_union(F#rbt_reach($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_reach($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)))) && !$intset_in($rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node)), $intset_union(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)))) && $oset_disjoint(F#rbt_reach($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_reach($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && $intset_disjoint(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && $intset_lt_one2(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), $rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node))) && $intset_lt_one1($rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && ($rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0 || (F#rbt_black($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && F#rbt_black($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(rbt_reach(*((x->left))), rbt_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt_reach($s, $phys_ptr_cast(P#x, ^r_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^r_node)), $oset_union(F#rbt_reach($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_reach($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), &&(&&(&&(==>(&&(<(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), ==(*((x->color)), 0)), ==(rbt_bh(x), +(rbt_bh(*((x->right))), 1))), ==>(&&(<(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), !=(*((x->color)), 0)), ==(rbt_bh(x), rbt_bh(*((x->right)))))), ==>(&&(>=(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), ==(*((x->color)), 0)), ==(rbt_bh(x), +(rbt_bh(*((x->left))), 1)))), ==>(&&(>=(rbt_bh(*((x->left))), rbt_bh(*((x->right)))), !=(*((x->color)), 0)), ==(rbt_bh(x), rbt_bh(*((x->left))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) < F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) + 1) && (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) < F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) != 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) && (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) >= F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) + 1) && (F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)) >= F#rbt_bh($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) && $rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) != 0 ==> F#rbt_bh($s, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt_black(x), ==(*((x->color)), 0))); 
        assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt_black($s, $phys_ptr_cast(P#x, ^r_node)) == ($rd_inv($s, r_node.color, $phys_ptr_cast(P#x, ^r_node)) == 0);
        // assume ==>(@_vcc_ptr_neq_null(x), ==(rbt_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(rbt_keys(*((x->left))), rbt_keys(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^r_node)) ==> F#rbt_keys($s, $phys_ptr_cast(P#x, ^r_node)) == $intset_union($intset_singleton($rd_inv($s, r_node.key, $phys_ptr_cast(P#x, ^r_node))), $intset_union(F#rbt_keys($s, $rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node)), F#rbt_keys($s, $rd_phys_ptr($s, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, rbt_reach(x)))), ==(old(_dryad_S0, rbt(x)), old(_dryad_S1, rbt(x)))); 
        assume !$oset_in($rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node), F#rbt_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^r_node))) ==> F#rbt(SL#_dryad_S0, $phys_ptr_cast(P#x, ^r_node)) == F#rbt(SL#_dryad_S1, $phys_ptr_cast(P#x, ^r_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, rbt_reach(x)))), ==(old(_dryad_S0, rbt_reach(x)), old(_dryad_S1, rbt_reach(x)))); 
        assume !$oset_in($rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node), F#rbt_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^r_node))) ==> F#rbt_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^r_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, rbt_reach(x)))), ==(old(_dryad_S0, rbt_bh(x)), old(_dryad_S1, rbt_bh(x)))); 
        assume !$oset_in($rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node), F#rbt_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^r_node))) ==> F#rbt_bh(SL#_dryad_S0, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_bh(SL#_dryad_S1, $phys_ptr_cast(P#x, ^r_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, rbt_reach(x)))), ==(old(_dryad_S0, rbt_black(x)), old(_dryad_S1, rbt_black(x)))); 
        assume !$oset_in($rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node), F#rbt_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^r_node))) ==> F#rbt_black(SL#_dryad_S0, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_black(SL#_dryad_S1, $phys_ptr_cast(P#x, ^r_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, rbt_reach(x)))), ==(old(_dryad_S0, rbt_keys(x)), old(_dryad_S1, rbt_keys(x)))); 
        assume !$oset_in($rd_phys_ptr($s, r_node.left, $phys_ptr_cast(P#x, ^r_node), ^r_node), F#rbt_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^r_node))) ==> F#rbt_keys(SL#_dryad_S0, $phys_ptr_cast(P#x, ^r_node)) == F#rbt_keys(SL#_dryad_S1, $phys_ptr_cast(P#x, ^r_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, rbt_reach(*((x->right)))))), ==(old(_dryad_S0, rbt(*((x->right)))), old(_dryad_S1, rbt(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^r_node), F#rbt_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) ==> F#rbt(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) == F#rbt(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, rbt_reach(*((x->right)))))), ==(old(_dryad_S0, rbt_reach(*((x->right)))), old(_dryad_S1, rbt_reach(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^r_node), F#rbt_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) ==> F#rbt_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) == F#rbt_reach(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, rbt_reach(*((x->right)))))), ==(old(_dryad_S0, rbt_bh(*((x->right)))), old(_dryad_S1, rbt_bh(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^r_node), F#rbt_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) ==> F#rbt_bh(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) == F#rbt_bh(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, rbt_reach(*((x->right)))))), ==(old(_dryad_S0, rbt_black(*((x->right)))), old(_dryad_S1, rbt_black(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^r_node), F#rbt_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) ==> F#rbt_black(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) == F#rbt_black(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, rbt_reach(*((x->right)))))), ==(old(_dryad_S0, rbt_keys(*((x->right)))), old(_dryad_S1, rbt_keys(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^r_node), F#rbt_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node))) ==> F#rbt_keys(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node)) == F#rbt_keys(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, r_node.right, $phys_ptr_cast(P#x, ^r_node), ^r_node));
        // return r; 
        $result := L#r;
        assume true;
        assert $position_marker();
        goto #exit;
    }

  anon4:
    // skip

  #exit:
}



const unique l#public: $label;

const unique #tok$2^21.11: $token;

const unique #tok$3^0.0: $token;

const unique #file^?3Cno?20file?3E: $token;

axiom $file_name_is(3, #file^?3Cno?20file?3E);

const unique #tok$2^5.3: $token;

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Crbt?5Crbt?2Dfind?2Dsmallest.c: $token;

axiom $file_name_is(2, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Crbt?5Crbt?2Dfind?2Dsmallest.c);

const unique #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Crbt?5Cdryad_rbt.h: $token;

axiom $file_name_is(1, #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Crbt?5Cdryad_rbt.h);

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^r_node);
