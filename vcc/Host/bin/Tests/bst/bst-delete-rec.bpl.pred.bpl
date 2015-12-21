
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

axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

const unique ^$##thread_id: $ctype;

axiom $def_math_type(^$##thread_id);

type $##thread_id;

const unique ^$##club: $ctype;

axiom $def_math_type(^$##club);

type $##club;

const unique ^b_node: $ctype;

axiom $is_span_sequential(^b_node);

axiom $def_struct_type(^b_node, 24, false, false);

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2(#s1, #s2, #p, ^b_node) } $inv2(#s1, #s2, #p, ^b_node) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2_without_lemmas(#s1, #s2, #p, ^b_node) } $inv2_without_lemmas(#s1, #s2, #p, ^b_node) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall p: $ptr, q: $ptr, s: $state :: { $in(q, $composite_extent(s, p, ^b_node)) } $in(q, $composite_extent(s, p, ^b_node)) == (q == p));

const unique b_node.left: $field;

axiom $def_phys_field(^b_node, b_node.left, $ptr_to(^b_node), false, 0);

const unique b_node.right: $field;

axiom $def_phys_field(^b_node, b_node.right, $ptr_to(^b_node), false, 8);

const unique b_node.key: $field;

axiom $def_phys_field(^b_node, b_node.key, ^^i4, false, 16);

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

const unique ^$#bst_delete_rec.c..36261#3: $ctype;

axiom $def_fnptr_type(^$#bst_delete_rec.c..36261#3);

type $#bst_delete_rec.c..36261#3;

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

function F#bst(#s: $state, SP#root: $ptr) : bool;

const unique cf#bst: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#bst(#s, SP#root) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#root, ^b_node)) ==> F#bst(#s, SP#root));

axiom $function_arg_type(cf#bst, 0, ^^bool);

axiom $function_arg_type(cf#bst, 1, $ptr_to(^b_node));

procedure bst(SP#root: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#root, ^b_node)) ==> $result;
  free ensures $result == F#bst($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#bst_reach(#s: $state, SP#root: $ptr) : $oset;

const unique cf#bst_reach: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#bst_reach(#s, SP#root) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#root, ^b_node)) ==> $oset_in($phys_ptr_cast(SP#root, ^b_node), F#bst_reach(#s, SP#root))) && ($is_null($phys_ptr_cast(SP#root, ^b_node)) ==> F#bst_reach(#s, SP#root) == $oset_empty()));

axiom $function_arg_type(cf#bst_reach, 0, ^$#oset);

axiom $function_arg_type(cf#bst_reach, 1, $ptr_to(^b_node));

procedure bst_reach(SP#root: $ptr) returns ($result: $oset);
  ensures $non_null($phys_ptr_cast(SP#root, ^b_node)) ==> $oset_in($phys_ptr_cast(SP#root, ^b_node), $result);
  ensures $is_null($phys_ptr_cast(SP#root, ^b_node)) ==> $result == $oset_empty();
  free ensures $result == F#bst_reach($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#bst_keys(#s: $state, SP#root: $ptr) : $intset;

const unique cf#bst_keys: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#bst_keys(#s, SP#root) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#root, ^b_node)) ==> $intset_in($rd_inv(#s, b_node.key, $phys_ptr_cast(SP#root, ^b_node)), F#bst_keys(#s, SP#root))) && ($is_null($phys_ptr_cast(SP#root, ^b_node)) ==> F#bst_keys(#s, SP#root) == $intset_empty()));

axiom $function_arg_type(cf#bst_keys, 0, ^$#intset);

axiom $function_arg_type(cf#bst_keys, 1, $ptr_to(^b_node));

procedure bst_keys(SP#root: $ptr) returns ($result: $intset);
  ensures $non_null($phys_ptr_cast(SP#root, ^b_node)) ==> $intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(SP#root, ^b_node)), $result);
  ensures $is_null($phys_ptr_cast(SP#root, ^b_node)) ==> $result == $intset_empty();
  free ensures $result == F#bst_keys($s, SP#root);
  free ensures $call_transition(old($s), $s);



procedure bst_remove_root(P#x: $ptr) returns ($result: $ptr);
  requires F#bst($s, $phys_ptr_cast(P#x, ^b_node));
  requires $intset_le(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)));
  modifies $s, $cev_pc;
  ensures F#bst($s, $phys_ptr_cast($result, ^b_node));
  ensures F#bst_keys($s, $phys_ptr_cast($result, ^b_node)) == $intset_diff(F#bst_keys(old($s), $phys_ptr_cast(P#x, ^b_node)), $intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))));
  ensures F#bst_keys($s, $phys_ptr_cast($result, ^b_node)) == $intset_union(F#bst_keys(old($s), $rd_phys_ptr(old($s), b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys(old($s), $rd_phys_ptr(old($s), b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)));
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



procedure bst_delete_rec(P#x: $ptr, P#k: int) returns ($result: $ptr);
  requires F#bst($s, $phys_ptr_cast(P#x, ^b_node));
  requires $intset_in(P#k, F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)));
  modifies $s, $cev_pc;
  ensures F#bst($s, $phys_ptr_cast($result, ^b_node));
ensures b0000 ==> (F#bst($s,$phys_ptr_cast(P#x,^b_node)));
ensures b0001 ==> (F#bst($s,$phys_ptr_cast($result,^b_node)));
ensures b0002 ==> ((F#bst_reach($s,$phys_ptr_cast(P#x,^b_node)) == F#bst_reach($s,$phys_ptr_cast($result,^b_node))));
ensures b0003 ==> ((F#bst_reach($s,$phys_ptr_cast($result,^b_node)) == F#bst_reach($s,$phys_ptr_cast(P#x,^b_node))));
ensures b0004 ==> ((F#bst_reach($s,$phys_ptr_cast(P#x,^b_node)) == F#bst_reach(old($s),$phys_ptr_cast(P#x,^b_node))));
ensures b0005 ==> ((F#bst_reach($s,$phys_ptr_cast($result,^b_node)) == F#bst_reach(old($s),$phys_ptr_cast($result,^b_node))));
ensures b0006 ==> ($non_null($phys_ptr_cast(P#x,^b_node)));
ensures b0007 ==> ($non_null($phys_ptr_cast($result,^b_node)));
ensures b0008 ==> ($is_null($phys_ptr_cast(P#x,^b_node)));
ensures b0009 ==> ($is_null($phys_ptr_cast($result,^b_node)));
ensures b0010 ==> (($phys_ptr_cast(P#x,^b_node) == $phys_ptr_cast($result,^b_node)));
ensures b0011 ==> (($phys_ptr_cast($result,^b_node) == $phys_ptr_cast(P#x,^b_node)));
ensures b0012 ==> (($non_null($phys_ptr_cast(P#x,^b_node)) ==> $non_null($rd_phys_ptr($s,b_node.left,$phys_ptr_cast(P#x,^b_node),^b_node))));
ensures b0013 ==> (($non_null($phys_ptr_cast($result,^b_node)) ==> $non_null($rd_phys_ptr($s,b_node.left,$phys_ptr_cast($result,^b_node),^b_node))));
ensures b0014 ==> (($non_null($phys_ptr_cast(P#x,^b_node)) ==> $is_null($rd_phys_ptr($s,b_node.left,$phys_ptr_cast(P#x,^b_node),^b_node))));
ensures b0015 ==> (($non_null($phys_ptr_cast($result,^b_node)) ==> $is_null($rd_phys_ptr($s,b_node.left,$phys_ptr_cast($result,^b_node),^b_node))));
ensures b0016 ==> (($non_null($phys_ptr_cast(P#x,^b_node)) ==> ($rd_phys_ptr($s,b_node.left,$phys_ptr_cast(P#x,^b_node),^b_node) == $phys_ptr_cast($result,^b_node))));
ensures b0017 ==> (($non_null($phys_ptr_cast($result,^b_node)) ==> ($rd_phys_ptr($s,b_node.left,$phys_ptr_cast($result,^b_node),^b_node) == $phys_ptr_cast(P#x,^b_node))));
ensures b0018 ==> (($non_null($phys_ptr_cast(P#x,^b_node)) ==> $non_null($rd_phys_ptr($s,b_node.right,$phys_ptr_cast(P#x,^b_node),^b_node))));
ensures b0019 ==> (($non_null($phys_ptr_cast($result,^b_node)) ==> $non_null($rd_phys_ptr($s,b_node.right,$phys_ptr_cast($result,^b_node),^b_node))));
ensures b0020 ==> (($non_null($phys_ptr_cast(P#x,^b_node)) ==> $is_null($rd_phys_ptr($s,b_node.right,$phys_ptr_cast(P#x,^b_node),^b_node))));
ensures b0021 ==> (($non_null($phys_ptr_cast($result,^b_node)) ==> $is_null($rd_phys_ptr($s,b_node.right,$phys_ptr_cast($result,^b_node),^b_node))));
ensures b0022 ==> (($non_null($phys_ptr_cast(P#x,^b_node)) ==> ($rd_phys_ptr($s,b_node.right,$phys_ptr_cast(P#x,^b_node),^b_node) == $phys_ptr_cast($result,^b_node))));
ensures b0023 ==> (($non_null($phys_ptr_cast($result,^b_node)) ==> ($rd_phys_ptr($s,b_node.right,$phys_ptr_cast($result,^b_node),^b_node) == $phys_ptr_cast(P#x,^b_node))));
ensures b0024 ==> ((F#bst_keys($s,$phys_ptr_cast(P#x,^b_node)) == F#bst_keys($s,$phys_ptr_cast($result,^b_node))));
ensures b0025 ==> ((F#bst_keys($s,$phys_ptr_cast($result,^b_node)) == F#bst_keys($s,$phys_ptr_cast(P#x,^b_node))));
ensures b0026 ==> ((F#bst_keys($s,$phys_ptr_cast(P#x,^b_node)) == F#bst_keys(old($s),$phys_ptr_cast(P#x,^b_node))));
ensures b0027 ==> ((F#bst_keys($s,$phys_ptr_cast($result,^b_node)) == F#bst_keys(old($s),$phys_ptr_cast($result,^b_node))));
ensures b0028 ==> ((F#bst_keys($s,$phys_ptr_cast(P#x,^b_node)) == $intset_union(F#bst_keys(old($s),$phys_ptr_cast(P#x,^b_node)),$intset_singleton(P#k))));
ensures b0029 ==> ((F#bst_keys($s,$phys_ptr_cast($result,^b_node)) == $intset_union(F#bst_keys(old($s),$phys_ptr_cast($result,^b_node)),$intset_singleton(P#k))));
ensures b0030 ==> ((P#k < 2147483647));
ensures b0031 ==> ((P#k < 2147483647));
ensures b0032 ==> ((P#k < 4294967295));
ensures b0033 ==> ((P#k < 4294967295));
ensures b0034 ==> ((P#k >= 0));
ensures b0035 ==> ((P#k >= 0));
ensures b0036 ==> (($rd_inv($s,b_node.key,$phys_ptr_cast(P#x,^b_node)) < P#k));
ensures b0037 ==> (($rd_inv($s,b_node.key,$phys_ptr_cast($result,^b_node)) < P#k));
ensures b0038 ==> (($rd_inv($s,b_node.key,$phys_ptr_cast(P#x,^b_node)) <= $rd_inv($s,b_node.key,$phys_ptr_cast($result,^b_node))));
ensures b0039 ==> (($rd_inv($s,b_node.key,$phys_ptr_cast($result,^b_node)) <= $rd_inv($s,b_node.key,$phys_ptr_cast(P#x,^b_node))));
ensures b0040 ==> (($rd_inv($s,b_node.key,$phys_ptr_cast(P#x,^b_node)) == $rd_inv($s,b_node.key,$phys_ptr_cast($result,^b_node))));
ensures b0041 ==> (($rd_inv($s,b_node.key,$phys_ptr_cast($result,^b_node)) == $rd_inv($s,b_node.key,$phys_ptr_cast(P#x,^b_node))));

  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);

// INV:PTR: P#x, $result
// INV:INT: P#k
// INV:LST: bst


implementation bst_delete_rec(P#x: $ptr, P#k: int) returns ($result: $ptr)
{
  var stmtexpr6#20: $state;
  var _dryad_S3#10: $state;
  var stmtexpr5#19: $state;
  var _dryad_S2#9: $state;
  var stmtexpr4#18: $oset;
  var res_bst_reach#3: $oset;
  var stmtexpr3#17: $state;
  var _dryad_S1#8: $state;
  var stmtexpr2#16: $state;
  var _dryad_S0#7: $state;
  var stmtexpr1#15: $ptr;
  var x1#6: $ptr;
  var stmtexpr0#14: $ptr;
  var x0#5: $ptr;
  var xl#4: $ptr;
  var xr#3: $ptr;
  var r#2: $ptr;
  var stmtexpr6#13: $state;
  var SL#_dryad_S3: $state;
  var stmtexpr5#12: $state;
  var SL#_dryad_S2: $state;
  var stmtexpr4#11: $oset;
  var res_bst_reach#2: $oset;
  var stmtexpr3#10: $state;
  var _dryad_S1#1: $state;
  var stmtexpr2#9: $state;
  var _dryad_S0#0: $state;
  var stmtexpr1#8: $ptr;
  var SL#x1: $ptr;
  var stmtexpr0#7: $ptr;
  var SL#x0: $ptr;
  var L#xl: $ptr;
  var L#xr: $ptr;
  var L#l: $ptr;
  var stmtexpr2#6: $oset;
  var res_bst_reach#1: $oset;
  var stmtexpr1#5: $state;
  var SL#_dryad_S1: $state;
  var stmtexpr0#4: $state;
  var SL#_dryad_S0: $state;
  var L#r: $ptr;
  var stmtexpr1#22: $oset;
  var stmtexpr0#21: $oset;
  var SL#_dryad_G1: $oset;
  var SL#_dryad_G0: $oset;
  var #wrTime$3^13.3: int;
  var #stackframe: int;

  anon5:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$3^13.3, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$3^13.3 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$3^13.3, (lambda #p: $ptr :: false));
    // assume true
    // assume @in_range_i4(k); 
    assume $in_range_i4(P#k);
    // assume @decreases_level_is(2147483647); 
    assume 2147483647 == $decreases_level;
    //  --- Dryad annotated function --- 
    // _math \oset _dryad_G0; 
    // _math \oset _dryad_G1; 
    // _dryad_G0 := bst_reach(x); 
    call SL#_dryad_G0 := bst_reach($phys_ptr_cast(P#x, ^b_node));
    assume $full_stop_ext(#tok$4^0.0, $s);
    // _math \oset stmtexpr0#21; 
    // stmtexpr0#21 := _dryad_G0; 
    stmtexpr0#21 := SL#_dryad_G0;
    // _dryad_G1 := _dryad_G0; 
    SL#_dryad_G1 := SL#_dryad_G0;
    // _math \oset stmtexpr1#22; 
    // stmtexpr1#22 := _dryad_G1; 
    stmtexpr1#22 := SL#_dryad_G1;
    // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), &&(@_vcc_mutable(@state, x), @writes_check(x))); 
    assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> $mutable($s, $phys_ptr_cast(P#x, ^b_node)) && $top_writable($s, #wrTime$3^13.3, $phys_ptr_cast(P#x, ^b_node));
    // assert @reads_check_normal((x->key)); 
    assert $thread_local($s, $phys_ptr_cast(P#x, ^b_node));
    assume true;
    // if (==(*((x->key)), k)) ...
    if ($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)) == P#k)
    {
      anon1:
        // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
        // struct b_node* r; 
        // _math \state _dryad_S0; 
        // _dryad_S0 := @_vcc_current_state(@state); 
        SL#_dryad_S0 := $current_state($s);
        // _math \state stmtexpr0#4; 
        // stmtexpr0#4 := _dryad_S0; 
        stmtexpr0#4 := SL#_dryad_S0;
        // non-pure function
        // r := bst_remove_root(x); 
        call L#r := bst_remove_root($phys_ptr_cast(P#x, ^b_node));
        assume $full_stop_ext(#tok$3^23.17, $s);
        // _math \state _dryad_S1; 
        // _dryad_S1 := @_vcc_current_state(@state); 
        SL#_dryad_S1 := $current_state($s);
        // _math \state stmtexpr1#5; 
        // stmtexpr1#5 := _dryad_S1; 
        stmtexpr1#5 := SL#_dryad_S1;
        // assume @_vcc_oset_disjoint(bst_reach(r), @_vcc_oset_diff(_dryad_G1, old(_dryad_S0, bst_reach(x)))); 
        assume $oset_disjoint(F#bst_reach($s, $phys_ptr_cast(L#r, ^b_node)), $oset_diff(SL#_dryad_G1, F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node))));
        // _math \oset res_bst_reach#1; 
        // res_bst_reach#1 := bst_reach(r); 
        call res_bst_reach#1 := bst_reach($phys_ptr_cast(L#r, ^b_node));
        assume $full_stop_ext(#tok$4^0.0, $s);
        // _dryad_G1 := @_vcc_oset_union(res_bst_reach#1, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S0, bst_reach(x))))); 
        SL#_dryad_G1 := $oset_union(res_bst_reach#1, $oset_diff(SL#_dryad_G1, F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node))));
        // _math \oset stmtexpr2#6; 
        // stmtexpr2#6 := _dryad_G1; 
        stmtexpr2#6 := SL#_dryad_G1;
        // assume ==(glob_reach(), _dryad_G1); 
        assume F#glob_reach() == SL#_dryad_G1;
        // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0, bst_reach(x)), old(_dryad_S0, bst_reach(x))), ==(old(_dryad_S0, bst(x)), old(_dryad_S1, bst(x)))); 
        assume $oset_disjoint(F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node)), F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node))) ==> F#bst(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node)) == F#bst(SL#_dryad_S1, $phys_ptr_cast(P#x, ^b_node));
        // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0, bst_reach(x)), old(_dryad_S0, bst_reach(x))), ==(old(_dryad_S0, bst_reach(x)), old(_dryad_S1, bst_reach(x)))); 
        assume $oset_disjoint(F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node)), F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node))) ==> F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node)) == F#bst_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^b_node));
        // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0, bst_reach(x)), old(_dryad_S0, bst_reach(x))), ==(old(_dryad_S0, bst_keys(x)), old(_dryad_S1, bst_keys(x)))); 
        assume $oset_disjoint(F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node)), F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node))) ==> F#bst_keys(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node)) == F#bst_keys(SL#_dryad_S1, $phys_ptr_cast(P#x, ^b_node));
        // assume ==>(@_vcc_ptr_neq_null(r), ==(bst(r), &&(&&(&&(&&(&&(&&(&&(bst(*((r->left))), bst(*((r->right)))), unchecked!(@_vcc_oset_in(r, @_vcc_oset_union(bst_reach(*((r->left))), bst_reach(*((r->right))))))), unchecked!(@_vcc_intset_in(*((r->key)), @_vcc_intset_union(bst_keys(*((r->left))), bst_keys(*((r->right))))))), @_vcc_oset_disjoint(bst_reach(*((r->left))), bst_reach(*((r->right))))), @_vcc_intset_disjoint(bst_keys(*((r->left))), bst_keys(*((r->right))))), @_vcc_intset_lt_one2(bst_keys(*((r->left))), *((r->key)))), @_vcc_intset_lt_one1(*((r->key)), bst_keys(*((r->right))))))); 
        assume $non_null($phys_ptr_cast(L#r, ^b_node)) ==> F#bst($s, $phys_ptr_cast(L#r, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#r, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#r, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(L#r, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#r, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#r, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(L#r, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#r, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#r, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#r, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#r, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#r, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#r, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#r, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(L#r, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(L#r, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#r, ^b_node), ^b_node))));
        // assume ==>(@_vcc_ptr_neq_null(r), ==(bst_reach(r), @_vcc_oset_union(@_vcc_oset_singleton(r), @_vcc_oset_union(bst_reach(*((r->left))), bst_reach(*((r->right))))))); 
        assume $non_null($phys_ptr_cast(L#r, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(L#r, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(L#r, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#r, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#r, ^b_node), ^b_node))));
        // assume ==>(@_vcc_ptr_neq_null(r), ==(bst_keys(r), @_vcc_intset_union(@_vcc_intset_singleton(*((r->key))), @_vcc_intset_union(bst_keys(*((r->left))), bst_keys(*((r->right))))))); 
        assume $non_null($phys_ptr_cast(L#r, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(L#r, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(L#r, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#r, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#r, ^b_node), ^b_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
        // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0, bst_reach(x)))), @_vcc_ptr_eq_pure(*((x->left)), old(_dryad_S0, *((x->left))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S0, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node);
        // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0, bst_reach(x)))), @_vcc_ptr_eq_pure(*((x->right)), old(_dryad_S0, *((x->right))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S0, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node);
        // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0, bst_reach(x)))), ==(*((x->key)), old(_dryad_S0, *((x->key))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)) == $rd_inv(SL#_dryad_S0, b_node.key, $phys_ptr_cast(P#x, ^b_node));
        // return r; 
        $result := $phys_ptr_cast(L#r, ^b_node);
        assume true;
        assert $position_marker();
        goto #exit;
    }
    else
    {
      anon4:
        // assert @reads_check_normal((x->key)); 
        assert $thread_local($s, $phys_ptr_cast(P#x, ^b_node));
        assume true;
        // if (<(k, *((x->key)))) ...
        if (P#k < $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)))
        {
          anon2:
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // struct b_node* l; 
            // struct b_node* xr; 
            // struct b_node* xl; 
            // struct b_node* x0; 
            // x0 := x; 
            SL#x0 := $phys_ptr_cast(P#x, ^b_node);
            // struct b_node* stmtexpr0#7; 
            // stmtexpr0#7 := x0; 
            stmtexpr0#7 := $phys_ptr_cast(SL#x0, ^b_node);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assert @reads_check_normal((x->left)); 
            assert $thread_local($s, $phys_ptr_cast(P#x, ^b_node));
            // xl := *((x->left)); 
            L#xl := $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node);
            // assume ==>(@_vcc_ptr_neq_null(xl), ==(bst(xl), &&(&&(&&(&&(&&(&&(&&(bst(*((xl->left))), bst(*((xl->right)))), unchecked!(@_vcc_oset_in(xl, @_vcc_oset_union(bst_reach(*((xl->left))), bst_reach(*((xl->right))))))), unchecked!(@_vcc_intset_in(*((xl->key)), @_vcc_intset_union(bst_keys(*((xl->left))), bst_keys(*((xl->right))))))), @_vcc_oset_disjoint(bst_reach(*((xl->left))), bst_reach(*((xl->right))))), @_vcc_intset_disjoint(bst_keys(*((xl->left))), bst_keys(*((xl->right))))), @_vcc_intset_lt_one2(bst_keys(*((xl->left))), *((xl->key)))), @_vcc_intset_lt_one1(*((xl->key)), bst_keys(*((xl->right))))))); 
            assume $non_null($phys_ptr_cast(L#xl, ^b_node)) ==> F#bst($s, $phys_ptr_cast(L#xl, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(L#xl, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl), ==(bst_reach(xl), @_vcc_oset_union(@_vcc_oset_singleton(xl), @_vcc_oset_union(bst_reach(*((xl->left))), bst_reach(*((xl->right))))))); 
            assume $non_null($phys_ptr_cast(L#xl, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(L#xl, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(L#xl, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl), ==(bst_keys(xl), @_vcc_intset_union(@_vcc_intset_singleton(*((xl->key))), @_vcc_intset_union(bst_keys(*((xl->left))), bst_keys(*((xl->right))))))); 
            assume $non_null($phys_ptr_cast(L#xl, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(L#xl, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // struct b_node* x1; 
            // x1 := x; 
            SL#x1 := $phys_ptr_cast(P#x, ^b_node);
            // struct b_node* stmtexpr1#8; 
            // stmtexpr1#8 := x1; 
            stmtexpr1#8 := $phys_ptr_cast(SL#x1, ^b_node);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assert @reads_check_normal((x->right)); 
            assert $thread_local($s, $phys_ptr_cast(P#x, ^b_node));
            // xr := *((x->right)); 
            L#xr := $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node);
            // assume ==>(@_vcc_ptr_neq_null(xr), ==(bst(xr), &&(&&(&&(&&(&&(&&(&&(bst(*((xr->left))), bst(*((xr->right)))), unchecked!(@_vcc_oset_in(xr, @_vcc_oset_union(bst_reach(*((xr->left))), bst_reach(*((xr->right))))))), unchecked!(@_vcc_intset_in(*((xr->key)), @_vcc_intset_union(bst_keys(*((xr->left))), bst_keys(*((xr->right))))))), @_vcc_oset_disjoint(bst_reach(*((xr->left))), bst_reach(*((xr->right))))), @_vcc_intset_disjoint(bst_keys(*((xr->left))), bst_keys(*((xr->right))))), @_vcc_intset_lt_one2(bst_keys(*((xr->left))), *((xr->key)))), @_vcc_intset_lt_one1(*((xr->key)), bst_keys(*((xr->right))))))); 
            assume $non_null($phys_ptr_cast(L#xr, ^b_node)) ==> F#bst($s, $phys_ptr_cast(L#xr, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(L#xr, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr), ==(bst_reach(xr), @_vcc_oset_union(@_vcc_oset_singleton(xr), @_vcc_oset_union(bst_reach(*((xr->left))), bst_reach(*((xr->right))))))); 
            assume $non_null($phys_ptr_cast(L#xr, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(L#xr, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(L#xr, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr), ==(bst_keys(xr), @_vcc_intset_union(@_vcc_intset_singleton(*((xr->key))), @_vcc_intset_union(bst_keys(*((xr->left))), bst_keys(*((xr->right))))))); 
            assume $non_null($phys_ptr_cast(L#xr, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(L#xr, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // _math \state _dryad_S0#0; 
            // _dryad_S0#0 := @_vcc_current_state(@state); 
            _dryad_S0#0 := $current_state($s);
            // _math \state stmtexpr2#9; 
            // stmtexpr2#9 := _dryad_S0#0; 
            stmtexpr2#9 := _dryad_S0#0;
            // non-pure function
            // l := bst_delete_rec(xl, k); 
            call L#l := bst_delete_rec($phys_ptr_cast(L#xl, ^b_node), P#k);
            assume $full_stop_ext(#tok$3^29.17, $s);
            // _math \state _dryad_S1#1; 
            // _dryad_S1#1 := @_vcc_current_state(@state); 
            _dryad_S1#1 := $current_state($s);
            // _math \state stmtexpr3#10; 
            // stmtexpr3#10 := _dryad_S1#1; 
            stmtexpr3#10 := _dryad_S1#1;
            // assume @_vcc_oset_disjoint(bst_reach(l), @_vcc_oset_diff(_dryad_G1, old(_dryad_S0#0, bst_reach(xl)))); 
            assume $oset_disjoint(F#bst_reach($s, $phys_ptr_cast(L#l, ^b_node)), $oset_diff(SL#_dryad_G1, F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))));
            // _math \oset res_bst_reach#2; 
            // res_bst_reach#2 := bst_reach(l); 
            call res_bst_reach#2 := bst_reach($phys_ptr_cast(L#l, ^b_node));
            assume $full_stop_ext(#tok$4^0.0, $s);
            // _dryad_G1 := @_vcc_oset_union(res_bst_reach#2, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S0#0, bst_reach(xl))))); 
            SL#_dryad_G1 := $oset_union(res_bst_reach#2, $oset_diff(SL#_dryad_G1, F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))));
            // _math \oset stmtexpr4#11; 
            // stmtexpr4#11 := _dryad_G1; 
            stmtexpr4#11 := SL#_dryad_G1;
            // assume ==(glob_reach(), _dryad_G1); 
            assume F#glob_reach() == SL#_dryad_G1;
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(x1))), ==(old(_dryad_S0#0, bst(x1)), old(_dryad_S1#1, bst(x1)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(SL#x1, ^b_node))) ==> F#bst(_dryad_S0#0, $phys_ptr_cast(SL#x1, ^b_node)) == F#bst(_dryad_S1#1, $phys_ptr_cast(SL#x1, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(x1))), ==(old(_dryad_S0#0, bst_reach(x1)), old(_dryad_S1#1, bst_reach(x1)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(SL#x1, ^b_node))) ==> F#bst_reach(_dryad_S0#0, $phys_ptr_cast(SL#x1, ^b_node)) == F#bst_reach(_dryad_S1#1, $phys_ptr_cast(SL#x1, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(x1))), ==(old(_dryad_S0#0, bst_keys(x1)), old(_dryad_S1#1, bst_keys(x1)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(SL#x1, ^b_node))) ==> F#bst_keys(_dryad_S0#0, $phys_ptr_cast(SL#x1, ^b_node)) == F#bst_keys(_dryad_S1#1, $phys_ptr_cast(SL#x1, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(x0))), ==(old(_dryad_S0#0, bst(x0)), old(_dryad_S1#1, bst(x0)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(SL#x0, ^b_node))) ==> F#bst(_dryad_S0#0, $phys_ptr_cast(SL#x0, ^b_node)) == F#bst(_dryad_S1#1, $phys_ptr_cast(SL#x0, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(x0))), ==(old(_dryad_S0#0, bst_reach(x0)), old(_dryad_S1#1, bst_reach(x0)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(SL#x0, ^b_node))) ==> F#bst_reach(_dryad_S0#0, $phys_ptr_cast(SL#x0, ^b_node)) == F#bst_reach(_dryad_S1#1, $phys_ptr_cast(SL#x0, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(x0))), ==(old(_dryad_S0#0, bst_keys(x0)), old(_dryad_S1#1, bst_keys(x0)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(SL#x0, ^b_node))) ==> F#bst_keys(_dryad_S0#0, $phys_ptr_cast(SL#x0, ^b_node)) == F#bst_keys(_dryad_S1#1, $phys_ptr_cast(SL#x0, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(xl))), ==(old(_dryad_S0#0, bst(xl)), old(_dryad_S1#1, bst(xl)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> F#bst(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)) == F#bst(_dryad_S1#1, $phys_ptr_cast(L#xl, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(xl))), ==(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S1#1, bst_reach(xl)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)) == F#bst_reach(_dryad_S1#1, $phys_ptr_cast(L#xl, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(xl))), ==(old(_dryad_S0#0, bst_keys(xl)), old(_dryad_S1#1, bst_keys(xl)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> F#bst_keys(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)) == F#bst_keys(_dryad_S1#1, $phys_ptr_cast(L#xl, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(xr))), ==(old(_dryad_S0#0, bst(xr)), old(_dryad_S1#1, bst(xr)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xr, ^b_node))) ==> F#bst(_dryad_S0#0, $phys_ptr_cast(L#xr, ^b_node)) == F#bst(_dryad_S1#1, $phys_ptr_cast(L#xr, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(xr))), ==(old(_dryad_S0#0, bst_reach(xr)), old(_dryad_S1#1, bst_reach(xr)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xr, ^b_node))) ==> F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xr, ^b_node)) == F#bst_reach(_dryad_S1#1, $phys_ptr_cast(L#xr, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(xr))), ==(old(_dryad_S0#0, bst_keys(xr)), old(_dryad_S1#1, bst_keys(xr)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xr, ^b_node))) ==> F#bst_keys(_dryad_S0#0, $phys_ptr_cast(L#xr, ^b_node)) == F#bst_keys(_dryad_S1#1, $phys_ptr_cast(L#xr, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(x))), ==(old(_dryad_S0#0, bst(x)), old(_dryad_S1#1, bst(x)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^b_node))) ==> F#bst(_dryad_S0#0, $phys_ptr_cast(P#x, ^b_node)) == F#bst(_dryad_S1#1, $phys_ptr_cast(P#x, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(x))), ==(old(_dryad_S0#0, bst_reach(x)), old(_dryad_S1#1, bst_reach(x)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^b_node))) ==> F#bst_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^b_node)) == F#bst_reach(_dryad_S1#1, $phys_ptr_cast(P#x, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#0, bst_reach(xl)), old(_dryad_S0#0, bst_reach(x))), ==(old(_dryad_S0#0, bst_keys(x)), old(_dryad_S1#1, bst_keys(x)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node)), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(P#x, ^b_node))) ==> F#bst_keys(_dryad_S0#0, $phys_ptr_cast(P#x, ^b_node)) == F#bst_keys(_dryad_S1#1, $phys_ptr_cast(P#x, ^b_node));
            // assume ==>(@_vcc_ptr_neq_null(x1), ==(bst(x1), &&(&&(&&(&&(&&(&&(&&(bst(*((x1->left))), bst(*((x1->right)))), unchecked!(@_vcc_oset_in(x1, @_vcc_oset_union(bst_reach(*((x1->left))), bst_reach(*((x1->right))))))), unchecked!(@_vcc_intset_in(*((x1->key)), @_vcc_intset_union(bst_keys(*((x1->left))), bst_keys(*((x1->right))))))), @_vcc_oset_disjoint(bst_reach(*((x1->left))), bst_reach(*((x1->right))))), @_vcc_intset_disjoint(bst_keys(*((x1->left))), bst_keys(*((x1->right))))), @_vcc_intset_lt_one2(bst_keys(*((x1->left))), *((x1->key)))), @_vcc_intset_lt_one1(*((x1->key)), bst_keys(*((x1->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x1, ^b_node)) ==> F#bst($s, $phys_ptr_cast(SL#x1, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(SL#x1, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x1, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(SL#x1, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x1, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x1), ==(bst_reach(x1), @_vcc_oset_union(@_vcc_oset_singleton(x1), @_vcc_oset_union(bst_reach(*((x1->left))), bst_reach(*((x1->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x1, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(SL#x1, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(SL#x1, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x1), ==(bst_keys(x1), @_vcc_intset_union(@_vcc_intset_singleton(*((x1->key))), @_vcc_intset_union(bst_keys(*((x1->left))), bst_keys(*((x1->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x1, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(SL#x1, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x1, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0), ==(bst(x0), &&(&&(&&(&&(&&(&&(&&(bst(*((x0->left))), bst(*((x0->right)))), unchecked!(@_vcc_oset_in(x0, @_vcc_oset_union(bst_reach(*((x0->left))), bst_reach(*((x0->right))))))), unchecked!(@_vcc_intset_in(*((x0->key)), @_vcc_intset_union(bst_keys(*((x0->left))), bst_keys(*((x0->right))))))), @_vcc_oset_disjoint(bst_reach(*((x0->left))), bst_reach(*((x0->right))))), @_vcc_intset_disjoint(bst_keys(*((x0->left))), bst_keys(*((x0->right))))), @_vcc_intset_lt_one2(bst_keys(*((x0->left))), *((x0->key)))), @_vcc_intset_lt_one1(*((x0->key)), bst_keys(*((x0->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x0, ^b_node)) ==> F#bst($s, $phys_ptr_cast(SL#x0, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(SL#x0, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x0, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(SL#x0, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x0, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0), ==(bst_reach(x0), @_vcc_oset_union(@_vcc_oset_singleton(x0), @_vcc_oset_union(bst_reach(*((x0->left))), bst_reach(*((x0->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x0, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(SL#x0, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(SL#x0, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0), ==(bst_keys(x0), @_vcc_intset_union(@_vcc_intset_singleton(*((x0->key))), @_vcc_intset_union(bst_keys(*((x0->left))), bst_keys(*((x0->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x0, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(SL#x0, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x0, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl), ==(bst(xl), &&(&&(&&(&&(&&(&&(&&(bst(*((xl->left))), bst(*((xl->right)))), unchecked!(@_vcc_oset_in(xl, @_vcc_oset_union(bst_reach(*((xl->left))), bst_reach(*((xl->right))))))), unchecked!(@_vcc_intset_in(*((xl->key)), @_vcc_intset_union(bst_keys(*((xl->left))), bst_keys(*((xl->right))))))), @_vcc_oset_disjoint(bst_reach(*((xl->left))), bst_reach(*((xl->right))))), @_vcc_intset_disjoint(bst_keys(*((xl->left))), bst_keys(*((xl->right))))), @_vcc_intset_lt_one2(bst_keys(*((xl->left))), *((xl->key)))), @_vcc_intset_lt_one1(*((xl->key)), bst_keys(*((xl->right))))))); 
            assume $non_null($phys_ptr_cast(L#xl, ^b_node)) ==> F#bst($s, $phys_ptr_cast(L#xl, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(L#xl, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl), ==(bst_reach(xl), @_vcc_oset_union(@_vcc_oset_singleton(xl), @_vcc_oset_union(bst_reach(*((xl->left))), bst_reach(*((xl->right))))))); 
            assume $non_null($phys_ptr_cast(L#xl, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(L#xl, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(L#xl, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl), ==(bst_keys(xl), @_vcc_intset_union(@_vcc_intset_singleton(*((xl->key))), @_vcc_intset_union(bst_keys(*((xl->left))), bst_keys(*((xl->right))))))); 
            assume $non_null($phys_ptr_cast(L#xl, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(L#xl, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr), ==(bst(xr), &&(&&(&&(&&(&&(&&(&&(bst(*((xr->left))), bst(*((xr->right)))), unchecked!(@_vcc_oset_in(xr, @_vcc_oset_union(bst_reach(*((xr->left))), bst_reach(*((xr->right))))))), unchecked!(@_vcc_intset_in(*((xr->key)), @_vcc_intset_union(bst_keys(*((xr->left))), bst_keys(*((xr->right))))))), @_vcc_oset_disjoint(bst_reach(*((xr->left))), bst_reach(*((xr->right))))), @_vcc_intset_disjoint(bst_keys(*((xr->left))), bst_keys(*((xr->right))))), @_vcc_intset_lt_one2(bst_keys(*((xr->left))), *((xr->key)))), @_vcc_intset_lt_one1(*((xr->key)), bst_keys(*((xr->right))))))); 
            assume $non_null($phys_ptr_cast(L#xr, ^b_node)) ==> F#bst($s, $phys_ptr_cast(L#xr, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(L#xr, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr), ==(bst_reach(xr), @_vcc_oset_union(@_vcc_oset_singleton(xr), @_vcc_oset_union(bst_reach(*((xr->left))), bst_reach(*((xr->right))))))); 
            assume $non_null($phys_ptr_cast(L#xr, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(L#xr, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(L#xr, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr), ==(bst_keys(xr), @_vcc_intset_union(@_vcc_intset_singleton(*((xr->key))), @_vcc_intset_union(bst_keys(*((xr->left))), bst_keys(*((xr->right))))))); 
            assume $non_null($phys_ptr_cast(L#xr, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(L#xr, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(l), ==(bst(l), &&(&&(&&(&&(&&(&&(&&(bst(*((l->left))), bst(*((l->right)))), unchecked!(@_vcc_oset_in(l, @_vcc_oset_union(bst_reach(*((l->left))), bst_reach(*((l->right))))))), unchecked!(@_vcc_intset_in(*((l->key)), @_vcc_intset_union(bst_keys(*((l->left))), bst_keys(*((l->right))))))), @_vcc_oset_disjoint(bst_reach(*((l->left))), bst_reach(*((l->right))))), @_vcc_intset_disjoint(bst_keys(*((l->left))), bst_keys(*((l->right))))), @_vcc_intset_lt_one2(bst_keys(*((l->left))), *((l->key)))), @_vcc_intset_lt_one1(*((l->key)), bst_keys(*((l->right))))))); 
            assume $non_null($phys_ptr_cast(L#l, ^b_node)) ==> F#bst($s, $phys_ptr_cast(L#l, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(L#l, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(l), ==(bst_reach(l), @_vcc_oset_union(@_vcc_oset_singleton(l), @_vcc_oset_union(bst_reach(*((l->left))), bst_reach(*((l->right))))))); 
            assume $non_null($phys_ptr_cast(L#l, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(L#l, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(L#l, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(l), ==(bst_keys(l), @_vcc_intset_union(@_vcc_intset_singleton(*((l->key))), @_vcc_intset_union(bst_keys(*((l->left))), bst_keys(*((l->right))))))); 
            assume $non_null($phys_ptr_cast(L#l, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(L#l, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(!(@_vcc_oset_in(x1, old(_dryad_S0#0, bst_reach(xl)))), @_vcc_ptr_eq_pure(*((x1->left)), old(_dryad_S0#0, *((x1->left))))); 
            assume !$oset_in($phys_ptr_cast(SL#x1, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#0, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x1, old(_dryad_S0#0, bst_reach(xl)))), @_vcc_ptr_eq_pure(*((x1->right)), old(_dryad_S0#0, *((x1->right))))); 
            assume !$oset_in($phys_ptr_cast(SL#x1, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#0, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x1, old(_dryad_S0#0, bst_reach(xl)))), ==(*((x1->key)), old(_dryad_S0#0, *((x1->key))))); 
            assume !$oset_in($phys_ptr_cast(SL#x1, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(SL#x1, ^b_node)) == $rd_inv(_dryad_S0#0, b_node.key, $phys_ptr_cast(SL#x1, ^b_node));
            // assume ==>(!(@_vcc_oset_in(x0, old(_dryad_S0#0, bst_reach(xl)))), @_vcc_ptr_eq_pure(*((x0->left)), old(_dryad_S0#0, *((x0->left))))); 
            assume !$oset_in($phys_ptr_cast(SL#x0, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#0, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x0, old(_dryad_S0#0, bst_reach(xl)))), @_vcc_ptr_eq_pure(*((x0->right)), old(_dryad_S0#0, *((x0->right))))); 
            assume !$oset_in($phys_ptr_cast(SL#x0, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#0, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x0, old(_dryad_S0#0, bst_reach(xl)))), ==(*((x0->key)), old(_dryad_S0#0, *((x0->key))))); 
            assume !$oset_in($phys_ptr_cast(SL#x0, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(SL#x0, ^b_node)) == $rd_inv(_dryad_S0#0, b_node.key, $phys_ptr_cast(SL#x0, ^b_node));
            // assume ==>(!(@_vcc_oset_in(xl, old(_dryad_S0#0, bst_reach(xl)))), @_vcc_ptr_eq_pure(*((xl->left)), old(_dryad_S0#0, *((xl->left))))); 
            assume !$oset_in($phys_ptr_cast(L#xl, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#0, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(xl, old(_dryad_S0#0, bst_reach(xl)))), @_vcc_ptr_eq_pure(*((xl->right)), old(_dryad_S0#0, *((xl->right))))); 
            assume !$oset_in($phys_ptr_cast(L#xl, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#0, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(xl, old(_dryad_S0#0, bst_reach(xl)))), ==(*((xl->key)), old(_dryad_S0#0, *((xl->key))))); 
            assume !$oset_in($phys_ptr_cast(L#xl, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node)) == $rd_inv(_dryad_S0#0, b_node.key, $phys_ptr_cast(L#xl, ^b_node));
            // assume ==>(!(@_vcc_oset_in(xr, old(_dryad_S0#0, bst_reach(xl)))), @_vcc_ptr_eq_pure(*((xr->left)), old(_dryad_S0#0, *((xr->left))))); 
            assume !$oset_in($phys_ptr_cast(L#xr, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#0, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(xr, old(_dryad_S0#0, bst_reach(xl)))), @_vcc_ptr_eq_pure(*((xr->right)), old(_dryad_S0#0, *((xr->right))))); 
            assume !$oset_in($phys_ptr_cast(L#xr, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#0, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(xr, old(_dryad_S0#0, bst_reach(xl)))), ==(*((xr->key)), old(_dryad_S0#0, *((xr->key))))); 
            assume !$oset_in($phys_ptr_cast(L#xr, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node)) == $rd_inv(_dryad_S0#0, b_node.key, $phys_ptr_cast(L#xr, ^b_node));
            // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0#0, bst_reach(xl)))), @_vcc_ptr_eq_pure(*((x->left)), old(_dryad_S0#0, *((x->left))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#0, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0#0, bst_reach(xl)))), @_vcc_ptr_eq_pure(*((x->right)), old(_dryad_S0#0, *((x->right))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#0, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0#0, bst_reach(xl)))), ==(*((x->key)), old(_dryad_S0#0, *((x->key))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S0#0, $phys_ptr_cast(L#xl, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)) == $rd_inv(_dryad_S0#0, b_node.key, $phys_ptr_cast(P#x, ^b_node));
            // _math \state _dryad_S2; 
            // _dryad_S2 := @_vcc_current_state(@state); 
            SL#_dryad_S2 := $current_state($s);
            // _math \state stmtexpr5#12; 
            // stmtexpr5#12 := _dryad_S2; 
            stmtexpr5#12 := SL#_dryad_S2;
            // assert @prim_writes_check((x->left)); 
            assert $writable_prim($s, #wrTime$3^13.3, $dot($phys_ptr_cast(P#x, ^b_node), b_node.left));
            // *(x->left) := l; 
            call $write_int(b_node.left, $phys_ptr_cast(P#x, ^b_node), $ptr_to_int($phys_ptr_cast(L#l, ^b_node)));
            assume $full_stop_ext(#tok$3^31.5, $s);
            // _math \state _dryad_S3; 
            // _dryad_S3 := @_vcc_current_state(@state); 
            SL#_dryad_S3 := $current_state($s);
            // _math \state stmtexpr6#13; 
            // stmtexpr6#13 := _dryad_S3; 
            stmtexpr6#13 := SL#_dryad_S3;
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(*((x->right)))))), ==(old(_dryad_S2, bst(*((x->right)))), old(_dryad_S3, bst(*((x->right)))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) ==> F#bst(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) == F#bst(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(*((x->right)))))), ==(old(_dryad_S2, bst_reach(*((x->right)))), old(_dryad_S3, bst_reach(*((x->right)))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) ==> F#bst_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) == F#bst_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(*((x->right)))))), ==(old(_dryad_S2, bst_keys(*((x->right)))), old(_dryad_S3, bst_keys(*((x->right)))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) ==> F#bst_keys(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) == F#bst_keys(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(x1)))), ==(old(_dryad_S2, bst(x1)), old(_dryad_S3, bst(x1)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(SL#x1, ^b_node))) ==> F#bst(SL#_dryad_S2, $phys_ptr_cast(SL#x1, ^b_node)) == F#bst(SL#_dryad_S3, $phys_ptr_cast(SL#x1, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(x1)))), ==(old(_dryad_S2, bst_reach(x1)), old(_dryad_S3, bst_reach(x1)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(SL#x1, ^b_node))) ==> F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(SL#x1, ^b_node)) == F#bst_reach(SL#_dryad_S3, $phys_ptr_cast(SL#x1, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(x1)))), ==(old(_dryad_S2, bst_keys(x1)), old(_dryad_S3, bst_keys(x1)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(SL#x1, ^b_node))) ==> F#bst_keys(SL#_dryad_S2, $phys_ptr_cast(SL#x1, ^b_node)) == F#bst_keys(SL#_dryad_S3, $phys_ptr_cast(SL#x1, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(x0)))), ==(old(_dryad_S2, bst(x0)), old(_dryad_S3, bst(x0)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(SL#x0, ^b_node))) ==> F#bst(SL#_dryad_S2, $phys_ptr_cast(SL#x0, ^b_node)) == F#bst(SL#_dryad_S3, $phys_ptr_cast(SL#x0, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(x0)))), ==(old(_dryad_S2, bst_reach(x0)), old(_dryad_S3, bst_reach(x0)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(SL#x0, ^b_node))) ==> F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(SL#x0, ^b_node)) == F#bst_reach(SL#_dryad_S3, $phys_ptr_cast(SL#x0, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(x0)))), ==(old(_dryad_S2, bst_keys(x0)), old(_dryad_S3, bst_keys(x0)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(SL#x0, ^b_node))) ==> F#bst_keys(SL#_dryad_S2, $phys_ptr_cast(SL#x0, ^b_node)) == F#bst_keys(SL#_dryad_S3, $phys_ptr_cast(SL#x0, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(xl)))), ==(old(_dryad_S2, bst(xl)), old(_dryad_S3, bst(xl)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#xl, ^b_node))) ==> F#bst(SL#_dryad_S2, $phys_ptr_cast(L#xl, ^b_node)) == F#bst(SL#_dryad_S3, $phys_ptr_cast(L#xl, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(xl)))), ==(old(_dryad_S2, bst_reach(xl)), old(_dryad_S3, bst_reach(xl)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#xl, ^b_node))) ==> F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#xl, ^b_node)) == F#bst_reach(SL#_dryad_S3, $phys_ptr_cast(L#xl, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(xl)))), ==(old(_dryad_S2, bst_keys(xl)), old(_dryad_S3, bst_keys(xl)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#xl, ^b_node))) ==> F#bst_keys(SL#_dryad_S2, $phys_ptr_cast(L#xl, ^b_node)) == F#bst_keys(SL#_dryad_S3, $phys_ptr_cast(L#xl, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(xr)))), ==(old(_dryad_S2, bst(xr)), old(_dryad_S3, bst(xr)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#xr, ^b_node))) ==> F#bst(SL#_dryad_S2, $phys_ptr_cast(L#xr, ^b_node)) == F#bst(SL#_dryad_S3, $phys_ptr_cast(L#xr, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(xr)))), ==(old(_dryad_S2, bst_reach(xr)), old(_dryad_S3, bst_reach(xr)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#xr, ^b_node))) ==> F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#xr, ^b_node)) == F#bst_reach(SL#_dryad_S3, $phys_ptr_cast(L#xr, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(xr)))), ==(old(_dryad_S2, bst_keys(xr)), old(_dryad_S3, bst_keys(xr)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#xr, ^b_node))) ==> F#bst_keys(SL#_dryad_S2, $phys_ptr_cast(L#xr, ^b_node)) == F#bst_keys(SL#_dryad_S3, $phys_ptr_cast(L#xr, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(l)))), ==(old(_dryad_S2, bst(l)), old(_dryad_S3, bst(l)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#l, ^b_node))) ==> F#bst(SL#_dryad_S2, $phys_ptr_cast(L#l, ^b_node)) == F#bst(SL#_dryad_S3, $phys_ptr_cast(L#l, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(l)))), ==(old(_dryad_S2, bst_reach(l)), old(_dryad_S3, bst_reach(l)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#l, ^b_node))) ==> F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#l, ^b_node)) == F#bst_reach(SL#_dryad_S3, $phys_ptr_cast(L#l, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, bst_reach(l)))), ==(old(_dryad_S2, bst_keys(l)), old(_dryad_S3, bst_keys(l)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(SL#_dryad_S2, $phys_ptr_cast(L#l, ^b_node))) ==> F#bst_keys(SL#_dryad_S2, $phys_ptr_cast(L#l, ^b_node)) == F#bst_keys(SL#_dryad_S3, $phys_ptr_cast(L#l, ^b_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x1)), @_vcc_ptr_eq_pure(*((x1->left)), old(_dryad_S2, *((x1->left))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(SL#x1, ^b_node)) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S2, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x1)), @_vcc_ptr_eq_pure(*((x1->right)), old(_dryad_S2, *((x1->right))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(SL#x1, ^b_node)) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x1)), ==(*((x1->key)), old(_dryad_S2, *((x1->key))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(SL#x1, ^b_node)) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(SL#x1, ^b_node)) == $rd_inv(SL#_dryad_S2, b_node.key, $phys_ptr_cast(SL#x1, ^b_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x0)), @_vcc_ptr_eq_pure(*((x0->left)), old(_dryad_S2, *((x0->left))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(SL#x0, ^b_node)) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S2, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x0)), @_vcc_ptr_eq_pure(*((x0->right)), old(_dryad_S2, *((x0->right))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(SL#x0, ^b_node)) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x0)), ==(*((x0->key)), old(_dryad_S2, *((x0->key))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(SL#x0, ^b_node)) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(SL#x0, ^b_node)) == $rd_inv(SL#_dryad_S2, b_node.key, $phys_ptr_cast(SL#x0, ^b_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xl)), @_vcc_ptr_eq_pure(*((xl->left)), old(_dryad_S2, *((xl->left))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(L#xl, ^b_node)) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S2, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xl)), @_vcc_ptr_eq_pure(*((xl->right)), old(_dryad_S2, *((xl->right))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(L#xl, ^b_node)) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xl)), ==(*((xl->key)), old(_dryad_S2, *((xl->key))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(L#xl, ^b_node)) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node)) == $rd_inv(SL#_dryad_S2, b_node.key, $phys_ptr_cast(L#xl, ^b_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xr)), @_vcc_ptr_eq_pure(*((xr->left)), old(_dryad_S2, *((xr->left))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(L#xr, ^b_node)) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S2, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xr)), @_vcc_ptr_eq_pure(*((xr->right)), old(_dryad_S2, *((xr->right))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(L#xr, ^b_node)) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xr)), ==(*((xr->key)), old(_dryad_S2, *((xr->key))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(L#xr, ^b_node)) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node)) == $rd_inv(SL#_dryad_S2, b_node.key, $phys_ptr_cast(L#xr, ^b_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, l)), @_vcc_ptr_eq_pure(*((l->left)), old(_dryad_S2, *((l->left))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(L#l, ^b_node)) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S2, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, l)), @_vcc_ptr_eq_pure(*((l->right)), old(_dryad_S2, *((l->right))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(L#l, ^b_node)) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node) == $rd_phys_ptr(SL#_dryad_S2, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, l)), ==(*((l->key)), old(_dryad_S2, *((l->key))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(L#l, ^b_node)) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node)) == $rd_inv(SL#_dryad_S2, b_node.key, $phys_ptr_cast(L#l, ^b_node));
            // assume ==>(@_vcc_ptr_neq_null(x1), ==(bst(x1), &&(&&(&&(&&(&&(&&(&&(bst(*((x1->left))), bst(*((x1->right)))), unchecked!(@_vcc_oset_in(x1, @_vcc_oset_union(bst_reach(*((x1->left))), bst_reach(*((x1->right))))))), unchecked!(@_vcc_intset_in(*((x1->key)), @_vcc_intset_union(bst_keys(*((x1->left))), bst_keys(*((x1->right))))))), @_vcc_oset_disjoint(bst_reach(*((x1->left))), bst_reach(*((x1->right))))), @_vcc_intset_disjoint(bst_keys(*((x1->left))), bst_keys(*((x1->right))))), @_vcc_intset_lt_one2(bst_keys(*((x1->left))), *((x1->key)))), @_vcc_intset_lt_one1(*((x1->key)), bst_keys(*((x1->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x1, ^b_node)) ==> F#bst($s, $phys_ptr_cast(SL#x1, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(SL#x1, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x1, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(SL#x1, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x1, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x1), ==(bst_reach(x1), @_vcc_oset_union(@_vcc_oset_singleton(x1), @_vcc_oset_union(bst_reach(*((x1->left))), bst_reach(*((x1->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x1, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(SL#x1, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(SL#x1, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x1), ==(bst_keys(x1), @_vcc_intset_union(@_vcc_intset_singleton(*((x1->key))), @_vcc_intset_union(bst_keys(*((x1->left))), bst_keys(*((x1->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x1, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(SL#x1, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x1, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x1, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x1, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0), ==(bst(x0), &&(&&(&&(&&(&&(&&(&&(bst(*((x0->left))), bst(*((x0->right)))), unchecked!(@_vcc_oset_in(x0, @_vcc_oset_union(bst_reach(*((x0->left))), bst_reach(*((x0->right))))))), unchecked!(@_vcc_intset_in(*((x0->key)), @_vcc_intset_union(bst_keys(*((x0->left))), bst_keys(*((x0->right))))))), @_vcc_oset_disjoint(bst_reach(*((x0->left))), bst_reach(*((x0->right))))), @_vcc_intset_disjoint(bst_keys(*((x0->left))), bst_keys(*((x0->right))))), @_vcc_intset_lt_one2(bst_keys(*((x0->left))), *((x0->key)))), @_vcc_intset_lt_one1(*((x0->key)), bst_keys(*((x0->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x0, ^b_node)) ==> F#bst($s, $phys_ptr_cast(SL#x0, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(SL#x0, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x0, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(SL#x0, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x0, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0), ==(bst_reach(x0), @_vcc_oset_union(@_vcc_oset_singleton(x0), @_vcc_oset_union(bst_reach(*((x0->left))), bst_reach(*((x0->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x0, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(SL#x0, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(SL#x0, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0), ==(bst_keys(x0), @_vcc_intset_union(@_vcc_intset_singleton(*((x0->key))), @_vcc_intset_union(bst_keys(*((x0->left))), bst_keys(*((x0->right))))))); 
            assume $non_null($phys_ptr_cast(SL#x0, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(SL#x0, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(SL#x0, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(SL#x0, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(SL#x0, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl), ==(bst(xl), &&(&&(&&(&&(&&(&&(&&(bst(*((xl->left))), bst(*((xl->right)))), unchecked!(@_vcc_oset_in(xl, @_vcc_oset_union(bst_reach(*((xl->left))), bst_reach(*((xl->right))))))), unchecked!(@_vcc_intset_in(*((xl->key)), @_vcc_intset_union(bst_keys(*((xl->left))), bst_keys(*((xl->right))))))), @_vcc_oset_disjoint(bst_reach(*((xl->left))), bst_reach(*((xl->right))))), @_vcc_intset_disjoint(bst_keys(*((xl->left))), bst_keys(*((xl->right))))), @_vcc_intset_lt_one2(bst_keys(*((xl->left))), *((xl->key)))), @_vcc_intset_lt_one1(*((xl->key)), bst_keys(*((xl->right))))))); 
            assume $non_null($phys_ptr_cast(L#xl, ^b_node)) ==> F#bst($s, $phys_ptr_cast(L#xl, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(L#xl, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl), ==(bst_reach(xl), @_vcc_oset_union(@_vcc_oset_singleton(xl), @_vcc_oset_union(bst_reach(*((xl->left))), bst_reach(*((xl->right))))))); 
            assume $non_null($phys_ptr_cast(L#xl, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(L#xl, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(L#xl, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl), ==(bst_keys(xl), @_vcc_intset_union(@_vcc_intset_singleton(*((xl->key))), @_vcc_intset_union(bst_keys(*((xl->left))), bst_keys(*((xl->right))))))); 
            assume $non_null($phys_ptr_cast(L#xl, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(L#xl, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(L#xl, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xl, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xl, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr), ==(bst(xr), &&(&&(&&(&&(&&(&&(&&(bst(*((xr->left))), bst(*((xr->right)))), unchecked!(@_vcc_oset_in(xr, @_vcc_oset_union(bst_reach(*((xr->left))), bst_reach(*((xr->right))))))), unchecked!(@_vcc_intset_in(*((xr->key)), @_vcc_intset_union(bst_keys(*((xr->left))), bst_keys(*((xr->right))))))), @_vcc_oset_disjoint(bst_reach(*((xr->left))), bst_reach(*((xr->right))))), @_vcc_intset_disjoint(bst_keys(*((xr->left))), bst_keys(*((xr->right))))), @_vcc_intset_lt_one2(bst_keys(*((xr->left))), *((xr->key)))), @_vcc_intset_lt_one1(*((xr->key)), bst_keys(*((xr->right))))))); 
            assume $non_null($phys_ptr_cast(L#xr, ^b_node)) ==> F#bst($s, $phys_ptr_cast(L#xr, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(L#xr, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr), ==(bst_reach(xr), @_vcc_oset_union(@_vcc_oset_singleton(xr), @_vcc_oset_union(bst_reach(*((xr->left))), bst_reach(*((xr->right))))))); 
            assume $non_null($phys_ptr_cast(L#xr, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(L#xr, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(L#xr, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr), ==(bst_keys(xr), @_vcc_intset_union(@_vcc_intset_singleton(*((xr->key))), @_vcc_intset_union(bst_keys(*((xr->left))), bst_keys(*((xr->right))))))); 
            assume $non_null($phys_ptr_cast(L#xr, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(L#xr, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(L#xr, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#xr, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#xr, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(l), ==(bst(l), &&(&&(&&(&&(&&(&&(&&(bst(*((l->left))), bst(*((l->right)))), unchecked!(@_vcc_oset_in(l, @_vcc_oset_union(bst_reach(*((l->left))), bst_reach(*((l->right))))))), unchecked!(@_vcc_intset_in(*((l->key)), @_vcc_intset_union(bst_keys(*((l->left))), bst_keys(*((l->right))))))), @_vcc_oset_disjoint(bst_reach(*((l->left))), bst_reach(*((l->right))))), @_vcc_intset_disjoint(bst_keys(*((l->left))), bst_keys(*((l->right))))), @_vcc_intset_lt_one2(bst_keys(*((l->left))), *((l->key)))), @_vcc_intset_lt_one1(*((l->key)), bst_keys(*((l->right))))))); 
            assume $non_null($phys_ptr_cast(L#l, ^b_node)) ==> F#bst($s, $phys_ptr_cast(L#l, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(L#l, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(l), ==(bst_reach(l), @_vcc_oset_union(@_vcc_oset_singleton(l), @_vcc_oset_union(bst_reach(*((l->left))), bst_reach(*((l->right))))))); 
            assume $non_null($phys_ptr_cast(L#l, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(L#l, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(L#l, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(l), ==(bst_keys(l), @_vcc_intset_union(@_vcc_intset_singleton(*((l->key))), @_vcc_intset_union(bst_keys(*((l->left))), bst_keys(*((l->right))))))); 
            assume $non_null($phys_ptr_cast(L#l, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(L#l, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(l), ==(bst(l), &&(&&(&&(&&(&&(&&(&&(bst(*((l->left))), bst(*((l->right)))), unchecked!(@_vcc_oset_in(l, @_vcc_oset_union(bst_reach(*((l->left))), bst_reach(*((l->right))))))), unchecked!(@_vcc_intset_in(*((l->key)), @_vcc_intset_union(bst_keys(*((l->left))), bst_keys(*((l->right))))))), @_vcc_oset_disjoint(bst_reach(*((l->left))), bst_reach(*((l->right))))), @_vcc_intset_disjoint(bst_keys(*((l->left))), bst_keys(*((l->right))))), @_vcc_intset_lt_one2(bst_keys(*((l->left))), *((l->key)))), @_vcc_intset_lt_one1(*((l->key)), bst_keys(*((l->right))))))); 
            assume $non_null($phys_ptr_cast(L#l, ^b_node)) ==> F#bst($s, $phys_ptr_cast(L#l, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(L#l, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(l), ==(bst_reach(l), @_vcc_oset_union(@_vcc_oset_singleton(l), @_vcc_oset_union(bst_reach(*((l->left))), bst_reach(*((l->right))))))); 
            assume $non_null($phys_ptr_cast(L#l, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(L#l, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(L#l, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(l), ==(bst_keys(l), @_vcc_intset_union(@_vcc_intset_singleton(*((l->key))), @_vcc_intset_union(bst_keys(*((l->left))), bst_keys(*((l->right))))))); 
            assume $non_null($phys_ptr_cast(L#l, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(L#l, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(L#l, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(L#l, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(L#l, ^b_node), ^b_node))));
            // return x; 
            $result := $phys_ptr_cast(P#x, ^b_node);
            assume true;
            assert $position_marker();
            goto #exit;
        }
        else
        {
          anon3:
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // struct b_node* r#2; 
            // struct b_node* xr#3; 
            // struct b_node* xl#4; 
            // struct b_node* x0#5; 
            // x0#5 := x; 
            x0#5 := $phys_ptr_cast(P#x, ^b_node);
            // struct b_node* stmtexpr0#14; 
            // stmtexpr0#14 := x0#5; 
            stmtexpr0#14 := $phys_ptr_cast(x0#5, ^b_node);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assert @reads_check_normal((x->left)); 
            assert $thread_local($s, $phys_ptr_cast(P#x, ^b_node));
            // xl#4 := *((x->left)); 
            xl#4 := $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node);
            // assume ==>(@_vcc_ptr_neq_null(xl#4), ==(bst(xl#4), &&(&&(&&(&&(&&(&&(&&(bst(*((xl#4->left))), bst(*((xl#4->right)))), unchecked!(@_vcc_oset_in(xl#4, @_vcc_oset_union(bst_reach(*((xl#4->left))), bst_reach(*((xl#4->right))))))), unchecked!(@_vcc_intset_in(*((xl#4->key)), @_vcc_intset_union(bst_keys(*((xl#4->left))), bst_keys(*((xl#4->right))))))), @_vcc_oset_disjoint(bst_reach(*((xl#4->left))), bst_reach(*((xl#4->right))))), @_vcc_intset_disjoint(bst_keys(*((xl#4->left))), bst_keys(*((xl#4->right))))), @_vcc_intset_lt_one2(bst_keys(*((xl#4->left))), *((xl#4->key)))), @_vcc_intset_lt_one1(*((xl#4->key)), bst_keys(*((xl#4->right))))))); 
            assume $non_null($phys_ptr_cast(xl#4, ^b_node)) ==> F#bst($s, $phys_ptr_cast(xl#4, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(xl#4, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl#4), ==(bst_reach(xl#4), @_vcc_oset_union(@_vcc_oset_singleton(xl#4), @_vcc_oset_union(bst_reach(*((xl#4->left))), bst_reach(*((xl#4->right))))))); 
            assume $non_null($phys_ptr_cast(xl#4, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(xl#4, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(xl#4, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl#4), ==(bst_keys(xl#4), @_vcc_intset_union(@_vcc_intset_singleton(*((xl#4->key))), @_vcc_intset_union(bst_keys(*((xl#4->left))), bst_keys(*((xl#4->right))))))); 
            assume $non_null($phys_ptr_cast(xl#4, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(xl#4, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // struct b_node* x1#6; 
            // x1#6 := x; 
            x1#6 := $phys_ptr_cast(P#x, ^b_node);
            // struct b_node* stmtexpr1#15; 
            // stmtexpr1#15 := x1#6; 
            stmtexpr1#15 := $phys_ptr_cast(x1#6, ^b_node);
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assert @reads_check_normal((x->right)); 
            assert $thread_local($s, $phys_ptr_cast(P#x, ^b_node));
            // xr#3 := *((x->right)); 
            xr#3 := $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node);
            // assume ==>(@_vcc_ptr_neq_null(xr#3), ==(bst(xr#3), &&(&&(&&(&&(&&(&&(&&(bst(*((xr#3->left))), bst(*((xr#3->right)))), unchecked!(@_vcc_oset_in(xr#3, @_vcc_oset_union(bst_reach(*((xr#3->left))), bst_reach(*((xr#3->right))))))), unchecked!(@_vcc_intset_in(*((xr#3->key)), @_vcc_intset_union(bst_keys(*((xr#3->left))), bst_keys(*((xr#3->right))))))), @_vcc_oset_disjoint(bst_reach(*((xr#3->left))), bst_reach(*((xr#3->right))))), @_vcc_intset_disjoint(bst_keys(*((xr#3->left))), bst_keys(*((xr#3->right))))), @_vcc_intset_lt_one2(bst_keys(*((xr#3->left))), *((xr#3->key)))), @_vcc_intset_lt_one1(*((xr#3->key)), bst_keys(*((xr#3->right))))))); 
            assume $non_null($phys_ptr_cast(xr#3, ^b_node)) ==> F#bst($s, $phys_ptr_cast(xr#3, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(xr#3, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr#3), ==(bst_reach(xr#3), @_vcc_oset_union(@_vcc_oset_singleton(xr#3), @_vcc_oset_union(bst_reach(*((xr#3->left))), bst_reach(*((xr#3->right))))))); 
            assume $non_null($phys_ptr_cast(xr#3, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(xr#3, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(xr#3, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr#3), ==(bst_keys(xr#3), @_vcc_intset_union(@_vcc_intset_singleton(*((xr#3->key))), @_vcc_intset_union(bst_keys(*((xr#3->left))), bst_keys(*((xr#3->right))))))); 
            assume $non_null($phys_ptr_cast(xr#3, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(xr#3, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // _math \state _dryad_S0#7; 
            // _dryad_S0#7 := @_vcc_current_state(@state); 
            _dryad_S0#7 := $current_state($s);
            // _math \state stmtexpr2#16; 
            // stmtexpr2#16 := _dryad_S0#7; 
            stmtexpr2#16 := _dryad_S0#7;
            // non-pure function
            // r#2 := bst_delete_rec(xr#3, k); 
            call r#2 := bst_delete_rec($phys_ptr_cast(xr#3, ^b_node), P#k);
            assume $full_stop_ext(#tok$3^38.17, $s);
            // _math \state _dryad_S1#8; 
            // _dryad_S1#8 := @_vcc_current_state(@state); 
            _dryad_S1#8 := $current_state($s);
            // _math \state stmtexpr3#17; 
            // stmtexpr3#17 := _dryad_S1#8; 
            stmtexpr3#17 := _dryad_S1#8;
            // assume @_vcc_oset_disjoint(bst_reach(r#2), @_vcc_oset_diff(_dryad_G1, old(_dryad_S0#7, bst_reach(xr#3)))); 
            assume $oset_disjoint(F#bst_reach($s, $phys_ptr_cast(r#2, ^b_node)), $oset_diff(SL#_dryad_G1, F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))));
            // _math \oset res_bst_reach#3; 
            // res_bst_reach#3 := bst_reach(r#2); 
            call res_bst_reach#3 := bst_reach($phys_ptr_cast(r#2, ^b_node));
            assume $full_stop_ext(#tok$4^0.0, $s);
            // _dryad_G1 := @_vcc_oset_union(res_bst_reach#3, @_vcc_oset_diff(_dryad_G1, pure(old(_dryad_S0#7, bst_reach(xr#3))))); 
            SL#_dryad_G1 := $oset_union(res_bst_reach#3, $oset_diff(SL#_dryad_G1, F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))));
            // _math \oset stmtexpr4#18; 
            // stmtexpr4#18 := _dryad_G1; 
            stmtexpr4#18 := SL#_dryad_G1;
            // assume ==(glob_reach(), _dryad_G1); 
            assume F#glob_reach() == SL#_dryad_G1;
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(x1#6))), ==(old(_dryad_S0#7, bst(x1#6)), old(_dryad_S1#8, bst(x1#6)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(x1#6, ^b_node))) ==> F#bst(_dryad_S0#7, $phys_ptr_cast(x1#6, ^b_node)) == F#bst(_dryad_S1#8, $phys_ptr_cast(x1#6, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(x1#6))), ==(old(_dryad_S0#7, bst_reach(x1#6)), old(_dryad_S1#8, bst_reach(x1#6)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(x1#6, ^b_node))) ==> F#bst_reach(_dryad_S0#7, $phys_ptr_cast(x1#6, ^b_node)) == F#bst_reach(_dryad_S1#8, $phys_ptr_cast(x1#6, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(x1#6))), ==(old(_dryad_S0#7, bst_keys(x1#6)), old(_dryad_S1#8, bst_keys(x1#6)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(x1#6, ^b_node))) ==> F#bst_keys(_dryad_S0#7, $phys_ptr_cast(x1#6, ^b_node)) == F#bst_keys(_dryad_S1#8, $phys_ptr_cast(x1#6, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(x0#5))), ==(old(_dryad_S0#7, bst(x0#5)), old(_dryad_S1#8, bst(x0#5)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(x0#5, ^b_node))) ==> F#bst(_dryad_S0#7, $phys_ptr_cast(x0#5, ^b_node)) == F#bst(_dryad_S1#8, $phys_ptr_cast(x0#5, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(x0#5))), ==(old(_dryad_S0#7, bst_reach(x0#5)), old(_dryad_S1#8, bst_reach(x0#5)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(x0#5, ^b_node))) ==> F#bst_reach(_dryad_S0#7, $phys_ptr_cast(x0#5, ^b_node)) == F#bst_reach(_dryad_S1#8, $phys_ptr_cast(x0#5, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(x0#5))), ==(old(_dryad_S0#7, bst_keys(x0#5)), old(_dryad_S1#8, bst_keys(x0#5)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(x0#5, ^b_node))) ==> F#bst_keys(_dryad_S0#7, $phys_ptr_cast(x0#5, ^b_node)) == F#bst_keys(_dryad_S1#8, $phys_ptr_cast(x0#5, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(xl#4))), ==(old(_dryad_S0#7, bst(xl#4)), old(_dryad_S1#8, bst(xl#4)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xl#4, ^b_node))) ==> F#bst(_dryad_S0#7, $phys_ptr_cast(xl#4, ^b_node)) == F#bst(_dryad_S1#8, $phys_ptr_cast(xl#4, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(xl#4))), ==(old(_dryad_S0#7, bst_reach(xl#4)), old(_dryad_S1#8, bst_reach(xl#4)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xl#4, ^b_node))) ==> F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xl#4, ^b_node)) == F#bst_reach(_dryad_S1#8, $phys_ptr_cast(xl#4, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(xl#4))), ==(old(_dryad_S0#7, bst_keys(xl#4)), old(_dryad_S1#8, bst_keys(xl#4)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xl#4, ^b_node))) ==> F#bst_keys(_dryad_S0#7, $phys_ptr_cast(xl#4, ^b_node)) == F#bst_keys(_dryad_S1#8, $phys_ptr_cast(xl#4, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(xr#3))), ==(old(_dryad_S0#7, bst(xr#3)), old(_dryad_S1#8, bst(xr#3)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> F#bst(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)) == F#bst(_dryad_S1#8, $phys_ptr_cast(xr#3, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(xr#3))), ==(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S1#8, bst_reach(xr#3)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)) == F#bst_reach(_dryad_S1#8, $phys_ptr_cast(xr#3, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(xr#3))), ==(old(_dryad_S0#7, bst_keys(xr#3)), old(_dryad_S1#8, bst_keys(xr#3)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> F#bst_keys(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)) == F#bst_keys(_dryad_S1#8, $phys_ptr_cast(xr#3, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(x))), ==(old(_dryad_S0#7, bst(x)), old(_dryad_S1#8, bst(x)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(P#x, ^b_node))) ==> F#bst(_dryad_S0#7, $phys_ptr_cast(P#x, ^b_node)) == F#bst(_dryad_S1#8, $phys_ptr_cast(P#x, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(x))), ==(old(_dryad_S0#7, bst_reach(x)), old(_dryad_S1#8, bst_reach(x)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(P#x, ^b_node))) ==> F#bst_reach(_dryad_S0#7, $phys_ptr_cast(P#x, ^b_node)) == F#bst_reach(_dryad_S1#8, $phys_ptr_cast(P#x, ^b_node));
            // assume ==>(@_vcc_oset_disjoint(old(_dryad_S0#7, bst_reach(xr#3)), old(_dryad_S0#7, bst_reach(x))), ==(old(_dryad_S0#7, bst_keys(x)), old(_dryad_S1#8, bst_keys(x)))); 
            assume $oset_disjoint(F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node)), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(P#x, ^b_node))) ==> F#bst_keys(_dryad_S0#7, $phys_ptr_cast(P#x, ^b_node)) == F#bst_keys(_dryad_S1#8, $phys_ptr_cast(P#x, ^b_node));
            // assume ==>(@_vcc_ptr_neq_null(x1#6), ==(bst(x1#6), &&(&&(&&(&&(&&(&&(&&(bst(*((x1#6->left))), bst(*((x1#6->right)))), unchecked!(@_vcc_oset_in(x1#6, @_vcc_oset_union(bst_reach(*((x1#6->left))), bst_reach(*((x1#6->right))))))), unchecked!(@_vcc_intset_in(*((x1#6->key)), @_vcc_intset_union(bst_keys(*((x1#6->left))), bst_keys(*((x1#6->right))))))), @_vcc_oset_disjoint(bst_reach(*((x1#6->left))), bst_reach(*((x1#6->right))))), @_vcc_intset_disjoint(bst_keys(*((x1#6->left))), bst_keys(*((x1#6->right))))), @_vcc_intset_lt_one2(bst_keys(*((x1#6->left))), *((x1#6->key)))), @_vcc_intset_lt_one1(*((x1#6->key)), bst_keys(*((x1#6->right))))))); 
            assume $non_null($phys_ptr_cast(x1#6, ^b_node)) ==> F#bst($s, $phys_ptr_cast(x1#6, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(x1#6, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(x1#6, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(x1#6, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(x1#6, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x1#6), ==(bst_reach(x1#6), @_vcc_oset_union(@_vcc_oset_singleton(x1#6), @_vcc_oset_union(bst_reach(*((x1#6->left))), bst_reach(*((x1#6->right))))))); 
            assume $non_null($phys_ptr_cast(x1#6, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(x1#6, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(x1#6, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x1#6), ==(bst_keys(x1#6), @_vcc_intset_union(@_vcc_intset_singleton(*((x1#6->key))), @_vcc_intset_union(bst_keys(*((x1#6->left))), bst_keys(*((x1#6->right))))))); 
            assume $non_null($phys_ptr_cast(x1#6, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(x1#6, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(x1#6, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0#5), ==(bst(x0#5), &&(&&(&&(&&(&&(&&(&&(bst(*((x0#5->left))), bst(*((x0#5->right)))), unchecked!(@_vcc_oset_in(x0#5, @_vcc_oset_union(bst_reach(*((x0#5->left))), bst_reach(*((x0#5->right))))))), unchecked!(@_vcc_intset_in(*((x0#5->key)), @_vcc_intset_union(bst_keys(*((x0#5->left))), bst_keys(*((x0#5->right))))))), @_vcc_oset_disjoint(bst_reach(*((x0#5->left))), bst_reach(*((x0#5->right))))), @_vcc_intset_disjoint(bst_keys(*((x0#5->left))), bst_keys(*((x0#5->right))))), @_vcc_intset_lt_one2(bst_keys(*((x0#5->left))), *((x0#5->key)))), @_vcc_intset_lt_one1(*((x0#5->key)), bst_keys(*((x0#5->right))))))); 
            assume $non_null($phys_ptr_cast(x0#5, ^b_node)) ==> F#bst($s, $phys_ptr_cast(x0#5, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(x0#5, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(x0#5, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(x0#5, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(x0#5, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0#5), ==(bst_reach(x0#5), @_vcc_oset_union(@_vcc_oset_singleton(x0#5), @_vcc_oset_union(bst_reach(*((x0#5->left))), bst_reach(*((x0#5->right))))))); 
            assume $non_null($phys_ptr_cast(x0#5, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(x0#5, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(x0#5, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0#5), ==(bst_keys(x0#5), @_vcc_intset_union(@_vcc_intset_singleton(*((x0#5->key))), @_vcc_intset_union(bst_keys(*((x0#5->left))), bst_keys(*((x0#5->right))))))); 
            assume $non_null($phys_ptr_cast(x0#5, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(x0#5, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(x0#5, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl#4), ==(bst(xl#4), &&(&&(&&(&&(&&(&&(&&(bst(*((xl#4->left))), bst(*((xl#4->right)))), unchecked!(@_vcc_oset_in(xl#4, @_vcc_oset_union(bst_reach(*((xl#4->left))), bst_reach(*((xl#4->right))))))), unchecked!(@_vcc_intset_in(*((xl#4->key)), @_vcc_intset_union(bst_keys(*((xl#4->left))), bst_keys(*((xl#4->right))))))), @_vcc_oset_disjoint(bst_reach(*((xl#4->left))), bst_reach(*((xl#4->right))))), @_vcc_intset_disjoint(bst_keys(*((xl#4->left))), bst_keys(*((xl#4->right))))), @_vcc_intset_lt_one2(bst_keys(*((xl#4->left))), *((xl#4->key)))), @_vcc_intset_lt_one1(*((xl#4->key)), bst_keys(*((xl#4->right))))))); 
            assume $non_null($phys_ptr_cast(xl#4, ^b_node)) ==> F#bst($s, $phys_ptr_cast(xl#4, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(xl#4, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl#4), ==(bst_reach(xl#4), @_vcc_oset_union(@_vcc_oset_singleton(xl#4), @_vcc_oset_union(bst_reach(*((xl#4->left))), bst_reach(*((xl#4->right))))))); 
            assume $non_null($phys_ptr_cast(xl#4, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(xl#4, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(xl#4, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl#4), ==(bst_keys(xl#4), @_vcc_intset_union(@_vcc_intset_singleton(*((xl#4->key))), @_vcc_intset_union(bst_keys(*((xl#4->left))), bst_keys(*((xl#4->right))))))); 
            assume $non_null($phys_ptr_cast(xl#4, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(xl#4, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr#3), ==(bst(xr#3), &&(&&(&&(&&(&&(&&(&&(bst(*((xr#3->left))), bst(*((xr#3->right)))), unchecked!(@_vcc_oset_in(xr#3, @_vcc_oset_union(bst_reach(*((xr#3->left))), bst_reach(*((xr#3->right))))))), unchecked!(@_vcc_intset_in(*((xr#3->key)), @_vcc_intset_union(bst_keys(*((xr#3->left))), bst_keys(*((xr#3->right))))))), @_vcc_oset_disjoint(bst_reach(*((xr#3->left))), bst_reach(*((xr#3->right))))), @_vcc_intset_disjoint(bst_keys(*((xr#3->left))), bst_keys(*((xr#3->right))))), @_vcc_intset_lt_one2(bst_keys(*((xr#3->left))), *((xr#3->key)))), @_vcc_intset_lt_one1(*((xr#3->key)), bst_keys(*((xr#3->right))))))); 
            assume $non_null($phys_ptr_cast(xr#3, ^b_node)) ==> F#bst($s, $phys_ptr_cast(xr#3, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(xr#3, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr#3), ==(bst_reach(xr#3), @_vcc_oset_union(@_vcc_oset_singleton(xr#3), @_vcc_oset_union(bst_reach(*((xr#3->left))), bst_reach(*((xr#3->right))))))); 
            assume $non_null($phys_ptr_cast(xr#3, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(xr#3, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(xr#3, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr#3), ==(bst_keys(xr#3), @_vcc_intset_union(@_vcc_intset_singleton(*((xr#3->key))), @_vcc_intset_union(bst_keys(*((xr#3->left))), bst_keys(*((xr#3->right))))))); 
            assume $non_null($phys_ptr_cast(xr#3, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(xr#3, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(r#2), ==(bst(r#2), &&(&&(&&(&&(&&(&&(&&(bst(*((r#2->left))), bst(*((r#2->right)))), unchecked!(@_vcc_oset_in(r#2, @_vcc_oset_union(bst_reach(*((r#2->left))), bst_reach(*((r#2->right))))))), unchecked!(@_vcc_intset_in(*((r#2->key)), @_vcc_intset_union(bst_keys(*((r#2->left))), bst_keys(*((r#2->right))))))), @_vcc_oset_disjoint(bst_reach(*((r#2->left))), bst_reach(*((r#2->right))))), @_vcc_intset_disjoint(bst_keys(*((r#2->left))), bst_keys(*((r#2->right))))), @_vcc_intset_lt_one2(bst_keys(*((r#2->left))), *((r#2->key)))), @_vcc_intset_lt_one1(*((r#2->key)), bst_keys(*((r#2->right))))))); 
            assume $non_null($phys_ptr_cast(r#2, ^b_node)) ==> F#bst($s, $phys_ptr_cast(r#2, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(r#2, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(r#2), ==(bst_reach(r#2), @_vcc_oset_union(@_vcc_oset_singleton(r#2), @_vcc_oset_union(bst_reach(*((r#2->left))), bst_reach(*((r#2->right))))))); 
            assume $non_null($phys_ptr_cast(r#2, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(r#2, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(r#2, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(r#2), ==(bst_keys(r#2), @_vcc_intset_union(@_vcc_intset_singleton(*((r#2->key))), @_vcc_intset_union(bst_keys(*((r#2->left))), bst_keys(*((r#2->right))))))); 
            assume $non_null($phys_ptr_cast(r#2, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(r#2, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(!(@_vcc_oset_in(x1#6, old(_dryad_S0#7, bst_reach(xr#3)))), @_vcc_ptr_eq_pure(*((x1#6->left)), old(_dryad_S0#7, *((x1#6->left))))); 
            assume !$oset_in($phys_ptr_cast(x1#6, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#7, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x1#6, old(_dryad_S0#7, bst_reach(xr#3)))), @_vcc_ptr_eq_pure(*((x1#6->right)), old(_dryad_S0#7, *((x1#6->right))))); 
            assume !$oset_in($phys_ptr_cast(x1#6, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#7, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x1#6, old(_dryad_S0#7, bst_reach(xr#3)))), ==(*((x1#6->key)), old(_dryad_S0#7, *((x1#6->key))))); 
            assume !$oset_in($phys_ptr_cast(x1#6, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(x1#6, ^b_node)) == $rd_inv(_dryad_S0#7, b_node.key, $phys_ptr_cast(x1#6, ^b_node));
            // assume ==>(!(@_vcc_oset_in(x0#5, old(_dryad_S0#7, bst_reach(xr#3)))), @_vcc_ptr_eq_pure(*((x0#5->left)), old(_dryad_S0#7, *((x0#5->left))))); 
            assume !$oset_in($phys_ptr_cast(x0#5, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#7, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x0#5, old(_dryad_S0#7, bst_reach(xr#3)))), @_vcc_ptr_eq_pure(*((x0#5->right)), old(_dryad_S0#7, *((x0#5->right))))); 
            assume !$oset_in($phys_ptr_cast(x0#5, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#7, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x0#5, old(_dryad_S0#7, bst_reach(xr#3)))), ==(*((x0#5->key)), old(_dryad_S0#7, *((x0#5->key))))); 
            assume !$oset_in($phys_ptr_cast(x0#5, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(x0#5, ^b_node)) == $rd_inv(_dryad_S0#7, b_node.key, $phys_ptr_cast(x0#5, ^b_node));
            // assume ==>(!(@_vcc_oset_in(xl#4, old(_dryad_S0#7, bst_reach(xr#3)))), @_vcc_ptr_eq_pure(*((xl#4->left)), old(_dryad_S0#7, *((xl#4->left))))); 
            assume !$oset_in($phys_ptr_cast(xl#4, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#7, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(xl#4, old(_dryad_S0#7, bst_reach(xr#3)))), @_vcc_ptr_eq_pure(*((xl#4->right)), old(_dryad_S0#7, *((xl#4->right))))); 
            assume !$oset_in($phys_ptr_cast(xl#4, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#7, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(xl#4, old(_dryad_S0#7, bst_reach(xr#3)))), ==(*((xl#4->key)), old(_dryad_S0#7, *((xl#4->key))))); 
            assume !$oset_in($phys_ptr_cast(xl#4, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node)) == $rd_inv(_dryad_S0#7, b_node.key, $phys_ptr_cast(xl#4, ^b_node));
            // assume ==>(!(@_vcc_oset_in(xr#3, old(_dryad_S0#7, bst_reach(xr#3)))), @_vcc_ptr_eq_pure(*((xr#3->left)), old(_dryad_S0#7, *((xr#3->left))))); 
            assume !$oset_in($phys_ptr_cast(xr#3, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#7, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(xr#3, old(_dryad_S0#7, bst_reach(xr#3)))), @_vcc_ptr_eq_pure(*((xr#3->right)), old(_dryad_S0#7, *((xr#3->right))))); 
            assume !$oset_in($phys_ptr_cast(xr#3, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#7, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(xr#3, old(_dryad_S0#7, bst_reach(xr#3)))), ==(*((xr#3->key)), old(_dryad_S0#7, *((xr#3->key))))); 
            assume !$oset_in($phys_ptr_cast(xr#3, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node)) == $rd_inv(_dryad_S0#7, b_node.key, $phys_ptr_cast(xr#3, ^b_node));
            // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0#7, bst_reach(xr#3)))), @_vcc_ptr_eq_pure(*((x->left)), old(_dryad_S0#7, *((x->left))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#7, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0#7, bst_reach(xr#3)))), @_vcc_ptr_eq_pure(*((x->right)), old(_dryad_S0#7, *((x->right))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S0#7, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_oset_in(x, old(_dryad_S0#7, bst_reach(xr#3)))), ==(*((x->key)), old(_dryad_S0#7, *((x->key))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S0#7, $phys_ptr_cast(xr#3, ^b_node))) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)) == $rd_inv(_dryad_S0#7, b_node.key, $phys_ptr_cast(P#x, ^b_node));
            // _math \state _dryad_S2#9; 
            // _dryad_S2#9 := @_vcc_current_state(@state); 
            _dryad_S2#9 := $current_state($s);
            // _math \state stmtexpr5#19; 
            // stmtexpr5#19 := _dryad_S2#9; 
            stmtexpr5#19 := _dryad_S2#9;
            // assert @prim_writes_check((x->right)); 
            assert $writable_prim($s, #wrTime$3^13.3, $dot($phys_ptr_cast(P#x, ^b_node), b_node.right));
            // *(x->right) := r#2; 
            call $write_int(b_node.right, $phys_ptr_cast(P#x, ^b_node), $ptr_to_int($phys_ptr_cast(r#2, ^b_node)));
            assume $full_stop_ext(#tok$3^40.5, $s);
            // _math \state _dryad_S3#10; 
            // _dryad_S3#10 := @_vcc_current_state(@state); 
            _dryad_S3#10 := $current_state($s);
            // _math \state stmtexpr6#20; 
            // stmtexpr6#20 := _dryad_S3#10; 
            stmtexpr6#20 := _dryad_S3#10;
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(*((x->left)))))), ==(old(_dryad_S2#9, bst(*((x->left)))), old(_dryad_S3#10, bst(*((x->left)))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node))) ==> F#bst(_dryad_S2#9, $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) == F#bst(_dryad_S3#10, $rd_phys_ptr(_dryad_S3#10, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(*((x->left)))))), ==(old(_dryad_S2#9, bst_reach(*((x->left)))), old(_dryad_S3#10, bst_reach(*((x->left)))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node))) ==> F#bst_reach(_dryad_S2#9, $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) == F#bst_reach(_dryad_S3#10, $rd_phys_ptr(_dryad_S3#10, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(*((x->left)))))), ==(old(_dryad_S2#9, bst_keys(*((x->left)))), old(_dryad_S3#10, bst_keys(*((x->left)))))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node))) ==> F#bst_keys(_dryad_S2#9, $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) == F#bst_keys(_dryad_S3#10, $rd_phys_ptr(_dryad_S3#10, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(x1#6)))), ==(old(_dryad_S2#9, bst(x1#6)), old(_dryad_S3#10, bst(x1#6)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(x1#6, ^b_node))) ==> F#bst(_dryad_S2#9, $phys_ptr_cast(x1#6, ^b_node)) == F#bst(_dryad_S3#10, $phys_ptr_cast(x1#6, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(x1#6)))), ==(old(_dryad_S2#9, bst_reach(x1#6)), old(_dryad_S3#10, bst_reach(x1#6)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(x1#6, ^b_node))) ==> F#bst_reach(_dryad_S2#9, $phys_ptr_cast(x1#6, ^b_node)) == F#bst_reach(_dryad_S3#10, $phys_ptr_cast(x1#6, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(x1#6)))), ==(old(_dryad_S2#9, bst_keys(x1#6)), old(_dryad_S3#10, bst_keys(x1#6)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(x1#6, ^b_node))) ==> F#bst_keys(_dryad_S2#9, $phys_ptr_cast(x1#6, ^b_node)) == F#bst_keys(_dryad_S3#10, $phys_ptr_cast(x1#6, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(x0#5)))), ==(old(_dryad_S2#9, bst(x0#5)), old(_dryad_S3#10, bst(x0#5)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(x0#5, ^b_node))) ==> F#bst(_dryad_S2#9, $phys_ptr_cast(x0#5, ^b_node)) == F#bst(_dryad_S3#10, $phys_ptr_cast(x0#5, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(x0#5)))), ==(old(_dryad_S2#9, bst_reach(x0#5)), old(_dryad_S3#10, bst_reach(x0#5)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(x0#5, ^b_node))) ==> F#bst_reach(_dryad_S2#9, $phys_ptr_cast(x0#5, ^b_node)) == F#bst_reach(_dryad_S3#10, $phys_ptr_cast(x0#5, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(x0#5)))), ==(old(_dryad_S2#9, bst_keys(x0#5)), old(_dryad_S3#10, bst_keys(x0#5)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(x0#5, ^b_node))) ==> F#bst_keys(_dryad_S2#9, $phys_ptr_cast(x0#5, ^b_node)) == F#bst_keys(_dryad_S3#10, $phys_ptr_cast(x0#5, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(xl#4)))), ==(old(_dryad_S2#9, bst(xl#4)), old(_dryad_S3#10, bst(xl#4)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(xl#4, ^b_node))) ==> F#bst(_dryad_S2#9, $phys_ptr_cast(xl#4, ^b_node)) == F#bst(_dryad_S3#10, $phys_ptr_cast(xl#4, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(xl#4)))), ==(old(_dryad_S2#9, bst_reach(xl#4)), old(_dryad_S3#10, bst_reach(xl#4)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(xl#4, ^b_node))) ==> F#bst_reach(_dryad_S2#9, $phys_ptr_cast(xl#4, ^b_node)) == F#bst_reach(_dryad_S3#10, $phys_ptr_cast(xl#4, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(xl#4)))), ==(old(_dryad_S2#9, bst_keys(xl#4)), old(_dryad_S3#10, bst_keys(xl#4)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(xl#4, ^b_node))) ==> F#bst_keys(_dryad_S2#9, $phys_ptr_cast(xl#4, ^b_node)) == F#bst_keys(_dryad_S3#10, $phys_ptr_cast(xl#4, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(xr#3)))), ==(old(_dryad_S2#9, bst(xr#3)), old(_dryad_S3#10, bst(xr#3)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(xr#3, ^b_node))) ==> F#bst(_dryad_S2#9, $phys_ptr_cast(xr#3, ^b_node)) == F#bst(_dryad_S3#10, $phys_ptr_cast(xr#3, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(xr#3)))), ==(old(_dryad_S2#9, bst_reach(xr#3)), old(_dryad_S3#10, bst_reach(xr#3)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(xr#3, ^b_node))) ==> F#bst_reach(_dryad_S2#9, $phys_ptr_cast(xr#3, ^b_node)) == F#bst_reach(_dryad_S3#10, $phys_ptr_cast(xr#3, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(xr#3)))), ==(old(_dryad_S2#9, bst_keys(xr#3)), old(_dryad_S3#10, bst_keys(xr#3)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(xr#3, ^b_node))) ==> F#bst_keys(_dryad_S2#9, $phys_ptr_cast(xr#3, ^b_node)) == F#bst_keys(_dryad_S3#10, $phys_ptr_cast(xr#3, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(r#2)))), ==(old(_dryad_S2#9, bst(r#2)), old(_dryad_S3#10, bst(r#2)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(r#2, ^b_node))) ==> F#bst(_dryad_S2#9, $phys_ptr_cast(r#2, ^b_node)) == F#bst(_dryad_S3#10, $phys_ptr_cast(r#2, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(r#2)))), ==(old(_dryad_S2#9, bst_reach(r#2)), old(_dryad_S3#10, bst_reach(r#2)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(r#2, ^b_node))) ==> F#bst_reach(_dryad_S2#9, $phys_ptr_cast(r#2, ^b_node)) == F#bst_reach(_dryad_S3#10, $phys_ptr_cast(r#2, ^b_node));
            // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2#9, bst_reach(r#2)))), ==(old(_dryad_S2#9, bst_keys(r#2)), old(_dryad_S3#10, bst_keys(r#2)))); 
            assume !$oset_in($phys_ptr_cast(P#x, ^b_node), F#bst_reach(_dryad_S2#9, $phys_ptr_cast(r#2, ^b_node))) ==> F#bst_keys(_dryad_S2#9, $phys_ptr_cast(r#2, ^b_node)) == F#bst_keys(_dryad_S3#10, $phys_ptr_cast(r#2, ^b_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x1#6)), @_vcc_ptr_eq_pure(*((x1#6->left)), old(_dryad_S2#9, *((x1#6->left))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(x1#6, ^b_node)) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x1#6)), @_vcc_ptr_eq_pure(*((x1#6->right)), old(_dryad_S2#9, *((x1#6->right))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(x1#6, ^b_node)) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S2#9, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x1#6)), ==(*((x1#6->key)), old(_dryad_S2#9, *((x1#6->key))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(x1#6, ^b_node)) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(x1#6, ^b_node)) == $rd_inv(_dryad_S2#9, b_node.key, $phys_ptr_cast(x1#6, ^b_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x0#5)), @_vcc_ptr_eq_pure(*((x0#5->left)), old(_dryad_S2#9, *((x0#5->left))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(x0#5, ^b_node)) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x0#5)), @_vcc_ptr_eq_pure(*((x0#5->right)), old(_dryad_S2#9, *((x0#5->right))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(x0#5, ^b_node)) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S2#9, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, x0#5)), ==(*((x0#5->key)), old(_dryad_S2#9, *((x0#5->key))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(x0#5, ^b_node)) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(x0#5, ^b_node)) == $rd_inv(_dryad_S2#9, b_node.key, $phys_ptr_cast(x0#5, ^b_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xl#4)), @_vcc_ptr_eq_pure(*((xl#4->left)), old(_dryad_S2#9, *((xl#4->left))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(xl#4, ^b_node)) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xl#4)), @_vcc_ptr_eq_pure(*((xl#4->right)), old(_dryad_S2#9, *((xl#4->right))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(xl#4, ^b_node)) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S2#9, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xl#4)), ==(*((xl#4->key)), old(_dryad_S2#9, *((xl#4->key))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(xl#4, ^b_node)) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node)) == $rd_inv(_dryad_S2#9, b_node.key, $phys_ptr_cast(xl#4, ^b_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xr#3)), @_vcc_ptr_eq_pure(*((xr#3->left)), old(_dryad_S2#9, *((xr#3->left))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(xr#3, ^b_node)) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xr#3)), @_vcc_ptr_eq_pure(*((xr#3->right)), old(_dryad_S2#9, *((xr#3->right))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(xr#3, ^b_node)) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S2#9, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, xr#3)), ==(*((xr#3->key)), old(_dryad_S2#9, *((xr#3->key))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(xr#3, ^b_node)) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node)) == $rd_inv(_dryad_S2#9, b_node.key, $phys_ptr_cast(xr#3, ^b_node));
            // assume ==>(!(@_vcc_ptr_eq_pure(x, r#2)), @_vcc_ptr_eq_pure(*((r#2->left)), old(_dryad_S2#9, *((r#2->left))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(r#2, ^b_node)) ==> $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S2#9, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, r#2)), @_vcc_ptr_eq_pure(*((r#2->right)), old(_dryad_S2#9, *((r#2->right))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(r#2, ^b_node)) ==> $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node) == $rd_phys_ptr(_dryad_S2#9, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node);
            // assume ==>(!(@_vcc_ptr_eq_pure(x, r#2)), ==(*((r#2->key)), old(_dryad_S2#9, *((r#2->key))))); 
            assume !($phys_ptr_cast(P#x, ^b_node) == $phys_ptr_cast(r#2, ^b_node)) ==> $rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node)) == $rd_inv(_dryad_S2#9, b_node.key, $phys_ptr_cast(r#2, ^b_node));
            // assume ==>(@_vcc_ptr_neq_null(x1#6), ==(bst(x1#6), &&(&&(&&(&&(&&(&&(&&(bst(*((x1#6->left))), bst(*((x1#6->right)))), unchecked!(@_vcc_oset_in(x1#6, @_vcc_oset_union(bst_reach(*((x1#6->left))), bst_reach(*((x1#6->right))))))), unchecked!(@_vcc_intset_in(*((x1#6->key)), @_vcc_intset_union(bst_keys(*((x1#6->left))), bst_keys(*((x1#6->right))))))), @_vcc_oset_disjoint(bst_reach(*((x1#6->left))), bst_reach(*((x1#6->right))))), @_vcc_intset_disjoint(bst_keys(*((x1#6->left))), bst_keys(*((x1#6->right))))), @_vcc_intset_lt_one2(bst_keys(*((x1#6->left))), *((x1#6->key)))), @_vcc_intset_lt_one1(*((x1#6->key)), bst_keys(*((x1#6->right))))))); 
            assume $non_null($phys_ptr_cast(x1#6, ^b_node)) ==> F#bst($s, $phys_ptr_cast(x1#6, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(x1#6, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(x1#6, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(x1#6, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(x1#6, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x1#6), ==(bst_reach(x1#6), @_vcc_oset_union(@_vcc_oset_singleton(x1#6), @_vcc_oset_union(bst_reach(*((x1#6->left))), bst_reach(*((x1#6->right))))))); 
            assume $non_null($phys_ptr_cast(x1#6, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(x1#6, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(x1#6, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x1#6), ==(bst_keys(x1#6), @_vcc_intset_union(@_vcc_intset_singleton(*((x1#6->key))), @_vcc_intset_union(bst_keys(*((x1#6->left))), bst_keys(*((x1#6->right))))))); 
            assume $non_null($phys_ptr_cast(x1#6, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(x1#6, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(x1#6, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x1#6, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x1#6, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0#5), ==(bst(x0#5), &&(&&(&&(&&(&&(&&(&&(bst(*((x0#5->left))), bst(*((x0#5->right)))), unchecked!(@_vcc_oset_in(x0#5, @_vcc_oset_union(bst_reach(*((x0#5->left))), bst_reach(*((x0#5->right))))))), unchecked!(@_vcc_intset_in(*((x0#5->key)), @_vcc_intset_union(bst_keys(*((x0#5->left))), bst_keys(*((x0#5->right))))))), @_vcc_oset_disjoint(bst_reach(*((x0#5->left))), bst_reach(*((x0#5->right))))), @_vcc_intset_disjoint(bst_keys(*((x0#5->left))), bst_keys(*((x0#5->right))))), @_vcc_intset_lt_one2(bst_keys(*((x0#5->left))), *((x0#5->key)))), @_vcc_intset_lt_one1(*((x0#5->key)), bst_keys(*((x0#5->right))))))); 
            assume $non_null($phys_ptr_cast(x0#5, ^b_node)) ==> F#bst($s, $phys_ptr_cast(x0#5, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(x0#5, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(x0#5, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(x0#5, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(x0#5, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0#5), ==(bst_reach(x0#5), @_vcc_oset_union(@_vcc_oset_singleton(x0#5), @_vcc_oset_union(bst_reach(*((x0#5->left))), bst_reach(*((x0#5->right))))))); 
            assume $non_null($phys_ptr_cast(x0#5, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(x0#5, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(x0#5, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x0#5), ==(bst_keys(x0#5), @_vcc_intset_union(@_vcc_intset_singleton(*((x0#5->key))), @_vcc_intset_union(bst_keys(*((x0#5->left))), bst_keys(*((x0#5->right))))))); 
            assume $non_null($phys_ptr_cast(x0#5, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(x0#5, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(x0#5, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(x0#5, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(x0#5, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl#4), ==(bst(xl#4), &&(&&(&&(&&(&&(&&(&&(bst(*((xl#4->left))), bst(*((xl#4->right)))), unchecked!(@_vcc_oset_in(xl#4, @_vcc_oset_union(bst_reach(*((xl#4->left))), bst_reach(*((xl#4->right))))))), unchecked!(@_vcc_intset_in(*((xl#4->key)), @_vcc_intset_union(bst_keys(*((xl#4->left))), bst_keys(*((xl#4->right))))))), @_vcc_oset_disjoint(bst_reach(*((xl#4->left))), bst_reach(*((xl#4->right))))), @_vcc_intset_disjoint(bst_keys(*((xl#4->left))), bst_keys(*((xl#4->right))))), @_vcc_intset_lt_one2(bst_keys(*((xl#4->left))), *((xl#4->key)))), @_vcc_intset_lt_one1(*((xl#4->key)), bst_keys(*((xl#4->right))))))); 
            assume $non_null($phys_ptr_cast(xl#4, ^b_node)) ==> F#bst($s, $phys_ptr_cast(xl#4, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(xl#4, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl#4), ==(bst_reach(xl#4), @_vcc_oset_union(@_vcc_oset_singleton(xl#4), @_vcc_oset_union(bst_reach(*((xl#4->left))), bst_reach(*((xl#4->right))))))); 
            assume $non_null($phys_ptr_cast(xl#4, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(xl#4, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(xl#4, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xl#4), ==(bst_keys(xl#4), @_vcc_intset_union(@_vcc_intset_singleton(*((xl#4->key))), @_vcc_intset_union(bst_keys(*((xl#4->left))), bst_keys(*((xl#4->right))))))); 
            assume $non_null($phys_ptr_cast(xl#4, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(xl#4, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(xl#4, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xl#4, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xl#4, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr#3), ==(bst(xr#3), &&(&&(&&(&&(&&(&&(&&(bst(*((xr#3->left))), bst(*((xr#3->right)))), unchecked!(@_vcc_oset_in(xr#3, @_vcc_oset_union(bst_reach(*((xr#3->left))), bst_reach(*((xr#3->right))))))), unchecked!(@_vcc_intset_in(*((xr#3->key)), @_vcc_intset_union(bst_keys(*((xr#3->left))), bst_keys(*((xr#3->right))))))), @_vcc_oset_disjoint(bst_reach(*((xr#3->left))), bst_reach(*((xr#3->right))))), @_vcc_intset_disjoint(bst_keys(*((xr#3->left))), bst_keys(*((xr#3->right))))), @_vcc_intset_lt_one2(bst_keys(*((xr#3->left))), *((xr#3->key)))), @_vcc_intset_lt_one1(*((xr#3->key)), bst_keys(*((xr#3->right))))))); 
            assume $non_null($phys_ptr_cast(xr#3, ^b_node)) ==> F#bst($s, $phys_ptr_cast(xr#3, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(xr#3, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr#3), ==(bst_reach(xr#3), @_vcc_oset_union(@_vcc_oset_singleton(xr#3), @_vcc_oset_union(bst_reach(*((xr#3->left))), bst_reach(*((xr#3->right))))))); 
            assume $non_null($phys_ptr_cast(xr#3, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(xr#3, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(xr#3, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(xr#3), ==(bst_keys(xr#3), @_vcc_intset_union(@_vcc_intset_singleton(*((xr#3->key))), @_vcc_intset_union(bst_keys(*((xr#3->left))), bst_keys(*((xr#3->right))))))); 
            assume $non_null($phys_ptr_cast(xr#3, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(xr#3, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(xr#3, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(xr#3, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(xr#3, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(r#2), ==(bst(r#2), &&(&&(&&(&&(&&(&&(&&(bst(*((r#2->left))), bst(*((r#2->right)))), unchecked!(@_vcc_oset_in(r#2, @_vcc_oset_union(bst_reach(*((r#2->left))), bst_reach(*((r#2->right))))))), unchecked!(@_vcc_intset_in(*((r#2->key)), @_vcc_intset_union(bst_keys(*((r#2->left))), bst_keys(*((r#2->right))))))), @_vcc_oset_disjoint(bst_reach(*((r#2->left))), bst_reach(*((r#2->right))))), @_vcc_intset_disjoint(bst_keys(*((r#2->left))), bst_keys(*((r#2->right))))), @_vcc_intset_lt_one2(bst_keys(*((r#2->left))), *((r#2->key)))), @_vcc_intset_lt_one1(*((r#2->key)), bst_keys(*((r#2->right))))))); 
            assume $non_null($phys_ptr_cast(r#2, ^b_node)) ==> F#bst($s, $phys_ptr_cast(r#2, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(r#2, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(r#2), ==(bst_reach(r#2), @_vcc_oset_union(@_vcc_oset_singleton(r#2), @_vcc_oset_union(bst_reach(*((r#2->left))), bst_reach(*((r#2->right))))))); 
            assume $non_null($phys_ptr_cast(r#2, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(r#2, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(r#2, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(r#2), ==(bst_keys(r#2), @_vcc_intset_union(@_vcc_intset_singleton(*((r#2->key))), @_vcc_intset_union(bst_keys(*((r#2->left))), bst_keys(*((r#2->right))))))); 
            assume $non_null($phys_ptr_cast(r#2, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(r#2, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst(x), &&(&&(&&(&&(&&(&&(&&(bst(*((x->left))), bst(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))), @_vcc_oset_disjoint(bst_reach(*((x->left))), bst_reach(*((x->right))))), @_vcc_intset_disjoint(bst_keys(*((x->left))), bst_keys(*((x->right))))), @_vcc_intset_lt_one2(bst_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst($s, $phys_ptr_cast(P#x, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(P#x, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(bst_reach(*((x->left))), bst_reach(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(P#x, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(x), ==(bst_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(bst_keys(*((x->left))), bst_keys(*((x->right))))))); 
            assume $non_null($phys_ptr_cast(P#x, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(P#x, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(P#x, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(P#x, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(P#x, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(r#2), ==(bst(r#2), &&(&&(&&(&&(&&(&&(&&(bst(*((r#2->left))), bst(*((r#2->right)))), unchecked!(@_vcc_oset_in(r#2, @_vcc_oset_union(bst_reach(*((r#2->left))), bst_reach(*((r#2->right))))))), unchecked!(@_vcc_intset_in(*((r#2->key)), @_vcc_intset_union(bst_keys(*((r#2->left))), bst_keys(*((r#2->right))))))), @_vcc_oset_disjoint(bst_reach(*((r#2->left))), bst_reach(*((r#2->right))))), @_vcc_intset_disjoint(bst_keys(*((r#2->left))), bst_keys(*((r#2->right))))), @_vcc_intset_lt_one2(bst_keys(*((r#2->left))), *((r#2->key)))), @_vcc_intset_lt_one1(*((r#2->key)), bst_keys(*((r#2->right))))))); 
            assume $non_null($phys_ptr_cast(r#2, ^b_node)) ==> F#bst($s, $phys_ptr_cast(r#2, ^b_node)) == (F#bst($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)) && F#bst($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node)) && !$oset_in($phys_ptr_cast(r#2, ^b_node), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node)))) && !$intset_in($rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node)), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node)))) && $oset_disjoint(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))) && $intset_disjoint(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))) && $intset_lt_one2(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), $rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node))) && $intset_lt_one1($rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(r#2), ==(bst_reach(r#2), @_vcc_oset_union(@_vcc_oset_singleton(r#2), @_vcc_oset_union(bst_reach(*((r#2->left))), bst_reach(*((r#2->right))))))); 
            assume $non_null($phys_ptr_cast(r#2, ^b_node)) ==> F#bst_reach($s, $phys_ptr_cast(r#2, ^b_node)) == $oset_union($oset_singleton($phys_ptr_cast(r#2, ^b_node)), $oset_union(F#bst_reach($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_reach($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))));
            // assume ==>(@_vcc_ptr_neq_null(r#2), ==(bst_keys(r#2), @_vcc_intset_union(@_vcc_intset_singleton(*((r#2->key))), @_vcc_intset_union(bst_keys(*((r#2->left))), bst_keys(*((r#2->right))))))); 
            assume $non_null($phys_ptr_cast(r#2, ^b_node)) ==> F#bst_keys($s, $phys_ptr_cast(r#2, ^b_node)) == $intset_union($intset_singleton($rd_inv($s, b_node.key, $phys_ptr_cast(r#2, ^b_node))), $intset_union(F#bst_keys($s, $rd_phys_ptr($s, b_node.left, $phys_ptr_cast(r#2, ^b_node), ^b_node)), F#bst_keys($s, $rd_phys_ptr($s, b_node.right, $phys_ptr_cast(r#2, ^b_node), ^b_node))));
            // return x; 
            $result := $phys_ptr_cast(P#x, ^b_node);
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

const unique #tok$3^40.5: $token;

const unique #tok$3^38.17: $token;

const unique #tok$3^31.5: $token;

const unique #tok$3^29.17: $token;

const unique #tok$3^23.17: $token;

const unique #tok$4^0.0: $token;

const unique #file^?3Cno?20file?3E: $token;

axiom $file_name_is(4, #file^?3Cno?20file?3E);

const unique #tok$3^13.3: $token;

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Cbst?5Cbst?2Ddelete?2Drec.c: $token;

axiom $file_name_is(3, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Cbst?5Cbst?2Ddelete?2Drec.c);

const unique #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Cbst?5Cdryad_bst.h: $token;

axiom $file_name_is(2, #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Cbst?5Cdryad_bst.h);

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?2Dbin?5CHeaders?5Cvccp.h: $token;

axiom $file_name_is(1, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?2Dbin?5CHeaders?5Cvccp.h);

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^b_node);

