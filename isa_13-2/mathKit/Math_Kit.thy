(*********************************************************************** 
* HiVe theory files
* 
* Copyright (C) 2015 Commonwealth of Australia as represented by Defence Science and Technology 
* Group (DST Group)
* 
* All rights reserved.
*
* The HiVe theory files are free software: released for redistribution and use, and/or modification,
* under the BSD License, details of which can be found in the LICENSE file included in the 
* distribution. 
************************************************************************)

theory Math_Kit 
  imports
    Z_Toolkit 
(*J: 19/11/2015 Requires Multivariate_Analysis
    xCalculus 
*)
    xReal_Type
    xReal_Type_nonassoc
    Value_Cardinals
begin

instance
  nibble :: svcard
  by (rule data_svcardI, rule type_definition_nibble)

instantiation (* type: String.nibble *)
  String.nibble :: svaltype
begin

definition
  nibble_vinj_def: "\<vinj>-[nibble] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: nibble_vinj_def)
  done

end

instance
  char :: svcard
  by (rule data_svcardI, rule type_definition_char)

instantiation (* type: String.char *)
  String.char :: svaltype
begin

definition
  char_vinj_def: "\<vinj>-[char] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: char_vinj_def)
  done

end

instance
  sumbool :: svcard
  by (rule data_svcardI, rule type_definition_sumbool)

instantiation (* type: Extraction.sumbool *)
  Extraction.sumbool :: svaltype
begin

definition
  sumbool_vinj_def: "\<vinj>-[sumbool] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: sumbool_vinj_def)
  done

end

(*
instance
  quot :: ("{eqv, svcard}")svcard
  by (rule type_def_svcardI, rule type_definition_quot)

instance
  quot :: ("{eqv, svaltype}")vtype
  by (intro_classes)

defs (overloaded)
  quot_vinj_def: "\<vinj>-[('a::{eqv, svaltype}) quot] \<defs> scinj"

instance
  quot :: ("{eqv, svaltype}") svaltype
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: quot_vinj_def)
  done
*)

(*
instance
  fraction :: svcard
  by (rule type_def_svcardI, rule type_definition_fraction)

instance
  fraction :: vtype
  by (intro_classes)

defs (overloaded)
  fraction_vinj_def: "\<vinj>-[fraction] \<defs> scinj"

instance
  fraction :: svaltype
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: fraction_vinj_def)
  done
*)

instance
  rat :: svcard
  by (rule type_def_svcardI, rule type_definition_rat)

instantiation (* type: Rat.rat *)
  Rat.rat :: svaltype
begin

definition
  rat_vinj_def: "\<vinj>-[rat] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: rat_vinj_def)
  done

end

(*

instance
  preal :: svcard
  by (rule type_def_svcardI, rule type_definition_preal)

instantiation
  preal :: svaltype
begin

definition
  preal_vinj_def: "\<vinj>-[preal] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: preal_vinj_def)
  done

end

*)

instance
  real :: svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_real)
  done

instantiation (* type: RealDef.real *)
  Real.real :: svaltype
begin

definition
  real_vinj_def: "\<vinj>-[real] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: real_vinj_def)
  done

end

instance
  xreal :: svcard
  by (rule data_svcardI, rule type_definition_xreal)

instantiation (* type: xReal_Type.xreal *)
  xReal_Type.xreal :: svaltype
begin

definition
  xreal_vinj_def: "\<vinj>-[xreal] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: xreal_vinj_def)
  done

end

instance
  xreal_na :: svcard
  by (rule data_svcardI, rule type_definition_xreal_na)

instantiation (* type: Real_Type_nonassoc.xreal_na *)
  xReal_Type_nonassoc.xreal_na :: svaltype
begin

definition
  xreal_na_vinj_def: "\<vinj>-[xreal_na] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: xreal_na_vinj_def)
  done

end

instance
  dual :: (svcard) svcard
  by (rule type_def_svcardI, rule type_definition_dual)

instantiation (* type: Dual.dual *)
  dual :: (svaltype) svaltype
begin

definition
  dual_vinj_def: "\<vinj>-[('a::svaltype) dual] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: dual_vinj_def)
  done

end

(*
instance
  bag :: (svcard) svcard
  by (rule type_def_svcardI, rule type_definition_bag)

instance
  bag :: (svaltype) vtype
  by (intro_classes)

defs (overloaded)
  bag_vinj_def: "\<vinj>-[('a::svaltype) bag] \<defs> scinj"

instance
  bag :: (svaltype) svaltype
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: bag_vinj_def)
  done
*)

instance
  ordinal :: (svcard)svcard
  by (rule type_def_svcardI, rule type_definition_ordinal)

instantiation (* type: Ordinal.ordinal *)
  Ordinal.ordinal :: (svaltype)svaltype
begin

definition
  ordinal_vinj_def: "\<vinj>-[('a::svaltype)ordinal] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: ordinal_vinj_def)
  done

end

instance
  "term" :: svcard
  apply (rule data_svcardI)
  apply (rule type_definition_term)
  done

instantiation (* type: Code_Evaluation.term *)
  Code_Evaluation.term :: svaltype
begin

definition
  term_vinj_def: "\<vinj>-[term] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: term_vinj_def)
  done

end

instance
  natural :: svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_natural)
  done

instantiation (* type: Code_Numeral.code_numeral *)
  natural :: svaltype
begin

definition
  natural_vinj_def: "\<vinj>-[natural] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: natural_vinj_def)
  done

end

instance
  complex :: svcard
  apply (rule data_svcardI)
  apply (rule type_definition_complex)
  done

instantiation (* type: Complex.complex *)
  Complex.complex :: svaltype
begin

definition
  complex_vinj_def: "\<vinj>-[complex] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: complex_vinj_def)
  done

end

instance
  Datatype.node :: (svcard, svcard)svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_node)
  done

instantiation (* type: Datatype.node *)
  Datatype.node :: (svaltype, svaltype)svaltype
begin

definition
  Node_vinj_def: "\<vinj>-[('a::svaltype, 'b::svaltype)Datatype.node] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: Node_vinj_def)
  done

end

(*
instance
  Finite_Cartesian_Product.cart :: (svcard, "{finite, svcard}") svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_Cart)
  done

instantiation (* type: Finite_Cartesian_Product.cart *)
  Finite_Cartesian_Product.cart :: (svaltype, "{finite, svaltype}") svaltype
begin

definition
  Cart_vinj_def: "\<vinj>-[('a::svaltype, 'b::{finite, svaltype}) Finite_Cartesian_Product.cart] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: Cart_vinj_def)
  done

end
*)

instance
  Lazy_Sequence.lazy_sequence :: (svcard)svcard
  apply (rule data_svcardI)
  apply (rule type_definition_lazy_sequence)
  done

instantiation (* type: Lazy_Sequence.lazy_sequence *)
  Lazy_Sequence.lazy_sequence :: (svaltype)svaltype
begin

definition
  lazy_sequence_vinj_def: "\<vinj>-[('a::svaltype)Lazy_Sequence.lazy_sequence] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: lazy_sequence_vinj_def)
  done

end

(*
instance
  net :: (svcard)svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_net)
  done

instantiation (* type: Limits.net *)
  net :: (svaltype)svaltype
begin

definition
  net_vinj_def: "\<vinj>-[('a::svaltype)net] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: net_vinj_def)
  done

end

instance
  bit0 :: ("{finite, svcard}")svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_bit0)
  done

instantiation (* type: Numeral_Type.bit0 *)
  Numeral_Type.bit0 :: ("{finite, svaltype}")svaltype
begin

definition
  bit0_vinj_def: "\<vinj>-[('a::{finite, svaltype})bit0] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: bit0_vinj_def)
  done

end

instance
  bit1 :: ("{finite, svcard}")svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_bit1)
  done

instantiation (* type: Numeral_Type.bit1 *)
  Numeral_Type.bit1 :: ("{finite, svaltype}")svaltype
begin

definition
  bit1_vinj_def: "\<vinj>-[('a::{finite, svaltype})bit1] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: bit1_vinj_def)
  done

end

instance
  num0 :: svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_num0)
  done

instantiation (* type: Numeral_Type.num0 *)
  Numeral_Type.num0 :: svaltype
begin

definition
  num0_vinj_def: "\<vinj>-[num0] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: num0_vinj_def)
  done

end

instance
  num1 :: svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_num1)
  done

instantiation (* type: Numeral_Type.num1 *)
  Numeral_Type.num1 :: svaltype
begin

definition
  num1_vinj_def: "\<vinj>-[num1] \<defs> scinj"

instance
  apply (intro_classes)
  apply (unfold num1_vinj_def)
  apply (rule scinj_inj)
  apply (rule scinj_bound_inj)
  done

end
*)

instance
  Predicate.pred :: (svcard)svcard
  apply (rule data_svcardI)
  apply (rule type_definition_pred)
  done

instantiation (* type: Predicate.pred *)
  Predicate.pred :: (svaltype)svaltype
begin

definition
  pred_vinj_def: "\<vinj>-[('a::svaltype)Predicate.pred] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: pred_vinj_def)
  done

end

instance
  Predicate.seq :: (svcard)svcard
  apply (rule data_svcardI)
  apply (rule type_definition_seq)
  done

instantiation (* type: Predicate.seq *)
  Predicate.seq :: (svaltype)svaltype
begin

definition
  seq_vinj_def: "\<vinj>-[('a::svaltype)Predicate.seq] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: seq_vinj_def)
  done

end

instance
  Record.tuple_isomorphism :: (svcard, svcard, svcard)svcard
  apply (rule data_svcardI)
  apply (rule type_definition_tuple_isomorphism)
  done

instantiation (* type: Record.tuple_isomorphism *)
  Record.tuple_isomorphism :: (svaltype, svaltype, svaltype)svaltype
begin

definition
  tuple_isomorphism_vinj_def: "\<vinj>-[('a::svaltype, 'b::svaltype, 'c::svaltype)Record.tuple_isomorphism] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: tuple_isomorphism_vinj_def)
  done

end

instance
  SMT.pattern :: svcard
  apply (rule data_svcardI)
  apply (rule type_definition_pattern)
  done

instantiation (* type: SMT.pattern *)
  SMT.pattern :: svaltype
begin

definition
  pattern_vinj_def: "\<vinj>-[SMT.pattern] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: pattern_vinj_def)
  done

end

instance
  String.literal :: svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_literal)
  done

instantiation (* type: String.literal *)
  String.literal :: svaltype
begin

definition
  literal_vinj_def: "\<vinj>-[String.literal] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: literal_vinj_def)
  done

end

(*J: 19/11/2015 Requires Multivariate_Analysis
instance
  Topology_Euclidean_Space.topology :: (svcard)svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_topology)
  done

instantiation (* type: Numeral_Type.bit1 *)
  Topology_Euclidean_Space.topology :: (svaltype)svaltype
begin

definition
  topology_vinj_def: "\<vinj>-[('a::svaltype)Topology_Euclidean_Space.topology] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: topology_vinj_def)
  done

end
*)

instance
  Typerep.typerep :: svcard
  apply (rule data_svcardI)
  apply (rule type_definition_typerep)
  done

instantiation (* type: Typerep.typerep *)
  Typerep.typerep :: svaltype
begin

definition
  typerep_vinj_def: "\<vinj>-[Typerep.typerep] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: typerep_vinj_def)
  done

end

instance
  Cartesian_Universe.CT :: svcard
  apply (rule data_svcardI)
  apply (rule type_definition_CT)
  done

instantiation (* type: Cartesian_Universe.CT *)
  Cartesian_Universe.CT :: svaltype
begin

definition
  CT_vinj_def: "\<vinj>-[Cartesian_Universe.CT] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: CT_vinj_def)
  done

end


instance
  Enum.finite_1 :: svcard
  apply (rule data_svcardI)
  apply (rule type_definition_finite_1)
  done

instantiation (* type: Enum.finite_1 *)
  Enum.finite_1 :: svaltype
begin

definition
  finite_1_vinj_def: "\<vinj>-[Enum.finite_1] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: finite_1_vinj_def)
  done

end

instance
  Enum.finite_2 :: svcard
  apply (rule data_svcardI)
  apply (rule type_definition_finite_2)
  done

instantiation (* type: Enum.finite_2 *)
  Enum.finite_2 :: svaltype
begin

definition
  finite_2_vinj_def: "\<vinj>-[Enum.finite_2] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: finite_2_vinj_def)
  done

end

instance
  Enum.finite_3 :: svcard
  apply (rule data_svcardI)
  apply (rule type_definition_finite_3)
  done

instantiation (* type: Enum.finite_3 *)
  Enum.finite_3 :: svaltype
begin

definition
  finite_3_vinj_def: "\<vinj>-[Enum.finite_3] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: finite_3_vinj_def)
  done

end

instance
  Enum.finite_4 :: svcard
  apply (rule data_svcardI)
  apply (rule type_definition_finite_4)
  done

instantiation (* type: Enum.finite_4 *)
  Enum.finite_4 :: svaltype
begin

definition
  finite_4_vinj_def: "\<vinj>-[Enum.finite_4] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: finite_4_vinj_def)
  done

end

instance
  Enum.finite_5 :: svcard
  apply (rule data_svcardI)
  apply (rule type_definition_finite_5)
  done

instantiation (* type: Enum.finite_5 *)
  Enum.finite_5 :: svaltype
begin

definition
  finite_5_vinj_def: "\<vinj>-[Enum.finite_5] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: finite_5_vinj_def)
  done

end

instance
  Equipotence.cardinal :: (svcard)svcard
  apply (rule type_def_svcardI)
  apply (rule type_definition_cardinal)
  done

instantiation (* type: Equipotence.cardinal *)
  Equipotence.cardinal :: (svaltype)svaltype
begin

definition
  cardinal_vinj_def: "\<vinj>-[('a::svaltype)Equipotence.cardinal] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: cardinal_vinj_def)
  done

end

instance
  Nitpick.word :: (svcard)svcard
  apply (rule data_svcardI)
  apply (rule type_definition_word)
  done

instantiation (* type: Nitpick.word *)
  Nitpick.word :: (svaltype)svaltype
begin

definition
  word_vinj_def: "\<vinj>-[('a::svaltype)Nitpick.word] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: word_vinj_def)
  done

end

instance
  Nitpick.pair_box :: (svcard, svcard)svcard
  apply (rule data_svcardI)
  apply (rule type_definition_pair_box)
  done

instantiation (* type: Nitpick.pair_box *)
  Nitpick.pair_box :: (svaltype,svaltype)svaltype
begin

definition
  pair_box_vinj_def: "\<vinj>-[('a::svaltype,'b::svaltype)Nitpick.pair_box] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: pair_box_vinj_def)
  done

end

instance
  Nitpick.fun_box :: (svcard, svcard)svcard
  apply (rule data_svcardI)
  apply (rule type_definition_fun_box)
  done

instantiation (* type: Nitpick.fun_box *)
  Nitpick.fun_box :: (svaltype,svaltype)svaltype
begin

definition
  fun_box_vinj_def: "\<vinj>-[('a::svaltype,'b::svaltype)Nitpick.fun_box] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: fun_box_vinj_def)
  done

end

(*
ML {*

val thy = @{theory};
val {tsig = ts, ...} = Sign.rep_sg thy;
val {log_types = lts, classes = (_, alg), ...} = Type.rep_tsig ts;
val arTab = Sorts.arities_of alg;
fun is_not_valtype t = (AList.lookup (op =) (Symtab.lookup_list arTab t) "Value_Types.valtype" = NONE);

map writeln (filter is_not_valtype lts);

*}
*)

end
