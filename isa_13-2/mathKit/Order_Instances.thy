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

theory Order_Instances 
  
imports
  Order_Morphism

begin

section {* Axclass matters *}

text {*

We introduce some useful mechanism for discussing orders at the type level.

*}

notation (zed)
  less_eq  ("\<opleT>") and
  less ("\<opltT>")

interpretation type_po: Order_Locale.partial_order "\<univ>-['a::order]" "\<opleT>-['a::order]"
  apply (insert default_po [of "\<univ>-['a::order]"])
  apply (simp add: default_order_def subset_order_def op2rel_def rel2op_def)
  done

interpretation type_order: Order_Locale.order "\<univ>-['a::linorder]" "\<opleT>-['a::linorder]"
  apply (insert default_order [of "\<univ>-['b::linorder]"])
  apply (simp add: default_order_def subset_order_def op2rel_def rel2op_def)
  done

lemma derefl_eq_less:
  "derefl \<opleT>-['a::order] = \<opltT>"
  apply (intro ext)
  apply (simp add: less_le)
  done

section {* Booleans *}

instance
  bool :: linorder
proof (intro_classes, unfold le_bool_def less_bool_def derefl_def)
  fix 
    x::"\<bool>" and 
    y::"\<bool>"
  show 
      "(x \<Rightarrow> y) \<or> (y \<Rightarrow> x)"
    by (auto)
qed

section {* The unit type *}

instantiation 
  unit :: linorder
begin

definition
  less_eq_unit_def: "\<opleT>-[unit] \<defs> (\<olambda> x y \<bullet> True)"

definition
  less_unit_def: "\<opltT>-[unit] \<defs> derefl \<opleT>"

instance
  by (intro_classes, auto simp add: less_eq_unit_def less_unit_def)

end

section {* Products *}

text {*

The natural order on a product of ordered sets
is the conjunction of the component orders.

Actually 

*}

definition
  product_order :: "['a orderT, 'b orderT] \<rightarrow> ('a \<times> 'b) orderT"
where
  product_order_def: "product_order BS_leq_d_1 BS_leq_d_2 \<defs> (\<olambda> (x_d_1, x_d_2) (y_d_1, y_d_2) \<bullet> \<^infopa>{:x_d_1:}{:BS_leq_d_1:}{:y_d_1:} \<and> \<^infopa>{:x_d_2:}{:BS_leq_d_2:}{:y_d_2:})"

notation (zed)
  product_order ("\<^prodord>{:_:}{:_:}")


instantiation
  prod :: (ord, ord) ord
begin

definition
  less_eq_prod_def: "\<opleT>-[('a::ord) \<times> ('b::ord)] \<defs> \<^prodord>{:\<opleT>-['a]:}{:\<opleT>-['b]:}"

definition
  less_prod_def: "\<opltT>-[('a::ord) \<times> ('b::ord)] \<defs> derefl \<opleT>"

instance
  by (intro_classes)

end

lemma le_prod_conv:
    "(x_d_1, y_d_1) \<le> (x_d_2, y_d_2) \<Leftrightarrow> x_d_1 \<le> x_d_2 \<and> y_d_1 \<le> y_d_2"
  by (simp add: less_eq_prod_def product_order_def)

text {*

The product order preserves order properties of the component spaces.

*}

lemma product_poI:
  assumes 
    a1: "\<^poset>{:X:}{:BS_leq_d_X:}" and a2: "\<^poset>{:Y:}{:BS_leq_d_Y:}"
  shows 
    "\<^poset>{:(X \<times> Y):}{:(\<^prodord>{:BS_leq_d_X:}{:BS_leq_d_Y:}):}"
proof (rule partial_orderI)
  from a1 interpret poX: partial_order X BS_leq_d_X
    by (simp_all add: Order_Locale.partial_order_def)
  from a2 interpret poY: partial_order Y BS_leq_d_Y
    by (simp_all add: Order_Locale.partial_order_def)
{
  from a1 a2 have 
        "X \<noteq> \<emptyset>" "Y \<noteq> \<emptyset>"
    by (simp_all add: partial_order_def')
  then show 
        "X \<times> Y \<noteq> \<emptyset>"
    by (auto)
next
  from a1 a2 have 
      "\<^oprel>{:BS_leq_d_X:} \<in> X \<zrel> X" "\<^oprel>{:BS_leq_d_Y:} \<in> Y \<zrel> Y"
    by (simp_all add: partial_order_def')
  then show 
      "\<^oprel>{:\<^prodord>{:BS_leq_d_X:}{:BS_leq_d_Y:}:} \<in> (X \<times> Y) \<zrel> (X \<times> Y)"
    apply (msafe(fspace))
    apply (auto simp add: product_order_def op2rel_def eind_def)
    done
next
  fix x 
  assume 
    b1: "x \<in> X \<times> Y"
  with a1 a2 show 
      "(\<^prodord>{:BS_leq_d_X:}{:BS_leq_d_Y:}) x x"
    by (auto simp add: product_order_def
      partial_order_conv reflexive_def reflexive_axioms_def)
next
  fix x y z
  assume 
    b1: "x \<in> X \<times> Y \<and> y \<in> X \<times> Y \<and> z \<in> X \<times> Y" and
    b2: "(\<^prodord>{:BS_leq_d_X:}{:BS_leq_d_Y:}) x y" and
    b3: "(\<^prodord>{:BS_leq_d_X:}{:BS_leq_d_Y:}) y z"
  then show 
      "(\<^prodord>{:BS_leq_d_X:}{:BS_leq_d_Y:}) x z"
    apply (auto simp add: product_order_def)
    apply (rule poX.trans [simplified, rule_format], mauto(inference))
    apply (rule poY.trans [simplified, rule_format], mauto(inference))
    done
(*J: note needed mauto(inference) here! *)
next
  fix x y
  assume 
    b1: "x \<in> X \<times> Y \<and> y \<in> X \<times> Y" and
    b2: "(\<^prodord>{:BS_leq_d_X:}{:BS_leq_d_Y:}) x y" and
    b3: "(\<^prodord>{:BS_leq_d_X:}{:BS_leq_d_Y:}) y x"
  then show 
      "x = y"
    apply (auto simp add: product_order_def)
    apply (rule poX.antisym [simplified, rule_format], msafe(inference))
    apply (rule poY.antisym [simplified, rule_format], msafe(inference))
    done
}
qed

lemma UNIV_prod:
    "\<univ>-['a \<times> 'b] = \<univ>-['a] \<times> \<univ>-['b]"
  by (auto)

instance
  prod :: (order, order) order
  apply (rule order_classI)
  apply (simp only: less_eq_prod_def UNIV_prod)
  apply (rule product_poI)
  apply (rule order_classD)
  apply (rule order_classD)
  apply (simp add: less_prod_def derefl_def)
  done



section {* Operator spaces *}

definition
  op_carrier :: "'b set \<rightarrow> ('a \<rightarrow> 'b) set"
where
  op_carrier_def: "op_carrier X \<defs> { f | range f \<subseteq> X }"

definition
  op_order :: "'b orderT \<rightarrow> ('a \<rightarrow> 'b) orderT"
where
  op_order_def: "op_order BS_leq \<defs> (\<olambda> f g \<bullet> (\<forall> a \<bullet> \<^infopa>{:f a:}{:BS_leq:}{:g a:}))"

syntax (zed)
  "_Order_Instances\<ZZ>op_carrier" :: "[type, logic] \<rightarrow> logic" ("\<^opset>{:_:}{:_:}")
  "_Order_Instances\<ZZ>op_order" :: "[type, logic] \<rightarrow> logic" ("\<^opord>{:_:}{:_:}")

translations
  "\<^opset>{:'a:}{:X:}" \<rightharpoonup> "(CONST Order_Instances.op_carrier X)::('a \<rightarrow> _) set"
  "\<^opord>{:'a:}{:BS_leq:}" \<rightharpoonup> "(CONST Order_Instances.op_order BS_leq)::('a \<rightarrow> _) orderT"

lemma (in partial_order) operator_poI:
    "\<^poset>{:\<^opset>{:'b:}{:X:}:}{:\<^opord>{:'b:}{:(op \<preceq>):}:}"
proof (rule partial_orderI)
  from non_empty show 
      "\<^opset>{:'b:}{:X:} \<noteq> \<emptyset>"
    by (auto simp add: op_carrier_def)
next
  from rel show 
      "\<^oprel>{:\<^opord>{:'b:}{:(op \<preceq>):}:} \<in> \<^opset>{:'b:}{:X:} \<zrel>\<^opset>{:'b:}{:X:}"
    by (auto simp add: rel_def op2rel_def op_carrier_def op_order_def eind_def) 
next
  fix f
  assume 
    "f \<in> \<^opset>{:'b:}{:X:}"
  with refl
  show 
      "\<^infopa>{:f:}{:\<^opord>{:'b:}{:(op \<preceq>):}:}{:f:}"
    by (auto simp add: op_carrier_def op_order_def) 
next
  fix f g h
  assume 
      "f \<in> \<^opset>{:'b:}{:X:} \<and> g \<in> \<^opset>{:'b:}{:X:} \<and> h \<in> \<^opset>{:'b:}{:X:}" and
      "\<^infopa>{:f:}{:\<^opord>{:'b:}{:(op \<preceq>):}:}{:g:}" "\<^infopa>{:g:}{:\<^opord>{:'b:}{:(op \<preceq>):}:}{:h:}" 
  then show 
      "\<^infopa>{:f:}{:\<^opord>{:'b:}{:(op \<preceq>):}:}{:h:}"
    apply (auto simp add: op_carrier_def op_order_def) 
    apply (rule transD)
    apply (auto)
    done
next
  fix f g
  assume 
      "f \<in> \<^opset>{:'b:}{:X:} \<and> g \<in> \<^opset>{:'b:}{:X:}" and
      "\<^infopa>{:f:}{:\<^opord>{:'b:}{:(op \<preceq>):}:}{:g:}" "\<^infopa>{:g:}{:\<^opord>{:'b:}{:(op \<preceq>):}:}{:f:}" 
  then show 
      "f = g"
    apply (intro ext)
    apply (auto simp add: op_carrier_def op_order_def) 
    apply (rule antisymD)
    apply (auto)
    done
qed

lemma UNIV_op:
    "\<univ>-['a \<rightarrow> 'b] = \<^opset>{:'a:}{:\<univ>-['b]:}"
  by (auto simp add: op_carrier_def)

lemma le_fun_conv:
    "f \<le> g \<Leftrightarrow> (\<forall> x \<bullet> f x \<le> g x)"
  by (auto simp add: le_fun_def op_order_def)

lemma fun_le:
    "f \<le> g \<turnstile> f x \<le> g x"
  by (auto simp add: le_fun_def op_order_def)

section {* Power sets *}

text {*

The power set of any set forms a partial order under the subset relation.

*}

definition
  pow_subset :: "'a set \<rightarrow> ['a set, 'a set] \<rightarrow> \<bool>"
where
  pow_subset_def: "pow_subset X A B \<defs> A \<subseteq> X \<and> B \<subseteq> X \<and> A \<subseteq> B"

syntax (xsymbols output)
  "_Order_Instances\<ZZ>pow_subset" :: "[logic, logic, logic] \<rightarrow> logic" ("_/ \<subseteq>\<^bsub>_\<^esub> _" [50, 1000, 51] 50)

syntax (zed)
  "_Order_Instances\<ZZ>pow_subset" :: "[logic, logic, logic] \<rightarrow> logic" ("_ \<^powsub>{:_:} _" [50, 1000, 51] 50)

translations
  "_Order_Instances\<ZZ>pow_subset A X B" \<rightleftharpoons> "(CONST Order_Instances.pow_subset) X A B"

interpretation pow_po: Order_Locale.partial_order "\<pset> X" "pow_subset X"
  apply (intro_locales)
  apply (simp_all add: carrier_def setrel_axioms_def reflexive_axioms_def transitive_axioms_def antisymmetric_axioms_def)
  apply (msafe(inference))
proof -
  show "\<pset> X \<noteq> \<emptyset>"
    by (auto)
next
  show "\<^oprel>{:pow_subset X:} \<in> \<pset> X \<zrel> \<pset> X"
    by (auto simp add: pow_subset_def op2rel_def rel_def)
next
  fix A 
  assume 
    b1: "A \<subseteq> X"
  then show 
      "A \<^powsub>{:X:} A"
    by (auto simp add: pow_subset_def)
next
  fix A B C
  assume 
    b1: "A \<subseteq> X" "B \<subseteq> X" "C \<subseteq> X" and
    b2: "A \<^powsub>{:X:} B" "B \<^powsub>{:X:} C" 
  then show 
      "A \<^powsub>{:X:} C"
    by (auto simp add: pow_subset_def)
next
  fix A B
  assume 
    b1: "A \<subseteq> X" "B \<subseteq> X" and
    b2: "A \<^powsub>{:X:} B" "B \<^powsub>{:X:} A" 
  then show 
      "A = B"
    by (auto simp add: pow_subset_def)
qed

section {* Dual spaces *}

text {*

The ordering on the dual space is the reverse of the ordering on the
original space.

*}

definition
  dual_carrier :: "'a set \<rightarrow> 'a dual set"
where
  dual_carrier_def: "dual_carrier X \<defs> { x | x \<in> X \<bullet> \<^adual>{:x:} }"

definition
  dual_order :: "'a orderT \<rightarrow> 'a dual orderT"
where
  dual_order_def: "dual_order BS_leq \<defs> (\<olambda> a b \<bullet> \<^infopa>{:\<^rdual>{:b:}:}{:BS_leq:}{:\<^rdual>{:a:}:})"

notation (xsymbols output)
  dual_carrier ("_\<^isup>\<circ>" [999] 1000) and
  dual_order ("_\<^isup>\<circ>" [999] 1000)

notation (zed)
  dual_carrier ("_\<dualset>" [999] 1000) and
  dual_order ("_\<dualord>" [999] 1000)

lemma (in partial_order) dual_poI:
  "\<^poset>{:X\<dualset>:}{:(op \<preceq>)\<dualord>:}"
proof (rule partial_orderI)
  from non_empty show "X\<dualset> \<noteq> \<emptyset>"
    by (auto simp add: dual_carrier_def)
next
  show "\<^oprel>{:(op \<preceq>)\<dualord>:} \<in> X\<dualset> \<zrel> X\<dualset>"
    apply (auto dest: relD1 relD2 simp add: rel_def op2rel_def dual_carrier_def dual_order_def type_definition.Rep_inverse [TDINST dual])
    apply (intro exI conjI)
    apply (rule type_definition.Rep_inverse [TDINST dual, symmetric])
    apply (rule relD2)
    apply (assumption)
    apply (intro exI conjI)
    apply (rule type_definition.Rep_inverse [TDINST dual, symmetric])
    apply (rule relD1)
    apply (assumption)
    done
next
  fix a
  assume 
      "a \<in> X\<dualset>"
  with refl show 
      "\<^infopa>{:a:}{:(op \<preceq>)\<dualord>:}{:a:}"
    by (auto simp add: dual_carrier_def dual_order_def Abs_dual_inverse2)
next
  fix a b c
  assume "a \<in> X\<dualset> \<and> b \<in> X\<dualset> \<and> c \<in> X\<dualset>" and
    "\<^infopa>{:a:}{:(op \<preceq>)\<dualord>:}{:b:}" "\<^infopa>{:b:}{:(op \<preceq>)\<dualord>:}{:c:}"
  then show "\<^infopa>{:a:}{:(op \<preceq>)\<dualord>:}{:c:}"
    apply (auto simp add: dual_carrier_def dual_order_def Abs_dual_inverse2)
    apply (rule transD)
    apply (assumption+)
    done
next
  fix a b
  assume 
      "a \<in> X\<dualset> \<and> b \<in> X\<dualset>" and
      "\<^infopa>{:a:}{:(op \<preceq>)\<dualord>:}{:b:}" "\<^infopa>{:b:}{:(op \<preceq>)\<dualord>:}{:a:}"
  then show 
      "a = b"
    apply (auto simp add: dual_carrier_def dual_order_def Abs_dual_inverse2 Abs_dual_inject Abs_dual)
    apply (rule antisymD)
    apply (assumption+)
    done
qed

instantiation
  dual :: (ord) ord
begin

definition
  less_eq_dual_def: "\<opleT>-[('a::ord) dual] \<defs> (op \<le>)\<dualord>"

definition
  less_dual_def: "\<opltT>-[('a::ord) dual] \<defs> derefl (op \<le>)"

instance
  by (intro_classes)

end

lemma less_eq_dual_conv:
    "a \<le> b \<Leftrightarrow> \<^rdual>{:b:} \<le> \<^rdual>{:a:}"
  by (simp add: less_eq_dual_def dual_order_def)

text {*

The dual of an order is an order.

*}

lemma UNIV_dual:
    "\<univ> = \<univ>\<dualset>"
  apply (auto simp add: dual_carrier_def)
  apply (rule exI)
  apply (rule Rep_dual_inverse [symmetric])
  done

instance
  dual :: (order) order
  apply (rule order_classI)
  apply (simp add: less_eq_dual_def UNIV_dual)
  apply (rule partial_order.dual_poI)
  apply (rule order_classD)
  apply (simp add: less_dual_def derefl_def)
  done

text {*

The dual ordering induces the reverse order on the original type.

*}

lemma less_dual_conv:
    "(a::('a::order) dual) < b \<Leftrightarrow> \<^rdual>{:b:} < \<^rdual>{:a:}"
  by (auto simp add: less_dual_def less_eq_dual_conv dual_order_def derefl_def Abs_dual_inverse2 Abs_dual_inject Abs_dual order_less_le Rep_dual_inject)

lemma less_eq_dual_conv2:
    "\<^adual>{:(a::'a::order):} \<le> \<^adual>{:b:} \<Leftrightarrow> b \<le> a"
  by (simp add: less_eq_dual_def dual_order_def Abs_dual_inverse2)

lemma less_dual_conv2:
    "\<^adual>{:(a::'a::order):} < \<^adual>{:b:} \<Leftrightarrow> b < a"
  by (auto simp add: less_dual_def less_eq_dual_conv2 dual_order_def derefl_def Abs_dual_inverse2 Abs_dual_inject Abs_dual order_less_le)

definition
  dual_fun :: "('a \<rightarrow> 'b) \<rightarrow> ('a dual \<rightarrow> 'b)"
where
  dual_fun_def [simp]: "dual_fun \<defs> (\<olambda> f a \<bullet> (f \<^rdual>{:a:}))"

definition
  amono :: "(('a::order) \<rightarrow> ('b::order)) \<rightarrow> \<bool>"
where
  amono_def: "amono f \<defs> mono (dual_fun f)"

lemma amonoI:
  assumes 
    a1: "(\<And> A B \<bullet> B \<le> A \<turnstile> f A \<le> f B)"
  shows 
      "amono f"
  apply (unfold amono_def)
  apply (rule monoI)
  apply (simp add: le_fun_def ge_def)
  apply (rule a1)
  apply (simp add: less_eq_dual_def dual_order_def)
  done

lemma amonoI':
  assumes 
    a1: "(\<And> A B \<bullet> B \<le> A \<turnstile> f A \<le> f B)"
  shows 
      "amono f"
  apply (rule amonoI)
  apply (rule a1)
  apply (assumption)
  done

lemma amonoD:
  assumes 
    a1: "amono f" and 
    a2: "B \<le> A" 
  shows 
      "f A \<le> f B"
proof -
  from a2 have 
    b1:"\<^adual>{:A:} \<le> \<^adual>{:B:}"
    by (simp add: less_eq_dual_def dual_order_def Abs_dual_inverse2)
  from monoD [OF a1 [unfolded amono_def] b1] show 
      ?thesis
    by (simp add: Abs_dual_inverse2)
qed

lemma amonoD':
  assumes 
    a1: "amono f" and 
    a2: "B \<le> A" 
  shows 
      "f A \<le> f B"
  apply (rule amonoD [OF a1])
  using a1 a2
  apply (simp)
  done

lemma amono_mono_comp:
  assumes 
    a1: "amono f" and 
    a2: "mono g"
  shows 
      "amono (f \<circ> g)"
  using a1 a2
  by (auto intro!: amonoI dest!: monoD amonoD)

lemma mono_amono_comp:
  assumes 
    a1: "mono f" and 
    a2: "amono g"
  shows 
      "amono (f \<circ> g)"
  using a1 a2
  by (auto intro!: amonoI dest!: monoD amonoD)

lemma amono_amono_comp:
  assumes 
    a1: "amono f" and 
    a2: "amono g"
  shows 
      "mono (f \<circ> g)"
  using a1 a2
  by (auto intro!: monoI dest!: amonoD)

lemma (in order) dual_orderI:
    "\<^order>{:X\<dualset>:}{:(op \<preceq>)\<dualord>:}"
  apply (simp add: order_conva)
  apply (msafe(inference))
  apply (rule dual_poI)
  apply (simp add: dual_order_def dual_carrier_def)
  apply (msafe(inference))
  apply (simp add: Abs_dual_inverse2)
  apply (rule linD)
  apply (msafe(inference))
  done

instance
  dual :: (linorder) linorder
  apply (rule linorder_classI)
  apply (simp add: less_eq_dual_def UNIV_dual)
  apply (rule order.dual_orderI)
  apply (rule linorder_classD)
  apply (simp add: less_dual_def derefl_def)
  done



section {* The identity order *}

lemma id_poI: 
    "X \<noteq> \<emptyset> \<turnstile> \<^poset>{:X:}{:(\<^relop>{:(\<zid> X):}):}"
  apply (insert id_in_relI [of X])
  apply (rule partial_orderI)
  apply (simp_all add:  op2rel_def rel2op_def rel_id_def eind_def)
  done

definition
  extend_ord :: "['a set, ['a, 'a] \<rightarrow> \<bool>] \<rightarrow>  (['a, 'a] \<rightarrow> \<bool>)"
where
  extend_ord_def: "extend_ord Y BS_leq \<defs> \<^relop>{:\<^oprel>{:BS_leq:} \<union> \<zid> Y:}"

notation (zed)
  extend_ord ("\<extord>{:_:}{:_:}")

lemma (in partial_order) extend_ord_conv:
  assumes 
    a1: "X \<subseteq> Y"
  shows 
      "\<^infop>{:x:}{:\<extord>{:Y:}{:(op \<preceq>):}:}{:y:}
      \<Leftrightarrow> x \<in> Y \<and> x \<notin> X \<and> y = x \<or> x \<in> X \<and> y \<in> X \<and> \<^infop>{:x:}{:(op \<preceq>):}{:y:}"
proof -
  from rel reflD
  show 
      ?thesis
    apply (msafe(fspace))
    apply (simp add: extend_ord_def op2rel_def rel2op_def rel_id_def)
    apply (auto simp add: eind_def)
    done
qed

lemma id_ext_poI:
  assumes 
    a1: "\<^poset>{:X:}{:BS_leq:}" and 
    a2: "X \<subseteq> Y"
  shows 
      "\<^poset>{:Y:}{:\<extord>{:Y:}{:BS_leq:}:}"
proof -
  from a1 interpret partial_order "X" "BS_leq"
    by (simp_all add: Order_Locale.partial_order_def)
  show 
      ?thesis
  proof (rule partial_orderI)
    from non_empty a2 show 
        "Y \<noteq> \<emptyset>"
      by (auto)
  next
    from rel a2 show 
        "\<^oprel>{:\<extord>{:Y:}{:BS_leq:}:} \<in> Y \<zrel> Y"
      apply (msafe(fspace))
      apply (auto simp add: extend_ord_def op2rel_def rel2op_def rel_id_def eind_def)
      done
  next
    fix y 
    assume 
      b1: "y \<in> Y"
    with a2 show 
        "\<^infop>{:y:}{:\<extord>{:Y:}{:BS_leq:}:}{:y:}"
      by (auto simp add: extend_ord_def op2rel_def rel2op_def rel_id_def eind_def)
  next
    fix x y z 
    assume 
      b1: "x \<in> Y \<and> y \<in> Y \<and> z \<in> Y" and
      b2: "\<^infop>{:x:}{:\<extord>{:Y:}{:BS_leq:}:}{:y:}" and
      b3: "\<^infop>{:y:}{:\<extord>{:Y:}{:BS_leq:}:}{:z:}"
    with a2 show 
        "\<^infop>{:x:}{:\<extord>{:Y:}{:BS_leq:}:}{:z:}"
      apply (auto simp add: extend_ord_conv)
      apply (rule transD, assumption+) 
      apply (rule transD, assumption+) 
      done
  next
    fix x y 
    assume 
      b1: "x \<in> Y \<and> y \<in> Y" and
      b2: "\<^infop>{:x:}{:\<extord>{:Y:}{:BS_leq:}:}{:y:}" and
      b3: "\<^infop>{:y:}{:\<extord>{:Y:}{:BS_leq:}:}{:x:}"
     with a2 show 
        "x = y"
      apply (auto simp add: extend_ord_conv)
      apply (rule antisymD, assumption+) 
      done
  qed
qed




section {* Subset order on relational graphs *}

definition
  rel_subset :: "['a set, 'b set ] \<rightarrow> ['a \<leftrightarrow> 'b, 'a \<leftrightarrow> 'b] \<rightarrow> \<bool>"
where
  rel_subset_def: "rel_subset X Y \<defs> pow_subset (X \<times> Y)"

syntax (xsymbols output)
  "_Order_Instances\<ZZ>rel_subset" :: "[logic, logic, logic, logic] \<rightarrow> logic" ("_ \<subseteq>\<^bsub>_ \<leftrightarrow> _\<^esub> _" [50, 1000, 1000, 51] 50)

syntax (zed)
  "_Order_Instances\<ZZ>rel_subset" :: "[logic, logic, logic, logic] \<rightarrow> logic" ("_ \<^relsub>{:_:}{:_:} _")

translations
  "_Order_Instances\<ZZ>rel_subset r X Y s" \<rightleftharpoons> "CONST Order_Instances.rel_subset X Y r s"


interpretation rel_po: Order_Locale.partial_order "X \<zrel> Y" "rel_subset X Y"
  apply (intro_locales)
  apply (simp_all add: rel_subset_def rel_def)
  apply (simp_all only: 
          carrier_def setrel_axioms_def reflexive_axioms_def 
          transitive_axioms_def antisymmetric_axioms_def)
  apply (msafe(inference))
  apply (rule pow_po.non_empty)
  apply (rule pow_po.rel)
  apply (rule pow_po.reflD, assumption)
  apply (rule pow_po.transD, assumption+)
  apply (rule pow_po.antisymD, assumption+)
  done





section {* Result order on functional graphs *}

definition
  res_le :: "[['b, 'b] \<rightarrow> \<bool>, 'a \<leftrightarrow> 'b, 'a \<leftrightarrow> 'b] \<rightarrow> \<bool>"
where
  res_le_def: "res_le r f g \<defs> functional f \<and> functional g \<and> (\<forall> x | x \<in> \<zdom> g \<bullet> x \<in> \<zdom> f \<and> \<^infop>{:f\<cdot>x:}{:r:}{:g\<cdot>x:})"

definition
  def_res_le :: "['a \<leftrightarrow> ('b::ord), 'a \<leftrightarrow> 'b] \<rightarrow> \<bool>"
where
  def_res_le_def: "def_res_le f g \<defs> res_le (op \<le>) f g"

notation (zed)
  res_le ("\<^resle>{:_:}") and
  def_res_le ("_ \<dresle> _" [50,51] 50)


lemma def_res_le_conv: 
    "f \<dresle> g \<Leftrightarrow> functional f \<and> functional g \<and> (\<forall> x | x \<in> \<zdom> g \<bullet> x \<in> \<zdom> f \<and> f\<cdot>x \<le> g\<cdot>x)"
  by (simp add: def_res_le_def res_le_def)

lemma res_le_def':
    "\<^infop>{:f:}{:\<^resle>{:r:}:}{:g:} 
    \<Leftrightarrow> functional f \<and> functional g \<and> 
        (\<forall> x y | (x \<mapsto> y) \<in> g \<bullet> (\<exists> y' | (x \<mapsto> y') \<in> f \<bullet> \<^infop>{:y':}{:r:}{:y:}))"
  apply (unfold res_le_def)
  apply (mauto(wind))
  proof-
    fix x
    assume 
       b1: "functional f" and 
       b2: "functional g"
    have "(x \<in> \<zdom> g \<Rightarrow> x \<in> \<zdom> f \<and> r (f\<cdot>x) (g\<cdot>x)) = (\<forall> y \<bullet>  (x \<mapsto> y) \<in> g \<Rightarrow> x \<in> \<zdom> f \<and> r (f\<cdot>x) (g\<cdot>x))"
    by (simp add: Domain_iff)
    also have
    "... = (\<forall> y \<bullet> (x, y) \<in> g \<Rightarrow> (\<exists> y' \<bullet> (x, y') \<in> f \<and> r y' y))"
      apply (mauto(wind))
      apply (simp add: Domain_iff)
      apply (subst ex_simps')
      apply (mauto(wind))
    proof -
      fix y y' 
      assume 
        b3: "(x \<mapsto> y) \<in> g" and 
        b4: "(x \<mapsto> y') \<in> f"
      with b1 b2 show 
          "\<^infop>{:f\<cdot>x:}{:r:}{:g\<cdot>x:} \<Leftrightarrow> \<^infop>{:y':}{:r:}{:y:}"
        by (simp add: functional_beta)
    qed
    finally show 
      "(x \<in> \<zdom> g 
        \<Rightarrow> x \<in> \<zdom> f \<and> r (f\<cdot>x) (g\<cdot>x)) = (\<forall> y \<bullet> (x \<mapsto> y) \<in> g \<Rightarrow> (\<exists> y' \<bullet> r y' y \<and> (x \<mapsto> y') \<in> f))" 
    by (auto)
  qed

lemma functional_poI:
  assumes 
    a1: "\<^poset>{:\<univ>:}{:BS_leq:}"
  shows 
      "\<^poset>{:{f::'a \<leftrightarrow> 'b | functional f}:}{:\<^resle>{:BS_leq:}:}"
  apply (rule partial_orderI)
  apply (simp_all)
proof (msafe(inference))
  show 
      "(\<exists> f::'a \<leftrightarrow> 'b \<bullet> functional f)"
    apply (witness "\<glambda> (y::'a) \<bullet> \<arb>-['b]")
    apply (auto simp add: glambda_functional glambda_ran)
    done
next
  show 
      "\<^oprel>{:\<^resle>{:BS_leq:}:} \<in> {f | functional f} \<zrel> {f | functional f}"
    apply (msafe(fspace))
    apply (auto simp add: op2rel_def res_le_def)
    done
next
  fix f::"'a \<leftrightarrow> 'b" 
  assume 
    b1: "functional f"
  with a1 show 
      "\<^infop>{:f:}{:\<^resle>{:BS_leq:}:}{:f:}"
    by (simp add: res_le_def partial_order_def')
next
  fix f::"'a \<leftrightarrow> 'b" 
  assume 
    b1: "functional f"
  fix g::"'a \<leftrightarrow> 'b" 
  assume 
    b2: "functional g"
  fix h::"'a \<leftrightarrow> 'b" 
  assume 
    b3: "functional h"
  assume 
    b4: "\<^infop>{:f:}{:\<^resle>{:BS_leq:}:}{:g:}" and 
    b5: "\<^infop>{:g:}{:\<^resle>{:BS_leq:}:}{:h:}"
  show 
      "\<^infop>{:f:}{:\<^resle>{:BS_leq:}:}{:h:}"
    apply (simp add: res_le_def b1 b3)
    apply (msafe(inference))
  proof -
    fix x 
    assume 
      c1: "x \<in> \<zdom> h"
    with b4 b5 show 
        "x \<in> \<zdom> f"
      by (simp add: res_le_def)
    from a1 c1 b4 b5 show 
        "\<^infop>{:f\<cdot>x:}{:BS_leq:}{:h\<cdot>x:}"
      apply (intro transitive.transD [of "\<univ>" "BS_leq" "f\<cdot>x" "g\<cdot>x" "h\<cdot>x"])
      apply (auto simp add: partial_order_conv res_le_def)
      done
  qed
next
  fix f::"'a \<leftrightarrow> 'b" 
  assume 
    b1: "functional f"
  fix g::"'a \<leftrightarrow> 'b" 
  assume 
    b2: "functional g"
  assume 
    b3: "\<^infop>{:f:}{:\<^resle>{:BS_leq:}:}{:g:}" and 
    b4: "\<^infop>{:g:}{:\<^resle>{:BS_leq:}:}{:f:}"
  show 
      "f = g"
    apply (rule functional_eqI)
    apply (rule b1, rule b2)
  proof -
    from b3 b4 show 
      c1: "\<zdom> f = \<zdom> g"
      by (auto simp add: res_le_def)
    fix x 
    assume 
        "x \<in> \<zdom> f"
    with a1 b3 b4 c1 show 
        "f\<cdot>x = g\<cdot>x"
      apply (intro antisymmetric.antisymD [of "\<univ>" "BS_leq" "f\<cdot>x" "g\<cdot>x"])
      apply (simp_all add: partial_order_conv res_le_def)
      done
  qed
qed

lemma pfun_poI:
  fixes 
    X::"'a set" and 
    Y::"'b set"
  assumes 
    a1: "\<^poset>{:Y:}{:BS_leq:}"
  shows 
      "\<^poset>{:(X \<zpfun> Y):}{:(\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}):}"
proof -
  from a1 interpret a1: partial_order "Y" "BS_leq"
    by (simp_all add: Order_Locale.partial_order_def)
  show 
      ?thesis
  proof (rule partial_orderI, msafe(inference))
    show 
        "X \<zpfun> Y \<noteq> \<emptyset>"
      apply (simp add: fun_space_defs)
      apply (witness "\<emptyset>-['a \<times> 'b]")
      apply (auto)
      done
  next
    show 
        "\<^oprel>{:\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}:} \<in> (X \<zpfun> Y) \<zrel> (X \<zpfun> Y)"
      apply (msafe(fspace))
      apply (auto simp add: op2rel_def rel2op_def subset_order_def subset_def)
      done
  next
    fix f 
    assume 
      c1: "f \<in> X \<zpfun> Y"
    then show 
        "\<^infop>{:f:}{:\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}:}{:f:}"
      apply (simp add: res_le_def op2rel_def rel2op_def subset_order_def)
      apply (msafe(inference))
      apply (msafe(fspace))
    proof -
      fix x 
      assume 
          "x \<in> \<zdom> f"
      with c1 have 
          "f\<cdot>x \<in> Y" by (auto)
      with a1.refl show 
          "\<^infop>{:f\<cdot>x:}{:BS_leq:}{:f\<cdot>x:}"
        by (auto)
    qed
  next
    fix f g h 
    assume 
      c1: "f \<in> X \<zpfun> Y" " g \<in> X \<zpfun> Y" "h \<in> X \<zpfun> Y" and 
      c2: "\<^infop>{:f:}{:\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}:}{:g:}" and 
      c3: "\<^infop>{:g:}{:\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}:}{:h:}"
    from c1 show 
        "\<^infop>{:f:}{:\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}:}{:h:}"
      apply (simp add: res_le_def op2rel_def rel2op_def subset_order_def)
      apply (msafe(inference))
      apply (msafe(fspace))
    proof -
      fix x 
      assume 
        d1: "x \<in> \<zdom> h"
      with c3 have 
        d2: "x \<in> \<zdom> g"
        by (simp add: res_le_def op2rel_def rel2op_def subset_order_def)
      with c2 show 
        d3: "x \<in> \<zdom> f"
        by (simp add: res_le_def op2rel_def rel2op_def subset_order_def)
      from c2 d2 d3 have 
        d4: "\<^infop>{:f\<cdot>x:}{:BS_leq:}{:g\<cdot>x:}"
        by (auto simp add: res_le_def op2rel_def rel2op_def subset_order_def)
      from c3 d1 d2 have 
        d5: "\<^infop>{:g\<cdot>x:}{:BS_leq:}{:h\<cdot>x:}"
        by (auto simp add: res_le_def op2rel_def rel2op_def subset_order_def)
      from d4 d5 show 
          "\<^infop>{:f\<cdot>x:}{:BS_leq:}{:h\<cdot>x:}"
        by (rule a1.transD)
    qed
  next
    fix f g 
    assume 
      c1: "f \<in> X \<zpfun> Y" "g \<in> X \<zpfun> Y" and 
      c2: "\<^infop>{:f:}{:\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}:}{:g:}" and 
      c3: "\<^infop>{:g:}{:\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}:}{:f:}"
    show 
        "f = g"
      apply (rule functional_eqI)
      apply (rule c1 [THEN dr_pfunD1])
      apply (rule c1 [THEN dr_pfunD1])
    proof -
      from c2 c3 show 
        d1: "\<zdom> f = \<zdom> g"
        by (auto simp add: res_le_def op2rel_def rel2op_def subset_order_def)
      fix x 
      assume 
        d2: "x \<in> \<zdom> f"
      from d2 c2 d1 have 
        d3: "\<^infop>{:f\<cdot>x:}{:BS_leq:}{:g\<cdot>x:}"
        by (auto simp add: res_le_def op2rel_def rel2op_def subset_order_def)
      from d2 c3 d1 have 
        d4: "\<^infop>{:g\<cdot>x:}{:BS_leq:}{:f\<cdot>x:}"
        by (auto simp add: res_le_def op2rel_def rel2op_def subset_order_def)
      from d3 d4 show 
          "f\<cdot>x = g\<cdot>x"
        by (rule a1.antisymD)
    qed
  qed
qed

text {*

The result order specialises nicely to total functions.

*}

definition
  tfun_order :: "['a set, 'b set, ['b, 'b] \<rightarrow> \<bool>] \<rightarrow> (['a \<leftrightarrow> 'b, 'a \<leftrightarrow> 'b] \<rightarrow> \<bool>)"
where
  tfun_order_def: 
    "tfun_order X Y BS_leq_d_Y 
    \<defs> (\<olambda> f g \<bullet> 
        \<lch> f, g \<chIn> X \<ztfun> Y \<rch> \<and> 
        (\<forall> x | x \<in> X \<bullet> \<^infopa>{:f\<cdot>x:}{:BS_leq_d_Y:}{:g\<cdot>x:}))"

lemma tfun_res_le:
    "tfun_order X Y BS_leq = \<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<ztfun> Y):}"
  apply (auto simp add: tfun_order_def op2rel_def rel2op_def subset_order_def fun_eq_def res_le_def)
  apply (mauto(fspace))
  apply (auto)
  done

lemma tfun_poI:
  assumes 
    a1: "\<^poset>{:Y:}{:BS_leq:}"
  shows 
      "\<^poset>{:(X \<ztfun> Y):}{:(tfun_order X Y BS_leq):}"
proof -
  from a1 interpret a1: Order_Locale.partial_order "Y" "BS_leq"
    by (simp_all add: Order_Locale.partial_order_def)
  from a1 interpret 
    b1: Order_Locale.partial_order "X \<zpfun> Y" "\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}"
    by (rule pfun_poI)
  interpret 
    b2: Order_Locale.sub_partial_order 
          "X \<zpfun> Y" "\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}" "X \<ztfun> Y"
  proof (unfold_locales)
    from a1.non_empty obtain y where 
        "y \<in> Y" 
      by (auto)
    then show 
        "X \<ztfun> Y \<noteq> \<emptyset>"
      apply (simp add: nempty_conv)
      apply (witness "(\<glambda> x | x \<in> X \<bullet> y)")
      apply (rule glambda_tfun)
      apply (auto) 
      done
    show "X \<ztfun> Y \<subseteq> X \<zpfun> Y"
      by (auto)
  qed
  have 
      "\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<ztfun> Y):} 
      = \<^subord>{:\<^subord>{:\<^resle>{:BS_leq:}:}{:(X \<zpfun> Y):}:}{:(X \<ztfun> Y):}"
    by (auto simp add: op2rel_def rel2op_def subset_order_def fun_eq_def)
  then show 
      ?thesis
    apply (simp add: tfun_res_le)
    apply (rule b2.Y_poI)
    done
qed


section {* Strings *}

fun
  find_ind_raw :: "'a \<rightarrow> \<nat> \<rightarrow> 'a list \<rightarrow> \<nat> option"
where
  "find_ind_raw a n (x#xs) = \<if> a = x \<then> Some n \<else> find_ind_raw a (n+1) xs \<fi>"
| "find_ind_raw a n [] = None"

definition
  find_ind :: "'a \<rightarrow> 'a list \<rightarrow> \<nat> option"
where
  "find_ind a = find_ind_raw a 0"

lemma find_ind_raw_bound1:
  "(\<forall> n m \<bullet> find_ind_raw x n X = Some m \<Rightarrow> n \<le> m)"
  apply (induct "X")
  apply (simp)
proof -
  fix
    a X
  assume
    b1 [rule_format]: "(\<forall> n m \<bullet> find_ind_raw x n X = Some m \<Rightarrow> n \<le> m)"
  show
    "(\<forall> n m \<bullet> find_ind_raw x n (a#X) = Some m \<Rightarrow> n \<le> m)"
    apply (cases "x = a")
    apply (simp)
    apply (auto)
    apply (rule order_trans)
    apply (rule less_imp_le [OF lessI])
    apply (rule b1)
    apply (assumption)
    done
qed

lemma find_ind_raw_bound2:
  "(\<forall> n m \<bullet> Some m = find_ind_raw x n X \<Rightarrow> n \<le> m)"
  by (auto intro!: find_ind_raw_bound1 [rule_format])

lemmas
  find_ind_raw_bound = find_ind_raw_bound1 [rule_format] find_ind_raw_bound2 [rule_format]
 
lemma find_ind_raw_dom [rule_format]:
  "(\<forall> n \<bullet> find_ind_raw x n X \<noteq> None \<Leftrightarrow> x \<in> set X)"
  apply (induct "X")
  apply (auto)
  done

lemma find_ind_dom:
  "find_ind x X \<noteq> None \<Leftrightarrow> x \<in> set X"
  by (simp only: find_ind_def find_ind_raw_dom)

lemma find_ind_raw_inj [rule_format]:
  "(\<forall> n x | x \<in> set X \<bullet> (\<forall> y | y \<in> set X \<bullet> find_ind_raw x n X = find_ind_raw y n X \<Leftrightarrow> x = y))"
  apply (induct "X")
  apply (simp)
  apply (mauto(inference))
proof -
  fix
    a X n x y
  assume
    b1: "(\<forall> n x | x \<in> set X \<bullet> (\<forall> y | y \<in> set X \<bullet> find_ind_raw x n X = find_ind_raw y n X \<Leftrightarrow> x = y))" and
    b2: "x \<in> set (a#X)" "y \<in> set (a#X)" and
    b3: "find_ind_raw x n (a # X) = find_ind_raw y n (a # X)"
  from b3 show
    "x = y"
    apply (multi_cases "x = a" "y = a")
    using b1 [rule_format] b2
    apply (auto dest: find_ind_raw_bound)
    done
qed

context 
  enum

begin

definition
  enum_ord :: "'a \<rightarrow> 'a \<rightarrow> \<bool>"
where
  "enum_ord x y \<Leftrightarrow> the (find_ind x enum) \<le> the (find_ind y enum)"

lemma enum_ord_linear:
  "\<^order>{:\<univ>-['a]:}{:enum_ord:}"
  apply (intro orderI)
  apply (auto simp add: enum_ord_def find_ind_def rel_def)
proof -
  fix
    x y
  assume
    b1: "the (find_ind_raw y 0 enum) = the (find_ind_raw x 0 enum)"
  with in_enum [of "x"] in_enum [of "y"] have
    b2: "(find_ind_raw y 0 enum) = (find_ind_raw x 0 enum)"
    by (auto simp add: find_ind_dom [symmetric] find_ind_def)
  show
    "x = y"
    apply (rule find_ind_raw_inj [THEN iffD1])
    using in_enum [of "x"] in_enum [of "y"] b2 [symmetric]
    apply (auto)
    done
qed

end

instantiation 
  nibble :: ord

begin

definition
  less_eq_nibble_def: "\<opleT>-[nibble] \<defs> enum_ord"

definition
  less_nibble_def: "\<opltT>-[nibble] \<defs> derefl \<opleT>"

instance
  by (intro_classes)

end

instance
  nibble :: linorder
  apply (rule linorder_classI)
  apply (auto simp add: enum_ord_linear less_eq_nibble_def less_nibble_def)
  done

instantiation char :: ord

begin

definition
  less_eq_char_def: "\<opleT>-[char] \<defs> enum_ord"

definition
  less_char_def: "\<opltT>-[char] \<defs> derefl \<opleT>"

instance
  by (intro_classes)

end

instance
  char :: linorder
  apply (rule linorder_classI)
  apply (auto simp add: enum_ord_linear less_eq_char_def less_char_def)
  done

context
  ord

begin
  
fun
  lex_ord :: "['a list, 'a list] \<rightarrow> \<bool>"
where
  "lex_ord [] [] \<Leftrightarrow> \<True>"
| "lex_ord [] (y#Y) \<Leftrightarrow> \<True>"
| "lex_ord (x#X) [] \<Leftrightarrow> \<False>"
| "lex_ord (x#X) (y#Y) \<Leftrightarrow> x < y \<or> x = y \<and> lex_ord X Y"

end

lemma lex_ord_poI:
  "\<^poset>{:\<univ>-[(('a::order) list)]:}{:lex_ord:}"
  apply (intro partial_order_intros)
  apply (auto simp add: rel_def)
proof -
  fix
    x :: "'a list"
  show
    "lex_ord x x"
    apply (induct "x")
    apply (auto)
    done
next
  fix
    x :: "'a list" and  
    y :: "'a list"
  assume
    b1: "lex_ord x y" "lex_ord y x" 
  have
    "(\<forall> y \<bullet> lex_ord x y \<and> lex_ord y x \<Rightarrow> x = y)" (is "(\<forall> y \<bullet> ?P x y)")
    apply (induct "x")
    apply (intro allI)
  proof -
    fix
      y :: "'a list"
    show
      "lex_ord [] y \<and> lex_ord y [] \<Rightarrow> [] = y"
      apply (cases "y")
      apply (auto)
      done
  next
    apply_end (rule allI)
    fix 
      a :: "'a" and
      x :: "'a list" and
      y :: "'a list"
    assume
      c1 [rule_format]: "(\<forall> y \<bullet> lex_ord x y \<and> lex_ord y x \<Rightarrow> x = y)" 
    show
      "lex_ord (a#x) y \<and> lex_ord y (a#x) \<Rightarrow> (a#x) = y"
      apply (cases "y")
      apply (simp)
      apply (msafe(inference))
      apply (auto intro: c1 simp add: less_le)
      done
  qed
  with b1 show
    "x = y"
    by (auto)
next
  fix
    x :: "'a list" and  
    y :: "'a list" and  
    z :: "'a list"
  assume
    b1: "lex_ord x y" "lex_ord y z" 
  have
    "(\<forall> y z \<bullet> lex_ord x y \<and> lex_ord y z \<Rightarrow> lex_ord x z)" (is "(\<forall> y z \<bullet> ?P x y z)")
    apply (induct "x")
    apply (intro allI)
  proof -
    fix
      y :: "'a list" and  
      z :: "'a list"
    show
      "?P [] y z"
      apply (multi_cases "y" "z")
      apply (auto)
      done
  next
    apply_end (intro allI)
    fix
      a :: "'a" and  
      x :: "'a list" and  
      y :: "'a list" and  
      z :: "'a list"
    assume
      c1 [rule_format]: "(\<forall> y z \<bullet> ?P x y z)"
    show
      "?P (a#x) y z"
      apply (multi_cases "y" "z")
      apply (auto)
      apply (mauto(inference) melim!: notE mintro: less_trans c1)
      done
  qed
  with b1 show
    "lex_ord x z"
    by (auto)
qed

lemma lex_ord_orderI:
  "\<^order>{:\<univ>-[('a::linorder) list]:}{:lex_ord:}"
  apply (rule partial_order.orderIa)
  apply (rule lex_ord_poI)
  apply (simp)
proof -
  fix
    x :: "'a list" and  
    y :: "'a list"
  have
    "(\<forall> y \<bullet> lex_ord x y \<or> lex_ord y x)"
    apply (induct "x")
    apply (rule allI)  
  proof -
    fix
      y :: "'a list"
    show
      "lex_ord [] y \<or> lex_ord y []"
      apply (cases "y")
      apply (auto)
      done
  next
    apply_end (rule allI)  
    fix
      a :: "'a" and  
      x :: "'a list" and  
      y :: "'a list"
    assume
      c1 [rule_format]: "(\<forall> y \<bullet> lex_ord x y \<or> lex_ord y x)"
    show
      "lex_ord (a#x) y \<or> lex_ord y (a#x)"
      apply (cases "y")
      apply (simp)
      using c1
      apply (auto)
      done
  qed
  then show
    "lex_ord x y \<or> lex_ord y x"
    by (auto)
qed

instantiation String.literal :: ord

begin

definition
  less_eq_literal_def: "\<opleT>-[String.literal] = induce_ord explode lex_ord"

definition
  less_literal_def: "\<opltT>-[String.literal] = derefl \<opleT>"

instance
  by (intro_classes)

end

instance
  String.literal :: linorder
proof (rule epi_typedefs_linorder_classI [OF _ lex_ord_orderI less_eq_literal_def less_literal_def])
   interpret 
     litTD: type_definition explode STR \<univ>
     by (rule type_definition_literal)
   show
     "epi_type_definition explode STR"
     apply (rule epi_type_definition.intro)
     apply (rule surjI)
     apply (auto intro: litTD.Abs_inverse litTD.Rep_inverse)
     done
qed

end
