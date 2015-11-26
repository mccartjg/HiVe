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

theory 
  Order_Locale
  
imports 
  Z_Rel
  Z_Fun

begin

text {*

In considering the theory of ordered sets, we are faced with a modelling
choice as to whether to use a graph or operator model of the order
relation. The most convenient from algebraic considerations would be
the graph model, but the @{text "order"} class already makes use of the
operator model. Since the primary purpose of developing the theory is
to support instance reasoning on the @{text "order"} class, we are 
forced to adopt the operator model, leading occasionally to inelegant
type coercions.

Note: at some stage it might be worthwhile to re-implement relational
theory using operators.

Our development primarily follows Back and von Wright \cite{Back:Text},
with contributons from Davey and Priestley \cite{Davey:Lattice}.

*}

section {* Partially ordered sets *}

text {* 

Let @{text X} be a non-empty set and @{text "r"} a relation on 
@{text X}.

*}

locale carrier_sig =
  fixes 
    X :: "'a set"

locale carrier = carrier_sig +
  assumes
    non_empty: "X \<noteq> \<emptyset>"

notation (zed)
  carrier ("\<^carrier>{:_:}")

lemma (in carrier) carrier:
  "\<^carrier>{:X:}"
  by (simp add: carrier_def non_empty)

lemmas carrier_def' = carrier_def
lemmas carrier_intros = carrier_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]

type_synonym
  'a orderT = "['a, 'a] \<rightarrow> \<bool>"

text {*

We include the carrier set in setrel_sig so as to provide a context for
defining operators on relations
over carrier sets without bringing in the setrel conditions.
This approach allows the use of these operators in the various order contexts, 
without explicit reference to the context parameters.

*}

locale setrel_sig =
  fixes 
    X :: "'a set" and
    r :: "'a orderT"

begin
  
notation
  r (infixl "\<hookrightarrow>" 50)

end

locale setrel = 
  carrier + 
  setrel_sig +
assumes
  rel: "\<^oprel>{:(op \<hookrightarrow>):} \<in> X \<zrel> X"

begin

lemmas setrel_carrier = carrier

end

notation (zed)
  setrel ("\<^setrel>{:_:}{:_:}")

lemma (in setrel) setrel:
    "\<^setrel>{:X:}{:(op \<hookrightarrow>):}"
  by unfold_locales

lemmas setrel_def' = setrel_def [simplified setrel_axioms_def carrier_def' conj_ac']
lemmas setrel_intros = setrel_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]

lemma (in setrel) relD1:
    "x \<hookrightarrow> y \<turnstile> x \<in> X"
  apply (rule rel_dom_mem [OF rel])
  apply (simp add: op2rel_def)
  done

lemma (in setrel) relD2:
    "x \<hookrightarrow> y \<turnstile> y \<in> X"
  apply (rule rel_ran_mem [OF rel])
  apply (simp add: op2rel_def)
  done

lemma (in setrel) eq_trans1 [trans]:
    "\<lbrakk> x = y; y \<hookrightarrow> z \<rbrakk> \<turnstile> x \<hookrightarrow> z"
  by (simp)

lemma (in setrel) eq_trans2 [trans]:
    "\<lbrakk> x \<hookrightarrow> y; y = z \<rbrakk> \<turnstile> x \<hookrightarrow> z"
  by (simp)

text {*

We define the notions of relexive, transitive, symmetric and antisymmetric
relations as follows.

*}

locale reflexive = setrel + 
  assumes 
    refl: "(\<forall> x | x \<in> X \<bullet> x \<hookrightarrow> x)"

begin

lemmas reflexive_setrel = setrel

end


notation (zed)
  reflexive ("\<^reflexive>{:_:}{:_:}")

lemma (in reflexive) reflexive:
  "\<^reflexive>{:X:}{:r:}"
  by (unfold_locales)

lemmas reflexive_def' = reflexive_def [simplified reflexive_axioms_def setrel_def' conj_ac']
lemmas reflexive_intros = reflexive_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]

lemma (in reflexive) reflD:
  "x \<in> X \<turnstile> x \<hookrightarrow> x"
  apply (rule refl [rule_format])
  apply (auto)
  done

lemma (in reflexive) total_rel:
  "\<zdom> (\<^oprel>{:r:}) = X" and "\<zran> (\<^oprel>{:r:}) = X"
proof -
  from rel refl
  show "\<zdom> (\<^oprel>{:r:}) = X" and "\<zran> (\<^oprel>{:r:}) = X"
    by (auto simp add: rel_def Domain_def Range_def op2rel_def subset_def)
qed

locale transitive = 
  setrel +
  
assumes
    trans: "\<forall> x y z | \<lch> x, y, z \<chIn> X \<rch> \<bullet> x \<hookrightarrow> y \<and> y \<hookrightarrow> z \<Rightarrow> x \<hookrightarrow> z"

begin

lemmas transitive_setrel = setrel

end

notation (zed)
  transitive ("\<^transitive>{:_:}{:_:}")

lemma (in transitive) transitive:
  "\<^transitive>{:X:}{:r:}"
  by (unfold_locales)

lemmas transitive_def' = transitive_def [simplified setrel_def' transitive_axioms_def conj_ac']
lemmas transitive_intros = transitive_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]

lemma (in transitive) transD [trans]:
  "\<lbrakk> x \<hookrightarrow> y; y \<hookrightarrow> z \<rbrakk> \<turnstile> x \<hookrightarrow> z"
  apply (rule trans [rule_format])
  apply (auto simp add: relD1 relD2)
  done

locale symmetric = setrel +
  assumes
    sym: "\<forall> x y | \<lch> x, y \<chIn> X \<rch> \<bullet> x \<hookrightarrow> y \<Rightarrow> y \<hookrightarrow> x"

begin

lemmas symmetric_setrel = setrel

end

notation (zed)
  symmetric ("\<^symmetric>{:_:}{:_:}")

lemma (in symmetric) symmetric:
  "\<^symmetric>{:X:}{:r:}"
  by (unfold_locales)

lemmas symmetric_def' = symmetric_def [simplified setrel_def' symmetric_axioms_def conj_ac']
lemmas symmetric_intros = symmetric_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]

lemma (in symmetric) symD: 
  "x \<hookrightarrow> y \<turnstile> y \<hookrightarrow> x"
  apply (rule sym [rule_format])
  apply (auto simp add: relD1 relD2)
  done 

locale antisymmetric =
  setrel +
  
assumes
  antisym: "\<forall> x y | \<lch> x, y \<chIn> X \<rch> \<bullet> x \<hookrightarrow> y \<and> y \<hookrightarrow> x \<Rightarrow> x = y"

begin

lemmas antisymmetric_setrel = setrel

end

notation (zed)
  antisymmetric ("\<^antisymmetric>{:_:}{:_:}")

lemma (in antisymmetric) antisymmetric:
  "\<^antisymmetric>{:X:}{:r:}"
  by (unfold_locales)

lemmas antisymmetric_def' = antisymmetric_def [simplified setrel_def' antisymmetric_axioms_def conj_ac']
lemmas antisymmetric_intros = antisymmetric_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]

lemma (in antisymmetric) antisymD [trans]:
  "\<lbrakk> x \<hookrightarrow> y;  y \<hookrightarrow> x \<rbrakk> \<turnstile> x = y"
  apply (rule antisym [rule_format])
  apply (auto simp add: relD1 relD2)
  done

text {*

A relation is a preorder if it is reflexive and transitive.

*}

locale preorder = 
  reflexive + 
  transitive

begin

lemmas preorder_reflexive = reflexive

lemmas preorder_transitive = transitive

end

notation (zed)
  preorder ("\<^preorder>{:_:}{:_:}")

lemma (in preorder) preorder:
  "\<^preorder>{:X:}{:r:}"
  by (simp add: preorder_def reflexive_axioms transitive_axioms setrel_axioms carrier)

lemmas preorder_def' = preorder_def [simplified reflexive_def' transitive_def' conj_ac']
lemmas preorder_intros = preorder_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]

text {*

A preorder is an equivalence if it is also symmetric.

*}


locale equivalence =
    preorder X BS_sim +
    symmetric X BS_sim
  
for 
  X::"'a set" and 
  BS_sim::"'a orderT"

begin

notation
  BS_sim (infixl "\<sim>" 50) 

lemmas equivalence_preorder = preorder

lemmas equivalence_symmetric = symmetric

lemmas equivalence_reflexive = reflexive

lemmas equivalence_transitive = transitive

lemmas equivalence_setrel = setrel

end

notation (zed)
  equivalence ("\<^equivalence>{:_:}{:_:}")

lemma (in equivalence) equivalence:
  "\<^equivalence>{:X:}{:(op \<sim>):}"
  by (unfold_locales)

lemmas equivalence_def' = equivalence_def [simplified preorder_def' symmetric_def' conj_ac']
lemmas equivalence_intros = equivalence_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]

lemma equivalence_conv:
  "\<^equivalence>{:X:}{:BS_sim:} \<Leftrightarrow>  \<^reflexive>{:X:}{:BS_sim:} \<and> \<^transitive>{:X:}{:BS_sim:} \<and> \<^symmetric>{:X:}{:BS_sim:}"
  by (simp add: equivalence_def preorder_def)

text {*

A preorder is a partial order if it is also anti-symmetric.

*}

locale partial_order = 
  preorder +
  antisymmetric

begin

notation
  r (infixl "\<preceq>" 50)

lemmas partial_order_preorder = preorder

lemmas partial_order_antisymmetric = antisymmetric

lemmas partial_order_reflexive = reflexive

lemmas partial_order_transitive = transitive

lemmas partial_order_setrel = setrel

end

notation (zed)
  partial_order ("\<^poset>{:_:}{:_:}")

lemma (in partial_order) partial_order:
  "\<^poset>{:X:}{:(op \<preceq>):}"
  by (unfold_locales)

lemmas partial_order_def' = 
  partial_order_def [simplified preorder_def' antisymmetric_def' conj_ac']
lemmas partial_order_intros = 
  partial_order_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]


lemma partial_order_conv:
  "\<^poset>{:X:}{:BS_leq:} \<Leftrightarrow> \<^reflexive>{:X:}{:BS_leq:} \<and> \<^transitive>{:X:}{:BS_leq:} \<and> \<^antisymmetric>{:X:}{:BS_leq:}"
  by (auto simp add: partial_order_def preorder_def)

text {*

If every pair of elements are related, the relation is a linear order,
or simply order.

*}

locale linear = 
  setrel + 
  
assumes 
  lin: "\<forall> x y | \<lch> x, y \<chIn> X \<rch> \<bullet> x \<hookrightarrow> y \<or> y \<hookrightarrow> x"

begin

lemmas linear_setrel = setrel

end

notation (zed)
  linear ("\<^linear>{:_:}{:_:}")

lemma (in linear) linear:
  "\<^linear>{:X:}{:(op \<hookrightarrow>):}"
  by (unfold_locales)

lemmas linear_def' = linear_def [simplified linear_axioms_def setrel_def' conj_ac']
lemmas linear_intros = linear_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]

lemma (in linear) linD: 
  "\<lbrakk> x \<in> X; y \<in> X \<rbrakk> \<turnstile> x \<hookrightarrow> y \<or> y \<hookrightarrow> x"
  apply (rule lin [rule_format])
  apply (auto simp add: relD1)
  done

locale order = 
  partial_order + 
  linear

begin

lemmas order_partial_order = partial_order

lemmas order_linear = linear

lemmas order_antisymmetric = antisymmetric

lemmas order_reflexive = reflexive

lemmas order_transitive = transitive

lemmas order_setrel = setrel

end

notation (zed)
  order ("\<^order>{:_:}{:_:}")

lemma (in order) order:
  "\<^order>{:X:}{:op \<preceq>:}"
  by (unfold_locales)

lemmas order_def' = 
  order_def [simplified partial_order_def' linear_def' conj_ac']
lemmas order_intros = 
  order_def' [THEN meta_eq_to_obj_eq, THEN iffD2, simplified, rule_format]

lemma order_conv:
  "\<^order>{:X:}{:BS_leq:} \<Leftrightarrow> \<^reflexive>{:X:}{:BS_leq:} \<and> \<^transitive>{:X:}{:BS_leq:} \<and> \<^antisymmetric>{:X:}{:BS_leq:} \<and> \<^linear>{:X:}{:BS_leq:}"
  by (auto simp add: order_def partial_order_def preorder_def)

lemma order_conva:
  "\<^order>{:X:}{:BS_leq:} \<Leftrightarrow> \<^poset>{:X:}{:BS_leq:} \<and> (\<forall> x y | \<lch> x, y \<chIn> X \<rch> \<bullet> \<^infop>{:x:}{:BS_leq:}{:y:} \<or> \<^infop>{:y:}{:BS_leq:}{:x:})"
  by (auto simp add: order_def partial_order_def preorder_def linear_def' reflexive_def')

lemmas partial_orderI = partial_order_intros

lemmas orderI = order_intros

lemma (in partial_order) orderIa:
  "(\<And> x y \<bullet> \<lbrakk> x \<in> X; y \<in> X \<rbrakk> \<turnstile> x \<preceq> y \<or> y \<preceq> x) \<turnstile> \<^order>{:X:}{:op \<preceq>:}"
  apply (unfold_locales)
  apply (auto)
  done

section {* The converse order *}

text {*

The converse order is generated by the converse of the order relation.

*}

definition
  converse_rel :: "('a orderT) \<rightarrow> ('a orderT)"
where
  converse_rel_def: "converse_rel \<defs> (\<olambda> r x y \<bullet> \<^infopa>{:y:}{:r:}{:x:})"

notation (zed)
  converse_rel ("\<^convord>{:_:}")

context setrel_sig

begin

abbreviation
  converse_rel :: "'a orderT" (infixl "\<hookleftarrow>" 50)
where
  "(op \<hookleftarrow>) \<defs> \<^convord>{:(op \<hookrightarrow>):}"

end

context partial_order

begin

notation
  converse_rel (infixl "\<succeq>" 50)

lemma converse_poI:
    "\<^poset>{:X:}{:(op \<succeq>):}"
  apply (simp add: converse_rel_def)
  apply (rule partial_orderI)
  apply (rule non_empty)
  apply (insert rel)
  apply (simp add: op2rel_def rel_def subset_def)
  apply (rule reflD)
  apply (assumption)
  apply (rule antisymD)
  apply (assumption+)
  apply (rule transD)
  apply (assumption+)
  done

end

lemma (in order) converse_orderI:
  "\<^order>{:X:}{:op \<succeq>:}"
  apply (simp add: order_conva)
  apply (mauto(inference) mintro: converse_poI)
  apply (simp add: linear_def linear_axioms_def converse_rel_def)
  apply (rule linD)
  apply (assumption+)
  done

section {* On the relation between classes and locales *}

text {*

We demonstrate the useful connection between posets and the
@{text order} axclass, namely that you can demonstrate that a type
is an order, by showing that its universal set is a poset under the 
standard order.

*}

definition
  derefl :: "('a orderT) \<rightarrow> ('a orderT)"
where
  derefl_def [simp]: "derefl \<defs> (\<olambda> r x y \<bullet> \<^infopa>{:x:}{:r:}{:y:} \<and> x \<noteq> y)"

notation (zed)
  derefl ("\<derefl>")

theorem order_classI: 
  "\<lbrakk> \<^poset>{:\<univ>-[('a::ord)]:}{:(op \<le>):};
    ((op <)::('a::ord) orderT) = \<derefl> (op \<le>) \<rbrakk>
  \<turnstile> OFCLASS('a, order_class)"
proof -
  assume po: "\<^poset>{:\<univ>-['a]:}{:(op \<le>):}" and
    lt: "((op <)::'a orderT) = \<derefl> (op \<le>)"
  show "OFCLASS('a, order_class)"
  proof (intro_classes)
    fix x::'a
    from po show "x \<le> x"   
      apply (intro reflexive.reflD [of "\<univ>-['a]" "(op \<le>)" x])
      apply (auto simp add: partial_order_conv)
      done
  next
    fix x::'a and y::'a and z::'a
    assume a1: "x \<le> y" and a2: "y \<le> z"
    from po show "x \<le> z"
       apply (intro transitive.transD [of "\<univ>-['a]" "(op \<le>)", OF _ a1 a2])
       apply (simp add: partial_order_conv)
       done
  next
    fix x::'a and y::'a
    assume a1: "x \<le> y" and a2: "y \<le> x"
    from po show "x = y"
      apply (intro antisymmetric.antisymD [of "\<univ>-['a]" "(op \<le>)", OF _ a1 a2])
      apply (simp add: partial_order_conv)
      done
  next
    fix x::'a and y::'a
    from po show "x < y \<Leftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
      apply (simp add: lt derefl_def)
      apply (msafe(inference))
      apply (rule contrapos_nn, assumption)
      apply (intro antisymmetric.antisymD [of "\<univ>-['a]" "(op \<le>)"])
      apply (simp_all add: partial_order_conv)
      apply (rule contrapos_nn, assumption,simp)
    done
  qed
qed

lemma order_classD: "\<^poset>{:\<univ>-[('a::order)]:}{:(op \<le>):}"
  apply (rule partial_orderI)
  apply (auto intro: order_antisym order_trans simp add: op2rel_def rel_def)
  done

interpretation order_class: partial_order "\<univ>-[('a::order)]" "(op \<le>)"
  by (rule order_classD)

theorem linorder_classI: 
  "\<lbrakk> \<^order>{:\<univ>-[('a::ord)]:}{:(op \<le>):};
    ((op <)::('a::ord) orderT) = \<derefl> (op \<le>) \<rbrakk>
  \<turnstile> OFCLASS('a, linorder_class)"
proof -
  assume 
    ord: "\<^order>{:\<univ>-['a]:}{:(op \<le>):}" and
    lt: "((op <)::'a orderT) = \<derefl> (op \<le>)"
  show "OFCLASS('a, linorder_class)"
  proof (intro_classes)
    fix x::'a
    from ord show "x \<le> x"   
      apply (intro reflexive.reflD [of "\<univ>-['a]" "(op \<le>)" x])
      apply (auto simp add: order_conv)
      done
  next
    fix x::'a and y::'a and z::'a
    assume a1: "x \<le> y" and a2: "y \<le> z"
    from ord show "x \<le> z"
       apply (intro transitive.transD [of "\<univ>-['a]" "(op \<le>)", OF _ a1 a2])
       apply (simp add: order_conv)
       done
  next
    fix x::'a and y::'a
    assume a1: "x \<le> y" and a2: "y \<le> x"
    from ord show "x = y"
      apply (intro antisymmetric.antisymD [of "\<univ>-['a]" "(op \<le>)", OF _ a1 a2])
      apply (simp add: order_conv)
      done
  next 
    fix x::'a and y::'a
    from ord show "x \<le> y \<or> y \<le> x"
      apply (intro linear.linD [of "\<univ>-['a]" "(op \<le>)"])
      apply (auto simp add: order_conv)
      done
  next
    fix x::'a and y::'a
    from ord show "x < y \<Leftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
      apply (simp add: lt derefl_def)
      apply (msafe(inference))
      apply (rule contrapos_nn, assumption)
      apply (intro antisymmetric.antisymD [of "\<univ>-['a]" "(op \<le>)"])
      apply (simp_all add: order_conv)
      apply (rule contrapos_nn, assumption,simp)
    done
  qed
qed

lemma linorder_classI2:
  "\<^linear>{:\<univ>-[('a::order)]:}{:(op \<le>):}
  \<turnstile> OFCLASS('a::order, linorder_class)"
proof -
  assume lin: "\<^linear>{:\<univ>-['a]:}{:(op \<le>):}"
  show "OFCLASS('a, linorder_class)"
  proof (intro_classes)
    fix x::'a and y::'a
    from lin linear.linD [of "\<univ>-['a]" "(op \<le>)"]
    show "x \<le> y \<or> y \<le> x"
      by (auto)
  qed
qed

lemma linorder_classD: "\<^order>{:\<univ>-[('a::linorder)]:}{:(op \<le>):}"
  apply (rule partial_order.orderIa)
  apply (rule order_classD)
  apply (rule linorder_linear)
  done

interpretation linorder_class: order "\<univ>-[('a::linorder)]" "(op \<le>)"
  by (rule linorder_classD)

text {*

Of course, we are now left with the question of what has been gained
by converting the problem to the poset formalism. The answer to this
is that in the poset formalism we are better able to treat algebraic
concepts such as sub-orders, quotient orders, and order-morphisms and
that such notions are often critical to efficient demonstration of
poset instances.

*}

section {* Two orders *}

text {*

There are a number of occasions in which it is necessary to consider two orders
at once. To facilitate this we develop distinguished copies of the order hierachy.

*}

locale X_carrier =
  X: carrier X
for 
  X::"'a set"

locale Y_carrier =
  Y: carrier Y
for 
  Y::"'a set"

locale X_setrel =
  X: setrel X r
for 
  X::"'a set" and
  r::"'a orderT"

begin

notation
  r (infixl "\<hookrightarrow>\<^sub>X" 50) and
  converse_rel (infixl "\<hookleftarrow>\<^sub>X" 50)

end

sublocale X_setrel \<subseteq> X_carrier
  by (unfold_locales)

locale Y_setrel =
  Y: setrel Y s
for 
  Y::"'a set" and
  s::"'a orderT"

begin

notation
  s (infixl "\<hookrightarrow>\<^sub>Y" 50) and
  converse_rel (infixl "\<hookleftarrow>\<^sub>Y" 50)

end

sublocale Y_setrel \<subseteq> Y_carrier
  by (unfold_locales)

locale X_partial_order =
  X: partial_order X r
for 
  X::"'a set" and
  r::"'a orderT"

begin

notation
  r (infixl "\<preceq>\<^sub>X" 50)

end

sublocale X_partial_order \<subseteq> X_setrel
  by (unfold_locales)

locale Y_partial_order =
  Y: partial_order Y s
for 
  Y::"'a set" and
  s::"'a orderT"

begin

notation
  s (infixl "\<preceq>\<^sub>Y" 50)

end

sublocale Y_partial_order \<subseteq> Y_setrel
  by (unfold_locales)

locale X_order =
  X: order X r
for 
  X::"'a set" and
  r::"'a orderT"

sublocale X_order \<subseteq> X_partial_order
  by (unfold_locales)

locale Y_order =
  Y: order Y s
for 
  Y::"'a set" and
  s::"'a orderT"

sublocale Y_order \<subseteq> Y_partial_order
  by (unfold_locales)

section {* Sub-orders *}

text {*

We begin by considering the concept of sub-order. A sub-order is
just an order relation restricted to a sub-space. A sub-order
is also an order.

*}

definition
  subset_order :: "['a orderT, 'a set] \<rightarrow> 'a orderT"
where
  subset_order_def: "subset_order \<defs> (\<olambda> r Y \<bullet> \<^relop>{:(\<^oprel>{:r:} \<inter> (Y \<times> Y)):})"

notation (xsymbols output)
  subset_order ("_|\<^bsub>_\<^esub>")

notation (zed)
  subset_order ("\<^subord>{:_:}{:_:}")


lemma subset_order_conv:
  "\<^infopa>{:x:}{:\<^subord>{:BS_leq:}{:Y:}:}{:y:} \<Leftrightarrow> x \<in> Y \<and> y \<in> Y \<and> \<^infopa>{:x:}{:BS_leq:}{:y:}"
  by (auto simp add: subset_order_def op2rel_def rel2op_def)

locale sub_setrel = 
  X_setrel +
  Y_carrier +
assumes
  subset_Y: "Y \<subseteq> X"

begin

abbreviation
  Y_subset_order :: "'a orderT" (infixl "\<hookrightarrow>\<^sub>Y"50)
where
  "Y_subset_order \<defs> subset_order (op \<hookrightarrow>) Y"

end

sublocale sub_setrel \<subseteq> Y_setrel Y Y_subset_order
proof (unfold_locales)
  show
      "\<^oprel>{:Y_subset_order:} \<in> Y \<zrel> Y"
    by (auto simp add: rel_def subset_order_def op2rel_def rel2op_def)
qed

context sub_setrel

begin

lemmas X_setrel = X.setrel

lemmas Y_setrel = Y.setrel

end

text {*

Here we show that all of the order attributes are preserved by sub-orders.
There is the option of introducing subset relation variants for each of the
order attribute locales or of simply assuming the attribute in a 
@{text "sub_setrel"} theorem. The balance seems with the latter option, unless
the subset locale is likely to get significant use. Thus we develop subset locales
only for @{text "partial_order"} and @{text "order"}.

*}

lemma (in sub_setrel) sub_reflI:
  assumes
    a1: "\<^reflexive>{:X:}{:(op \<hookrightarrow>):}"
  shows
      "\<^reflexive>{:Y:}{:(op \<hookrightarrow>\<^sub>Y):}"
  apply (rule reflexive.intro)
  apply (rule Y_setrel)
  apply (auto simp add: reflexive_axioms_def)
proof -
  fix x 
  assume 
    "x \<in> Y"
  with reflexive.reflD [OF a1] subset_Y show 
      "x \<hookrightarrow>\<^sub>Y x"
    by (auto simp add: subset_order_def op2rel_def rel2op_def)
qed

lemma (in sub_setrel) sub_transI:
  assumes
    a1: "\<^transitive>{:X:}{:(op \<hookrightarrow>):}"
  shows
      "\<^transitive>{:Y:}{:(op \<hookrightarrow>\<^sub>Y):}"
  apply (rule transitive.intro)
  apply (rule Y_setrel)
  apply (auto intro: transitive.transD [OF a1] simp add: transitive_axioms_def subset_order_def op2rel_def rel2op_def)
  done

lemma (in sub_setrel) sub_antisymI:
  assumes
    a1: "\<^antisymmetric>{:X:}{:(op \<hookrightarrow>):}"
  shows
    "\<^antisymmetric>{:Y:}{:(op \<hookrightarrow>\<^sub>Y):}"
  apply (rule antisymmetric.intro)
  apply (rule Y_setrel)
  apply (auto intro: antisymmetric.antisymD [OF a1] simp add: antisymmetric_axioms_def subset_order_def op2rel_def rel2op_def)
  done

lemma (in sub_setrel) sub_linI:
  assumes
    a1: "\<^linear>{:X:}{:(op \<hookrightarrow>):}"
  shows
      "\<^linear>{:Y:}{:(op \<hookrightarrow>\<^sub>Y):}"
  apply (rule linear.intro)
  apply (rule Y_setrel)
  apply (simp add: linear_axioms_def subset_order_def op2rel_def rel2op_def)
  apply (msafe(inference))
  apply (rule linear.linD [OF a1])
  apply (auto intro: subset_Y [THEN subsetD])
  done

lemma (in sub_setrel) sub_preorderI:
  assumes
    a1: "\<^preorder>{:X:}{:(op \<hookrightarrow>):}"
  shows
      "\<^preorder>{:Y:}{:(op \<hookrightarrow>\<^sub>Y):}"
  using a1
  by (auto intro!: sub_reflI sub_transI simp add: preorder_def)

locale sub_partial_order =
  X_partial_order + 
  sub_setrel

sublocale sub_partial_order \<subseteq> Y_partial_order Y Y_subset_order
  using 
    sub_transI [OF X.transitive] 
    sub_reflI [OF X.reflexive]  
    sub_antisymI [OF X.antisymmetric]
  by (auto intro: Y_partial_order.intro partial_order.intro preorder.intro)

context sub_partial_order

begin

notation
  Y_subset_order (infixl "\<preceq>\<^sub>Y" 50)

lemmas X_reflI = X.reflexive

lemmas Y_reflI = Y.reflexive

lemmas X_transI = X.transitive

lemmas Y_transI = Y.transitive

lemmas X_antisymI = X.antisymmetric

lemmas Y_antisymI = Y.antisymmetric

lemmas X_poI = X.partial_order

lemmas Y_poI = Y.partial_order

end (* sub_partial_order *)

locale sub_order =
  X_order + 
  sub_partial_order

sublocale sub_order \<subseteq> Y_order Y Y_subset_order
  apply (unfold_locales)
  using 
    linear.linD [OF sub_linI [OF X.linear]] 
  apply (auto)
  done

context sub_order

begin

lemmas X_linI = X.linear

lemmas Y_linI = Y.linear

lemmas X_poI = X.partial_order

lemmas Y_poI = Y.partial_order

lemmas X_orderI = X.order

lemmas Y_orderI = Y.order

end (* sub_order *)

text {*

The sub-order construction can be used to determine a default ordering on
any subset of an ordered type.

*}

definition
  default_order :: "('a::ord) set \<rightarrow> 'a orderT"
where
  default_order_def: "default_order Y \<defs> \<^subord>{:(op \<le>):}{:Y:}"

lemma default_order_conv:
    "default_order Y x y \<Leftrightarrow> x \<in> Y \<and> y \<in> Y \<and> x \<le> y"
  by (auto simp add: default_order_def subset_order_conv)

lemma [simp]:
  assumes 
    a1: "x \<in> Y" "y \<in> Y"
  shows 
    "default_order Y x y \<Leftrightarrow> x \<le> y"
  using a1
  by (auto simp add: default_order_conv)

lemma default_po: 
  fixes 
    Y::"('a::order) set"
  assumes 
    a1: "Y \<noteq> \<emptyset>"
  shows 
    "\<^poset>{:Y:}{:(default_order Y):}"
proof -
  interpret 
    b1: sub_partial_order "\<univ>" "(op \<le>)" "Y"
    apply (unfold_locales)
    apply (auto simp add: a1)
    done
  from b1.Y_poI show 
      ?thesis
    by (auto simp add: default_order_def)
qed

locale po_carrier =
  carrier X
for
  X::"('a::order) set"

sublocale po_carrier \<subseteq> carrier
  by (unfold_locales)

sublocale po_carrier \<subseteq> partial_order X "(default_order X)"
  apply (rule default_po)
  apply (rule non_empty)
  done

text {*

The default order on any subset of a linearly ordered type is
a linear order.

*}

lemma default_order: 
  fixes 
    Y::"('a::linorder) set"
  assumes 
    a1: "Y \<noteq> \<emptyset>"
  shows 
    "\<^order>{:Y:}{:(default_order Y):}"
proof -
  interpret 
    b1: sub_order "\<univ>" "(op \<le>)" "Y"
    apply (unfold_locales)
    apply (auto simp add: a1)
    done
  from b1.Y_orderI show 
      ?thesis
    by (auto simp add: default_order_def)
qed

locale order_carrier =
  carrier X
for
  X::"('a::linorder) set"

sublocale order_carrier \<subseteq> carrier
  by (unfold_locales)

sublocale order_carrier \<subseteq> order X "(default_order X)"
  apply (rule default_order)
  apply (rule non_empty)
  done

section {* Chains *}

text {*

The term chain is synonym for ordered set, but the term tends to be used
when applying the properties of ordered sets in other areas of mathematics,
rather than when investigating ordered sets. As such we feel entitled to
co-opt the term to name a collection of objects that are well-ordered 
under the type-ordering.

*}

definition
  chain :: "('a::order) set \<rightarrow> \<bool> "
where
  chain_def: "chain X \<defs> order X (default_order X)"

lemma chain_conv: 
    "chain X \<Leftrightarrow> X \<noteq> \<emptyset> \<and> (\<forall> x y | x \<in> X \<and> y \<in> X \<bullet> x \<le> y \<or> y \<le> x)"
proof -
  have 
      "chain X 
      \<Leftrightarrow> \<^poset>{:X:}{:(default_order X):} \<and> (\<forall> x y | x \<in> X \<and> y \<in> X \<bullet> x \<le> y \<or> y \<le> x)" 
    by (auto simp add: chain_def order_conv partial_order_conv 
      linear_def linear_axioms_def subset_order_def default_order_def 
      reflexive_def op2rel_def rel2op_def)
  also have "\<dots> 
      \<Leftrightarrow> X \<noteq> \<emptyset> \<and> (\<forall> x y | x \<in> X \<and> y \<in> X \<bullet> x \<le> y \<or> y \<le> x)"
  proof (mauto(wind))
    show 
        "\<^poset>{:X:}{:(default_order X):} \<Leftrightarrow> X \<noteq> \<emptyset>"
      apply (msafe(inference))
      apply (rule carrier.non_empty [of X])
      apply (simp add: partial_order_conv reflexive_def' carrier_def')
      apply (simp add: default_po)
      done
  qed
  finally show 
      ?thesis 
    by this
qed

lemma chainI: 
    "\<lbrakk> X \<noteq> \<emptyset>; (\<And> x y \<bullet> \<lbrakk> x \<in> X; y \<in> X \<rbrakk> \<turnstile> x \<le> y \<or> y \<le> x) \<rbrakk>
    \<turnstile> chain X "
  by (auto simp add: chain_conv)

lemma chainE: 
    "\<lbrakk> chain X; x \<in> X; y \<in> X; x \<le> y \<turnstile> R; y \<le> x \<turnstile> R \<rbrakk> \<turnstile> R"
  by (auto simp add: chain_conv)

section {* Bounds *}


text {*

Suppose that @{text "X\<^bsub>BS_leq\<^esub>)"} is a poset and that @{text "Y \<subseteq> X"}.

A lower (upper) bound for @{text Y} is an lower (upper) bound for every 
element of @{text Y}.

*}

definition
  is_lb  :: "['a set, 'a orderT, 'a set, 'a] \<rightarrow> \<bool>"
where
  is_lb_def: "is_lb \<defs> (\<olambda> X r Y a \<bullet> a \<in> X \<and> (\<forall> x | x \<in> Y \<bullet> \<^infopa>{:a:}{:r:}{:x:}))"

definition
  is_ub  :: "['a set, 'a orderT, 'a set, 'a] \<rightarrow> \<bool>" 
where
  is_ub_def: "is_ub \<defs> (\<olambda> X r Y a \<bullet> a \<in> X \<and> (\<forall> x | x \<in> Y \<bullet> \<^infopa>{:x:}{:r:}{:a:}))"

notation (zed)
  is_lb ("\<^lbp>{:_:}{:_:}") and
  is_ub ("\<^ubp>{:_:}{:_:}")

text {*

A lower (upper) bound of @{text Y} that is in @{text Y} is called the
least (greatest) element of @{text Y}.

*}

definition
  is_least :: "['a set, 'a orderT, 'a set, 'a] \<rightarrow> \<bool>"
where
  is_least_def: "is_least \<defs> (\<olambda> X r Y a \<bullet> a \<in> X \<inter> Y \<and> (\<forall> x | x \<in> Y \<bullet> \<^infopa>{:a:}{:r:}{:x:}))"

definition
  is_greatest :: "['a set, 'a orderT, 'a set, 'a] \<rightarrow> \<bool>"
where
  is_greatest_def: "is_greatest \<defs> (\<olambda> X r Y a \<bullet> a \<in> X \<inter> Y \<and> (\<forall> x | x \<in> Y \<bullet> \<^infopa>{:x:}{:r:}{:a:}))"

notation (zed)
  is_least ("\<^lp>{:_:}{:_:}") and
  is_greatest ("\<^gp>{:_:}{:_:}")

text {*

The greatest (least) lower (upper) bound for @{text Y} is the greatest
(least) of the lower (upper) bounds of @{text Y}.

*}

definition
  is_glb :: "['a set, 'a orderT, 'a set, 'a] \<rightarrow> \<bool>"
where
  is_glb_def: "is_glb \<defs> (\<olambda> X r Y a \<bullet> is_greatest X r {b | is_lb X r Y b} a)"

definition
  is_lub :: "['a set, 'a orderT, 'a set, 'a] \<rightarrow> \<bool>"
where
  is_lub_def: "is_lub \<defs> (\<olambda> X r Y a \<bullet> is_least X r {b | is_ub X r Y b} a)"

notation (zed)
  is_glb ("\<^glbp>{:_:}{:_:}") and
  is_lub ("\<^lubp>{:_:}{:_:}")



text {*

Bounds and extremals only exist for subsets of the poset.

*}

context setrel_sig

begin

abbreviation
  is_lb :: "['a set, 'a] \<rightarrow> \<bool>"
where
  "is_lb \<defs> \<^lbp>{:X:}{:(op \<hookrightarrow>):}"

abbreviation
  is_ub :: "['a set, 'a] \<rightarrow> \<bool>"
where
  "is_ub \<defs> \<^ubp>{:X:}{:(op \<hookrightarrow>):}"

abbreviation
  is_least :: "['a set, 'a] \<rightarrow> \<bool>"
where
  "is_least \<defs> \<^lp>{:X:}{:(op \<hookrightarrow>):}"

abbreviation
  is_greatest :: "['a set, 'a] \<rightarrow> \<bool>"
where
  "is_greatest \<defs> \<^gp>{:X:}{:(op \<hookrightarrow>):}"

abbreviation
  is_glb :: "['a set, 'a] \<rightarrow> \<bool>"
where
  "is_glb \<defs> \<^glbp>{:X:}{:(op \<hookrightarrow>):}"

abbreviation
  is_lub :: "['a set, 'a] \<rightarrow> \<bool>"
where
  "is_lub \<defs> \<^lubp>{:X:}{:(op \<hookrightarrow>):}"

end

context X_setrel

begin

notation
  X.is_glb ("is'_glb\<^sub>X") and
  X.is_lub ("is'_lub\<^sub>X")

end

context Y_setrel

begin

notation
  Y.is_glb ("is'_glb\<^sub>Y") and
  Y.is_lub ("is'_lub\<^sub>Y")

end

context setrel

begin

lemma lb_sub:
    "is_lb Y a \<turnstile> Y \<subseteq> X"
  by (auto intro: relD2 simp add: is_lb_def)

lemma ub_sub:
    "is_ub Y a \<turnstile> Y \<subseteq> X"
  by (auto intro: relD1 simp add: is_ub_def)

lemma least_sub:
    "is_least Y a \<turnstile> Y \<subseteq> X"
  by (auto intro: relD2 simp add: is_least_def)

lemma greatest_sub:
    "is_greatest Y a \<turnstile> Y \<subseteq> X"
  by (auto intro: relD1 simp add: is_greatest_def)

lemma glb_sub:
    "is_glb Y a \<turnstile> Y \<subseteq> X"
  by (auto intro: relD2 simp add: is_glb_def is_greatest_def is_lb_def)

lemma lub_sub:
    "is_lub Y a \<turnstile> Y \<subseteq> X"
  by (auto intro: relD1 simp add: is_lub_def is_least_def is_ub_def)

end

text {*

A bound or extremal must by in the poset.

*}

context setrel_sig

begin

lemma lb_elt:
    "is_lb Y a \<turnstile> a \<in> X"
  by (auto simp add: is_lb_def)

lemma ub_elt:
    "is_ub Y a \<turnstile> a \<in> X"
  by (auto simp add: is_ub_def)

end

context setrel

begin


lemma least_elt:
    "is_least Y a \<turnstile> a \<in> X"
  by (auto intro: relD1 simp add: is_least_def)

lemma greatest_elt:
    "is_greatest Y a \<turnstile> a \<in> X"
  by (auto intro: relD1 simp add: is_greatest_def)

lemma glb_elt:
    "is_glb Y a \<turnstile> a \<in> X"
  by (auto intro: relD1 simp add: is_glb_def is_greatest_def is_lb_def)

lemma lub_elt:
    "is_lub Y a \<turnstile> a \<in> X"
  by (auto intro: relD1 simp add: is_lub_def is_least_def is_ub_def)

end

text {*

If a least (greatest) element exists then it is unique.

*}

context partial_order

begin

lemma least_unique:
  assumes
    a1: "is_least Y a" and
    a2: "is_least Y x"
  shows
    "x = a"
proof -
  from a1 have 
    b1: "a \<in> Y"
    by (simp add: is_least_def)
  from a2 have 
    b2: "x \<in> Y"
    by (simp add: is_least_def)
  from a1 b2 have 
    b3: "a \<preceq> x"
    by (simp add: is_least_def)
  also from a2 b1 have 
    b4: "x \<preceq> a"
    by (simp add: is_least_def)
  finally show 
      "x = a"
    by (auto)
qed

lemma greatest_unique:
  assumes
    a1: "is_greatest Y a" and
    a2: "is_greatest Y x"
  shows
    "x = a"
proof -
  from a1 have 
    b1: "a \<in> Y"
    by (simp add: is_greatest_def)
  from a2 have 
    b2: "x \<in> Y"
    by (simp add: is_greatest_def)
  from a1 b2 have 
      "x \<preceq> a"
    by (simp add: is_greatest_def)
  also from a2 b1 have 
      "a \<preceq> x"
    by (simp add: is_greatest_def)
  finally show 
      "x = a"
    by (auto)
qed

lemma lub_unique:
  assumes
    a1: "is_lub Y a" and
    a2: "is_lub Y x"
  shows
    "x = a"
  apply (rule least_unique)
  using a1 a2
  apply (auto simp add: is_lub_def)
  done

lemma glb_unique:
  assumes
    a1: "is_glb Y a" and
    a2: "is_glb Y x"
  shows
    "x = a"
  apply (rule greatest_unique)
  using a1 a2
  apply (auto simp add: is_glb_def)
  done

end

text {*

Finally we develop introduction and elimination rules for bounds.

*}

context setrel_sig

begin

lemma is_ubI:
    "\<lbrakk> a \<in> X; (\<And> x \<bullet> x \<in> A \<turnstile> x \<hookrightarrow> a) \<rbrakk> \<turnstile> is_ub A a"
  by (auto simp add: is_ub_def)

lemma is_lbI:
    "\<lbrakk> a \<in> X; (\<And> x \<bullet> x \<in> A \<turnstile> a \<hookrightarrow> x) \<rbrakk> \<turnstile> is_lb A a"
  by (auto simp add: is_lb_def)

end

context setrel 

begin

lemma is_leastI:
    "\<lbrakk> a \<in> A; (\<And> x \<bullet> x \<in> A \<turnstile> a \<hookrightarrow> x) \<rbrakk> \<turnstile> is_least A a"
  by (auto intro!: relD1 simp add: is_least_def)

lemma is_lubI:
    "\<lbrakk> 
      a \<in> X; 
      (\<And> x \<bullet> x \<in> A \<turnstile> x \<hookrightarrow> a); 
      (\<And> b \<bullet> \<lbrakk> b \<in> X; (\<forall> x \<bullet> x \<in> A \<Rightarrow> x \<hookrightarrow> b) \<rbrakk> \<turnstile> a \<hookrightarrow> b) 
     \<rbrakk> \<turnstile> is_lub A a"
  by (auto simp add: is_lub_def is_least_def is_ub_def)

lemma is_greatestI:
    "\<lbrakk> a \<in> A; (\<And> x \<bullet> x \<in> A \<turnstile> x \<hookrightarrow> a) \<rbrakk> \<turnstile> is_greatest A a"
  by (auto intro!: relD1 simp add: is_greatest_def)

lemma is_glbI:
    "\<lbrakk> 
      a \<in> X; 
      (\<And> x \<bullet> x \<in> A \<turnstile> a \<hookrightarrow> x); 
      (\<And> b \<bullet> \<lbrakk> b \<in> X; (\<forall> x \<bullet> x \<in> A \<Rightarrow> b \<hookrightarrow> x) \<rbrakk>  \<turnstile> b \<hookrightarrow> a) 
     \<rbrakk> \<turnstile> is_glb A a"
  by (auto simp add: is_glb_def is_greatest_def is_lb_def)

lemma is_ubD:
    "\<lbrakk> is_ub A a; x \<in> A \<rbrakk> \<turnstile> x \<hookrightarrow> a"
  by (simp add: is_ub_def)

lemma is_lbD:
    "\<lbrakk> is_lb A a; x \<in> A \<rbrakk> \<turnstile> a \<hookrightarrow> x"
  by (simp add: is_lb_def)

lemma is_leastD:
    "\<lbrakk> is_least A a; x \<in> A \<rbrakk> \<turnstile> a \<hookrightarrow> x"
  by (simp add: is_least_def)

lemma is_greatestD:
    "\<lbrakk> is_greatest A a; x \<in> A \<rbrakk> \<turnstile> x \<hookrightarrow> a"
  by (simp add: is_greatest_def)

lemma is_lubD1:
    "is_lub A a \<turnstile> is_ub A a"
  by (simp add: is_lub_def is_ub_def is_least_def)

lemma is_lubD1':
    "\<lbrakk> is_lub A a; x \<in> A\<rbrakk> \<turnstile> x \<hookrightarrow> a"
  by (auto intro: is_ubD [OF is_lubD1])

lemma is_lubD2:
    "is_lub A a \<turnstile> is_least {x | is_ub A x} a"
  by (simp add: is_lub_def is_ub_def is_least_def)

lemma is_lubD2':
    "\<lbrakk> is_lub A a;  x \<in> X; (\<And> y \<bullet> y \<in> A \<turnstile> y \<hookrightarrow> x)\<rbrakk> \<turnstile> a \<hookrightarrow> x"
  by (auto intro: is_lubD2 [THEN is_leastD, simplified, OF _ is_ubI])

lemma is_glbD1:
    "is_glb A a \<turnstile> is_lb A a"
  by (simp add: is_glb_def is_lb_def is_greatest_def)

lemma is_glbD1':
    "\<lbrakk> is_glb A a; x \<in> A\<rbrakk> \<turnstile> a \<hookrightarrow> x"
  by (auto intro: is_lbD [OF is_glbD1])

lemma is_glbD2:
    "is_glb A a \<turnstile> is_greatest {x | is_lb A x} a"
  by (simp add: is_glb_def is_lb_def is_greatest_def)

lemma is_glbD2':
    "\<lbrakk> is_glb A a;  x \<in> X; (\<And> y \<bullet> y \<in> A \<turnstile> x \<hookrightarrow> y)\<rbrakk> \<turnstile> x \<hookrightarrow> a"
  by (auto intro: is_glbD2 [THEN is_greatestD, simplified, OF _ is_lbI])

end

text {*

If linearly ordered then of course the bounds can be computed.

*}

definition
  minimum :: "['a set, 'a orderT, 'a, 'a] \<rightarrow> 'a"
where
  minimum_def: "minimum \<defs> (\<olambda> X r x y \<bullet> \<if> \<^infop>{:x:}{:r:}{:y:} \<then> x \<else> y \<fi>)"

definition
  maximum :: "['a set, 'a orderT, 'a, 'a] \<rightarrow> 'a"
where
  maximum_def: "maximum \<defs> (\<olambda> X r x y \<bullet> \<if> \<^infop>{:x:}{:r:}{:y:} \<then> y \<else> x \<fi>)"

notation (zed)
  minimum ("\<^min>{:_:}{:_:}") and
  maximum ("\<^max>{:_:}{:_:}")

context setrel_sig

begin

abbreviation
  minimum :: "['a, 'a] \<rightarrow> 'a"
where
  "minimum \<defs> \<^min>{:X:}{:(op \<hookrightarrow>):}"

abbreviation
  maximum :: "['a, 'a] \<rightarrow> 'a"
where
  "maximum \<defs> \<^max>{:X:}{:(op \<hookrightarrow>):}"

end

context order

begin

lemma is_glb_eq:
  assumes 
    A1: "x \<in> X" and 
    A2: "y \<in> X"
  shows
    "is_glb {x, y} (minimum x y)"
  apply (unfold minimum_def)
  apply (rule is_glbI)
  using A1 A2
  apply (simp)
  apply (simp, elim disjE, simp_all, msafe(inference))
  apply (rule A1 [THEN refl [rule_format]])
  using A2 [THEN A1 [THEN linD]]
  apply (simp)
  apply (rule A2 [THEN refl [rule_format]])
  done

lemma is_lub_eq:
  assumes 
    A1: "x \<in> X" and 
    A2: "y \<in> X"
  shows
    "is_lub {x,y} (maximum x y)"
  apply (unfold maximum_def)
  apply (rule is_lubI)
  using A1 A2
  apply (simp)
  apply (simp_all, elim disjE, simp_all, msafe(inference))
  apply (rule A1 [THEN refl [rule_format]])
  apply (rule A2 [THEN refl [rule_format]])
  using A2 [THEN A1 [THEN linD]]
  apply (simp)
  done

end

text {*

The two notions of bounds/extremals are mutually dual.

*}

context setrel_sig 

begin

lemma is_lb_dual:
    "\<^lbp>{:X:}{:(op \<hookleftarrow>):} = is_ub"
  by (simp add: is_lb_def is_ub_def converse_rel_def)

lemma is_ub_dual:
    "\<^ubp>{:X:}{:(op \<hookleftarrow>):} = is_lb"
  by (simp add: is_lb_def is_ub_def converse_rel_def)

lemma is_least_dual:
  "\<^lp>{:X:}{:(op \<hookleftarrow>):} = is_greatest"
  by (simp add: is_greatest_def is_least_def converse_rel_def)

lemma is_greatest_dual:
    "\<^gp>{:X:}{:(op \<hookleftarrow>):} = is_least"
  by (simp add: is_greatest_def is_least_def converse_rel_def)

lemma is_lub_dual:
    "\<^lubp>{:X:}{:(op \<hookleftarrow>):} = is_glb"
  by (simp add: is_lub_def is_glb_def is_least_dual is_ub_dual)

lemma is_glb_dual:
    "\<^glbp>{:X:}{:(op \<hookleftarrow>):} = is_lub"
  by (simp add: is_lub_def is_glb_def is_greatest_dual is_lb_dual)

end

end
