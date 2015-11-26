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

theory Order_Quotient
 
imports 
  Order_Locale 
  Order_Morphism 
  Quotient_Sets

begin

text {*

The quotient-order modulo @{text "BS_sim"} consists of all pairs
of equivalence classes with witnesses in the order.

*}

definition
  quot_order :: "['a orderT, 'a orderT] \<rightarrow> ('a set) orderT"
where
  quot_order_def: "quot_order BS_leq BS_sim \<defs> \<^relop>{:{x y | \<^infopa>{:x:}{:BS_leq:}{:y:} \<bullet> (\<^eclass>{:x:}{:BS_sim:} \<mapsto> \<^eclass>{:y:}{:BS_sim:})}:}"

notation ("" output)
  quot_order (infixl "'/'/" 90) 

notation (zed)
  quot_order ("\<^quotord>{:_:}{:_:}")


text {*

The standard use of quotient orders is to convert a preorder to an
order by taking a quotient with respect to the equivalence induced
by symmetric pairs.

*}

definition
  default_equiv :: "('a orderT) \<rightarrow> ('a orderT)"
where
  default_equiv_def: "default_equiv BS_leq \<defs> (\<olambda> x y \<bullet> \<^infopa>{:x:}{:BS_leq:}{:y:} \<and> \<^infopa>{:y:}{:BS_leq:}{:x:})"

text {*

More generally, the quotient trick will work for any equivalence relation
with respect to which the preorder is antisymmetric.

*}

locale order_cong = 
  r: preorder X r + 
  BS_sim: equivalence X BS_sim 
for 
  X::"'a set" and
  r::"'a orderT" and
  BS_sim::"'a orderT" +
assumes
  ocong: "r_congruent (op \<sim>) (op \<hookrightarrow>)" and
  antisym': "(\<forall> x y | \<lch> x, y \<chIn> X \<rch> \<bullet> x \<hookrightarrow> y \<and> y \<hookrightarrow> x \<Rightarrow> x \<sim> y)"

begin

abbreviation
  X_BS_sim_qspace ("X\<^sub>\<sim>")
where
  "X_BS_sim_qspace \<defs> \<^qspace>{:X:}{:(op \<sim>):}"

abbreviation
  r_BS_sim_qorder (infixl "\<hookrightarrow>\<^sub>\<sim>" 50)
where
  "r_BS_sim_qorder \<defs>  \<^quotord>{:(op \<hookrightarrow>):}{:(op \<sim>):}"

lemma quotpoI:
  "\<^poset>{:X\<^sub>\<sim>:}{:(op \<hookrightarrow>\<^sub>\<sim>):}"
proof (rule partial_orderI, 
       msafe(inference))
  from non_empty show 
      "X\<^sub>\<sim> \<noteq> \<emptyset>"
    by (auto simp add: quot_set_def)
  from r.rel BS_sim.rel show 
      "\<^oprel>{:(op \<hookrightarrow>\<^sub>\<sim>):} \<in> X\<^sub>\<sim> \<zrel> X\<^sub>\<sim>"
    by (auto simp add: quot_set_def quot_order_def op2rel_def rel2op_def rel_def eind_def)
next
  fix x
  assume 
      "x \<in> X\<^sub>\<sim>"
  with r.refl show 
      "x \<hookrightarrow>\<^sub>\<sim> x"
   by (auto simp add: quot_set_def quot_order_def rel2op_def)
next

txt {*

\includegraphics{qord_trans}

*}
  fix 
    x y z
  assume 
    b1: "x \<in> X\<^sub>\<sim>" "y \<in> X\<^sub>\<sim>" "z \<in> X\<^sub>\<sim>" and
    b2: "x \<hookrightarrow>\<^sub>\<sim> y" and
    b3: "y \<hookrightarrow>\<^sub>\<sim> z"
  from b2 b3 show 
      "x \<hookrightarrow>\<^sub>\<sim> z"
    apply (cases x rule: quot_class_cases)
    apply (rule b1)
    apply (cases y rule: quot_class_cases)
    apply (rule b1)
    apply (cases z rule: quot_class_cases)
    apply (rule b1)
    apply (auto simp add: BS_sim.equiv_class_eq quot_set_def quot_order_def rel2op_def)
  proof -
    fix a a' b' b b'' c'' c
    assume 
      ca: "a \<in> X" and cc: "c \<in> X" and
      c1: "a' \<hookrightarrow> b'" and c2: "b'' \<hookrightarrow> c''" and
      c3: "a \<sim> a'" and c4: "b \<sim> b'" and
      c5: "b \<sim> b''" and c6: "c \<sim> c''"
    from c1 c3 c4 ocong have 
      c7: "a \<hookrightarrow> b"
      by (auto simp add: r_congruent_def)
    also from c2 c5 c6 ocong have 
      c8: "b \<hookrightarrow> c"
      by (auto simp add: r_congruent_def)
    finally show 
        "(\<exists> x \<bullet> a \<sim> x \<and> (\<exists> y \<bullet> c \<sim> y \<and> x \<hookrightarrow> y))"
      apply (witness "a")
      apply (msafe(inference))
      apply (rule BS_sim.refl [rule_format, OF ca])
      apply (witness "c")
      apply (msafe(inference))
      apply (rule BS_sim.refl [rule_format, OF cc])
      done
  qed
next

txt {*

\includegraphics{qord_antisym}

*}
  fix 
    x y
  assume 
    b1: "x \<in> X\<^sub>\<sim>" "y \<in> X\<^sub>\<sim>" and
    b2: "x \<hookrightarrow>\<^sub>\<sim> y" and
    b3: "y \<hookrightarrow>\<^sub>\<sim> x"
  from b2 b3 show 
      "x = y"
    apply (cases x rule: quot_class_cases)
    apply (rule b1)
    apply (cases y rule: quot_class_cases)
    apply (rule b1)
    apply (auto simp add: BS_sim.equiv_class_eq quot_set_def quot_order_def rel2op_def)
  proof -
    fix a a' a'' b b' b''
    assume 
      ca: "a \<in> X" and cb: "b \<in> X" and
      c1: "a' \<hookrightarrow> b'" and c2: "b'' \<hookrightarrow> a''" and
      c3: "a \<sim> a'" and c4: "b \<sim> b'" and
      c5: "b \<sim> b''" and c6: "a \<sim> a''"
    from c1 c3 c4 ocong have 
      c7: "a \<hookrightarrow> b"
      by (auto simp add: r_congruent_def)
    moreover from c2 c5 c6 ocong have 
      c8: "b \<hookrightarrow> a"
      by (auto simp add: r_congruent_def)
    ultimately show 
        "a \<sim> b"
      apply (intro antisym' [rule_format])
      apply (auto simp add: ca cb)
      done
  qed
qed

end

context preorder

begin


abbreviation
  r_equiv (infixl "\<sim>" 50)
where
  "r_equiv \<defs> default_equiv (op \<hookrightarrow>)"

lemma default_order_congI:
  "order_cong X (op \<hookrightarrow>) (op \<sim>)"
  apply (intro_locales)
  apply (auto intro!: setrel_axioms.intro reflexive_axioms.intro transitive_axioms.intro symmetric_axioms.intro order_cong_axioms.intro simp add: r_congruent_def)
proof -
  from rel show 
      "\<^oprel>{:(op \<sim>):} \<in> X \<zrel> X"
    by (auto simp add: default_equiv_def op2rel_def rel_def eind_def)
next
  fix 
    x 
  assume 
    "x \<in> X"
  with refl show 
      "x \<sim> x"
    by (simp add: default_equiv_def)
next
  fix x y z
  assume b1: "x \<in> X" "y \<in> X" "z \<in> X" and
    b2: "x \<sim> y" and
    b3: "y \<sim> z"
  from b2 have 
      "x \<hookrightarrow> y"
    by (simp add: default_equiv_def)
  also from b3 have 
      "y \<hookrightarrow> z"
    by (simp add: default_equiv_def)
  finally have 
    b4: "x \<hookrightarrow> z"
    by (this)
  from b3 have 
      "z \<hookrightarrow> y"
    by (simp add: default_equiv_def)
  also from b2 have 
      "y \<hookrightarrow> x"
    by (simp add: default_equiv_def)
  finally have 
    b5: "z \<hookrightarrow> x"
    by (this)
  from b4 b5 show 
      "x \<sim> z"
    by (simp add: default_equiv_def)
next
  fix 
    x y 
  assume 
      "x \<sim> y"
  then show 
      "y \<sim> x"
    by (simp add: default_equiv_def)
next
  fix 
    x x' y y'
  assume 
    b1: "x \<sim> x'" and 
    b2: "y \<sim> y'" and
    b3: "x' \<hookrightarrow> y'"
  from b1 have 
      "x \<hookrightarrow> x'"
    by (simp add: default_equiv_def)
  also note b3
  also from b2 have 
      "y' \<hookrightarrow> y"
    by (simp add: default_equiv_def)
  finally show 
      "x \<hookrightarrow> y"
    by (this)
next
  fix 
    x x' y y'
  assume 
    b1: "x \<sim> x'" and 
    b2: "y \<sim> y'" and
    b3: "x \<hookrightarrow> y"
  from b1 have 
      "x' \<hookrightarrow> x"
    by (simp add: default_equiv_def)
  also note b3
  also from b2 have 
      "y \<hookrightarrow> y'"
    by (simp add: default_equiv_def)
  finally show 
      "x' \<hookrightarrow> y'"
    by (this)
next
  fix 
    x y 
  assume 
      "x \<hookrightarrow> y" "y \<hookrightarrow> x"
  then show 
      "x \<sim> y"
    by (simp add: default_equiv_def)
qed

abbreviation
  X_r_qspace :: "'a set set" ("X\<^sub>\<sim>")
where
  "X_r_qspace \<defs> \<^qspace>{:X:}{:(op \<sim>):}"

abbreviation
  r_dqorder (infixl "\<hookrightarrow>\<^sub>\<sim>" 50)
where
  "r_dqorder \<defs>  \<^quotord>{:(op \<hookrightarrow>):}{:(op \<sim>):}"

lemma default_quotient_poI:
    "partial_order X\<^sub>\<sim> (op \<hookrightarrow>\<^sub>\<sim>)"
  apply (rule order_cong.quotpoI)
  apply (rule default_order_congI)
  done

end

context partial_order

begin

lemma ord_congI:
  assumes 
    a1: "r_congruent BS_sim (op \<preceq>)" and
    a2: "\<^infopa>{:x_d_1:}{:BS_sim:}{:x_d_2:}" "\<^infopa>{:y_d_1:}{:BS_sim:}{:y_d_2:}" and
    a3: "x_d_1 \<preceq> y_d_1"
  shows "x_d_2 \<preceq> y_d_2"
  using a1 a2 a3
  apply (simp add: r_congruent_def)
  apply (auto)
  done

lemma quot_order_conv:
  assumes 
    equiv: "equivalence X BS_sim" and
    cong: "r_congruent BS_sim (op \<preceq>)"  
  shows 
      "\<^infopa>{:A:}{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:}{:B:} 
      \<Leftrightarrow> A \<in> \<^qspace>{:X:}{:BS_sim:} \<and> B \<in> \<^qspace>{:X:}{:BS_sim:} \<and>
      (\<forall> x y | x \<in> A \<and> y \<in> B \<bullet> x \<preceq> y)"
  apply (auto simp del: ex_simps simp add: quot_order_def quot_set_def rel2op_def relD1 relD2)
  defer
  apply (rule exI, rule exI, msafe(inference), rule HOL.refl, rule HOL.refl)
proof -
  fix x x' y y'
  assume 
    "x' \<in> \<^eclass>{:x:}{:BS_sim:}" "y' \<in> \<^eclass>{:y:}{:BS_sim:}" "x \<preceq> y"
  with cong show 
      "x' \<preceq> y'"
    by (auto simp add: r_congruent_def equiv_class_def)
next
  fix x y 
  assume 
    b1: "(\<forall> x' y' | x' \<in> \<^eclass>{:x:}{:BS_sim:} \<and> y' \<in> \<^eclass>{:y:}{:BS_sim:} \<bullet> x' \<preceq> y')" and
    b2: "x \<in> X" "y \<in> X"
  from b2 equiv reflexive.reflD [of X BS_sim] have 
    b3: "x \<in> \<^eclass>{:x:}{:BS_sim:}"
    by (auto simp add: equivalence_conv equiv_class_def reflexive_def relD1)
  from b2 equiv reflexive.reflD [of X BS_sim] have 
    b4: "y \<in> \<^eclass>{:y:}{:BS_sim:}"
    by (auto simp add: equivalence_conv equiv_class_def reflexive_def relD1)
  from b3 b4 b1 show 
      "x \<preceq> y"
    by (auto)
qed

lemma quot_order_conva:
  assumes    
    equiv: "equivalence X BS_sim" and
    cong: "r_congruent BS_sim (op \<preceq>)"
  shows 
      "\<^infopa>{:\<^eclass>{:x:}{:BS_sim:}:}{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:}{:\<^eclass>{:y:}{:BS_sim:}:} \<Leftrightarrow> x \<preceq> y" (is "?LHS = ?RHS")
proof (msafe(inference))
  assume 
    b1: "?LHS"
  also have 
      "?LHS
      \<Leftrightarrow> x \<in> X \<and> y \<in> X \<and> (\<forall> x' y' \<bullet> \<^infopa>{:x:}{:BS_sim:}{:x':} \<and> \<^infopa>{:y:}{:BS_sim:}{:y':} \<Rightarrow> x' \<preceq> y')"
    apply (simp add: quot_order_conv [OF equiv cong] equivalence.quot_set_mem_ec [OF equiv])
    apply (simp add: equiv_class_def)
    done
  also have "\<dots>
      \<Rightarrow> (x \<in> X \<and> y \<in> X) \<and> (\<^infopa>{:x:}{:BS_sim:}{:x:} \<and> \<^infopa>{:y:}{:BS_sim:}{:y:} \<Rightarrow> x \<preceq> y)"
    by (auto)
  also from equiv have "\<dots>
      \<Rightarrow> (\<^infopa>{:x:}{:BS_sim:}{:x:} \<and> \<^infopa>{:y:}{:BS_sim:}{:y:}) \<and> (\<^infopa>{:x:}{:BS_sim:}{:x:} \<and> \<^infopa>{:y:}{:BS_sim:}{:y:} \<Rightarrow> x \<preceq> y)"
    apply (mauto(wind))
    apply (simp add: equivalence_conv reflexive.reflD [of X BS_sim])
    done
  finally show 
      "?RHS" 
    by (auto)
next 
  assume
    b1: "?RHS"
  from b1 show 
      "?LHS"
    apply (auto dest: relD1 relD2 simp add: quot_order_conv [OF equiv cong] quot_setI)
    apply (simp add: equiv_class_def)
  proof -
    fix 
      x' y'
    assume 
        "\<^infopa>{:x:}{:BS_sim:}{:x':}" "\<^infopa>{:y:}{:BS_sim:}{:y':}"
    with cong have    
        "x \<preceq> y \<Leftrightarrow> x' \<preceq> y'"
      by (auto simp add: r_congruent_def)
    with b1 show 
        "x' \<preceq> y'"
      by (simp)
  qed
qed

lemma quot_poI: 
  assumes 
    equiv: "equivalence X BS_sim" and
    cong: "r_congruent BS_sim (op \<preceq>)"
  shows 
      "\<^poset>{:\<^qspace>{:X:}{:BS_sim:}:}{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:}" 
proof (rule partial_orderI,
       msafe(inference))
  from non_empty show 
      "\<^qspace>{:X:}{:BS_sim:} \<noteq> \<emptyset>"
    by (simp add: quot_set_def)
next
  show 
      "\<^oprel>{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:} \<in> \<^qspace>{:X:}{:BS_sim:} \<zrel> \<^qspace>{:X:}{:BS_sim:}"
    by (auto 
          dest: relD1 relD2 
          simp add: quot_order_def quot_set_def rel_def rel2op_def op2rel_def eind_def)
next
  fix 
    A 
  assume 
    b1: "A \<in> \<^qspace>{:X:}{:BS_sim:}"
  then show 
      "\<^infopa>{:A:}{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:}{:A:}"
    by (auto dest: reflD simp add: quot_set_mem quot_order_conva [OF equiv cong])
next
  fix 
    A B C
  assume 
      "A \<in> \<^qspace>{:X:}{:BS_sim:}" 
      "B \<in> \<^qspace>{:X:}{:BS_sim:}" 
      "C \<in> \<^qspace>{:X:}{:BS_sim:}"
      "\<^infopa>{:A:}{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:}{:B:}" 
      "\<^infopa>{:B:}{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:}{:C:}"
  then show 
      "\<^infopa>{:A:}{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:}{:C:}"
    by (auto dest: transD simp add: quot_set_mem quot_order_conva [OF equiv cong]) 
next
  fix 
    A B 
  assume 
      "A \<in> \<^qspace>{:X:}{:BS_sim:}" 
      "B \<in> \<^qspace>{:X:}{:BS_sim:}"
      "\<^infopa>{:A:}{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:}{:B:}" 
      "\<^infopa>{:B:}{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:}{:A:}"
  then show 
      "A = B"
    by (auto dest: antisymD simp add: quot_set_mem quot_order_conva [OF equiv cong])
qed

end

lemma (in order) quot_orderI: 
  assumes 
    equiv: "equivalence X BS_sim" and
    cong: "r_congruent BS_sim (op \<preceq>)"
  shows 
    "\<^order>{:\<^qspace>{:X:}{:BS_sim:}:}{:\<^quotord>{:(op \<preceq>):}{:BS_sim:}:}" 
  apply (rule partial_order.orderIa [OF quot_poI [OF equiv cong]])
  apply (auto dest: linD simp add: quot_set_mem quot_order_conva [OF equiv cong]) 
  done


end
 
