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

theory Quotient_Sets 
  
imports
  Order_Locale

begin

text {*

A quotient space is constructed by taking the collection of equivalence
classes modulo an equivalence relation @{text "BS_sim"}.

*}

definition
  equiv_class :: "['a, 'a orderT] \<rightarrow> 'a set"
where
  equiv_class_def: "equiv_class x BS_sim \<defs> {y | \<^infopa>{:x:}{:BS_sim:}{:y:}}"

notation (xsymbols output)
  equiv_class (infixl "\<up>" 90) 

notation (zed)
  equiv_class ("\<^eclass>{:_:}{:_:}") 


lemma equiv_class_mem: "y \<in> \<^eclass>{:x:}{:BS_sim:} \<Leftrightarrow> \<^infopa>{:x:}{:BS_sim:}{:y:}" 
  by (simp add: equiv_class_def)

lemma (in equivalence) equiv_class_eq: 
  assumes a1: "x \<in> X"
  shows "\<^eclass>{:x:}{:BS_sim:} = \<^eclass>{:y:}{:BS_sim:} \<Leftrightarrow> \<^infopa>{:x:}{:BS_sim:}{:y:}"
  apply (simp add: equiv_class_def)
  apply (rule iffI)
proof -
  assume b1: "{z | \<^infopa>{:x:}{:BS_sim:}{:z:}} = {z | \<^infopa>{:y:}{:BS_sim:}{:z:}}"
  from a1 have "\<^infopa>{:x:}{:BS_sim:}{:x:}"
    by (rule reflD)
  then have "{z | \<^infopa>{:y:}{:BS_sim:}{:z:}} \<noteq> \<emptyset>"
    by (auto simp add: b1 [THEN HOL.sym])
  then have "y \<in> X"
    by (auto dest: relD1)
  then have "\<^infopa>{:y:}{:BS_sim:}{:y:}"
    by (rule reflD)
  also from b1 have "\<^infopa>{:y:}{:BS_sim:}{:y:}
  \<Leftrightarrow> \<^infopa>{:x:}{:BS_sim:}{:y:}"
    by (simp add: set_eq_def)
  finally show "\<^infopa>{:x:}{:BS_sim:}{:y:}" by (this)
next
  assume b1: "\<^infopa>{:x:}{:BS_sim:}{:y:}"
  show "{z | \<^infopa>{:x:}{:BS_sim:}{:z:}} = {z | \<^infopa>{:y:}{:BS_sim:}{:z:}}"
  proof (auto)
    fix z assume c1: "\<^infopa>{:x:}{:BS_sim:}{:z:}"
    from b1 have "\<^infopa>{:y:}{:BS_sim:}{:x:}"
      by (rule symD)
    also have "\<^infopa>{:x:}{:BS_sim:}{:z:}"
      by (rule c1)
    finally show "\<^infopa>{:y:}{:BS_sim:}{:z:}"
      by (this)
  next
    fix z assume c1: "\<^infopa>{:y:}{:BS_sim:}{:z:}"
    have "\<^infopa>{:x:}{:BS_sim:}{:y:}"
      by (rule b1)
    also have "\<^infopa>{:y:}{:BS_sim:}{:z:}"
      by (rule c1)
    finally show "\<^infopa>{:x:}{:BS_sim:}{:z:}"
      by (this)
  qed
qed

lemma (in equivalence) equiv_class_eq': 
  assumes a1: "y \<in> X"
  shows "\<^eclass>{:x:}{:BS_sim:} = \<^eclass>{:y:}{:BS_sim:} \<Leftrightarrow> \<^infopa>{:x:}{:BS_sim:}{:y:}"
proof -
  have "\<^eclass>{:x:}{:BS_sim:} = \<^eclass>{:y:}{:BS_sim:}
  \<Leftrightarrow> \<^eclass>{:y:}{:BS_sim:} = \<^eclass>{:x:}{:BS_sim:}"
    by (auto)
  also have "\<dots>
  \<Leftrightarrow> \<^infopa>{:y:}{:BS_sim:}{:x:}"
    by (simp add: equiv_class_eq [OF a1])
  also have "\<dots>
  \<Leftrightarrow> \<^infopa>{:x:}{:BS_sim:}{:y:}"
    by (auto dest: symD)
  finally show ?thesis by (this)
qed

lemma (in equivalence) equiv_class_eqI: 
  assumes 
    a1: "\<^infopa>{:x:}{:BS_sim:}{:y:}"
  shows 
    "\<^eclass>{:x:}{:BS_sim:} = \<^eclass>{:y:}{:BS_sim:}"
  using relD1 [OF a1] a1 
  by (simp add: equiv_class_eq)

definition
  quot_set :: "['a set, 'a orderT] \<rightarrow> 'a set set"
where
  quot_set_def: "quot_set X BS_sim \<defs> {x | x \<in> X \<bullet> \<^eclass>{:x:}{:BS_sim:}}"

notation ("" output)
  quot_set (infixl "'/'/" 90) 

notation (zed)
  quot_set ("\<^qspace>{:_:}{:_:}")

lemma quot_setI: "x \<in> X \<turnstile> \<^eclass>{:x:}{:BS_sim:} \<in> \<^qspace>{:X:}{:BS_sim:}"
  by (auto simp add: quot_set_def equiv_class_def)

lemma (in equivalence) ec_range:
  "A \<in> \<^qspace>{:X:}{:BS_sim:} \<turnstile> A \<subseteq> X"
  by (auto simp add: quot_set_def equiv_class_def set_eq_def relD2)

lemma quot_set_mem: "A \<in> \<^qspace>{:X:}{:BS_sim:} \<Leftrightarrow> (\<exists> x \<bullet> x \<in> X \<and> A = \<^eclass>{:x:}{:BS_sim:})"
  by (auto simp add: quot_set_def equiv_class_def)

lemma (in equivalence) quot_set_mem_ec: 
  "\<^eclass>{:x:}{:BS_sim:} \<in> \<^qspace>{:X:}{:BS_sim:} \<Leftrightarrow> x \<in> X"
  by (auto simp add: quot_set_mem reflD relD1 equiv_class_eq')

lemma (in equivalence) quot_set_mem_ec': 
  assumes a1: "A \<subseteq> X"
  shows "\<^eclass>{:x:}{:BS_sim:} \<in> \<^qspace>{:A:}{:BS_sim:} \<Leftrightarrow> (\<exists> y \<bullet> y \<in> A \<and> \<^infopa>{:x:}{:BS_sim:}{:y:})"
proof -
  have "\<^eclass>{:x:}{:BS_sim:} \<in> \<^qspace>{:A:}{:BS_sim:}
  \<Leftrightarrow> (\<exists> y \<bullet> y \<in> A \<and> \<^eclass>{:x:}{:BS_sim:} = \<^eclass>{:y:}{:BS_sim:})"
    by (simp add: quot_set_mem)
  also have "\<dots> 
  \<Leftrightarrow> (\<exists> y \<bullet> y \<in> A \<and> \<^infopa>{:x:}{:BS_sim:}{:y:})"
  proof (mauto(wind))
    fix y assume c1: "y \<in> A"
    with a1 have "y \<in> X" by (auto)
    then show "\<^eclass>{:x:}{:BS_sim:} = \<^eclass>{:y:}{:BS_sim:} \<Leftrightarrow> \<^infopa>{:x:}{:BS_sim:}{:y:}"
      by (simp add: equiv_class_eq')
  qed
  finally show ?thesis by (this)
qed

lemma quot_class_cases:
  assumes a1: "A \<in> \<^qspace>{:X:}{:BS_sim:}" and
    a2: "\<And> x \<bullet> \<lbrakk> x \<in> X; A = \<^eclass>{:x:}{:BS_sim:} \<rbrakk> \<turnstile> R"
  shows R
proof -
  from a1 obtain x where "x \<in> X" "A = \<^eclass>{:x:}{:BS_sim:}"
    by (auto simp add: quot_set_mem)
  then show R
    by (rule a2)
qed

lemma (in equivalence) quotient_space_eq:
  assumes
    a1: "A \<in> \<^qspace>{:X:}{:BS_sim:}" and  
    a2: "B \<in> \<^qspace>{:X:}{:BS_sim:}"
  shows
    "A = B \<Leftrightarrow> (\<forall> x y | x \<in> A \<and> y \<in> B \<bullet> \<^infopa>{:x:}{:BS_sim:}{:y:})"
  apply (rule quot_class_cases [OF a1])
  apply (rule quot_class_cases [OF a2])
  apply (rule iffI)
  apply (simp add: set_eq_def)
  apply (simp add: equiv_class_mem)
  apply (mauto(inference) mintro: transD [OF symD])
  apply (rule set_eqI)
  apply (subst (asm) equiv_class_mem)+
  apply (subst equiv_class_mem)+
proof -
  fix
    x xa xb
  assume
    b1 [rule_format]: "\<forall> xb y \<bullet> x \<sim> xb \<and> xa \<sim> y \<Rightarrow> xb \<sim> y"  and
    b2: "x \<in> X" and
    b3: "xa \<in> X"
  from b1 [OF _ reflD [OF b3], THEN symD] b1 [OF reflD [OF b2]] show
    "x \<sim> xb \<Leftrightarrow> xa \<sim> xb"
    by (auto)
qed

definition
  quot_char :: "['a set, 'a orderT] \<rightarrow> 'a"
where
  quot_char_def: "quot_char A BS_sim \<defs> (\<some> x | x \<in> A \<and> A = \<^eclass>{:x:}{:BS_sim:})"

notation (xsymbols output)
  quot_char (infixl "\<down>" 90)

notation (zed)
  quot_char ("\<^qchar>{:_:}{:_:}")

lemma (in equivalence) quot_char_class: 
  assumes a1: "A \<in> \<^qspace>{:X:}{:BS_sim:}"
  shows "\<^eclass>{:\<^qchar>{:A:}{:BS_sim:}:}{:BS_sim:} = A"
proof -
  let "?P x" = "x \<in> A \<and> A = \<^eclass>{:x:}{:BS_sim:}"
  from a1 reflD have b1: "\<exists> x \<bullet> ?P x"
    apply (simp add: quot_set_mem total_rel equiv_class_def)
    apply (blast)
    done
  from b1 [THEN someI_ex [of ?P]]
  have "?P (\<^qchar>{:A:}{:BS_sim:})"
    by (simp add: quot_char_def)
  then have "A = \<^eclass>{:\<^qchar>{:A:}{:BS_sim:}:}{:BS_sim:}"
    by (msafe(inference))
  then show ?thesis
    by (rule HOL.sym)
qed
  
lemma (in equivalence) quot_class_char: 
  assumes 
    a1: "x \<in> X"
  shows 
    "\<^infopa>{:\<^qchar>{:\<^eclass>{:x:}{:BS_sim:}:}{:BS_sim:}:}{:BS_sim:}{:x:}"
proof (rule symD)
  let
    ?P = "(\<olambda> y \<bullet> y \<in> \<^eclass>{:x:}{:BS_sim:} \<and> \<^eclass>{:x:}{:BS_sim:} = \<^eclass>{:y:}{:BS_sim:})"
  have
    b1: "?P x"
    by (simp add: equiv_class_mem reflD [OF a1])
  from someI [of ?P, OF b1] show
    "\<^infopa>{:x:}{:BS_sim:}{:\<^qchar>{:\<^eclass>{:x:}{:BS_sim:}:}{:BS_sim:}:}"
    by (simp add: quot_char_def equiv_class_eq [OF a1])
qed

lemma (in equivalence) quot_char_mem:
  assumes a1: "A \<in> \<^qspace>{:X:}{:BS_sim:}"
  shows "\<^qchar>{:A:}{:BS_sim:} \<in> A"
proof -
  let "?P x" = "x \<in> A \<and> A = \<^eclass>{:x:}{:BS_sim:}"
  from a1 reflD have b1: "\<exists> x \<bullet> ?P x"
    apply (simp add: quot_set_mem total_rel equiv_class_def)
    apply (blast)
    done
  from b1 someI_ex [of ?P]
  have "?P (\<^qchar>{:A:}{:BS_sim:})"
    by (simp add: quot_char_def)
  then show ?thesis 
    by (msafe(inference))
qed

lemma (in equivalence) quot_class_mem:
  "A \<in> \<^qspace>{:X:}{:BS_sim:} \<turnstile> x \<in> A \<Leftrightarrow> x \<in> X \<and> A = \<^eclass>{:x:}{:BS_sim:}"
  apply (simp add: quot_set_mem equiv_class_mem set_eq_def)
  apply (elim exE conjE)
  apply (simp)
proof -
  fix y 
  show "\<^infopa>{:y:}{:BS_sim:}{:x:} \<Leftrightarrow> x \<in> X \<and> (\<forall> z \<bullet> \<^infopa>{:y:}{:BS_sim:}{:z:} \<Leftrightarrow> \<^infopa>{:x:}{:BS_sim:}{:z:})"
  proof (msafe(inference))
    assume c1: "\<^infopa>{:y:}{:BS_sim:}{:x:}"
    from c1 show "x \<in> X" by (simp add: relD2)
    {fix z assume c2: "\<^infopa>{:y:}{:BS_sim:}{:z:}"
    from c1 have "\<^infopa>{:x:}{:BS_sim:}{:y:}"
      by (rule symD)
    also have "\<^infopa>{:y:}{:BS_sim:}{:z:}" 
      by (rule c2)
    finally show "\<^infopa>{:x:}{:BS_sim:}{:z:}"
      by (this)}
    {fix z assume c2: "\<^infopa>{:x:}{:BS_sim:}{:z:}"
    have "\<^infopa>{:y:}{:BS_sim:}{:x:}"
      by (rule c1)
    also have "\<^infopa>{:x:}{:BS_sim:}{:z:}" 
      by (rule c2)
    finally show "\<^infopa>{:y:}{:BS_sim:}{:z:}"
      by (this)}
  next
    assume "x \<in> X" "\<forall> z \<bullet> \<^infopa>{:y:}{:BS_sim:}{:z:} \<Leftrightarrow> \<^infopa>{:x:}{:BS_sim:}{:z:}"
    then show "\<^infopa>{:y:}{:BS_sim:}{:x:}"
      by (simp add: reflD)
  qed
qed


lemma (in equivalence) quot_set_subset: 
   "CL_A \<subseteq> \<^qspace>{:X:}{:BS_sim:} \<Leftrightarrow> (\<exists> A \<bullet> CL_A = \<^qspace>{:A:}{:BS_sim:} \<and> A \<subseteq> X)" 
   (is "?LHS \<Leftrightarrow> ?RHS")
proof (rule iffI)
  assume "?RHS"
  then show "?LHS"
    by (auto simp add: quot_set_def equiv_class_def subset_def)+
next
  let ?A = "{A | A \<in> CL_A \<bullet> \<^qchar>{:A:}{:BS_sim:}}"
  assume b1: "?LHS"
  have "CL_A = \<^qspace>{:?A:}{:BS_sim:}"
  proof (rule subset_antisym)
    from b1 show "\<^qspace>{:?A:}{:BS_sim:} \<subseteq> CL_A"
      by (auto simp add: quot_set_def quot_char_class subset_def)
    show "CL_A \<subseteq> \<^qspace>{:?A:}{:BS_sim:}"
      apply (auto simp add: quot_set_def quot_char_class subset_def)
      apply (subst ex_simps')
      apply (simp del: ex_simps)
    proof -
      fix A assume d1: "A \<in> CL_A"
      from b1 d1 have "A = \<^eclass>{:\<^qchar>{:A:}{:BS_sim:}:}{:BS_sim:}"
        by (auto simp add: quot_char_class)
      with d1 show "\<exists> A' \<bullet> A = \<^eclass>{:\<^qchar>{:A':}{:BS_sim:}:}{:BS_sim:} \<and> A' \<in> CL_A"
        by (blast)
    qed
  qed
  moreover have "?A \<subseteq> X"
    apply (auto)
    using quot_char_mem ec_range 
    apply (auto dest!: b1 [THEN subsetD])
    done
  ultimately show "?RHS"
    by (auto)
qed

lemma (in equivalence) quot_class_set_cases:
  assumes a1: "CL_A \<subseteq> \<^qspace>{:X:}{:BS_sim:}" and
    a2: "\<And> A \<bullet> \<lbrakk> A \<subseteq> X; CL_A = \<^qspace>{:A:}{:BS_sim:} \<rbrakk> \<turnstile> R"
  shows "R"
proof -
  from a1 obtain A where "A \<subseteq> X" "CL_A = \<^qspace>{:A:}{:BS_sim:}"
    by (auto simp add: quot_set_subset)
  then show R by (rule a2)
qed

end
