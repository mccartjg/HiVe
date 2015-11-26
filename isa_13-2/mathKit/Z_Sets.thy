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
  Z_Sets

imports 
  Z_Exp
  Z_Rel_Chap

begin

section {* The Set Order *}

text {*

The empty set, universal set and subset relations~\cite[p 90]{Spivey:ZRef}\cite[p 95]{ZStand02}
are defined as operators in HOL. We make use of the existing, type-generic operators,
with appropriate Z-style syntax. 

*}

lemma Z_empty_def:
  "\<emptyset> = { x | \<False> }"
  by (auto)

lemma Z_UNIV_def:
  "\<univ> = { x | \<True> }"
  by (auto)

lemma Z_subseteq_def:
  "S \<subseteq> T \<defs> (\<forall> x \<bullet> x \<in> S \<Rightarrow> x \<in> T)"
  apply (rule eq_reflection)
  apply (auto)
  done

lemma Z_subset_def:
  "S \<subset> T \<defs> S \<subseteq> T \<and> S \<noteq> T"
  apply (rule eq_reflection)
  apply (auto)
  done

text {*

The non-empty power set~\cite[p 90]{Spivey:ZRef}\cite[p 96]{ZStand02} 
we define as an operator on sets.

*}

definition
  Pow1 :: "'a set \<rightarrow> 'a set set"
where
  Z_Pow1_def: "Pow1 X \<defs> { S | S \<in> \<pset> X \<and> S \<noteq> \<emptyset> }"

notation (xsymbols)
  Pow1 ("\<pset>\<subone>")

lemma Z_notin_empty:
  "x \<notin> \<emptyset>"
  by (auto)

lemma Z_subset_Pow:
  "S \<subseteq> T \<Leftrightarrow> S \<in> \<pset> T"
  by (auto)

lemma Z_subset_refl:
  "S \<subseteq> S"
  by (rule order_refl)

lemma Z_subset_antisym:
  "S \<subseteq> T \<and> T \<subseteq> S \<Leftrightarrow> S = T"
  by (auto intro: order_antisym) 

lemma Z_subset_trans:
  "S \<subseteq> T \<and> T \<subseteq> V \<Rightarrow> S \<subseteq> V"
  by (auto)

lemma Z_psubset_not_refl:
  "\<not>\<^zid>{:(S \<subset> S):}"
  by (auto)

lemma Z_psubset_chained:
  "\<not>(S \<subset> T \<and> T \<subset> S)"
  by (auto)

lemma Z_psubset_trans:
  "S \<subset> T \<and> T \<subset> V \<Rightarrow> S \<subset> V"
  by (auto)

lemma Z_empty_subset:
  "\<emptyset> \<subseteq> S"
  by (auto)

lemma Z_empty_psubset:
  "\<emptyset> \<subset> S \<Leftrightarrow> S \<noteq> \<emptyset>"
  by (auto)

lemma Z_Pow1_empty:
  "\<pset>\<subone> X = \<emptyset> \<Leftrightarrow> X = \<emptyset>"
  by (auto simp add: Z_Pow1_def) 

lemma Z_nempty_Pow1:
  "X \<noteq> \<emptyset> \<Leftrightarrow> X \<in> \<pset>\<subone> X"
  by (auto simp add: Z_Pow1_def)

section {* Set operators *}

text {*

Set union, intersection, and difference~\cite[p 91]{Spivey:ZRef}\cite[p 97]{ZStand02}
are already defined in HOL.
We make use of the existing, type-generic operators,
with appropriate Z-style syntax.

Difference is type generic in Isabelle, so we provide a specialised syntax for the
set instantiation.

*}

abbreviation
  set_minus :: "['a set, 'a set] \<rightarrow> 'a set" (infixl "\<setminus>" 55)
where
  "S \<setminus> T \<defs> S - T"

(*

BPM [130408]: I think this is now unnecessary.

syntax (xsymbols output)
  "_Z_Sets\<ZZ>setsub" :: "[logic, logic] \<fun> logic" (infixl "\<setminus>" 55)

syntax (zed)
  "_Z_Sets\<ZZ>setsub" :: "[logic, logic] \<fun> logic" (infixl "\<setminus>" 55)

translations
  "X \<setminus> Y" \<rightharpoonup> "(X::_ set) - Y"

typed_print_translation {*

let
  fun is_setT (Type("fun", [Type("fun", [_, Type("bool", _)]), _])) = true
   |  is_setT _ = false;
  fun trT' flag typ [a, b] = 
    if is_setT (typ) then
      Const("_Z_Sets\<ZZ>setsub", typ) $ a $ b
    else
      raise Match;
in
  [("\<^const>HOL.minus_class.minus", trT')]
end;
*}

*)

lemma Z_set_operations_def:
  "\<forall> S T \<bullet> 
     S \<union> T = { x | x \<in> S \<or> x \<in> T} \<and>
     S \<inter> T = { x | x \<in> S \<and> x \<in> T} \<and>
     S \<setminus> T = { x | x \<in> S \<and> x \<notin> T}"
  by (auto)

lemma Z_union_def:
  "S \<union> T = { x | x \<in> S \<or> x \<in> T}"
  by (auto simp add: Un_def)

lemma Z_inter_def:
  "S \<inter> T = { x | x \<in> S \<and> x \<in> T}"
  by (auto simp add: Int_def)

lemma Z_set_diff_def:
  "S \<setminus> T = { x | x \<in> S \<and> x \<notin> T}"
  by (auto)

lemma Z_set_identities:
  shows 
    set_union_idem: "S \<union> S = S" and
    set_union_empty: "S \<union> \<emptyset> = S" and
    set_inter_idem: "S \<inter> S = S" and
    set_diff_empty: "S \<setminus> \<emptyset> = S"
  by (auto)

lemma Z_empty_identities:
  shows 
    set_inter_empty: "S \<inter> \<emptyset> = \<emptyset>" and
    set_diff_set: "S \<setminus> S = \<emptyset>" and
    empty_diff: "\<emptyset> \<setminus> S = \<emptyset>"
  by (auto)

lemma Z_union_comm:
  "S \<union> T = T \<union> S"
  by (auto)

lemma Z_union_assoc:
  "S \<union> (T \<union> V) = (S \<union> T) \<union> V"
  by (auto)

lemma Z_inter_comm:
  "S \<inter> T = T \<inter> S"
  by (auto)

lemma Z_inter_assoc:
  "S \<inter> (T \<inter> V) = (S \<inter> T) \<inter> V"
  by (auto)

lemma Z_union_dist:
  "S \<union> (T \<inter> V) = (S \<union> T) \<inter> (S \<union> V)"
  by (auto)

lemma Z_inter_dist:
  "S \<inter> (T \<union> V) = (S \<inter> T) \<union> (S \<inter> V)"
  by (auto)

lemma Z_partition:
  "(S \<inter> T) \<union> (S \<setminus> T) = S"
  by (auto)

lemma Z_diff_disjoint:
  "(S \<setminus> T) \<inter> T = \<emptyset>"
  by (auto)

lemma Z_union_diff:
  "S \<union> (T \<setminus> V) = (S \<union> T) \<setminus> (V \<setminus> S)"
  by (auto)

lemma Z_inter_diff:
  "S \<inter> (T \<setminus> V) = (S \<inter> T) \<setminus> V"
  by (auto)

lemma Z_diff_diff1:
  "S \<setminus> (T \<setminus> V) = (S \<setminus> T) \<union> (S \<inter> V)"
  by (auto)

lemma Z_diff_diff2:
  "(S \<setminus> T) \<setminus> V = S \<setminus> (T \<union> V)"
  by (auto)

lemma Z_diff_union:
  "(S \<union> T) \<setminus> V = (S \<setminus> V) \<union> (T \<setminus> V)"
  by (auto)

lemma Z_diff_inter:
  "S \<setminus> (T \<inter> V) = (S \<setminus> T) \<union> (S \<setminus> V)"
  by (auto)

text {*

The symmetric set difference operator~\cite[p 97]{ZStand02} is not already defined in HOL.
We define it as a binary set operator.

*}

definition
  sym_diff :: "['a set, 'a set] \<rightarrow> 'a set"
where
  sym_diff_def: "sym_diff X Y \<defs> { x | x \<in> X \<xor> x \<in> Y }"

notation (xsymbols)
  sym_diff (infixl "\<ominus>" 60)

lemma Z_union_inter_diff_idem:
  "\<lch> S \<union> S \<chEq> S \<union> \<emptyset> \<chEq> S \<inter> S \<chEq> S \<setminus> \<emptyset> \<chEq> S \<rch>"
  by (simp add: set_union_idem set_union_empty set_inter_idem)

lemma Z_inter_diff_empty:
  "\<lch> S \<inter> \<emptyset> \<chEq> S \<setminus> S \<chEq> \<emptyset> \<setminus> S \<chEq> \<emptyset> \<rch>"
  by (simp add: set_inter_empty set_diff_set empty_diff)


text {*

Generalised union and intersection~\cite[p 92]{Spivey:ZRef}\cite[p 97]{ZStand02}
are defined as operators in HOL.
We make use of the existing, type-generic operators,
with appropriate Z-style syntax.

*}

lemma Z_Union_Inter_def:
  "\<forall> A \<bullet> 
    \<Union>A = { x | (\<exists> S | S \<in> A \<bullet> x \<in> S) } \<and>
    \<Inter>A = { x | (\<forall> S | S \<in> A \<bullet> x \<in> S) }"
  by (auto)

lemma Z_Union_def:
  "\<Union>A = { x | (\<exists> S | S \<in> A \<bullet> x \<in> S) }"
  by (auto simp add: Union_eq)

lemma Z_Inter_def:
  "\<Inter>A = { x | (\<forall> S | S \<in> A \<bullet> x \<in> S) }"
  by (auto simp add: Inter_eq)

lemma Z_Union_union_dist:
  "\<Union>(A \<union> B) = (\<Union>A) \<union> (\<Union>B)"
  by (auto)

lemma Z_Inter_union_dist:
  "\<Inter>(A \<union> B) = (\<Inter>A) \<inter> (\<Inter>B)"
  by (auto)

lemma Z_Union_empty:
  "\<Union>\<emptyset> = \<emptyset>"
  by (auto)

text {* 

Since generalised intersection is type generic, so the intersection of the empty 
set is the whole type, rather than the set generic.

*}

lemma Z_Inter_empty:
  "\<Inter>\<emptyset> = \<univ>"                                                            
  by (auto)

lemma Z_inter_Union_dist:
  "S \<inter> (\<Union>A) = (\<Union> T | T \<in> A \<bullet> S \<inter> T)"
  by (auto simp add: eind_def)

lemma Z_union_Inter_dist:
  "S \<union> (\<Inter>A) = (\<Inter> T | T \<in> A \<bullet> S \<union> T)"
  by (auto)+

lemma Z_Union_diff_dist:
  "(\<Union>A) \<setminus> S = (\<Union> T | T \<in> A \<bullet> T \<setminus> S)"
  by (auto)+

lemma Z_diff_Inter_dist:
  "S \<setminus> (\<Inter>A) = (\<Union> T | T \<in> A \<bullet> S \<setminus> T)"
  by (auto)+

lemma Z_diff_Union_dist:
  "A \<noteq> \<emptyset> \<Rightarrow> S \<setminus> (\<Union>A) = (\<Inter> T | T \<in> A \<bullet> S \<setminus> T)"
  by (auto)+

lemma Z_Inter_diff_dist:
  "A \<noteq> \<emptyset> \<Rightarrow> (\<Inter>A) \<setminus> S = (\<Inter> T | T \<in> A \<bullet> T \<setminus> S)"
  by (auto)+

lemma Z_Union_mono:
  "A \<subseteq> B \<Rightarrow> \<Union>A \<subseteq> \<Union>B"
  by (auto)

lemma Z_Inter_antimono:
  "A \<subseteq> B \<Rightarrow> \<Inter>B \<subseteq> \<Inter>A"
  by (auto)

section {* Finite Sets *}

text {*

We introduce finite subsets and finite non-empty 
subsets~\cite[p 111]{Spivey:ZRef}\cite[p 97]{ZStand02} as set operators.
We define them as restrictions of the existing HOL finite set operator,
giving the semantics.

*}

definition
  fin_pow :: "'a set \<rightarrow> 'a set set"
where
  fin_pow_def: "fin_pow X \<defs> { Y | Y \<in> \<pset> X \<and> finite Y }"

notation (xsymbols)
  fin_pow ("\<fset>")

definition
  fin_pow1 :: "'a set \<rightarrow> 'a set set"
where
  fin_pow1_def: "fin_pow1 X \<defs> \<fset> X \<setminus> {\<emptyset>}"

notation (zed)
  fin_pow1 ("\<fset>\<subone>")

lemma fin_pow_induct [induct set: fin_pow]:
  assumes 
    a1: "S \<in> \<fset> X" and
    a2: "P \<emptyset>" and
    a3: "\<And> x S \<bullet> \<lbrakk> S \<in> \<fset> X; P S; x \<in> X; x \<notin> S \<rbrakk>  \<turnstile> P (insert x S)"
  shows "P S"
proof -
  from a1 have
    b1: "finite S"
    by (simp add: fin_pow_def)
  from b1 have 
    "S \<subseteq> X \<Rightarrow> P S"
    apply (induct set: finite)
    using a2 a3
    apply (auto simp add: fin_pow_def)
    done
  with a1 show "P S"
    by (simp add: fin_pow_def)
qed

text {*

Finally we introduce some results about the set order~\cite[p 94]{Spivey:ZRef}.

*}

lemma Z_union_lub:
  shows 
    union_ub1: "S \<subseteq> S \<union> T" and
    union_ub2: "T \<subseteq> S \<union> T" and
    union_least: "S \<subseteq> W \<and> T \<subseteq> W \<Rightarrow> S \<union> T \<subseteq> W"
  by (auto)

lemma Z_Union_lub:
  shows 
    Union_ub: "S \<in> A \<Rightarrow> S \<subseteq> (\<Union>A)" and
    Union_least: "(\<forall> S | S \<in> A \<bullet> S \<subseteq> W) \<Rightarrow> (\<Union>A) \<subseteq> W"
  by (auto)

lemma Z_inter_glb:
  shows 
    inter_lb1: "S \<inter> T \<subseteq> S" and
    inter_lb2: "S \<inter> T \<subseteq> T" and
    inter_greatest: "W \<subseteq> S \<and> W \<subseteq> T \<Rightarrow> W \<subseteq> S \<inter> T"
  by (auto)

lemma Z_Inter_glb:
  shows 
    Z_Inter_lb: "S \<in> A \<Rightarrow> (\<Inter>A) \<subseteq> S" and
    Z_Inter_greatest: "(\<forall> S | S \<in> A \<bullet> W \<subseteq> S) \<Rightarrow> W \<subseteq> (\<Inter>A)"
  by (auto)

lemma diff_gdlb:
  shows 
    diff_lb: "S \<setminus> T \<subseteq> S" and
    diff_disjoint: "(S \<setminus> T) \<inter> T = \<emptyset>" and
    diff_greatest: "W \<subseteq> S \<and> W \<inter> T = \<emptyset> \<Rightarrow> W \<subseteq> S \<setminus> T"
  by (auto)

end
