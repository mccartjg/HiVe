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
  Z_Exp

imports
  Z_Rel_Chap

begin

section {* Preliminaries *}

text {*

In this section we introduce a number of rules quoted by Spivey~\cite{Spivey:ZRef} 
about the basic term constructors of the Z language.

Rules about equality~\cite[p. 68]{Spivey:ZRef}.

*}

lemma Z_sym: 
  "x = y \<Rightarrow> y = x"
  by (auto)

lemma Z_trans: 
  "x = y \<and> y = z \<Rightarrow> x = z"
  by (auto)

lemma Z_set_eq_def: 
  "S = T \<Leftrightarrow> (\<forall> x \<bullet> x \<in> S \<Leftrightarrow> x \<in> T)"
  by (auto)

lemma Z_member_congruence: 
  "x = y \<Leftrightarrow> (\<forall> S \<bullet> x \<in> S \<Leftrightarrow> y \<in> S)"
  apply (msafe(inference))
(* J: note improves!
  apply (msafe_no_assms(inference))
  apply (simp_all)
*)
proof -
  assume b1 [rule_format]: 
    "(\<forall> S \<bullet> x \<in> S \<Leftrightarrow> y \<in> S)"
  from b1 [of "{x}"] show 
    "x = y"
    by (auto)
qed

text {*

The negations of equality and set 
membership~\cite[p 89]{Spivey:ZRef}\cite[p 95]{ZStand02}
are already defined as syntactic operators in HOL.
We simply make use of these existing, type-generic operators. 

*}


lemma Z_neq_def:
  "x \<noteq> y \<defs> \<not>\<^zid>{:(x = y):}"
  by (auto)

lemma Z_nin_def:
  "x \<notin> S \<defs> \<not>\<^zid>{:(x \<in> S):}"
  by (auto)

lemma Z_neq_commute:
  "x \<noteq> y \<Rightarrow> y \<noteq> x"
  by (auto)

text {*

Rules about the boolean constants.

*}

lemma Z_FalseE:
  "\<False> \<Rightarrow> P"
  by (auto)

lemma Z_TrueI:
  "P \<Rightarrow> \<True>"
  by (auto)

lemma Z_bool_cases:
  "(P = \<True> \<Rightarrow> R) \<and> (P = \<False> \<Rightarrow> R) \<Rightarrow> R"
  by (auto)

text {*

Rules about the boolean connectives~\cite[p. 69]{Spivey:ZRef}.

*}

lemma Z_notI: "(P \<Rightarrow> \<False>) \<Rightarrow> \<not> P"
  by (auto)

lemma Z_conjI: "P \<Rightarrow> (Q \<Rightarrow> P \<and> Q)"
  by (auto)

lemma Z_disjI: "(P \<Rightarrow> P \<or> Q) \<and> (Q \<Rightarrow> P \<or> Q)"
  by (auto)

lemma Z_iffI: "(P \<Rightarrow> Q) \<and> (Q \<Rightarrow> P) \<Rightarrow> (P \<Leftrightarrow> Q)"
  by (msafe(inference))

lemma Z_ex1_def:
  "(\<exists>\<subone> x \<bullet> P x) \<Leftrightarrow> (\<exists> x \<bullet> P x \<and> (\<forall> y \<bullet> P y \<Rightarrow> y = x))"
  by (auto)

text {*

Rules about sets and products.

*}

lemma Z_prod_def:
  "X \<times> Y = { x y | x \<in> X \<and> y \<in> Y \<bullet> (x, y) }"
  by (auto)

lemma Z_coll_mem:
  "y \<in> { x | Q x \<bullet> t x } \<Leftrightarrow> (\<exists> x | Q x \<bullet> y = t x)"
  by (auto)

lemma Z_collect_the_equality:
  "P a \<Rightarrow> (\<forall> x \<bullet> P x \<Rightarrow> x = a) \<Rightarrow> (\<mu> x | P x) = a"
  apply (msafe(inference))
  apply (rule the_equality)
  apply (fast+)
  done

text {*

Rules about alternation.

*}

lemma Z_true_if:
  "P \<Rightarrow> \<if> P \<then> E_d_1 \<else> E_d_2 \<fi> = E_d_1"
  by (auto)

lemma Z_false_if:
  "\<not> P \<Rightarrow> \<if> P \<then> E_d_1 \<else> E_d_2 \<fi> = E_d_2"
  by (auto)

lemma Z_idem_if:
  "\<if> P \<then> E \<else> E \<fi> = E"
  by (auto)

text {*

The first and second operators~\cite[p 93]{Spivey:ZRef}\cite[p 98]{ZStand02}
are defined in HOL. These are not strictly
compatible with those defined in the Z Standard, since the Z operators
act on bindings rather than tuples, which are subsumed by the binding
structure in Z. Nevertheless we find it convenient to make use of the HOL
operators. As noted elsewhere, 
bindings are a difficult structure to model in HOL.

*}

lemma Z_fst_snd_def:
  "\<forall> x y \<bullet>
    \<fst> (x, y) = x \<and> 
    \<snd> (x, y) = y"
  by (auto)

lemma Z_fst_def:
  "\<fst> (x, y) \<defs> x"
  by (simp add: fst_conv)

lemma Z_snd_def:
  "\<snd> (x, y) \<defs> y"
  by (simp add: snd_conv)

lemma Z_tuple_cong:
  "(\<fst> p, \<snd> p) = p"
  by (auto) 

end
