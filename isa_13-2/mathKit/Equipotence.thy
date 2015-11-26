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

theory Equipotence 
  
imports 
  Z_Fun
  Orders
  Ordinal
begin

text {*

We follow Dugundji~\cite{Dugundji:Top}.

While ordinals are aimed at counting through sets, cardinals are aimed
at comparing their sizes. 
Two sets have the ``same size'', or formally speaking are {\em equipotent},
if there is bijection between them.
One set is {\em sub-equipotent} to another if there is a total injection 
between them.

*}

definition
  subequipotent :: "['a set, 'b set] \<rightarrow> \<bool>"
where
  subequipotent_def: "subequipotent A B \<defs> (\<exists> f \<bullet> f \<in> A \<zinj> B)" 

definition
  equipotent :: "['a set, 'b set] \<rightarrow> \<bool>"
where
  equipotent_def: "equipotent A B \<defs> (\<exists> f \<bullet> f \<in> A \<zbij> B)"

notation (xsymbols output)
  subequipotent ("card _ \<le> card _" [1000,1000] 1000)

notation (xsymbols)
  subequipotent  ("op \<preceq>") and
  subequipotent  ("(_/ \<preceq> _)"  [51, 51] 50) and
  equipotent (infixl "\<asymp>" 50)

notation (zed)
  subequipotent ("\<^sEP>{:_:}{:_:}") and
  equipotent ("\<^EP>{:_:}{:_:}")

abbreviation
  nequipotent  :: "['a set, 'b set] \<rightarrow> \<bool>"
where
  "nequipotent X Y \<equiv> \<not>(\<^EP>{:X:}{:Y:})"

notation (xsymbols)
  nequipotent (infixl "\<notasymp>" 50)

notation (zed)
  nequipotent ("\<^nEP>{:_:}{:_:}")

abbreviation
  subequipotent_ne  :: "['a set, 'b set] \<rightarrow> \<bool>"
where
  "subequipotent_ne X Y \<equiv> \<^sEP>{:X:}{:Y:} \<and> \<^nEP>{:X:}{:Y:}"

notation (xsymbols)
  subequipotent_ne  ("op \<prec>") and
  subequipotent_ne ("(_/ \<prec> _)"  [51, 51] 50)

notation (zed)
  subequipotent_ne ("\<^sEPne>{:_:}{:_:}")

lemma subequipotentI:
  assumes 
    a1: "f \<in> A \<zinj> B"
  shows 
    "\<^sEP>{:A:}{:B:}"
  using a1
  by (auto simp add: subequipotent_def)

lemma subequipotentE:
  assumes 
    a1: "\<^sEP>{:A:}{:B:}"
        "\<And> f \<bullet> f \<in> A \<zinj> B \<turnstile> R"
  shows "R"
  using a1
  by (auto simp add: subequipotent_def)

lemma subequipotent_eq_inj_on:
  "\<^sEP>{:A:}{:B:} \<Leftrightarrow> (\<exists> f \<bullet> inj_on f A \<and> f\<lparr>A\<rparr> \<subseteq> B)"
proof (msafe_no_assms(inference))
  assume
    b1: "\<^sEP>{:A:}{:B:}"
  then obtain f where
    b2: "f \<in> A \<zinj> B"
    by (auto simp add: subequipotent_def)
  have
    b3: "inj_on (\<opof> f) A" and
    b4: "(\<opof> f)\<lparr>A\<rparr> \<subseteq> B"
    by (auto intro!: inj_onI tinj_inj [OF b2] tinj_range [OF b2])
  then show
    "(\<exists> f \<bullet> inj_on f A \<and> f\<lparr>A\<rparr> \<subseteq> B)"
    by (auto)
next
  fix
    f
  assume
    b1: "inj_on f A" and 
    b2: "f\<lparr>A\<rparr> \<subseteq> B"
  from b1 [THEN graph_of_dresf_inj_on] b2 have 
    "A \<zdres> (\<graphof> f) \<in> A \<zinj> B"
    apply (mauto(fspace))
    apply (auto simp add: Image_def image_def dres_graph_of eind_def)
    done
  then show 
    "\<^sEP>{:A:}{:B:}"
    by (rule subequipotentI)
qed

lemma subepIinj_on:
  assumes 
    a1: "inj_on f A" and 
    a2: "f\<lparr>A\<rparr> \<subseteq> B"
  shows 
    "\<^sEP>{:A:}{:B:}"
  using a1 a2
  by (auto simp add: subequipotent_eq_inj_on)

lemma subepEinj_on:
  assumes 
    a1: "\<^sEP>{:A:}{:B:}" and
    a2: "\<And> f \<bullet> \<lbrakk> inj_on f A; f\<lparr>A\<rparr> \<subseteq> B \<rbrakk> \<turnstile> R"
  shows
    "R"
  using a1
  by (auto intro: a2 simp add: subequipotent_eq_inj_on)  

lemma subepIsurj:
  assumes a1: "A \<subseteq> f\<lparr>B\<rparr>"
  shows "\<^sEP>{:A:}{:B:}"
proof (rule subepIinj_on)
  let ?finv = "(\<olambda> x \<bullet> (\<some> y | y \<in> B \<and> f y = x))"
{ fix y 
  have "y \<in> f\<lparr>B\<rparr> ==> f(?finv y) = y"
    apply (rule conjunct2)
    apply (rule someI_ex)
    apply (auto)
   done
} note f_finv = this
{ fix x y
  assume eq: "?finv x = ?finv y"
      and x: "x \<in> f\<lparr>B\<rparr>"
      and y: "y \<in> f\<lparr>B\<rparr>"
  have "x = y"
  proof -
    have "f (?finv x) = f (?finv y)" using eq by simp
    thus ?thesis by (simp add: f_finv x y)
  qed                                                                           
} note finv_injective = this
  from a1 show "inj_on ?finv A"
    by (fast intro: inj_onI elim: finv_injective injD)
  from a1 show "(?finv)\<lparr>A\<rparr> \<subseteq> B"
    apply (auto simp add: image_def subset_def)
    apply (rule conjunct1)
    apply (rule someI_ex)
    apply (fast)
    done
qed

lemma univ_top:
  "\<^sEP>{:(A::'a set):}{:\<univ>-['a]:}"
proof -
  from Z_id_bij have "rel_id A \<in> A \<zinj> \<univ>-['a]"
    apply (mauto(fspace))
    apply (auto simp add: rel_id_def)
    done
  then show "\<^sEP>{:A:}{:\<univ>-['a]:}"
    by (rule subequipotentI)
qed

lemma empty_bot:
  "\<^sEP>{:\<emptyset>-['b]:}{:(A::'a set):}"
proof -
  have "\<emptyset> \<in> \<emptyset>-['b] \<zinj> A"
    by (mauto(fspace) mintro: fin_pfunI msimp add: fin_pfun_simp vacuous_inv empty_functional)
  then show 
    "\<^sEP>{:\<emptyset>-['b]:}{:A:}"
    by (rule subequipotentI)
qed

lemma empty_glb:
  "\<^sEP>{:(A::'a set):}{:\<emptyset>-['b]:} \<Leftrightarrow> A = \<emptyset>-['a]"
proof (auto simp add: empty_bot)
  fix 
    x :: "'a"
  assume
    b1: "\<^sEP>{:A:}{:\<emptyset>-['b]:}" and
    b2: "x \<in> A"
  from b1 obtain f where
    b3: "f \<in> A \<zinj> \<emptyset>-['b]" 
    by (auto simp add: subequipotent_def)
  from tinj_range [OF b3 b2] show
    "\<False>"
    by (auto)
qed

lemma equipotentI:
  assumes 
    a1: "f \<in> A \<zbij> B"
  shows 
    "\<^EP>{:A:}{:B:}"
  using a1
  by (auto simp add: equipotent_def)

lemma equipotentE:
  assumes 
    a1: "\<^EP>{:A:}{:B:}"
        "\<And> f \<bullet> f \<in> A \<zbij> B \<turnstile> R"
  shows 
    "R"
  using a1
  by (auto simp add: equipotent_def)

lemma equipotentD1:
  assumes 
    a1: "\<^EP>{:A:}{:B:}"
  shows  
    "\<^sEP>{:A:}{:B:}"
  using a1
  by (auto intro!: subequipotentI elim!: equipotentE)

lemma equipotentD2:
  assumes 
    a1: "\<^EP>{:A:}{:B:}"
  shows  
    "\<^sEP>{:B:}{:A:}"
  using a1
  by (auto intro!: subequipotentI elim!: equipotentE)

lemma equipotentIinj_on:
  assumes 
    a1: "inj_on f A" and 
    a2: "f\<lparr>A\<rparr> = B"
  shows 
    "\<^EP>{:A:}{:B:}"
proof -
  from a1 [THEN graph_of_dresf_inj_on] a2
  have "A \<zdres> (\<graphof> f) \<in> A \<zbij> B"
    apply (mauto(fspace))
    apply (auto simp add: Image_def image_def dres_graph_of)
    done
  then show ?thesis
    by (rule equipotentI)
qed

lemma equipotentIinj_on':
  assumes 
    a1: "inj_on f A"
  shows 
    "\<^EP>{:A:}{:f\<lparr>A\<rparr>:}"
  apply (rule equipotentIinj_on [OF a1])
  apply (auto)
  done

lemma subep_subsetE:
  assumes 
    a1: "\<^sEP>{:A:}{:B:}" and
    a2: "\<And> B' \<bullet> \<lbrakk> \<^EP>{:A:}{:B':}; B' \<subseteq> B \<rbrakk> \<turnstile> R"
  shows
    "R"
proof (rule subepEinj_on [OF a1])
  fix 
    f
  assume
    b1: "inj_on f A" and
    b2: "f\<lparr>A\<rparr> \<subseteq> B"
  from equipotentIinj_on' [OF b1] b2 show
    "R"
    by (rule a2)
qed

lemma equipotentEinj_on:
  assumes 
    a1: "\<^EP>{:A:}{:B:}" and
    a2: "\<And> f \<bullet> \<lbrakk> inj_on f A; f\<lparr>A\<rparr> = B \<rbrakk> \<turnstile> R"
  shows
    "R"
proof -
  from a1 obtain f where
    b1: "f \<in> A \<zbij> B"
    by (auto simp add: equipotent_def)
  have
    b2: "inj_on (\<opof> f) A" and
    b3: "(\<opof> f)\<lparr>A\<rparr> = B"
    apply (auto intro!: inj_onI bij_inj [OF b1] bij_range [OF b1] simp add: image_conv)
    apply (auto intro: bij_beta [OF b1, symmetric] simp add: bij_ran [OF b1, symmetric] bij_dom [OF b1, symmetric])
    done
  then show
    "R"
    by (rule a2)
qed

lemma equipotent_eq_inj_on:
  "\<^EP>{:A:}{:B:} \<Leftrightarrow> (\<exists> f \<bullet> inj_on f A \<and> f\<lparr>A\<rparr> = B)"
  by (auto elim: equipotentEinj_on intro: equipotentIinj_on)

lemma subset_subequipotent:
  assumes 
    a1: "A \<subseteq> B"
  shows 
    "\<^sEP>{:A:}{:B:}"
  apply (rule subequipotentI [of "\<zid> A"])
  apply (mauto(fspace))
  using a1
  apply (auto simp add: rel_id_def)
  done

text {*

The equipotence relation is a generalised form of equivalence relation.

*}

lemma 
  equipotent_refl: "\<^EP>{:A:}{:A:}"
proof -
  have "\<zid> A \<in> A \<zbij> A"
    by (auto simp add: rel_id_def fun_space_defs)
  then show ?thesis
    by (auto simp add: equipotent_def)
qed

lemma 
  equipotent_sym [sym]: "\<^EP>{:A:}{:B:} \<turnstile> \<^EP>{:B:}{:A:}"
  by (auto simp add: equipotent_def)

lemma equipotent_trans [trans]: 
  assumes 
    a1: "\<^EP>{:A:}{:B:}" and 
    a2: "\<^EP>{:B:}{:C:}"
  shows
    "\<^EP>{:A:}{:C:}"
proof -
  from a1 [unfolded equipotent_def] a2 [unfolded equipotent_def]
  show ?thesis
  proof (auto)
    fix f g
    assume 
      b1: "f \<in> A \<zbij> B" and 
      b2: "g \<in> B \<zbij> C"
    then have 
      "(f \<zfcomp> g) \<in> A \<zbij> C"
      by (auto)
    then show 
      ?thesis
      by (auto simp add: equipotent_def)
  qed
qed

lemma equipotent_substL:
  assumes
    a1: "\<^EP>{:A:}{:B:}"
  shows 
    "\<^EP>{:A:}{:C:} \<Leftrightarrow> \<^EP>{:B:}{:C:}"
  by (auto intro: equipotent_trans a1 a1 [THEN equipotent_sym])

lemma equipotent_substR:
  assumes
    a1: "\<^EP>{:A:}{:B:}"
  shows 
    "\<^EP>{:C:}{:A:} \<Leftrightarrow> \<^EP>{:C:}{:A:}"
  by (auto intro: equipotent_trans a1 a1 [THEN equipotent_sym])

lemma equipotent_cong: 
  assumes
    a1: "\<^EP>{:A:}{:A':}" and
    a2: "\<^EP>{:B:}{:B':}"
  shows 
    "\<^EP>{:A:}{:B:} \<Leftrightarrow> \<^EP>{:A':}{:B':}"
  by (auto intro: equipotent_trans [THEN equipotent_trans] a1 a1 [THEN equipotent_sym] a2 a2 [THEN equipotent_sym])

lemma equipotent_equiv:
  "equivalence \<univ>-['a set] equipotent"
  apply (simp_all add: equivalence_def')
  apply (auto simp add: op2rel_def rel_def)
  apply (rule equipotent_refl)
  apply (rule equipotent_sym, assumption)
  apply (rule equipotent_trans, assumption+)
  done

interpretation equi_equiv: equivalence "\<univ>-['a set]" "equipotent"
  by (rule equipotent_equiv)
 
text {*

We introduce some congruence style rules for breaking down equipotence goals involving image and cross product operators..

*}

lemma equipotent_prodL:
  assumes
    a1: "\<^EP>{:A:}{:B:}"
  shows
    "\<^EP>{:A \<times> C:}{:B \<times> C:}"
proof -
  from a1 obtain f where
    b1: "f \<in> A \<zbij> B"
    by (auto elim!: equipotentE)
  show
    "?thesis"
    apply (rule equipotentI [of "(\<glambda> (a, c) | (a, c) \<in> A \<times> C \<bullet> (f\<cdot>a, c))"])
    apply (mauto(fspace) msimp add: glambda_dom glambda_ran split_def)
    apply (msafe_no_assms(inference))
    using b1
    apply (auto elim!: bij_surjE [OF b1] simp add: bij_inj bij_range)
    done
qed
  
lemma equipotent_prod_com:
  "\<^EP>{:C \<times> A:}{:A \<times> C:}"
  apply (rule equipotentI [of "(\<glambda> (c, a) | (c, a) \<in> C \<times> A \<bullet> (a, c))"])
  apply (mauto(fspace) msimp add: glambda_dom glambda_ran split_def)
  apply (auto)
  done
  
lemma equipotent_prod_assoc:
  "\<^EP>{:(A \<times> B) \<times> C:}{:A \<times> (B \<times> C):}"
  apply (rule equipotentI [of "(\<glambda> ((a, b), c) | ((a, b), c) \<in> (A \<times> B) \<times> C \<bullet> (a, (b, c)))"])
  apply (mauto(fspace) msimp add: glambda_dom glambda_ran split_def)
  apply (auto)
  done

lemma equipotent_prodR:
  assumes
    a1: "\<^EP>{:A:}{:B:}"
  shows
    "\<^EP>{:C \<times> A:}{:C \<times> B:}"
  apply (rule equipotent_trans)
  apply (rule equipotent_trans)
  apply (rule equipotent_prod_com)
  apply (rule equipotent_prodL [OF a1])
  apply (rule equipotent_prod_com)
  done

lemma equipotent_prod_cong:
  assumes
    a1: "\<^EP>{:A:}{:A':}" and
    a2: "\<^EP>{:B:}{:B':}"
  shows
    "\<^EP>{:A \<times> B:}{:A' \<times> B':}"
  apply (rule equipotent_trans)
  apply (rule equipotent_prodL [OF a1])
  apply (rule equipotent_prodR [OF a2])
  done

lemma [mintro!(wind)]:
  assumes
    a1: "\<^EP>{:A:}{:A':}"
  shows
    "\<^EP>{:A \<times> B:}{:A' \<times> B:}"
  by (rule equipotent_prod_cong [OF a1 equipotent_refl])

lemma [mintro!(wind)]:
  assumes
    a1: "\<^EP>{:B:}{:B':}"
  shows
    "\<^EP>{:A \<times> B:}{:A \<times> B':}"
  by (rule equipotent_prod_cong [OF equipotent_refl a1])


lemma equipotent_prod_singletonL:
  assumes
    a1: "\<^EP>{:B:}{:B':}"
  shows
  "\<^EP>{:{x} \<times> B:}{:B':}"
  apply (rule equipotent_trans [OF _ a1])
  apply (rule equipotentI [of "(\<glambda> (a, b) | a = x \<and> b \<in> B \<bullet> b)"])
  apply (mauto(fspace) msimp add: glambda_dom glambda_ran split_def)
  apply (auto)
  done

lemma equipotent_prod_singletonR:
  assumes
    a1: "\<^EP>{:A:}{:A':}"
  shows
  "\<^EP>{:A \<times> {x}:}{:A':}"
  apply (rule equipotent_trans [OF _ a1])
  apply (rule equipotentI [of "(\<glambda> (a, b) | a \<in> A \<and> b = x \<bullet> a)"])
  apply (mauto(fspace) msimp add: glambda_dom glambda_ran split_def)
  apply (auto)
  done

lemma equipotent_prod_singleton_congL:
  assumes
    a1: "\<^EP>{:A:}{:{True}:}"
  shows
  "\<^EP>{:A \<times> B:}{:B:}"
  apply (rule equipotent_trans)
  apply (rule equipotent_prod_cong [OF a1 equipotent_refl])
  apply (rule equipotent_prod_singletonL [OF equipotent_refl])
  done

lemma equipotent_prod_singleton_congR:
  assumes
    a1: "\<^EP>{:A:}{:{True}:}"
  shows
  "\<^EP>{:B \<times> A:}{:B:}"
  apply (rule equipotent_trans)
  apply (rule equipotent_prod_cong [OF equipotent_refl a1])
  apply (rule equipotent_prod_singletonR [OF equipotent_refl])
  done

text {*

The sub-equipotence relation is a generalised form of partial ordering.

*}

lemma subequipotent_refl: "\<^sEP>{:A:}{:A:}"
proof -
  have "\<zid> A \<in> A \<zinj> A"
    by (auto simp add: rel_id_def fun_space_defs)
  then show ?thesis
    by (auto simp add: subequipotent_def)
qed

lemma subequipotent_trans [trans]: 
  assumes a1: "\<^sEP>{:A:}{:B:}" and a2: "\<^sEP>{:B:}{:C:}"
  shows "\<^sEP>{:A:}{:C:}"
proof -
  from a1 [unfolded subequipotent_def] a2 [unfolded subequipotent_def]
  show ?thesis
  proof (auto)
    fix f g
    assume b1: "f \<in> A \<zinj> B" and b2: "g \<in> B \<zinj> C"
    then have "(f \<zfcomp> g) \<in> A \<zinj> C"
      by (auto)
    then show ?thesis
      by (auto simp add: subequipotent_def)
  qed
qed

lemma subeq_eq_trans [trans]:
  assumes a1: "\<^sEP>{:A:}{:B:}" and a2: "\<^EP>{:B:}{:C:}"
  shows "\<^sEP>{:A:}{:C:}"
  apply (rule subequipotent_trans)
  apply (rule a1)
  apply (rule equipotentD1)
  apply (rule a2)
  done

lemma eq_subeq_trans [trans]:
  assumes a1: "\<^EP>{:A:}{:B:}" and a2: "\<^sEP>{:B:}{:C:}"
  shows "\<^sEP>{:A:}{:C:}"
  apply (rule subequipotent_trans)
  apply (rule equipotentD1)
  apply (rule a1)
  apply (rule a2)
  done


interpretation cardpre: preorder "\<univ>-['a set]" "subequipotent"
  apply (rule preorder_intros)
  apply (simp)
  apply (simp add: op2rel_def rel_def)
  apply (rule subequipotent_refl)
  apply (rule subequipotent_trans)
  apply (assumption+)
  done

lemma subeq_prodL:
  assumes 
    a1: "\<^sEP>{:A:}{:A':}"
  shows
    "\<^sEP>{:A \<times> B:}{:A' \<times> B:}"
proof - 
  from a1 obtain f where
    b1: "f \<in> A \<zinj> A'"
    by (auto simp add: subequipotent_def)
  let ?g = "(\<glambda> (a, b) | a \<in> A \<and> b \<in> B \<bullet> (f\<cdot>a, b))"
  have
    "?g \<in> (A \<times> B) \<zinj> (A' \<times> B)"
    apply (mauto(fspace) msimp add: split_def)
    apply (auto intro: tinj_inj [OF b1] tinj_range [OF b1] tinj_dom [OF b1] simp add: glambda_dom glambda_ran)
    done
  then show
    "?thesis"
    by (rule subequipotentI)
qed

lemma subeq_prod_com:
  "\<^sEP>{:A \<times> B:}{:B \<times> A:}"
  apply (rule subequipotentI [of "(\<glambda> (a, b) | a \<in> A \<and> b \<in> B \<bullet> (b, a))"])
  apply (mauto(fspace) msimp add: split_def)
  apply (auto simp add: glambda_dom glambda_ran)
  done

lemma subeq_prod_cong:
  assumes 
    a1: "\<^sEP>{:A:}{:A':}" and
    a2: "\<^sEP>{:B:}{:B':}"
  shows
    "\<^sEP>{:A \<times> B:}{:A' \<times> B':}"
  apply (rule subequipotent_trans)
  apply (rule subeq_prodL [OF a1])
  apply (rule subequipotent_trans)
  apply (rule subeq_prod_com)
  apply (rule subequipotent_trans)
  apply (rule subeq_prodL [OF a2])
  apply (rule subeq_prod_com)
  done

lemma [mintro!(wind)]:
  assumes
    a1: "\<^sEP>{:A:}{:A':}"
  shows
    "\<^sEP>{:A \<times> B:}{:A' \<times> B:}"
  by (rule subeq_prod_cong [OF a1 subequipotent_refl])

lemma [mintro!(wind)]:
  assumes
    a1: "\<^sEP>{:B:}{:B':}"
  shows
    "\<^sEP>{:A \<times> B:}{:A \<times> B':}"
  by (rule subeq_prod_cong [OF subequipotent_refl a1])

text {*

The Schroeder-Bernstein Theorem, following a proof outline due to Joe Hurd.

*}

lemma subequipotent_antisym [trans]: 
  assumes a1: "\<^sEP>{:A:}{:B:}" and a2: "\<^sEP>{:B:}{:A:}"
  shows "\<^EP>{:A:}{:B:}"
proof -
txt {* 
First we reduce the result to the case of @{text "B"} a subset of 
@{text A}, showing this to be enough to establish the general result.
*}
  { 
  presume b1:
    "\<forall> Y | Y \<subseteq> A \<and> \<^sEP>{:A:}{:Y:} \<bullet> \<^EP>{:A:}{:Y:}"
  from a1 a2 show ?thesis
  proof (elim subequipotentE)
    fix f g
    assume c1: "f \<in> A \<zinj> B" and c2: "g \<in> B \<zinj> A"
    from c2 have c3: "g\<zlImg>B\<zrImg> \<subseteq> A"
      by (mauto(fspace))
    from c1 c2 c3 have c4: "f \<zfcomp> g \<in> A \<zinj> g\<zlImg>B\<zrImg>"
      apply (intro fcomp_in_tinjI2)
      apply (mauto(fspace))
      done
    from c3 c4 [THEN subequipotentI]
    have c5: "\<^EP>{:A:}{:g\<zlImg>B\<zrImg>:}"
      by (rule b1 [rule_format])
    then obtain h where c6: "h \<in> A \<zbij> g\<zlImg>B\<zrImg>"
      by (auto elim!: equipotentE)
    from c2 have c7: "g \<in> B \<zbij> g\<zlImg>B\<zrImg>"
      apply (intro in_bijI)
      apply (mauto(fspace))
      done
    from c6 c7 have c8: "h \<zfcomp> g\<^sup>\<sim> \<in> A \<zbij> B"
      by (auto)
    then show ?thesis
      by (rule equipotentI)
  qed
  }
txt {*
Now we must prove the special case.
*}
  show
    "\<forall> Y | Y \<subseteq> A \<and> \<^sEP>{:A:}{:Y:} \<bullet> \<^EP>{:A:}{:Y:}"
  proof (msafe_no_assms(inference))
    fix Y 
    assume c1: "Y \<subseteq> A" and c2: "\<^sEP>{:A:}{:Y:}"
    from c2 obtain f where c3: "f \<in> A \<zinj> Y"
      by (auto elim!: subequipotentE)
txt {*
The key insight is to distinguish between elements of @{text Y}
that are not related
through @{text "f"} back to @{text "A - Y"}, for which the identity relation
is a suitable bijection, and those that are related back to @{text "A - Y"},
for which @{text f} is a suitable bijection. The two bijections are then pasted 
together to give the complete bijection.
*}
    let ?X = "(f^*)\<zlImg>A - Y\<zrImg>"
    let ?h = "(\<glambda> x | x \<in> A \<bullet> \<if> x \<in> ?X \<then> f\<cdot>x \<else> x \<fi>)"
    from c3 [THEN dr_tinjD3] subset_trans [OF c3 [THEN dr_tinjD5] c1]
    have c4: "?X \<subseteq> A"
      apply (auto simp add: subset_def)
      apply (cases set: rtrancl)
      apply (assumption)
      apply (auto)
      done
    from c4 have c5: "\<forall> x | x \<in> ?X \<bullet> ?h\<cdot>x = f\<cdot>x"
      by (auto simp add: subset_def glambda_beta)
    have c6: "\<forall> x | x \<in> A - ?X \<bullet> ?h\<cdot>x = x"
      by (auto simp add: glambda_beta)
    have c7: "f\<zlImg>?X\<zrImg> \<subseteq> ?X"
      by (auto simp add: Image_def)
    have "?h \<in> A \<zbij> Y"
      apply (rule in_bijIa)
      apply (rule in_pinjI)
      apply (mauto(fspace))
      apply (simp_all add: glambda_dom)
    proof -
      show d1: "\<zran> ?h \<subseteq> Y"
      proof (auto simp add: glambda_mem)
        fix x 
        assume e1: "x \<in> A"
        with c3 show "f\<cdot>x \<in> Y"
          by (auto intro!: tfun_range)
      next
        fix x 
        assume e1: "x \<in> A" and e2: "x \<notin> ?X"
        from e2 have "x \<notin> A - Y"
          by (auto)
        with e1 show "x \<in> Y"
          by (auto)
      qed
      {
      fix x_d_1 x_d_2 y 
      assume e1: "(x_d_1 \<mapsto> y) \<in> ?h" and e2: "(x_d_2 \<mapsto> y) \<in> ?h"
      from e1 have e3: "?h\<cdot>x_d_1 = y"
        by (rule functional_beta [OF glambda_functional])
      from e2 have e4: "?h\<cdot>x_d_2 = y"
        by (rule functional_beta [OF glambda_functional]) 
      show "x_d_1 = x_d_2"
         apply (cases "x_d_1 \<in> ?X")
         apply (cases "x_d_2 \<in> ?X")
      proof -
        assume f1: "x_d_1 \<in> ?X" and f2: "x_d_2 \<in> ?X"
        show "x_d_1 = x_d_2"
        proof (rule pinj_inj)
          from c3 show "f \<in> A \<zpinj> Y"
            by (rule tinj_pinj)
          from f1 c3 [THEN dr_tinjD3] subset_trans [OF c3 [THEN dr_tinjD5] c1]
          show g1: "x_d_1 \<in> \<zdom> f"
            apply (simp add: Image_def)
            apply (msafe_no_assms(inference))
            apply (cases set: rtrancl)
            apply (assumption)
            apply (auto)
            done
          from f2 c3 [THEN dr_tinjD3] subset_trans [OF c3 [THEN dr_tinjD5] c1]
          show g2: "x_d_2 \<in> \<zdom> f"
            apply (simp add: Image_def)
            apply (msafe_no_assms(inference))
            apply (cases set: rtrancl)
            apply (assumption)
            apply (auto)
            done
          from g1 f1 c3 [THEN dr_tinjD3] have "f\<cdot>x_d_1 = ?h\<cdot>x_d_1"
            by (simp add: glambda_beta)
          also from e3 have "\<dots> = y"
            by (simp)
          also from e4 have "\<dots> = ?h\<cdot>x_d_2"
            by (simp)
          also from g2 f2 c3 [THEN dr_tinjD3] have "\<dots> = f\<cdot>x_d_2"
            by (simp add: glambda_beta)
          finally show "f\<cdot>x_d_1 = f\<cdot>x_d_2"
            by (this)
        qed
      next
        assume f1: "x_d_1 \<notin> ?X"
        from e1 [THEN DomainI] have f2: "x_d_1 \<in> A"
          by (simp add: glambda_dom)       
        with f1 e3 have "x_d_1 = y"
           by (simp add: glambda_beta)
        with e2 have f3: "(x_d_2 \<mapsto> x_d_1) \<in> ?h"
           by (simp)
        from f1 c7 have f4: "x_d_1 \<notin> f\<zlImg>?X\<zrImg>"
           by (auto)
        from f3 f4
        show "x_d_1 = x_d_2"
          apply (simp add: glambda_mem)
          apply (msafe_no_assms(inference))
          apply (simp)
          apply (elim notE)
          apply (rule ImageI)
          apply (rule functional_appl)
          apply (rule c3 [THEN dr_tinjD1])
          apply (simp add: c3 [THEN dr_tinjD3])
          apply (assumption)
          done
      next
        assume f1: "x_d_2 \<notin> ?X"
        from e2 [THEN DomainI] have f2: "x_d_2 \<in> A"
          by (simp add: glambda_dom)       
        with f1 e4 have "x_d_2 = y"
           by (simp add: glambda_beta)
        with e1 have f3: "(x_d_1 \<mapsto> x_d_2) \<in> ?h"
           by (simp)
        from f1 c7 have f4: "x_d_2 \<notin> f\<zlImg>?X\<zrImg>"
           by (auto)
        from f3 f4
        show "x_d_1 = x_d_2"
          apply (simp add: glambda_mem)
          apply (msafe_no_assms(inference))
          apply (simp)
          apply (elim notE)
          apply (rule ImageI)
          apply (rule functional_appl)
          apply (rule c3 [THEN dr_tinjD1])
          apply (simp add: c3 [THEN dr_tinjD3])
          apply (assumption)
          done
      qed
      }
      from d1 show "\<zran> ?h = Y"
      proof (auto)
        fix x assume e1: "x \<in> Y"
        show "x \<in> \<zran> ?h"
        proof (cases "x \<in> ?X")
          assume f1: "x \<in> ?X"
          then show "x \<in> \<zran> ?h"
            apply (auto)
            apply (cases set: rtrancl)
            apply (assumption)
            apply (simp add: e1)
          proof -
            fix y z 
            assume g1: "y \<in> A" "y \<notin> Y" "(y \<mapsto> z) \<in> f\<^sup>*" and g2: "(z \<mapsto> x) \<in> f"
            from g1 have g3: "z \<in> ?X"
              by (auto simp add: Image_def)
            with c4 have "(z \<mapsto> x) \<in> ?h"
              apply (auto simp add: glambda_mem)
              apply (rule functional_beta [THEN sym])
              apply (rule c3 [THEN dr_tinjD1])
              apply (rule g2)
              done
            then show "x \<in> \<zran> ?h" 
              by (auto)
          qed
        next
          assume f1: "x \<notin> ?X"
          with c1 e1 have "(x \<mapsto> x) \<in> ?h"
            by (auto simp add: glambda_mem)
          then show "x \<in> \<zran> ?h" 
            by (auto)
        qed
      qed
    qed
    then show "\<^EP>{:A:}{:Y:}"  
      by (rule equipotentI)
  qed
qed

lemma equipotent_iff:
  "\<^EP>{:A:}{:B:} \<Leftrightarrow> \<^sEP>{:A:}{:B:} \<and> \<^sEP>{:B:}{:A:}"
  by (blast intro: subequipotent_antisym equipotentD1 equipotentD2)

lemma epI_inj_surj:
  assumes a1: "inj_on f A" "f\<lparr>A\<rparr> \<subseteq> B"
    and a2: "B \<subseteq> g\<lparr>A\<rparr>"
  shows "\<^EP>{:A:}{:B:}"
  apply (rule subequipotent_antisym)
  apply (rule subepIinj_on)
  apply (rule a1)
  apply (rule a1)
  apply (rule subepIsurj)
  apply (rule a2)
  done

lemma inj_on_equipotent_image_inject:
  assumes 
    a1: "inj_on f A" and
    a2: "inj_on g B"
  shows
    "\<^EP>{:f\<lparr>A\<rparr>:}{:g\<lparr>B\<rparr>:} \<Leftrightarrow> \<^EP>{:A:}{:B:}"
proof (rule iffI)
  assume
    b1: "\<^EP>{:f\<lparr>A\<rparr>:}{:g\<lparr>B\<rparr>:}"
  have 
    "\<^EP>{:A:}{:f\<lparr>A\<rparr>:}"
    by (rule equipotentIinj_on' [OF a1])
  also have 
    "\<^EP>{:f\<lparr>A\<rparr>:}{:g\<lparr>B\<rparr>:}"
    by (rule b1)
  also have 
    "\<^EP>{:g\<lparr>B\<rparr>:}{:B:}"
    apply (rule equipotent_sym)
    apply (rule equipotentIinj_on' [OF a2])
    done
  finally show
    "\<^EP>{:A:}{:B:}"
    by (this)
next
  assume 
    b1: "\<^EP>{:A:}{:B:}"
  have
    "\<^EP>{:f\<lparr>A\<rparr>:}{:A:}"
    apply (rule equipotent_sym)
    apply (rule equipotentIinj_on' [OF a1])
    done
  also have 
    "\<^EP>{:A:}{:B:}"
    by (rule b1)
  also have
    "\<^EP>{:B:}{:g\<lparr>B\<rparr>:}"
    by (rule equipotentIinj_on' [OF a2])
  finally show
    "\<^EP>{:f\<lparr>A\<rparr>:}{:g\<lparr>B\<rparr>:}"
    by (this)
qed

lemmas inj_on_equipotent_image_cong = inj_on_equipotent_image_inject [THEN iffD2]

lemma inj_on_equipotent_image:
  assumes
    a1: "inj_on f A" and
    a2: "\<^EP>{:A:}{:A':}"
  shows
    "\<^EP>{:f\<lparr>A\<rparr>:}{:A':}"
  apply (rule equipotent_trans [OF _ a2])
  apply (rule equipotent_sym)
  apply (rule equipotentIinj_on' [OF a1])
  done

lemma inj_equipotent_image:
  assumes
    a1: "inj f" and
    a2: "\<^EP>{:A:}{:A':}"
  shows
    "\<^EP>{:f\<lparr>A\<rparr>:}{:A':}"
  apply (rule inj_on_equipotent_image [OF a1 [THEN subset_inj_on] a2])
  apply (auto)
  done

lemma inj_inj_equipotent_image_inject:
  assumes 
    a1: "inj f" and
    a2: "inj g" 
  shows
    "\<^EP>{:f\<lparr>A\<rparr>:}{:g\<lparr>B\<rparr>:} \<Leftrightarrow> \<^EP>{:A:}{:B:}"
  apply (rule inj_on_equipotent_image_inject)
  using a1 a2
  apply (auto intro: subset_inj_on)
  done

lemmas inj_inj_equipotent_image_cong = inj_inj_equipotent_image_inject [THEN iffD2]

lemma inj_equipotent_image_inject:
  assumes 
    a1: "inj f" 
  shows
    "\<^EP>{:f\<lparr>A\<rparr>:}{:f\<lparr>B\<rparr>:} \<Leftrightarrow> \<^EP>{:A:}{:B:}"
  apply (rule inj_on_equipotent_image_inject)
  using a1
  apply (auto intro: subset_inj_on)
  done

lemmas inj_equipotent_image_cong = inj_equipotent_image_inject [THEN iffD2]

lemma inj_on_subequipotent_image_inject:
  assumes 
    a1: "inj_on f A" and
    a2: "inj_on g B"
  shows
    "\<^sEP>{:f\<lparr>A\<rparr>:}{:g\<lparr>B\<rparr>:} \<Leftrightarrow> \<^sEP>{:A:}{:B:}"
proof (rule iffI)
  assume
    b1: "\<^sEP>{:f\<lparr>A\<rparr>:}{:g\<lparr>B\<rparr>:}"
  have 
    "\<^EP>{:A:}{:f\<lparr>A\<rparr>:}"
    apply (rule equipotentIinj_on [OF a1])
    apply (simp)
    done
  also have 
    "\<^sEP>{:f\<lparr>A\<rparr>:}{:g\<lparr>B\<rparr>:}"
    by (rule b1)
  also have 
    "\<^EP>{:g\<lparr>B\<rparr>:}{:B:}"
    apply (rule equipotent_sym)
    apply (rule equipotentIinj_on [OF a2])
    apply (simp)
    done
  finally show
    "\<^sEP>{:A:}{:B:}"
    by (this)
next
  assume 
    b1: "\<^sEP>{:A:}{:B:}"
  have
    "\<^EP>{:f\<lparr>A\<rparr>:}{:A:}"
    apply (rule equipotent_sym)
    apply (rule equipotentIinj_on [OF a1])
    apply (simp)
    done
  also have 
    "\<^sEP>{:A:}{:B:}"
    by (rule b1)
  also have
    "\<^EP>{:B:}{:g\<lparr>B\<rparr>:}"
    apply (rule equipotentIinj_on [OF a2])
    apply (simp)
    done
  finally show
    "\<^sEP>{:f\<lparr>A\<rparr>:}{:g\<lparr>B\<rparr>:}"
    by (this)
qed

lemmas inj_on_subequipotent_image_cong = inj_on_subequipotent_image_inject [THEN iffD2]

lemma inj_inj_subequipotent_image_inject:
  assumes 
    a1: "inj f" and
    a2: "inj g" 
  shows
    "\<^sEP>{:f\<lparr>A\<rparr>:}{:g\<lparr>B\<rparr>:} \<Leftrightarrow> \<^sEP>{:A:}{:B:}"
  apply (rule inj_on_subequipotent_image_inject)
  using a1 a2
  apply (auto intro: subset_inj_on)
  done

lemmas inj_inj_subequipotent_image_cong = inj_inj_subequipotent_image_inject [THEN iffD2]

lemma inj_subequipotent_image_inject:
  assumes 
    a1: "inj f" 
  shows
    "\<^sEP>{:f\<lparr>A\<rparr>:}{:f\<lparr>B\<rparr>:} \<Leftrightarrow> \<^sEP>{:A:}{:B:}"
  apply (rule inj_on_subequipotent_image_inject)
  using a1
  apply (auto intro: subset_inj_on)
  done

lemmas inj_subequipotent_image_cong = inj_subequipotent_image_inject [THEN iffD2]

lemma subequipotent_iUnion:
  assumes
    a1: "Disjoint { i | i \<in> I \<bullet> \<P> i }" and
    a2: "Disjoint { i | i \<in> I \<bullet> \<Q> i }" and
    a3: "inj_on \<P> I" and
    a4: "inj_on \<Q> I" and
    a5: "(\<forall> i | i \<in> I \<bullet> \<^sEP>{:\<P> i:}{:\<Q> i:})"
  shows
    "\<^sEP>{:(\<Union> i | i \<in> I \<bullet> \<P> i):}{:(\<Union> i | i \<in> I \<bullet> \<Q> i):}"
proof -
  from a5 obtain F where
    b1 [rule_format]: "(\<forall> i | i \<in> I \<bullet> F i \<in> \<P> i \<zinj> \<Q> i)"
    by (auto simp add: subequipotent_def qual_ax_choice_eq)
  have
    b2: "(\<Union> i | i \<in> I \<bullet> F i) \<in> (\<Union> i | i \<in> I \<bullet> \<P> i) \<zinj> (\<Union> i | i \<in> I \<bullet> \<Q> i)"
  proof (mauto(fspace))
    show
      "functional (\<Union> i | i \<in> I \<bullet> F i)"
      apply (rule disj_rel_Union_functional')
      using b1 [THEN tinj_functional] b1 [THEN tinj_dom]
      apply (simp)
      apply (simp add: b1 [THEN tinj_dom])
      apply (rule a1 [THEN DisjointD1])
      apply (auto simp add: inj_on_iff [OF a3])
      done
  next
    show
      "functional ((\<Union> i | i \<in> I \<bullet> F i)\<^sup>\<sim>)"
      apply (simp add: converse_Union eind_def eind_comp)
      apply (simp add: eind_norm [of "(\<olambda> x \<bullet> Union (Collect x))"])
      apply (rule disj_rel_Union_functional')
      using b1 [THEN tinj_inv_functional] Z_inverse_dom b1 [THEN tinj_ran]
      apply (simp)
      apply (simp add: Z_inverse_dom)
      apply (rule 
        disjoint_left_mono 
          [OF b1 [THEN tinj_ran], 
           OF _ disjoint_right_mono [OF b1 [THEN tinj_ran]],
           OF _ _ DisjointD1 [OF a2]])
      apply (auto simp add: inj_on_iff [OF a4])
      done
  next
    show
      "\<zdom> (\<Union> i | i \<in> I \<bullet> F i) = (\<Union> i | i \<in> I \<bullet> \<P> i)"
      using b1 [THEN tinj_dom]
      by (auto simp add: rel_Union_dom eind_def eind_comp)
  next
    show
      "\<zran> (\<Union> i | i \<in> I \<bullet> F i) \<subseteq> (\<Union> i | i \<in> I \<bullet> \<Q> i)"
      using b1 [THEN tinj_ran]
      by (auto simp add: eind_def)        
  qed
  then show
    "?thesis"
    by (rule subequipotentI)
qed

lemma subequipotent_iUnion':
  assumes
    a1: "Disjoint \<P>" and
    a2: "Disjoint { P | P \<in> \<P> \<bullet> \<Q> P }" and
    a3: "inj_on \<Q> \<P>" and
    a4: "(\<forall> P | P \<in> \<P> \<bullet> \<^sEP>{:P:}{:\<Q> P:})"
  shows
    "\<^sEP>{:(\<Union>\<P>):}{:(\<Union> P | P \<in> \<P> \<bullet> \<Q> P):}"
  using subequipotent_iUnion [OF _ a2 inj_on_id [of "\<P>"] a3] a1 a4
  by (simp add: eind_def)  

lemma subequipotent_iUnion'':
  assumes
    a1: "Disjoint \<P>" and
    a2: "Disjoint { P | P \<in> \<P> \<bullet> \<Q> P }" and
    a3: "inj_on \<Q> \<P>" and
    a4: "(\<forall> P | P \<in> \<P> \<bullet> \<^sEP>{:\<Q> P:}{:P:})"
  shows
    "\<^sEP>{:(\<Union> P | P \<in> \<P> \<bullet> \<Q> P):}{:(\<Union>\<P>):}"
  using subequipotent_iUnion [OF a2 _ a3 inj_on_id [of "\<P>"]] a1 a4
  by (simp add: eind_def)

lemma equipotent_iUnion:
  assumes
    a1: "Disjoint { i | i \<in> I \<bullet> \<P> i }" and
    a2: "Disjoint { i | i \<in> I \<bullet> \<Q> i }" and
    a3: "inj_on \<P> I" and
    a4: "inj_on \<Q> I" and
    a5: "(\<forall> i | i \<in> I \<bullet> \<^EP>{:\<P> i:}{:\<Q> i:})"
  shows
    "\<^EP>{:(\<Union> i | i \<in> I \<bullet> \<P> i):}{:(\<Union> i | i \<in> I \<bullet> \<Q> i):}"
  apply (rule subequipotent_antisym)
  apply (rule subequipotent_iUnion [OF a1 a2 a3 a4])
  apply (simp add: a5 [rule_format, THEN equipotentD1])
  apply (rule subequipotent_iUnion [OF a2 a1 a4 a3])
  apply (simp add: a5 [rule_format, THEN equipotent_sym, THEN equipotentD1])
  done

lemma equipotent_iUnion':
  assumes
    a1: "Disjoint \<P>" and
    a2: "Disjoint { P | P \<in> \<P> \<bullet> \<Q> P }" and
    a3: "inj_on \<Q> \<P>" and
    a4: "(\<forall> P | P \<in> \<P> \<bullet> \<^EP>{:P:}{:\<Q> P:})"
  shows
    "\<^EP>{:(\<Union>\<P>):}{:(\<Union> P | P \<in> \<P> \<bullet> \<Q> P):}"
  using equipotent_iUnion [OF _ a2 inj_on_id [of "\<P>"] a3] a1 a4
  by (simp add: eind_def)

lemma equipotent_Plus_union:
  assumes
    a1: "disjoint A B"
  shows
    "\<^EP>{:A <+> B:}{:A \<union> B:}"
  apply (rule equipotentI 
                [of "(\<glambda> ab | ab \<in> A <+> B \<bullet> \<case> ab \<of> Inl a \<longrightarrow> a | Inr b \<longrightarrow> b \<esac>)"])
  apply (mauto(fspace) msimp add: glambda_dom glambda_ran)
  using a1
  apply (auto simp add: glambda_dom glambda_ran Plus_def image_def disjoint_def)
  apply (intro exI conjI disjI1)
  apply (auto)
  apply (intro exI conjI disjI2)
  apply (auto)
  done

lemma equipotent_Plus_cong:
  assumes
    a1: "\<^EP>{:A:}{:A':}" and
    a2: "\<^EP>{:B:}{:B':}"
  shows
    "\<^EP>{:A <+> B:}{:A' <+> B':}"
proof -
  from a1 obtain f where
    b1: "f \<in> A \<zbij> A'"
    by (auto elim!: equipotentE)
  from a2 obtain g where
    b2: "g \<in> B \<zbij> B'"
    by (auto elim!: equipotentE)
  have 
    "(\<glambda> ab 
     | ab \<in> A <+> B 
     \<bullet> \<case> ab \<of> 
         Inl a \<longrightarrow> Inl (f\<cdot>a) 
         | Inr b \<longrightarrow> Inr (g\<cdot>b) 
       \<esac>) \<in> (A <+> B) \<zbij> (A' <+> B')"
    apply (mauto(fspace) msimp add: Collect_mem_eq glambda_dom glambda_ran)
    apply (intro allI impI)
    apply (elim conjE)
  proof - 
    fix 
      "ab" and "cd"
    assume
      c1: "ab \<in> (A <+> B)" and
      c2: "cd \<in> (A <+> B)"
    with b1 b2 show
      "\<case> ab \<of> 
         Inl a \<longrightarrow> Inl (f\<cdot>a) 
         | Inr b \<longrightarrow> Inr (g\<cdot>b) 
       \<esac> 
       = \<case> cd \<of> 
           Inl a \<longrightarrow> Inl (f\<cdot>a) 
           | Inr b \<longrightarrow> Inr (g\<cdot>b) 
         \<esac>
      \<Leftrightarrow> ab = cd"
        by (auto simp add: tinj_inj tinj_range)
  next
    show 
      "{ ab | ab \<in> (A <+> B) \<bullet> \<case> ab \<of> Inl a \<longrightarrow> Inl (f\<cdot>a) | Inr b \<longrightarrow> Inr (g\<cdot>b) \<esac> }
      = A' <+> B'"
      apply (simp split: sum.split add: set_eq_def)
      apply (msafe_no_assms(inference))
    proof -
      fix 
        "ab" and 
        "ab'"
      assume
        c1: "(\<forall> a | ab = Inl a \<bullet> ab' = Inl (f\<cdot>a) \<and> Inl a \<in> A <+> B)" and
        c2: "(\<forall> b | ab = Inr b \<bullet> ab' = Inr (g\<cdot>b) \<and> Inr b \<in> A <+> B)"
      with b1 b2 show 
        "ab' \<in> A' <+> B'"
        apply (cases "ab")
        apply (auto simp add: tinj_range)
        done
    next
      fix 
        "ab'"
      assume
        c1: "ab' \<in> A' <+> B'"
      show
        "(\<exists> ab \<bullet> 
          (\<forall> a | ab = Inl a \<bullet> ab' = Inl (f\<cdot>a) \<and> Inl a \<in> A <+> B) \<and> 
          (\<forall> b | ab = Inr b \<bullet> ab' = Inr (g\<cdot>b) \<and> Inr b \<in> A <+> B))"
      proof (cases ab')
        fix 
          "a'"
        assume
          d1: "ab' = Inl a'"
        with b1 b2 c1 show
          "?thesis"
          apply (witness "Inl-['a,'c] ((f\<^sup>\<sim>)\<cdot>a')")
          apply (auto)
          done
      next
        fix 
          "b'"
        assume
          d1: "ab' = Inr b'"
        with b1 b2 c1 show
          "?thesis"
          apply (witness "Inr-['c,'a] ((g\<^sup>\<sim>)\<cdot>b')")
          apply (auto)
          done
      qed
    qed
  qed
  then show
    "?thesis"
    by (rule equipotentI)
qed

lemma equipotent_Plus_unionIl:
  assumes
    a2: "\<^EP>{:A:}{:A':}" and
    a1: "disjoint A' B"
  shows
    "\<^EP>{:A <+> B:}{:A' \<union> B:}"
  apply (rule equipotent_trans)
  apply (rule equipotent_Plus_cong [OF a2 equipotent_refl [of "B"]])
  apply (rule equipotent_Plus_union [OF a1])
  done

lemma equipotent_Plus_unionIr:
  assumes
    a2: "\<^EP>{:B:}{:B':}" and
    a1: "disjoint A B'"
  shows
    "\<^EP>{:A <+> B:}{:A \<union> B':}"
  apply (rule equipotent_trans)
  apply (rule equipotent_Plus_cong [OF equipotent_refl [of "A"] a2])
  apply (rule equipotent_Plus_union [OF a1])
  done

lemma [mintro!(wind)]:
  assumes
    a1: "\<^EP>{:A:}{:A':}"
  shows
    "\<^EP>{:A <+> B:}{:A' <+> B:}"
  by (rule equipotent_Plus_cong [OF a1 equipotent_refl])

lemma [mintro!(wind)]:
  assumes
    a1: "\<^EP>{:B:}{:B':}"
  shows
    "\<^EP>{:A <+> B:}{:A <+> B':}"
  by (rule equipotent_Plus_cong [OF equipotent_refl a1])


lemma equipotent_Plus_com:
  "\<^EP>{:A <+> B:}{:B <+> A:}"
  apply (rule equipotentI [of "(\<glambda> ab | ab \<in> A <+> B \<bullet> \<case> ab \<of> Inl a \<longrightarrow> Inr a | Inr a \<longrightarrow> Inl a \<esac>)"])
  apply (mauto(fspace) msimp add: glambda_dom glambda_ran)
  apply (auto)
  apply (auto split: sum.splits)
  done

lemma equipotent_Plus_assoc:
  "\<^EP>{:(A <+> B) <+> C:}{:A <+> (B <+> C):}"
  apply (rule equipotentI [of "(\<glambda> abc | abc \<in> (A <+> B) <+> C \<bullet> \<case> abc \<of> Inl ab \<longrightarrow> \<case> ab \<of> Inl a \<longrightarrow> Inl a | Inr b \<longrightarrow> Inr (Inl b) \<esac> | Inr c \<longrightarrow> Inr (Inr c) \<esac>)"])
  apply (mauto(fspace) msimp add: glambda_dom glambda_ran)
  apply (auto)
  apply (intro exI conjI)
  defer
  apply (rule InlI [THEN InlI, of _ "A" "B" "C"])
  apply (assumption)
  apply (intro exI conjI)
  defer
  apply (rule InrI [THEN InlI, of _ "B" "A" "C"])
  apply (assumption)
  apply (intro exI conjI)
  defer
  apply (rule InrI)
  apply (assumption)
  apply (auto split: sum.splits)
  done

lemma equipotent_Plus_emptyL:
  "\<^EP>{:\<emptyset> <+> B:}{:B:}"
  apply (rule equipotentI [of "{ b | b \<in> B \<bullet> (Inr b \<mapsto> b) }"])
  apply (mauto(fspace))
  apply (auto intro!: functionalI)
  done

lemma equipotent_Plus_empty_congL:
  assumes
    a1: "\<^EP>{:B:}{:B':}"
  shows
    "\<^EP>{:\<emptyset> <+> B:}{:B':}"
  by (rule equipotent_trans [OF equipotent_Plus_emptyL a1])

lemma equipotent_Plus_emptyR:
  "\<^EP>{:B <+> \<emptyset>:}{:B:}"
  apply (rule equipotentI [of "{ b | b \<in> B \<bullet> (Inl b \<mapsto> b) }"])
  apply (mauto(fspace))
  apply (auto intro!: functionalI)
  done

lemma equipotent_Plus_empty_congR:
  assumes
    a1: "\<^EP>{:B:}{:B':}"
  shows
    "\<^EP>{:B <+> \<emptyset>:}{:B':}"
  by (rule equipotent_trans [OF equipotent_Plus_emptyR a1])

lemma subequipotent_Plus_union:
  "\<^sEP>{:A \<union> B:}{:A <+> B:}"
  apply (rule subequipotentI [of "(\<glambda> a | a \<in> A \<union> B \<bullet> \<if> a \<in> A \<then> Inl a \<else> Inr a \<fi>)"])
  apply (mauto(fspace) msimp add: glambda_dom glambda_ran)
  apply (auto)
  done

lemma subequipotent_Plus_cong:
  assumes
    a1: "\<^sEP>{:A:}{:A':}" and
    a2: "\<^sEP>{:B:}{:B':}"
  shows
    "\<^sEP>{:A <+> B:}{:A' <+> B':}"
proof -
  from a1 obtain f where
    b1: "f \<in> A \<zinj> A'"
    by (auto elim!: subequipotentE)
  from a2 obtain g where
    b2: "g \<in> B \<zinj> B'"
    by (auto elim!: subequipotentE)
  have 
    "(\<glambda> ab | ab \<in> A <+> B \<bullet> 
      \<case> ab \<of> Inl a \<longrightarrow> Inl (f\<cdot>a) | Inr b \<longrightarrow> Inr (g\<cdot>b) \<esac>) \<in> (A <+> B) \<zinj> (A' <+> B')"
    apply (mauto(fspace) msimp add: glambda_dom glambda_ran Collect_mem_eq)
    apply (intro allI impI)
    apply (elim conjE)
  proof -
    fix 
      "ab" and "cd"
    assume
      c1: "ab \<in> (A <+> B)" and
      c2: "cd \<in> (A <+> B)"
    with b1 b2 show
      "\<case> ab \<of> 
        Inl a \<longrightarrow> Inl (f\<cdot>a) 
      | Inr b \<longrightarrow> Inr (g\<cdot>b) 
      \<esac> 
      = \<case> cd \<of> 
          Inl a \<longrightarrow> Inl (f\<cdot>a) 
        | Inr b \<longrightarrow> Inr (g\<cdot>b) 
        \<esac>
      \<Leftrightarrow> ab = cd"
        by (auto simp add: tinj_inj tinj_range)
  next
    from b1 b2 show 
      "{ ab | ab \<in> (A <+> B) \<bullet> \<case> ab \<of> Inl a \<longrightarrow> Inl (f\<cdot>a) | Inr b \<longrightarrow> Inr (g\<cdot>b) \<esac> }
      \<subseteq> A' <+> B'"
      by (auto  split: sum.split simp add: subset_def)
  qed
  then show
    "?thesis"
    by (rule subequipotentI)
qed

lemma [mintro!(wind)]:
  assumes
    a1: "\<^sEP>{:A:}{:A':}"
  shows
    "\<^sEP>{:A <+> B:}{:A' <+> B:}"
  by (rule subequipotent_Plus_cong [OF a1 subequipotent_refl])

lemma [mintro!(wind)]:
  assumes
    a1: "\<^sEP>{:B:}{:B':}"
  shows
    "\<^sEP>{:A <+> B:}{:A <+> B':}"
  by (rule subequipotent_Plus_cong [OF subequipotent_refl a1])

lemmas cartesian_equipotent_intros = 
  equipotent_refl subequipotent_refl
  inj_on_equipotent_image inj_on_equipotent_image_cong inj_on_subequipotent_image_cong
  equipotent_prod_cong equipotent_prod_singletonL equipotent_prod_singletonR subeq_prod_cong
  equipotent_Plus_union equipotent_Plus_cong equipotent_Plus_empty_congL equipotent_Plus_empty_congR
  subequipotent_Plus_union subequipotent_Plus_cong

text {*

In fact equipotentence is exactly the default equivalence generated by 
subequipotence.

*}

lemma equipotent_default:
  "equipotent = default_equiv subequipotent"
  apply (intro ext)
  apply (simp add: default_equiv_def)
  apply (msafe_no_assms(inference))
proof -
  fix X Y 
{ assume "\<^EP>{:X:}{:Y:}"
  then show "\<^sEP>{:X:}{:Y:}"
    by (auto intro!: subequipotentI elim!: equipotentE)
next
  assume "\<^EP>{:X:}{:Y:}"
  then show "\<^sEP>{:Y:}{:X:}"
    by (auto intro!: subequipotentI elim!: equipotentE)
next
  assume "\<^sEP>{:X:}{:Y:}" "\<^sEP>{:Y:}{:X:}"
  then show "\<^EP>{:X:}{:Y:}"
    by (rule subequipotent_antisym)
}
qed

interpretation cardqpo: partial_order "\<^qspace>{:\<univ>-['a set]:}{:equipotent:}" "\<^quotord>{:subequipotent:}{:equipotent:}"
  apply (simp_all add: equipotent_default)
  apply (rule cardpre.default_order_congI [THEN order_cong.quotpoI])
  done

lemma equipotent_congruent:
  "r_congruent equipotent subequipotent"
  apply (simp add: r_congruent_def)
  apply (msafe_no_assms(inference))
proof -
  fix y_d_1 y_d_2 z_d_1 z_d_2
  assume 
    b1: "\<^EP>{:y_d_1:}{:z_d_1:}" and
    b2: "\<^EP>{:y_d_2:}{:z_d_2:}"
  {
  assume b3: "\<^sEP>{:y_d_1:}{:y_d_2:}"
  from b1 have "\<^sEP>{:z_d_1:}{:y_d_1:}"
    by (rule equipotentD2)
  also have "\<^sEP>{:y_d_1:}{:y_d_2:}"
    by (rule b3)
  also from b2 have "\<^sEP>{:y_d_2:}{:z_d_2:}"
    by (rule equipotentD1)
  finally show "\<^sEP>{:z_d_1:}{:z_d_2:}"
    by (this)
  }
  {
  assume b3: "\<^sEP>{:z_d_1:}{:z_d_2:}"
  from b1 have "\<^sEP>{:y_d_1:}{:z_d_1:}"
    by (rule equipotentD1)
  also have "\<^sEP>{:z_d_1:}{:z_d_2:}"
    by (rule b3)
  also from b2 have "\<^sEP>{:z_d_2:}{:y_d_2:}"
    by (rule equipotentD2)
  finally show "\<^sEP>{:y_d_1:}{:y_d_2:}"
    by (this)
  }
qed

section {* Finite sets *}

lemma subequipotent_nat_interval_nat:
  "\<^sEP>{:\<lclose>0\<dots>N::\<nat>\<ropen>:}{:\<univ>-[\<nat>]:}"
  apply (rule subequipotentI [of "(\<glambda> n | n \<in> \<lclose>0\<dots>N\<ropen> \<bullet> n)"])
  apply (mauto(fspace))
  apply (auto simp add: glambda_dom)
  done

lemma finite_card: 
  fixes F::"'a set"
  shows "finite F \<Leftrightarrow> (\<exists> N::\<nat> \<bullet> \<^EP>{:F:}{:\<lclose>0\<dots>N\<ropen>:})"
proof (msafe_no_assms(inference))
  assume a1: "finite F"
  then show "\<exists> N::\<nat> \<bullet> \<^EP>{:F:}{:\<lclose>0\<dots>N\<ropen>:}"
  proof (induct F rule: finite_induct)
    have "\<emptyset>-['a \<times> \<nat>] \<in> \<emptyset>-['a] \<zbij> \<lclose>0\<dots>0\<ropen>"
      by (mauto(fspace), auto simp add: functional_def interval_defs)
    then have "\<^EP>{:\<emptyset>-['a]:}{:\<lclose>0\<dots>(0::\<nat>)\<ropen>:}"
      by (auto simp add: equipotent_def)
    then show "\<exists> N::\<nat> \<bullet> \<^EP>{:\<emptyset>-['a]:}{:\<lclose>0\<dots>N\<ropen>:}"
      apply (witness "0::\<nat>")
      apply (auto)
      done
  next
    fix F::"'a set" and x::'a
    assume a1: "finite F" and a2: "x \<notin> F" and
      a3: "\<exists> N::\<nat> \<bullet> \<^EP>{:F:}{:\<lclose>0\<dots>N\<ropen>:}"
    from a3 have "\<exists> (N::\<nat>) f \<bullet> f \<in> F \<zbij> \<lclose>0\<dots>N\<ropen>"
      by (auto simp add: equipotent_def)
    then have "\<exists> (M::\<nat>) g \<bullet> g \<in> \<^ins>{:x:}{:F:} \<zbij> \<lclose>0\<dots>M\<ropen>"
    proof (msafe_no_assms(inference))
      fix N::"\<nat>" and f::"('a \<times> \<nat>)set"
      assume b1: "f \<in> F \<zbij> \<lclose>0\<dots>N\<ropen>"
      from b1 have b2: "N \<notin> \<zran> f"
        by (mauto(fspace), simp)
      from b1 b2 a2 have "\<^ins>{:(x \<mapsto> N):}{:f:} \<in> \<^ins>{:x:}{:F:} \<zbij> \<lclose>0\<dots>N+1\<ropen>"
      proof (mauto(fspace))
(*
        show "\<zdom> (\<^ins>{:(x \<mapsto> N):}{:f:}) = \<^ins>{:x:}{:(\<zdom> f):}"
          by (simp only: fin_pfun_simp)
      next
*)
        assume c1: "\<zran> f = \<lclose>0\<dots>N\<ropen>"
        then show "\<zran> (\<^ins>{:(x \<mapsto> N):}{:f:}) = \<lclose>0\<dots>N+1\<ropen>"
        proof (simp add: fin_pfun_simp)
          show "\<^ins>{:N:}{:\<lclose>0\<dots>N\<ropen>:} = \<lclose>0\<dots>Suc N\<ropen>"
            by (auto simp add: interval_defs less_Suc_eq)
        qed
      qed
      then show "?thesis" by (auto)
    qed
    then show "\<exists> N::\<nat> \<bullet> \<^EP>{:\<^ins>{:x:}{:F:}:}{:\<lclose>0\<dots>N\<ropen>:}"
      by (simp add: equipotent_def)
  qed
next
  fix N::"\<nat>"
  assume a1: "\<^EP>{:F:}{:\<lclose>0\<dots>N\<ropen>:}"
  have a2: "\<forall> F::'a set \<bullet> \<^EP>{:F:}{:\<lclose>0\<dots>N\<ropen>:} \<Rightarrow> finite F"
  proof (induct N type: nat, msafe_no_assms(inference))
    fix F::"'a set"
    assume b1: "\<^EP>{:F:}{:\<lclose>0\<dots>(0::\<nat>)\<ropen>:}"
    then have "F = \<emptyset>"
    proof (simp add: equipotent_def interval_defs, msafe_no_assms(inference))
      fix f x
      assume c1: "f \<in> F \<zbij> \<emptyset>-[\<nat>]"
      then have "f = \<emptyset>"
        by (mauto(fspace), auto)
      then have "\<zdom> f = \<emptyset>" by (auto)
      with c1 show "F = \<emptyset>"
        by (mauto(fspace))
    qed
    then show "finite F" by (auto)
  next
    fix N::"\<nat>" and F::"'a set"
    assume b1: "\<forall> F::'a set \<bullet> \<^EP>{:F:}{:\<lclose>0\<dots>N\<ropen>:} \<Rightarrow> finite F" and
      b2: "\<^EP>{:F:}{:\<lclose>0\<dots>Suc N\<ropen>:}"
    from b2 show "finite F"
    proof (simp add: equipotent_def, msafe_no_assms(inference))
      fix f assume c1: "f \<in> F \<zbij> \<lclose>0\<dots>Suc N\<ropen>"
      then have "\<exists> x \<bullet> (x \<mapsto> N) \<in> f"
        by (mauto(fspace), auto simp add: Range_def Domain_def interval_defs)
      then have "\<exists> x | x \<in> \<zdom> f \<bullet> (x \<mapsto> N) \<in> f"
        by (auto)
      also from c1 have "\<zdom> f = F" by (mauto(fspace))
      finally have "\<exists> x | x \<in> F \<bullet> (x \<mapsto> N) \<in> f" by (auto)
      then show "finite F"
      proof (msafe_no_assms(inference))
        fix x assume d1: "x \<in> F" and d2: "(x \<mapsto> N) \<in> f"
        have d3: "f - {(x \<mapsto> N)} = ({x} \<zdsub> f)"
        proof (auto simp add: dsub_def)
          fix M 
          assume e1: "(x \<mapsto> M) \<in> f"
          with c1 d2 show "M = N"
            by (mauto(fspace), auto elim!: functionalE)
        qed
        have d4: "f - {(x \<mapsto> N)} = (f \<zrsub> {N})"
        proof (auto simp add: rsub_def)
          fix y 
          assume e1: "(y \<mapsto> N) \<in> f"
          with c1 d2 show "y = x"
            apply (mauto(fspace))
            apply (auto elim!: functionalE)
            done
        qed
        from c1 have d5: "(f - {(x \<mapsto> N)}) \<in> (F - {x}) \<zbij> \<lclose>0\<dots>N\<ropen>"
        proof (simp only: d3, mauto(fspace))
          show "\<zdom> ({x} \<zdsub> f) = (\<zdom> f) - {x}"
           by (auto simp add: dsub_def)
        next
          assume e1: "\<zran> f = \<lclose>0\<dots>Suc N\<ropen>"
          have "\<zran> (f - {(x \<mapsto> N)}) = (\<zran> f) - {N}"
            by (auto simp add: d4 rsub_def)
          also from e1 have "\<dots> = \<lclose>0\<dots>N\<ropen>"
            by (auto simp add: interval_defs less_Suc_eq)
          finally show "\<zran> ({x} \<zdsub> f) = \<lclose>0\<dots>N\<ropen>"
            by (simp add: d3)
        qed
        then have "\<^EP>{:(F - {x}):}{:\<lclose>0\<dots>N\<ropen>:}"
          by (auto simp add: equipotent_def)
        with b1 have "finite (F - {x})" by (auto)
        then show "finite F" by (auto)
      qed
    qed
  qed
  with a1 show "finite F" by (auto)
qed

lemma finite_interval:
  "finite \<lclose>0-[\<nat>]\<dots>N\<ropen>"
  apply (simp add: finite_card)
  apply (witness "N")
  apply (rule equipotentI [of "(\<glambda> n | n \<in> \<lclose>0-[\<nat>]\<dots>N\<ropen> \<bullet> n)"])
  apply (mauto(fspace))
  apply (auto simp add: glambda_dom glambda_ran)
  done

lemma finite_card': 
  fixes F::"'a set"
  shows "finite F \<Leftrightarrow> (\<exists> N::\<nat> \<bullet> \<^sEP>{:F:}{:\<lclose>0\<dots>N\<ropen>:})"
proof (auto intro: equipotentD1 simp add: finite_card)
  fix
    n :: "\<nat>"
  assume
    b1: "\<^sEP>{:F:}{:\<lclose>0\<dots>n\<ropen>:}"
  then obtain f where
    b2: "f \<in> F \<zinj> \<lclose>0\<dots>n\<ropen>"
    by (auto simp add: subequipotent_def)
  from b2 [THEN tinj_ran] have
    b3: "finite (\<zran> f)"
    apply (rule finite_subset)
    apply (simp add: finite_interval)
    done
  have
    b4: "finite (f\<^sup>\<sim>)"
    apply (rule dom_finite_fun)
    using b2 [THEN tinj_inv_pfun] b3
    apply (mauto(fspace) msimp add: Z_inverse_dom)
    done
  from fun_finite_ran [OF b4] have
    b5: "finite F"
    by (simp add: Z_inverse_ran tinj_dom [OF b2])
  then show
    "(\<exists> N::\<nat> \<bullet> \<^EP>{:F:}{:\<lclose>0\<dots>N\<ropen>:})"
    by (simp add: finite_card)
qed

(* Move to somewhere in Z Toolkit 

lemma Z_fin_pow_def:  
  "\<fset> X \<defs> { S::'b set | S \<in> \<pset> X \<and> (\<exists> n::'a::znumbers | n \<in> zNats \<bullet> (\<exists> f \<bullet> f \<in> zint_range 1 n \<zbij> S)) }"
proof (rule eq_reflection)
  let "?g n" = "(\<glambda> k | k \<in> \<lclose>0\<dots>n\<ropen> \<bullet> (of_nat k) + (1::'a))"
  have b1 [rule_format]: "(\<forall> n \<bullet> ?g n \<in> \<lclose>0\<dots>n\<ropen> \<zbij> zint_range 1 (of_nat n))" 
  proof (msafe_no_assms(inference), mauto(fspace), simp_all)
    fix n
    show "\<zdom> (\<glambda> k | k < n \<bullet> (of_nat k) + (1::'a)) = \<lclose>0\<dots>n\<ropen>"
      by (simp add: glambda_dom interval_defs)
    show "\<zran> (\<glambda> k | k < n \<bullet> (of_nat k) + (1::'a)) = zint_range 1 (of_nat n)"
    proof (auto simp add: glambda_ran interval_defs nat_of_norm zNats.Rep_inverse)
      fix k::'a
      assume d1: "k \<in> zInts" and d2: "1 \<le> k" and d3: "k \<le> of_nat n"
      from d1 d2 have d4: "k \<in> zNats"
        by (auto simp add: Z_zNats_zInts_conv)
      from d4 d2 have d5: "0 < k"
        by (auto)
      with d2 d3 d4 show "(\<exists> a \<bullet> k = of_nat a + 1 \<and> a < n)"
        apply (witness "nat_of k - 1")
        apply (simp add: nat_of_norm zNats.Rep_inverse)
        done
    qed
  qed
  show "\<fset> X = { S::'b set | S \<in> \<pset> X \<and> (\<exists> n::'a::znumbers | n \<in> zNats \<bullet> (\<exists> f \<bullet> f \<in> zint_range 1 n \<zbij> S)) }"
  proof (auto simp add: fin_pow_def finite_card equipotent_def)
    fix S::"'b set" and n::\<nat> and f::"'b \<leftrightarrow> \<nat>"
    assume c1: "S \<subseteq> X" and c2: "f \<in> S \<zbij> \<lclose>0\<dots>n\<ropen>"
    show "(\<exists> n::'a | n \<in> zNats \<bullet> (\<exists> f \<bullet> f \<in> zint_range 1 n \<zbij> S))"
      apply (witness "(of_nat n)::'a")
      apply (simp)
      apply (witness "((?g n)\<^sup>\<sim>)\<zfcomp> (f\<^sup>\<sim>)")
      apply (rule fcomp_in_bijI)
      apply (rule bij_inv_bij [OF b1])
      apply (rule bij_inv_bij [OF c2])
      done
  next
    fix S::"'b set" and n::'a and f::"'a \<leftrightarrow> 'b"
    assume c1: "S \<subseteq> X" and c2: "f \<in> zint_range 1 n \<zbij> S" and c3: "n \<in> zNats"
    from bij_inv_bij [OF b1 [of "nat_of n"]]
    show "(\<exists> (n::\<nat>) f \<bullet> f \<in> S \<zbij> \<lclose>0\<dots>n\<ropen>)"
      apply (witness "nat_of n")
      apply (witness "(f\<^sup>\<sim>)\<zfcomp> ((?g (nat_of n))\<^sup>\<sim>)")
      apply (rule fcomp_in_bijI)
      apply (rule bij_inv_bij [OF c2])
      apply (simp add: zNats.Abs_inverse [OF c3])
      done
  qed
qed

lemma Z_zcard_def:  
  assumes a1: "S \<in> \<fset> (X::'b set)"
  shows "zcard S \<defs> (\<mu> (n::'a::znumbers) | n \<in> zNats \<and> (\<exists> f \<bullet> f \<in> zint_range 1 n \<zbij> S))"
proof (rule eq_reflection)
  from a1
  obtain n::'a and f where b1: "n \<in> zNats" and b2: "f \<in> zint_range 1 n \<zbij> S"
    by (auto simp add: Z_fin_pow_def [where ?'a = 'a])
  from b2 have b3: "((zcard S)::'a) = zcard (zint_range (1::'a) n)"
    by (rule zcard_Image)
  also from b1 have "zcard (zint_range (1::'a) n) = n"
    by (simp add: zint_range_zcard_from_1)
  finally have b5: "zcard S = n"
    by (simp)
  with b2 have b6: "f \<in> zint_range 1 ((zcard S)::'a) \<zbij> S"
    by (simp)
  show "zcard S = (\<mu> (n::'a::znumbers) | n \<in> zNats \<and> (\<exists> f \<bullet> f \<in> zint_range 1 n \<zbij> S))"
    apply (rule collect_the_equality [symmetric])
    apply (simp add: zNats_zcard)
    apply (rule exI)
    apply (rule b6)
    apply (auto)
  proof -
    fix m::'a and f
    assume c1: "m \<in> zNats" and c2: "f \<in> zint_range 1 m \<zbij> S"
    have "((zcard S)::'a) = zcard (zint_range (1::'a) m)"
      by (rule zcard_Image [OF c2])
    then show "m = zcard S"
      by (simp add: zint_range_zcard_from_1 [OF c1])
  qed
qed
*)
lemma equipotent_empty:
  "\<^EP>{:\<emptyset>-['a]:}{:\<emptyset>-['b]:}"
  apply (rule equipotentI [of "\<emptyset>-['a \<times> 'b]"])
  apply (mauto(fspace) mintro: fin_pfunI msimp add: fin_pfun_simp vacuous_inv empty_functional)
  done

lemma equipotent_empty_iff:
  "\<^EP>{:X:}{:\<emptyset>-['b]:} \<Leftrightarrow> X = \<emptyset>-['a]" 
  "\<^EP>{:\<emptyset>-['b]:}{:X:} \<Leftrightarrow> X = \<emptyset>-['a]" 
  apply (auto simp add: equipotent_empty)
  apply (auto simp add: equipotent_def)
  apply (mauto(fspace))
  done

lemma subequipotent_insert_cong:
  assumes
    a1: "\<^sEP>{:X - {x}:}{:Y - {y}:}"
  shows
    "\<^sEP>{:insert x X:}{:insert y Y:}"
proof -
  from a1 obtain f where 
    b1: "f \<in> (X - {x}) \<zinj> (Y - {y})"
    by (auto simp add: subequipotent_def)
  show
    "?thesis"
    apply (rule subequipotentI [of "insert (x \<mapsto> y) f"])
    using b1
    apply (mauto_full(fspace) mintro!: insert_functionalI msimp add: insert_rinv)
    apply (auto)
    done
qed
(* J: this above is no good... have to fix up fin_fspace andeven fspace to extend the simpset!
 DONE! ! 
*)

lemma equipotent_insert_cong:
  assumes
    a1: "\<^EP>{:X - {x}:}{:Y - {y}:}"
  shows
    "\<^EP>{:insert x X:}{:insert y Y:}"
  using a1
  by (simp add: equipotent_iff subequipotent_insert_cong)

lemma subequipotent_insert_iff:
  "\<^sEP>{:insert x X:}{:insert y Y:} \<Leftrightarrow> \<^sEP>{:X - {x}:}{:Y - {y}:}"
proof (rule iffI [OF _ subequipotent_insert_cong])
  assume
    b1: "\<^sEP>{:insert x X:}{:insert y Y:}"
  then obtain f where
    b2: "f \<in> (insert x X) \<zinj> (insert y Y)"
    by (auto simp add: subequipotent_def)
  show
    "\<^sEP>{:X - {x}:}{:Y - {y}:}"
  proof (cases "y \<in> \<zran> f")
    assume
      c1: "y \<in> \<zran> f"
    then obtain x' where
      c2: "(x' \<mapsto> y) \<in> f"
      by (auto)
    from c2 b2 have
      c3: "f\<cdot>x' = y"
      by (mauto(fspace) mintro!: functional_beta)
    from c2 b2 have
      c4: "x' \<in> insert x X"
      by (mauto(fspace))
    let 
      ?g = "({x, x'} \<zdsub> f)"
    from c4 have
      c5: "?g = f \<zrsub> { f\<cdot>x, f\<cdot>x' }"
      by (auto simp add: dsub_def rsub_def tinj_unique [OF b2] tinj_inj_iff [OF b2])
    from b2 have
      c6: "?g \<in> (X \<setminus> {x, x'}) \<zinj> (Y \<setminus> {f\<cdot>x, f\<cdot>x'})"
      apply (
        mauto(fspace) 
          mintro!: dsub_functional rsub_functional 
          msimp add: dsub_rinv rsub_rinv)
      apply (simp add: dsub_dom)
      apply (simp add: c5 rsub_ran c3 [symmetric])
      apply (auto)
      done
    show 
      "?thesis"
    proof (cases "x' = x")
      assume
        d1: "x' = x"
      show
        "?thesis"
        apply (rule subequipotentI [of "?g"])
        using c6 c3
        apply (simp add: d1)
        done
    next
      assume
        d1: "x' \<noteq> x"
      with c4 have 
        d2: "x' \<in> X"
        by (auto)
      from d1 d2 c3 [symmetric] have
        d3: "f\<cdot>x \<noteq> y"
        by (simp add: tinj_inj_iff [OF b2])
      from tinj_range [OF b2, of "x"] d3 have 
        d4: "f\<cdot>x \<in> Y"
        by (auto)
      show
        "?thesis"
        apply (rule subequipotentI [of "insert (x' \<mapsto> f\<cdot>x) ?g"])
        using c6 d1
        apply
          (mauto(fspace)
            mintro!: insert_functionalI 
            msimp add: dsub_rinv rsub_rinv insert_rinv Z_rel_insert_dom Z_rel_insert_ran)
        apply (simp add: Z_dom_def rsub_def)
        apply (mauto(inference) mintro!: disjCI')
        apply (simp add: tinj_unique [OF b2])
        apply (mauto(inference))
        apply (simp add: tinj_inj_iff [OF b2])
        defer 1
        using d2 c3 d3 d1 d4
        apply (simp add: dsub_def Z_ran_def subset_def)
        apply (rule set_eqI)
        using d2
        apply (auto)
        done
    qed
  next
    assume
      c1: "y \<notin> \<zran> f"
    from tinj_ran [OF b2] c1 have
      c2: "\<zran> f \<subseteq> Y \<setminus> {y}"
      by (auto)
    let 
      ?g = "({x} \<zdsub> f)"
    show
      "?thesis"
      apply (rule subequipotentI [of "?g"])
      using b2 c1 c2
      apply
        (mauto(fspace)
          mintro!: insert_functionalI 
          msimp add: dsub_rinv rsub_rinv insert_rinv Z_rel_insert_dom Z_rel_insert_ran)
      apply (simp add: dsub_dom)
      apply (auto simp add: Z_ran_def dsub_def eind_def)
      done
  qed
qed (simp)

lemma equipotent_insert_iff:
  "\<^EP>{:insert x X:}{:insert y Y:} \<Leftrightarrow> \<^EP>{:X - {x}:}{:Y - {y}:}"
  by (simp add: equipotent_iff subequipotent_insert_iff)

lemma finite_subequipotent_card:
  assumes
    a1: "finite (A::'a set)" and
    a2: "finite (B::'b set)"
  shows
    "\<^sEP>{:A:}{:B:} \<Leftrightarrow> card A \<le> card B"
proof -
  have
    b1 [rule_format]: 
      "\<forall> A::'a set | finite A \<bullet> \<^sEP>{:A:}{:B:} \<Leftrightarrow> card A \<le> card B"
      (is "?P B")
  using a2
  proof (induct "B" set: finite)
    show
      "?P \<emptyset>"
      by (simp add: empty_glb)
  next
    fix
      B x
    assume
      b1: "finite B" and
      b2: "x \<notin> B" and
      b3: "?P B"
    from b1 show
      "?P (insert x B)"
    proof (mauto(inference) mdel: iffI)
      fix 
        A::"'a set"
      assume
        c1: "finite A"
      then show
        "\<^sEP>{:A:}{:insert x B:} \<Leftrightarrow> card A \<le> card (insert x B)" (is "?Q A")
      proof (induct "A" set: finite)
        show
          "?Q \<emptyset>"
          by (simp add: empty_bot)
      next
        fix 
          A :: "'a set" and
          a :: "'a"
        assume
          d1: "finite A" and
          d2: "a \<notin> A"
        with b2 have
          "\<^sEP>{:insert a A:}{:insert x B:}
          \<Leftrightarrow> \<^sEP>{:A:}{:B:}"
          by (simp add: subequipotent_insert_iff)
        also from b3 [rule_format, OF d1] have "\<dots>
          \<Leftrightarrow> card A \<le> card B"
          by (this)
        also from d1 d2 b1 b2 have "\<dots>
          \<Leftrightarrow> card (insert a A) \<le> card (insert x B)"
          by (auto)     
        finally show
          "?Q (insert a A)"
          by (this)
      qed
    qed
  qed
  with a1 show
    "?thesis"
    by (auto)
qed

lemma finite_equipotent_card:
  assumes
    a1: "finite (A::'a set)" and
    a2: "finite (B::'b set)"
  shows
    "\<^EP>{:A:}{:B:} \<Leftrightarrow> card A = card B"
  using a1 a2
  by (auto simp add: equipotent_iff finite_subequipotent_card)

lemma equipotent_singleton:
  "\<^EP>{:{x}:}{:{y}:}"
  apply (subst finite_equipotent_card)
  apply (auto)
  done

lemma equipotent_singleton_iff:
  "\<^EP>{:X:}{:{y}:} \<Leftrightarrow> (\<exists> x \<bullet> X = {x})"
proof (auto simp add: equipotent_singleton)
  assume
    b1: "\<^EP>{:X:}{:{y}:}"
  from b1 obtain f where
    b2: "f \<in> X \<zbij> {y}"
    by (auto simp add: equipotent_def)
  then show
    "(\<exists> x \<bullet> X = {x})"
    apply (witness "(f\<^sup>\<sim>)\<cdot>y")
    apply (mauto(fspace))
    apply (auto intro: functional_beta [symmetric] functional_ran [of "f\<^sup>\<sim>", simplified])
    done
qed

lemma subequipotent_nat_interval_lemma:
  fixes
    n :: "\<nat>" and 
    n' :: "\<nat>"
  shows
   "\<^sEP>{:{0..<n}:}{:{0..<n'}:} \<Leftrightarrow> \<zid> {0..<n} \<in> {0..<n} \<zinj> {0..<n'}"
proof -
  have 
    b1: "(\<forall> n \<bullet> \<^sEP>{:{0..<n}:}{:{0..<n'}:} \<Rightarrow> \<zid> {0..<n} \<in> {0..<n} \<zinj> {0..<n'})" (is "?P n'")
  proof (induct "n'" type: nat)
    show
      "?P 0" 
      apply (auto elim!: subequipotentE)
      apply (mauto(fspace))
      apply (auto simp add: Z_rel_id_mem Z_dom_def Z_ran_def)
      done
  next
    fix
      n' :: "\<nat>"
    assume
      ihyp: "?P n'"
    show
      "?P (Suc n')"
    proof (msafe_no_assms(inference))
      fix 
        n :: "\<nat>"
      assume
        d1: "\<^sEP>{:{0..<n}:}{:{0..<Suc n'}:}"
      show
        "\<zid> {0..<n} \<in> {0..<n} \<zinj> {0..<Suc n'}"
      proof (cases "n" type: nat)
        assume
          e1: "n = 0"
        with d1 id_in_relI [of "{0..<0-[\<nat>]}"]  show
          "?thesis"
          by (mauto_full(fspace) msimp add: empty_bot)
      next
        fix 
          n0 :: "\<nat>"
        assume
          e1: "n = Suc n0"
        from d1 obtain f where
          e2: "f \<in> {0..<n} \<zinj> {0..<Suc n'}" 
          by (auto simp add: subequipotent_def)
        have
          e3: "\<^sEP>{:{0..<n0}:}{:{0..<n'}:}"
        proof (cases "n' \<in> \<zran> f")
          assume
            f1: "n' \<notin> \<zran> f"
          then have
            "(\<forall> a | a \<in> \<zran> f \<bullet> a \<noteq> n')"
            by (auto)
          with e2 have
            f2: "f \<in> {0..<n} \<zinj> {0..<n'}"
            by (mauto_full(fspace) msimp add: subset_def less_Suc_eq mdel: RangeE)
         show
            "\<^sEP>{:{0..<n0}:}{:{0..<n'}:}"
            apply (rule subequipotentI [of "\<zid> {0..<n0}\<zfcomp> f"])
            apply (rule fcomp_in_tinjI2 [OF _ f2])
            apply (mauto_full(fspace) msimp add: id_dom id_ran e1)
            done
        next
          assume
            f1: "n' \<in> \<zran> f"
          then have
            f2: "((f\<^sup>\<sim>)\<cdot>n' \<mapsto> n') \<in> f"
            by (rule pfun_appl [OF tinj_inv_pfun [OF e2], simplified Z_inverse_mem Z_inverse_dom])
          have
            f3: "(n0 \<mapsto> f\<cdot>n0) \<in> f"
            apply (rule tinj_appl [OF e2])
            apply (auto simp add: e1)
            done
          from f2 f3 have 
            f4 [rule_format]: 
              "f\<cdot>n0 = n' \<Rightarrow> (f\<^sup>\<sim>)\<cdot>n' = n0"
              "f\<cdot>n0 \<noteq> n' \<Rightarrow> (f\<^sup>\<sim>)\<cdot>n' \<noteq> n0"
            apply (auto elim!: contrapos_nn)
            apply (mauto(inference) mintro: tinj_inv_beta [OF e2] tinj_beta [OF e2])
            done
          show
            "?thesis"
          proof (cases "f\<cdot>n0 = n'")
            assume
              g1: "f\<cdot>n0 = n'"
            show
              "?thesis"
              apply (rule subequipotentI [of "{n0} \<zdsub> f"])
              using Z_subset_in_pinj [rule_format, OF tinj_pinj [OF e2], of "{n0} \<zdsub> f", OF Z_dsub_sub_self] e2
              apply (mauto_full(fspace) msimp add: e1 g1 f4)
              apply (auto simp add: dsub_mem g1 f4 tinj_unique [OF e2] e1)
            proof -
              fix
                x :: "\<nat>"
              assume
                h1: "x \<noteq> n0" and
                h2: "x < Suc n0"
              from tinj_range [OF e2, of "x"] h2 have
                h3: "f\<cdot>x < Suc n'"
                by (auto simp add: less_Suc_eq e1)
              from h1 have
                h4: "f\<cdot>x \<noteq> f\<cdot>n0"
                apply (rule contrapos_nn)
                apply (rule tinj_inj [OF e2])
                apply (auto simp add: e1 h2)
                done
              from h3 h4 show
                "f\<cdot>x < n'"
                by (simp add: g1)
            qed
          next
            assume
              g1: "f\<cdot>n0 \<noteq> n'"
            have 
              g2: 
                "(f \<oplus> {((f\<^sup>\<sim>)\<cdot>n' \<mapsto> f\<cdot>n0), (n0 \<mapsto> n')})\<^sup>\<sim> 
                = (f\<^sup>\<sim>) \<oplus> {(f\<cdot>n0 \<mapsto> (f\<^sup>\<sim>)\<cdot>n'), (n' \<mapsto> n0)}"
              apply (auto simp add: rel_oride_mem Z_inverse_mem fin_pfun_simp tinj_beta [OF e2] tinj_inv_beta [OF e2] tinj_f_inv_f_beta [OF e2] tinj_f_f_inv_beta [OF e2 f1] e1 f4 split: if_splits)
              apply (auto elim:  notE [OF _ tinj_inj [OF e2]] simp add: tinj_unique [OF e2] tinj_f_f_inv_beta [OF e2 f1] e1)
              done
(*J: bad below need fin_fspace method! ! *)
            from  e2 f2 f3 g1 g2 have 
              g3: "f \<oplus> {((f\<^sup>\<sim>)\<cdot>n' \<mapsto> f\<cdot>n0), (n0 \<mapsto> n')} \<in>  {0..<Suc n0} \<zinj> {0..<Suc n'}"
              apply (mauto_full(fspace) msimp add: Z_rel_oride_dom_dist rel_oride_ran_dist fin_pfun_simp f4 e1)
              apply (mauto_no_assms(fspace) mintro: fin_pfunI msimp add: fin_pfun_simp vacuous_inv empty_functional  Z_rel_oride_dom_dist rel_oride_ran_dist e1 f4)
              apply (mstep(fspace) mintro: fin_pfunI | simp)+
              apply (mauto(fspace) mintro: fin_pfunI msimp add: fin_pfun_simp vacuous_inv empty_functional  Z_rel_oride_dom_dist rel_oride_ran_dist e1 f4)
              apply ((mstep(fspace) mintro: fin_pfunI)+ | simp)
              apply ((mstep(fspace) mintro: fin_pfunI)+ | simp)
              apply ((mstep(fspace) mintro: fin_pfunI)+ | simp)
              apply ((mstep(fspace) mintro: fin_pfunI)+ | simp)
              apply ((mstep(fspace) mintro: fin_pfunI) | simp)
              using tinj_range [OF e2]
              apply (auto simp add: e1 rel_oride_mem tinj_unique [OF e2] e1 f4 g1 fin_pfun_simp split: if_splits)
              done
            have
              g4: "{n0} \<zdsub> (f \<oplus> {((f\<^sup>\<sim>)\<cdot>n' \<mapsto> f\<cdot>n0), (n0 \<mapsto> n')}) \<subseteq> f \<oplus> {((f\<^sup>\<sim>)\<cdot>n' \<mapsto> f\<cdot>n0), (n0 \<mapsto> n')}"
              by (rule Z_dsub_sub_self)
            from Z_subset_in_pinj [rule_format, OF tinj_pinj [OF g3], OF g4] have 
              "{n0} \<zdsub> (f \<oplus> {((f\<^sup>\<sim>)\<cdot>n' \<mapsto> f\<cdot>n0), (n0 \<mapsto> n')}) \<in> {0..<n0} \<zinj> {0..<n'}"
              apply (mauto(fspace))
              apply (auto simp add: dsub_mem rel_oride_mem fin_pfun_simp split: if_splits)
              apply (simp add: dsub_dom Z_rel_oride_dom_dist fin_pfun_simp tinj_dom [OF e2] e1)
              using tinj_range [OF e2, of "n0"] g1
              apply (simp add: e1)
              apply (auto simp add: tinj_unique [OF e2] e1 less_Suc_eq)
            proof -
              fix
                x :: "\<nat>"
              assume
                h1: "x \<noteq> (f\<^sup>\<sim>)\<cdot>n'" and
                h2: "x < n0"
              from f2 have
                h3: "(f\<^sup>\<sim>)\<cdot>n' \<in> \<zdom> f"
                by (auto)
              from h1 have
                h4: "f\<cdot>x \<noteq> f\<cdot>((f\<^sup>\<sim>)\<cdot>n')"
                apply (rule contrapos_nn)
                apply (rule tinj_inj [OF e2])
                using h3
                apply (auto simp add: e1 h2 less_Suc_eq g1 tinj_dom [OF e2])
                done
              have 
                h5: "f\<cdot>((f\<^sup>\<sim>)\<cdot>n') = n'"
                apply (rule tinj_f_f_inv_beta [OF e2])
                using f2
                apply (auto)
                done
              from h4 h5 tinj_range [OF e2, of "x"] h2 show
                "f\<cdot>x < n'"
                by (auto simp add: e1)
            qed
            then show
              "?thesis"
              by (rule subequipotentI)
          qed
        qed
        from ihyp [rule_format, OF e3] show
          "\<zid> {0..<n} \<in> {0..<n} \<zinj> {0..<Suc n'}"
          apply (mauto(fspace) msimp add: e1 id_dom id_ran)
          apply (auto)
          done
      qed
    qed
  qed
  show 
    "?thesis"
    apply (mauto(inference) mintro: b1 [rule_format])
    apply (mauto(inference) mintro: subequipotentI)
    done 
qed

lemma subequipotent_nat_interval_iff:
  fixes
    m :: "\<nat>" and 
    n :: "\<nat>" and 
    n' :: "\<nat>"
  assumes
    a1: "m \<le> n" and
    a2: "m \<le> n'"
  shows
    "\<^sEP>{:{m..<n}:}{:{m..<n'}:} \<Leftrightarrow> n \<le> n'"
  using a1 a2
  by (auto simp add: finite_subequipotent_card)

lemma subequipotent_nat_interval_iff_empty:
  fixes
    m :: "\<nat>" and 
    n :: "\<nat>" and 
    n' :: "\<nat>"
  shows
    "\<^sEP>{:{m..<n}:}{:\<emptyset>-[\<nat>]:} \<Leftrightarrow> n \<le> m"
  by (auto simp add: finite_subequipotent_card)

lemma equipotent_nat_interval_iff:
  fixes
    m :: "\<nat>" and 
    n :: "\<nat>" and 
    n' :: "\<nat>"
  assumes
    a1: "m \<le> n" and
    a2: "m \<le> n'"
  shows
   "\<^EP>{:{m..<n}:}{:{m..<n'}:} \<Leftrightarrow> n = n'"
  using a1 a2
  by (auto simp add: finite_equipotent_card)

lemma equipotent_nat_interval_iff_empty:
  fixes
    m :: "\<nat>" and 
    n :: "\<nat>" and 
    n' :: "\<nat>"
  shows
   "\<^EP>{:\<emptyset>-[\<nat>]:}{:{m..<n'}:} \<Leftrightarrow> n' \<le> m"
   "\<^EP>{:{m..<n}:}{:\<emptyset>-[\<nat>]:} \<Leftrightarrow> n \<le> m"
  by (auto simp add: finite_equipotent_card)

lemma equipotent_nat_interval_iff_0:
  fixes
    n :: "\<nat>" and 
    n' :: "\<nat>"
  shows
    "\<^EP>{:{0..<n}:}{:{0..<n'}:} \<Leftrightarrow> n = n'"
    "\<^EP>{:\<emptyset>-[\<nat>]:}{:{0..<n'}:} \<Leftrightarrow> n' = 0"
    "\<^EP>{:{0..<n}:}{:\<emptyset>-[\<nat>]:} \<Leftrightarrow> n = 0"
  by (auto simp add: finite_equipotent_card)

lemma subequipotent_int_interval_iff:
  fixes
    m :: "\<int>" and 
    n :: "\<int>" and 
    n' :: "\<int>"
  assumes
    a1: "m \<le> n" and
    a2: "m \<le> n'"
  shows
    "\<^sEP>{:{m..<n}:}{:{m..<n'}:} \<Leftrightarrow> n \<le> n'"
  using a1 a2
  by (auto simp add: finite_subequipotent_card)

lemma subequipotent_int_interval_iff_empty:
  fixes
    n :: "\<int>" and 
    n' :: "\<int>"
  shows
    "\<^sEP>{:{m..<n}:}{:\<emptyset>-[\<int>]:} \<Leftrightarrow> n \<le> m"
  by (auto simp add: finite_subequipotent_card)

lemma equipotent_int_interval_iff:
  fixes
    n :: "\<int>" and 
    n' :: "\<int>"
  assumes
    a1: "m \<le> n" and
    a2: "m \<le> n'"
  shows
   "\<^EP>{:{m..<n}:}{:{m..<n'}:} \<Leftrightarrow> n = n'"
  using a1 a2
  by (auto simp add: finite_equipotent_card)

lemma equipotent_int_interval_iff_empty:
  fixes
    n :: "\<int>" and 
    n' :: "\<int>"
  shows
   "\<^EP>{:\<emptyset>-[\<int>]:}{:{m..<n'}:} \<Leftrightarrow> n' \<le> m"
   "\<^EP>{:{m..<n}:}{:\<emptyset>-[\<int>]:} \<Leftrightarrow> n \<le> m"
  by (auto simp add: finite_equipotent_card)

section {* Ordinals and equipotence *}

text {*

We need some results about ordinals and equipotence.

The representation of every ordinal is equipotent to the set of 
lower ordinals.

*}

lemma ordinal_equipotent:
  "\<^EP>{:Rep_ordinal b:}{:{a | a < b}:}"
proof -
  have b1: "oindex\<lparr>Rep_ordinal b\<rparr> = {a | a < b}"
  proof (auto simp add: image_def)
    fix x 
    assume c1: "x \<in> Rep_ordinal b"
    from oindex_under [of x]
    show "oindex x < b"
      apply (rule contrapos_np)
      apply (auto simp add: linorder_not_less ole_def c1)
      done
  next
    fix a
    assume c1: "a < b"
    let ?x = "(\<some> x | x \<notin> Rep_ordinal a)"
    from order_less_le_trans [OF c1 omax_ub [of b]]
    have c2: "?x \<notin> Rep_ordinal a"
      apply (intro someI_ex [of "\<olambda> x \<bullet> x \<notin> Rep_ordinal a"])
      apply (auto simp add: olt_def Romax_conv)
      done
    then have c3: "a \<le> oindex ?x"
      apply (simp add: oindex_def)
      apply (rule olim_char)
      apply (auto)
      done
    have c4: "?x \<in> Rep_ordinal (\<osuc> a)"
      by (simp add: Rosuc_conv osuc_Rep_def)
    from oindex_under [of ?x] have c5: "oindex ?x < osuc a"
      apply (rule contrapos_np)
      apply (auto simp add: linorder_not_less ole_def c4)
      done
    from c3 c5 [THEN osuc_char2] have c6: "a = oindex ?x"
      by (rule order_antisym)
    from c1 [THEN osuc_char] c4 have c7: "?x \<in> Rep_ordinal b"
      by (auto simp add: ole_def)
    from c6 c7 show "\<exists> x \<bullet> x \<in> Rep_ordinal b \<and> a = oindex x"
      by (auto)
  qed
  from ord_inj have b2: "inj_on oindex (Rep_ordinal b)"
    apply (rule subset_inj_on)
    apply (auto)
    done
  from b2 b1 show ?thesis
    by (rule equipotentIinj_on)
qed

definition
  ord_of :: "'a set \<rightarrow> 'a ordinal"
where
  ord_of_def: "ord_of A \<defs> (\<LEAST> b | \<^sEP>{:A:}{:Rep_ordinal b:})"

lemma ord_of_wdef1:
  "\<^sEP>{:A:}{:Rep_ordinal (ord_of A):}"
proof -
  from univ_top [of A]
  have "\<^sEP>{:A:}{:Rep_ordinal (\<omax>::'a ordinal):}"
    by (simp add: Romax_conv)
  then show ?thesis
    apply (simp add: ord_of_def)
    apply (rule wellorder_Least_lemma)
    apply (assumption)
    done
qed

lemma ord_of_wdef2:
  assumes 
    a1: "\<^sEP>{:A:}{:Rep_ordinal b:}"
  shows 
    "ord_of A \<le> b"
  apply (simp add: ord_of_def)
  apply (rule Least_le)
  apply (rule a1)
  done

lemma Rep_ord_of: 
  "\<^EP>{:A:}{:Rep_ordinal (ord_of A):}"
  apply (rule subequipotent_antisym)
  apply (rule ord_of_wdef1)
proof -
	show "\<^sEP>{:Rep_ordinal (ord_of A):}{:A:}"
	proof (cases "A = \<emptyset>")
	  assume b1: "A = \<emptyset>"
	  then have "{b::'a ordinal | \<^sEP>{:A:}{:Rep_ordinal b:}} = \<univ>"
	    by (auto simp add: empty_bot)
	  then have "ord_of A = \<ozero>"
	    apply (simp add: ord_of_def set_eq_def)
	    apply (rule Least_equality)
	    apply (auto simp add: ozero_lb)
	    done
	  then have "Rep_ordinal (ord_of A) = \<emptyset>"
	    by (simp add: Rozero_conv)
	  then show "\<^sEP>{:Rep_ordinal (ord_of A):}{:A:}"
	    by (simp add: empty_bot)
	next
	  assume b1: "A \<noteq> \<emptyset>"
	  obtain "next" where next_def: "next = (\<olambda> X \<bullet> (\<some> x | x \<in> A \<and> (A-X \<noteq> \<emptyset> \<Rightarrow> x \<notin> X)))"
	    by (auto)
	  obtain char where char_def: "char = orec (\<olambda> X (b::'a ordinal) \<bullet> insert (next X) X) (\<olambda> CL_X (b::'a ordinal) \<bullet> \<Union>CL_X)"
	    by (auto)
	  obtain ind where ind_def: "ind = (\<olambda> (b::'a ordinal) \<bullet> next (char b))"
	    by (auto)
	  have b2 [rule_format]: "\<forall> b::'a ordinal \<bullet> char b \<subseteq> A"
	  proof (msafe_no_assms(inference))
	    fix b
	    show "char b \<subseteq> A"
	    proof (induct b rule: ord_baseinduct)
	      fix b
	      assume d1: "b \<noteq> \<omax>" and d2: "char b \<subseteq> A"
	      show "char (\<osuc> b) \<subseteq> A"
	      proof (cases "A-(char b) = \<emptyset>")
	        assume e1: "A-(char b) = \<emptyset>"
	        with b1 have e2: "\<exists> x \<bullet> x \<in> A \<and> (A-(char b) \<noteq> \<emptyset> \<Rightarrow> x \<notin> (char b))"
	          by (auto)
	        from someI_ex [OF e2] e1 have "next (char b) \<in> A"
	          by (auto simp add: next_def)
	        with d2 show "char (\<osuc> b) \<subseteq> A"
	          by (simp add: osuc_unwind [OF d1] char_def)
	      next
	        assume e1: "A-(char b) \<noteq> \<emptyset>"
	        then have e2: "\<exists> x \<bullet> x \<in> A \<and> (A-(char b) \<noteq> \<emptyset> \<Rightarrow> x \<notin> char b)"
	          by (auto)
	        from someI_ex [OF e2] e1 have "next (char b) \<in> A"
	          by (auto simp add: next_def)
	        with d2 show "char (\<osuc> b) \<subseteq> A"
	          by (simp add: osuc_unwind [OF d1] char_def)
	      qed
	    next
	      fix b::"'a ordinal"
	      assume "is_limit b" and "\<forall> a | a < b \<bullet> char a \<subseteq> A"
	      then show "char b \<subseteq> A" 
	        by (auto simp add: olim_unwind char_def eind_def)
	    qed
	  qed
	  have b3 [rule_format]: "\<forall> b \<bullet> char b = {a | a < b \<bullet> ind a}"
	  proof (rule allI)
	    fix b
	    show "char b = {a | a < b \<bullet> ind a}"
	    proof (induct b rule: ord_baseinduct)
	      fix b
	      assume d1: "b \<noteq> \<omax>" and d2: "char b = {a | a < b \<bullet> ind a}"
	      have d3 [rule_format]: "\<forall> a \<bullet> a < \<osuc> b \<Leftrightarrow> a < b \<or> a = b"
	        by (auto intro: order_neq_le_trans osuc_char2 order_less_trans simp add: osuc_incr [OF d1])
	      have "char (\<osuc> b) = insert (next (char b)) (char b)"
	        by (auto simp add: osuc_unwind [OF d1] char_def)
	      also have "\<dots> = insert (ind b) (char b)"
	        by (simp add: ind_def)
	      also from d2 have "\<dots> = insert (ind b) {a | a < b \<bullet> ind a}"
	        by (simp add: d1)
	      also have "\<dots> = {a | a < \<osuc> b \<bullet> ind a}"
	        by (auto simp add: d3)
	      finally show "char (\<osuc> b) = {a | a < \<osuc> b \<bullet> ind a}"
	        by (simp)
	    next
	      fix b::"'a ordinal"
	      assume 
	        d1: "is_limit b" and
	        d2: "\<forall> a | a < b \<bullet> char a = {c | c < a \<bullet> ind c}"
	      have "char b = \<Union>{a | a < b \<bullet> char a}"
	        by (simp add: olim_unwind [OF d1] char_def)
	      also have "\<dots> = \<Union>{a | a < b \<bullet> {c | c < a \<bullet> ind c}}"
	        apply (mauto(wind))
	        apply (auto simp add: d2)
	        done
	      also have "\<dots> = {a | a < b \<bullet> ind a}"
	        apply (auto simp add: eind_def)
	        apply (intro exI conjI)
	      proof -
	        fix a
	        assume e1: "a < b"
	        show "a < \<osuc> a"
	          apply (rule osuc_incr)
	          apply (simp add: nonmax_conv [THEN sym])
	          apply (rule order_less_le_trans [OF e1 omax_ub])
	          done
	        from d1 e1 show "\<osuc> a < b"
	         by (rule le_is_limit_osuc_le)
	      qed (simp)
	      finally show "char b = {a | a < b \<bullet> ind a}"
	        by (this)
	    qed
	  qed
	  have b3a [rule_format]: "\<forall> a b \<bullet> a \<le> b \<Rightarrow> char a \<le> char b"
	    by (auto simp add: b3 eind_def)
	  from b1 have b3b [rule_format]: "\<forall> b \<bullet> ind b \<in> A"
	    apply (simp add: ind_def next_def)
	    apply (rule allI)
	    apply (rule someI_ex [THEN conjunct1])
	    apply (auto)
	    done
	  have b4 [rule_format]: "\<forall> b | char b \<subset> A \<bullet> ind b \<notin> char b"
	    apply (simp add: ind_def subset_def)
	    apply (msafe_no_assms(inference))
	  proof -
	    fix b 
	    assume c1: "char b \<subset> A"
	    then obtain x where c2: "x \<in> A - char b"
	      by (auto)
	    then have "x \<in> A \<and> (A - char b \<noteq> \<emptyset> \<Rightarrow> x \<notin> char b)"
	      by (auto)
	    then have "next (char b) \<in> A \<and> (A - char b \<noteq> \<emptyset> \<Rightarrow> next (char b) \<notin> char b)"
	      apply (simp only: next_def)
	      apply (rule someI)
	      apply (assumption)
	      done
	    with c1 show "next (char b) \<notin> char b"
	      by (auto)
	  qed
	  have b5 [rule_format]: "\<forall> b | char b \<subset> A \<bullet> inj_on ind {c | c \<le> b}"
	  proof (rule allI)
	    fix b
	    show "char b \<subset> A \<Rightarrow> inj_on ind {c | c \<le> b}" (is "?P b")
	    proof (induct b)
	      from b1 show "?P \<ozero>"
	        by (auto simp add: b3 ozero_bot ozero_eq)
	    next
	      fix b 
	      assume c1: "b \<noteq> \<omax>" and c2: "?P b"
	      show "?P (\<osuc> b)"
	      proof (rule impI)
	        assume d1: "char (\<osuc> b) \<subset> A"
	        have d2: "char b \<subset> A"
	          apply (rule order_le_less_trans [OF _ d1])
	          apply (auto simp add: b3 osuc_less_le [OF c1] eind_def)
	          done
	        with c2 have d3: "inj_on ind {c | c \<le> b}"
	          by (simp)
	        have d4: "{c | c \<le> \<osuc> b} = insert (\<osuc> b) {c | c \<le> b}"
	          by (auto simp add: set_eq_def osuc_less_le [OF c1] order_le_less)
	        from c1 [THEN osuc_incr] have d5: "{c | c \<le> b} - {\<osuc> b} = {c | c \<le> b}"
	          by (auto)
	        from b4 [OF d1]
	        show "inj_on ind {c | c \<le> \<osuc> b}"
	          apply (simp add: d4 d3 d5)
	          apply (simp only: b3 Collect_image)
	          apply (auto simp add: osuc_less_le [OF c1])
	          done
	      qed
	    next
	      fix b assume c1: "\<ozero> < b" and c2: "is_limit b" and
	        c3: "\<forall> a | a < b \<bullet> ?P a"
	      show "?P b"
	      proof (rule impI)
	        assume d1: "char b \<subset> A"
	        show "inj_on ind {c | c \<le> b}"
	        proof (rule inj_onI, auto simp add: order_le_less)
	          fix x y
	          assume e1: "ind x = ind y" and e2: "x < b" and e3: "y < b"
	          from e2 e3 have "char x \<subseteq> char b" "char y \<subseteq> char b"
	            by (auto simp add: b3 subset_def)
	          with d1 have e4: "char x \<subset> A" "char y \<subset> A"
	            by (auto)
	          show "x = y"
	          proof (cases x y rule: linorder_cases, auto)
	            assume f1: "x < y"
	            from e1 e3 e4 f1 show "x = y"
	              by (auto intro!: c3 [rule_format, THEN inj_onD])
	          next
	            assume f1: "y < x"
	            from e1 e2 e4 f1 show "x = y"
	              by (auto intro!: c3 [rule_format, THEN inj_onD])
	          qed
	        next
	          apply_end (rule contrapos_pp)
	          apply_end (assumption)
	          fix x assume e1: "x < b"
	          show "ind x \<noteq> ind b"
                    apply (rule not_sym)
	            using b4 [OF d1] e1
	            by (auto simp add: b3)
	        next
	          apply_end (rule contrapos_pp)
	          apply_end (assumption)
	          fix y assume "y < b"
	          with b4 [OF d1]
	          show "ind b \<noteq> ind y"
	            by (auto simp add: b3)         
	        qed
	      qed
	    qed
	  qed
	  have b6 [rule_format]: "\<forall> b | char b \<subset> A \<bullet> \<^sEP>{:{c | c \<le> b}:}{:A:}"
	    apply (msafe_no_assms(inference))
	    apply (rule subepIinj_on)
	    apply (rule b5)
	    apply (auto simp add: b3b Collect_image subset_def)
	    done 
	  show ?thesis
	  proof (cases "char \<omax> = A")
	    assume "char \<omax> \<noteq> A"
	    with b2 [of "\<omax>"] have c1: "char \<omax> \<subset> A"
	      by (auto)
	    have "\<^EP>{:Rep_ordinal (ord_of A):}{:{c::'a ordinal | c < ord_of A}:}"
	      by (rule ordinal_equipotent)
	    also have "\<^sEP>{:\<dots>:}{:{c::'a ordinal | c \<le> ord_of A}:}"
	      apply (rule subset_subequipotent)
	      apply (auto)
	      done
	    also have "\<^sEP>{:\<dots>:}{:A:}"
	    proof (rule b6)
	      show "char (ord_of A) \<subset> A"
	        apply (rule order_le_less_trans [of _ "char \<omax>"])
	        apply (rule b3a)
	        apply (rule omax_ub)
	        apply (rule c1)
	        done
	    qed
	    finally show ?thesis by (this)
	  next
	    assume c1: "char \<omax> = A"
	    let ?b = "\<LEAST> b | char b = A"
	    from c1 have c2: "char ?b = A"
	      by (rule LeastI)
	    have c3 [rule_format]: "\<forall> a | a < ?b \<bullet> char a \<subset> A"
	    proof (msafe_no_assms(inference))
	      fix a assume "a < ?b"
	      then have "char a \<noteq> A"
	        apply (rule contrapos_pp)
	        apply (simp add: linorder_not_less)
	        apply (rule Least_le)
	        apply (assumption)
	        done
	      with b2 [of a] show "char a \<subset> A"
	        by (auto)
	    qed
	    then have c4 [rule_format]: "\<forall> a | a < ?b \<bullet> \<^sEP>{:{c | c \<le> a}:}{:A:}"
	      apply (msafe_no_assms(inference))
	      apply (rule b6)
	      apply (auto)
	      done
	    have c5: "\<^sEP>{:{c | c < ?b}:}{:A:}"
	      apply (rule subepIinj_on [of ind])
	      defer 1
	      apply (simp add: b3b Collect_image subset_def)    
	    proof (cases "?b" rule: ord_basecases)
	      assume d1: "is_limit ?b"
	      show "inj_on ind {c | c < ?b}"
	      proof (rule inj_onI, simp)
	        fix x y 
	        assume e1: "x < ?b" and e2: "y < ?b" and e3: "ind x = ind y"
	        show "x = y"
	        proof (rule inj_onD)
	          show "inj_on ind {c | c \<le> x \<lsup> y}"
	            apply (rule b5)
	            apply (rule c3)
	            apply (cases x y rule: xHOL_Lemmas.linorder_le_cases)
	            apply (auto simp add: Lattice_Class.sup_max sup_max' Lattice_Class.sup_idem e1 e2)
	            done
	          show "ind x = ind y" by (rule e3)
	          show "x \<in> {c | c \<le> x \<lsup> y}"
	            by (simp add: sup_ub1)
	          show "y \<in> {c | c \<le> x \<lsup> y}"
	            by (simp add: sup_ub2)
	        qed
	      qed
	    next
	      apply_end (msafe_no_assms(inference))  
	      fix b assume d1: "b \<noteq> \<omax>" and d2: "?b = \<osuc> b"
	      from d1 have "b < \<osuc> b"
	        by (rule osuc_incr)
	      then have "b < ?b"
	        by (simp add: d2)
	      then have d3: "char b \<subset> A"
	        by (rule c3)
	      from d3 have d4: "inj_on ind {c | c \<le> b}"
	        by (rule b5)
	      have d5: "{c | c < ?b} = {c | c \<le> b}"
	        apply (auto simp add: d2 osuc_char2)
	        apply (rule order_le_less_trans)
	        apply (assumption)
	        apply (rule osuc_incr)
	        apply (rule d1)
	        done
	      from d4 d5 show "inj_on ind {c | c < ?b}"
	        by (simp)
	    qed
	    with ordinal_equipotent [THEN equipotentD1]
	    have c6: "\<^sEP>{:Rep_ordinal ?b:}{:A:}"
	      by (rule subequipotent_trans)
	    from c2 have c7: "\<^sEP>{:A:}{:Rep_ordinal ?b:}"
	      apply (intro subequipotent_trans [OF _ ordinal_equipotent [THEN equipotentD2]])
	      apply (rule subepIsurj [of _ ind])
	      apply (simp add: b3 Collect_image)
	      done
	    from ord_of_wdef2 [OF c7]
	    have c8 : "\<^sEP>{:Rep_ordinal (ord_of A):}{:Rep_ordinal ?b:}"
	      by (auto intro: subset_subequipotent simp add: ole_def)
	    from c8 c6 show "\<^sEP>{:Rep_ordinal (ord_of A):}{:A:}"
	      by (rule subequipotent_trans)
	  qed
	qed
qed

lemma ord_of_conv:
  "ord_of (A::'a set) = (\<LEAST> b::'a ordinal | \<^EP>{:A:}{:Rep_ordinal b:})"
  apply (rule sym)
  apply (rule Least_equality)
proof -
  show "\<^EP>{:A:}{:Rep_ordinal (ord_of A):}"
    by (rule Rep_ord_of)
next
  fix b::"'a ordinal"
  assume b1: "\<^EP>{:A:}{:Rep_ordinal b:}"
  show "ord_of A \<le> b"
    apply (rule ord_of_wdef2)
    apply (rule equipotentD1)
    apply (rule b1)
    done
qed

lemma ord_of_sEP:
  "ord_of A \<le> ord_of B \<Leftrightarrow> \<^sEP>{:A:}{:B:}"
proof (msafe_no_assms(inference))
  assume b1: "ord_of A \<le> ord_of B"
  have "\<^EP>{:A:}{:Rep_ordinal (ord_of A):}"
    by (simp add: Rep_ord_of)
  also from b1 have "\<^sEP>{:\<dots>:}{:Rep_ordinal (ord_of B):}"
    by (simp add: ole_def subset_subequipotent)
  also have "\<^EP>{:\<dots>:}{:B:}"
    by (rule equipotent_sym, simp add:  Rep_ord_of)
  finally show "\<^sEP>{:A:}{:B:}"
    by (this)
next
  assume a1: "\<^sEP>{:A:}{:B:}"
  show "ord_of A \<le> ord_of B"
    apply (rule ord_of_wdef2)
    apply (rule subequipotent_trans)
    apply (rule a1)
    apply (rule ord_of_wdef1)
    done
qed

lemma linear_sEP':
  fixes
    A :: "'a set" and
    B :: "'a set"
  shows
    "\<^sEP>{:A:}{:B:} \<or> \<^sEP>{:B:}{:A:}"
  apply (simp add: ord_of_sEP [symmetric])
  apply (rule linear)
  done


lemma linear_sEP:
  "\<^sEP>{:A:}{:B:} \<or> \<^sEP>{:B:}{:A:}"
  apply (multi_cases "A = \<emptyset>" "B = \<emptyset>")
  apply (simp_all add: empty_bot nempty_conv)
  apply (mauto(inference))
proof -
  fix
    a b
  assume
    b1: "a \<in> A" and
    b2: "b \<in> B"
  have
    b3: "\<^EP>{:A:}{:A \<times> {b}:}"
    apply (rule equipotent_sym)
    apply (rule equipotent_prod_singletonR [OF equipotent_refl])
    done
   have
    b4: "\<^EP>{:{a} \<times> B:}{:B:}"
    by (rule equipotent_prod_singletonL [OF equipotent_refl])
 from linear_sEP' [of "A \<times> {b}" "{a} \<times> B"] show
    "?thesis"
    apply (mauto(inference))
    apply (rule disjI1)
    apply (rule eq_subeq_trans)
    apply (rule b3)
    apply (rule subeq_eq_trans)
    apply (assumption)
    apply (rule b4)
    apply (rule disjI2)
    apply (rule eq_subeq_trans)
    apply (rule b4 [THEN equipotent_sym])
    apply (rule subeq_eq_trans)
    apply (assumption)
    apply (rule b3 [THEN equipotent_sym])
    done
qed


lemma ord_of_EP:
  "ord_of A = ord_of B \<Leftrightarrow> \<^EP>{:A:}{:B:}"
  by (simp add: order_eq_iff equipotent_iff ord_of_sEP)

interpretation 
  cardqord: 
    order 
      "\<^qspace>{:\<univ>-['a set]:}{:equipotent:}" 
      "\<^quotord>{:subequipotent:}{:equipotent:}"
  apply (rule cardqpo.orderIa)
  apply (simp add: quot_set_def)
  apply (msafe_no_assms(inference))
  apply (simp)
proof -
  fix 
    A :: "'a set" and
    B :: "'a set"
  from linear_sEP [of A B] show
    "\<^infopa>{:\<^eclass>{:A:}{:equipotent:}:}{:
      \<^quotord>{:subequipotent:}{:equipotent:}:}{:\<^eclass>{:B:}{:equipotent:}:} 
    \<or> \<^infopa>{:\<^eclass>{:B:}{:equipotent:}:}{:
      \<^quotord>{:subequipotent:}{:equipotent:}:}{:\<^eclass>{:A:}{:equipotent:}:}"
    by (auto simp add: quot_order_def rel2op_def)
qed


section {* Infinite sets *}

lemma infinite_card': 
  fixes F::"'a set"
  shows "infinite F \<Leftrightarrow> (\<forall> N::\<nat> \<bullet> \<^sEP>{:\<lclose>0\<dots>N\<ropen>:}{:F:})"
  apply (subst iff_conv_conj_imp)
  apply (simp add: finite_card')
  apply (rule conjI)
proof -
  show
    "(\<forall> N::\<nat> \<bullet> \<not>\<^sEP>{:F:}{:\<lclose>0\<dots>N\<ropen>:}) \<Rightarrow> (\<forall> N::\<nat> \<bullet> \<^sEP>{:\<lclose>0\<dots>N\<ropen>:}{:F:})"
    apply (mauto(wind))
    apply (mauto(inference))
  proof -
    fix
      N::"\<nat>"
    assume
      c1: "\<not>\<^sEP>{:F:}{:\<lclose>0\<dots>N\<ropen>:}"
    with linear_sEP [of "F" "\<lclose>0\<dots>N\<ropen>"] show
      "\<^sEP>{:\<lclose>0\<dots>N\<ropen>:}{:F:}"
      by (auto)
  qed
next
  apply_end (mauto(inference))
  fix
    N::"\<nat>"
  assume
    b1: "(\<forall> N::\<nat> \<bullet> \<^sEP>{:\<lclose>0\<dots>N\<ropen>:}{:F:})"
  then show
    "\<not>\<^sEP>{:F:}{:\<lclose>0\<dots>N\<ropen>:}"
    apply (rule contrapos_pn)
    apply (auto)
    apply (witness "Suc N")
    apply (auto)
  proof -
    assume
      c1: "\<^sEP>{:F:}{:\<lclose>0\<dots>N\<ropen>:}" and
      c2: "\<^sEP>{:\<lclose>0\<dots>Suc N\<ropen>:}{:F:}"
    from c2 c1 have
      c3: "\<^sEP>{:\<lclose>0\<dots>Suc N\<ropen>:}{:\<lclose>0\<dots>N\<ropen>:}"
      by (rule subequipotent_trans)
    with subequipotent_nat_interval_iff [of "0" "Suc N" "N"] show
      "\<False>"
      by (auto simp add: interval_defs)
  qed
qed

primrec
  nat_maps_to_chain :: "'a set \<rightarrow> \<nat> \<rightarrow> (\<nat> \<leftrightarrow> 'a)"
where
  "nat_maps_to_chain A 0 = \<emptyset>"
| "nat_maps_to_chain A (Suc n) 
   = (nat_maps_to_chain A n) \<union> 
     { (n \<mapsto> (\<some> a | a \<in> A \<and> a \<notin> \<zran> (nat_maps_to_chain A n))) }"

definition
  "nat_index A = (\<Union> N \<bullet> nat_maps_to_chain A N)"

lemma infinite_nat_index:
  assumes
    a1: "infinite F"
  shows
    "nat_index F \<in> \<univ>-[\<nat>] \<zinj> F"
  using a1
proof (auto simp add: infinite_card')
  assume
    b1: "(\<forall> N::\<nat> \<bullet> \<^sEP>{:\<lclose>0\<dots>N\<ropen>:}{:F:})"
{
  fix
    N
  have
    "nat_maps_to_chain F N \<in> \<lclose>0\<dots>N\<ropen> \<zinj> F"
  proof (induct "N")
    show
      "nat_maps_to_chain F 0 \<in> \<lclose>0\<dots>0\<ropen> \<zinj> F"
      apply (simp add: interval_defs)
      apply (mauto(fspace) msimp add: empty_functional converse_empty)
      done
  next
    fix
      N
    assume
      c1: "nat_maps_to_chain F N \<in> \<lclose>0\<dots>N\<ropen> \<zinj> F"
    have
      c2: "finite (nat_maps_to_chain F N)"
      apply (rule dom_finite_fun [OF c1 [THEN tinj_functional]])
      apply (simp add: c1 [THEN tinj_dom] interval_defs)
      done
    then have
      c3: "finite (\<zran> (nat_maps_to_chain F N))"
      by (rule fun_finite_ran)
    from c1 [THEN tinj_ran] have
      c4: "\<zran> (nat_maps_to_chain F N) \<subset> F"
    proof (auto)
      assume
        d1: "\<zran> (nat_maps_to_chain F N) = F"
      from 
        fun_card_dom [OF tinj_functional [OF c1]] 
        fun_card_dom [OF tinj_inv_functional [OF c1], symmetric]
      have
        d2: "card (\<zran> (nat_maps_to_chain F N)) = N"
        by (auto simp add: 
              inverse_card [of "nat_maps_to_chain F N"]
              tinj_dom [OF c1] cINTVLo_atLeastLessThan)
      from b1 [rule_format, of "Suc N"] d2 card_infinite [of "\<zran> (nat_maps_to_chain F N)"] have
        d4: "Suc N \<le> N"
        apply (subst (asm) d1 [symmetric])
        apply (subst (asm) finite_subequipotent_card)
        apply (auto simp add: cINTVLo_atLeastLessThan c3)
        done
      then show
        "\<False>"
        by (auto)
    qed
    then have
      c5: "(\<exists> a \<bullet> a \<in> F \<and> a \<notin> \<zran> (nat_maps_to_chain F N))"
      by (auto)
    from someI_ex [OF c5] c1 show
      "nat_maps_to_chain F (Suc N) \<in> \<lclose>0\<dots>Suc N\<ropen> \<zinj> F"
      apply (simp)
      apply (mauto(fspace) msimp add: insert_functional)
      apply (rule disjI1)
      apply (simp add: interval_defs)
      apply (auto simp add: interval_defs)
      done
  qed
} note b2 = this
{
  fix
    M::\<nat> and N::\<nat>
  have
    "M \<le> N \<Rightarrow> nat_maps_to_chain F M \<subseteq> nat_maps_to_chain F N"
    apply (induct "N")
    apply (simp)
    apply (simp add: less_Suc_eq_le le_less)
    apply (auto)
    done
} note b3 = this
  show
    "?thesis"
  proof (mauto(fspace) mintro!: functionalI msimp add: Z_inverse_mem)
    fix
      n a b
    assume
      c1: "(n \<mapsto> a) \<in> nat_index F" and
      c2: "(n \<mapsto> b) \<in> nat_index F"
    from c1 obtain N where
      c3: "(n \<mapsto> a) \<in> nat_maps_to_chain F N"
      by (auto simp add: nat_index_def)
    from c2 obtain M where
      c4: "(n \<mapsto> b) \<in> nat_maps_to_chain F M"
      by (auto simp add: nat_index_def)
    from c3 b3 [of "N" "max N M"] have
      c5: "(n \<mapsto> a) \<in> nat_maps_to_chain F (max N M)"
      by (auto)
    from c4 b3 [of "M" "max N M"] have
      c6: "(n \<mapsto> b) \<in> nat_maps_to_chain F (max N M)"
      by (auto)
    from c5 c6 show
      "a = b"
      by (simp add: b2 [of "max N M", THEN tinj_unique])
  next
    fix
      n m a
    assume
      c1: "(n \<mapsto> a) \<in> nat_index F" and
      c2: "(m \<mapsto> a) \<in> nat_index F"
    from c1 obtain N where
      c3: "(n \<mapsto> a) \<in> nat_maps_to_chain F N"
      by (auto simp add: nat_index_def)
    from c2 obtain M where
      c4: "(m \<mapsto> a) \<in> nat_maps_to_chain F M"
      by (auto simp add: nat_index_def)
    from c3 b3 [of "N" "max N M"] have
      c5: "(n \<mapsto> a) \<in> nat_maps_to_chain F (max N M)"
      by (auto)
    from c4 b3 [of "M" "max N M"] have
      c6: "(m \<mapsto> a) \<in> nat_maps_to_chain F (max N M)"
      by (auto)
    from c5 c6 show
      "n = m"
      apply (simp add: b2 [of "max N M", THEN tinj_unique])
      apply (rule tinj_inj [OF b2 [of "max N M"]])
      apply (auto simp add: interval_defs)
      done
  next
    show
      "\<zdom> (nat_index F) = \<univ>"
      apply (simp add: nat_index_def rel_Union_dom' tinj_dom  [OF b2])
      apply (auto)
      done
  next
    show
      "\<zran> (nat_index F) \<subseteq> F"
      apply (simp add: nat_index_def rel_Union_ran')
      using tinj_ran [OF b2]
      apply (auto simp add: eind_def)
      done
  qed
qed

lemma infinite_card: 
  fixes F::"'a set"
  shows "infinite F \<Leftrightarrow> \<^sEP>{:\<univ>-[\<nat>]:}{:F:}"
  using infinite_nat_index [THEN subequipotentI, of "F"]
proof (auto simp add: infinite_card')
  fix
    N::\<nat>
  assume
    b1: "\<^sEP>{:\<univ>-[\<nat>]:}{:F:}"
  then obtain f where
    b2: "f \<in> \<univ>-[\<nat>] \<zinj> F"
    by (auto simp add: subequipotent_def)
  with dres_subset_in_tfunI [OF tinj_tfun [OF b2], of "\<lclose>0\<dots>N\<ropen>"] have
    b3: "\<lclose>0\<dots>N\<ropen> \<zdres> f \<in> \<lclose>0\<dots>N\<ropen> \<zinj> F"
    apply (simp)
    apply (mauto(fspace))
    done
  then show
    "\<^sEP>{:\<lclose>0\<dots>N\<ropen>:}{:F:}"
    by (auto simp add: subequipotent_def)
qed

class infinite =
  assumes 
    nat_subep_UNIV: "\<^sEP>{:\<univ>-[\<nat>]:}{:\<univ>-['a]:}"
begin

lemma infinite_UNIV:
  "infinite \<univ>-['a]"
  apply (rule infinite_card [THEN iffD2])
  apply (rule nat_subep_UNIV)
  done

definition
  "nat_index_op = \<opof> (nat_index \<univ>-['a])"

lemma nat_index_op_inj:
  "inj nat_index_op"
  apply (simp add: nat_index_op_def)
  apply (rule fun_of_f_inj)
  apply (rule infinite_nat_index)
  apply (rule infinite_UNIV)
  done

end

lemma infinite_ep_infinite:
  assumes
    a1: "infinite A" and
    a2: "A \<asymp> B"
  shows
    "infinite B"
  using a1 subequipotent_trans [OF _ equipotentD1 [OF a2]]
  by (auto simp add: infinite_card)

lemma infinite_sep_infinite:
  assumes
    a1: "infinite A" and
    a2: "A \<preceq> B"
  shows
    "infinite B"
  using a1 subequipotent_trans [OF _ a2]
  by (auto simp add: infinite_card)

lemma finite_sub_infinite:
  assumes 
    a1: "finite F" and
    a2: "infinite A"
  shows
    "\<^sEP>{:F:}{:A:}"
  using a1 a2
  apply (subst (asm) finite_card)
  apply (subst (asm) infinite_card)
  apply (auto)
  apply (rule 
           subequipotent_trans 
             [OF _ subequipotent_trans [OF subequipotent_nat_interval_nat]])
  apply (auto intro: equipotentD1)
  done

lemma finite_neq_infinite:
  assumes 
    a1: "finite F" and
    a2: "infinite A"
  shows
    "\<^nEP>{:F:}{:A:}"
  using a1
proof (auto simp add: finite_card)
  fix
    N :: "\<nat>"
  assume
    b1: "F \<asymp> \<lclose>0\<dots>N\<ropen>" and
    b2: "F \<asymp> A"
  from b2 [symmetric] b1 have
    b3: "A \<asymp> \<lclose>0\<dots>N\<ropen>"
    by (rule equipotent_trans)
  moreover from a2 have
    b4: "A \<notasymp> \<lclose>0\<dots>N\<ropen>"
    by (auto simp add: finite_card)
  ultimately show
    "\<False>"
    by (contradiction)
qed

lemma seq_not_infinite_finite:
  assumes 
    a1: "A \<preceq> B"
  shows
    "\<not> (finite B \<and> infinite A)"
proof (mauto(inference) mintro!: notI)
  assume
    b1: "finite B" and
    b2: "infinite A"
  from 
    subequipotent_antisym [OF a1 finite_sub_infinite [OF b1 b2], symmetric] 
    finite_neq_infinite [OF b1 b2]
  show
    "\<False>"
    by (contradiction)
qed

lemma countable_card: 
  fixes F::"'a set"
  shows "countable F \<Leftrightarrow> \<^sEP>{:F:}{:\<univ>-[\<nat>]:}"
proof (auto simp add: countable_def)
  fix 
    f::"'a \<rightarrow> \<nat>"
  assume
    b1: "inj_on f F"
  show
    "\<^sEP>{:F:}{:\<univ>-[\<nat>]:}"
    apply (rule subequipotentI [of "F \<zdres> (\<graphof> f)"])
    apply (mauto(fspace) mintro!: functionalI)
    apply (auto simp add: dres_mem graph_of_def glambda_mem inj_onD [OF b1])
    done
next
  assume
    b1: "\<^sEP>{:F:}{:\<univ>-[\<nat>]:}"
  then obtain f where
    b2: "f \<in> F \<zinj> \<univ>-[\<nat>]"
    by (auto simp add: subequipotent_def)
  have
    "inj_on (\<opof> f) F"
    apply (rule inj_onI)
    apply (auto intro: tinj_inj [OF b2])
    done
  then show
    "(\<exists> f::'a \<rightarrow> \<nat> \<bullet> inj_on f F)"
    by (auto)
qed

abbreviation
  "countable_inf P
  \<defs> infinite P \<and> countable P"

lemma countable_inf_card: 
  fixes F::"'a set"
  shows "countable_inf F \<Leftrightarrow> \<^EP>{:F:}{:\<univ>-[\<nat>]:}"
  apply (simp add: infinite_card countable_card)
  apply (auto intro: subequipotent_antisym equipotentD1 equipotentD2)
  done

lemmas countable_infD = countable_inf_card [THEN iffD1]
lemmas countable_infI = countable_inf_card [THEN iffD2]

lemma finite_subeq_countable_inf:
  assumes
    a1: "finite F" and
    a2: "countable_inf A"
  shows
    "\<^sEP>{:F:}{:A:}"
  using a1 a2
  apply (subst (asm) countable_inf_card)
  apply (auto simp add: finite_card)
proof -
  fix
    N :: "\<nat>"
  assume
    b1: "\<^EP>{:F:}{:\<lclose>0\<dots>N\<ropen>:}" and
    b2: "\<^EP>{:A:}{:\<univ>-[\<nat>]:}"
  note b1
  also have "\<^sEP>{:\<lclose>0\<dots>N\<ropen>
    :}{:\<univ>-[\<nat>]:}"
    by (rule subequipotent_nat_interval_nat)
  also note b2 [symmetric]
  finally show
    "\<^sEP>{:F:}{:A:}"
    by (this)
qed

lemma infinite_card'': 
  fixes F::"'a set"
  shows "infinite F \<Leftrightarrow> (\<exists> F' \<bullet> F' \<subseteq> F \<and> countable_inf F')"
  apply (subst infinite_card)
  apply (subst countable_inf_card)
  apply (mauto(inference))
proof -
  assume
    b1: "\<^sEP>{:\<univ>-[\<nat>]:}{:F:}"
  have
    b2: "(\<exists> F' \<bullet> F' \<subseteq> F \<and> \<^EP>{:F':}{:\<univ>-[\<nat>]:})
    \<Leftrightarrow> (\<exists> F' \<bullet> F' \<subseteq> F \<and> \<^EP>{:\<univ>-[\<nat>]:}{:F':})"
    apply (mauto(wind))
    apply (auto intro: equipotent_sym)
    done
   from b1 show
    "(\<exists> F' \<bullet> F' \<subseteq> F \<and> \<^EP>{:F':}{:\<univ>-[\<nat>]:})"
    apply (simp add: b2)
    apply (auto simp add: subequipotent_eq_inj_on equipotent_eq_inj_on)
    done
next
  fix 
    F'
  assume
    b1: "F' \<subseteq> F" and
    b2: "\<^EP>{:F':}{:\<univ>-[\<nat>]:}"
  from b2 [symmetric] subset_subequipotent [OF b1] show
    "\<^sEP>{:\<univ>-[\<nat>]:}{:F:}"
    by (rule eq_subeq_trans)
qed

lemma finite_subeq_infinite:
  assumes
    a1: "finite F" and
    a2: "infinite A"
  shows
    "\<^sEP>{:F:}{:A:}"
  using a2
  apply (subst (asm) infinite_card'')
  apply (elim exE conjE)
  apply (rule subequipotent_trans)
  apply (rule finite_subeq_countable_inf [OF a1])
  apply (auto intro: subset_subequipotent)
  done

lemma infinite_partition:
  assumes
    a1: "infinite A"
  shows
    "(\<exists> \<P> \<bullet> 
      (\<forall> P | P \<in> \<P> \<bullet> countable_inf P) \<and> 
      Disjoint \<P> \<and>
      (\<Union>\<P>) = A)"
proof -
  let
    ?\<A> 
    = "{ \<P> | 
        (\<forall> P | P \<in> \<P> \<bullet> countable_inf P) \<and> 
        Disjoint \<P> \<and> 
        (\<Union>\<P>) \<subseteq> A}"
{
  fix
    \<P> P
  assume
    b1: "\<P> \<in> ?\<A>" and
    b2: "P \<in> \<P>"
  then have
    "countable_inf P"
    by (auto)
} note b2 = this
{
  fix
    \<P> P P'
  assume
    b1: "\<P> \<in> ?\<A>" and
    b2: "P \<in> \<P>" and
    b3: "P' \<in> \<P>" and
    b4: "P \<inter> P' \<noteq> \<emptyset>"
  then have
    "P = P'"
    apply (intro DisjointD1')
    apply (auto simp add: disjoint_def)
    done
} note b3 = this
{
  fix
    \<P> P P'
  assume
    b1: "\<P> \<in> ?\<A>" and
    b2: "P \<in> \<P>" and
    b3: "P' \<in> \<P>" and
    b4: "P = P'"
  then have
    "P \<inter> P' \<noteq> \<emptyset>"
    by (auto)
} note b3' = this
{
  fix
    \<P>
  assume
    b1: "\<P> \<in> ?\<A>"
  then have
    "(\<Union>\<P>) \<subseteq> A"
    by (auto)
} note b4 = this 
  have  
    "(\<exists> \<P> \<bullet> \<P> \<in> ?\<A> \<and> (\<forall> \<P>' \<bullet> \<P>' \<in> ?\<A> \<Rightarrow> \<P> \<subseteq> \<P>' \<Rightarrow> \<P>' = \<P>))"
  proof (rule subset_Zorn' [of "?\<A>", simplified Ball_def Bex_def])
    fix 
      C
    assume
      c1: "subset.chain ?\<A> C"
    then have
      c2: "C \<subseteq> ?\<A>"
      by (simp add: pred_on.chain_def)
    show
      "\<Union>C \<in> ?\<A>"
      apply (simp add: Disjoint_def' disjoint_def)
      apply (mauto(inference))
    proof -
      fix
        \<P> P
      assume
        d1: "\<P> \<in> C" and
        d2: "P \<in> \<P>"
      from c2 [THEN subsetD, THEN b2, OF d1 d2] show
        "countable P"
        "infinite P"
        by (auto)
    next
      fix
        \<P> P \<P>' P'
      assume
        d1: "\<P> \<in> C" and
        d2: "P \<in> \<P>" and
        d3: "\<P>' \<in> C" and
        d4: "P' \<in> \<P>'" and
        d5: "P \<inter> P' \<noteq> \<emptyset>"
      from pred_on.chain_total [OF c1 d1 d3] have
        d6: "\<P> \<subseteq> \<P>' \<or> \<P>' \<subseteq> \<P>"
        by (auto)
      then show
        "P = P'"
      proof (mauto(inference))
        assume
          e1: "\<P> \<subseteq> \<P>'"
        from c2 [THEN subsetD, THEN b3, OF d3 subsetD [OF e1 d2] d4 d5] show
          "P = P'"
          by (this)
      next
        assume
          e1: "\<P>' \<subseteq> \<P>"      
        from c2 [THEN subsetD, THEN b3, OF d1 d2 subsetD [OF e1 d4] d5] show
          "P = P'"
          by (this)
      qed
    next
      fix
        \<P> P \<P>'
      assume
        d1: "\<P> \<in> C" and
        d2: "P \<in> \<P>" and
        d3: "\<P>' \<in> C" and
        d4: "P \<in> \<P>'"
      from pred_on.chain_total [OF c1 d1 d3] have
        "\<P> \<subseteq> \<P>' \<or> \<P>' \<subseteq> \<P>"
        by (auto)
      then show
        "P \<inter> P \<noteq> \<emptyset>"
      proof (mauto(inference))
        assume
          e1: "\<P> \<subseteq> \<P>'"      
        from c2 [THEN subsetD, THEN b3', OF d3 subsetD [OF e1 d2] d4] show
          "P \<inter> P \<noteq> \<emptyset>"
          by (simp)
      next
        assume
          e1: "\<P>' \<subseteq> \<P>"      
        from c2 [THEN subsetD, THEN b3', OF d1 d2 subsetD [OF e1 d4]] show
          "P \<inter> P \<noteq> \<emptyset>"
          by (simp)
      qed
    next
      show
        "\<Union>\<Union>C \<subseteq> A"
      proof (auto)
        fix
          \<P> P a
        assume
          d1: "\<P> \<in> C" and
          d2: "P \<in> \<P>" and
          d3: "a \<in> P"      
        from c2 [THEN subsetD, THEN b4, OF d1] d2 d3 show
          "a \<in> A"
          by (auto)
      qed
    qed
  qed
  then obtain \<P> where  
    b5: "\<P> \<in> ?\<A>" and 
    b6: "(\<forall> \<P>' \<bullet> \<P>' \<in> ?\<A> \<Rightarrow> \<P> \<subseteq> \<P>' \<Rightarrow> \<P>' = \<P>)"
    by (auto)
  from b6 have
    b7: "finite (A \<setminus> (\<Union>\<P>))"
  proof (rule contrapos_pp)
    assume
      c1: "infinite (A \<setminus> (\<Union>\<P>))"
    then obtain f where
      c2: "f \<in> \<univ>-[\<nat>] \<zinj> (A \<setminus> (\<Union>\<P>))"
      by (auto simp add: infinite_card subequipotent_def)
    then have
      c3: "f \<in> \<univ>-[\<nat>] \<zbij> (\<zran> f)"
      by (mauto(fspace))
    from equipotentI [OF c3] have
      c4: "countable (\<zran> f) \<and> infinite (\<zran> f)"
      by (simp add: equipotentD1 equipotentD2 countable_card infinite_card)
    from c3 have
      c5: "\<zran> f \<noteq> \<emptyset>"
      apply (simp add: nempty_conv)
      apply (witness "f\<cdot>0")
      apply (rule bij_range)
      apply (auto)
      done
    from tinj_ran [OF c2] c4 c5 have
      c6: "insert (\<zran> f) \<P> \<in> ?\<A>"
      apply (simp add: Disjoint_def' disjoint_def)
      apply (mauto(inference))
      apply (simp add: b2 [OF b5])
      apply (simp add: b2 [OF b5])
      apply (rule b3 [OF b5])
      apply (simp)
      apply (simp)
      apply (simp)
      apply (rule b3' [OF b5])
      apply (simp)+
      apply (rule b4 [OF b5])
      done
    from tinj_ran [OF c2] have
      c7: "(\<zran> f) \<inter> (\<Union>\<P>) = \<emptyset>"
      by (auto simp add: subset_def)
    with c5 have
      c8: "(\<zran> f) \<notin> \<P>"
      by (auto)
    then have
      c9: "\<P> \<subseteq> insert (\<zran> f) \<P>" and
      c10: "\<P> \<noteq> insert (\<zran> f) \<P>"
      by (auto)
    from c4 c6 c9 c10 show
      "\<not>(\<forall> \<P>' \<bullet> \<P>' \<in> ?\<A> \<Rightarrow> \<P> \<subseteq> \<P>' \<Rightarrow> \<P>' = \<P>)"
      apply (simp)
      apply (witness "insert (\<zran> f) \<P>")
      apply (simp)
      done
  qed
  from a1 have
    b8: "\<Union>\<P> \<noteq> \<emptyset>"
    apply (rule contrapos_nn)
    using b7
    apply (simp only:)
    apply (auto)
    done
  then obtain P where
    b9: "P \<in> \<P>"
    by (auto)
  from b7 b2 [OF b5 b9] have
    b10: "countable (P \<union> (A \<setminus> (\<Union>\<P>))) \<and> infinite (P \<union> (A \<setminus> (\<Union>\<P>)))"
    by (simp add: countable_finite)
  let
    ?P' = "P \<union> (A \<setminus> (\<Union>\<P>))" 
  let
    ?\<P>' = "insert ?P' (\<P> \<setminus> {P})"
  from b5 b10 have
    b11: "(\<forall> P \<bullet> P \<in> ?\<P>' \<Rightarrow> countable P \<and> infinite P)"
    by (auto)
  from b5 b9 b3' [OF b5 b9 b9] have
    b12: "(\<forall> P Q \<bullet> P \<in> ?\<P>' \<and> Q \<in> ?\<P>' \<Rightarrow> P \<inter> Q \<noteq> \<emptyset> \<Leftrightarrow> P = Q)"
  proof (mauto_full(inference) msimp add: Disjoint_def' disjoint_def mdel: iffI)
    fix
      Q
    assume
      c1: "Q \<in> \<P>" and
      c2: "Q \<noteq> P"
    from c2 b3 [OF b5 b9 c1] have
      c3: "P \<inter> Q = \<emptyset>"
      by (auto)
    from b4 [OF b5] c1 have
      c4: "(A \<setminus> (\<Union>\<P>)) \<inter> Q = \<emptyset>"
      by (auto)
    from c3 c4 have
      c5: "?P' \<inter> Q = \<emptyset>"
      by (auto)
    from c5 b3' [OF b5 b9 b9] have
      c6: "?P' \<noteq> Q"
      by (auto)
    from c5 c6 show
      "?P' \<inter> Q \<noteq> \<emptyset> \<Leftrightarrow> ?P' = Q"
      by (auto)
    then show
      "Q \<inter> ?P' \<noteq> \<emptyset> \<Leftrightarrow> Q = ?P'"
      by (auto)
  qed
  from b4 [OF b5] b9 have
    b13: "\<Union>?\<P>' = A"
    by (auto)
  from b11 b12 b13 show
    "?thesis"
    apply (witness "insert (P \<union> (A \<setminus> (\<Union>\<P>))) (\<P> \<setminus> {P})")
    apply (simp add: Disjoint_def' disjoint_def)
    done
qed  

lemma nat_sum_card:
  "\<^EP>{:\<univ>-[\<nat>] <+> \<univ>-[\<nat>]:}{:\<univ>-[\<nat>]:}"
  apply (rule equipotentI [of "\<graphof> sum_encode"])
  apply (mauto(fspace) mintro!: functionalI)
  using
    bij_sum_encode [THEN bij_is_inj, THEN injD]
    bij_sum_encode [THEN bij_is_surj, THEN surjD]
  apply (auto simp add: graph_of_def glambda_def Z_ran_def)
  done

lemma countable_inf_part:
  assumes
    a1: "countable_inf A" 
  shows
    "(\<exists> B C | B \<subseteq> A \<and> C \<subseteq> A \<and> disjoint B C \<bullet> 
       \<^EP>{:B:}{:A:} \<and> \<^EP>{:C:}{:A:} \<and> B \<union> C = A)"
proof -
  from equipotent_trans [OF a1 [THEN countable_infD] nat_sum_card [symmetric]]  obtain f where
    b1: "f \<in> A \<zbij> (\<univ>-[\<nat>] <+> \<univ>-[\<nat>])"
    by (auto simp add: equipotent_def)
  let
    ?L = "range Inl"
  have 
    b2: "(\<glambda> n::\<nat> \<bullet> Inl n) \<in> \<univ>-[\<nat>] \<zbij> ?L"
    apply (mauto(fspace))
    apply (auto simp add: Z_dom_def Z_ran_def glambda_mem)
    done
  let
    ?R = "range Inr"
  have 
    b3: "(\<glambda> n::\<nat> \<bullet> Inr n) \<in> \<univ>-[\<nat>] \<zbij> ?R"
    apply (mauto(fspace))
    apply (auto simp add: Z_dom_def Z_ran_def glambda_mem)
    done
  let
    ?AL = "{ a | a \<in> A \<and> f\<cdot>a \<in> ?L }" and
    ?AR = "{ a | a \<in> A \<and> f\<cdot>a \<in> ?R }"
  have
    b4: "disjoint ?AL ?AR"
    by (auto simp add: disjoint_def)
  from b1 [THEN bij_dom] have
    b5: "?AL \<union> ?AR = A"
    apply (auto simp add: b1 [THEN bij_beta] image_def)
    apply (rule sum.exhaust)
    apply (rule exI)
    apply (auto)
    done
  from b1 have
    b6: "?AL \<zdres> f \<in> ?AL \<zbij> ?L"
    apply (mauto(fspace) mintro!: dres_functional dres_conv_functional)
    apply (simp_all add: bij_dom [OF b1])
  proof -
    show
      "\<zdom> (?AL \<zdres> f) = ?AL"
      by (auto simp add: Z_dres_dom bij_dom [OF b1])
    show
      "\<zran> (?AL \<zdres> f) = ?L"
    proof (auto simp add: dres_mem Z_ran_def bij_beta [OF b1])
      fix
        n :: "\<nat>"
      from bij_ran [OF b1] have
        c1: "Inl n \<in> \<zran> f"
        by (auto)
      then obtain a where
        c2: "(a \<mapsto> Inl n) \<in> f"
        by (auto)
      with bij_dom [OF b1] have
        c3: "a \<in> A"
        by (auto)
      show
        "(\<exists> a \<bullet> a \<in> A \<and> f\<cdot>a \<in> range Inl \<and> (a, Inl n) \<in> f)"
        apply (witness "a")
        apply (simp add: c2 c3 bij_beta [OF b1 c2])
        done
    qed
  qed
  from 
    b6 [THEN equipotentI] 
    b2 [THEN equipotentI, symmetric] 
    a1 [THEN countable_infD, symmetric]
  have
    b7: "\<^EP>{:?AL:}{:A:}"
    by (auto intro: equipotent_trans)
  from b1 have
    b8: "?AR \<zdres> f \<in> ?AR \<zbij> ?R"
    apply (mauto(fspace) mintro!: dres_functional dres_conv_functional)
    apply (simp_all add: bij_dom [OF b1])
  proof -
    show
      "\<zdom> (?AR \<zdres> f) = ?AR"
      by (auto simp add: Z_dres_dom bij_dom [OF b1])
    show
      "\<zran> (?AR \<zdres> f) = ?R"
    proof (auto simp add: dres_mem Z_ran_def bij_beta [OF b1])
      fix
        n :: "\<nat>"
      from bij_ran [OF b1] have
        c1: "Inr n \<in> \<zran> f"
        by (auto)
      then obtain a where
        c2: "(a \<mapsto> Inr n) \<in> f"
        by (auto)
      with bij_dom [OF b1] have
        c3: "a \<in> A"
        by (auto)
      show
        "(\<exists> a \<bullet> a \<in> A \<and> f\<cdot>a \<in> range Inr \<and> (a, Inr n) \<in> f)"
        apply (witness "a")
        apply (simp add: c2 c3 bij_beta [OF b1 c2])
        done
    qed
  qed
  from 
    b8 [THEN equipotentI] 
    b3 [THEN equipotentI, symmetric] 
    a1 [THEN countable_infD, symmetric]
  have
    b9: "\<^EP>{:?AR:}{:A:}"
    by (auto intro: equipotent_trans)
  from b7 b9 b4 b5 show
    "?thesis"
    apply (witness "?AL")
    apply (witness "?AR")
    apply (auto)
    done
qed

lemma infinite_part:
  assumes
    a1: "infinite A" 
  shows
    "(\<exists> B C | B \<subseteq> A \<and> C \<subseteq> A \<and> disjoint B C \<bullet> 
       \<^EP>{:B:}{:A:} \<and> \<^EP>{:C:}{:A:} \<and> B \<union> C = A)"
proof -
  from infinite_partition [OF a1] obtain \<P> where
    b1 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> countable_inf P)" and
    b2: "Disjoint \<P>" and
    b3: "\<Union>\<P> = A"
    by (auto)
  have
    "(\<forall> P | P \<in> \<P> \<bullet> 
      (\<exists> X Y | X \<subseteq> P \<and> Y \<subseteq> P \<and> disjoint X Y \<bullet> 
        \<^EP>{:X:}{:P:} \<and> \<^EP>{:Y:}{:P:} \<and> X \<union> Y = P))"
    by (mauto(inference) mintro: countable_inf_part [OF b1])
  then obtain l r where
    b4 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> 
        l P \<subseteq> P \<and> r P \<subseteq> P \<and> disjoint (l P) (r P) \<and>
        \<^EP>{:l P:}{:P:} \<and> \<^EP>{:r P:}{:P:} \<and> (l P) \<union> (r P) = P)" and
    b41 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> l P \<subseteq> P)" and
    b42 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> r P \<subseteq> P)" and
    b43 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> disjoint (l P) (r P))" and
    b44 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> \<^EP>{:l P:}{:P:})" and
    b45 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> \<^EP>{:r P:}{:P:})" and
    b46 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> (l P) \<union> (r P) = P)"
    apply (subst (asm) qual_ax_choice_eq)
    apply (subst (asm) qual_ax_choice_eq)
    apply (auto)
    done
  have
    b50 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> l P \<noteq> \<emptyset>)"
  proof (mauto(inference))
    fix
      P
    assume
      c1: "P \<in> \<P>"
    from b44 [OF c1, THEN equipotentD2] b2 [THEN DisjointD0] c1 empty_glb [of "P"] show
      "l P \<noteq> \<emptyset>"
    by (auto)
  qed
  have
    b5: "inj_on l \<P>"
  proof (rule inj_onI)
    fix
      P P'
    assume
      c1: "P \<in> \<P>" and
      c2: "P' \<in> \<P>" and
      c3: "l P = l P'"
    from b50 [OF c1] have
      c4: "l P \<noteq> \<emptyset>"
      by (auto)
    from b41 [OF c1] b41 [OF c2] c3 c4 have
      c5: "\<not> disjoint P P'"
      by (auto simp add: disjoint_def)
    from DisjointD1' [OF b2 c1 c2 c5]  show
      "P = P'"
      by (this)
  qed
  have
    b60 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> r P \<noteq> \<emptyset>)"
  proof (mauto(inference))
    fix
      P
    assume
      c1: "P \<in> \<P>"
    from b45 [OF c1, THEN equipotentD2] b2 [THEN DisjointD0] c1 empty_glb [of "P"] show
      "r P \<noteq> \<emptyset>"
    by (auto)
  qed
  have
    b6: "inj_on r \<P>"
  proof (rule inj_onI)
    fix
      P P'
    assume
      c1: "P \<in> \<P>" and
      c2: "P' \<in> \<P>" and
      c3: "r P = r P'"
    from b60 [OF c1] have
      c4: "r P \<noteq> \<emptyset>"
      by (auto)
    from b42 [OF c1] b42 [OF c2] c3 c4 have
      c5: "\<not> disjoint P P'"
      by (auto simp add: disjoint_def)
    from DisjointD1' [OF b2 c1 c2 c5]  show
      "P = P'"
      by (this)
  qed
  have
    b7: "Disjoint { P | P \<in> \<P> \<bullet> l P }"
    apply (rule DisjointI)
    apply (mauto_full(inference))
    using b50
    apply (fast)
    apply (rule disjoint_left_mono [OF b41])
    apply (assumption)
    apply (rule disjoint_right_mono [OF b41])
    apply (assumption)
    apply (rule b2 [THEN DisjointD1])
    using b5 [THEN inj_on_iff]
    apply (auto)
    done
  have
    b8: "Disjoint { P | P \<in> \<P> \<bullet> r P }"
    apply (rule DisjointI)
    apply (mauto_full(inference))
    using b60
    apply (fast)
    apply (rule disjoint_left_mono [OF b42])
    apply (assumption)
    apply (rule disjoint_right_mono [OF b42])
    apply (assumption)
    apply (rule b2 [THEN DisjointD1])
    using b6 [THEN inj_on_iff]
    apply (auto)
    done
  let
    ?AL = "(\<Union> P | P \<in> \<P> \<bullet> l P)" and
    ?AR = "(\<Union> P | P \<in> \<P> \<bullet> r P)"
  show
    "?thesis"
    apply (witness "?AL")
    apply (witness "?AR")
  proof (mauto(inference))
    from b3 b4 show
      "?AL \<subseteq> A"
      by (auto simp add: eind_def)
  next
    from b3 b4 show
      "?AR \<subseteq> A"
      by (auto simp add: eind_def)
  next
    have 
      "?AL \<union> ?AR
      = (\<Union> P | P \<in> \<P> \<bullet> l P \<union> r P)"
      by (auto)
    also have "\<dots>
      = \<Union>\<P>"
      using b46 
      by (auto simp add: eind_def) 
    finally show
      "?AL \<union> ?AR = A"
      by (simp add: b3)
  next
    from b4 have
      c1 [rule_format]: "(\<forall> P | P \<in> \<P> \<bullet> disjoint (l P) (r P))"
      by (auto)
    show
      "disjoint (\<Union> P | P \<in> \<P> \<bullet> l P) (\<Union> P | P \<in> \<P> \<bullet> r P)"
    proof (auto simp add: disjoint_right_Union_iff disjoint_left_Union_iff)
      fix
        P Q
      assume
        d1: "P \<in> \<P>" and
        d2: "Q \<in> \<P>"
      then show
        "disjoint (l P) (r Q)"
        apply (cases "P = Q")
        apply (simp add: c1)
        apply (rule disjoint_right_mono)
        apply (rule b42)
        apply (assumption)
        apply (rule disjoint_left_mono)
        apply (rule b41)
        apply (assumption)
        apply (rule DisjointD1)
        apply (rule b2)
        apply (auto)
        done
    qed
  next
    have
      "\<^EP>{:(\<Union> P | P \<in> \<P> \<bullet> l P):}{:(\<Union> P | P \<in> \<P> \<bullet> P):}"
      apply (rule equipotent_iUnion)
      using b7 b2 b5 inj_on_id [of "\<P>"] b44
      apply (auto simp add: eind_def)
      done
    with b3 show
      "\<^EP>{:(\<Union> P | P \<in> \<P> \<bullet> l P):}{:A:}"
      by (simp add: eind_def)
  next
    have
      "\<^EP>{:(\<Union> P | P \<in> \<P> \<bullet> r P):}{:(\<Union> P | P \<in> \<P> \<bullet> P):}"
      apply (rule equipotent_iUnion)
      using b8 b2 b6 inj_on_id [of "\<P>"] b45
      apply (auto simp add: eind_def)
      done
    with b3 show
      "\<^EP>{:(\<Union> P | P \<in> \<P> \<bullet> r P):}{:A:}"
      by (simp add: eind_def)
  qed
qed
  
lemma infinite_sum_part:
  fixes
    A :: "'a set"
  assumes
    a1: "infinite A" 
  shows
    "(\<exists> (B::'a set) (C::'a set) \<bullet> 
       \<^EP>{:B:}{:A:} \<and> \<^EP>{:C:}{:A:} \<and> \<^EP>{:B <+> C:}{:A:})"
proof -
  from infinite_part [OF a1] obtain B C where
    b1: "B \<subseteq> A" and
    b2: "C \<subseteq> A" and
    b3: "disjoint B C" and
    b4: "\<^EP>{:B:}{:A:}" and
    b5: "\<^EP>{:C:}{:A:}" and
    b6: "B \<union> C = A"
    by (auto)
  from equipotent_Plus_union [OF b3] b4 b5 show
    "?thesis"
    by (auto simp add: b6)
qed

lemma infinite_sum_part':
  fixes
    A :: "'a set"
  assumes
    a1: "\<^sEP>{:\<univ>-['a]:}{:\<univ>-['b]:}" and
    a2: "\<^sEP>{:\<univ>-['a]:}{:\<univ>-['c]:}" and
    a3: "infinite A" 
  shows
    "(\<exists> (B::'b set) (C::'c set) \<bullet> 
       \<^EP>{:B:}{:A:} \<and> \<^EP>{:C:}{:A:} \<and> \<^EP>{:B <+> C:}{:A:})"
proof -
  from infinite_sum_part [OF a3] obtain B' :: "'a set" and C' :: "'a set" where
    b1: "\<^EP>{:B':}{:A:}" and
    b2: "\<^EP>{:C':}{:A:}" and
    b3: "\<^EP>{:B' <+> C':}{:A:}"
    by (auto)
  from a1 obtain f where
    b4: "f \<in> \<univ>-['a] \<zinj> \<univ>-['b]"
    by (auto simp add: subequipotent_def)
  then have
    b4': "B' \<zdres> f \<in> B' \<zinj> \<univ>-['b]"
    apply (mauto(fspace))
    apply (simp add: Z_dres_dom)
    done
  note b4'' = equipotentIinj_on' [OF fun_of_f_inj_on [OF b4'], symmetric]
  from a2 obtain g where
    b5: "g \<in> \<univ>-['a] \<zinj> \<univ>-['c]"
    by (auto simp add: subequipotent_def)
  then have
    b5': "C' \<zdres> g \<in> C' \<zinj> \<univ>-['c]"
    apply (mauto(fspace))
    apply (simp add: Z_dres_dom)
    done
  note b5'' = equipotentIinj_on' [OF fun_of_f_inj_on [OF b5'], symmetric]
  note b6 = equipotent_Plus_cong [OF b4'' b5'']
  from 
    equipotent_trans [OF b4'' b1]  
    equipotent_trans [OF b5'' b2]
    equipotent_trans [OF b6 b3]
  show
    "?thesis"
    by (auto)
qed    

lemma infinite_sum':
  fixes
    A :: "'a set"
  assumes
    a1: "infinite A"
  shows
    "\<^EP>{:A <+> A:}{:A:}"
proof -
  from infinite_sum_part [OF a1] obtain B' :: "'a set" and C' :: "'a set" where
    b1: "\<^EP>{:B':}{:A:}" and
    b2: "\<^EP>{:C':}{:A:}" and
    b3: "\<^EP>{:B' <+> C':}{:A:}"
    by (auto)
  from equipotent_Plus_cong [OF b1 b2, symmetric] b3 show
    "?thesis"
    by (rule equipotent_trans)
qed

definition
  "sum_encode_map A = (\<some> f | f \<in> (A <+> A) \<zbij> A)"

lemma sum_encode_map_bij:
  assumes
    a1: "infinite A"
  shows
    "sum_encode_map A \<in> (A <+> A) \<zbij> A"
  using a1 [THEN infinite_sum']
  apply (simp add: sum_encode_map_def equipotent_def)  
  apply (rule someI_ex)
  apply (assumption)
  done

definition
  "sum_decode_map A = (sum_encode_map A)\<^sup>\<sim>"

lemma sum_decode_map_bij:
  assumes
    a1: "infinite A"
  shows
    "sum_decode_map A \<in> A \<zbij> (A <+> A)"
  apply (simp add: sum_decode_map_def)
  apply (rule bij_inv_bij)
  apply (rule sum_encode_map_bij [OF a1])
  done

context infinite
begin

definition
  "sum_encode_op = \<opof>(sum_encode_map \<univ>-['a])"

lemma sum_encode_op_bij:
  "bij sum_encode_op"
  apply (simp add: sum_encode_op_def)
  apply (rule fun_of_f_bij)
  using sum_encode_map_bij [OF infinite_UNIV]
  apply (simp)
  done

definition
  "iInl x = sum_encode_op (Inl x)"

definition
  "iInr x = sum_encode_op (Inr x)"

definition
  "sum_decode_op = \<opof>(sum_decode_map \<univ>-['a])"

lemma sum_decode_op_bij:
  "bij sum_decode_op"
  apply (simp add: sum_decode_op_def)
  apply (rule fun_of_f_bij)
  using sum_decode_map_bij [OF infinite_UNIV]
  apply (simp)
  done

lemma sum_encode_op_inv:
  "sum_decode_op (sum_encode_op x) = x"
  apply (simp add: sum_decode_op_def sum_encode_op_def sum_decode_map_def)
  apply (rule bij_inv_beta2 [OF sum_encode_map_bij])
  apply (auto simp add: infinite_UNIV)
  done

lemma sum_decode_op_inv:
  "sum_encode_op (sum_decode_op x) = x"
  apply (simp add: sum_decode_op_def sum_encode_op_def sum_decode_map_def)
  apply (rule bij_inv_beta1 [OF sum_encode_map_bij])
  apply (auto simp add: infinite_UNIV)
  done

lemma isumE: 
  assumes 
   a1: "\<And> x::'a \<bullet> s = iInl x \<turnstile> P" and 
   a2: "\<And> y::'a \<bullet> s = iInr y \<turnstile> P"
  shows 
    "P"
  apply (cases "sum_decode_op s")
  apply (rule a1)
  apply (simp add: iInl_def)
  apply (rule arg_cong [of "sum_decode_op s" _ "sum_encode_op", simplified sum_decode_op_inv])
  apply (assumption)
  apply (rule a2)
  apply (simp add: iInr_def)
  apply (rule arg_cong [of "sum_decode_op s" _ "sum_encode_op", simplified sum_decode_op_inv])
  apply (assumption)
  done

definition
  "isum_case f g z = \<case> sum_decode_op z \<of> Inl a \<longrightarrow> f a | Inr b \<longrightarrow> g b \<esac>"

end

lemma infinite_sum:
  assumes
    a1: "infinite B" and
    a2: "\<^sEP>{:A:}{:B:}"
  shows
    "\<^EP>{:A <+> B:}{:B:}"
proof (rule subequipotent_antisym)
  from subequipotent_Plus_cong [OF a2 subequipotent_refl] infinite_sum' [OF a1] show
    "\<^sEP>{:A <+> B:}{:B:}"
    by (rule subeq_eq_trans)
next
  show
    "\<^sEP>{:B:}{:A <+> B:}"
    apply (rule subequipotent_trans [OF _ subset_subequipotent])
    apply (rule equipotentIinj_on' [OF inj_Inr, THEN equipotentD1, of "B"])
    apply (auto)
    done
qed

lemma nat_prod_card:
  "\<^EP>{:\<univ>-[\<nat>] \<times> \<univ>-[\<nat>]:}{:\<univ>-[\<nat>]:}"
  apply (rule equipotentI [of "\<graphof> prod_encode"])
  apply (mauto(fspace) mintro!: functionalI)
  using
    bij_prod_encode [THEN bij_is_inj, THEN injD]
    bij_prod_encode [THEN bij_is_surj, THEN surjD]
  apply (auto simp add: graph_of_def glambda_def Z_ran_def eind_def)
  done

lemma countable_inf_prod:
  assumes
    a1: "countable_inf A" 
  shows
    "\<^EP>{:A \<times> A:}{:A:}"
proof -
  note b1 = a1 [THEN countable_inf_card [THEN iffD1]] 
  from
    equipotent_prod_cong [OF b1 b1]
    nat_prod_card 
    b1 [symmetric]
  show
    "?thesis"
    by (auto intro: equipotent_trans)
qed

lemma Times_empty' [simp]:
  "\<emptyset> = A \<times> B \<Leftrightarrow> A = \<emptyset> \<or> B = \<emptyset>"
  using Times_empty [of "A" "B"]
  by (auto)

lemma finite_prod_card:
  fixes
    A::"'a set" and
    B::"'b set"
  assumes
    a1: "finite A" and
    a2: "finite B"
  shows
    "card (A \<times> B) = (card A) * (card B)"
  using a1
proof (induct "A" set: finite)
  show
    "card (\<emptyset> \<times> B) = (card \<emptyset>) * (card B)"
    by (auto)
next
  fix
    a::"'a" and
    A::"'a set"
  assume
    b1: "finite A" and
    b2: "card (A \<times> B) = (card A) * (card B)" and
    b3: "a \<notin> A"
  have
    "(insert a A) \<times> B 
    = {a} \<times> B \<union> A \<times> B"
    by (auto)
  also have
    b6: "card ({a} \<times> B \<union> A \<times> B) 
    = card ({a} \<times> B) + card (A \<times> B)"
    apply (rule card_Un_disjoint)
    using a2 b1 b3
    apply (auto simp add: linsert_def eind_def)
    done
  also from a2 have
    b5: "card ({a} \<times> B) = card B"
    apply (induct "B" set: finite)
    apply (auto simp add: linsert_def eind_def)
    done
  finally show 
    "card ((insert a A) \<times> B) = (card (insert a A)) * (card B)"
    using a2 b1 b3
    by (auto)
qed

lemma finite_card_wit:
  "\<card>A = Suc N \<Leftrightarrow> (\<exists> x A' \<bullet> x \<notin> A' \<and> finite A' \<and> A = insert x A' \<and> \<card>A' = N)"
proof (auto)
  assume
    b1: "\<card>A = Suc N"
  then have
    b2: "finite A"
    apply (rule contrapos_pp)
    apply (simp add: card_infinite)
    done
  from b1 have
    b3: "A \<noteq> \<emptyset>"
        by (auto)
  then obtain x where
    b4: "x \<in> A"
    by (auto)
  then have
    b5: "A = insert x (A \<setminus> {x})"
    by (auto)
  from b2 have
    b6: "finite (A \<setminus> {x})"
    apply (rule rev_finite_subset)
    apply (auto)
    done
  from b6 b2 b4 b1 show
    "(\<exists> x A' \<bullet> x \<notin> A' \<and> finite A' \<and> A = insert x A' \<and> \<card>A' = N)"
    apply (witness "x")
    apply (witness "A \<setminus> {x}")
    apply (auto)
    done
qed

lemma rel_oride_inverse:
  "(f \<oplus> g)\<^sup>\<sim> = ((\<zdom> g \<zdsub> f)\<^sup>\<sim>) \<union> (g\<^sup>\<sim>)"
  by (auto simp add: rel_oride_def)  

lemma infinite_prod':
  assumes
    a1: "infinite A" 
  shows
    "\<^EP>{:A \<times> A:}{:A:}"
proof -
  let
    ?\<A> = "{ S f | S \<subseteq> A \<and> f \<in> (S \<times> S) \<zbij> S \<bullet> f }"
  have  
    "(\<exists> f \<bullet> f \<in> ?\<A> \<and> (\<forall> f' \<bullet> f' \<in> ?\<A> \<Rightarrow> f \<subseteq> f' \<Rightarrow> f' = f))"
  proof (rule subset_Zorn' [of "?\<A>", simplified Ball_def Bex_def])
    fix 
      C
    assume
      c1: "subset.chain ?\<A> C"
    then have
      c2: "C \<subseteq> ?\<A>" 
      by (auto simp add: pred_on.chain_def)
    then have
      c2' [rule_format]: "(\<forall> f | f \<in> C \<bullet> (\<exists> S | S \<subseteq> A \<bullet> f \<in> (S \<times> S) \<zbij> S))"
      by (auto simp add: eind_def)
    from pred_on.chain_total [OF c1] have
      c3 [rule_format]: "(\<forall> f f' | f \<in> C \<and> f' \<in> C \<bullet> f \<subseteq> f' \<or> f' \<subseteq> f)"
      by (auto)
    from c1 have
      c4: "subset.chain { S f | S \<subseteq> A \<and> f \<in> S \<zbij> (S \<times> S) \<bullet> f } { f | f \<in> C \<bullet> f\<^sup>\<sim> }"
      by (simp add: pred_on.chain_def Z_inverse_mono subset_def bij_inv_bij_iff) 
    then have
      c5: "{ f | f \<in> C \<bullet> f\<^sup>\<sim> } \<subseteq> { S f | S \<subseteq> A \<and> f \<in> S \<zbij> (S \<times> S) \<bullet> f }" 
      by (auto simp add: pred_on.chain_def)
    then have
      c5' [rule_format]: "(\<forall> f | f \<in> C \<bullet> (\<exists> S | S \<subseteq> A \<bullet> f\<^sup>\<sim> \<in> S \<zbij> (S \<times> S)))"
      by (auto simp add: eind_def)
    show
      "\<Union>C \<in> ?\<A>"
      apply (simp)
      apply (witness "(\<Union> f | f \<in> C \<bullet> \<zran> f)")
      apply (mauto(inference))
    proof -
      show
        "(\<Union> f | f \<in> C \<bullet> \<zran> f) \<subseteq> A"
        apply (auto dest!: c2')
        apply (subst (3) bij_beta [symmetric])
        apply (assumption)+
        apply (rule subsetD)
        apply (assumption)+
        apply (rule bij_range)
        apply (assumption)+
        apply (subst (2) bij_dom [symmetric])
        apply (assumption)
        apply (auto)
        done
    next
      show
        "\<Union>C \<in> ((\<Union> f | f \<in> C \<bullet> \<zran> f) \<times> (\<Union> f | f \<in> C \<bullet> \<zran> f)) \<zbij> (\<Union> f | f \<in> C \<bullet> \<zran> f)"
        apply (mauto(fspace))
        apply (rule chain_Union_functional [OF c1])
        apply (mauto(inference) mdest!: c2')
        apply (fast intro!: bij_functional)
        apply (simp add: converse_Union)
        apply (rule chain_Union_functional [OF c4])
        apply (mauto_full(inference) mdest!: c5')
        apply (fast intro!: bij_functional)
        apply (auto del: RangeE DomainE simp add: rel_Union_dom eind_def)
      proof -
        fix
          a b f 
        assume
          d1: "(a \<mapsto> b) \<in> \<zdom> f" and
          d2: "f \<in> C"
        with c2' [OF d2] show
          "(\<exists> f \<bullet> f \<in> C \<and> a \<in> \<zran> f)"
          "(\<exists> f \<bullet> f \<in> C \<and> b \<in> \<zran> f)"
          by (auto del: RangeE DomainE simp add: bij_dom bij_ran)
      next
        fix
          a b f g
        assume
          d1: "a \<in> \<zran> f" and
          d2: "f \<in> C" and
          d3: "b \<in> \<zran> g" and
          d4: "g \<in> C"
        from c3 [OF d2 d4] show
          "(\<exists> f \<bullet> f \<in> C \<and> (a, b) \<in> \<zdom> f)"
        proof (mauto(inference))
          assume
            e1: "f \<subseteq> g"
          from Z_ran_mono [OF e1] d1 have
            e2: "a \<in> \<zran> g"
            by (auto)
          with d3 c2' [OF d4] d4 show
            "(\<exists> f \<bullet> f \<in> C \<and> (a, b) \<in> \<zdom> f)"
            by (auto del: RangeE DomainE simp add: bij_dom bij_ran)
        next
          assume
            e1: "g \<subseteq> f"
          from Z_ran_mono [OF e1] d3 have
            e2: "b \<in> \<zran> f"
            by (auto)
          with d1 c2' [OF d2] d2 show
            "(\<exists> f \<bullet> f \<in> C \<and> (a, b) \<in> \<zdom> f)"
            by (auto del: RangeE DomainE simp add: bij_dom bij_ran)
        qed
      qed (auto)
    qed
  qed
  then obtain f S where  
    b2: "S \<subseteq> A" and
    b3: "f \<in> (S \<times> S) \<zbij> S" and
    b4: "(\<forall> f' \<bullet> f' \<in> ?\<A> \<Rightarrow> f \<subseteq> f' \<Rightarrow> f' = f)"
    by (auto)
  obtain T where
    b5: "T = A \<setminus> S"
    by (auto)
  from b2 have
    b6: "A = T \<union> S"
    by (auto simp add: b5)
  from linear_sEP [of "S" "T"] show
    "?thesis"
  proof (elim disjE)
    assume
      c1: "T \<preceq> S"
    from b2 b5 have
      c2: "disjoint T S"
      by (auto simp add: disjoint_def)
    from a1 seq_not_infinite_finite [OF c1] have
      c3: "infinite S"
      by (auto simp add: b6)
    have
      "A 
      \<asymp> T \<union> S"
      by (simp add: b6 equipotent_refl)
    also from equipotent_Plus_union [OF c2] have "\<dots>
      \<asymp> T <+> S"
      by (rule equipotent_sym)
    also from infinite_sum [OF c3 c1] have "\<dots>
      \<asymp> S"
      by (this)
    finally have 
      c4: "A \<asymp> S"
      by (this)
    from c4 c4 have
      "A \<times> A 
      \<asymp> S \<times> S"
      by (rule equipotent_prod_cong)
    also have "\<dots>
      \<asymp> S"
      by (rule equipotentI [OF b3])
    also from c4 have "\<dots>
      \<asymp> A"
      by (rule equipotent_sym)
    finally show
      "?thesis"
      by (this)
  next
    assume
      c1: "S \<preceq> T"
    show
      "?thesis"
    proof (cases "finite S")
      assume
        d1: "infinite S"
      from c1 obtain T' where
        d2: "S \<asymp> T'" and
        d3: "T' \<subseteq> T"
        by (auto elim: subep_subsetE)
      from b5 d3 b2 have
        d4: "disjoint S T'"
        by (auto simp add: disjoint_def)
       have
        "S \<times> T' \<union> T' \<times> S \<union> T' \<times> T'
        \<asymp> (S \<times> T' <+> T' \<times> S) <+> T' \<times> T'"
        apply (rule equipotent_sym)
        apply (intro equipotent_Plus_unionIl)
        apply (rule equipotent_refl)
        using d4
        apply (auto simp add: disjoint_def)
        done
      also have "\<dots>
        \<asymp> (S \<times> S <+> S \<times> S) <+> S \<times> S"
        by (intro equipotent_Plus_cong equipotent_prod_cong equipotent_refl d2 [symmetric])
      also have "\<dots>
        \<asymp> (S <+> S) <+> S"
        by (intro equipotent_Plus_cong equipotentI [OF b3])
      also have "\<dots>
        \<asymp> T'"
        apply (rule equipotent_trans [OF _ d2])
        apply (rule equipotent_trans [OF _ infinite_sum' [OF d1]])
        apply (intro equipotent_Plus_cong infinite_sum' [OF d1] equipotent_refl)
        done
      finally obtain g where
        d5: "g \<in> (S \<times> T' \<union> T' \<times> S \<union> T' \<times> T') \<zbij> T'"
        by (auto simp add: equipotent_def)
      from b3 d5 have
        d6: "f \<union> g \<in> ((S \<union> T') \<times> (S \<union> T')) \<zbij> (S \<union> T')"
        apply (mauto(fspace) 
                mintro!: disjoint_dres_empty 
                msimp: converse_union Z_inverse_dom Z_rel_union_dom)
        using d4
        apply (auto simp add: bij_ran [OF d5] bij_ran [OF b3] disjoint_def)
        done
      have
        "f \<union> g \<noteq> f"
      proof -
        from infinite_ep_infinite [OF d1 d2] have
          "T' \<noteq> \<emptyset>"
          by (auto)
        then obtain x where
          l1: "x \<in> T'"
          by (auto)
        have 
          l2: "( (x, x) \<mapsto> g\<cdot>(x, x) ) \<in> g"
          apply (rule bij_appl [OF d5]) 
          using l1
          apply (auto)
          done
        from disjointD2 [OF d4 l1] bij_dom [OF b3] have 
          l3: "( (x, x) \<mapsto> g\<cdot>(x, x) ) \<notin> f"
          by (auto)
        from l2 l3 show
          "?thesis"
          by (auto)
      qed
      moreover have
        "f \<union> g = f"
        apply (rule b4 [rule_format, OF _ Un_upper1, of "g"])
        apply (simp)
        apply (witness "(S \<union> T')")
        using b2 b6 d3 d6
        apply (auto)
        done
      ultimately show
        "?thesis"
        by (contradiction)
    next
      assume
        d1: "finite S"
      with b6 a1 have
        d2: "infinite T"
        by (auto)
      from d2 [THEN infinite_card'' [THEN iffD1]] obtain T' where
        d3: "countable_inf T'" and
        d4: "T' \<subseteq> T"
        by (auto)
      from b5 d4 b2 have
        d5: "disjoint S T'"
        by (auto simp add: disjoint_def)
      from countable_inf_prod [OF d3] have
        d6: "T' \<times> T' \<asymp> T'"
        by (this)
      have
        "S \<times> T' \<union> T' \<times> S \<union> T' \<times> T'
        \<asymp> (S \<times> T' <+> T' \<times> S) <+> T' \<times> T'"
        apply (rule equipotent_sym)
        apply (intro equipotent_Plus_unionIl)
        apply (rule equipotent_refl)
        using d5
        apply (auto simp add: disjoint_def)
        done
      also have "\<dots>
        \<asymp> T' \<times> T'"
        apply (rule infinite_sum)
        apply (rule infinite_ep_infinite [OF _ d6 [symmetric]])
        apply (simp add: d3)
        apply (rule subequipotent_trans)
        apply (rule subequipotent_Plus_cong)
        apply (rule subeq_prod_cong [OF finite_sub_infinite [OF d1, of "T'"] subequipotent_refl])
        apply (simp add: d3)
        apply (rule subeq_prod_cong [OF subequipotent_refl finite_sub_infinite [OF d1, of "T'"]])
        apply (simp add: d3)
        apply (rule equipotentD1)
        apply (rule infinite_sum')
        apply (rule infinite_ep_infinite [OF _ d6 [symmetric]])
        apply (simp add: d3)
        done
      also have "\<dots>
        \<asymp> T'"
        by (rule d6)
      finally obtain g where
        d7: "g \<in> (S \<times> T' \<union> T' \<times> S \<union> T' \<times> T') \<zbij> T'"
        by (auto simp add: equipotent_def)
      from b3 d7 have
        d8: "f \<union> g \<in> ((S \<union> T') \<times> (S \<union> T')) \<zbij> (S \<union> T')"
        apply (mauto(fspace) 
                mintro!: disjoint_dres_empty 
                msimp: converse_union Z_inverse_dom Z_rel_union_dom)
        using d5
        apply (auto simp add: bij_ran [OF d7] bij_ran [OF b3] disjoint_def)
        done
      have
        "f \<union> g \<noteq> f"
      proof -
        from d3 have
          "T' \<noteq> \<emptyset>"
          by (auto)
        then obtain x where
          l1: "x \<in> T'"
          by (auto)
        have 
          l2: "( (x, x) \<mapsto> g\<cdot>(x, x) ) \<in> g"
          apply (rule bij_appl [OF d7]) 
          using l1
          apply (auto)
          done
        from disjointD2 [OF d5 l1] bij_dom [OF b3] have 
          l3: "( (x, x) \<mapsto> g\<cdot>(x, x) ) \<notin> f"
          by (auto)
        from l2 l3 show
          "?thesis"
          by (auto)
      qed
      moreover have
        "f \<union> g = f"
        apply (rule b4 [rule_format, OF _ Un_upper1, of "g"])
        apply (simp)
        apply (witness "(S \<union> T')")
        using b2 b6 d4 d8
        apply (auto)
        done
      ultimately show
        "?thesis"
        by (contradiction)
    qed
  qed
qed

definition
  "prod_encode_map A = (\<some> f | f \<in> (A \<times> A) \<zbij> A)"

lemma prod_encode_map_bij:
  assumes
    a1: "infinite A"
  shows
    "prod_encode_map A \<in> (A \<times> A) \<zbij> A"
  using a1 [THEN infinite_prod']
  apply (simp add: prod_encode_map_def equipotent_def)  
  apply (rule  someI_ex)
  apply (assumption)
  done

definition
  "prod_decode_map A = (prod_encode_map A)\<^sup>\<sim>"

lemma prod_decode_map_bij:
  assumes
    a1: "infinite A"
  shows
    "prod_decode_map A \<in> A \<zbij> (A \<times> A)"
  apply (simp add: prod_decode_map_def)
  apply (rule bij_inv_bij)
  apply (rule prod_encode_map_bij [OF a1])
  done

context infinite
begin

definition
  "prod_encode_op = \<opof>(prod_encode_map \<univ>-['a])"

lemma prod_encode_op_bij:
  "bij prod_encode_op"
  apply (simp add: prod_encode_op_def)
  apply (rule fun_of_f_bij)
  using prod_encode_map_bij [OF infinite_UNIV]
  apply (simp)
  done

definition
  "prod_decode_op = \<opof>(prod_decode_map \<univ>-['a])"

lemma prod_decode_op_bij:
  "bij prod_decode_op"
  apply (simp add: prod_decode_op_def)
  apply (rule fun_of_f_bij)
  using prod_decode_map_bij [OF infinite_UNIV]
  apply (simp)
  done

lemma prod_encode_op_inv:
  "prod_decode_op (prod_encode_op x) = x"
  apply (simp add: prod_decode_op_def prod_encode_op_def prod_decode_map_def)
  apply (rule bij_inv_beta2 [OF prod_encode_map_bij])
  apply (auto simp add: infinite_UNIV)
  done

lemma prod_decode_op_inv:
  "prod_encode_op (prod_decode_op x) = x"
  apply (simp add: prod_decode_op_def prod_encode_op_def prod_decode_map_def)
  apply (rule bij_inv_beta1 [OF prod_encode_map_bij])
  apply (auto simp add: infinite_UNIV)
  done

definition
  "iPair a b = prod_encode_op (Pair a b)"

definition
  "ifst x = fst (prod_decode_op x)"

definition
  "isnd x = snd (prod_decode_op x)"

lemma iprodE: 
  assumes 
   a1: "\<And> (x::'a) (y::'a) \<bullet> s = iPair x y \<turnstile> P"
  shows 
    "P"
  apply (cases "prod_decode_op s")
  apply (rule a1)
  apply (simp add: iPair_def)
  apply (rule arg_cong [of "prod_decode_op s" _ "prod_encode_op", simplified prod_decode_op_inv])
  apply (assumption)
  done

definition
  "iprod_case f z = \<case> prod_decode_op z \<of> (a, b) \<longrightarrow> f a b \<esac>"

end

lemma subep_nempty_prod:
  assumes
    a1: "A \<noteq> \<emptyset>"
  shows
    "B \<preceq> A \<times> B"
proof -
  from a1 obtain x where
    b1: "x \<in> A"
    by (auto)
  show
    "?thesis"
    apply (rule subepIinj_on [of "(\<olambda> b \<bullet> (x, b))"])
    apply (auto intro: inj_onI simp add: b1)
    done
qed

lemma infinite_prod:
  assumes
    a1: "infinite B" and
    a2: "A \<noteq> \<emptyset>" and
    a3: "A \<preceq> B"
  shows
    "\<^EP>{:A \<times> B:}{:B:}"
  apply (rule subequipotent_antisym [OF _ subep_nempty_prod [OF a2]])
  apply (rule subequipotent_trans)
  apply (rule subeq_prod_cong [OF a3 subequipotent_refl])
  apply (rule equipotentD1)
  apply (rule infinite_prod' [OF a1])
  done

text {*

Function spaces have strictly higher (infinite) cardinality.

*}

lemma Cantor_cor_graphs:
  fixes
    X :: "'a set" and
    Y :: "'b set"
  assumes
    a1: "\<^sEP>{:\<univ>-[\<bool>]:}{:Y:}"
  shows
    "\<not>(\<exists> f \<bullet> f \<in> (X \<ztfun> Y) \<zinj> X)"
proof (auto)
  fix
    f
  assume
    b1: "f \<in> (X \<ztfun> Y) \<zinj> X"
  have
    b2: "\<not>(\<exists> f \<bullet> f \<in> (X \<ztfun> \<univ>-[\<bool>]) \<zinj> X)"
  proof (auto)
    fix
      f
    assume
      c1: "f \<in> (X \<ztfun> \<univ>-[\<bool>]) \<zinj> X"
    have 
      c2 [rule_format]: "(\<forall> Y | Y \<in> \<pset> X \<bullet> (\<glambda> x | x \<in> X \<bullet> x \<in> Y) \<in> X \<ztfun> \<univ>-[\<bool>])"
      apply (auto)
      apply (mauto_full(fspace) msimp add: glambda_dom)
      done
    let  
      ?g = "(\<olambda> Y \<bullet> \<if> Y \<in> \<pset> X \<then> f\<cdot>(\<glambda> x | x \<in> X \<bullet> x \<in> Y) \<else> \<arb> \<fi>)"
    have
      c3: "inj_on ?g (\<pset> X)"
      apply (rule inj_onI)
      using c2 
      apply (simp add: tinj_inj_iff [OF c1] glambda_eq)
      apply (auto)
      done
    from Cantor' [of "X" "inv_into (\<pset> X) ?g"] obtain Y where
      c4: "Y \<in> \<pset> X" and
      c5: "Y \<notin> (inv_into (\<pset> X) ?g)\<lparr>X\<rparr>"
      by (auto)
    have 
      c6: "Y \<in> (inv_into (\<pset> X) ?g)\<lparr>X\<rparr>"
      apply (subst inv_into_f_f [OF c3 c4, symmetric])
      apply (rule imageI)
      using c4
      apply (simp add: tinj_range [OF c1] c2)
      done
    from c5 c6 show
      "\<False>"
      by (contradiction)
  qed
  from a1 obtain g where
    b3: "g \<in> \<univ>-[\<bool>] \<zinj> Y"
    by (auto simp add: subequipotent_def)
  let
    ?h = "(\<olambda> A \<bullet> (\<glambda> x | x \<in> X \<bullet> g\<cdot>(A\<cdot>x)))"
  from b3 have
    b4 [rule_format]: "(\<forall> A | A \<in> (X \<ztfun> \<univ>-[\<bool>]) \<bullet> ?h A \<in> (X \<ztfun> Y))"
  proof (auto)
    fix
      A
    assume
      c1: "A \<in> X \<ztfun> \<univ>-[\<bool>]"
    show
      "?h A \<in> X \<ztfun> Y"
      apply (mauto_full(fspace) msimp add: glambda_dom glambda_ran)
      apply (auto intro!: tinj_range [OF b3] tfun_range [OF c1])
      done
  qed
  let
    ?f' = "(\<glambda> A | A \<in> X \<ztfun> \<univ>-[\<bool>] \<bullet> f\<cdot>(?h A))"
  have
    b5: "?f' \<in> (X \<ztfun> \<univ>-[\<bool>]) \<zinj> X"
    apply (mauto_full(fspace) msimp add: glambda_dom glambda_ran)
    apply (msafe_no_assms(inference))
  proof -
    fix 
      A B
    assume
      c1: "A \<in> X \<ztfun> \<univ>-[\<bool>]" and
      c2: "B \<in> X \<ztfun> \<univ>-[\<bool>]" and
      c3: "f\<cdot>(?h A) = f\<cdot>(?h B)" 
    show
      "A = B"
      apply (rule tfun_eqI [OF c1 c2])
      using c3 c1 c2 b4
      apply (simp add: tinj_inj_iff [OF b1] glambda_eq tinj_inj_iff [OF b3] tfun_range [OF c1] tfun_range [OF c2])
      done
  next
    show
      "{ A | A \<in> X \<ztfun> UNIV-[\<bool>] \<bullet> f\<cdot>(\<glambda> x | x \<in> X \<bullet> g\<cdot>(A\<cdot>x)) } \<subseteq> X"
      apply (auto)
      apply (rule tinj_range [OF b1])
      apply (mauto_full(fspace) msimp add: glambda_dom glambda_ran)
      apply (auto)
      apply (rule tinj_range [OF b3])
      apply (simp)
      done
  qed (simp)
  with b2 show
    "\<False>" 
    by (auto)
qed

lemma power_not_equipotent:
  "\<^sEPne>{:X:}{:\<pset> X:}"
proof (rule conjI)
  show
    "\<^sEP>{:X:}{:\<pset> X:}"
    apply (rule subequipotentI [of "(\<glambda> x | x \<in> X \<bullet> {x})"])
    apply (mauto_full(fspace) msimp add: glambda_dom glambda_ran)
    apply (auto)
    done
  from Cantor_cor' [of "X"] have
    "\<not>\<^sEP>{:\<pset> X:}{:X:}"
    by (auto simp add: subequipotent_eq_inj_on)
  then show
    "\<not>(X \<asymp> \<pset> X)"
    apply (rule contrapos_nn)  
    apply (rule equipotentD2)
    apply (assumption)
    done
qed

section {* Cardinals *}

typedef 'a cardinal = "\<^qspace>{:\<univ>-['a set]:}{:equipotent:}"
  apply (witness "\<^eclass>{:\<emptyset>-['a]:}{:equipotent:}")
  apply (auto simp add: quot_set_def)
  done

instantiation
  cardinal :: (type) ord
begin

definition
  lesseq_cardinal_def: "\<opleT>-[('a::type) cardinal] \<defs> induce_ord Rep_cardinal \<^quotord>{:subequipotent:}{:equipotent:}"

definition
  less_cardinal_def: "\<opltT>-[('a::type) cardinal] \<defs> derefl \<opleT>"

instance
  by (intro_classes)

end

instance
  cardinal :: (type) linorder
  apply (rule typedefs_linorder_classI)
  apply (rule type_definition_cardinal)
  apply (rule cardqord.order)
  apply (simp add: lesseq_cardinal_def)
  apply (simp add: less_cardinal_def)
  done

lemma cardinalI:
  "\<^eclass>{:A:}{:equipotent:} \<in> \<^qspace>{:\<univ>-['a set]:}{:equipotent:}"
  by (simp add: equi_equiv.quot_set_mem_ec)

definition
  card_of :: "'a set \<rightarrow> 'a cardinal"
where
  "card_of A \<defs> Abs_cardinal \<^eclass>{:A:}{:equipotent:}"

lemma card_of_equipotent:
  "card_of A = card_of B \<Leftrightarrow> \<^EP>{:A:}{:B:}"
  by (simp add: card_of_def Abs_cardinal_inject equi_equiv.quot_set_mem_ec equi_equiv.equiv_class_eq cardinalI)

lemma card_of_subequipotent:
  "card_of A \<le> card_of B \<Leftrightarrow> \<^sEP>{:A:}{:B:}"
  apply (auto intro!: exI equi_equiv.refl simp add: lesseq_cardinal_def quot_order_def card_of_def induce_ord_def Abs_cardinal_inverse cardinalI rel2op_def equi_equiv.equiv_class_eq equi_equiv.refl)
  apply (auto intro: subequipotent_trans dest: equipotentD1 equipotentD2)
  done

definition
  card_char :: "'a cardinal \<rightarrow> 'a set"
where
  "card_char a \<defs> \<^qchar>{:Rep_cardinal a:}{:equipotent:}"

lemma card_char_inverse:
  "card_of (card_char a) = a"
proof - 
  from Rep_cardinal [of "a"] have
    "\<^eclass>{:\<^qchar>{:Rep_cardinal a:}{:equipotent:}:}{:equipotent:} = Rep_cardinal a"
    by (simp add: equi_equiv.quot_char_class)
  then show
    "?thesis"
    by (simp add: card_of_def card_char_def Rep_cardinal_inverse)
qed

lemma card_char_equipotent:
  "a = b \<Leftrightarrow> \<^EP>{:card_char a:}{:card_char b:}"
  apply (subst (2) card_char_inverse [symmetric])
  apply (subst card_char_inverse [symmetric])
  apply (simp add: card_of_equipotent)
  done

lemma card_char_subequipotent:
  "a \<le> b \<Leftrightarrow> \<^sEP>{:card_char a:}{:card_char b:}"
  apply (subst (2) card_char_inverse [symmetric])
  apply (subst card_char_inverse [symmetric])
  apply (simp add: card_of_subequipotent)
  done

end
