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

theory Lattice_Morphism
 
imports 
  Lattice_Locale 
  Order_Morphism 
  Lattice_Class

begin

section {* Lattice Images *}

text {*

A lattice morphism is a an order-morphism that also respects meets
and joins.

*}

locale lattice_tfun =
  X_lattice + 
  carrier_tfun

locale lattice_rel_tfun =
  X_lattice + 
  po_rel_tfun

locale lattice_preserving = 
  rel_preserving + 
  lattice_rel_tfun

locale lattice_embedding = 
  rel_embedding + 
  lattice_rel_tfun

locale lattice_bij = 
  carrier_bij +
  lattice_tfun 

locale lattice_bij_embedding =
  lattice_embedding + 
  lattice_bij

sublocale lattice_bij_embedding \<subseteq> po_bij_embedding
  by (unfold_locales)

sublocale lattice_bij_embedding \<subseteq> Y_lattice
proof (unfold_locales)
  fix x y
  assume 
    b1: "x \<in> Y" and
    b2: "y \<in> Y"
  show 
      "(\<exists> a \<bullet> is_glb\<^sub>Y {x, y} a)"
    apply (witness "f\<cdot>((f\<^sup>\<sim>)\<cdot>x \<sqinter>\<^sub>X (f\<^sup>\<sim>)\<cdot>y)")
    apply (rule Y.is_glbI)
    apply (auto simp add: finv_embeds [rule_format] bij_inv_beta2 [OF f_bij] meet_lbD1 meet_lbD2 meet_glbD bij_range [OF f_bij] meetR tinj_range [OF bij_inv_tinj [OF f_bij]] b1 b2)
    done
  show 
      "(\<exists> a \<bullet> is_lub\<^sub>Y {x, y} a)"
    apply (witness "f\<cdot>((f\<^sup>\<sim>)\<cdot>x \<squnion>\<^sub>X (f\<^sup>\<sim>)\<cdot>y)")
    apply (rule Y.is_lubI)
    apply (auto simp add: finv_embeds [rule_format] bij_inv_beta2 [OF f_bij] join_ubD1 join_ubD2 join_lubD bij_range [OF f_bij] meetR tinj_range [OF bij_inv_tinj [OF f_bij]] b1 b2)
    done
qed

text{*

Not sure where this was going.  I'm going to include in here the
results required to derive the lattice and clattice class structure
from a type\_def given an order embedding isomorphism.

*}

theorem (in Lattice_Locale.lattice) iso_latticeI: 
  assumes 
    embed: "f \<in> \<^oembfun>{:X:}{:(op \<sqsubseteq>):}{:Y:}{:BS_leq_d_Y:}" and
    f_bij: "f \<in> X \<zbij> Y" and
    Y_rel: "(\<^oprel>{:BS_leq_d_Y:}) \<in> Y \<zrel> Y"
  shows "\<^lattice>{:Y:}{:BS_leq_d_Y:}"
proof -
  from embed interpret
    embde: po_embedding X "(op \<sqsubseteq>)" Y BS_leq_d_Y f
    by auto
  interpret
    iso: lattice_bij_embedding X "(op \<sqsubseteq>)" Y BS_leq_d_Y f
    apply (unfold_locales)
    apply (rule f_bij)
    done
  show
      ?thesis
    by (rule iso.Y.lattice)
qed

lemma (in Lattice_Locale.lattice) image_latticeI:
  assumes 
    f_bij: "f \<in> X \<zbij> Y" 
  shows 
      "\<^lattice>{:Y:}{:\<^imgord>{:(op \<sqsubseteq>):}{:f:}:}"
proof -
  have 
    b1: "Y \<noteq> \<emptyset>"
  proof -
    from non_empty obtain x where
        "x \<in> X"
      by (auto)
    with bij_range [OF f_bij] show 
        "Y \<noteq> \<emptyset>"
      by (auto)
  qed
  with f_bij interpret image_po: po_bij_embedding X "(op \<sqsubseteq>)" Y "\<^imgord>{:(op \<sqsubseteq>):}{:f:}" f
    apply (intro po_bij.image_po)
    apply (unfold_locales)
    apply (auto)
    done
  interpret image_lat: lattice_bij_embedding X "(op \<sqsubseteq>)" Y "\<^imgord>{:(op \<sqsubseteq>):}{:f:}" f
    by (unfold_locales)
  show
      "?thesis"
    by (rule image_lat.Y.lattice)
qed

lemma (in type_definition) induce_lattice:
  assumes 
    a1: "\<^lattice>{:A:}{:BS_leq_d_A:}"
  shows 
      "\<^lattice>{:\<univ>:}{:(induce_ord Rep BS_leq_d_A):}"
proof -
  from a1 interpret b1: Lattice_Locale.lattice A BS_leq_d_A
    by (auto simp add: Lattice_Locale.lattice_def)
  show ?thesis
    apply (simp add: induce_image_ord [OF b1.setrel])
    apply (rule b1.image_latticeI)
    apply (rule Abs_graph_bij)
    done
qed

definition
  induce_inf :: "['b \<rightarrow> 'a, 'a \<rightarrow> 'b, 'a set, 'a orderT] \<rightarrow> (['b, 'b] \<rightarrow> 'b)"
where
  induce_inf_def: "induce_inf Rep Abs A BS_leq \<defs> (\<olambda> x y \<bullet> Abs ((Rep x) \<^meet>{:A:}{:BS_leq:} (Rep y)))"

definition
  induce_sup :: "['b \<rightarrow> 'a, 'a \<rightarrow> 'b, 'a set, 'a orderT] \<rightarrow> (['b, 'b] \<rightarrow> 'b)"
where
  induce_sup_def: "induce_sup Rep Abs A BS_leq \<defs> (\<olambda> x y \<bullet> Abs ((Rep x) \<^join>{:A:}{:BS_leq:} (Rep y)))"

lemma (in type_definition) induce_inf:
  assumes a1: 
    "\<^lattice>{:A:}{:BS_leq_d_A:}"
  shows 
    "induce_inf Rep Abs A BS_leq_d_A = (\<olambda> a b \<bullet> a \<^meet>{:\<univ>:}{:(induce_ord Rep BS_leq_d_A):} b)"
proof -
  from a1 interpret 
    b1: Lattice_Locale.lattice "A" "BS_leq_d_A"
    by (this)
  from induce_lattice [OF a1] interpret 
    b2: Lattice_Locale.lattice "\<univ>" "(induce_ord Rep BS_leq_d_A)"
    by (this)
  show ?thesis 
    apply (intro ext)
    apply (rule b2.meet_unique)
    apply (rule b2.is_glbI)
    apply (auto simp add: induce_inf_def induce_ord_def b1.meetR Rep Abs_inverse b1.meet_lbD1 b1.meet_lbD2  b1.meet_glbD)
    done
qed

lemma (in type_definition) induce_sup:
  assumes 
    a1: "\<^lattice>{:A:}{:BS_leq_d_A:}"
  shows 
      "induce_sup Rep Abs A BS_leq_d_A = (\<olambda> a b \<bullet> a \<^join>{:\<univ>:}{:(induce_ord Rep BS_leq_d_A):} b)"
proof -
  from a1 interpret 
    b1: Lattice_Locale.lattice "A" "BS_leq_d_A"
    by (this)
  from induce_lattice [OF a1] interpret 
    b2: Lattice_Locale.lattice "\<univ>" "(induce_ord Rep BS_leq_d_A)"
    by (this)
  show ?thesis 
    apply (intro ext)
    apply (rule b2.join_unique)
    apply (rule b2.is_lubI)
    apply (auto simp add: induce_sup_def induce_ord_def b1.joinR Rep Abs_inverse b1.join_ubD1 b1.join_ubD2  b1.join_lubD)
    done
qed

lemma typedefs_lattice_classI:
  assumes
    a1: "type_definition (Rep::('a::{order, lat}) \<rightarrow> 'b) Abs (A::'b set)" and
    a2: "\<^lattice>{:A:}{:BS_leq_d_A:}" and
    a3: "(op \<le>::['a::{order, lat},'a] \<rightarrow> \<bool>) = induce_ord Rep BS_leq_d_A" and
    a4: "(op &&) = induce_inf Rep Abs A BS_leq_d_A" and
    a5: "(op ||) = induce_sup Rep Abs A BS_leq_d_A"
  shows 
      "OFCLASS('a::{order, lat}, lattice_class)"
proof -
  from a1 interpret 
    b1: type_definition Rep Abs A
    by (this)
  show "OFCLASS('a::{order, lat}, lattice_class)"
    apply (rule lattice_classI)
    apply (simp add: a3)
    apply (rule b1.induce_lattice [OF a2])
    apply (auto simp add: a4 a5 b1.induce_inf b1.induce_sup a2 a3)
    done
qed

lemma epi_typedefs_lattice_classI:
  assumes
    a1: "epi_type_definition (Rep::('a::{order, lat}) \<rightarrow> 'b) Abs " and
    a2: "\<^lattice>{:\<univ>:}{:BS_leq:}" and
    a3: "(op \<le>::['a::{order, lat},'a] \<rightarrow> \<bool>) = induce_ord Rep BS_leq" and
    a4: "(op &&) = induce_inf Rep Abs \<univ> BS_leq" and
    a5: "(op ||) = induce_sup Rep Abs \<univ> BS_leq"
  shows 
      "OFCLASS('a::{order, lat}, lattice_class)"
proof -
  interpret ETD: epi_type_definition Rep Abs
    by (rule a1)
  show
    "OFCLASS('a, lattice_class)"
    apply (rule typedefs_lattice_classI)
    apply (rule ETD.type_definition_axioms)
    apply (simp_all add: a2 a3 a4 a5)
    done
qed

lemma induce_default_inf:
  assumes 
    a1: "type_definition Rep Abs (A::('a::lattice) set)" and 
    a2: "\<And> a b \<bullet> \<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<turnstile> a \<linf> b \<in> A" and 
    a3: "\<And> a b \<bullet> \<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<turnstile> a \<lsup> b \<in> A"
  shows 
    "induce_inf Rep Abs A (default_order A) = (\<olambda> x y \<bullet> Abs ((Rep x) \<linf> (Rep y)))"
proof -
  from a1 interpret 
    b1: type_definition Rep Abs A
    by (this)
  from lattice_class_defaultD [OF b1.Rep_nonempty a2 a3] interpret 
    b2: Lattice_Locale.lattice "A" "default_order A"
    by (auto)
  from b1.induce_lattice [OF b2.lattice] interpret 
    b3: Lattice_Locale.lattice "\<univ>" "induce_ord Rep (default_order A)"
    by (this)
  show ?thesis
    apply (intro ext)
    apply (simp add: b1.induce_inf [OF b2.lattice])
    apply (rule b3.meet_unique [symmetric])
    apply (rule b3.is_glbI)
    apply (auto simp add: induce_ord_def default_order_def subset_order_def rel2op_def op2rel_def b1.Abs_inverse [OF a2] b1.Rep inf_lb1 inf_lb2 inf_glb)
    done
qed

lemma induce_default_sup:
  assumes 
    a1: "type_definition Rep Abs (A::('a::lattice) set)" and 
    a2: "\<And> a b \<bullet> \<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<turnstile> a \<linf> b \<in> A" and 
    a3: "\<And> a b \<bullet> \<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<turnstile> a \<lsup> b \<in> A"
  shows 
    "induce_sup Rep Abs A (default_order A) = (\<olambda> x y \<bullet> Abs ((Rep x) \<lsup> (Rep y)))"
proof -
  from a1 interpret 
    b1: type_definition Rep Abs A
    by (this)
  from lattice_class_defaultD [OF b1.Rep_nonempty a2 a3] interpret 
    b2: Lattice_Locale.lattice "A" "default_order A"
    by (auto)
  from b1.induce_lattice [OF b2.lattice] interpret 
    b3: Lattice_Locale.lattice "\<univ>" "induce_ord Rep (default_order A)"
    by (this)
  show ?thesis
    apply (intro ext)
    apply (simp add: b1.induce_sup [OF b2.lattice])
    apply (rule b3.join_unique [symmetric])
    apply (rule b3.is_lubI)
    apply (auto simp add: induce_ord_def default_order_def subset_order_def rel2op_def op2rel_def b1.Abs_inverse [OF a3] b1.Rep sup_ub1 sup_ub2 sup_lub)
    done
qed

text {*

Complete lattices

*}

locale clattice_tfun =
  X_clattice + 
  carrier_tfun

sublocale clattice_tfun \<subseteq> lattice_tfun
  by (unfold_locales)

locale clattice_rel_tfun =
  X_clattice + 
  po_rel_tfun

sublocale clattice_rel_tfun \<subseteq> lattice_rel_tfun
  by (unfold_locales)

locale clattice_preserving = 
  rel_preserving + 
  clattice_rel_tfun

sublocale clattice_preserving \<subseteq> lattice_preserving
  by (unfold_locales)

locale clattice_embedding = 
  rel_embedding + 
  clattice_rel_tfun

sublocale clattice_embedding \<subseteq> lattice_embedding
  by (unfold_locales)

locale clattice_bij = 
  carrier_bij +
  clattice_tfun 

sublocale clattice_bij \<subseteq> lattice_bij
  by (unfold_locales)

locale clattice_bij_embedding =
  clattice_embedding + 
  clattice_bij

sublocale clattice_bij_embedding \<subseteq> lattice_bij_embedding
  by (unfold_locales)

sublocale clattice_bij_embedding \<subseteq> Y_clattice
proof (unfold_locales)
  fix 
    A
  assume 
    b1: "A \<subseteq> Y"
  with f_bij have
    b2: "(f\<^sup>\<sim>)\<zlImg>A\<zrImg> \<subseteq> X"
    by (mauto(fspace))
  show 
      "(\<exists> a \<bullet> is_glb\<^sub>Y A a)"
    apply (witness "f\<cdot>(\<Sqinter>\<^sub>X ((f\<^sup>\<sim>)\<zlImg>A\<zrImg>))")
    apply (rule Y.is_glbI)
  proof -
    show 
      c1: "f\<cdot>(\<Sqinter>\<^sub>X ((f\<^sup>\<sim>)\<zlImg>A\<zrImg>)) \<in> Y"
      apply (rule bij_range [OF f_bij])
      apply (rule MeetR)
      apply (rule b2)
      done
  { fix 
      a
    assume
      c2: "a \<in> A"
    from c1 subsetD [OF b1, OF c2] show
        "f\<cdot>(\<Sqinter>\<^sub>X ((f\<^sup>\<sim>)\<zlImg>A\<zrImg>)) \<preceq>\<^sub>Y a"
      apply (simp add: finv_embeds [rule_format] bij_inv_beta2 [OF f_bij] MeetR b2)
      apply (rule Meet_lbD [OF b2])
      apply (auto intro!: exI c2 bij_inv_appl' [OF f_bij] simp add: Image_def)
      done
  next
    fix
      b
    assume
      c2: "b \<in> Y" and
      c3: "(\<forall> x \<bullet> x \<in> A \<Rightarrow> b \<preceq>\<^sub>Y x)"
    from c1 c2 show
        "b \<preceq>\<^sub>Y f\<cdot>(\<Sqinter>\<^sub>X ((f\<^sup>\<sim>)\<zlImg>A\<zrImg>))"
      apply (simp add: finv_embeds [rule_format] bij_inv_beta2 [OF f_bij] MeetR b2)
      apply (rule Meet_glbD [OF b2])
      apply (auto simp add: bij_inv_range [OF f_bij])
    proof -
      fix 
        a y
      assume
        d1: "a \<in> A" and
        d2: "(y \<mapsto> a) \<in> f"
      from c3 [rule_format, OF d1] c2 subsetD [OF b1, OF d1] have
          "(f\<^sup>\<sim>)\<cdot>b \<sqsubseteq>\<^sub>X (f\<^sup>\<sim>)\<cdot>a"
        by (simp add:  finv_embeds [rule_format])
      with bij_inv_beta [OF f_bij d2] show
          "(f\<^sup>\<sim>)\<cdot>b \<sqsubseteq>\<^sub>X y"
        by (simp)
    qed }
  qed
  show 
      "(\<exists> a \<bullet> is_lub\<^sub>Y A a)"
    apply (witness "f\<cdot>(\<Squnion>\<^sub>X ((f\<^sup>\<sim>)\<zlImg>A\<zrImg>))")
    apply (rule Y.is_lubI)
  proof -
    show 
      c1: "f\<cdot>(\<Squnion>\<^sub>X ((f\<^sup>\<sim>)\<zlImg>A\<zrImg>)) \<in> Y"
      apply (rule bij_range [OF f_bij])
      apply (rule JoinR)
      apply (rule b2)
      done
  { fix 
      a
    assume
      c2: "a \<in> A"
    from c1 subsetD [OF b1, OF c2] show
        "a  \<preceq>\<^sub>Y f\<cdot>(\<Squnion>\<^sub>X ((f\<^sup>\<sim>)\<zlImg>A\<zrImg>))"
      apply (simp add: finv_embeds [rule_format] bij_inv_beta2 [OF f_bij] JoinR b2)
      apply (rule Join_ubD [OF b2])
      apply (auto intro!: exI c2 bij_inv_appl' [OF f_bij] simp add: Image_def)
      done
  next
    fix
      b
    assume
      c2: "b \<in> Y" and
      c3: "(\<forall> x \<bullet> x \<in> A \<Rightarrow> x \<preceq>\<^sub>Y b)"
    from c1 c2 show
        "f\<cdot>(\<Squnion>\<^sub>X ((f\<^sup>\<sim>)\<zlImg>A\<zrImg>)) \<preceq>\<^sub>Y b"
      apply (simp add: finv_embeds [rule_format] bij_inv_beta2 [OF f_bij] JoinR b2)
      apply (rule Join_lubD [OF b2])
      apply (auto simp add: bij_inv_range [OF f_bij])
    proof -
      fix 
        a y
      assume
        d1: "a \<in> A" and
        d2: "(y \<mapsto> a) \<in> f"
      from c3 [rule_format, OF d1] c2 subsetD [OF b1, OF d1] have
          "(f\<^sup>\<sim>)\<cdot>a \<sqsubseteq>\<^sub>X (f\<^sup>\<sim>)\<cdot>b"
        by (simp add:  finv_embeds [rule_format])
      with bij_inv_beta [OF f_bij d2] show
          "y \<sqsubseteq>\<^sub>X (f\<^sup>\<sim>)\<cdot>b"
        by (simp)
    qed }
  qed
qed

theorem (in Lattice_Locale.clattice) iso_clatticeI: 
  assumes 
    embed: "f \<in> \<^oembfun>{:X:}{:(op \<sqsubseteq>):}{:Y:}{:BS_leq_d_Y:}" and
    f_bij: "f \<in> X \<zbij> Y" and
    Y_rel: "\<^oprel>{:BS_leq_d_Y:} \<in> Y \<zrel> Y"
  shows 
      "\<^clattice>{:Y:}{:BS_leq_d_Y:}"
proof -
  from embed interpret
    embde: po_embedding X "(op \<sqsubseteq>)" Y BS_leq_d_Y f
    by auto
  interpret
    iso: clattice_bij_embedding X "(op \<sqsubseteq>)" Y BS_leq_d_Y f
    apply (unfold_locales)
    apply (rule f_bij)
    done
  show
      ?thesis
    by (rule iso.Y.clattice)
qed

lemma (in Lattice_Locale.clattice) image_clatticeI:
  assumes 
    f_bij: "f \<in> X \<zbij> Y" 
  shows 
    "\<^clattice>{:Y:}{:\<^imgord>{:(op \<sqsubseteq>):}{:f:}:}"
proof -
  have 
    b1: "Y \<noteq> \<emptyset>"
  proof -
    from non_empty obtain x where
        "x \<in> X"
      by (auto)
    with bij_range [OF f_bij] show 
        "Y \<noteq> \<emptyset>"
      by (auto)
  qed
  with f_bij interpret image_po: po_bij_embedding X "(op \<sqsubseteq>)" Y "\<^imgord>{:(op \<sqsubseteq>):}{:f:}" f
    apply (intro po_bij.image_po)
    apply (unfold_locales)
    apply (auto)
    done
  interpret image_clat: clattice_bij_embedding X "(op \<sqsubseteq>)" Y "\<^imgord>{:(op \<sqsubseteq>):}{:f:}" f
    by (unfold_locales)
  show
      "?thesis"
    by (rule image_clat.Y.clattice)
qed

lemma (in type_definition) induce_clattice:
  assumes 
    a1: "\<^clattice>{:A:}{:BS_leq_d_A:}"
  shows 
      "\<^clattice>{:\<univ>:}{:(induce_ord Rep BS_leq_d_A):}"
proof -
  from a1 interpret b1: Lattice_Locale.clattice A BS_leq_d_A
    by (this)
  show ?thesis
    apply (simp add: induce_image_ord [OF b1.setrel])
    apply (rule b1.image_clatticeI)
    apply (rule Abs_graph_bij)
    done
qed

definition
  induce_bot :: "['b \<rightarrow> 'a, 'a \<rightarrow> 'b, 'a set, 'a orderT] \<rightarrow> 'b"
where
  induce_bot_def: "induce_bot Rep Abs A BS_leq \<defs> Abs (Bottom A BS_leq)"

definition
  induce_top :: "['b \<rightarrow> 'a, 'a \<rightarrow> 'b, 'a set, 'a orderT] \<rightarrow> 'b"
where
  induce_top_def: "induce_top Rep Abs A BS_leq \<defs> Abs (Top A BS_leq)"

definition
  induce_Inf :: "['b \<rightarrow> 'a, 'a \<rightarrow> 'b, 'a set, 'a orderT] \<rightarrow> ('b set \<rightarrow> 'b)"
where
  induce_Inf_def: "induce_Inf Rep Abs A BS_leq \<defs> (\<olambda> X \<bullet> Abs (\<^Meet>{:A:}{:BS_leq:} { x | x \<in> X \<bullet> (Rep x) }))"

definition
  induce_Sup :: "['b \<rightarrow> 'a, 'a \<rightarrow> 'b, 'a set, 'a orderT] \<rightarrow> ('b set \<rightarrow> 'b)"
where
  induce_Sup_def: "induce_Sup Rep Abs A BS_leq \<defs> (\<olambda> X \<bullet> Abs (\<^Join>{:A:}{:BS_leq:} { x | x \<in> X \<bullet> (Rep x) }))"

lemma (in type_definition) induce_bot:
  assumes 
    a1: "\<^clattice>{:A:}{:BS_leq_d_A:}"
  shows 
      "induce_bot Rep Abs A BS_leq_d_A = Meet \<univ> (induce_ord Rep BS_leq_d_A) \<univ>"
proof -
  from a1 interpret
    b1: Lattice_Locale.clattice A BS_leq_d_A
    by (this)
  from induce_clattice [OF a1] interpret 
    b2: Lattice_Locale.clattice "\<univ>" "(induce_ord Rep BS_leq_d_A)"
    by (this)
  show ?thesis
    apply (rule b2.Meet_unique)
    apply (auto simp add: induce_ord_def induce_bot_def Abs_inverse b1.BottomR b1.Bottom_lb Rep)
    done
qed

lemma (in type_definition) induce_top:
  assumes 
    a1: "\<^clattice>{:A:}{:BS_leq_d_A:}"
  shows 
      "induce_top Rep Abs A BS_leq_d_A = Join \<univ> (induce_ord Rep BS_leq_d_A) \<univ>"
proof -
  from a1 interpret 
    b1: Lattice_Locale.clattice A BS_leq_d_A
    by (this)
  from induce_clattice [OF a1] interpret 
    b2: Lattice_Locale.clattice "\<univ>" "(induce_ord Rep BS_leq_d_A)"
    by (this)
  show ?thesis
    apply (rule b2.Join_unique)
    apply (auto)
    apply (simp add: induce_ord_def induce_top_def Abs_inverse b1.TopR b1.Top_ub Rep)
    done
qed

lemma (in type_definition) induce_Inf:
  assumes 
    a1: "\<^clattice>{:A:}{:BS_leq_d_A:}"
  shows 
      "induce_Inf Rep Abs A BS_leq_d_A = Meet \<univ> (induce_ord Rep BS_leq_d_A)"
proof -
  from a1 interpret 
    b1: Lattice_Locale.clattice A BS_leq_d_A
    by (this)
  from induce_clattice [OF a1] interpret 
    b2: Lattice_Locale.clattice "\<univ>" "(induce_ord Rep BS_leq_d_A)"
    by (this)
  have b3 [rule_format]: "(\<forall> X \<bullet> { x | x \<in> X \<bullet> Rep x } \<subseteq> A)"
    by (auto simp add: Rep)
  show ?thesis 
    apply (intro ext)
    apply (rule b2.Meet_unique)
    apply (auto 
              intro!: b1.Meet_lbD b1.Meet_glbD 
              simp add: induce_Inf_def induce_ord_def b1.MeetR Rep Abs_inverse b3)
    done
qed

lemma (in type_definition) induce_Sup:
  assumes 
    a1: "\<^clattice>{:A:}{:BS_leq_d_A:}"
  shows
    "induce_Sup Rep Abs A BS_leq_d_A = Join \<univ> (induce_ord Rep BS_leq_d_A)"
proof -
  from a1 interpret 
     b1: Lattice_Locale.clattice A BS_leq_d_A
    by (this)
  from induce_clattice [OF a1] interpret 
     b2: Lattice_Locale.clattice "\<univ>" "(induce_ord Rep BS_leq_d_A)"
    by (this)
  have b3 [rule_format]: "(\<forall> X \<bullet> { x | x \<in> X \<bullet> Rep x } \<subseteq> A)"
    by (auto simp add: Rep)
  show ?thesis 
    apply (intro ext)
    apply (rule b2.Join_unique)
    apply (auto 
              intro!: b1.Join_ubD b1.Join_lubD 
              simp add: induce_Sup_def induce_ord_def b1.JoinR Rep Abs_inverse b3)
    done
qed

lemma induce_default_Inf:
  assumes 
    a1: "type_definition Rep Abs (A::('a::clattice) set)" and 
    a2: "\<And> X \<bullet> \<lbrakk> X \<noteq> \<emptyset>; X \<subseteq> A \<rbrakk> \<turnstile> \<lInf>X \<in> A" and 
    a3: "\<And> X \<bullet> \<lbrakk> X \<noteq> \<emptyset>; X \<subseteq> A \<rbrakk> \<turnstile> \<lSup>X \<in> A" and
    a4: "X \<noteq> \<emptyset>"
  shows 
    "induce_Inf Rep Abs A (default_order A) X = Abs (\<lINF> x | x \<in> X \<bullet> Rep x)"
proof -
  from a1 interpret 
    b1: type_definition Rep Abs "A"
    by (this)
  from clattice_class_defaultD [OF b1.Rep_nonempty a2 a3] interpret 
    b2: Lattice_Locale.clattice "A" "default_order A"
    by (this)
  from b1.induce_clattice [OF b2.clattice] interpret 
    b3: Lattice_Locale.clattice  "\<univ>" "(induce_ord Rep (default_order A))"
    by (this)
  from a4 have 
    b4: "{ x | x \<in> X \<bullet> Rep x } \<noteq> \<emptyset>"
    by (auto)
  show 
      ?thesis
    apply (simp add: b1.induce_Inf [OF b2.clattice])
    apply (rule b3.Meet_unique [symmetric])
    apply (auto)
    apply (auto intro!: Inf_lb Inf_glb simp add: induce_ord_def default_order_def subset_order_def rel2op_def op2rel_def b1.Abs_inverse [OF a2 [OF b4 b1.Rep_image]] b1.Rep)
    done
qed

lemma induce_default_Sup:
  assumes 
    a1: "type_definition Rep Abs (A::('a::clattice) set)" and 
    a2: "\<And> X \<bullet> \<lbrakk> X \<noteq> \<emptyset>; X \<subseteq> A \<rbrakk> \<turnstile> \<lInf>X \<in> A" and 
    a3: "\<And> X \<bullet> \<lbrakk> X \<noteq> \<emptyset>; X \<subseteq> A \<rbrakk> \<turnstile> \<lSup>X \<in> A" and
    a4: "X \<noteq> \<emptyset>"
  shows 
      "induce_Sup Rep Abs A (default_order A) X = Abs (\<lSUP> x | x \<in> X \<bullet> Rep x)"
proof -
  from a1 interpret 
    b1: type_definition Rep Abs "A"
    by (this)
  from clattice_class_defaultD [OF b1.Rep_nonempty a2 a3] interpret 
    b2: Lattice_Locale.clattice "A" "default_order A"
    by (this)
  from b1.induce_clattice [OF b2.clattice] interpret 
    b3: Lattice_Locale.clattice "\<univ>" "(induce_ord Rep (default_order A))"
    by (this)
  from a4 have 
    b4: "{ x | x \<in> X \<bullet> Rep x } \<noteq> \<emptyset>"
    by (auto)
  show ?thesis
    apply (simp add: b1.induce_Sup [OF b2.clattice])
    apply (rule b3.Join_unique [symmetric])
    apply (auto)
    apply (auto intro!: Sup_ub Sup_lub simp add: induce_ord_def default_order_def subset_order_def rel2op_def op2rel_def b1.Abs_inverse [OF a3 [OF b4 b1.Rep_image]] b1.Rep)
    done
qed

lemma induce_default_bot:
  assumes 
    a1: "type_definition Rep Abs (A::('a::clattice) set)" and 
    a2: "\<And> X \<bullet> \<lbrakk> X \<noteq> \<emptyset>; X \<subseteq> A \<rbrakk> \<turnstile> \<lInf>X \<in> A" and 
    a3: "\<And> X \<bullet> \<lbrakk> X \<noteq> \<emptyset>; X \<subseteq> A \<rbrakk> \<turnstile> \<lSup>X \<in> A"
  shows 
      "induce_bot Rep Abs A (default_order A) = Abs (\<lINF> x \<bullet> Rep x)"
proof -
  from a1 interpret 
    b1: type_definition Rep Abs "A"
    by (this)
  from clattice_class_defaultD [OF b1.Rep_nonempty a2 a3] interpret 
    b2: Lattice_Locale.clattice "A" "default_order A"
    by (this)
  from b1.induce_clattice [OF b2.clattice] interpret 
    b3: Lattice_Locale.clattice "\<univ>" "(induce_ord Rep (default_order A))"
    by (this)
  have 
    b4: "{x \<bullet> Rep x} \<noteq> \<emptyset>"
    by (auto)
  show 
      ?thesis
    apply (simp add: b1.induce_bot [OF b2.clattice])
    apply (rule b3.Meet_unique [symmetric])
    apply (auto)
    apply (auto intro!: Inf_lb Inf_glb simp add: induce_ord_def default_order_def subset_order_def rel2op_def op2rel_def b1.Abs_inverse [OF a2 [OF b4 b1.Rep_image']] b1.Rep)
    done
qed

lemma induce_default_top:
  assumes 
    a1: "type_definition Rep Abs (A::('a::clattice) set)" and 
    a2: "\<And> X \<bullet> \<lbrakk> X \<noteq> \<emptyset>; X \<subseteq> A \<rbrakk> \<turnstile> \<lInf>X \<in> A" and 
    a3: "\<And> X \<bullet> \<lbrakk> X \<noteq> \<emptyset>; X \<subseteq> A \<rbrakk> \<turnstile> \<lSup>X \<in> A"
  shows 
    "induce_top Rep Abs A (default_order A) = Abs (\<lSUP> x \<bullet> Rep x)"
proof -
  from a1 interpret 
    b1: type_definition Rep Abs "A"
    by (this)
  from clattice_class_defaultD [OF b1.Rep_nonempty a2 a3] interpret 
    b2: Lattice_Locale.clattice "A" "default_order A"
    by (this)
  from b1.induce_clattice [OF b2.clattice] interpret 
    b3: Lattice_Locale.clattice "\<univ>" "(induce_ord Rep (default_order A))"
    by (this)
  have 
    b4: "{x \<bullet> Rep x} \<noteq> \<emptyset>"
    by (auto)
  show 
      ?thesis
    apply (simp add: b1.induce_top [OF b2.clattice])
    apply (rule b3.Join_unique [symmetric])
    apply (auto)
    apply (auto intro!: Sup_ub Sup_lub simp add: induce_ord_def default_order_def subset_order_def rel2op_def op2rel_def b1.Abs_inverse [OF a3 [OF b4 b1.Rep_image']] b1.Rep)
    done
qed

lemma typedefs_clattice_classI:
  assumes
    a1: "type_definition (Rep::('a::{order, clat}) \<rightarrow> 'b) Abs (A::'b set)" and
    a2: "\<^clattice>{:A:}{:BS_leq_d_A:}" and
    a3: "(op \<le>::['a::{order, clat},'a] \<rightarrow> \<bool>) = induce_ord Rep BS_leq_d_A" and
    a4: "\<And> x y \<bullet> (op &&) = induce_inf Rep Abs A BS_leq_d_A" and
    a5: "\<And> x y \<bullet> (op ||) = induce_sup Rep Abs A BS_leq_d_A" and
    a6: "\<And> X \<bullet> Inf = induce_Inf Rep Abs A BS_leq_d_A" and
    a7: "\<And> X \<bullet> Sup = induce_Sup Rep Abs A BS_leq_d_A" and
    a8: "\<And> X \<bullet> bot = induce_bot Rep Abs A BS_leq_d_A" and
    a9: "\<And> X \<bullet> top = induce_top Rep Abs A BS_leq_d_A"
  shows 
    "OFCLASS('a::{order, clat}, clattice_class)"
proof -
  from a1 interpret 
    b1: type_definition Rep Abs "A"
    by (this)
  from a2 interpret 
    b2: Lattice_Locale.clattice A BS_leq_d_A 
    by (this)
  show "OFCLASS('a::{order, clat}, clattice_class)"
    apply (rule clattice_classI)
    apply (simp add: a3)
    apply (rule b1.induce_clattice [OF a2])
    apply (auto simp add: a4 a5 b1.induce_inf b1.induce_sup a2 b2.lattice a3 a6 a7 b1.induce_Inf b1.induce_Sup a8 a9 b1.induce_bot b1.induce_top)
    done
qed

lemma epi_typedefs_clattice_classI:
  assumes
    a1: "epi_type_definition (Rep::('a::{order, clat}) \<rightarrow> 'b) Abs" and
    a2: "\<^clattice>{:\<univ>:}{:BS_leq:}" and
    a3: "(op \<le>::['a::{order, clat},'a] \<rightarrow> \<bool>) = induce_ord Rep BS_leq" and
    a4: "\<And> x y \<bullet> (op &&) = induce_inf Rep Abs \<univ> BS_leq" and
    a5: "\<And> x y \<bullet> (op ||) = induce_sup Rep Abs \<univ> BS_leq" and
    a6: "\<And> X \<bullet> Inf = induce_Inf Rep Abs \<univ> BS_leq" and
    a7: "\<And> X \<bullet> Sup = induce_Sup Rep Abs \<univ> BS_leq" and
    a8: "\<And> X \<bullet> bot = induce_bot Rep Abs \<univ> BS_leq" and
    a9: "\<And> X \<bullet> top = induce_top Rep Abs \<univ> BS_leq"
  shows 
    "OFCLASS('a::{order, clat}, clattice_class)"
proof -
  interpret ETD: epi_type_definition Rep Abs
    by (rule a1)
  show
    "OFCLASS('a, clattice_class)"
    apply (rule typedefs_clattice_classI)
    apply (rule ETD.type_definition_axioms)
    apply (simp_all add: a2 a3 a4 a5 a6 a7 a8 a9)
    done
qed

section {* Monotonic functions *}

text {* 

Monotonic functions has the following interactions with lattice operators.

*}

lemma mh_inf:
  assumes
    a1: "f \<in> \<mh>"
  shows 
    "f (x \<linf> y) \<lle> (f x) \<linf> (f y)"
proof (rule inf_glb)
  show 
    "f(x \<linf> y) \<lle> f x" 
    by (rule a1 [THEN mhD]) (rule inf_lb1)
  show 
    "f(x \<linf> y) \<lle> f y" 
    by (rule a1 [THEN mhD]) (rule inf_lb2)
qed
  
lemma mh_sup:
  assumes 
    a1: "f \<in> \<mh>"
  shows 
    "(f x) \<lsup> (f y) \<lle> f(x \<lsup> y)"
proof (rule sup_lub)
  show 
    "f x \<lle> f(x \<lsup> y)" 
     by (rule a1 [THEN mhD]) (rule sup_ub1)
  show 
     "f y \<lle> f(x \<lsup> y)" 
     by (rule a1 [THEN mhD]) (rule sup_ub2)
qed
  
lemma mh_bot:
  assumes a1: "f \<in> \<mh>"
  shows "f \<lbot> \<lle> f x"
  by (rule bot_lb [THEN [2] mhD, OF a1])

lemma mh_top:
  assumes a1: "f \<in> \<mh>"
  shows "f x \<lle> f \<ltop>"
  by (rule top_ub [THEN [2] mhD, OF a1])

lemma mh_Inf:
  assumes a1: "f \<in> \<mh>"
  shows "f(\<lInf> P) \<lle> (\<lINF> x | x \<in> P \<bullet> f x)"
proof (rule Inf_glb, auto)
  fix x::'a
  assume a2: "x \<in> P"
  show "f(\<lInf>P) \<lle> f x"
    by (rule a1 [THEN mhD]) (rule a2 [THEN Inf_lb])
qed

lemma mh_Sup:
  assumes a1: "f \<in> \<mh>"
  shows "(\<lSUP> x | x \<in> P\<bullet>f x) \<lle> f(\<lSup>P)"
proof (rule Sup_lub, auto)
  fix x::'a
  assume a2: "x \<in> P"
  show "f x \<lle> f(\<lSup>P)"
    by (rule a1 [THEN mhD]) (rule a2 [THEN Sup_ub])
qed

lemma mh_QInf:
  assumes 
    a1: "f \<in> \<mh>"
  shows 
    "f(\<lINF> x | P x) \<lle> (\<lINF> x | P x \<bullet> f x)"
proof (rule Inf_glb, auto)
  fix 
    x::'a
  assume 
    a2: "P x"
  show 
    "f(\<lINF> x | P x) \<lle> f x"
    apply (rule a1 [THEN mhD])
    apply (rule a2 [THEN CollectqI [of "P"], THEN Inf_lb])
    done
qed

lemma mh_QSup:
  assumes 
    a1: "f \<in> \<mh>"
  shows 
    "(\<lSUP> x | P x \<bullet> f x) \<lle> f(\<lSUP> x | P x)"
proof (rule Sup_lub, auto)
  fix 
    x::'a
  assume 
    a2: "P x"
  show 
    "f x \<lle> f(\<lSUP> x | P x)"
    by (rule a1 [THEN mhD])
      (rule a2 [THEN CollectqI [THEN Sup_ub [of x "{ x | P x }"]]])
qed

lemma mh_QTInf:
  assumes a1: "f \<in> \<mh>"
  shows "f(\<lINF> x | P x \<bullet> g x) \<lle> (\<lINF> x | P x \<bullet> f(g x))"
proof (rule Inf_glb, auto)
  fix 
    x
  assume 
    a2: "P x"
  show 
    "f(\<lINF> x | P x \<bullet> g x) \<lle> f (g x)"
    by (rule a1 [THEN mhD], rule Inf_lb, auto intro!: a2)
qed

lemma mh_QTSup:
  assumes a1: "f \<in> \<mh>"
  shows "(\<lSUP> x | P x \<bullet> f (g x)) \<lle> f (\<lSUP> x | P x \<bullet> g x)"
proof (rule Sup_lub, auto)
  fix x assume 
    a2: "P x"
  show 
    "f(g x) \<lle> f(\<lSUP> x | P x \<bullet> g x)"
    by (rule a1 [THEN mhD], rule Sup_ub, auto intro!: a2)
qed

section {* Lattice-morphic properties *}

text {*

In addition to monotonicity, lattice functions may
be categorised according to their preservation of the other lattice operators.

*}

definition
  inf_morphic :: "(('A::lattice) \<rightarrow> ('B::lattice)) set"
where
  inf_morphic_def: "inf_morphic \<defs> { p | (\<forall> A B \<bullet> p (A \<linf> B) = p A \<linf> p B) }"

notation (xsymbols output)
  inf_morphic ("M\<^bsub>\<sqinter>\<^esub>")

notation (zed)
  inf_morphic ("\<mhi>")

definition
  sup_morphic :: "(('A::lattice) \<rightarrow> ('B::lattice)) set"
where
  sup_morphic_def: "sup_morphic \<defs> { p | (\<forall> A B \<bullet> p (A \<lsup> B) = p A \<lsup> p B) }"

notation (xsymbols output)
  sup_morphic ("M\<^bsub>\<squnion>\<^esub>")

notation (zed)
  sup_morphic ("\<mhs>")

abbreviation
  inf_sup_morphic :: "(('A::lattice) \<rightarrow> ('B::lattice)) set"
where
  "inf_sup_morphic \<defs> \<mhi> \<inter> \<mhs>"

notation (xsymbols output)
  inf_sup_morphic ("M\<^bsub>\<sqinter>\<squnion>\<^esub>")

notation (zed)
  inf_sup_morphic ("\<mhis>")

lemma mhiI:
  assumes 
    a1: "\<And> A B \<bullet> p (A \<linf> B) = p A \<linf> p B"
  shows 
    "p \<in> \<mhi>"
  using a1
  by (simp add: inf_morphic_def)

lemma mhiD:
  assumes 
    a1: "p \<in> \<mhi>"
  shows 
    "p (A \<linf> B) = p A \<linf> p B"
  using a1
  by (simp add: inf_morphic_def)

lemma mhsI:
  assumes 
    a1: "\<And> A B \<bullet> p (A \<lsup> B) = p A \<lsup> p B"
  shows 
    "p \<in> \<mhs>"
  using a1
  by (simp add: sup_morphic_def)

lemma mhsD:
  assumes 
    a1: "p \<in> \<mhs>"
  shows 
    "p (A \<lsup> B) = p A \<lsup> p B"
  using a1
  by (simp add: sup_morphic_def)

lemma mhiDm:
  assumes 
    a1: "p \<in> \<mhi>-['A::lattice, 'B::lattice]"
  shows 
    "p \<in> \<mh>-['A::lattice, 'B::lattice]"
proof (rule mhI)
  fix A::'A and B::'A
  assume
    b1: "A \<lle> B"
  from b1 have
    "A \<linf> B 
    = A"
    by (simp add: inf_min)
  then have 
    "p A 
    = p (A \<linf> B)"
    by (simp)
  also have "\<dots> 
    = p A \<linf> p B" 
    by (simp add: mhiD [OF a1])
  also have "\<dots> 
    \<lle> p B"
    by (rule inf_lb2)
  finally show 
    "p A \<lle> p B"
    by (this)
qed

lemma mhsDm:
  assumes 
    a1: "p \<in> \<mhs>-['A::lattice,'B::lattice]"
  shows 
    "p \<in> \<mh>-['A::lattice, 'B::lattice]"
proof (rule mhI)
  fix A::'A and B::'A
  assume 
    b1: "A \<lle> B"
  from b1 have 
    "B = A \<lsup> B"
    by (simp add: sup_max)
  then have 
    "p B 
    = p (A \<lsup> B)"
    by (simp)
  also have "\<dots> 
    = p A \<lsup> p B" 
    by (simp add: mhsD [OF a1])
  also have "\<dots>
    \<lge> p A"
    apply (simp add: ge_def)
    apply (rule sup_ub1)
    done
  finally show 
    "p A \<lle> p B"
    by (simp add: ge_def)
qed

text {*

In the case of complete lattice, it is useful to distinguish distribution through
empty meets and joins from the non-empty case.

*}

definition
  bot_morphic :: "(('A::boundlattice) \<rightarrow> ('B::boundlattice)) set" 
where
  bot_morphic_def: "bot_morphic \<defs> \<mh> \<inter> {p | p \<lbot> = \<lbot>}"

notation (xsymbols output)
  bot_morphic ("M\<^bsub>\<bottom>\<^esub>")

notation (zed)
  bot_morphic ("\<mhb>")

definition
  top_morphic :: "(('A::boundlattice) \<rightarrow> ('B::boundlattice)) set" 
where
  top_morphic_def: "top_morphic \<defs>  \<mh> \<inter> {p | p \<ltop> = \<ltop>}"

notation (xsymbols output)
  top_morphic ("M\<^bsub>\<top>\<^esub>")

notation (zed)
  top_morphic ("\<mht>")

abbreviation
  bot_top_morphic :: "(('A::boundlattice) \<rightarrow> ('B::boundlattice)) set" 
where
  "bot_top_morphic \<defs>  \<mhb> \<inter> \<mht>"

notation (xsymbols output)
  bot_top_morphic ("M\<^bsub>\<bottom>\<top>\<^esub>")

notation (zed)
  bot_top_morphic ("\<mhbt>")

lemma mhbI:
  "\<lbrakk> p \<in> \<mh>; p \<lbot> = \<lbot> \<rbrakk> \<turnstile> p \<in> \<mhb>"
  by (simp add: bot_morphic_def)

lemma mhtI:
  "\<lbrakk> p \<in> \<mh>; p \<ltop> = \<ltop> \<rbrakk> \<turnstile> p \<in> \<mht>"
  by (simp add: top_morphic_def)

lemma mhbD:
  "p \<in> \<mhb> \<turnstile> p \<lbot> = \<lbot>"
  by (simp add: bot_morphic_def)

lemma mhtD:
  "p \<in> \<mht> \<turnstile> p \<ltop> = \<ltop>"
  by (simp add: top_morphic_def)

lemma mhbDm:
  assumes a1: "p \<in> \<mhb>"
  shows "p \<in> \<mh>"
  using a1
  by (auto simp add: bot_morphic_def)

lemma mhtDm:
  assumes a1: "p \<in> \<mht>"
  shows "p \<in> \<mh>"
  using a1
  by (auto simp add: top_morphic_def)

definition
  Inf_morphic :: "(('A::clattice) \<rightarrow> ('B::clattice)) set"
where 
  Inf_morphic_def: "Inf_morphic \<defs> {p | (\<forall> CL_A | CL_A \<noteq> \<emptyset> \<bullet> p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A))}"

notation (xsymbols output)
  Inf_morphic ("M\<^bsub>\<Sqinter>\<^esub>")

notation (zed)
  Inf_morphic ("\<mhI>")

definition
  Sup_morphic :: "(('A::clattice) \<rightarrow> ('B::clattice)) set"
where 
  Sup_morphic_def: "Sup_morphic \<defs> {p | (\<forall> CL_A | CL_A \<noteq> \<emptyset> \<bullet> p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A))}"

notation (xsymbols output)
  Sup_morphic ("M\<^bsub>\<Squnion>\<^esub>")

notation (zed)
  Sup_morphic ("\<mhS>")

abbreviation
  Sup_Inf_morphic :: "(('A::clattice) \<rightarrow> ('B::clattice)) set"
where 
  "Sup_Inf_morphic \<defs> \<mhS> \<inter> \<mhI>"

notation (xsymbols output)
  Sup_Inf_morphic ("M\<^bsub>\<Squnion>\<Sqinter>\<^esub>")

notation (zed)
  Sup_Inf_morphic ("\<mhSI>")

abbreviation
  bot_Sup_morphic :: "(('A::clattice) \<rightarrow> ('B::clattice)) set"
where 
  "bot_Sup_morphic \<defs> \<mhb> \<inter> \<mhS>"

notation (xsymbols output)
  bot_Sup_morphic ("M\<^bsub>\<bottom>\<Squnion>\<^esub>")

notation (zed)
  bot_Sup_morphic ("\<mhbS>")

abbreviation
  bot_Sup_Inf_morphic :: "(('A::clattice) \<rightarrow> ('B::clattice)) set"
where 
  "bot_Sup_Inf_morphic \<defs> \<mhbS> \<inter> \<mhI>"

notation (xsymbols output)
  bot_Sup_Inf_morphic ("M\<^bsub>\<bottom>\<Squnion>\<Sqinter>\<^esub>")

notation (zed)
  bot_Sup_Inf_morphic ("\<mhbSI>")

abbreviation
  Inf_top_morphic :: "(('A::clattice) \<rightarrow> ('B::clattice)) set"
where 
  "Inf_top_morphic \<defs> \<mhI> \<inter> \<mht>"

notation (xsymbols output)
  Inf_top_morphic ("M\<^bsub>\<Sqinter>\<top>\<^esub>")

notation (zed)
  Inf_top_morphic ("\<mhIt>")

abbreviation
  Sup_Inf_top_morphic :: "(('A::clattice) \<rightarrow> ('B::clattice)) set"
where 
  "Sup_Inf_top_morphic \<defs> \<mhSI> \<inter> \<mht>"

notation (xsymbols output)
  Sup_Inf_top_morphic ("M\<^bsub>\<Squnion>\<Sqinter>\<top>\<^esub>")

notation (zed)
  Sup_Inf_top_morphic ("\<mhSIt>")

abbreviation
  bot_Sup_Inf_top_morphic :: "(('A::clattice) \<rightarrow> ('B::clattice)) set"
where 
  "bot_Sup_Inf_top_morphic \<defs> \<mhbSI> \<inter> \<mht>"

notation (xsymbols output)
  bot_Sup_Inf_top_morphic ("M\<^bsub>\<bottom>\<Squnion>\<Sqinter>\<top>\<^esub>")

notation (zed)
  bot_Sup_Inf_top_morphic ("\<mhbSIt>")

lemma mhII:
  assumes 
    a1: "\<And> CL_A \<bullet> CL_A \<noteq> \<emptyset> \<turnstile> p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
  shows 
    "p \<in> \<mhI>"
  using a1
  by (auto simp add: Inf_morphic_def)

lemma mhSI:
  assumes 
    a1: "\<And> CL_A \<bullet> CL_A \<noteq> \<emptyset> \<turnstile> p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
  shows 
    "p \<in> \<mhS>"
  using a1
  by (auto simp add: Sup_morphic_def)

lemma mhID:
  assumes a1: "p \<in> \<mhI>" and a2: "CL_A \<noteq> \<emptyset>"
  shows "p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
  using a1 a2
  by (auto simp add: Inf_morphic_def)

lemma mhSD:
  assumes a1: "p \<in> \<mhS>" and a2: "CL_A \<noteq> \<emptyset>"
  shows "p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
  using a1 a2
  by (auto simp add: Sup_morphic_def)

lemma mhIDi:
  assumes 
    a1: "p \<in> \<mhI>"
  shows 
    "p \<in> \<mhi>"
  apply (rule mhiI)
  apply (simp add: inf_Inf mhID [OF a1])
  apply (rule arg_cong [of _ _ "Inf"])
  apply (auto)
  done

lemma mhSDs:
  assumes a1: "p \<in> \<mhS>"
  shows "p \<in> \<mhs>"
  apply (rule mhsI)
  apply (simp add: sup_Sup mhSD [OF a1])
  apply (rule arg_cong [of _ _ "Sup"])
  apply (auto)
  done

lemma mhbSI:
  assumes 
    a1: "\<And> CL_A \<bullet> p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
  shows "p \<in> \<mhbS>"
proof (auto)
  show b1: "p \<in> \<mhS>"
    apply (rule mhSI)
    apply (rule a1)
    done
  show "p \<in> \<mhb>"
    apply (rule mhbI)
    apply (rule mhsDm)
    apply (rule mhSDs)
    apply (rule b1)
    apply (simp add: Sup_empty [symmetric] a1 eind_def)
    done
qed

lemma mhbSD:
  assumes a1: "p \<in> \<mhbS>"
  shows "p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
proof (cases "CL_A = \<emptyset>")
  assume b1: "CL_A = \<emptyset>"
  have "p (\<lSup> CL_A) = p \<lbot>"
    by (simp add: b1 Sup_empty)
  also from a1 have "\<dots> = \<lbot>"
    by (simp add: mhbD)
  also have "\<dots> = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
    by (simp add: b1 Sup_empty eind_def)
  finally show "p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
    by (this)
next
  assume b1: "CL_A \<noteq> \<emptyset>"
  with a1 show "p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
    by (simp add: mhSD)
qed

lemma mhItI:
  assumes 
    a1: "\<And> CL_A \<bullet> p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
  shows "p \<in> \<mhIt>"
proof (auto)
  show b1: "p \<in> \<mhI>"
    apply (rule mhII)
    apply (rule a1)
    done
  show "p \<in> \<mht>"
    apply (rule mhtI)
    apply (rule mhiDm)
    apply (rule mhIDi)
    apply (rule b1)
    apply (simp add: Inf_empty [symmetric] a1 eind_def)
    done
qed

lemma mhItD:
  assumes a1: "p \<in> \<mhIt>"
  shows "p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
proof (cases "CL_A = \<emptyset>")
  assume b1: "CL_A = \<emptyset>"
  have "p (\<lInf> CL_A) = p \<ltop>"
    by (simp add: b1 Inf_empty)
  also from a1 have "\<dots> = \<ltop>"
    by (simp add: mhtD)
  also have "\<dots> = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
    by (simp add: b1 Inf_empty eind_def)
  finally show "p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
    by (this)
next
  assume b1: "CL_A \<noteq> \<emptyset>"
  with a1 show "p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
    by (simp add: mhID)
qed

lemma mhbSItI:
  assumes 
    a1: "\<And> CL_A \<bullet> p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A)" and 
    a2: "\<And> CL_A \<bullet> p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
  shows "p \<in> \<mhbSIt>"
proof (auto)
  show b1: "p \<in> \<mhI>"
    apply (rule mhII)
    apply (rule a1)
    done
  show b2: "p \<in> \<mhS>"
    apply (rule mhSI)
    apply (rule a2)
    done
  show "p \<in> \<mhb>"
    apply (rule mhbI)
    apply (rule mhiDm)
    apply (rule mhIDi)
    apply (rule b1)
    apply (simp add: Sup_empty [symmetric] a2 eind_def)
    done
  show "p \<in> \<mht>"
    apply (rule mhtI)
    apply (rule mhiDm)
    apply (rule mhIDi)
    apply (rule b1)
    apply (simp add: Inf_empty [symmetric] a1 eind_def)
    done
qed

lemma mhbSItD1:
  assumes a1: "p \<in> \<mhbSIt>"
  shows "p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
proof (cases "CL_A = \<emptyset>")
  assume b1: "CL_A = \<emptyset>"
  have "p (\<lInf> CL_A) = p \<ltop>"
    by (simp add: b1 Inf_empty)
  also from a1 have "\<dots> = \<ltop>"
    by (simp add: mhtD)
  also have "\<dots> = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
    by (simp add: b1 Inf_empty eind_def)
  finally show "p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
    by (this)
next
  assume b1: "CL_A \<noteq> \<emptyset>"
  with a1 show "p (\<lInf> CL_A) = (\<lINF> A | A \<in> CL_A \<bullet> p A)"
    by (simp add: mhID)
qed

lemma mhbSItD2:
  assumes a1: "p \<in> \<mhbSIt>"
  shows "p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
proof (cases "CL_A = \<emptyset>")
  assume b1: "CL_A = \<emptyset>"
  have "p (\<lSup> CL_A) = p \<lbot>"
    by (simp add: b1 Sup_empty)
  also from a1 have "\<dots> = \<lbot>"
    by (simp add: mhbD)
  also have "\<dots> = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
    by (simp add: b1 Sup_empty eind_def)
  finally show "p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
    by (this)
next
  assume b1: "CL_A \<noteq> \<emptyset>"
  with a1 show "p (\<lSup> CL_A) = (\<lSUP> A | A \<in> CL_A \<bullet> p A)"
    by (simp add: mhSD)
qed

lemmas mhIDm = mhIDi [THEN mhiDm]

lemmas mhSDm = mhSDs [THEN mhsDm]

end
  


