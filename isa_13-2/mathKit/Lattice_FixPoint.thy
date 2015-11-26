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

theory Lattice_FixPoint 

imports 
  Lattice_Class 
  Lattice_Morphism 
  Lattice_Instance

begin


subsection {* Fixed points *}

text {*

For any function @{term[show_types] "f::'a \<rightarrow> 'a"}, the fixed points of 
@{term "f"} are those points @{term "a"} such that @{term "f a = a"}.

*}

definition
  fp_set :: "('a \<rightarrow> 'a) \<rightarrow> 'a set"
where
  fp_set_def: "fp_set \<defs> (\<olambda> f \<bullet> { x | f x = x })"

text {*

The least fixed point is the infimum of the fixed point set.

*}

definition
  llfp :: "(('a::clattice) \<rightarrow> 'a) \<rightarrow> 'a"
where
  lfp_def: "llfp f \<defs> \<lInf>(fp_set f)"

definition
  lgfp :: "(('a::clattice) \<rightarrow> 'a) \<rightarrow> 'a"
where
  gfp_def: "lgfp f \<defs> \<lSup>(fp_set f)"

syntax (xsymbols)
  "_Lattice_FixPoint\<ZZ>lLFP" :: "[pttrn, ('a::clattice)] \<rightarrow> 'a" ("(2\<lLFP> _ \<bullet>/ _)" [0,10] 10)
  "_Lattice_FixPoint\<ZZ>lGFP" :: "[pttrn, ('a::clattice)] \<rightarrow> 'a" ("(2\<lGFP> _ \<bullet>/ _)" [0,10] 10)

translations
  "_Lattice_FixPoint\<ZZ>lLFP p b" \<rightleftharpoons> "(CONST llfp) (\<olambda> p \<bullet> b)"
  "_Lattice_FixPoint\<ZZ>lGFP p b" \<rightleftharpoons> "(CONST lgfp) (\<olambda> p \<bullet> b)"

(*
syntax (xsymbols output)
  "_Lattice_FixPoint\<ZZ>lLFP" :: "[idt, ('a::clattice)] \<rightarrow> 'a" ("(2\<mu> _ \<bullet>/ _)" [0,10] 10)
  "_Lattice_FixPoint\<ZZ>lGFP" :: "[idt, ('a::clattice)] \<rightarrow> 'a" ("(2\<nu> _ \<bullet>/ _)" [0,10] 10);

syntax (zed)
  "_Lattice_FixPoint\<ZZ>lLFP" :: "[idt, ('a::clattice)] \<rightarrow> 'a" ("(2\<lLFP>_\<bullet>/ _)" [0,10] 10)
  "_Lattice_FixPoint\<ZZ>lGFP" :: "[idt, ('a::clattice)] \<rightarrow> 'a" ("(2\<lGFP>_\<bullet>/ _)" [0,10] 10);

parse_translation {* [
  mk_binder_tr("_Lattice_FixPoint\<ZZ>lLFP","\<^const>Lattice_FixPoint.llfp"), 
  mk_binder_tr("_Lattice_FixPoint\<ZZ>lGFP","\<^const>Lattice_FixPoint.lgfp")
] *};

print_translation {* [
  mk_binder_tr'("\<^const>Lattice_FixPoint.llfp","_Lattice_FixPoint\<ZZ>lLFP"), 
  mk_binder_tr'("\<^const>Lattice_FixPoint.lgfp","_Lattice_FixPoint\<ZZ>lGFP")
] *};

*)

text {* 
The infimum of all the fixed points is a fixed point, as is the
supremum.
*}

lemma lfp_wit:
  assumes a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>"
  shows "f (\<lINF> x | f x \<lle> x) = (\<lINF> x | f x \<lle> x)"
proof -
txt {* We follow the proof of Back and von Wright~\cite[p 18,19]{Back:Text}. *}
  from a1 [THEN mh_Inf, of "{ x | f x \<lle> x }"] have 
    "f(\<lINF> x | f x \<lle> x) \<lle> (\<lINF> x | f x \<lle> x \<bullet> f x)"
    by (auto)
  also have "\<dots> \<lle> (\<lINF> x | f x \<le> x)"
  proof (rule Inf_glb, simp)
    fix x::'a assume b1: "f x \<lle> x"
    show "(\<lINF> x | f x \<lle> x \<bullet> f x) \<lle> x"
      by (rule b1 [THEN [2] order_trans])
        (rule Inf_lb, simp, rule exI [of _ x], auto intro: b1)
  qed
  finally have a2: "f(\<lINF> x | f x \<lle> x) \<lle> (\<lINF> x | f x \<le> x)" .
  from a2 have "f(f(\<lINF> x | f x \<lle> x)) \<lle> f(\<lINF> x | f x \<le> x)"  
    by (auto intro: a1 [THEN mhD])
  hence "f(\<lINF> x | f x \<le> x) \<in> {x | f x \<le> x}" 
    by (auto)
  hence "(\<lINF> x | f x \<lle> x) \<lle> f(\<lINF> x | f x \<lle> x)" 
    by (auto intro: Inf_lb)
  with a2 show ?thesis by (rule order_antisym)
qed

lemma gfp_wit:
  assumes a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>"
  shows "f (\<lSUP> x | x \<lle> f x) = (\<lSUP> x | x \<lle> f x)"
proof -
  have "(\<lSUP> x | x \<lle> f x) \<lle> (\<lSUP> x | x \<lle> f x \<bullet> f x)"
  proof (rule Sup_lub, simp)
    fix x::'a assume b1: "x \<lle> f x"
    show "x \<lle> (\<lSUP> x | x \<lle> f x \<bullet> f x)"
      by (rule b1 [THEN order_trans])
        (rule Sup_ub, simp, rule exI [of _ x], auto intro: b1)
  qed
  also from a1 [THEN mh_Sup, of "{ x | x \<lle> f x }"] have "\<dots> \<lle> f (\<lSUP> x | x \<lle> f x)"
    by (auto)
  finally have a2: "(\<lSUP> x | x \<lle> f x) \<lle> f (\<lSUP> x | x \<lle> f x)" .
  from a2 have "f(\<lSUP> x | x \<lle> f x) \<lle> f (f (\<lSUP> x | x \<lle> f x))" 
    by (auto intro: a1 [THEN mhD])
  hence "f (\<lSUP> x | x \<lle> f x) \<in> { x | x \<lle> f x}"
    by (auto)
  hence "f (\<lSUP> x | x \<lle> f x) \<lle> (\<lSUP> x | x \<lle> f x)" 
    by (auto intro: Sup_ub)
  with a2 show ?thesis 
    by (auto intro: order_antisym)
qed

lemma lfp_char:
  assumes a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>"
  shows "(\<lLFP> x \<bullet> f x) = (\<lINF> x | f x \<lle> x)"
  apply (unfold lfp_def)
  apply (rule Min_eq)
  apply (auto intro: lfp_wit [OF a1] simp add: fp_set_def)
proof -  
  fix x::'a assume a2: "f x = x"
  from a2 have "f x \<lle> x" by (rule order_eq_refl)
  hence "x \<in> {x | f x \<lle> x}" by (auto)
  thus "(\<lINF> x | f x \<lle> x) \<lle> x" by (rule Inf_lb)
qed
  
lemma gfp_char:
  assumes a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>"
  shows "(\<lGFP> x \<bullet> f x) = (\<lSUP> x | x \<lle> f x)"
proof (unfold gfp_def, rule Max_eq, auto intro: gfp_wit [OF a1] simp add: fp_set_def)
  fix x::'a assume a2: "f x = x"
  from a2 have "x \<lle> f x" by (rule sym [THEN order_eq_refl])
  hence "x \<in> {x | x \<lle> f x}" by (auto)
  thus "x \<lle> (\<lSUP> x | x \<lle> f x)" by (rule Sup_ub)
qed

text {*

Thus every monotonic function has a least and a greatest fixed point.

*}

theorem Knaster_Tarski:
  assumes a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>"
  shows 
    "(\<exists> x \<bullet> f x = x \<and> (\<lLFP> x \<bullet> f x) = x)"
    "(\<exists> x \<bullet> f x = x \<and> (\<lGFP> x \<bullet> f x) = x)"
proof -
  show "\<exists> x \<bullet> f x = x \<and> (\<lLFP> x \<bullet> f x) = x"
    by (witness "\<lINF> x | f x \<lle> x")
      (auto intro: a1 [THEN lfp_wit] a1 [THEN lfp_char])
  show "\<exists>x \<bullet> f x = x \<and> (\<lGFP> x \<bullet> f x) = x"
    by (witness "\<lSUP> x | x \<lle> f x")
      (auto intro: a1 [THEN gfp_wit] a1 [THEN gfp_char])
qed

text {*
Least (greatest) fixed points admit the expected unfolding and induction 
rules.
*}

lemma lfp_fold:
  assumes a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>"
  shows "f (\<lLFP> x \<bullet> f x) = (\<lLFP> x \<bullet> f x)"
  using a1
  by (auto simp add: lfp_char lfp_wit)
 
lemma lfp_induct:
  assumes 
    a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>" "f x \<lle> x"
  shows  
    "(\<lLFP> x \<bullet> f x) \<lle> x"
  using a1
  by (auto simp add: lfp_char intro: Inf_lb)

lemma lfp_glbfp:
  assumes
    a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>" and
    a2: "(\<And> x \<bullet> f x \<lle> x \<turnstile> z \<lle> x)"
  shows
    "z \<lle> (\<lLFP> x \<bullet> f x)"
  using a1 a2
  by (auto simp add: lfp_char intro: Inf_glb)

lemma lfp_eq:
  assumes
    a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>" and
    a2: "f z \<lle> z" and
    a3: "(\<And> y \<bullet> f y \<lle> y \<turnstile> z \<lle> y)"
  shows 
    "(\<lLFP> x \<bullet> f x) = z"
  using a1 a2 a3
  by (auto simp add: lfp_char intro: Inf_eq)
    
lemma gfp_fold:
  assumes 
    a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>"
  shows 
    "f (\<lGFP> x \<bullet> f x) = (\<lGFP> x \<bullet> f x)"
  using a1
  by (auto simp add: gfp_char gfp_wit)

lemma gfp_induct:
  assumes 
    a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>" "x \<lle> f x"
  shows 
    "x \<lle> (\<lGFP> x \<bullet> f x)"
  using a1
  by (auto simp add: gfp_char intro: Sup_ub)

text {*

The fixed point operators are monotonic on monotonic functions.

*}

lemma lfp_mono:
 fixes f::"('a::clattice) \<rightarrow> 'a" and g::"('a::clattice) \<rightarrow> 'a"
 assumes  a1: "f \<in> \<mh>" and
    a2: "g \<in> \<mh>" and
    a3: "f \<lle> g"
  shows "(\<lLFP> x \<bullet> f x) \<lle> (\<lLFP> x \<bullet> g x)"
proof -
  from a3 have "f (\<lLFP> x \<bullet> g x) \<lle> g (\<lLFP> x \<bullet> g x)" 
    by (rule fun_le)
  with a2 have "f (\<lLFP> x \<bullet> g x) \<lle> (\<lLFP> x \<bullet> g x)" 
    by (simp add: lfp_fold)
  with a1 show "(\<lLFP> x \<bullet> f x) \<lle> (\<lLFP> x \<bullet> g x)" 
    by (rule lfp_induct)
qed

    
lemma gfp_mono:
  fixes f::"('a::clattice) \<rightarrow> 'a" and g::"('a::clattice) \<rightarrow> 'a"
  assumes  a1: "f \<in> \<mh>" and
    a2: "g \<in> \<mh>" and
    a3: "f \<lle> g"
  shows "(\<lGFP> x \<bullet> f x) \<lle> (\<lGFP> x \<bullet> g x)"
proof -
  from a3 have "f (\<lGFP> x \<bullet> f x) \<lle> g (\<lGFP> x \<bullet> f x)" 
    by (rule fun_le)
  with a1 have "(\<lGFP> x \<bullet> f x) \<lle> g (\<lGFP> x \<bullet> f x)" 
    by (simp add: gfp_fold)
  with a2 show "(\<lGFP> x \<bullet> f x) \<lle> (\<lGFP> x \<bullet> g x)" 
    by (rule gfp_induct)
qed

text {*

We can extract fold equations from tuple recursion equations.

*}

lemma split_lfp_fold:
  assumes
    a1: "(\<olambda> (a, b) \<bullet> (f a b, g a b)) \<in> \<mh>" and
    a2: "(x, y) = (\<lLFP> (a, b) \<bullet> (f a b, g a b))"
  shows
    split_lfp_fold1: "f x y = x" and
    split_lfp_fold2: "g x y = y"
proof -
  from lfp_fold [OF a1, simplified a2 [symmetric]] show 
     "f x y = x"  "g x y = y"
    by (auto)
qed

lemma split_lfp_fold1':
  assumes
    a1: "f \<in> \<mh>" and
    a2: "(x, y) = (\<lLFP> ab \<bullet> f ab)"
  shows
    "\<fst> (f (x, y)) = x" 
  apply (rule split_lfp_fold1 [of "(\<olambda> a b \<bullet> fst (f (a, b)))" "(\<olambda> a b \<bullet> snd (f (a, b)))" "x" "y"])
  using a1 a2
  apply (auto)
  done

lemma split_lfp_fold2':
  assumes
    a1: "f \<in> \<mh>" and
    a2: "(x, y) = (\<lLFP> ab \<bullet> f ab)"
  shows
    "\<snd> (f (x, y)) = y"
  apply (rule split_lfp_fold2 [of "(\<olambda> a b \<bullet> fst (f (a, b)))" "(\<olambda> a b \<bullet> snd (f (a, b)))" "x" "y"])
  using a1 a2
  apply (auto)
  done

lemmas split_lfp_fold' = split_lfp_fold1' split_lfp_fold2'

lemma prod_mh:
    "(\<olambda> (a, b) \<bullet> (f a b, g a b)) \<in> \<mh> 
    \<Leftrightarrow> (\<forall> y \<bullet> (\<olambda> a \<bullet> f a y) \<in> \<mh>) \<and> 
      (\<forall> y \<bullet> (\<olambda> a \<bullet> g a y) \<in> \<mh>) \<and>
      (\<forall> x \<bullet> (\<olambda> b \<bullet> g x b) \<in> \<mh>) \<and>
      (\<forall> x \<bullet> (\<olambda> b \<bullet> f x b) \<in> \<mh>)"
proof (msafe(inference))
  assume
    b1: "(\<olambda> (a, b) \<bullet> (f a b, g a b)) \<in> \<mh>"
{ fix x
  from b1 show
      "(\<olambda> b \<bullet> g x b) \<in> \<mh>"
      "(\<olambda> b \<bullet> f x b) \<in> \<mh>"
    by (auto elim!: mhE intro!: mhI simp add: le_prod_conv)
next
  fix y
  from b1 show
      "(\<olambda> a \<bullet> f a y) \<in> \<mh>" 
      "(\<olambda> a \<bullet> g a y) \<in> \<mh>"
    by (auto elim!: mhE intro!: mhI simp add: le_prod_conv) }
next
  assume
    b1: "(\<forall> y \<bullet> (\<olambda> a \<bullet> f a y) \<in> \<mh>)" and
    b2: "(\<forall> y \<bullet> (\<olambda> a \<bullet> g a y) \<in> \<mh>)" and
    b3: "(\<forall> x \<bullet> (\<olambda> b \<bullet> g x b) \<in> \<mh>)" and
    b4: "(\<forall> x \<bullet> (\<olambda> b \<bullet> f x b) \<in> \<mh>)"
  show
      "(\<olambda> (a, b) \<bullet> (f a b, g a b)) \<in> \<mh>"
  proof (auto intro!: mhI simp add: le_prod_conv)
    fix 
      x::"'a" and
      x'::"'a" and
      y::"'b" and
      y'::"'b"
    assume
      c1: "x \<le> x'" and
      c2: "y \<le> y'"
    from b4 [rule_format, of "x"] c2
    have
        "f x y 
        \<le> f x y'"
      by (rule mhD)
    also from b1 [rule_format, of "y'"] c1 have "\<dots>
        \<le>  f x' y'"
      by (rule mhD)
    finally show
        "f x y \<le> f x' y'"
      by (this)
    from b3 [rule_format, of "x"] c2
    have
        "g x y 
        \<le> g x y'"
      by (rule mhD)
    also from b2 [rule_format, of "y'"] c1 have "\<dots>
        \<le>  g x' y'"
      by (rule mhD)
    finally show
        "g x y \<le> g x' y'"
      by (this)
  qed
qed

lemma split_lfp:
  assumes
    a1: "(\<olambda> (a, b) \<bullet> (f a b, g a b)) \<in> \<mh>" and
    a2: "(x, y) = (\<lLFP> (a, b) \<bullet> (f a b, g a b))"
  shows
    split_lfp1: "x = (\<lLFP> a \<bullet> f a y)" and
    split_lfp2: "y = (\<lLFP> b \<bullet> g x b)"
proof -
  from a1 have
    b1: "(\<forall> b \<bullet> (\<olambda> a \<bullet> f a b) \<in> \<mh>)" and
    b2: "(\<forall> b \<bullet> (\<olambda> a \<bullet> g a b) \<in> \<mh>)" and
    b3: "(\<forall> a \<bullet> (\<olambda> b \<bullet> g a b) \<in> \<mh>)" and 
    b4: "(\<forall> a \<bullet> (\<olambda> b \<bullet> f a b) \<in> \<mh>)"
    by (simp_all add: prod_mh)
  show 
      "x = (\<lLFP> a \<bullet> f a y)" 
      "y = (\<lLFP> b \<bullet> g x b)"
  proof (auto intro!: order_antisym)
    from split_lfp_fold1 [OF a1 a2]
    show 
      c1: "(\<lLFP> a \<bullet> f a y) \<lle> x"
      apply (simp add: lfp_def fp_set_def)
      apply (rule Inf_lb)
      apply (simp)
      done
    from split_lfp_fold2 [OF a1 a2]
    show 
      c2: "(\<lLFP> b \<bullet> g x b) \<lle> y"
      apply (simp add: lfp_def fp_set_def)
      apply (rule Inf_lb)
      apply (simp)
      done
    have "(x, y) \<lle> ((\<lLFP> a \<bullet> f a y), (\<lLFP> b \<bullet> g x b))"
    proof (simp add: a2, rule lfp_induct [OF a1])
      have 
          "(\<olambda> (a, b) \<bullet> (f a b, g a b)) ((\<lLFP> a \<bullet> f a y), (\<lLFP> b \<bullet> g x b))
          = (f (\<lLFP> a \<bullet> f a y) (\<lLFP> b \<bullet> g x b), g (\<lLFP> a \<bullet> f a y) (\<lLFP> b \<bullet> g x b))"
        by (simp)
      also have "\<dots>
          \<lle> (f (\<lLFP> a \<bullet> f a y) y, g (\<lLFP> a \<bullet> f a y) (\<lLFP> b \<bullet> g x b))" 
        by (auto simp add: le_prod_conv mhD [OF b4 [rule_format] c2])
      also have "\<dots>
          \<lle> (f (\<lLFP> a \<bullet> f a y) y, g x (\<lLFP> b \<bullet> g x b))" 
        by (auto simp add: le_prod_conv mhD [OF b2 [rule_format] c1])
      also have "\<dots> 
          = ((\<lLFP> a \<bullet> f a y), g x (\<lLFP> b \<bullet> g x b))" 
        by (auto simp add: lfp_fold [OF b1 [rule_format]])
      also have "\<dots> 
          = ((\<lLFP> a \<bullet> f a y), (\<lLFP> b \<bullet> g x b))" 
        by (auto simp add: lfp_fold [OF b3 [rule_format]])
      finally show 
          "(\<olambda> (a, b) \<bullet> (f a b, g a b)) ((\<lLFP> a \<bullet> f a y), (\<lLFP> b \<bullet> g x b))
          \<lle> ((\<lLFP> a \<bullet> f a y), (\<lLFP> b \<bullet> g x b))"
        by (this)
    qed
    then show
        "x \<lle> (\<lLFP> a \<bullet> f a y)"
        "y \<lle> (\<lLFP> b \<bullet> g x b)"
      by (auto simp add: le_prod_conv)
  qed
qed 

lemma split_lfp1':
  assumes
    a1: "f \<in> \<mh>" and
    a2: "(x, y) = (\<lLFP> ab \<bullet> f ab)"
  shows
    "x = (\<lLFP> a \<bullet> \<fst> (f (a, y)))"
  apply (rule split_lfp1 [of "(\<olambda> a b \<bullet> fst (f (a, b)))" "(\<olambda> a b \<bullet> snd (f (a, b)))" "x" "y"])
  using a1 a2
  apply (auto)
  done

lemma split_lfp2':
  assumes
    a1: "f \<in> \<mh>" and
    a2: "(x, y) = (\<lLFP> ab \<bullet> f ab)"
  shows
    "y = (\<lLFP> b \<bullet> \<snd> (f (x, b)))"
  apply (rule split_lfp2 [of "(\<olambda> a b \<bullet> fst (f (a, b)))" "(\<olambda> a b \<bullet> snd (f (a, b)))" "x" "y"])
  using a1 a2
  apply (auto)
  done

lemmas split_lfp' = split_lfp1' split_lfp2'

(*

ML{*

MProver.mclasimpset_of ("wind", @{context})

*}

*)


end
