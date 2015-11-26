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

theory Lattice_Class 
  
imports 
  Lattice_Locale

begin

text {*

In order to do applied reasoning with lattices, we introduce axiomatic
classes for the various kinds of lattice.

*}

section {* Binary Lattices *}

text {*

A lattice is an order with pairwise meets and joins.

*}

class lat = ord +

fixes
  oinf :: "['a,'a] \<rightarrow> 'a" (infixl "&&" 70) and
  osup :: "['a,'a] \<rightarrow> 'a" (infixl "||" 65)

begin

end

class lattice = order + lat +
assumes
  inf_lb1: "x && y \<le> x" and
  inf_lb2: "x && y \<le> y" and
  inf_glb: "\<lbrakk> z \<le> x; z \<le> y \<rbrakk> \<turnstile> z \<le> x && y" and
  sup_ub1: "x \<le> x || y" and
  sup_ub2: "y \<le> x || y" and
  sup_lub: "\<lbrakk> x \<le> z; y \<le> z \<rbrakk> \<turnstile> x || y \<le> z"

begin

end

text {*

When discussing lattices we write
@{text "(op \<llt>)"} for less-than and
@{text "(op \<linf>)"} for infimum (meet) and 
@{text "(op \<lsup>)"} for supremum (join).

*}

abbreviation
  linf :: "['a,'a] \<rightarrow> ('a::lattice)"
where
  "linf \<defs> oinf"

abbreviation
  lsup :: "['a,'a] \<rightarrow> ('a::lattice)"
where
  "lsup \<defs> osup"

notation (xsymbols)
  linf (infixl "\<linf>" 70) and
  lsup (infixl "\<lsup>" 65)

syntax ("" output)
  "_Lattice_Class\<ZZ>le" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "[=" 50)
  "_Lattice_Class\<ZZ>lt" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "[" 50)
  "_Lattice_Class\<ZZ>ge" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "]=" 50)
  "_Lattice_Class\<ZZ>gt" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "]" 50)

syntax (xsymbols output)
  "_Lattice_Class\<ZZ>le" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  "_Lattice_Class\<ZZ>lt" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "\<sqsubset>" 50)
  "_Lattice_Class\<ZZ>ge" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "\<sqsupseteq>" 50)
  "_Lattice_Class\<ZZ>gt" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "\<sqsupset>" 50)

syntax (zed)
  "_Lattice_Class\<ZZ>le" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "\<lle>" 50)
  "_Lattice_Class\<ZZ>lt" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "\<llt>" 50)
  "_Lattice_Class\<ZZ>ge" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "\<lge>" 50)
  "_Lattice_Class\<ZZ>gt" :: "['a::lattice,'a] \<rightarrow> bool" (infixl "\<lgt>" 50)

parse_translation {*
let
  val dlattT = TFree("'_dummy_", [@{class "lattice"}]);
  val dlordT =
    dlattT --> dlattT --> boolT;
  fun trT nm _ [a, b] = 
    Const(nm, dlordT) $ a $ b
    | trT nm _ [a] = 
    Const(nm, dlordT) $ a
    | trT nm _ [] = 
    Const(nm, dlordT);
in
  [(@{syntax_const "_Lattice_Class\<ZZ>le"}, trT @{const_syntax "less_eq"}), 
   (@{syntax_const "_Lattice_Class\<ZZ>lt"}, trT @{const_syntax "less"}), 
   (@{syntax_const "_Lattice_Class\<ZZ>ge"}, trT @{const_syntax "great_eq"}),
   (@{syntax_const "_Lattice_Class\<ZZ>gt"}, trT @{const_syntax "great"})]
end;
*}

definition
  ch_lle :: "['a::lattice,'a] \<rightarrow> bool"
where
  ch_lle_def: "ch_lle x y \<defs> x \<lle> y"

definition
  ch_llt :: "['a::lattice,'a] \<rightarrow> bool"
where
  ch_llt_def: "ch_llt x y \<defs> x \<llt> y"

definition
  ch_lge :: "['a::lattice,'a] \<rightarrow> bool"
where
  ch_lge_def: "ch_lge x y \<defs> x \<lge> y"

definition
  ch_lgt :: "['a::lattice,'a] \<rightarrow> bool"
where
  ch_lgt_def: "ch_lgt x y \<defs> x \<lgt> y"

syntax (xsymbols output)
  "_Lattice_Class\<ZZ>ch_lle" :: "['a, chainelt] \<rightarrow> chainrel" (infixr "\<sqsubseteq>" 50)
  "_Lattice_Class\<ZZ>ch_llt" :: "['a, chainelt] \<rightarrow> chainrel" (infixr "\<sqsubset>" 50)
  "_Lattice_Class\<ZZ>ch_lge" :: "['a, chainelt] \<rightarrow> chainrel" (infixr "\<sqsupseteq>" 50)
  "_Lattice_Class\<ZZ>ch_lgt" :: "['a, chainelt] \<rightarrow> chainrel" (infixr "\<sqsupset>" 50)

syntax (zed)
  "_Lattice_Class\<ZZ>ch_lle" :: "['a, chainelt] \<rightarrow> chainrel" (infixr "\<chLle>" 50)
  "_Lattice_Class\<ZZ>ch_llt" :: "['a, chainelt] \<rightarrow> chainrel" (infixr "\<chLlt>" 50)
  "_Lattice_Class\<ZZ>ch_lge" :: "['a, chainelt] \<rightarrow> chainrel" (infixr "\<chLge>" 50)
  "_Lattice_Class\<ZZ>ch_lgt" :: "['a, chainelt] \<rightarrow> chainrel" (infixr "\<chLgt>" 50)

parse_translation {*

[
  (chNode_tr "Lattice_Class" "ch_llt"),
  (chNode_tr "Lattice_Class" "ch_lle"),
  (chNode_tr "Lattice_Class" "ch_lgt"),
  (chNode_tr "Lattice_Class" "ch_lge")
]

*}

print_translation {*

[
  (chNode_tr' "Lattice_Class" "ch_llt"),
  (chNode_tr' "Lattice_Class" "ch_lle"),
  (chNode_tr' "Lattice_Class" "ch_lgt"),
  (chNode_tr' "Lattice_Class" "ch_lge")
]

*}

text {*

We provide a typed print translation to ensure that order predicates
only use the square cup sign when the arguments are of lattice sort.
Also for some lattices (eg nat) it may not be appropriate to use
the square cup, so we introduce a trivial class @{text "nonsqord"}
which can be used to suppress it.
Since it is not conventional to use the squared cup sign on 
numbers, we suppress this translation for any type of @{text number}
class, whether a lattice or not.

*}

class
  nonsqord = lattice

typed_print_translation {*
let
  fun ck_lat sgn (Type(@{type_name "fun"}, (typ::_))) =
  let
    val ityp = typ;
  in
    Sign.of_sort sgn (ityp, [@{class "lattice"}]) andalso
    not (Sign.of_sort sgn (ityp, [@{class "nonsqord"}])) 
(* andalso
    not (Sign.of_sort sgn (ityp, [@{class "number"}]))
*)
  end
   |  ck_lat _ _ = false;
  fun trT' nml ctxt typ ts = 
    if ck_lat (Proof_Context.theory_of ctxt) typ then
      list_comb (Syntax.const nml, ts) 
    else
      raise Match; 
in
  [(@{const_syntax "less"}, trT' @{syntax_const "_Lattice_Class\<ZZ>lt"}),
   (@{const_syntax "less_eq"}, trT' @{syntax_const "_Lattice_Class\<ZZ>le"}),
   (@{const_syntax "great"}, trT' @{syntax_const "_Lattice_Class\<ZZ>gt"}),
   (@{const_syntax "great_eq"}, trT' @{syntax_const "_Lattice_Class\<ZZ>ge"})]
end;
*}

lemma inf_glbI: 
    "\<^glbp>{:\<univ>:}{:(op \<lle>):} {x, y} (x \<linf> y)"
  apply (rule order_class.is_glbI)
  apply (auto intro!: inf_lb1 inf_lb2 inf_glb)
  done

lemma sup_lubI: 
    "\<^lubp>{:\<univ>:}{:(op \<lle>):} {x, y} (x \<lsup> y)"
  apply (rule order_class.is_lubI)
  apply (auto intro!: sup_ub1 sup_ub2 sup_lub)
  done

theorem lattice_classI:
  assumes 
    a1: "\<^lattice>{:\<univ>-[('a::{order, lat})]:}{:(op \<le>):}" and
    a2: "\<And> x y \<bullet> x && y = x \<^meet>{:\<univ>-[('a::{order, lat})]:}{:(op \<le>):} y" and
    a3: "\<And> x y \<bullet> x || y = x \<^join>{:\<univ>-[('a::{order, lat})]:}{:(op \<le>):} y"
  shows 
      "OFCLASS('a::{order, lat}, lattice_class)"
  apply (intro_classes)
  apply (auto simp add: a2 a3)
  apply (auto intro!: 
    lattice.meet_lbD1 [OF a1] lattice.meet_lbD2 [OF a1] lattice.meet_glbD [OF a1]
    lattice.join_ubD1 [OF a1] lattice.join_ubD2 [OF a1] lattice.join_lubD [OF a1])
  done

lemma lattice_classD:
    "\<^lattice>{:\<univ>-[('a::lattice)]:}{:(op \<lle>):}"
  apply (rule order_class.latticeI)
  apply (auto intro!: exI inf_glbI sup_lubI)
  done

lemma lattice_class_defaultD:
  assumes 
    a1: "X \<noteq> \<emptyset>" and
    a2: "\<And> a b \<bullet> \<lbrakk> a \<in> X; b \<in> X \<rbrakk> \<turnstile> a \<linf> b \<in> X" and 
    a3: "\<And> a b \<bullet> \<lbrakk> a \<in> X; b \<in> X \<rbrakk> \<turnstile> a \<lsup> b \<in> X"
  shows 
    "\<^lattice>{:X:}{:(default_order X):}"
proof -
  from a1 interpret 
    def_po: po_carrier X
    by (unfold_locales)
  from def_po.partial_order show
    "\<^lattice>{:X:}{:(default_order X):}"
  proof (unfold_locales)
    fix a b 
    assume 
      b1: "a \<in> X" and 
      b2: "b \<in> X"
    show 
        "(\<exists> x \<bullet> \<^glbp>{:X:}{:(default_order X):} {a, b} x)"
      apply (witness "a \<linf> b")
      apply (rule def_po.is_glbI)
      apply (auto intro!: inf_lb1 inf_lb2 inf_glb simp add: default_order_def subset_order_def rel2op_def op2rel_def b1 b2 a2)
      done
    show 
        "(\<exists> x \<bullet> \<^lubp>{:X:}{:(default_order X):} {a, b} x)"
      apply (witness "a \<lsup> b")
      apply (rule def_po.is_lubI)
      apply (auto intro!: sup_ub1 sup_ub2 sup_lub simp add: default_order_def subset_order_def rel2op_def op2rel_def b1 b2 a3)
      done
  qed
qed

interpretation lattice_class_interpretation: Lattice_Locale.lattice "\<univ>-[('a::lattice)]" "(op <=)"
  by (rule lattice_classD)

lemma
  inf_meet: "(op \<linf>) = (\<olambda> x y \<bullet> x \<^meet>{:\<univ>:}{:(op <=):} y)"
  apply (intro ext)
  apply (rule order_class.glb_unique)
  apply (auto intro: lattice_class_interpretation.meet_glb inf_glbI)
  done

lemma
  sup_join: "(op \<lsup>) = (\<olambda> x y \<bullet> x \<^join>{:\<univ>:}{:(op <=):} y)"
  apply (intro ext)
  apply (rule order_class.lub_unique)
  apply (auto intro: lattice_class_interpretation.join_lub sup_lubI)
  done

text {*

We introduce introduction and elimination rules for making use of these
facts.

*}

lemma infE:
  assumes
    a1:
      "\<lbrakk> 
        x \<linf> y \<lle> x; 
        x \<linf> y \<lle> y; 
        (\<And> z \<bullet> \<lbrakk> z \<le> x; z \<lle> y \<rbrakk> \<turnstile> z \<le> x \<linf> y) 
       \<rbrakk> \<turnstile> R"
  shows 
      "R"
proof -
  from a1 inf_glbI show R 
    by (auto intro!: a1 simp add: is_glb_def is_greatest_def is_lb_def)
qed

lemma inf_lb1:
    "x \<linf> y \<lle> x"
  by (rule infE, auto)
  
lemma inf_lb2:
    "x \<linf> y \<lle> y"
  by (rule infE, auto)

lemma inf_glb:
    "\<lbrakk> z \<lle> x; z \<lle> y \<rbrakk> \<turnstile> z \<lle> x \<linf> y"
  by (rule infE [of x y]) (auto)

lemma inf_eq:
  "\<lbrakk> 
    a \<lle> x; 
    a \<lle> y; 
    (\<And> z \<bullet> \<lbrakk> z \<le> x; z \<lle> y \<rbrakk> \<turnstile> z \<lle> a)
   \<rbrakk> \<turnstile> x \<linf> y = a"
  by (auto intro!: order_class.meet_unique [symmetric] order_class.is_glbI simp add: inf_meet)

lemma supE:
  assumes
    a1: 
      "\<lbrakk> 
        x \<lle> x \<lsup> y;
        y \<lle> x \<lsup> y;
        (\<And> z \<bullet> \<lbrakk> x \<le> z; y \<lle> z \<rbrakk> \<turnstile> x \<lsup> y \<le> z)
       \<rbrakk> \<turnstile> R"
  shows
      "R"
proof -
  from a1 sup_lubI show 
      R 
    by (auto intro!: a1 simp add: is_lub_def is_least_def is_ub_def)
qed

lemma sup_ub1:
    "x \<lle> x \<lsup> y"
  by (rule supE, auto)

lemma sup_ub2:
    "y \<lle> x \<lsup> y"
  by (rule supE, auto)

lemma sup_lub:
    "\<lbrakk> x \<lle> z; y \<lle> z \<rbrakk> \<turnstile> x \<lsup> y \<lle> z"
  by (rule supE [of x y]) (auto)

lemma sup_eq:
    "\<lbrakk>
      x \<lle> s; 
      y \<lle> s; 
      (\<And> z \<bullet> \<lbrakk> x \<le> z; y \<lle> z \<rbrakk> \<turnstile> s \<lle> z)
     \<rbrakk> \<turnstile> x \<lsup> y = s"
  by (auto intro!: order_class.join_unique [symmetric] order_class.is_lubI simp add: sup_join)

text {*

Meet and join are monotonic, idempotent, commutative, associative, and
absorbative. 

*}

lemma inf_idem: 
    "x \<linf> x = x"
  apply (rule inf_eq) 
  apply (auto)
  done

lemma sup_idem: 
    "x \<lsup> x = x"
  apply (rule sup_eq) 
  apply (auto)
  done

lemma inf_com:
    "x \<linf> y = y \<linf> x"
  by (rule infE, rule inf_eq [THEN sym], auto)

lemma sup_com:
    "x \<lsup> y = y \<lsup> x"
  by (rule supE, rule sup_eq [THEN sym], auto)

lemma [mintro!(wind)]:
    "p = p' \<turnstile> p \<linf> q = p' \<linf> q"    
    "q = q' \<turnstile> p \<linf> q = p \<linf> q'"
  by (auto)    

lemma [mintro!(wind)]:
    "p = p' \<turnstile> p \<lsup> q = p' \<lsup> q"    
    "q = q' \<turnstile> p \<lsup> q = p \<lsup> q'"
  by (auto)    

lemma inf_mono1 [mintro!(wind)]:
  assumes 
    a1: "x \<lle> x'"
  shows
      "x \<linf> y \<lle> x' \<linf> y"
proof (rule inf_glb)
  show 
      "x \<linf> y \<lle> x'"
    by (rule a1 [THEN [2] order_trans], rule infE, assumption)
  show 
      "x \<linf> y \<lle> y"
    by (rule infE, assumption)
qed

lemma inf_mono2 [mintro!(wind)]:
    "x \<lle> x' \<turnstile> y \<linf> x \<lle> y \<linf> x'"
  by (simp add: inf_com, rule inf_mono1, auto)

lemmas inf_mono = inf_mono2 [THEN [2] inf_mono1 [THEN order_trans]]

lemma sup_mono1 [mintro!(wind)]:
  assumes
    a1: "x \<lle> x'"
  shows
      "x \<lsup> y \<lle> x' \<lsup> y"
proof (rule sup_lub)
  show 
      "x \<lle> x' \<lsup> y"
    by (rule a1 [THEN order_trans], rule supE, assumption)
  show 
      "y \<lle> x' \<lsup> y"
    by (rule supE, assumption)
qed

lemma sup_mono2 [mintro!(wind)]:
    "x \<lle> x' \<turnstile> y \<lsup> x \<lle> y \<lsup> x'"
  by (simp add: sup_com, rule sup_mono1, auto)

lemmas sup_mono = sup_mono2 [THEN [2] sup_mono1 [THEN order_trans]]

lemma inf_assoc:
    "(x \<linf> y) \<linf> z = x \<linf> (y \<linf> z)"
proof (rule sym, rule inf_eq [THEN sym])
  show 
      "x \<linf> (y \<linf> z) \<lle> x \<linf> y"
    by (rule inf_mono2, rule infE, auto)
  show 
      "x \<linf> (y \<linf> z) \<lle> z"
    by (rule order_trans [of _ "y \<linf> z"], rule infE, auto, 
      rule infE, auto)
  fix a 
  assume 
    a1: "a \<lle> x \<linf> y" and
    a2: "a \<le> z"
  have 
    a3: "a \<le> x"
    by (rule a1 [THEN order_trans], rule infE, auto)
  have 
    a4: "a \<le> y"
    by (rule a1 [THEN order_trans], rule infE, auto)
  have 
    a5: "a \<le> y \<linf> z"
    by (rule a2 [THEN a4 [THEN inf_glb]])
  show 
      "a \<le> x \<linf> (y \<linf> z)"
    by (auto intro: inf_glb a3 a5)
qed

lemma sup_assoc:
    "(x \<lsup> y) \<lsup> z = x \<lsup> (y \<lsup> z)"
proof (rule sym, rule sup_eq [THEN sym])
  show 
      "x \<lsup> y \<lle> x \<lsup> (y \<lsup> z)"
    by (rule sup_mono2, rule supE, auto)
  show 
      "z \<lle> x \<lsup> (y \<lsup> z)"
    by (rule order_trans [of _ "y \<lsup> z"], rule supE, auto, 
      rule supE, auto)
  fix a 
  assume 
    a1: "x \<lsup> y \<lle> a" and
    a2: "z \<le> a"
  have 
    a3: "x \<le> a"
    by (rule a1 [THEN [2] order_trans], rule supE, auto)
  have 
    a4: "y \<le> a"
    by (rule a1 [THEN [2] order_trans], rule supE, auto)
  have 
    a5: "y \<lsup> z \<le> a"
    by (rule a2 [THEN a4 [THEN sup_lub]])
  show 
      "x \<lsup> (y \<lsup> z) \<le> a"
    by (auto intro: sup_lub a3 a5)
qed

lemma inf_lcom:
  "x \<linf> (y \<linf> z) = y \<linf> (x \<linf> z)"
proof -
  have 
      "x \<linf> (y \<linf> z) 
      = (x \<linf> y) \<linf> z"
    by (simp add: inf_assoc)
  also have "\<dots> 
      = (y \<linf> x) \<linf> z"
    by (simp add: inf_com)
  also have "\<dots> 
      = y \<linf> (x \<linf> z)"
    by (simp add: inf_assoc)
  finally show 
      ?thesis 
    by (this)
qed

lemma sup_lcom:
    "x \<lsup> (y \<lsup> z) = y \<lsup> (x \<lsup> z)"
proof -
  have 
      "x \<lsup> (y \<lsup> z) 
      = (x \<lsup> y) \<lsup> z"
    by (simp add: sup_assoc)
  also have "\<dots> 
      = (y \<lsup> x) \<lsup> z"
    by (simp add: sup_com)
  also have "\<dots> 
      = y \<lsup> (x \<lsup> z)"
    by (simp add: sup_assoc)
  finally show 
      ?thesis 
    by (this)
qed 

lemmas lat_com_assoc = inf_com inf_assoc inf_lcom sup_com sup_assoc sup_lcom
  
lemma inf_absorption:
    "a \<linf> (a \<lsup> b) = a"
  by (rule supE, rule inf_eq, auto)

lemma sup_absorption:
    "a \<lsup> (a \<linf> b) = a"
  by (rule infE, rule sup_eq, auto)

text {*

The meet (join) of two elements is equal to one of them if and only if
they are related in the lattice order.

*}

lemma inf_min:
  assumes 
    a1: "x \<lle> y"
  shows 
      "x \<linf> y = x" 
  using a1
  by (auto intro:  inf_eq)

lemma inf_min':
  assumes 
    a1: "x \<lle> y"
  shows 
      "y \<linf> x = x"
  using a1
  by (auto intro:  inf_eq)

lemma sup_max:
  assumes 
    a1: "x \<lle> y"
  shows 
      "x \<lsup> y = y"
  using a1
  by (auto intro:  sup_eq)

lemma sup_max':
  assumes 
    a1: "x \<lle> y"
  shows 
      "y \<lsup> x = y"
  using a1
  by (auto intro:  sup_eq)

lemma min_inf:
  assumes
    a1: "x \<linf> y = x"
  shows
      "x \<lle> y"
  by (rule a1 [THEN subst], rule inf_lb2)

lemma max_sup:
  assumes
    a1: "x \<lsup> y = y"
  shows
      "x \<lsup> y = y \<turnstile> x \<lle> y"
  by (rule a1 [THEN subst], rule sup_ub1)

lemma inf_correspondence:
    "(x = x \<linf> y) = (x \<lle> y)"
proof (auto intro: inf_eq [THEN sym] simp add: order_antisym)
  assume 
    a1: "x = x \<linf> y"
  show 
      "x \<lle> y"
    by (rule a1 [THEN ssubst], rule infE [of x y], auto)
qed
  
lemma sup_correspondence:
    "(y = x \<lsup> y) = (x \<lle> y)"
proof (auto intro: sup_eq [THEN sym] simp add: order_antisym)
  assume 
    a1: "y = x \<lsup> y"
  show 
      "x \<lle> y"
    by (rule a1 [THEN ssubst], rule supE [of x y], auto)
qed

lemma inf_correspondence':
    "(x \<linf> y = x) = (x \<lle> y)"
proof (auto intro: inf_eq simp add: order_antisym)
  assume 
    a1: "x \<linf> y = x"
  show 
      "x \<lle> y"
    by (rule a1 [THEN sym, THEN ssubst], rule infE [of x y], auto)
qed
  
lemma sup_correspondence':
    "(x \<lsup> y = y) = (x \<lle> y)"
proof (auto intro: sup_eq simp add: order_antisym)
  assume 
    a1: "x \<lsup> y = y"
  show 
      "x \<lle> y"
    by (rule a1 [THEN sym,THEN ssubst], rule supE [of x y], auto)
qed

section {* Bounded lattices *}

text {*

A lattice with maximal amd minimal elements is said to be bounded.

*}

class blat = Lattice_Class.lat +

fixes
  bot :: "'a" and
  top :: "'a"

begin

end

class boundlattice = Lattice_Class.lattice + Lattice_Class.blat + 

assumes
  bot_lb: "bot \<le> x"

assumes
  top_ub: "x \<le> top"

begin

end

abbreviation
  bl_bot :: "'a::boundlattice"
where
  "bl_bot \<defs> bot"

abbreviation
  bl_top :: "'a::boundlattice"
where
  "bl_top \<defs> top"

notation (xsymbols)
  bl_bot ("\<lbot>") and 
  bl_top ("\<ltop>")

lemma bot_eq:
    "(\<forall> x \<bullet> y \<lle> x) \<turnstile> \<lbot> = y"
  by (rule order_antisym, auto intro: bot_lb)

lemma top_eq:
    "(\<forall> x \<bullet> x \<lle> y) \<turnstile> \<ltop> = y"
  by (rule order_antisym, auto intro: top_ub)

lemma bot_min:
    "x \<lle> \<lbot> \<Leftrightarrow> x = \<lbot>"
  apply (auto intro!: bot_eq [THEN sym])
  apply (rule order_trans)
  apply (assumption)
  apply (rule bot_lb)
  done

lemma top_max:
    "\<ltop> \<lle> x \<Leftrightarrow> x = \<ltop>"
  apply (auto intro!: top_eq [THEN sym])
  apply (rule order_trans)
  apply (rule top_ub)
  apply (assumption)
  done

lemmas lat_bounds = 
  bot_lb [THEN inf_min]  bot_lb [THEN sup_max]
  top_ub [THEN inf_min]  top_ub [THEN sup_max]
  bot_lb [THEN inf_min [THEN inf_com [THEN trans]]]  
  bot_lb [THEN sup_max [THEN sup_com [THEN trans]]]
  top_ub [THEN inf_min [THEN inf_com [THEN trans]]]  
  top_ub [THEN sup_max [THEN sup_com [THEN trans]]]

section {* Complete lattices *}

text {*

A complete lattice is one for which every collection of elements has an
infimum (supremum).

*}

class clat = blat +

fixes
  Inf :: "'a set \<rightarrow> 'a" and
  Sup :: "'a set \<rightarrow> 'a"

class clattice = clat + order +

assumes
  Inf_lb: "x \<in> P \<turnstile> Inf P \<le> x" and
  Inf_glb: "(\<And> x \<bullet> x \<in> P \<turnstile> z \<le> x) \<turnstile> z \<le> Inf P" and
  Sup_ub: "x \<in> P \<turnstile> x \<le> Sup P" and
  Sup_lub: "(\<And> x \<bullet> x \<in> P \<turnstile> x \<le> z) \<turnstile> Sup P \<le> z" and
  inf_Inf: "x && y = Inf {x, y}" and
  sup_Sup: "x || y = Sup {x, y}" and
  bot_Inf: "bot = Inf \<univ>" and
  top_Sup: "top = Sup \<univ>"

abbreviation
  lInf :: "'a set \<rightarrow> ('a::clattice)"
where
  "lInf \<defs> Inf"

abbreviation
  lSup :: "'a set \<rightarrow> ('a::clattice)"
where
  "lSup \<defs> Sup"

notation (xsymbols output)
  lInf ("\<Sqinter>") and
  lSup ("\<Squnion>")

syntax (xsymbols output)
  "_Lattice_Class\<ZZ>lInfs" :: "schematext \<rightarrow> logic" ("(1\<Sqinter>_)" 10)
  "_Lattice_Class\<ZZ>lSups" :: "schematext \<rightarrow> logic" ("(1\<Squnion>_)" 10)

notation (zed)
  lInf ("\<lInf>") and
  lSup ("\<lSup>")

syntax (xsymbols)
  "_Lattice_Class\<ZZ>lInfs" :: "schematext \<rightarrow> logic" ("(1\<lINF> _)" 10)
  "_Lattice_Class\<ZZ>lSups" :: "schematext \<rightarrow> logic" ("(1\<lSUP> _)" 10)

translations
  "_Lattice_Class\<ZZ>lInfs S" \<rightleftharpoons> "CONST lInf (_xHOL_Syntax\<ZZ>coll S)"
  "_Lattice_Class\<ZZ>lSups S" \<rightleftharpoons> "CONST lSup (_xHOL_Syntax\<ZZ>coll S)"

lemma Inf_glbI: 
    "\<^glbp>{:\<univ>:}{:(op \<le>):} X (\<lInf> X)"
  apply (rule order_class.is_glbI)
  apply (auto intro!: Inf_lb Inf_glb)
  done

lemma Sup_lubI: 
    "\<^lubp>{:\<univ>:}{:(op \<le>):} X (\<lSup> X)"
  apply (rule order_class.is_lubI)
  apply (auto intro!: Sup_ub Sup_lub)
  done

interpretation clattice_class_interpretation: Lattice_Locale.clattice "\<univ>-[('a::clattice)]" "(op <=)"
  apply (intro_locales)
  apply (auto intro!: exI Inf_glbI Sup_lubI simp add: Lattice_Locale.clattice_axioms_def Lattice_Locale.lattice_axioms_def)
  done  

instance
  clattice < lattice
  apply (intro_classes)
  apply (auto intro!: Inf_lb Inf_glb Sup_ub Sup_lub simp add: inf_Inf sup_Sup)
  done

lemma Inf_Meet:
  "\<^Meet>{:\<univ>-['a::clattice]:}{:op \<lle>:} = Inf"
  apply (rule ext)
  apply (rule clattice_class_interpretation.Meet_unique [symmetric])
  apply (auto intro: Inf_lb Inf_glb)
  done

lemma bot_Bottom:
    "\<^Bottom>{:\<univ>-['a::clattice]:}{:(op \<lle>):} = bot"
  by (simp add: Bottom_def bot_Inf Inf_Meet)

lemma Sup_Join:
  "\<^Join>{:\<univ>-['a::clattice]:}{:op \<lle>:} = Sup"
  apply (rule ext)
  apply (rule clattice_class_interpretation.Join_unique [symmetric])
  apply (auto intro: Sup_ub Sup_lub)
  done

lemma top_Top:
    "\<^Top>{:\<univ>-['a::clattice]:}{:(op \<lle>):} = top"
  by (simp add: Top_def top_Sup Sup_Join)

theorem clattice_classI:
  assumes 
    a1: "\<^clattice>{:\<univ>-[('a::{clat, order})]:}{:(op <=):}" and
    a2: "\<And> x y \<bullet> x && y = x \<^meet>{:\<univ>-[('a::{order, clat})]:}{:(op <=):} y" and
    a3: "\<And> x y \<bullet> x || y = x \<^join>{:\<univ>-[('a::{order, clat})]:}{:(op <=):} y" and
    a4: "\<And> X \<bullet> Inf X = \<^Meet>{:\<univ>-[('a::{order, clat})]:}{:(op <=):} X" and
    a5: "\<And> X \<bullet> Sup X = \<^Join>{:\<univ>-[('a::{order, clat})]:}{:(op <=):} X" and
    a6: "\<And> X \<bullet> bot = \<^Meet>{:\<univ>-[('a::{order, clat})]:}{:(op <=):} \<univ>" and
    a7: "\<And> X \<bullet> top = \<^Join>{:\<univ>-[('a::{order, clat})]:}{:(op <=):} \<univ>"
  shows 
      "OFCLASS('a::{clat, order}, clattice_class)"
  apply (intro_classes)
  using a1 a2 a3 a4 a5 a6 a7
  apply (auto intro!: clattice.Meet_lbD [OF a1] clattice.Join_ubD [OF a1] clattice.Meet_glbD [OF a1] clattice.Join_lubD [OF a1] clattice.meet_Meet [OF a1] clattice.join_Join [OF a1])
  done

lemma clattice_classD:
    "\<^clattice>{:\<univ>-[('a::clattice)]:}{:(op <=):}"
  apply (rule order_class.clatticeI)
  apply (auto intro!: exI Inf_glbI Sup_lubI)
  done

lemma InfE:
  assumes 
    a1: 
      "\<lbrakk> 
        (\<And> x \<bullet> x \<in> P \<turnstile> \<lInf> P \<lle> x);
        (\<And> y \<bullet> (\<forall> x | x \<in> P \<bullet> y \<lle> x) \<turnstile> y \<lle> (\<lInf> P))
      \<rbrakk> \<turnstile> R"
  shows 
      "R"
  apply (rule a1)
  apply (auto intro: 
    order_class.is_glbD1' [OF Inf_glbI]
    order_class.is_glbD2' [OF Inf_glbI])
  done

lemma SupE:
  assumes 
    a1: 
      "\<lbrakk> 
        (\<And> x \<bullet> x \<in> P \<turnstile> x \<lle> \<lSup> P);
        (\<And> y \<bullet> ( \<forall> x | x \<in> P \<bullet> x \<lle> y) \<turnstile> (\<lSup> P) \<lle> y)
      \<rbrakk> \<turnstile> R"
  shows 
      "R"
  apply (rule a1)
  apply (auto intro: 
    order_class.is_lubD1' [OF Sup_lubI]
    order_class.is_lubD2' [OF Sup_lubI])
  done

instance
  clattice < boundlattice
  apply (intro_classes)
  apply (auto simp add: bot_Inf top_Sup Inf_lb Sup_ub)
  done

lemma Inf_sub:
  assumes 
    a1: "P \<subseteq> Q"
  shows 
      "\<lInf> Q \<lle> \<lInf> P"
  apply (rule Inf_glb)
  apply (rule Inf_lb)
  using a1
  apply (auto)
  done

lemma QTInf_dom:
  assumes
    a1: "(\<forall> x | P x \<bullet> f x \<lle> g x)"
  shows
    "(\<lINF> x | P x \<bullet> f x) \<lle> (\<lINF> x | P x \<bullet> g x)"
proof (rule Inf_glb, auto)
  fix x 
  assume 
    a2: "P x"
  have 
      "(\<lINF> x | P x \<bullet> f x) 
      \<lle> f x"
    by (rule Inf_lb, auto intro!: exI [of _ x] a2)
  also have "\<dots> 
      \<lle> g x"
    by (rule a1 [rule_format], rule a2)
  finally show 
      " (\<lINF> x | P x \<bullet> f x) \<lle> g x" 
    by (this)
qed

lemma QInf_dom:
  assumes 
    a1: "(\<forall> x \<bullet> f x \<lle> g x)"
  shows
      "(\<lINF> x \<bullet> f x) \<lle> (\<lINF> x \<bullet> g x)"
proof (rule Inf_glb, auto)
  fix x
  have 
      "(\<lINF> x \<bullet> f x) 
      \<lle> f x"
    by (rule Inf_lb, auto intro!: exI [of _ x])
  also have "\<dots> 
      \<lle> g x"
    by (rule a1 [rule_format])
  finally show 
        "(\<lINF> x \<bullet> f x) \<lle> g x"
    by (this)
qed
   
lemma Inf_eq:
    "\<lbrakk> 
      (\<And> x \<bullet> x \<in> P \<turnstile> z \<lle> x);
      (\<And> y \<bullet> (\<forall> x | x \<in> P \<bullet> y \<lle> x) \<turnstile> y \<lle> z)
    \<rbrakk> \<turnstile> (\<lInf>P) = z"
  apply (rule order_class.glb_unique [OF _ Inf_glbI])
  apply (auto intro!: order_class.is_glbI)
  done

lemma Min_eq:
    "\<lbrakk> \<And> x \<bullet> x \<in> P \<turnstile> z \<lle> x; z \<in> P \<rbrakk> \<turnstile> (\<lInf>P) = z"
  apply (rule Inf_eq)
  apply (auto intro: order_antisym)
  done

lemma inf_Inf:
    "x \<linf> y = \<lInf> {x,y}"
  by (rule inf_eq, auto intro: Inf_lb Inf_glb)

lemma Inf_inf:
    "(\<lInf> (P::('a::clattice) set)) \<linf> (\<lInf> Q) = \<lInf> (P \<union> Q)"
proof (rule Inf_eq [THEN sym], auto simp add: Ball_def)
  fix 
    x::'a 
  assume 
    a1: "x \<in> P"
  show 
      "(\<lInf> P) \<linf> (\<lInf> Q) \<lle> x"
    by (rule a1 [THEN Inf_lb [THEN inf_mono1 [THEN order_trans]]], rule inf_lb1)
next
  fix 
    x::'a 
  assume 
    a1: "x \<in> Q"
  show 
      "(\<lInf> P) \<linf> (\<lInf> Q) \<lle> x"
    by (rule a1 [THEN Inf_lb [THEN inf_mono2 [THEN order_trans]]], rule inf_lb2)
next
  fix 
    y::'a
  assume 
    a1: "\<forall> x::'a \<bullet> (x \<in> P \<Rightarrow> y \<lle> x) \<and> (x \<in> Q \<Rightarrow> y \<le> x)"
  show 
      "y \<lle> (\<lInf> P) \<linf> (\<lInf> Q)"
  proof (intro inf_glb Inf_glb)
    fix 
      x::'a 
    assume 
      b1: "x \<in> P"
    show 
        "y \<le> x"
      by (insert a1, elim allE [of _ x], elim conjE, simp add: b1)
  next
    fix 
      x::'a 
    assume 
      b1: "x \<in> Q"
    show 
        "y \<le> x"
      by (insert a1, elim allE [of _ x], elim conjE, simp add: b1)
  qed
qed

lemma Inf_Inf:
    "(\<lINF> x | P x \<bullet> (\<lINF> y | Q x y \<bullet> f x y)) = (\<lINF> x y | P x \<and> Q x y \<bullet> f x y)" 
  apply (rule Inf_eq)
  apply (auto)
  apply (rule Inf_sub)
  apply (simp add: subset_def)
  apply (fast)
  apply (rule Inf_glb)
  apply (auto)
  apply (elim allE impE)
  apply (assumption)
  apply (rule order_trans)
  apply (assumption)
  apply (rule Inf_lb)
  apply (auto)
  done

lemma Inf_empty:
    "\<lInf> \<emptyset> = \<ltop>"
  by (rule Inf_eq, auto, rule top_ub)

lemma Inf_singleton:
    "\<lInf> {x} = x"
  by (rule Inf_eq, auto)

lemma Inf_top_unique:
    "\<lInf> X = \<ltop> \<Leftrightarrow> X = {\<ltop>} \<or> X = \<emptyset>"
proof (rule iffI)
  assume 
    b1: "\<lInf> X = \<ltop>"
  have 
      "(\<forall> x | x \<in> X \<bullet> \<ltop> \<lle> x)"
    by (auto simp add: b1 [symmetric] Inf_lb)
  then have 
      "(\<forall> x | x \<in> X \<bullet> x = \<ltop>)"
    by (auto simp add: top_max)
  then show 
      "X = {\<ltop>} \<or> X = \<emptyset>"
    by (auto)
qed (auto simp add: Inf_empty Inf_singleton)

lemma Inf_collect:
    "\<lInf> {x::'a::clattice, \<lInf> P} = \<lInf> ({x} \<union> P)"
proof (rule Inf_eq, safe, auto)
  show 
      "\<lInf> (insert x P) \<lle> x"
    by (rule Inf_lb, simp)
  show 
      "\<lInf> (insert x P) \<lle> \<lInf> P"
    by (rule Inf_glb, rule Inf_lb, simp)
  fix 
    y::'a 
  assume 
    a1: "y \<lle> x" "y \<lle> \<lInf> P"
  show 
      "y \<lle> \<lInf> (insert x P)"
  proof (rule Inf_glb, auto)
    from a1 show "
        y \<lle> x" 
      by (safe)
    fix 
      z::'a  
    assume  
      b1: "z \<in> P"
    from a1 have 
        "y 
        \<lle> \<lInf>P" 
      by (auto)
    also have "\<dots> 
        \<lle> z" 
      by (rule b1 [THEN Inf_lb])
    finally show 
        "y \<lle> z"
      by (this)
  qed
qed

lemmas fin_Inf = inf_Inf Inf_inf Inf_singleton Inf_collect ins_comm

lemma Inf_inf':
    "(\<lINF> x | P x \<bullet> f x \<linf> g x) = \<lInf>({ x | P x \<bullet> f x } \<union> { x | P x \<bullet> g x})"
  apply (rule Inf_eq)
  apply (simp_all)
  apply (msafe(inference))
  apply (simp add: Inf_inf [symmetric])
proof -
  fix x
  assume
    b1: "P x"
  then have
    b2a: "f x \<in> { x | P x \<bullet> f x }" and
    b2b: "g x \<in> { x | P x \<bullet> g x }"
    by (auto)
  show 
      "(\<lINF> x | P x \<bullet> f x) \<linf> (\<lINF> x | P x \<bullet> g x) \<lle> f x \<linf> g x"
    apply (rule order_trans)
    apply (rule inf_mono1)
    apply (rule Inf_lb [OF b2a])
    apply (rule order_trans)
    apply (rule inf_mono2)
    apply (rule Inf_lb [OF b2b])
    apply (rule order_refl)
    done
next
  fix a
  assume
    b1: "(\<forall> x \<bullet> P x \<Rightarrow> a \<lle> f x \<linf> g x)"
  then have 
    "(\<forall> x \<bullet> P x \<Rightarrow> a \<lle> f x \<and> a \<lle> g x)"
    apply (auto)
    apply (rule order_trans [OF _ inf_lb1])
    apply (fast)
    apply (rule order_trans [OF _ inf_lb2])
    apply (fast)
    done
  then show 
      "a \<lle> \<lInf>({ x | P x \<bullet> f x } \<union> { x | P x \<bullet> g x })"
    apply (intro Inf_glb)
    apply (auto)
    done
qed

lemma Sup_sub:
  assumes 
    a1: "P \<subseteq> Q"
  shows 
      "\<lSup> P \<lle> \<lSup> Q"
  apply (rule Sup_lub)
  apply (rule Sup_ub)
  using a1
  apply (auto)
  done

lemma QTSup_dom:
    "(\<forall> x | P x \<bullet> f x \<lle> g x) 
    \<turnstile> (\<lSUP> x | P x \<bullet> f x) \<lle> (\<lSUP> x | P x \<bullet> g x)"
proof (rule Sup_lub, auto)
  assume 
    a1: "(\<forall> x | P x \<bullet> f x \<lle> g x)"
  fix x 
  assume 
    a2: "P x"
  have 
      "f x 
      \<lle> g x"
    by (rule a1 [rule_format], rule a2)
  also have "\<dots> 
      \<lle> (\<lSUP> x | P x \<bullet> g x)"
    by (rule Sup_ub, auto intro!: exI [of _ x] a2)
  finally show 
      "f x  \<lle> (\<lSUP> x | P x \<bullet>g x)"
    by (this)
qed

lemma QSup_dom:
    "(\<forall> x \<bullet> f x \<lle> g x) 
    \<turnstile> (\<lSUP> x \<bullet> f x) \<lle> (\<lSUP> x \<bullet> g x)"
proof (rule Sup_lub, auto)
  assume 
    a1: "(\<forall> x \<bullet> f x \<lle> g x)"
  fix x 
  have 
      "f x 
      \<lle> g x"
    by (rule a1 [rule_format])
  also have "\<dots> 
      \<lle> (\<lSUP> x \<bullet> g x)"
    by (rule Sup_ub, auto intro!: exI [of _ x])
  finally show 
      "f x  \<lle> (\<lSUP> x \<bullet> g x)"
    by (this)
qed

lemma Sup_eq:
    "\<lbrakk> 
      (\<And> x \<bullet> x \<in> P \<turnstile> x \<lle> z);
      (\<And> y \<bullet> (\<forall> x | x \<in> P \<bullet> x \<lle> y) \<turnstile> z \<lle> y)
    \<rbrakk> \<turnstile> (\<lSup>P) = z"
  apply (rule order_class.lub_unique [OF _ Sup_lubI])
  apply (auto intro!: order_class.is_lubI)
  done
    
lemma Max_eq:
    "\<lbrakk> \<And> x \<bullet> x \<in> P \<turnstile> x \<lle> z; z \<in> P \<rbrakk> \<turnstile> (\<lSup>P) = z"
  apply (rule Sup_eq)
  apply (auto intro: order_antisym)
  done

lemma sup_Sup:
    "x \<lsup> y = \<lSup> {x,y}"
  by (rule sup_eq, auto intro: Sup_ub Sup_lub)

lemma Sup_sup:
    "(\<lSup> (P::('a::clattice) set)) \<lsup> (\<lSup> Q) = \<lSup> (P \<union> Q)"
proof (rule Sup_eq [THEN sym], auto)
  fix 
    x::'a 
  assume 
    a1: "x \<in> P"
  show 
      "x \<lle> (\<lSup> P) \<lsup> (\<lSup> Q)"
    by (rule a1 [THEN Sup_ub [THEN order_trans]], rule sup_ub1)
next
  fix 
    x::'a 
  assume 
    a1: "x \<in> Q"
  show 
      "x \<lle> (\<lSup> P) \<lsup> (\<lSup> Q)"
    by (rule a1 [THEN Sup_ub [THEN order_trans]], rule sup_ub2)
next
  fix 
    y::'a
  assume 
    a1: "(\<forall> x::'a \<bullet> (x \<in> P \<Rightarrow> x \<lle> y) \<and> (x \<in> Q \<Rightarrow> x \<le> y))"
  show 
      "(\<lSup> P) \<lsup> (\<lSup> Q) \<lle> y"
  proof (intro sup_lub Sup_lub)
    fix 
      x::'a 
    assume 
      b1: "x \<in> P"
    show 
        "x \<le> y"
      by (insert a1, elim allE [of _ x], elim conjE, simp add: b1)
  next
    fix 
      x::'a 
    assume 
      b1: "x \<in> Q"
    show 
        "x \<le> y"
      by (insert a1, elim allE [of _ x], elim conjE, simp add: b1)
  qed
qed

lemma Sup_Sup:
    "(\<lSUP> x | P x \<bullet> (\<lSUP> y | Q x y \<bullet> f x y)) = (\<lSUP> x y | P x \<and> Q x y \<bullet> f x y)" 
  apply (rule Sup_eq)
  apply (auto)
  apply (rule Sup_sub)
  apply (simp add: subset_def)
  apply (fast)
  apply (rule Sup_lub)
  apply (auto)
  apply (elim allE impE)
  apply (assumption)
  apply (rule order_trans)
  defer 1
  apply (assumption)
  apply (rule Sup_ub)
  apply (auto)
  done

lemma Sup_empty:
    "\<lSup> \<emptyset> = \<lbot>"
  by (rule Sup_eq, auto, rule bot_lb)

lemma Sup_singleton:
    "\<lSup> {x} = x"
  by (rule Sup_eq, auto)

lemma Sup_bot_unique:
    "\<lSup> X = \<lbot> \<Leftrightarrow> X = {\<lbot>} \<or> X = \<emptyset>"
proof (rule iffI)
  assume 
    b1: "\<lSup> X = \<lbot>"
  have 
      "(\<forall> x | x \<in> X \<bullet> x \<lle> \<lbot>)"
    by (auto simp add: b1 [symmetric] Sup_ub)
  then have 
      "(\<forall> x | x \<in> X \<bullet> x = \<lbot>)"
    by (auto simp add: bot_min)
  then show 
      "X = {\<lbot>} \<or> X = \<emptyset>"
    by (auto)
qed (auto simp add: Sup_empty Sup_singleton)

lemma Sup_collect:
    "\<lSup> {x::'a::clattice, \<lSup> P} = \<lSup> ({x} \<union> P)"
proof (rule Sup_eq, safe, auto)
  show 
      "x \<lle> \<lSup> (insert x P)"
    by (rule Sup_ub, simp)
  show 
      "\<lSup> P \<lle> \<lSup> (insert x P)"
    by (rule Sup_lub, rule Sup_ub, simp)
  fix 
    y::'a 
  assume 
    a1: "x \<lle> y" "\<lSup> P \<lle> y"
  show 
      "\<lSup> (insert x P) \<lle> y"
  proof (rule Sup_lub, auto)
    from a1 show 
        "x \<lle> y" 
      by (auto)
    fix 
      z::'a 
    assume 
      b1: "z \<in> P"
    then have 
        "z 
        \<lle> \<lSup> P" 
      by (rule Sup_ub)
    also from a1 have "\<dots>
        \<lle> y" 
      by (auto)
    finally show 
        "z \<lle> y" 
      by (this)
  qed
qed

lemma constant_sup_Sup:
    "\<lSup> {x \<bullet> b\<lsup>(c x)} = b\<lsup>(\<lSup>{x \<bullet> (c x)})"
  apply (rule Sup_eq,auto)
  apply (rule sup_mono2)
  apply (rule Sup_ub,auto)
proof -
  fix y
  assume 
    Aa1: "\<forall> x \<bullet> b \<lsup> (c x) \<le> y"
  have 
    Ra1: "b \<le> y"
    apply (rule order_trans)
    apply (rule sup_ub1)
    apply (rule Aa1 [rule_format])
    done
  have 
    Ra2: "(\<forall> x \<bullet> c x \<le> y)"
    apply (rule allI)
    apply (rule order_trans)
    apply (rule sup_ub2)
    apply (rule Aa1 [rule_format])
    done
  from Ra1 Ra2 show
      "b \<lsup> (\<lSUP> x \<bullet> c x) \<le> y"
    apply (intro sup_lub, simp)
    apply (intro Sup_lub, auto)
  done
qed

lemmas fin_Sup = sup_Sup Sup_sup Sup_singleton Sup_collect ins_comm

lemma Sup_sup':
    "(\<lSUP> x | P x \<bullet> f x \<lsup> g x) = \<lSup>({ x | P x \<bullet> f x } \<union> { x | P x \<bullet> g x})"
  apply (rule Sup_eq)
  apply (simp_all)
  apply (msafe(inference))
  apply (simp add: Sup_sup [symmetric])
proof -
  fix x
  assume
    b1: "P x"
  then have
    b2a: "f x \<in> { x | P x \<bullet> f x }" and
    b2b: "g x \<in> { x | P x \<bullet> g x }"
    by (auto)
  show 
      "f x \<lsup> g x \<lle> (\<lSUP> x | P x \<bullet> f x) \<lsup> (\<lSUP> x | P x \<bullet> g x)"
    apply (rule order_trans)
    apply (rule sup_mono1)
    apply (rule Sup_ub [OF b2a])
    apply (rule order_trans)
    apply (rule sup_mono2)
    apply (rule Sup_ub [OF b2b])
    apply (rule order_refl)
    done
next
  fix a
  assume
    b1: "(\<forall> x \<bullet> P x \<Rightarrow> f x \<lsup> g x \<lle> a)"
  then have 
    "(\<forall> x \<bullet> P x \<Rightarrow> f x \<lle> a \<and> g x \<lle> a)"
    apply (auto)
    apply (rule order_trans)
    apply (rule sup_ub1)
    apply (fast)
    apply (rule order_trans)
    apply (rule sup_ub2)
    apply (fast)
    done
  then show 
      "\<lSup>({ x | P x \<bullet> f x } \<union> { x | P x \<bullet> g x }) \<lle> a"
    apply (intro Sup_lub)
    apply (auto)
    done
qed

lemma Sup_bot_rem:
  "\<lSup> (A - {\<lbot>}) = \<lSup> A"
proof (cases "\<lbot> \<in> A")
  assume 
      "\<lbot> \<in> A"
  then have 
    b1: "{\<lbot>} \<union> (A - {\<lbot>}) = A"
    by (auto)
  have 
      "\<lSup> (A - {\<lbot>}) 
      = \<lbot> \<lsup> (\<lSup>(A - {\<lbot>}))"
    by (simp add: lat_bounds)
  also have "\<dots> 
      = (\<lSup>{\<lbot>}) \<lsup> (\<lSup>(A - {\<lbot>}))"
    by (simp add: Sup_singleton)
  also have "\<dots> 
      = \<lSup> ({\<lbot>} \<union> (A - {\<lbot>}))"
    by (simp add: Sup_sup)
  also from b1 have "\<dots> 
      = \<lSup> A"
    by (simp)
  finally show 
        "?thesis"
    by (this)
next
  assume 
      "\<lbot> \<notin> A"
  then have 
      "A - {\<lbot>} = A"
    by (auto)
  then show 
      "?thesis"
    by (simp)
qed

lemma Inf_top_rem:
    "\<lInf> (A - {\<ltop>}) = \<lInf> A"
proof (cases "\<ltop> \<in> A")
  assume 
      "\<ltop> \<in> A"
  then have 
    b1: "{\<ltop>} \<union> (A - {\<ltop>}) = A"
    by (auto)
  have 
      "\<lInf> (A - {\<ltop>}) 
      = \<ltop> \<linf> (\<lInf>(A - {\<ltop>}))"
    by (simp add: lat_bounds)
  also have "\<dots> 
      = (\<lInf>{\<ltop>}) \<linf> (\<lInf>(A - {\<ltop>}))"
    by (simp add: Inf_singleton)
  also have "\<dots> 
      = \<lInf> ({\<ltop>} \<union> (A - {\<ltop>}))"
    by (simp add: Inf_inf)
  also from b1 have "\<dots> 
      = \<lInf> A"
    by (simp)
  finally show 
      "?thesis"
    by (this)
next
  assume 
      "\<ltop> \<notin> A"
  then have 
      "A - {\<ltop>} = A"
    by (auto)
  then show 
      "?thesis"
    by (simp)
qed

lemma clattice_class_defaultD:
  fixes
    X :: "('a::clattice) set"
  assumes 
    a1: "X \<noteq> \<emptyset>" and
    a2: "\<And> P \<bullet> \<lbrakk> P \<noteq> \<emptyset>; P \<subseteq> X \<rbrakk> \<turnstile> \<lInf> P \<in> X" and 
    a3: "\<And> P \<bullet> \<lbrakk> P \<noteq> \<emptyset>; P \<subseteq> X \<rbrakk> \<turnstile> \<lSup> P \<in> X"
  shows "\<^clattice>{:X:}{:(default_order X):}"
proof -
  from a1 interpret 
    def_po: po_carrier X
    by (unfold_locales)
  from def_po.partial_order show
      "\<^clattice>{:X:}{:(default_order X):}"
  proof (unfold_locales)
    fix 
      P 
    assume 
      b1: "P \<subseteq> X"
    show 
        "(\<exists> x \<bullet> \<^glbp>{:X:}{:(default_order X):} P x)"
    proof (cases "P = \<emptyset>")
      assume 
        c1: "P = \<emptyset>"
      then show 
          ?thesis
        apply (witness "\<lSup> X")
        apply (rule def_po.is_glbI)
        apply (auto intro!: Sup_ub Sup_lub a3 [OF a1] simp add: default_order_def subset_order_def rel2op_def op2rel_def)
        done
    next
      assume 
        c1: "P \<noteq> \<emptyset>"
      with b1 show 
          ?thesis
        apply (witness "\<lInf> P")
        apply (rule def_po.is_glbI)
        apply (auto intro!: Inf_lb Inf_glb simp add: default_order_def subset_order_def rel2op_def op2rel_def a2)
        done
    qed
    show 
        "(\<exists> x \<bullet> \<^lubp>{:X:}{:(default_order X):} P x)"
    proof (cases "P = \<emptyset>")
      assume 
        c1: "P = \<emptyset>"
      then show 
          ?thesis
        apply (witness "\<lInf> X")
        apply (rule def_po.is_lubI)
        apply (auto intro!:Inf_lb Inf_glb a2 [OF a1] simp add: default_order_def subset_order_def rel2op_def op2rel_def)
        done
    next
      assume 
        c1: "P \<noteq> \<emptyset>"
      with b1 show 
          ?thesis
        apply (witness "\<lSup> P")
        apply (rule def_po.is_lubI)
        apply (auto intro!: Sup_ub Sup_lub simp add: default_order_def subset_order_def rel2op_def op2rel_def a3)
        done
    qed
  qed
qed

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> P x \<turnstile> f x = g x) \<turnstile> (\<lSUP> x | P x \<bullet> f x) = (\<lSUP> x | P x \<bullet> g x)"
  apply (rule arg_cong [of _ _ "Sup"])
  apply (mauto(wind))
  done

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> P x \<turnstile> f x = g x) \<turnstile> (\<lINF> x | P x \<bullet> f x) = (\<lINF> x | P x \<bullet> g x)"
  apply (rule arg_cong [of _ _ "Inf"])
  apply (mauto(wind))
  done

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> f x = g x) \<turnstile> (\<lSUP> x \<bullet> f x) = (\<lSUP> x \<bullet> g x)"
  apply (rule arg_cong [of _ _ "Sup"])
  apply (mauto(wind))
  done

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> f x = g x) \<turnstile> (\<lINF> x \<bullet> f x) = (\<lINF> x \<bullet> g x)"
  apply (rule arg_cong [of _ _ "Inf"])
  apply (mauto(wind))
  done

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> P x \<turnstile> f x \<lle> g x) 
    \<turnstile> (\<lSUP> x | P x \<bullet> f x) \<lle> (\<lSUP> x | P x \<bullet> g x)"
  apply (rule QTSup_dom)
  apply (auto)
  done

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> P x \<turnstile> f x \<lge> g x) 
    \<turnstile> (\<lSUP> x | P x \<bullet> f x) \<lge> (\<lSUP> x | P x \<bullet> g x)"
  apply (unfold ge_def)
  apply (rule QTSup_dom)
  apply (auto)
  done

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> P x \<turnstile> f x \<lle> g x) 
    \<turnstile> (\<lINF> x | P x \<bullet> f x) \<lle> (\<lINF> x | P x \<bullet> g x)"
  apply (rule QTInf_dom)
  apply (auto)
  done

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> P x \<turnstile> f x \<lge> g x) 
    \<turnstile> (\<lINF> x | P x \<bullet> f x) \<lge> (\<lINF> x | P x \<bullet> g x)"
  apply (unfold ge_def)
  apply (rule QTInf_dom)
  apply (auto)
  done

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> f x \<lle> g x) 
    \<turnstile> (\<lSUP> x \<bullet> f x) \<lle> (\<lSUP> x \<bullet> g x)"
  apply (rule QSup_dom)
  apply (auto)
  done

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> f x \<lge> g x) 
    \<turnstile> (\<lSUP> x \<bullet> f x) \<lge> (\<lSUP> x \<bullet> g x)"
  apply (unfold ge_def)
  apply (rule QSup_dom)
  apply (auto)
  done

lemma [mintro!(wind)]:
  "(\<And> x \<bullet> f x \<lle> g x) 
  \<turnstile> (\<lINF> x \<bullet> f x) \<lle> (\<lINF> x \<bullet> g x)"
  apply (rule QInf_dom)
  apply (auto)
  done

lemma [mintro!(wind)]:
    "(\<And> x \<bullet> f x \<lge> g x) 
    \<turnstile> (\<lINF> x \<bullet> f x) \<lge> (\<lINF> x \<bullet> g x)"
  apply (unfold ge_def)
  apply (rule QInf_dom)
  apply (auto)
  done

text{*

It is convenient to have a ``Sup indexed over type''.  Moreover, because
controlling the print translation of the syntax forms is difficult, we 
will introduce a const for this case.

*}


definition
  ISup :: "('x \<rightarrow> ('a::clattice)) \<rightarrow> 'a"
where
  ISup_def: "ISup f \<defs> (\<lSup> { x \<bullet> f x })"

syntax ("" output)
  "_Lattice_Class\<ZZ>ISup" :: "[pttrns, logic] \<rightarrow> logic" ("d|| _ @/ [ _ ]" [0,0] 10)

syntax (xsymbols output)
  "_Lattice_Class\<ZZ>ISup" :: "[pttrns, logic] \<rightarrow> logic" ("\<Lambda> _ \<bullet>/ [ _ ]" [0,0] 10)

syntax (zed)
  "_Lattice_Class\<ZZ>ISup" :: "[pttrns, logic] \<rightarrow> logic" ("\<ISup> _\<bullet>/ [ _ ]" [0,0] 10)

parse_translation {* [
  Syntax_Trans.mk_binder_tr("_Lattice_Class\<ZZ>ISup","\<^const>Lattice_Class.ISup")
] *}

print_translation {* [
  Syntax_Trans.mk_binder_tr'("\<^const>Lattice_Class.ISup","_Lattice_Class\<ZZ>ISup") 
] *}

lemma sett_range:
  "{ x \<bullet> f x } = range f"
  by (auto)

lemma ISup_lubI: 
    "\<^lubp>{:\<univ>:}{:(op \<le>):} (range f) (\<ISup> x \<bullet> [f x])"
  by (auto simp add: ISup_def Sup_lubI sett_range)

lemma ISupE:
  assumes 
    a1: 
      "(\<lbrakk> 
        (\<And> x \<bullet> x \<in> (range f) \<turnstile> x \<lle> (\<ISup> i \<bullet> [f i]));
        (\<And> y \<bullet> ( \<forall> x | x \<in> (range f) \<bullet> x \<lle> y) \<turnstile> (\<ISup> i \<bullet> [f i]) \<lle> y)
      \<rbrakk> \<turnstile> R)"
  shows 
      "R"
  apply (rule SupE [where ?P = "range f"])
  apply (rule a1)
  apply (simp add: ISup_def sett_range)+
  done

lemma ISupE':
  assumes 
    a1: 
      "\<lbrakk> 
        (\<And> x \<bullet> f x \<lle> (\<ISup> i \<bullet> [f i]));
        (\<And> y \<bullet> (\<forall> x \<bullet> f x \<lle> y) \<turnstile> (\<ISup> i \<bullet> [f i]) \<lle> y)
      \<rbrakk> \<turnstile> R"
  shows 
      "R"
  apply (rule ISupE [where ?f = "f"])
  apply (rule a1)
  apply (auto simp add: sett_range)+
  done

lemma ISup_ub:
    "x \<in> (range f) \<turnstile> x \<lle> (\<ISup> i \<bullet> [f i])"
  apply (simp add: ISup_def sett_range)
  apply (rule Sup_ub, assumption)
  done

lemma ISup_ub':
    "f x \<lle> (\<ISup> i \<bullet> [f i])"
  by (rule ISup_ub, simp add: sett_range)

lemma ISup_lub:
    "(\<And> x \<bullet> x \<in> (range f) \<turnstile> x \<lle> z) \<turnstile> (\<ISup> i \<bullet> [f i]) \<lle> z"
  by (rule ISupE, auto)

lemma ISup_lub':
    "(\<And> x \<bullet> f x \<lle> z) \<turnstile> (\<ISup> i \<bullet> [f i]) \<lle> z"
  by (rule ISup_lub, auto)

lemma ISup_dom:
  assumes 
    a1: "(\<forall> x \<bullet> f x \<lle> g x)"
  shows
      "(\<ISup> x \<bullet> [f x]) \<lle> (\<ISup> x \<bullet> [g x])"
proof (rule ISup_lub, auto)
  fix i
  have 
      "f i 
      \<lle> g i"
    by (rule a1 [rule_format])
  also have "\<dots> 
      \<lle> (ISup g)"
    by (rule ISup_ub, auto)
  finally show 
      "f i \<lle> (ISup g)" 
    by (this)
qed

lemma ISup_eq:
    "\<lbrakk> 
      (\<And> x \<bullet> f x \<lle> z);
      (\<And> y \<bullet> (\<forall> x \<bullet> f x \<lle> y) \<turnstile> z \<lle> y)
    \<rbrakk> \<turnstile> (\<ISup> x \<bullet> [f x]) = z"
  apply (simp add: ISup_def)
  apply (rule Sup_eq, auto)
  done
    
lemma IMax_eq:
    "(\<And> x \<bullet> f x \<lle> f z) \<turnstile> (\<ISup> x \<bullet> [f x]) = f z"
  apply (simp add: ISup_def)
  apply (rule Max_eq, auto)
  done

section {* Distributive lattices *}

text {*

If meet distributes through join we say that the lattice is
distributive.

*}

class dlattice = Lattice_Class.lattice +

assumes
  sup_dist: "x && (y || z) = (x && y) || (x && z)"

text {*

In a distributive lattice, join also distributes through meet.

*}

lemma inf_dist: 
    "(x::'a::dlattice) \<lsup> (y \<linf> z) = (x \<lsup> y) \<linf> (x \<lsup> z)"
proof -
  txt {*
    Following the reasoning of Davey~\cite[p 130]{Davey:Lattice}.
  *}
  have 
      "(x \<lsup> y) \<linf> (x \<lsup> z) 
      = ((x \<lsup> y) \<linf> x) \<lsup> ((x \<lsup> y) \<linf> z)"
    by (simp add: sup_dist)
  also have "\<dots> 
      = x \<lsup> (z \<linf> (x \<lsup> y))"
    by (simp add: inf_absorption inf_com)
  also have "\<dots> 
      = x \<lsup> ((z \<linf> x) \<lsup> (z \<linf> y))"
   by (simp add: sup_dist)
  also have "\<dots> 
      = (x \<lsup> (x \<linf> z)) \<lsup> (y \<linf> z)"
   by (simp add: sup_assoc inf_com)
  also have "\<dots> 
      = x \<lsup> (y \<linf> z)"
    by (simp add: sup_absorption)
  finally show 
      ?thesis 
    by (rule sym)
qed

section {* Boolean lattices *}

text {* 

A lattice complement is an inverse under both meet and join.
A distributive, bound lattice with complements is called a boolean lattice.

*}

class bllat = blat +

fixes
  "ocomp" :: "'a \<rightarrow> 'a" ("o~")

class boollattice = dlattice + boundlattice + bllat + 

assumes
  comp_inf: "x && (o~ x) = bot" and
  comp_sup: "x || (o~ x) = top"

abbreviation
  lcomp :: "('a::boollattice) \<rightarrow> 'a"
where
  "lcomp \<defs> ocomp"

notation (xsymbols)
  lcomp ("\<lcomp>_" [90] 90)

text {*

Complements are unique.

*}

lemma comp_eq:
  fixes 
    x::"'a::boollattice" and 
    cx::"'a::boollattice"
  assumes 
    a1: "x \<linf> cx = \<lbot>" and 
    a2: "x \<lsup> cx = \<ltop>"
  shows
      "\<lcomp>x = cx"
proof -
  have 
    a5: 
      "\<And>(y::'a) y' \<bullet> \<lbrakk> x \<lsup> y' = \<ltop>; x \<linf> y = \<lbot> \<rbrakk>
      \<turnstile> y \<lle> y'"
  proof -
    txt {*
    Following the reasoning of Davey~\cite[p 143]{Davey:Lattice}.
    *}
    fix
      y::'a and y'::'a
    assume 
      b1: "x \<lsup> y' = \<ltop>" and
      b2: "x \<linf> y = \<lbot>"
    have 
       "y 
       = y\<linf> \<ltop>" 
       by (simp add: top_ub [THEN inf_min])
    also have "\<dots> 
       = y \<linf> (x \<lsup> y')" 
      by (simp add: b1)
    also have "\<dots> 
       = (y \<linf> x) \<lsup> (y \<linf> y')" 
      by (simp add: sup_dist)
    also have "\<dots> 
       = (y \<linf> y')"
      by (simp add: inf_com b2 bot_lb [THEN sup_max])
    finally show 
        "y \<lle> y'" 
      by (rule sym [THEN min_inf])
  qed
  show 
      "\<lcomp>x = cx"
  proof (rule order_antisym)
    show 
        "\<lcomp>x \<lle> cx" 
      by (rule comp_inf [THEN a2 [THEN a5]])
    show 
        "cx \<lle> \<lcomp>x" 
      by (rule a1 [THEN comp_sup [THEN a5]])
  qed
qed

text {*

The top and bottom elements are complements.

*}

lemma comp_bot_conv:
    "\<lcomp>\<lbot> = \<ltop>"
proof (rule comp_eq)
  show 
      "\<lbot> \<linf> \<ltop> = \<lbot>" 
    by (rule bot_lb [THEN inf_min])
  show 
      "\<lbot> \<lsup> \<ltop> = \<ltop>"
    by (rule top_ub [THEN sup_max])
qed

lemma comp_top_conv:
    "\<lcomp>\<ltop> = \<lbot>"
proof (rule comp_eq)
  show 
      "\<ltop> \<linf> \<lbot> = \<lbot>"
    by (rule bot_lb [THEN inf_min [THEN inf_com [THEN trans]]])
  show 
      "\<ltop> \<lsup> \<lbot> = \<ltop>"
    by (rule top_ub [THEN sup_max [THEN sup_com [THEN trans]]])
qed

text {*

An element is the complement of its complement.

*}

lemma comp_involution:
    "\<lcomp>(\<lcomp>x) = x"
proof (rule comp_eq)
  show 
      "\<lcomp>x \<linf> x = \<lbot>"
    by (rule comp_inf [THEN inf_com [THEN trans]])
  show 
      "\<lcomp>x \<lsup> x = \<ltop>"
    by (rule comp_sup [THEN sup_com [THEN trans]])
qed

text {*

Complements satisfy de Morgan's laws.

*}

lemma inf_demorgan:
    "\<lcomp>(x \<linf> y) = \<lcomp>x \<lsup> \<lcomp>y"
proof (rule comp_eq)
  have 
      "(x \<linf> y) \<linf> (\<lcomp>x \<lsup> \<lcomp>y) 
      = (x \<linf> \<lcomp>x \<linf> y) \<lsup> (x \<linf> (y \<linf> \<lcomp>y))"
    by (simp add: lat_com_assoc sup_dist)
  also have "\<dots> 
      = \<lbot>" 
    by (simp add: comp_inf lat_bounds)
  finally show 
      "(x \<linf> y) \<linf> (\<lcomp>x \<lsup> \<lcomp>y) = \<lbot>" 
    by (this)
  have 
      "(x \<linf> y) \<lsup> (\<lcomp>x \<lsup> \<lcomp>y) 
      = (x \<lsup> \<lcomp>x \<lsup> \<lcomp>y) \<linf> (\<lcomp>x \<lsup> (y \<lsup>\<lcomp>y))"
    by (simp add: lat_com_assoc inf_dist)
  also have "\<dots> 
      = \<ltop>" 
    by (simp add: comp_sup lat_bounds)
  finally show 
      "(x \<linf> y) \<lsup> (\<lcomp>x \<lsup> \<lcomp>y) = \<ltop>" 
    by (this)
qed
  
lemma sup_demorgan:
    "\<lcomp>(x \<lsup> y) = \<lcomp>x \<linf> \<lcomp>y"
proof (rule comp_eq)
  have 
      "(x \<lsup> y) \<linf> (\<lcomp>x \<linf> \<lcomp>y) 
      = (x \<linf> \<lcomp>x \<linf> \<lcomp>y) \<lsup> (\<lcomp>x \<linf> (y \<linf> \<lcomp>y))"
    by (simp add: lat_com_assoc sup_dist)
  also have "\<dots> 
      = \<lbot>" 
    by (simp add: comp_inf lat_bounds)
  finally show 
      "(x \<lsup> y) \<linf> (\<lcomp>x \<linf> \<lcomp>y) = \<lbot>"
    by (this)
  have 
      "(x \<lsup> y) \<lsup> (\<lcomp>x \<linf> \<lcomp>y) 
      = (x \<lsup> \<lcomp>x \<lsup> y) \<linf> (x \<lsup> (y \<lsup> \<lcomp>y))"
    by (simp add: lat_com_assoc inf_dist)
  also have "\<dots> 
      = \<ltop>" 
    by (simp add: comp_sup lat_bounds)
  finally show 
      "(x \<lsup> y) \<lsup> (\<lcomp>x \<linf> \<lcomp>y) = \<ltop>"
    by (this)
qed

text {*

The complement operator is a bijection.

*}

lemma comp_bij:
    "(\<lcomp>x = \<lcomp>y) = (x = y)"
proof (rule iffI)
  assume 
    a1: "\<lcomp>x = \<lcomp>y"
  have 
    a2: "x = y \<Leftrightarrow> (\<lcomp>(\<lcomp>x) = \<lcomp>(\<lcomp>y))" 
    by (simp add: comp_involution)
  show 
      "x = y" 
    by (simp add: a1 a2)
next
  assume 
      "x = y" 
  then show 
      "\<lcomp>x = \<lcomp>y" 
    by (simp)
qed

text {*

The complement operator is a antimonotonic.

*}

lemma comp_antimono:
    "(\<lcomp>x \<lle> \<lcomp>y) = (y \<lle> x)"
proof -
  have 
      "(\<lcomp>x \<lle> \<lcomp>y) 
      \<Leftrightarrow> (\<lcomp>y = \<lcomp>x \<lsup> \<lcomp>y)"
    by (rule sup_correspondence [THEN sym])
  also have "\<dots> 
      \<Leftrightarrow> (\<lcomp>y = \<lcomp>(x \<linf> y))" 
    by (simp add: inf_demorgan)
  also have "\<dots> 
      \<Leftrightarrow> (y = (y \<linf> x))" 
    by (simp add: comp_bij lat_com_assoc)
  also have "\<dots> 
      \<Leftrightarrow> (y \<lle> x)"
    by (rule inf_correspondence)
  finally show 
      ?thesis 
    by (this)
qed

text {*

If a boolean lattice is complete, it satisfies distributed versions of
the de Morgan laws.

*}

lemma Inf_demorgan:
    "\<lcomp>(\<lInf>(P::(('a::{boollattice,clattice})set))) = (\<lSUP> x | x \<in> P \<bullet> \<lcomp>x)"
proof (rule Sup_eq [THEN sym], auto)
  fix 
    x::'a 
  assume 
    a1: "x \<in> P"
  show 
      "\<lcomp>x \<lle> \<lcomp>(\<lInf>P)"
    by (simp add: comp_antimono) (rule a1 [THEN Inf_lb])
next
  fix 
    x'::'a 
  assume 
    a1: "(\<forall> y' \<bullet> y' \<in> P \<Rightarrow> \<lcomp>y' \<lle> x')"
  have 
      "(\<lcomp>(\<lInf>P) \<lle> x') 
      = (\<lcomp>(\<lInf>P) \<lle> \<lcomp>(\<lcomp>x'))"
    by (simp add: comp_involution)
  also have "\<dots> 
      = (\<lcomp>x' \<lle> \<lInf>P)" 
    by (rule comp_antimono)
  finally have 
    a2: "(\<lcomp>(\<lInf>P) \<lle> x') = (\<lcomp>x' \<lle> \<lInf>P)"
    by (this)
  show 
      "\<lcomp>(\<lInf>P) \<lle> x'"
  proof (simp add: a2, rule Inf_glb)
    fix 
      y::'a 
    assume 
      b1: "y \<in> P"
    have 
      b2: "\<lcomp>y \<lle> x'"
      by (rule a1 [rule_format, OF b1])
    have 
        "(\<lcomp>x' \<lle> y) 
        = (\<lcomp>x' \<lle> \<lcomp>(\<lcomp>y))"
      by (simp add: comp_involution)
    also have "\<dots> 
        = (\<lcomp>y \<lle> x')" 
      by (rule comp_antimono)
    finally have 
      b3: "(\<lcomp>x' \<lle> y) = (\<lcomp>y \<lle> x')"
      by (this)
    show 
        "\<lcomp>x' \<lle> y" 
      by (simp add: b3 b2)
  qed
qed

lemma Sup_demorgan:
    "\<lcomp>(\<lSup>(P::(('a::{boollattice,clattice})set))) = (\<lINF> x | x \<in> P \<bullet> \<lcomp>x)"
  apply (rule comp_bij [THEN iffD1])
  apply (simp add: Inf_demorgan comp_involution)
  apply (rule arg_cong [of _ _ "lSup"])
  apply (auto simp add: comp_involution eind_comp)
  done







section {* Other lattice class relations *}

text {*

Finally we show that every linear order admits a lattice structure.

*}

class linlat = linorder + lat +

assumes
  inf_linorder_eq: "x && y = \<if> x \<le> y \<then> x \<else> y \<fi>" and
  sup_linorder_eq: "x || y = \<if> x \<le> y \<then> y \<else> x \<fi>"

instance
  linlat < lattice
  apply (intro_classes)
  apply (auto simp add: inf_linorder_eq sup_linorder_eq)
  done



end
