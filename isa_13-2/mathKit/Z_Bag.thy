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
  Z_Bag
 
imports 
  Z_Sequence
  Z_Bag_Chap

begin

section {* Ranged bags *}

text {*

Bags are collections that may be distinguished by the number of occurrrences
of a member. 
This makes them essentially natural number valued functions.
Spivey~\cite[p. 124]{Spivey:ZRef} introduces bags as non-zero valued functions
from a specified range set to the natural numbers.

*}

type_synonym 
  'a bagT = "'a \<leftrightarrow> \<arithmos>"

definition
  bag :: "'a set \<rightarrow> 'a bagT set"
where
  bag_def: "bag X \<defs> X \<zpfun> \<nat>\<subone>"

notation (zed)
  bag ("\<zbag>")


lemma in_bagI [mintro!(fspace)]:
  assumes a1: "b \<in> X \<zpfun> \<nat>\<subone>"
  shows "b \<in> \<zbag> X"
  using a1
  by (simp add: bag_def)

lemma in_bagE [melim!(fspace)]:
  assumes a1: "b \<in> \<zbag> X" "b \<in> X \<zpfun> \<nat>\<subone> \<turnstile> R"
  shows "R"
  using a1
  by (simp add: bag_def)

lemma bag_range:
  assumes a1: "b \<in> \<zbag> X" and a2: "x \<in> \<zdom> b"
  shows "b\<cdot>x \<in> \<nat>\<subone>"
proof -
  from a1 have b1: "functional b"
    by (msafe_no_assms(fspace))
  from a1 functional_ran [OF b1 a2]
  show "b\<cdot>x \<in> \<nat>\<subone>"
    apply (mauto(fspace))
    done
qed

lemma bag_ran:
  assumes a1: "b \<in> \<zbag> X" and a2: "(x \<mapsto> y) \<in> b"
  shows "y \<in> \<nat>\<subone>"
  apply (rule in_bagE [OF a1])
  apply (mauto(fspace))
  using a1 a2
  apply (auto simp add: Range_def Domain_def subset_def)
  done

lemma in_bag_functional:
  assumes a1: "b \<in> \<zbag> X"
  shows "functional b"
  using a1
  by (mauto(fspace))  

lemma in_bag_subset:
  assumes a1: "X \<subseteq> Y" "b \<in> \<zbag> X"
  shows "b \<in> \<zbag> Y"
  using a1
  by (mauto(fspace))

lemma in_bag_dom:
  assumes a1: "b \<in> \<zbag> X"
  shows "b \<in> \<zbag> (\<zdom> b)"
  using a1
  by (mauto(fspace))
  

section {* Bag count *}

text {*

The basic membership operator is the count operator which determines
the order of membership for a particular element.

*}

definition
  bhash :: "['a bagT, 'a] \<rightarrow> \<arithmos>"
where
  bhash_def: "bhash b \<defs> (\<^funK>{:0:})\<oporide>b"

notation (xsymbols)
  bhash ("_\<sharp>_" [1000, 999] 999)

lemma Z_bhash_def:
  "b\<sharp>x \<defs> ((\<olambda> x \<bullet> 0)\<oporide>b) x"
  by (simp add: bhash_def funK_def)

lemma mem_bhash:
  assumes 
    a1: "b \<in> \<zbag> X"
  shows
    "(x \<mapsto> y) \<in> b \<Leftrightarrow> y = b\<sharp>x \<and> b\<sharp>x \<in> \<nat>\<subone>"
  using a1
  apply (simp add: bhash_def op_oride_beta funK_def)
  apply (msafe(inference))
  apply (simp add: functional_beta in_bag_functional)
  apply (simp add: bag_range [OF a1])
  apply (simp add: functional_appl in_bag_functional)
  apply (auto simp add: zNats1_def)
  done

lemma Z_dom_bhash:
  assumes a1: "b \<in> \<zbag> X"
  shows "\<zdom> b = { x | b\<sharp>x \<in> \<nat>\<subone> }"
  apply (rule set_eqI)
  using a1
  apply (auto simp add: mem_bhash)
  done
 
lemma appl_bhash:
  assumes a1: "b \<in> \<zbag> X" "b\<sharp>x \<in> \<nat>\<subone>"
  shows "(x \<mapsto> b\<sharp>x) \<in> b"  
  using a1
  by (auto simp add: mem_bhash)

lemma bhash_beta:
  assumes a1: "b \<in> \<zbag> X" "(x \<mapsto> y) \<in> b"
  shows "b\<sharp>x = y"  
  using a1
  by (auto simp add: mem_bhash)

lemma bhash_range:
  assumes a1: "b \<in> \<zbag> X"
  shows "b\<sharp>x \<in> \<nat>"
  apply (simp add: bhash_def op_oride_beta funK_def)
  apply (msafe(inference))
  apply (rule subsetD [OF _ bag_range [OF a1]])
  apply (auto simp add: zNats1_def)
  done

lemma bhash_range2:
  assumes a1: "b \<in> \<zbag> X"
  shows "0 \<le> b\<sharp>x"
  apply (insert bhash_range [OF a1])
  apply (simp add: zInts_zNats_nonneg)
  done

lemma bhash_beta':
  assumes a1: "b \<in> \<zbag> X"
  shows "b\<sharp>x = \<if> x \<in> \<zdom> b \<then> b\<cdot>x \<else> 0 \<fi>"  
  using a1
  by (simp add: bhash_def op_oride_beta funK_def)

lemma bag_eqI:
  assumes 
    a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X" and 
    a3: "\<And> x \<bullet> b\<sharp>x = c\<sharp>x"
  shows "b = c"
  apply (rule functional_eqI)
  apply (insert a1 a2)
  apply (mauto(fspace))
proof -
  from a3 show b0: "\<zdom> b = \<zdom> c"
    by (auto simp add: Z_dom_bhash [OF a1] Z_dom_bhash [OF a2] set_eq_def)
  fix x assume 
    b1: "x \<in> \<zdom> b"
  with b0 have 
    b2: "x \<in> \<zdom> c"
    by (simp)
  from a3 [of x] b1 b2 a1 a2 show
   "b\<cdot>x = c\<cdot>x"
    by (simp add: bhash_beta')
qed

lemma bag_eqI':
  assumes 
    a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X" and 
    a3: "\<And> x \<bullet> x \<in> X \<turnstile> b\<sharp>x = c\<sharp>x"
  shows "b = c"
proof (rule bag_eqI [OF a1 a2])
  fix x show "b\<sharp>x = c\<sharp>x"
  proof (cases "x \<in> X")
    assume c1: "x \<in> X"
    then show "?thesis"
      by (rule a3)
  next
    assume c1: "x \<notin> X"
    with a1 a2 have "x \<notin> \<zdom> b" and "x \<notin> \<zdom> c"
      apply (mauto(fspace))
      done
    then show ?thesis
      by (simp add: bhash_beta' [OF a1]  bhash_beta' [OF a2])
  qed
qed

section {* Defining bag operators from bag count terms *}

text {*

The general approach taken by Spivey to defining bag operators is to 
express axiomatically the count of the result in terms of the count of the arguments.
Axiomatic definitions can adressed in HOL with the definite articl operator.
In order to demonstrate that such definitions are always well-defined, we introduce
the @{term "bag_of"} operator which converts any given natural number function to a bag.

*}

definition
  bag_of :: "('a \<leftrightarrow> \<arithmos>) \<rightarrow> 'a bagT"
where
  bag_of_def: "bag_of f \<defs> f\<zrres>\<nat>\<subone>"

lemma bag_of_in_bagI:
  assumes
    a1: "f \<in> X \<zpfun> \<nat>"
  shows 
    "bag_of f \<in> \<zbag> X"
  using a1
  apply (simp add: bag_of_def)
  apply (mauto(fspace))
  apply (auto simp add: rres_dom)
  apply (auto simp add: rres_def)
  done

lemma bag_of_glambda_in_bagI:
  assumes
    a1: "{ x | b x } \<subseteq> X" "{ x | b x \<bullet> t x } \<subseteq> \<nat>"
  shows 
    "bag_of (\<glambda> x | b x \<bullet> t x) \<in> \<zbag> X"
  apply (rule bag_of_in_bagI)
  apply (mauto(fspace))
  using a1
  apply (auto dest!: subsetD simp add: Domain_def Range_def rsub_def glambda_mem zNats1_def)
  done

lemma bag_of_beta:
  assumes a1: "functional f" and a2: "x \<in> \<zdom> f" and a3: "f\<cdot>x \<in> \<nat>\<subone>"
  shows "(bag_of f)\<cdot>x = f\<cdot>x"
  apply (insert functional_appl [OF a1 a2] a1 a2 a3)
  apply (simp add: bag_of_def)
  apply (rule functional_beta)
  apply (mauto(fspace))
  apply (simp add: rres_def)
  done

lemma bag_of_mem:
  "(x \<mapsto> y) \<in> bag_of f \<Leftrightarrow> (x \<mapsto> y) \<in> f \<and> y \<in> \<nat>\<subone>"
  by (auto simp add: bag_of_def rres_def)

lemma bag_of_dom:
  "\<zdom> (bag_of f) = { x | (\<exists> y | y \<in> \<nat>\<subone> \<bullet> (x \<mapsto> y) \<in> f)}"
  by (auto simp add: Domain_def bag_of_mem)

lemma bag_of_ran:
  "\<zran> (bag_of f) = \<zran> f \<inter> \<nat>\<subone>"
  by (auto simp add: bag_of_mem)

lemma bag_of_bhash:
  assumes a1: "functional f" and a2: "\<zran> f \<subseteq> \<nat>"
  shows "(bag_of f)\<sharp>x = \<if> x \<in> \<zdom> f \<then> f\<cdot>x \<else> 0 \<fi>"
  apply (cases "x \<in> \<zdom> f")
  apply (simp_all)
proof -
  from a1 a2 have b1: "bag_of f \<in> \<zbag> \<univ>"
    apply (intro bag_of_in_bagI)
    apply (mauto(fspace))
    done
{ assume b2: "x \<in> \<zdom> f"
  show "(bag_of f)\<sharp>x = f\<cdot>x"
  proof (cases "f\<cdot>x \<in> \<nat>\<subone>")
    assume c1: "f\<cdot>x \<notin> \<nat>\<subone>"
    with functional_unique [OF a1] have c3: "x \<notin> \<zdom> (bag_of f)"
      by (simp add: bag_of_dom zNats1_def)
    with a1 a2 [THEN subsetD, OF functional_ran [OF a1 b2]] functional_appl [OF a1 b2]
    show "(bag_of f)\<sharp>x = f\<cdot>x"
      apply (simp add: bhash_beta' [OF b1])
      apply (auto simp add: bag_of_dom zNats1_def)
      done
  next
    assume c1: "f\<cdot>x \<in> \<nat>\<subone>"
    have c2: "x \<in> \<zdom> (bag_of f)"
      apply (simp add: bag_of_mem Domain_iff)
      apply (witness "f\<cdot>x")
      apply (simp add: c1  functional_appl [OF a1 b2])
      done
    then show "(bag_of f)\<sharp>x = f\<cdot>x"
      by (simp add: bhash_beta' [OF b1] bag_of_beta [OF a1 b2 c1])
  qed
next
  assume "x \<notin> \<zdom> f"
  then have "x \<notin> \<zdom> (bag_of f)"
    by (auto simp add: bag_of_mem)   
  then show "(bag_of f)\<sharp>x = 0"
    by (simp add: bhash_beta' [OF b1]) }
qed

lemma bag_of_glambda_bhash:
  assumes a1: "\<And> x \<bullet> b x \<turnstile> t x \<in> \<nat>"
  shows "(bag_of (\<glambda> x | b x \<bullet> t x))\<sharp>x = \<if> b x \<then> t x \<else> 0 \<fi>"
proof -
  from a1 have b1: "\<zran> (\<glambda> x | b x \<bullet> t x) \<subseteq> \<nat>"
    by (auto simp add: glambda_ran)
  with a1 show "?thesis"
    by (auto simp add: bag_of_bhash [OF glambda_functional] glambda_dom glambda_beta)
qed

lemma bag_of_glambda_bhash':
  "(bag_of (\<glambda> x | b x \<bullet> of_nat (t x)))\<sharp>x = \<if> b x \<then> of_nat (t x) \<else> 0 \<fi>"
  apply (rule bag_of_glambda_bhash)
  apply (auto simp add: zNats_def)
  done

text {*

Now we make use of @{text "bag_of"} to demonstrate that all bag count style definitions
are well-defined.

*}

lemma bhash_def_wdef:
  assumes a1: "(\<forall> x | x \<in> X \<bullet> t x \<in> \<nat>)"
  shows "(\<exists>\<subone> b' \<bullet> b' \<in> \<zbag> X \<and> (\<forall> x | x \<in> X \<bullet> b'\<sharp>x = t x))"
  apply (rule ex1I [of _ "bag_of (\<glambda> x | x \<in> X \<bullet> t x)"])
  apply (msafe(inference))
proof -
  show b1: "bag_of (\<glambda> x | x \<in> X \<bullet> t x) \<in> \<zbag> X"
    apply (rule bag_of_glambda_in_bagI)
    using a1
    apply (auto)
    done
{ fix x assume "x \<in> X"
  with a1 show "(bag_of (\<glambda> x | x \<in> X \<bullet> t x))\<sharp>x = t x"
    by (simp add: bag_of_glambda_bhash) } note b2 = this
{ fix b'
  assume b3: "b' \<in> \<zbag> X" and b4: "(\<forall> x | x \<in> X \<bullet> b'\<sharp>x = t x)"
  from b3 b1 show "b' =  bag_of (\<glambda> x | x \<in> X \<bullet> t x)"
    apply (rule bag_eqI')
    apply (simp add: b2 b4)
    done }
qed

section {* Bag extension *}

text {*

Extensional bag comprehension uses a comma-separated list similar to 
that for sets and sequences, but with doubled bracket delimeters..

*}

definition
  bempty :: "'a bagT"
where
  bempty_def: "bempty \<defs> \<emptyset>"

definition
  binsert :: "['a, 'a bagT] \<rightarrow> 'a bagT"
where
  binsert_def: "binsert x b \<defs> b \<oplus> {(x \<mapsto> b\<sharp>x + 1)} "

notation (xsymbols)
  bempty ("\<lbag> \<rbag>") and
  bempty ("\<lbag> \<rbag>")

syntax (xsymbols)
  "_Z_Bag\<ZZ>extbag" :: "args \<rightarrow> logic" ("\<lbag> _ \<rbag>")

translations
  "\<lbag>x, xs\<rbag>"     \<rightleftharpoons> "CONST Z_Bag.binsert x \<lbag>xs\<rbag>"
  "\<lbag>x\<rbag>"         \<rightleftharpoons> "CONST Z_Bag.binsert x \<lbag> \<rbag>"

lemma bempty_in_bagI:
  "\<lbag> \<rbag> \<in> \<zbag> X"
  apply (simp add: bempty_def)
  apply (mauto(fspace) mintro: fin_pfunI)
  done

lemma binsert_in_bagI:
  assumes 
    a1: "b \<in> \<zbag> X" and 
    a2: "x \<in> X"
  shows 
    "binsert x b \<in> \<zbag> X"
  using a1 a2
  apply (simp add: binsert_def)
  apply (mauto(fspace))
  apply (mauto(fspace) mintro!: fin_pfunI)
  apply (simp add: Z_rel_oride_dom_dist fin_pfun_simp)
proof -
  have "b\<sharp>x \<in> \<nat>"
    by (rule bhash_range [OF a1])
  then have b1: "b\<sharp>x + 1 \<in> \<nat>\<subone>"
    by (auto simp add: zInts_zNats_nonneg zInts_zNats1_pos image_def)
  with a1 show "\<zran> (b \<oplus> {(x \<mapsto> b\<sharp>x + 1)}) \<subseteq> \<nat>\<subone>"
    apply (mauto(fspace))
    apply (auto dest!: subsetD simp add: rel_oride_def dsub_def)
    done
qed

lemma binsert_mem:
  "(y \<mapsto> n) \<in> binsert x b \<Leftrightarrow> (\<if> y = x \<then> n = b\<sharp>x + 1 \<else> (y \<mapsto> n) \<in> b \<fi>)"
  by (simp add: binsert_def rel_oride_mem fin_pfun_simp)

lemma bempty_mem:
  "(y \<mapsto> n) \<notin> \<lbag> \<rbag>"
  by (simp add: bempty_def)

lemmas bfin_mem = binsert_mem bempty_mem

lemma binsert_dom:
  "\<zdom> (binsert x b) = insert x (\<zdom> b)"
  by (auto simp add: binsert_mem Domain_def)

lemma bempty_dom:
  "\<zdom> \<lbag> \<rbag> = \<emptyset>"
  by (auto simp add: bempty_mem Domain_def)

lemmas bfin_dom = binsert_dom bempty_dom

lemma binsert_bhash:
  "(binsert x b)\<sharp>y = \<if> y = x \<then> b\<sharp>x + 1 \<else> b\<sharp>y \<fi>"
  by (simp add: bhash_def op_oride_beta binsert_def rel_oride_beta Z_rel_oride_dom_dist fin_pfun_simp fin_funappl)

lemma bempty_bhash: 
  "\<lbag> \<rbag>\<sharp>y = 0"
  by (simp add: bhash_def op_oride_beta funK_def bempty_def rel_oride_beta glambda_beta)

lemmas bfin_bhash = binsert_bhash bempty_bhash

lemma binsertC [simp]: "binsert x (binsert y b) = binsert y (binsert x b)"
  apply (rule rel_eqI)
  apply (simp add: binsert_mem binsert_bhash)
  done

lemma "\<lbag> 0::nat, 1, 1, 1, 2, 2, 3 \<rbag>\<sharp>1 = 3"
  by (simp add: bfin_bhash)

lemma "\<zdom> \<lbag> 0::nat, 1, 1, 1, 2, 2, 3 \<rbag> = {0, 1, 2, 3}"
  by (simp add: bfin_dom)

lemma "\<lbag> 0::nat, 1, 1, 1, 2, 2, 3 \<rbag> = \<lbag> 1, 2, 1, 0::nat, 1, 2, 3 \<rbag>"
  by (simp)






section {* Bag scaling *}

text {*

Scalar bag multiplication increases the membership of the bag by an integer
factor.

*}

definition
  bscale :: "[\<arithmos>, 'a bagT] \<rightarrow> 'a bagT"
where
  bscale_def: "bscale n b \<defs> (\<mu> b' | b' \<in> \<zbag> (\<zdom> b) \<and> (\<forall> x | x \<in> \<zdom> b \<bullet> b'\<sharp>x = n * (b\<sharp>x)))"

notation (xsymbols)
  bscale (infixr "\<otimes>" 100)


lemma bscale_in_zNats:
  assumes a1: "b \<in> \<zbag> X" and a2: "n \<in> \<nat>" 
  shows "(\<forall> x | x \<in> X \<bullet> n * (b\<sharp>x) \<in> \<nat>)"
  apply (msafe(inference))
  apply (rule zNats_mult)
  apply (rule a2)
  apply (rule bhash_range [OF a1])
  done

lemmas bscale_wdef = 
  bhash_def_wdef [
    of "\<zdom> b" "\<olambda> x \<bullet> n * b\<sharp>x", 
    THEN theI', 
    OF bscale_in_zNats,
    folded bscale_def, 
    standard]

lemma bscale_in_bagI:
  assumes a1: "b \<in> \<zbag> X" and a2: "n \<in> \<nat>"
  shows "n \<otimes> b \<in> \<zbag> X"
  apply (insert bscale_wdef [OF a1 [THEN in_bag_dom] a2, THEN conjunct1] a1)
  apply (mauto(fspace))
  done

lemma bscale_bhash:
  assumes a1: "b \<in> \<zbag> X" and a2: "n \<in> \<nat>"
  shows "(n \<otimes> b)\<sharp>x = n * (b\<sharp>x)"
  apply (cases "x \<in> \<zdom> b")
  apply (rule bscale_wdef [OF a1 [THEN in_bag_dom] a2, THEN conjunct2, rule_format])
  apply (assumption)
  apply (insert a1 bscale_wdef [OF a1 [THEN in_bag_dom] a2, THEN conjunct1])
  apply (simp add: bhash_beta')
  apply (mauto(fspace))
  apply (auto)
  done

lemma Z_bscale_def:
  assumes 
    a1: "b \<in> \<zbag> X" "n \<in> \<nat>"
  shows 
    "(n \<otimes> b)\<sharp>x \<defs> n * (b\<sharp>x)"
  using a1
  by (simp add: bscale_bhash)

lemma bscale_mem:
  assumes 
    a1: "b \<in> \<zbag> X" and
    a2: "n \<in> \<nat>"
  shows 
    "(x \<mapsto> y) \<in> n \<otimes> b \<Leftrightarrow> n \<noteq> 0 \<and> (\<exists> y' \<bullet> (x \<mapsto> y') \<in> b \<and> y = n * y')"
  using a1 a2
  by (auto simp add: mem_bhash [OF a1] mem_bhash [OF bscale_in_bagI [OF a1]] bscale_bhash zNats1_def bhash_range)

lemma bscale_dom:
  assumes 
    a1: "b \<in> \<zbag> X" and 
    a2: "n \<in> \<nat>"
  shows 
    "\<zdom> (n \<otimes> b) = \<if> n = 0 \<then> {} \<else> \<zdom> b \<fi>"  
  using a1 a2
  by (auto simp add: Domain_def bscale_mem zNats1_def)

lemma bscale_dom2:
  assumes 
    a1: "b \<in> \<zbag> X" and 
    a2: "n \<in> \<nat>"
  shows 
    "\<zdom> (n \<otimes> b) = \<if> 0 < n \<then> \<zdom> b \<else> {} \<fi>"  
  using a1 a2
  by (auto simp add: Domain_def bscale_mem zInts_zNats_nonneg zInts_zNats1_pos)

lemma bscale_beta: 
  assumes a1: "b \<in> \<zbag> X" and a2: "x \<in> \<zdom> b" and a3: "n \<in> \<nat>\<subone>"
  shows "(n \<otimes> b)\<cdot>x = n*(b\<cdot>x)"
  apply (insert bscale_in_bagI [OF a1 a3 [THEN zNats_zNats1]] a1 a2 a3)
  apply (simp add: zNats1_def)
  apply (mauto(fspace))
  apply (rule functional_beta)
  apply (assumption)
  apply (simp add: bscale_mem [OF a1 a3 [THEN zNats_zNats1]])
  apply (rule functional_appl)
  apply (mauto(fspace))
  done

lemma bempty_scale:
  assumes a1: "n \<in> \<nat>"
  shows "n \<otimes> \<lbag> \<rbag> = \<lbag> \<rbag>"
  by (auto simp add: bscale_mem [OF bempty_in_bagI a1] bempty_mem)

lemma zero_scale:
  assumes a1: "b \<in> \<zbag> X"
  shows "0 \<otimes> b = \<lbag> \<rbag>"
  by (auto simp add: bscale_mem [OF a1] bempty_mem)

lemma Z_bscale_bempty_zero:
  assumes a1: "b \<in> \<zbag> X" and a2: "n \<in> \<nat>"
  shows "\<lch> n \<otimes> \<lbag> \<rbag> \<chEq> 0 \<otimes> b \<chEq> \<lbag> \<rbag> \<rch>"
  using a1 a2
  by (simp add: zero_scale bempty_scale)

lemma Z_unit_scale:
  assumes a1: "b \<in> \<zbag> X"
  shows "1 \<otimes> b = b"
  by (auto simp add: bscale_mem [OF a1])

lemma Z_dist_scale:
  assumes a1: "b \<in> \<zbag> X" and a2: "n \<in> \<nat>" and a3: "m \<in> \<nat>" 
  shows  "(n * m) \<otimes> b = n \<otimes> m \<otimes> b"
  apply (insert a1 a2 a3 bscale_in_bagI [OF a1, of "m"])
  apply (auto simp add: bscale_mem set_eq_def)
  done

section {* Bag membership and sub-bags *}

text {*

An element is a member of a bag if it is in the domain of the bag function.

*} 

definition
  inbag :: "['a, 'a bagT] \<rightarrow> \<bool>"
where
  inbag_def : "inbag x b \<defs> x \<in> \<zdom> b"

notation (xsymbols)
  inbag (infixl "\<inbag>" 90)


lemma Z_inbag_def:
  assumes "x \<in> X" "B \<in> \<zbag> X"
  shows "x \<inbag> B \<defs> x \<in> \<zdom> B"
  by (auto simp add: inbag_def Domain_def)

lemma Z_inbag_bhash:
  assumes a1: "b \<in> \<zbag> X"
  shows "x \<inbag> b \<Leftrightarrow> 0 < b\<sharp>x"
  by (simp add: inbag_def Z_dom_bhash [OF a1] zNats1_pos bhash_range [OF a1])

text {*

The sub-bag relation can be defined as the pointwise order on bag counts.

*}

definition
  bag_le :: "['a bagT, 'a bagT] \<rightarrow> \<bool>"
where
  bag_le_def: "bag_le b_d_1 b_d_2 \<defs> (\<forall> x \<bullet> b_d_1\<sharp>x \<le> b_d_2\<sharp>x)"

notation (xsymbols)
  bag_le ("_ \<subbag> _" [50, 51] 50)

lemma Z_bag_le_def:
  assumes a1: "B \<in> \<zbag> X" "C \<in> \<zbag> X"
  shows "B \<subbag> C \<defs> (\<forall> x | x \<in> X \<bullet> B\<sharp>x \<le> C\<sharp>x)"
  apply (rule eq_reflection)
  using a1
  apply (auto simp add: bag_le_def)
proof -
  fix x
  assume b1: "(\<forall> x | x \<in> X \<bullet> B\<sharp>x \<le> C\<sharp>x)"
  show "B\<sharp>x \<le> C\<sharp>x"
    apply (cases "x \<in> X")
    apply (simp add: b1)
  proof -
    assume c1: "x \<notin> X"
    from a1 c1 have "x \<notin> \<zdom> B" "x \<notin> \<zdom> C"
      apply (mauto(fspace))
      done
    with a1 show "B\<sharp>x \<le> C\<sharp>x"
      by (simp add: bhash_beta')
  qed
qed

lemma Z_bempty_bag_le:
  assumes a1: "b \<in> \<zbag> X"
  shows "\<lbag> \<rbag> \<subbag> b"
  using a1
  by (simp add: bag_le_def bempty_in_bagI bempty_bhash bhash_range2)

lemma Z_bag_self_le:
  assumes a1: "b \<in> \<zbag> X"
  shows "b \<subbag> b"
  using a1
  by (auto simp add: bag_le_def)

lemma bag_le_dom:
  assumes 
    a1: "b_d_1 \<subbag> b_d_2" and
    a2: "b_d_1 \<in> \<zbag> X" and
    a3: "b_d_2 \<in> \<zbag> X"
  shows 
    "\<zdom> b_d_1 \<subseteq> \<zdom> b_d_2"
  using a1 a2 a3
  apply (simp add: Z_dom_bhash)
  apply (auto intro: order_less_le_trans)
  apply (simp add: bag_le_def)
proof -
  fix x
  assume b0: "\<forall> r \<bullet> b_d_1\<sharp>r \<le> b_d_2\<sharp>r" and b1: "b_d_1\<sharp>x \<in> \<nat>\<subone>"
  from b1 zNats1_def have b1': "b_d_1\<sharp>x \<in> zNats" and b1'': "b_d_1\<sharp>x \<noteq> 0" by auto
  from b0 [rule_format] have b2:  "b_d_1\<sharp>x \<le> b_d_2\<sharp>x" by auto
  from a3 have
    b3: "b_d_2\<sharp>x \<in> zNats"  
    by (rule bhash_range)
  

  have "b_d_2\<sharp>x \<noteq> 0" 
    by  (rule zNats_le_noteq_zero [OF b1' b3 b2 b1''] )

  with b3 show "b_d_2\<sharp>x \<in> \<nat>\<subone>"
    by (simp add: zNats1_def)
qed

lemma Z_bag_le_dom:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X"
  shows "b \<subbag> c \<Rightarrow> \<zdom> b \<subseteq> \<zdom> c"
  apply (msafe(inference))
  apply (intro bag_le_dom)
  using a1 a2
  apply (simp_all)
  done

lemma Z_bag_le_eq:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X"
  shows "b \<subbag> c \<and> c \<subbag> b \<Rightarrow> b = c"
  apply (simp add: bag_le_def)
  apply (msafe(inference))
proof (rule bag_eqI [OF a1 a2])
  fix x
  assume b0: "\<forall> r \<bullet> b\<sharp>r \<le> c\<sharp>r" and b1: "\<forall> r \<bullet> c\<sharp>r \<le> b\<sharp>r"
  from b0 [rule_format] have b0': "b\<sharp>x \<le> c\<sharp>x" by this
  from b1 [rule_format] have b1': "c\<sharp>x \<le> b\<sharp>x" by this
  from b0' b1' show "b\<sharp>x = c\<sharp>x" by auto
qed

lemma Z_bag_le_trans:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X" and a3: "d \<in> \<zbag> X"
  shows "b \<subbag> c \<and> c \<subbag> d \<Rightarrow> b \<subbag> d"
  apply (simp add: bag_le_def)
  apply (msafe(inference))
proof -
  fix x
  assume b0: "\<forall> r \<bullet> b\<sharp>r \<le> c\<sharp>r" and b1: "\<forall> r \<bullet> c\<sharp>r \<le> d\<sharp>r"
  from b0 [rule_format] have b0': "b\<sharp>x \<le> c\<sharp>x" by this
  from b1 [rule_format] have b1': "c\<sharp>x \<le> d\<sharp>x" by this  
  from b0' b1' show "b\<sharp>x \<le> d\<sharp>x" by auto
qed

(*
interpretation bagpo: Order_Locale.partial_order ["bag X" "bag_le X"]
  apply (simp_all add: carrier_def setrel_axioms_def reflexive_axioms_def transitive_axioms_def antisymmetric_axioms_def)
  apply (msafe(inference))
proof -
  from bempty_in_bagI [of X] show "\<zbag> X \<noteq> \<emptyset>"
    by (auto)
next
  show "\<oprel>(bag_le X) \<in> \<zbag> X \<zrel> \<zbag> X"
    by (auto simp add: op2rel_def bag_le_def rel_def)
next
  fix b assume "b \<in> \<zbag> X"
  then show "b \<^ble>{:X:} b"
    by (auto simp add: bag_le_def)
next
  fix b_d_1 b_d_2 b_d_3 
  assume "b_d_1 \<in> \<zbag> X" and "b_d_2 \<in> \<zbag> X" and "b_d_3 \<in> \<zbag> X" and
    "b_d_1 \<^ble>{:X:} b_d_2" and "b_d_2 \<^ble>{:X:} b_d_3"
  then show "b_d_1 \<^ble>{:X:} b_d_3"
    by (auto intro: order_trans simp add: bag_le_def)
next
  fix b_d_1 b_d_2
  assume "b_d_1 \<in> \<zbag> X" and "b_d_2 \<in> \<zbag> X" and
    "b_d_1 \<^ble>{:X:} b_d_2" and "b_d_2 \<^ble>{:X:} b_d_1"
  then show "b_d_1 = b_d_2"
    apply (intro bag_eqI)
    apply (auto intro: order_antisym simp add: bag_le_def)
    done
qed
*)

section {* Bag union and difference *} 

text {*

Bag union and bag difference can be defined in terms of arithmetic on the counts.

*}

definition
  bunion :: "['a bagT, 'a bagT] \<rightarrow> 'a bagT"
where
  bunion_def : "bunion b c \<defs> (\<mu> b' | b' \<in> \<zbag> (\<zdom> b \<union> \<zdom> c) \<and> (\<forall> x | x \<in> (\<zdom> b \<union> \<zdom> c) \<bullet> b'\<sharp>x = b\<sharp>x + c\<sharp>x))"

definition
  bdiff :: "['a bagT, 'a bagT] \<rightarrow> 'a bagT"
where
  bdiff_def : "bdiff b c \<defs> (\<mu> b' | b' \<in> \<zbag> (\<zdom> b \<union> \<zdom> c) \<and> (\<forall> x | x \<in> (\<zdom> b \<union> \<zdom> c) \<bullet> b'\<sharp>x = \<if> c\<sharp>x \<le> b\<sharp>x \<then> b\<sharp>x - c\<sharp>x \<else> 0 \<fi>))"

notation (xsymbols)
  bunion (infixl "\<bunion>" 100) and
  bdiff (infixl "\<bdiff>" 100)


lemma bunion_in_zNats:
  assumes 
    a1: "b \<in> \<zbag> X" "c \<in> \<zbag> X"
  shows 
    "(\<forall> x \<bullet> x \<in> Domain b \<union> Domain c \<Rightarrow> b\<sharp>x + c\<sharp>x \<in> \<nat>)"
  using a1
  by (auto intro!: zNats_add simp add: bhash_range)

lemmas bunion_wdef = 
  bhash_def_wdef [
    of "\<zdom> b \<union> \<zdom> c" "\<olambda> x \<bullet> b\<sharp>x + c\<sharp>x", 
    THEN theI', 
    folded bunion_def,
    OF bunion_in_zNats,
    standard]

lemma bdiff_in_zNats:
  assumes 
    a1: "b \<in> \<zbag> X" "c \<in> \<zbag> X"
  shows 
    "(\<forall> x \<bullet> x \<in> Domain b \<union> Domain c \<Rightarrow> \<if> c\<sharp>x \<le> b\<sharp>x \<then> b\<sharp>x - c\<sharp>x \<else> 0 \<fi> \<in> \<nat>)"
  using a1
  by (auto intro!: zNats_diff simp add: bhash_range)

lemmas bdiff_wdef =
  bhash_def_wdef [
    of "\<zdom> b \<union> \<zdom> c" "\<olambda> x \<bullet> \<if> c\<sharp>x \<le> b\<sharp>x \<then> b\<sharp>x - c\<sharp>x \<else> 0 \<fi>", 
    THEN theI', 
    folded bdiff_def, 
    OF bdiff_in_zNats,
    standard]

lemma bunion_in_bagI:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X"
  shows "b \<bunion> c \<in> \<zbag> X"
  apply (insert a1 a2 bunion_wdef [OF a1 a2])
  apply (msafe(inference))
  apply (mauto(fspace))
(*J XXX why need this now? *)
  apply (rule order_trans, assumption)
  apply auto
  done

lemma bdiff_in_bagI:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X"
  shows "b \<bdiff> c \<in> \<zbag> X"
  apply (insert a1 a2 bdiff_wdef [OF a1 a2])
  apply (msafe(inference))
  apply (mauto(fspace))
(*J XXX why need this now? *)
  apply (rule order_trans, assumption)
  apply auto
  done

lemma bunion_bhash:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X"
  shows "(b \<bunion> c)\<sharp>x = (b\<sharp>x) + (c\<sharp>x)"
  apply (cases "x \<in> \<zdom> b \<union> \<zdom> c")
  apply (simp add: bunion_wdef [OF a1 a2, THEN conjunct2, rule_format])
  apply (insert a1 a2 bunion_wdef [OF a1 a2, THEN conjunct1])
  apply (simp add: bhash_beta')
  apply (mauto(fspace))
  apply (auto)
  done

lemma Z_bunion_def:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X"
  shows "(b \<bunion> c)\<sharp>x \<defs> (b\<sharp>x) + (c\<sharp>x)"
  using a1 a2
  by (simp add: bunion_bhash)

lemma bdiff_bhash:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X"
  shows "(b \<bdiff> c)\<sharp>x = \<if> c\<sharp>x \<le> b\<sharp>x \<then> b\<sharp>x - c\<sharp>x \<else> 0 \<fi>"
  apply (cases "x \<in> \<zdom> b \<union> \<zdom> c")
  apply (simp add: bdiff_wdef [OF a1 a2, THEN conjunct2, rule_format])
  apply (insert a1 a2 bdiff_wdef [OF a1 a2, THEN conjunct1])
  apply (simp add: bhash_beta')
  apply (mauto(fspace))
  apply (auto)
  done

lemma Z_bdiff_def:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X"
  shows "(b \<bdiff> c)\<sharp>x \<defs> \<if> c\<sharp>x \<le> b\<sharp>x \<then> b\<sharp>x - c\<sharp>x \<else> 0 \<fi>"
  using a1 a2
  by (simp add: bdiff_bhash)

lemma Z_bunion_dom:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X"
  shows "\<zdom> (b \<bunion> c) = (\<zdom> b) \<union> (\<zdom> c)"
  apply (insert bunion_wdef [OF a1 a2, THEN conjunct1])
  apply (mauto(fspace))
  apply (rule order_antisym)
  apply (assumption)
  apply (rule subsetI)
  apply (insert bhash_range [OF a1] bhash_range [OF a2])
  apply (simp add: Z_dom_bhash [OF a1] Z_dom_bhash [OF a2] Z_dom_bhash [OF bunion_in_bagI [OF a1 a2]] 
    bunion_bhash [OF a1 a2] zNats1_def nat_of_norm)
  done

lemma bunion_empty:
  assumes a1: "b \<in> \<zbag> X"
  shows "\<lbag> \<rbag> \<bunion> b = b" "b \<bunion> \<lbag> \<rbag> = b"
  apply (rule bag_eqI')
  apply (rule bunion_in_bagI [OF bempty_in_bagI a1])
  apply (rule a1)
  apply (simp add: bunion_bhash [OF bempty_in_bagI a1] bempty_bhash)
  apply (rule bag_eqI')
  apply (rule bunion_in_bagI [OF a1 bempty_in_bagI])
  apply (rule a1)
  apply (simp add: bunion_bhash [OF a1 bempty_in_bagI] bempty_bhash)
  done

lemma Z_bunion_empty:
  assumes a1: "b \<in> \<zbag> X"
  shows "\<lch> \<lbag> \<rbag> \<bunion> b \<chEq> b \<bunion> \<lbag> \<rbag> \<chEq> b \<rch>"
  apply (insert bunion_empty [OF a1])
  apply auto
  done


lemma Z_bunion_commute:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X"
  shows "b \<bunion> c = c \<bunion> b"
  apply (rule bag_eqI')
  apply (rule bunion_in_bagI [OF a1 a2])
  apply (rule bunion_in_bagI [OF a2 a1])
  apply (simp add: bunion_bhash [OF a1 a2] bunion_bhash [OF a2 a1])
  done

lemma Z_bunion_assoc:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X" and a3: "d \<in> \<zbag> X"
  shows "(b \<bunion> c) \<bunion> d = b \<bunion> (c \<bunion> d)"
  apply (rule bag_eqI')
  apply (rule bunion_in_bagI [OF bunion_in_bagI [OF a1 a2] a3])
  apply (rule bunion_in_bagI [OF a1 bunion_in_bagI [OF a2 a3]])
  apply (simp add: 
    bunion_bhash [OF bunion_in_bagI [OF a1 a2] a3] bunion_bhash [OF a1 bunion_in_bagI [OF a2 a3]]
    bunion_bhash [OF a1 a2] bunion_bhash [OF a2 a3])
  done

lemma bunion_left_commute:
  assumes a1: "b \<in> \<zbag> X" and a2: "c \<in> \<zbag> X" and a3: "d \<in> \<zbag> X"
  shows "b \<bunion> (c \<bunion> d) = c \<bunion> (b \<bunion> d)"
  by (simp add: Z_bunion_assoc [OF a1 a2 a3, symmetric] Z_bunion_assoc [OF a2 a1 a3, symmetric]
    Z_bunion_commute [OF a1 a2])

lemmas bunion_AC = Z_bunion_commute Z_bunion_assoc bunion_left_commute

lemma Z_bdiff_empty:
  assumes a1: "b \<in> \<zbag> X"
  shows "\<lbag> \<rbag> \<bdiff> b = \<lbag> \<rbag> \<and> b \<bdiff> \<lbag> \<rbag> = b"
  apply (rule conjI)
  apply (rule bag_eqI')
  apply (rule bdiff_in_bagI [OF bempty_in_bagI a1])
  apply (rule bempty_in_bagI)
  using a1
  apply (simp add: bdiff_bhash [OF bempty_in_bagI a1] bempty_bhash bhash_range zNats_le_0_eq)
  apply (rule bag_eqI')
  apply (rule bdiff_in_bagI [OF a1 bempty_in_bagI])
  apply (rule a1)
  using a1
  apply (simp add: bdiff_bhash [OF a1 bempty_in_bagI] bempty_bhash bhash_range zNats_le0)
  done
  

lemma Z_bunion_inverse:
  assumes
    a1: "b \<in> \<zbag> X" and 
    a2: "c \<in> \<zbag> X"
  shows 
    "(b \<bunion> c) \<bdiff> c = b"
  apply (rule bag_eqI')
  apply (rule bdiff_in_bagI [OF bunion_in_bagI [OF a1 a2] a2])
  apply (rule a1)
  using a1 a2
  apply (simp add: bunion_bhash [OF a1 a2] bdiff_bhash [OF bunion_in_bagI [OF a1 a2] a2] 
    bhash_range zNats_le0)
  done

lemma Z_bscale_union:
  assumes 
    a1: "b \<in> \<zbag> X" and 
    a2: "n \<in> \<nat>" and 
    a3: "m \<in> \<nat>"
  shows "(n + m) \<otimes> b = (n \<otimes> b) \<bunion> (m \<otimes> b)"
  apply (rule bag_eqI')
  apply (rule bscale_in_bagI [OF a1 zNats_add [OF a2 a3]])
  apply (rule bunion_in_bagI [OF bscale_in_bagI [OF a1 a2] bscale_in_bagI [OF a1 a3]])
  using a1 a2 a3
  apply (simp add: bunion_bhash [OF bscale_in_bagI [OF a1] bscale_in_bagI [OF a1]] 
    bscale_bhash [OF a1] bhash_range distrib_right)
  done

lemma bscale_diff:
  assumes 
    a1: "b \<in> \<zbag> X" and 
    a2: "n \<in> \<nat>" and 
    a3: "m \<in> \<nat>" and 
    a4: "m \<le> n"
  shows 
    "(n - m) \<otimes> b = (n \<otimes> b) \<bdiff> (m \<otimes> b)"
  apply (rule bag_eqI')
  apply (rule bscale_in_bagI [OF a1])
  using a1 a2 a3 a4
  apply (simp)
  apply (rule bdiff_in_bagI [OF bscale_in_bagI [OF a1] bscale_in_bagI [OF a1]])
  using a1 a2 a3 a4
  apply (auto simp add: bdiff_bhash [OF bscale_in_bagI [OF a1] bscale_in_bagI [OF a1]] 
    bscale_bhash [OF a1] left_diff_distrib mult_right_mono bhash_range nat_of_norm)
  done

lemma Z_bscale_diff:
  assumes 
    a1: "b \<in> \<zbag> X" and 
    a2: "n \<in> \<nat>" and 
    a3: "m \<in> \<nat>"
  shows 
    "m \<le> n \<Rightarrow> (n - m) \<otimes> b = (n \<otimes> b) \<bdiff> (m \<otimes> b)"
  apply (msafe(inference))
  apply (intro bscale_diff)
  using a1 a2 a3
  apply (simp_all)
  done

lemma Z_bunion_distr:
  assumes 
    a1: "b \<in> \<zbag> X" and 
    a2: "c \<in> \<zbag> X" and 
    a3: "n \<in> \<nat>"
  shows 
    "n \<otimes> (b \<bunion> c) = (n \<otimes> b) \<bunion> (n \<otimes> c)"
  apply (rule bag_eqI')
  apply (rule bscale_in_bagI [OF bunion_in_bagI [OF a1 a2] a3])
  apply (rule bunion_in_bagI [OF bscale_in_bagI [OF a1 a3] bscale_in_bagI [OF a2 a3]])
  using a1 a2 a3
  apply (simp add: bunion_bhash [OF bscale_in_bagI [OF a1 a3] bscale_in_bagI [OF a2 a3]] 
    bscale_bhash [OF bunion_in_bagI [OF a1 a2] a3] bunion_bhash [OF a1 a2] 
    bscale_bhash [OF a1 a3] bscale_bhash [OF a2 a3] distrib_left bhash_range)
  done

lemma Z_bdiff_distr:
  assumes 
    a1: "b \<in> \<zbag> X" and 
    a2: "c \<in> \<zbag> X" and 
    a3: "n \<in> \<nat>"
  shows 
    "n \<otimes> (b \<bdiff> c) = (n \<otimes> b) \<bdiff> (n \<otimes> c)"
  apply (rule bag_eqI')
  apply (rule bscale_in_bagI [OF bdiff_in_bagI [OF a1 a2] a3])
  apply (rule bdiff_in_bagI [OF bscale_in_bagI [OF a1 a3] bscale_in_bagI [OF a2 a3]])
  apply (insert bhash_range [OF a1] bhash_range [OF a2] a1 a2 a3)
  apply (auto simp add: bdiff_bhash [OF bscale_in_bagI [OF a1 a3] bscale_in_bagI [OF a2 a3]] 
    bscale_bhash [OF bdiff_in_bagI [OF a1 a2] a3] bdiff_bhash [OF a1 a2] 
    bscale_bhash [OF a1 a3] bscale_bhash [OF a2 a3] right_diff_distrib bhash_range 
    mult_left_mono nat_of_norm diff_mult_distrib2)
  done


(*
lemma Z_bunion_bdiff_defs:
  "\<forall> B C x | B \<in> \<zbag> X \<and> C \<in> \<zbag> X \<and> x \<in> X \<bullet>
  ((B \<bunion> C)\<sharp>x = (B\<sharp>x) + (C\<sharp>x)) \<and>
  ((B \<bdiff> C)\<sharp>x = zmax\<cdot>{B\<sharp>x - C\<sharp>x, (0::\<arithmos>)})"
  apply (auto simp add: bunion_bhash)
  apply (simp add: bdiff_bhash)
*)

section {* Bags from sequences *}

text {*

A bag can be constructed by counting the occurrances of the elements of a list.

*}

definition
  bitems :: "'a seqT \<rightarrow> 'a bagT"
where
  bitems_def : "bitems s \<defs> (\<mu> b' | b' \<in> \<zbag> (\<zran> s) \<and> (\<forall> x | x \<in> \<zran> s \<bullet> b'\<sharp>x = \<zcard>{ i | i \<in> \<zdom> s \<and> s\<cdot>i = x }))"

notation (xsymbols)
  bitems ("\<bitems>")


lemma bitems_in_ZNats:
  "\<forall> x | x \<in> \<zran> s \<bullet> \<zcard>{ i | i \<in> \<zdom> s \<and> s\<cdot>i = x } \<in> \<nat>"
  by (simp add: zcard_def zNats_def)

lemmas bitems_wdef = 
  bhash_def_wdef [
    of "\<zran> (s::'a seqT)" "\<olambda> x \<bullet> \<zcard>{ i | i \<in> \<zdom> s \<and> s\<cdot>i = x }", 
    THEN theI', 
    folded bitems_def, 
    OF bitems_in_ZNats,
    standard]

lemma bitems_in_bagI:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<bitems> s \<in> \<zbag> X"
  apply (insert bitems_wdef [of s, THEN conjunct1] a1)
  apply (mauto(fspace))
  done

lemma bitems_in_bagI':
  "bitems s \<in> \<zbag> \<univ>"
  apply (insert bitems_wdef [of s, THEN conjunct1])
  apply (rule in_bag_subset)
  apply (auto)
  done

lemma zcard_pre_seq_zero:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<notin> \<zran> s"
  shows "\<zcard>{ i | i \<in> \<zdom> s \<and> s\<cdot>i = x } = 0"
proof -
  from a1 have b1: "functional s"
    by (mauto(fspace))
  from b1 have "{ i | i \<in> \<zdom> s \<and> s\<cdot>i = x } = { i | (i \<mapsto> x) \<in> s }"
  by (mauto(wind) msimp add: functional_unique functional_beta)
(*
    apply (mauto(wind))
    apply (msafe(inference))
    apply (simp add: functional_unique) 
    apply (fast)
    apply (simp add: functional_beta)
    done
*)
  also from a2 have "{ i | (i \<mapsto> x) \<in> s } = \<emptyset>"
    by (auto)
  finally have b2: "{ i | i \<in> \<zdom> s \<and> s\<cdot>i = x } = \<emptyset>"
    by (this)
  show "?thesis"
    by (simp add: b2 zcard_def)
qed

lemma zcard_pre_image:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zcard>{ i | i \<in> \<zdom> s \<and> s\<cdot>i = x } = \<zcard>{ i | (i \<mapsto> x) \<in> s \<bullet> (i \<mapsto> x)}"
proof -
  from a1 have b1: "{ i | (i \<mapsto> x) \<in> s \<bullet> (i \<mapsto> x)} = (\<olambda> i \<bullet> (i \<mapsto> x))\<lparr>{ i | i \<in> \<zdom> s \<and> s\<cdot>i = x }\<rparr>"
    apply (auto)
    apply (mauto(fspace))
    apply (auto intro: functional_appl functional_beta simp add: image_def)
    done
  then show "?thesis" 
    apply (simp add: zcard_def)
    apply (rule sym)
    apply (rule card_image)
    apply (rule inj_onI)
    apply (auto)
    done
qed

lemma bitems_bhash:
  assumes a1: "s \<in> \<zseq> X"
  shows  "(\<bitems> s)\<sharp>x = \<zcard>{ i | i \<in> \<zdom> s \<and> s\<cdot>i = x }"
  apply (cases "x \<in> \<zran> s")
  apply (insert bitems_wdef [of s, THEN conjunct2])
  apply (simp)
  apply (insert bitems_wdef [of s, THEN conjunct1])
  apply (simp add: bhash_beta' [OF bitems_wdef [of s, THEN conjunct1]])
  apply (mauto(fspace))
  apply (auto simp add: zcard_pre_seq_zero [OF a1])
  done

lemma Z_bitems_def:
  assumes a1: "s \<in> \<zseq> X" "x \<in> X"
  shows  "(\<bitems> s)\<sharp>x \<defs> \<zcard>{ i | i \<in> \<zdom> s \<and> s\<cdot>i = x }"
  using a1
  by (simp add: bitems_bhash)

lemma Z_bitems_dom:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zdom> (\<bitems> s) = \<zran> s"
  apply (rule set_eqI)
  apply (simp add: Z_dom_bhash [OF bitems_in_bagI [OF a1]] bitems_bhash [OF a1] 
    zcard_pre_image [OF a1] zNats1_pos [OF zcard_range])
proof -
  fix x
  from a1 have "{ i | (i \<mapsto> x) \<in> s \<bullet> (i \<mapsto> x) } \<subseteq> s" "finite s"
    by (auto intro: seq_finite)
  then have b2: "finite { i | (i \<mapsto> x) \<in> s \<bullet> (i \<mapsto> x) }"
    by (rule finite_subset)
  have "0 < \<zcard>{ i | (i \<mapsto> x) \<in> s \<bullet> (i \<mapsto> x) } \<Leftrightarrow> { i | (i \<mapsto> x) \<in> s \<bullet> (i \<mapsto> x) } \<noteq> \<emptyset>"
    apply (subst zcard_nempty_conv [OF b2])
    apply (fast)
    done
  also have "\<dots> \<Leftrightarrow> x \<in> \<zran> s"
    apply (subst nempty_conv)
    apply (auto)
    done
  finally show "0 < \<zcard>{ i | (i \<mapsto> x) \<in> s \<bullet> (i \<mapsto> x) } \<Leftrightarrow> x \<in> \<zran> s"
    by (this)
qed

lemma zcard_pre_sinsert:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X" and a3: "y \<in> X"
  shows "\<zcard>{i | (i, x) \<in> sinsert y s \<bullet> (i \<mapsto> x)} 
  = \<if> y = x 
    \<then> \<zcard>{i | (i, x) \<in> s \<bullet> (i \<mapsto> x)} + 1 
    \<else> \<zcard>{i | (i, x) \<in> s \<bullet> (i \<mapsto> x)} 
    \<fi>"
proof (auto)
  have "\<zcard>{i | (i, x) \<in> sinsert x s \<bullet> (i \<mapsto> x)} 
  = \<zcard>{i | (i, x) \<in> insert (1 \<mapsto> x) (stranslate s 1) \<bullet> (i \<mapsto> x)}"
     by (simp add: sinsert_redef [OF a1 a2])
  also have "{i | (i, x) \<in> insert (1 \<mapsto> x) (stranslate s 1) \<bullet> (i \<mapsto> x)} 
  = (insert (1 \<mapsto> x)  {i | (i, x) \<in> (stranslate s 1) \<bullet> (i \<mapsto> x)})"
     by (auto)
  also have "\<zcard>(insert (1 \<mapsto> x) {i | (i, x) \<in> (stranslate s 1) \<bullet> (i \<mapsto> x)}) 
  = (\<zcard>{i | (i, x) \<in> (stranslate s 1) \<bullet> (i \<mapsto> x)}) + 1"
    apply (rule zcard_insert_disjoint)
    apply (rule finite_subset [OF _ stranslate_finite [of s 1]])
    apply (simp add: eind_def subset_def)
    apply (rule seq_finite [OF a1])
    apply (simp add: stranslate_def)
    apply (rule contrapos_nn)
    defer 1
    apply (rule DomainI)
    apply (assumption)
    apply (simp add: seq_dom [OF a1])
    done
  also have "\<zcard>{i | (i, x) \<in> (stranslate s 1) \<bullet> (i \<mapsto> x)} 
  = \<zcard>{i | (i, x) \<in> s \<bullet> (i \<mapsto> x)}"
  proof -
    let ?f = "\<olambda>(n::\<arithmos>, x::'b) \<bullet> (n + 1, x)"
    have c1: "{i | (i, x) \<in> (stranslate s 1) \<bullet> (i \<mapsto> x)} = ?f\<lparr>{i | (i, x) \<in> s \<bullet> (i \<mapsto> x)}\<rparr>"
      by (auto simp add: stranslate_def eind_def)
    show "?thesis"
      apply (subst c1)
      apply (rule zcard_image)
      apply (rule inj_onI)
      apply (auto)
      done
    qed
  finally show "\<zcard>{i | (i, x) \<in> sinsert x s \<bullet> (i \<mapsto> x)}  
  = (\<zcard>{i | (i, x) \<in> s \<bullet> (i \<mapsto> x)}) + 1"
    by (this)
next
  assume b1: "y \<noteq> x"
  have "\<zcard>{i | (i, x) \<in> sinsert y s \<bullet> (i \<mapsto> x)} 
  = \<zcard>{i | (i, x) \<in> insert (1 \<mapsto> y) (stranslate s 1) \<bullet> (i \<mapsto> x)}"
    by (simp add: sinsert_redef [OF a1 a3])
  also from b1 have "{i | (i, x) \<in> insert (1 \<mapsto> y) (stranslate s 1) \<bullet> (i \<mapsto> x)} 
  = {i | (i, x) \<in> (stranslate s 1) \<bullet> (i \<mapsto> x)}"
    by (auto)
  also have "\<zcard>{i | (i, x) \<in> (stranslate s 1) \<bullet> (i \<mapsto> x)} 
  = \<zcard>{i | (i, x) \<in> s \<bullet> (i \<mapsto> x)}"
  proof -
    let ?f = "\<olambda>(n::\<arithmos>, x::'b) \<bullet> (n + 1, x)"
    have c1: "{i | (i, x) \<in> (stranslate s 1) \<bullet> (i \<mapsto> x)} = ?f\<lparr>{i | (i, x) \<in> s \<bullet> (i \<mapsto> x)}\<rparr>"
        by (auto simp add: stranslate_def eind_def)
    show "?thesis"
      apply (subst c1)
      apply (rule zcard_image)
      apply (rule inj_onI)
      apply (auto)
      done
  qed
  finally show "\<zcard>{i | (i, x) \<in> sinsert y s \<bullet> (i \<mapsto> x)} 
  = \<zcard>{i | (i, x) \<in> s \<bullet> (i \<mapsto> x)}"
    by (this)
qed

lemma Z_bitems_concat:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "\<bitems> (s \<zcat> t) = \<bitems> s \<bunion> \<bitems> t"
  apply (rule bag_eqI')
  apply (rule bitems_in_bagI [OF sconcat_closed [OF a1 a2]])
  apply (rule bunion_in_bagI [OF bitems_in_bagI [OF a1] bitems_in_bagI [OF a2]])
  apply (simp add: bitems_bhash [OF sconcat_closed [OF a1 a2]] 
    bunion_bhash [OF bitems_in_bagI [OF a1] bitems_in_bagI [OF a2]] bitems_bhash [OF a1] 
    bitems_bhash [OF a2] zcard_pre_image [OF sconcat_closed [OF a1 a2]] 
    zcard_pre_image [OF a1] zcard_pre_image [OF a2])
proof -
  fix x
  assume b1: "x \<in> X"
  show "\<zcard>{i | (i, x) \<in> s \<zcat> t \<bullet> (i \<mapsto> x)} = \<zcard>{i | (i, x) \<in> s \<bullet> (i \<mapsto> x)} + \<zcard>{i | (i, x) \<in> t \<bullet> (i \<mapsto> x)}"
    apply (induct s rule: seq_induct_insert)
    apply (rule a1)
  proof -
    show "\<zcard>{i | (i, x) \<in> \<sempty> \<zcat> t \<bullet> (i \<mapsto> x)} = \<zcard>{i | (i, x) \<in> \<sempty> \<bullet> (i \<mapsto> x)} + \<zcard>{i | (i, x) \<in> t \<bullet> (i \<mapsto> x)}"
      apply (simp add: Z_sconcat_sempty [OF a2])
      apply (simp add: sempty_def eind_def)
      done
  next
    fix s y
    assume c1: "s \<in> \<zseq> X" and c2: "y \<in> X" and
      c3: "\<zcard>{i | (i, x) \<in> s \<zcat> t \<bullet> (i \<mapsto> x)} = \<zcard>{i | (i, x) \<in> s \<bullet> (i \<mapsto> x)} + \<zcard>{i | (i, x) \<in> t \<bullet> (i \<mapsto> x)}"
    have "\<zcard>{i | (i, x) \<in> sinsert y (s \<zcat> t) \<bullet> (i \<mapsto> x)} = \<zcard>{i | (i, x) \<in> sinsert y s \<bullet> (i \<mapsto> x)} + \<zcard>{i | (i, x) \<in> t \<bullet> (i \<mapsto> x)}"
      by (simp add: zcard_pre_sinsert [OF c1 b1 c2] zcard_pre_sinsert [OF sconcat_closed [OF c1 a2] b1 c2] c3)
    also from c1 c2 a2 sconcat_closed [OF c1 a2] sinsert_closed [OF sempty_seq c2]
    have "sinsert y (s \<zcat> t) = (sinsert y s) \<zcat> t"
      by (simp add: sinsert_sconcat Z_sconcat_assoc)
    finally show "\<zcard>{i | (i, x) \<in> (sinsert y s) \<zcat> t \<bullet> (i \<mapsto> x)} = \<zcard>{i | (i, x) \<in> sinsert y s \<bullet> (i \<mapsto> x)} + \<zcard>{i | (i, x) \<in> t \<bullet> (i \<mapsto> x)}"
      by (this)
  qed
qed

lemma bitems_sempty:
  "bitems \<sempty> = \<lbag> \<rbag>"
  apply (rule bag_eqI)
  apply (rule bitems_in_bagI)
  apply (rule sempty_seq)
  apply (rule bempty_in_bagI)
  apply (simp add: bitems_bhash [OF sempty_seq])
  apply (simp add: sempty_def bempty_bhash)
  done

lemma Z_bitems_sinsert:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "bitems (sinsert x s) = binsert x (bitems s)"
  apply (rule bag_eqI')
  apply (rule bitems_in_bagI)
  apply (rule sinsert_closed [OF a1 a2])
  apply (rule binsert_in_bagI [OF bitems_in_bagI [OF a1] a2])
  apply (simp add: bitems_bhash [OF sinsert_closed [OF a1 a2]] binsert_bhash 
    bitems_bhash [OF a1] zcard_pre_image [OF a1] zcard_pre_image [OF sinsert_closed [OF a1 a2]] 
    zcard_pre_sinsert [OF a1 a2 a2] zcard_pre_sinsert [OF a1 _ a2])
  done

lemmas fin_bitems = bitems_sempty Z_bitems_sinsert

lemma Z_bitems_permutations:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "\<bitems> s = \<bitems> t \<Leftrightarrow> (\<exists> f | f \<in> \<zdom> s \<zbij> \<zdom> t \<bullet> s = t \<zbcomp> f)"
proof (rule iffI) 
  assume b1: "\<bitems> s = \<bitems> t"
  then have "\<zdom> (\<bitems> s) = \<zdom> (\<bitems> t)"
    by (simp)
  then have b2: "\<zran> s = \<zran> t"
    by (simp add: Z_bitems_dom [OF a1] Z_bitems_dom [OF a2])
  from b1 have 
    b3: "\<forall> x | x \<in> \<zran> s \<bullet> 
          (\<exists> f \<bullet> f \<in> { i | i \<in> \<zdom> s \<and> s\<cdot>i = x } \<zbij> { i | i \<in> \<zdom> t \<and> t\<cdot>i = x })"
    apply (msafe(inference))
    apply (rule zcard_eq_bij [where ?'c = "arithmos"])
    apply (rule finite_subset [OF _ seq_finite_dom [OF a1]])
    apply (fast)
    apply (rule finite_subset [OF _ seq_finite_dom [OF a2]])
    apply (fast)
    using a1 a2
    apply (simp add: bitems_bhash [symmetric])
    done
  then obtain F where 
    b4: "(\<forall> x | x \<in> \<zran> s \<bullet> F x \<in> { i | i \<in> \<zdom> s \<and> s\<cdot>i = x } \<zbij> { i | i \<in> \<zdom> t \<and> t\<cdot>i = x })"
    by (auto simp add: qual_ax_choice_eq)
  let ?f = "\<Union> x | x \<in> \<zran> s \<bullet> F x"
  have  
    b5: "(\<forall> x | x \<in> \<zran> s \<bullet> 
           functional (F x) \<and> functional ((F x)\<^sup>\<sim>) \<and> 
           \<zdom> (F x) = { i | i \<in> \<zdom> s \<and> s\<cdot>i = x } \<and> 
           \<zran> (F x) = { i | i \<in> \<zdom> t \<and> t\<cdot>i = x })"
    apply (rule mp [OF _ b4])
    apply (msafe(wind))
    apply (msafe(inference))
    apply (mauto(fspace))
    done
  have 
    b5': "(\<forall> x | x \<in> \<zran> s \<bullet> 
            functional (F x) \<and> functional ((F x)\<^sup>\<sim>) \<and> 
            \<zdom> (F x) = { i | (i \<mapsto> x) \<in> s} \<and> 
            \<zran> (F x) = { i | (i \<mapsto> x) \<in> t})"
  proof (msafe(inference))
    fix x assume c1: "x \<in> \<zran> s"
    from b5 [rule_format, OF c1] show "functional (F x)" "functional ((F x)\<^sup>\<sim>)"
      by (auto)
    from b5 [rule_format, OF c1] show "\<zdom> (F x) = { i | (i \<mapsto> x) \<in> s}"
      by (auto simp add: functional_beta [OF seq_functional [OF a1]])
    from b5 [rule_format, OF c1] show "\<zran> (F x) = { i | (i \<mapsto> x) \<in> t}"
      by (auto simp add: functional_beta [OF seq_functional [OF a2]])
  qed
  have b6: "?f \<in> \<zdom> s \<zbij> \<zdom> t"
  proof (mauto(fspace))
    show "functional (\<Union> x | x \<in> Range s \<bullet> F x)"
      apply (rule rel_Union_functional')
      apply (simp add: b5 [rule_format])
    proof -
      fix x y 
      assume d1: "x \<in> \<zran> s" and d2: "y \<in> \<zran> s"
      show "\<zdom> (F y) \<zdres> F x = \<zdom> (F x) \<zdres> F y"
        apply (cases "x = y")
        apply (simp)
      proof -
        assume e1: "x \<noteq> y"
        with d1 d2 have "\<zdom> (F x) \<inter> \<zdom> (F y) = \<emptyset>"
          apply (simp add: b5 [rule_format])
          apply (auto)
          done
        then show "?thesis"
          by (auto simp add: dres_def eind_def)
      qed
    qed
    show "functional ((\<Union> x | x \<in> Range s \<bullet> F x)\<^sup>\<sim>)"
      apply (simp add: converse_Union eind_norm [of "Collect"])
      apply (rule rel_Union_functional')
      apply (simp add: b5 [rule_format])
    proof -
      fix x y 
      assume d1: "x \<in> \<zran> s" and d2: "y \<in> \<zran> s"
      show "\<zdom> ((F y)\<^sup>\<sim>) \<zdres> (F x)\<^sup>\<sim> = \<zdom> ((F x)\<^sup>\<sim>) \<zdres> (F y)\<^sup>\<sim>"
        apply (cases "x = y")
        apply (simp)
      proof -
        assume e1: "x \<noteq> y"
        with d1 d2 have "\<zdom> ((F x)\<^sup>\<sim>) \<inter> \<zdom> ((F y)\<^sup>\<sim>) = \<emptyset>"
          apply (simp add: b5 [rule_format] Z_inverse_dom)
          apply (auto)
          done
        then show "?thesis"
          by (auto simp add: dres_def Range_iff set_eq_def)
      qed
    qed
    have "\<zdom> (\<Union> x | x \<in> \<zran> s \<bullet> F x) = (\<Union> x | x \<in> \<zran> s \<bullet> \<zdom> (F x))"
      by (simp add: rel_Union_dom eind_def eind_comp)
    also have "\<dots> = (\<Union> x | x \<in> Range s \<bullet> { i | i \<in> \<zdom> s \<and> s\<cdot>i = x })"
      by (mauto(wind) msimp add: b5 [rule_format])
    also have "\<dots> = \<zdom> s"
      apply (auto)
      apply (rule seq_in_ran1 [OF a1])
      apply (auto)
      done
    finally show "\<zdom> (\<Union> x | x \<in> Range s \<bullet> F x) = \<zdom> s"
      by (this)
    have "\<zran> (\<Union> x | x \<in> Range s \<bullet> F x) = (\<Union> x | x \<in> Range s \<bullet> \<zran> (F x))"
      by (simp add: rel_Union_ran eind_def eind_comp)
    also have "\<dots> = (\<Union> x | x \<in> Range s \<bullet> { i | i \<in> \<zdom> t \<and> t\<cdot>i = x })"
      by (mauto(wind) msimp add: b5 [rule_format])
    also have "\<dots> = \<zdom> t"
      apply (auto simp add: b2)
      apply (rule seq_in_ran1 [OF a2])
      apply (auto)
      done
    finally show "\<zran> (\<Union> x | x \<in> Range s \<bullet> F x) = \<zdom> t"
      by (this)
  qed
  from b6 have b6': "functional ?f"
    by (mauto(fspace))
  have b7: "s = t \<zbcomp> ?f"
  proof (rule rel_eqI)
    fix i x
    show "(i \<mapsto> x) \<in> s \<Leftrightarrow> (i \<mapsto> x) \<in> t \<zbcomp> ?f"
      apply (auto simp add: rel_bcomp_def)
      apply (witness "(F x)\<cdot>i")
      apply (msafe(inference))
      apply (witness "x")
      apply (msafe(inference))
    proof -
      assume d1: "(i \<mapsto> x) \<in> s"
      then show d2: "x \<in> \<zran> s"
        by (auto)
      from d1 b5' [rule_format, OF d2] show "(i \<mapsto> (F x)\<cdot>i) \<in> F x"
        by (auto intro!: functional_appl)
      with d1 b5' [rule_format, OF d2] show "((F x)\<cdot>i \<mapsto> x) \<in> t"
        by (auto)
    next
      fix k j y
      assume d1: "(k \<mapsto> x) \<in> t" and d2: "(i \<mapsto> k) \<in> F y" and d3: "(j \<mapsto> y) \<in> s"
      from d3 have d4: "y \<in> \<zran> s"
        by (auto)
      from b5' [rule_format, OF d4] d2 have d5: "(k \<mapsto> y) \<in> t"
        by (auto)
      from seq_functional [OF a2] d1 d5 have d6: "x = y"
        by (rule functionalD)
      from b5' [rule_format, OF d4] d2 d6
      show "(i \<mapsto> x) \<in> s"
        by (auto)
    qed
  qed
  from b6 b7 show "(\<exists> f | f \<in> \<zdom> s \<zbij> \<zdom> t \<bullet> s = t \<zbcomp> f)"
    apply (witness "?f")
    apply (auto)
    done
next
  apply_end (msafe_no_assms(inference))
  fix f
  assume b1: "f \<in> \<zdom> s \<zbij> \<zdom> t" and b2: "s = t \<zbcomp> f"
  from b1 have b3: "functional f"
    by (mauto(fspace))
  from b1 have b4: "functional (f\<^sup>\<sim>)"
    by (mauto(fspace))
  from b1 have b5: "\<zdom> s = \<zdom> f"
    by (mauto(fspace)) 
  from b1 have b6: "\<zdom> t = \<zran> f"
    by (mauto(fspace)) 
  from b1 a2 have b7: "(\<forall> i j | (i \<mapsto> j) \<in> f \<bullet> s\<cdot>i = t\<cdot>j)"
    apply (msafe(inference))
    apply (simp add: b2)
    apply (rule trans)
    apply (rule bcomp_beta)
    apply (mauto(fspace))
    apply (auto simp add: functional_beta)
    done
  show "\<bitems> s = \<bitems> t"
    apply (rule bag_eqI)
    apply (rule bitems_in_bagI [OF a1])
    apply (rule bitems_in_bagI [OF a2])
    apply (auto simp add: bitems_bhash [OF a1] bitems_bhash [OF a2])
  proof -
    fix x
    from b1 have 
      c1: "{i | i \<in> Domain s \<and> s\<cdot>i = x} \<zdres> f 
            \<in> {i | i \<in> Domain s \<and> s\<cdot>i = x} \<zbij> {i | i \<in> Domain t \<and> t\<cdot>i = x}"
    proof (mauto(fspace))
      show "\<zdom> ({i | i \<in> Domain s \<and> s\<cdot>i = x} \<zdres> f) = {i | i \<in> Domain s \<and> s\<cdot>i = x}"
        by (auto simp add: Z_dres_dom b5)
      from b7 [rule_format]
      show "\<zran> ({i | i \<in> Domain s \<and> s\<cdot>i = x} \<zdres> f) = {i | i \<in> Domain t \<and> t\<cdot>i = x}"
        apply (auto simp add: dres_def b5 b6 ran_eind Domain_iff)
        apply (auto intro!: exI)
      proof -
        fix i j k 
        assume d1: "(i \<mapsto> j) \<in> f" and d2: "(i \<mapsto> k) \<in> f"
        show "t\<cdot>j = t\<cdot>k"
          by (simp add: functionalD [OF b3 d1 d2])
      qed
    qed
    show "\<zcard>{i | i \<in> Domain s \<and> s\<cdot>i = x} = \<zcard>{i | i \<in> Domain t \<and> t\<cdot>i = x}"
      by (rule zcard_Image [where ?'c = "arithmos", OF c1, symmetric])
  qed
qed

end
