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
  Z_Fun
  
imports
  Z_Rel
  Z_Fun_Chap

begin

text {*

HOL provides a built-in model for functions (value abstractions), embodied by the type
constructor @{text "fun"} and the $\lambda$-constructor. In the following we 
refer to this model as the \emph{operator} model of functions.

The single-valued \emph{graphs} provide a convenient (and widely used)
mathematical model of functions. This is especially so
when partial or finite functions are of particular interest, as is
often the case in program specification. 

In the following we develop a graph model of functions, based on the
Z mathematical toolkit as described by Spivey~\cite{Spivey:ZRef}.

*}

section {* Function application *}

text {*

Where graph relations are single-valued it makes sense to introduce a notion of 
the \emph{result} of \emph{applying} the relation at that point.
We introduce a relational application operator that chooses the unique
range element related to a given domain element.

*}

definition
  fun_appl :: "[('a \<leftrightarrow> 'b), 'a] \<rightarrow> 'b"
where
  fun_appl_def: "fun_appl f x \<defs> (\<mu> y | (x \<mapsto> y) \<in> f)"  

definition
  single_val :: "[('a \<leftrightarrow> 'b), 'a] \<rightarrow> \<bool>"
where
  single_val_def: "single_val f x \<defs> (\<exists>\<subone> y \<bullet> (x \<mapsto> y) \<in> f)"

notation (xsymbols)
  fun_appl ("_\<cdot>_" [999, 1000] 999)

lemma single_val_appl: 
  "single_val f x \<turnstile> (x, f\<cdot>x) \<in> f"
  apply (auto simp add: single_val_def fun_appl_def)
  apply (rule theI2)
  apply (auto)
  done

lemma single_val_beta: 
  "\<lbrakk> single_val f x; (x, y) \<in> f \<rbrakk> \<turnstile> f\<cdot>x = y"
  by (auto simp add: single_val_def fun_appl_def)

lemma single_val_unique:
  "single_val f x \<turnstile> (x, y) \<in> f \<Leftrightarrow> y = f\<cdot>x"
  by (auto simp add: single_val_appl single_val_beta)

lemma undef_beta: 
  assumes 
    a1: "x \<notin> \<zdom> f"
  shows 
    "f\<cdot>x = (\<mu> y | \<False>)"
proof (unfold fun_appl_def)
  from a1 have 
    "\<forall> y \<bullet> (x \<mapsto> y) \<in> f \<Leftrightarrow> \<False>"
    by (auto)
  then have 
    "(\<olambda> y \<bullet> (x \<mapsto> y) \<in> f) = (\<olambda> y \<bullet> \<False>)"
    by (auto)
  then show 
    "(\<mu> y | (x \<mapsto> y) \<in> f) = (\<mu> y | \<False>)"
    by (auto)
qed

lemma Z_single_val_appl:
  "(\<exists>\<subone> y \<bullet> (x \<zmapsto> y) \<in> f) \<Rightarrow> (x \<zmapsto> f\<cdot>x) \<in> f"
  apply (simp)
  apply (msafe(inference))
  apply (rule single_val_appl)
  apply (simp add: single_val_def)
  done

text {*

A graph is functional if it is single valued at every point in its
domain.

*}

definition
  functional :: "('a \<leftrightarrow> 'b) \<rightarrow> \<bool>"
where
  functional_def: "functional f \<defs> \<forall> x | x \<in> \<zdom> f \<bullet> single_val f x"

lemma functionalI:
  assumes 
    a1: "\<And> x y_d_1 y_d_2 \<bullet> \<lbrakk> (x \<mapsto> y_d_1) \<in> f; (x \<mapsto> y_d_2) \<in> f \<rbrakk> \<turnstile> y_d_1 = y_d_2"
  shows 
    "functional f"
  using a1
  by (auto simp add: functional_def single_val_def)

lemma functionalD: 
  assumes 
    a1: "functional f"
  shows 
    "\<And> x y_d_1 y_d_2 \<bullet> \<lbrakk> (x \<mapsto> y_d_1) \<in> f; (x \<mapsto> y_d_2) \<in> f \<rbrakk> \<turnstile> y_d_1 = y_d_2"
  using a1
  by (auto simp add: functional_def single_val_def)

lemma functionalE:
  assumes 
    a1: "functional f" "(\<And> x y_d_1 y_d_2 \<bullet> \<lbrakk> (x \<mapsto> y_d_1) \<in> f; (x \<mapsto> y_d_2) \<in> f \<rbrakk> \<turnstile> y_d_1 = y_d_2) \<turnstile> R"
  shows 
    "R"
  using a1
  by (auto simp add: functional_def single_val_def)

lemma nonfunctionalI:
  assumes 
    a1: "(x \<mapsto> y_d_1) \<in> f" "(x \<mapsto> y_d_2) \<in> f" "y_d_1 \<noteq> y_d_2"
  shows 
    "\<not> (functional f)"
  using a1
  by (auto simp add: functional_def single_val_def)

lemma nonfunctionalE:
  assumes 
    a1: 
      "\<not> (functional f)" 
      "\<And> x y_d_1 y_d_2 \<bullet> \<lbrakk> (x \<mapsto> y_d_1) \<in> f; (x \<mapsto> y_d_2) \<in> f; y_d_1 \<noteq> y_d_2 \<rbrakk> \<turnstile> R"
  shows
   "R"
  using a1
  by (auto simp add: functional_def single_val_def)

lemma functional_singleton:
  "functional {x \<mapsto> y}"
  by (auto simp add: functional_def single_val_def)

lemma functional_subset:
  assumes a1: "functional g" and a2: "f \<subseteq> g"
  shows "functional f"
  apply (simp add: functional_def)
  apply (msafe(inference))
proof -
  fix x assume b1: "x \<in> \<zdom> f"
  with a2 have "x \<in> \<zdom> g" by (auto)
  with a1 have "single_val g x" by (auto simp add: functional_def)
  with a2 b1 show "single_val f x" by (auto simp add: single_val_def)
qed

lemma functional_appl: "\<lbrakk> functional f; x \<in> \<zdom> f \<rbrakk> \<turnstile> (x, f\<cdot>x) \<in> f"
  by (rule single_val_appl, auto simp add: functional_def)

lemma functional_beta: 
  "\<lbrakk> functional f; (x, y) \<in> f \<rbrakk> \<turnstile> f\<cdot>x = y"
  by (rule single_val_beta, auto simp add: functional_def)

lemma functional_ran:
  assumes a1: "functional f" and a2: "x \<in> \<zdom> f"
  shows "f\<cdot>x \<in> \<zran> f"
proof (rule rel_ran_mem)
  show "f \<in> \<zdom> f \<zrel> \<zran> f"
    by (simp add: rel_dr)
  from a1 a2 show "(x, f\<cdot>x) \<in> f"
    by (rule functional_appl)
qed

lemma functional_unique:
  assumes a1: "functional f"
  shows "(x \<mapsto> y) \<in> f \<Leftrightarrow> x \<in> \<zdom> f \<and> y = f\<cdot>x"
proof (rule iffI)
  assume b1: "(x \<mapsto> y) \<in> f"
  then have b2: "x \<in> \<zdom> f" 
    by (auto)
  with a1 have b3: "single_val f x"
    by (auto simp add: functional_def)
  from b2 b3 b1 show "x \<in> \<zdom> f \<and> y = f\<cdot>x"
    by (simp add: single_val_unique)
next
  assume b1: "x \<in> \<zdom> f \<and> y = f\<cdot>x"
  with a1 have b2:"single_val f x"
    by (auto simp add: functional_def)
  with b1 show "(x \<mapsto> y) \<in> f"
    by (simp add: single_val_unique)
qed

lemma functional_eqI:
  assumes a1: "functional f" and a2: "functional g" and
    a3: "\<zdom> f = \<zdom> g" and
    a4: "\<And> x \<bullet> x \<in> \<zdom> f \<turnstile> f\<cdot>x = g\<cdot>x"
  shows "f = g"
proof (rule rel_eqI)
  fix x y
  from a1 have 
  "(x \<mapsto> y) \<in> f
  \<Leftrightarrow> (x \<in> \<zdom> f \<and> f\<cdot>x = y)"
    by (auto simp add: functional_appl functional_beta)
  also from a3 a4 have "\<dots>
  \<Leftrightarrow> (x \<in> \<zdom> g \<and> g\<cdot>x = y)"
    apply (auto)
    apply (rule sym)
    apply (auto)
    done
  also from a2 have "\<dots>
  \<Leftrightarrow> (x \<mapsto> y) \<in> g"
    by (auto simp add: functional_appl functional_beta)
  finally show "(x \<mapsto> y) \<in> f \<Leftrightarrow> (x \<mapsto> y) \<in> g"
    by (this)
qed

lemma subset_beta:
  assumes a1a: "functional f" and a1b: "functional g" and 
    a2: "f \<subseteq> g" and a3: "n \<in> \<zdom> f"
  shows "f\<cdot>n = g\<cdot>n"
proof -
  from a1a a3 have "(n \<mapsto> f\<cdot>n) \<in> f"
    by (rule functional_appl)
  with a2 have "(n \<mapsto> f\<cdot>n) \<in> g"
    by (auto)
  with a2 a3 show "f\<cdot>n = g\<cdot>n"
    by (simp add: functional_unique [OF a1b])
qed

lemma functional_eq_def:
  assumes a1: "functional f" and a2: "functional g"
  shows "f = g \<Leftrightarrow> \<zdom> f = \<zdom> g \<and> (\<forall> x | x \<in> \<zdom> f \<bullet> f\<cdot>x = g\<cdot>x)"
  apply (rule iffI)
  apply (simp)
  apply (rule functional_eqI [OF a1 a2])
  apply (auto)
  done

lemma functional_conv_Image_inter:
  assumes A1: "functional R"
  shows
  "(R\<^sup>\<sim>)\<zlImg>U \<inter> V\<zrImg> = (R\<^sup>\<sim>)\<zlImg>U\<zrImg> \<inter> (R\<^sup>\<sim>)\<zlImg>V\<zrImg>"
  apply (auto simp add: converse_def Image_def)
  apply (insert A1 [THEN functionalD], auto)
done

section {* Function spaces *}

text {*
 
Z provides an extensive taxonomy of functions according
to completeness, injectivity, and surjectivity~\cite[p105,6]{Spivey:ZRef}.

*}

definition
  part_funs :: "['a set, 'b set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  part_funs_def: "part_funs X Y \<defs> {f | f \<in> X \<zrel> Y \<and> functional f}"

notation (xsymbols)
  part_funs (infixr "\<zpfun>" 92)

definition
  total_funs :: "['a set, 'b set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  total_funs_def: "total_funs X Y \<defs> {f | f \<in> X \<zpfun> Y \<and> \<zdom> f = X}"

notation (xsymbols)
  total_funs (infixr "\<ztfun>" 92)

definition
  part_injs :: "['a set, 'b set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  part_injs_def: "part_injs X Y \<defs> {f | f \<in> X \<zpfun> Y \<and> f\<^sup>\<sim> \<in> Y \<zpfun> X}"

notation (xsymbols)
  part_injs (infixr "\<zpinj>" 92)

definition
  total_injs :: "['a set, 'b set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  total_injs_def: "total_injs X Y \<defs> (X \<zpinj> Y) \<inter> (X \<ztfun> Y)"

notation (xsymbols)
  total_injs (infixr "\<zinj>" 92)

definition
  part_surjs :: "['a set, 'b set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  part_surjs_def: "part_surjs X Y \<defs> {f | f \<in> X \<zpfun> Y \<and> \<zran> f = Y}"

notation (xsymbols)
  part_surjs (infixr "\<zpsurj>" 92)

definition
  total_surjs :: "['a set, 'b set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  total_surjs_def: "total_surjs X Y \<defs> (X \<zpsurj> Y) \<inter> (X \<ztfun> Y)"

notation (xsymbols)
  total_surjs (infixr "\<zsurj>" 92)

definition
  bijs :: "['a set, 'b set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  bijs_def: "bijs X Y \<defs> (X \<zinj> Y) \<inter> (X \<zsurj> Y)"

notation (xsymbols)
  bijs (infixr "\<zbij>" 92)

lemmas fun_space_defs = 
  rel_def functional_def 
  part_funs_def total_funs_def part_injs_def total_injs_def
  part_surjs_def total_surjs_def bijs_def single_val_def fun_appl_def

subsection {* Partial functions *}

lemma in_pfunI: 
  assumes 
    a1: "f \<in> X \<zrel> Y" and
    a2: "\<And> x y_d_1 y_d_2 \<bullet> \<lbrakk> (x \<mapsto> y_d_1) \<in> f; (x \<mapsto> y_d_2) \<in> f \<rbrakk> \<turnstile> y_d_1 = y_d_2"
  shows "f \<in> X \<zpfun> Y"
  using a1 a2
  by (auto simp add: part_funs_def functional_def single_val_def)

lemma pfun_rel [intro]: 
  "f \<in> X \<zpfun> Y \<turnstile> f \<in> X \<zrel> Y"
  by (simp add: part_funs_def)

lemma DR_pfunI: 
  assumes 
    a1: "functional f" and
    a2: "\<zdom> f \<subseteq> X" and a3: "\<zran> f \<subseteq> Y"
  shows "f \<in> X \<zpfun> Y"
proof (auto simp add: part_funs_def functional_def)
  from a2 a3 show "f \<in> X \<zrel> Y" by (rule in_relI)
  fix x y
  assume "(x \<mapsto> y) \<in> f"
  with a1 show "single_val f x"
    by (auto simp add: part_funs_def functional_def)
qed

lemma pfun_functional: "f \<in> X \<zpfun> Y \<turnstile> functional f"
  by (auto simp add: part_funs_def functional_def rel_def)

lemma pfun_dom: "f \<in> X \<zpfun> Y \<turnstile> \<zdom> f \<subseteq> X"
  by (auto simp add: fun_space_defs)

lemma pfun_ran: "f \<in> X \<zpfun> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto simp add: fun_space_defs)

lemma pfun_appl:
  assumes a1: "f \<in> X \<zpfun> Y" and a2: "x \<in> \<zdom> f"
  shows "(x \<mapsto> f\<cdot>x) \<in> f"
  by (rule functional_appl [OF pfun_functional [OF a1] a2])

lemma Z_pfun_appl:
  assumes a1: "f \<in> X \<zpfun> Y"
  shows "x \<in> \<zdom> f \<Rightarrow> (x \<zmapsto> f\<cdot>x) \<in> f"
  by (auto intro!: functional_appl [OF pfun_functional [OF a1]])

lemma pfun_range [intro]: 
  assumes a1: "f \<in> X \<zpfun> Y" and
    a2: "x \<in> \<zdom> f" 
  shows "f\<cdot>x \<in> Y"
proof -
  from a1 a2 have a3: "(x, f\<cdot>x) \<in> f" by (rule pfun_appl)
  from a1 have a4: "f \<in> X \<zrel> Y" by (auto)
  from a3 a4 show ?thesis by (auto simp add: rel_def)
qed

lemma pfun_beta:
  "\<lbrakk> f \<in> X \<zpfun> Y; (x \<mapsto> y) \<in> f \<rbrakk> \<turnstile> f\<cdot>x = y"
  by (auto simp add: part_funs_def functional_def single_val_beta) 

lemma Z_pfun_beta:
  "f \<in> X \<zpfun> Y \<turnstile> (x \<zmapsto> y) \<in> f \<Rightarrow> f\<cdot>x = y"
  by (auto simp add: part_funs_def functional_def single_val_beta) 

lemma pfun_unique:
  "\<lbrakk> f \<in> X \<zpfun> Y; x \<in> \<zdom> f \<rbrakk> \<turnstile> (x \<mapsto> y) \<in> f \<Leftrightarrow> y = f\<cdot>x"
  by (auto simp add: part_funs_def functional_unique) 

lemma Z_pfun_unique:
  "f \<in> X \<zpfun> Y \<turnstile> x \<in> \<zdom> f \<Rightarrow> ((x \<zmapsto> y) \<in> f \<Leftrightarrow> y = f\<cdot>x)"
  by (auto simp add: part_funs_def functional_unique) 

lemma Z_pfun_left_inv: "f \<in> X \<zrel> Y \<turnstile> f \<in> X \<zpfun> Y \<Leftrightarrow> f\<^sup>\<sim> \<zfcomp> f = \<zid> (\<zran> f)"
proof -
  assume a1: "f \<in> X \<zrel> Y"
  show ?thesis
  proof (rule iffI)
    assume 
      b1: "f \<in> X \<zpfun> Y"
    show 
      "f\<^sup>\<sim> \<zfcomp> f = \<zid> (\<zran> f)"
    proof (auto simp add: rel_fcomp_def rel_id_def converse_def rel_bcomp_def)
      fix x y_d_1 y_d_2
      assume 
        c1: "(x \<mapsto> y_d_1) \<in> f" and 
        c2: "(x \<mapsto> y_d_2) \<in> f"
      from c1 have 
        c3: "x \<in> \<zdom> f" 
        by (auto simp add: Domain_def)
      from b1 c3 have 
        c4: "\<exists>\<subone> y \<bullet> (x \<mapsto> y) \<in> f"
        by (simp add: part_funs_def functional_def single_val_def)
      from c4 c1 c2 show 
        "y_d_1 = y_d_2"
        by (auto)
      from c1 show 
        "y_d_1 \<in> \<zran> f" 
        by (auto)
    qed
  next
    assume 
      b1: "f\<^sup>\<sim> \<zfcomp> f = \<zid> (\<zran> f)"
    with a1 show 
      "f \<in> X \<zpfun> Y"
      by (auto simp add: rel_fcomp_def rel_id_def converse_def rel_bcomp_def
        part_funs_def functional_def single_val_def rel_def set_eq_def)
  qed
qed

lemma pfun_left_inv_subset:
  assumes 
    a1: "f \<in> X \<zpfun> Y"
  shows
    "f\<zlImg>(f\<^sup>\<sim>)\<zlImg>B\<zrImg>\<zrImg> \<subseteq> B"
proof -
  have
    "f\<zlImg>(f\<^sup>\<sim>)\<zlImg>B\<zrImg>\<zrImg> 
    = ((f\<^sup>\<sim>)\<zfcomp>f)\<zlImg>B\<zrImg>"
    by (auto simp add: Image_rel_fcomp)
  also from a1 have "...
    = (\<zid> (\<zran> f))\<zlImg>B\<zrImg>"
    by (auto simp add: Z_pfun_left_inv [THEN sym [THEN iffD2]] part_funs_def Image_def rel_id_def functional_def single_val_def)
  also have "... 
    \<subseteq> B"
    by (auto simp add: rel_id_def)
  finally show 
    ?thesis
    by (this)
qed
  


lemma pfun_mono1:
  assumes 
    a1: "X_d_1 \<subseteq> X_d_2" and 
    a2: "f \<in> X_d_1 \<zpfun> Y"
  shows
    "f \<in> X_d_2 \<zpfun> Y"
  apply (rule DR_pfunI)
  apply (rule pfun_functional [OF a2])
  apply (rule subset_trans [OF pfun_dom [OF a2] a1])
  apply (rule pfun_ran [OF a2])
  done

lemma pfun_mono2:
  assumes 
    a1: "Y_d_1 \<subseteq> Y_d_2" and 
    a2: "f \<in> X \<zpfun> Y_d_1"
  shows 
    "f \<in> X \<zpfun> Y_d_2"
  apply (rule DR_pfunI)
  apply (rule pfun_functional [OF a2])
  apply (rule pfun_dom [OF a2])
  apply (rule subset_trans [OF pfun_ran [OF a2] a1])
  done

lemma Z_part_funs_def:
  "X \<zpfun> Y \<defs> {f | f \<in> X \<zrel> Y \<and> (\<forall> x | x \<in> \<zdom> f \<bullet> (\<exists>\<subone> y \<bullet> (x \<zmapsto> y) \<in> f)) }"
  by (simp add: part_funs_def functional_def single_val_def)

subsection {* Total functions *}

lemma in_tfunI: 
  "\<lbrakk> f \<in> X \<zpfun> Y; \<zdom> f = X \<rbrakk> \<turnstile> f \<in> X \<ztfun> Y"
  by (auto simp add: total_funs_def)

lemma tfun_pfun [intro]: 
  "f \<in> X \<ztfun> Y \<turnstile> f \<in> X \<zpfun> Y"
  by (auto simp add: total_funs_def)

lemma DR_tfunI: 
  assumes 
    a1: "functional f" and
    a2: "\<zdom> f = X" and 
    a3: "\<zran> f \<subseteq> Y"
  shows "f \<in> X \<ztfun> Y"
proof (rule in_tfunI)
  from a1 a2 a3 show 
    "f \<in> X \<zpfun> Y"
    by (auto intro!: DR_pfunI)
  from a2 show 
    "\<zdom> f = X"
    by this
qed

lemma tfun_functional: 
  "f \<in> X \<ztfun> Y \<turnstile> functional f"
  by (auto dest: tfun_pfun intro: pfun_functional)

lemma tfun_dom: 
  "f \<in> X \<ztfun> Y \<turnstile> \<zdom> f = X"
  by (auto simp add: fun_space_defs)

lemmas tfun_dom_mem = rel_dom_mem [OF pfun_rel [OF tfun_pfun]]

lemma tfun_ran: 
  "f \<in> X \<ztfun> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto simp add: fun_space_defs)

lemmas tfun_ran_mem = rel_ran_mem [OF pfun_rel [OF tfun_pfun]]

lemma tfun_appl: 
  "\<lbrakk> f \<in> X \<ztfun> Y; x \<in> X \<rbrakk> \<turnstile> (x \<mapsto> f\<cdot>x) \<in> f"
  by (auto intro!: pfun_appl tfun_pfun simp add: tfun_dom)

lemma tfun_range [intro]: 
  assumes 
    a1: "f \<in> X \<ztfun> Y" and
    a2: "x \<in> X" 
  shows "f\<cdot>x \<in> Y"
proof -
  from a1 a2 have
    a3: "(x \<mapsto> f\<cdot>x) \<in> f" 
    by (rule tfun_appl)
  from a1 have 
    a4: "f \<in> X \<zrel> Y" 
    by (auto)
  from a3 a4 show 
    ?thesis 
    by (auto simp add: rel_def)
qed

lemma tfun_beta:
  "\<lbrakk> f \<in> X \<ztfun> Y; (x, y) \<in> f \<rbrakk> \<turnstile> f\<cdot>x = y"
  by (auto intro!: pfun_beta)

lemma tfun_eq_def:
  assumes 
    a1: "f \<in> X \<ztfun> Y" and 
    a2: "g \<in> X \<ztfun> Y"
  shows 
   "f = g \<Leftrightarrow> (\<forall> x | x \<in> X \<bullet> f\<cdot>x = g\<cdot>x)" (is "?LHS = ?RHS")
proof (rule iffI)
  assume ?LHS then show ?RHS by (simp)
next
  assume b1: "?RHS"
  show "?LHS"
  proof (auto)
    fix x y
    assume c1: "(x \<mapsto> y) \<in> f"
    with a1 have "f\<cdot>x = y"
      by (auto intro!: tfun_beta)
    with a1 a2 b1 c1 have "g\<cdot>x = y"
      by (auto simp add: tfun_dom [OF a1, THEN sym])
    with a1 a2 c1 show "(x, y) \<in> g"
      by (auto intro!: tfun_appl simp add: tfun_dom [OF a1, THEN sym])
  next
    fix x y
    assume c1: "(x \<mapsto> y) \<in> g"
    with a2 have "g\<cdot>x = y"
      by (auto intro!: tfun_beta)
    with a1 a2 b1 c1 have "f\<cdot>x = y"
      by (auto simp add: tfun_dom [OF a2, THEN sym])
    with a1 a2 c1 show "(x, y) \<in> f"
      by (auto intro!: tfun_appl simp add: tfun_dom [OF a2, THEN sym])
  qed
qed

lemma tfun_eqI:
  assumes
    a1a: "f \<in> X \<ztfun> Y" and  
    a1b: "g \<in> X \<ztfun> Y" and
    a2: "\<And> x \<bullet> x \<in> X \<turnstile> f\<cdot>x = g\<cdot>x"
  shows
    "f = g"
  by (auto simp add: tfun_eq_def [OF a1a a1b] a2)

lemma tfun_mono2:
  assumes
    a1: "Y_d_1 \<subseteq> Y_d_2" and 
    a2: "f \<in> X \<ztfun> Y_d_1"
  shows 
   "f \<in> X \<ztfun> Y_d_2"
  apply (rule DR_tfunI)
  apply (rule tfun_functional [OF a2])
  apply (rule tfun_dom [OF a2])
  apply (rule subset_trans [OF tfun_ran [OF a2] a1])
  done


lemma tfun_right_inv_subset:
  assumes 
    A1: "f \<in> X \<ztfun> Y" and    
    A2: "A \<subseteq> X"  
  shows
    "A \<subseteq> (f\<^sup>\<sim>)\<zlImg>f\<zlImg>A\<zrImg>\<zrImg>"
proof-
  have R1:
    "\<zdom> f = X"
    by (intro A1 [THEN tfun_dom])
  from A2 have
    "A 
    = (\<zid> (\<zdom> f))\<zlImg>A\<zrImg>"
    by (auto simp add: R1 rel_id_def Image_def)
  also have "... 
    \<subseteq> (f\<zfcomp>(f\<^sup>\<sim>))\<zlImg>A\<zrImg>"
    by (auto simp add: Image_def Z_inverse_lgalois [THEN subsetD])
  also have "... 
    = (f\<^sup>\<sim>)\<zlImg>f\<zlImg>A\<zrImg>\<zrImg>"
    by (auto simp add: Image_rel_fcomp)
  finally show 
    ?thesis 
    by (this)
qed

lemma tfun_unique:
  assumes
    a1: "f \<in> X \<ztfun> Y"
  shows
    "(x \<mapsto> y) \<in> f \<Leftrightarrow> x \<in> X \<and> y = f\<cdot>x"
  apply (subst tfun_dom [OF a1, symmetric])
  apply (rule functional_unique)
  apply (rule tfun_functional [OF a1])
  done

lemma tfun_Image_conv:
  assumes
    a1: "f \<in> X \<ztfun> Y"
  shows
    "f\<zlImg>X'\<zrImg> = { x | x \<in> X \<and> x \<in> X' \<bullet> f\<cdot>x }"
  apply (auto simp add: Image_def)
  apply (auto intro!: exI simp add: tfun_beta [OF a1] tfun_dom_mem [OF a1] tfun_appl [OF a1])
  done

lemma tfun_Collect_Image:
  assumes
    a1: "f \<in> X \<ztfun> Y"
  shows
    "f\<zlImg>{ x | P x }\<zrImg> = { x | x \<in> X \<and> P x \<bullet> f\<cdot>x}"
  by (auto simp add: tfun_Image_conv [OF a1])  

lemma tfun_Collect_Image':
  assumes
    a1: "f \<in> X \<ztfun> Y"
  shows
    "f\<zlImg>{ x | P x \<bullet> g x }\<zrImg> = { x | g x \<in> X \<and> P x \<bullet> f\<cdot>(g x)}"
  by (auto simp add: tfun_Image_conv [OF a1])+  

subsection {* Partial injections *}

lemma in_pinjI: 
  "\<lbrakk> f \<in> X \<zpfun> Y;
    \<And> x_d_1 x_d_2 y \<bullet> \<lbrakk> (x_d_1 \<mapsto> y) \<in> f; (x_d_2 \<mapsto> y) \<in> f \<rbrakk> \<turnstile> x_d_1 = x_d_2 \<rbrakk>
  \<turnstile> f \<in> X \<zpinj> Y"
  by (auto simp add: part_injs_def part_funs_def functional_def single_val_def converse_def rel_def)

lemma DR_pinjI: 
  assumes 
    a1: "functional f" "functional (f\<^sup>\<sim>)" and
    a2: "\<zdom> f \<subseteq> X" "\<zran> f \<subseteq> Y"
  shows 
   "f \<in> X \<zpinj> Y"
  using a1 a2
  by (auto simp add: fun_space_defs)

lemma pinj_pfun [intro]: 
  "f \<in> X \<zpinj> Y \<turnstile> f \<in> X \<zpfun> Y"
  by (auto simp add: part_injs_def part_funs_def)

lemma Z_pinj_f_finv:
  "f \<in> X \<zpinj> Y \<Leftrightarrow> f \<in> X \<zpfun> Y \<and> f\<^sup>\<sim> \<in> Y \<zpfun> X"
  by (simp add: part_injs_def)

lemma pinj_functional: 
  "f \<in> X \<zpinj> Y \<turnstile> functional f"
  by (auto simp add: fun_space_defs)

lemma pinj_dom: 
  "f \<in> X \<zpinj> Y \<turnstile> \<zdom> f \<subseteq> X"
  by (auto simp add: fun_space_defs)

lemma pinj_ran: 
  "f \<in> X \<zpinj> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto simp add: fun_space_defs)

lemma pinj_appl:
  assumes 
    a1: "f \<in> X \<zpinj> Y" and 
    a2: "x \<in> \<zdom> f"
  shows 
    "(x \<mapsto> f\<cdot>x) \<in> f"
  by (rule pfun_appl [OF pinj_pfun [OF a1] a2])

lemma pinj_beta:
  assumes 
    a1: "f \<in> X \<zpinj> Y" and 
    a2: "(x \<mapsto> y) \<in> f"
  shows 
    "f\<cdot>x = y"
  by (rule pfun_beta [OF pinj_pfun [OF a1] a2])

lemma pinj_inv_pfun [intro]: 
  "f \<in> X \<zpinj> Y \<turnstile> f\<^sup>\<sim> \<in> Y \<zpfun> X"
  by (simp add: part_injs_def)

lemma Z_pinj_inv_pinj:
  "f \<in> X \<zpinj> Y \<Rightarrow> f\<^sup>\<sim> \<in> Y \<zpinj> X"
  by (simp add: part_injs_def)

lemma pinj_inv_functional: 
  "f \<in> X \<zpinj> Y \<turnstile> functional (f\<^sup>\<sim>)"
  by (auto simp add: fun_space_defs)

lemma pinj_inv_appl:
  assumes 
    a1: "f \<in> X \<zpinj> Y" and 
    a2: "x \<in> \<zdom> f"
  shows 
    "(f\<cdot>x \<mapsto> x) \<in> f\<^sup>\<sim>"
  using a1 a2
  by (simp add: converse_def pinj_appl)

lemma pinj_inv_beta:
  assumes 
    a1: "f \<in> X \<zpinj> Y" and a2: "(x \<mapsto> y) \<in> f"
  shows 
    "(f\<^sup>\<sim>)\<cdot>y = x"
  apply (rule pfun_beta [OF pinj_inv_pfun [OF a1]])
  using a1 a2
  apply (simp add: converse_def)
  done

lemma pinj_inj: 
  assumes 
    a1: "f \<in> X \<zpinj> Y" and
    a2: "x_d_1 \<in> \<zdom> f" and a3: "x_d_2 \<in> \<zdom> f" and
    a4: "f\<cdot>x_d_1 = f\<cdot>x_d_2"
  shows "x_d_1 = x_d_2"
proof -
  have 
    "x_d_1 
    = (f\<^sup>\<sim>)\<cdot>(f\<cdot>x_d_1)"
    apply (rule sym)
    apply (rule pinj_inv_beta [OF a1])
    apply (rule pinj_appl [OF a1 a2])
    done
  also from a4 have "\<dots> 
    = (f\<^sup>\<sim>)\<cdot>(f\<cdot>x_d_2)" by (simp)
  also have "\<dots> 
    = x_d_2"
    apply (rule pinj_inv_beta [OF a1])
    apply (rule pinj_appl [OF a1 a3])
    done
  finally show ?thesis by this
qed

subsection {* Total injections *}

lemma in_tinjI: 
  "\<lbrakk> f \<in> X \<zpinj> Y; f \<in> X \<ztfun> Y \<rbrakk> \<turnstile> f \<in> X \<zinj> Y"
  by (simp add: total_injs_def)

lemma in_tinjIa: 
  "\<lbrakk> f \<in> X \<zpinj> Y; \<zdom> f = X \<rbrakk> \<turnstile> f \<in> X \<zinj> Y"
  by (auto intro!: in_tinjI in_tfunI)

lemma tinj_pinj [intro]: 
  "f \<in> X \<zinj> Y \<turnstile> f \<in> X \<zpinj> Y"
  by (simp add: total_injs_def)

lemma tinj_tfun [intro]: 
  "f \<in> X \<zinj> Y \<turnstile> f \<in> X \<ztfun> Y"
  by (simp add: total_injs_def)

lemma Z_tinj_f_finv:
  "f \<in> X \<zinj> Y \<Leftrightarrow> f \<in> X \<ztfun> Y \<and> f\<^sup>\<sim> \<in> Y \<zpfun> X"
  by (auto simp add: fun_space_defs)

lemma DR_tinjI: 
  assumes 
    a1: "functional f" and a2: "functional (f\<^sup>\<sim>)" and
    a3: "\<zdom> f = X" and a4: "\<zran> f \<subseteq> Y"
  shows 
    "f \<in> X \<zinj> Y"
  using a1 a2 a3 a4
  by (auto simp add: fun_space_defs)

lemma tinj_functional: 
  "f \<in> X \<zinj> Y \<turnstile> functional f"
  by (auto simp add: fun_space_defs) 

lemma tinj_dom: 
  "f \<in> X \<zinj> Y \<turnstile> \<zdom> f = X"
  by (auto simp add: fun_space_defs)

lemmas tinj_dom_mem = tfun_dom_mem [OF tinj_tfun]

lemma tinj_ran: 
  "f \<in> X \<zinj> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto simp add: fun_space_defs)

lemmas tinj_ran_mem = tfun_ran_mem [OF tinj_tfun]

lemma tinj_appl:
  assumes 
    a1: "f \<in> X \<zinj> Y" and a2: "x \<in> X"
  shows 
    "(x \<mapsto> f\<cdot>x) \<in> f"
  by (rule tfun_appl [OF tinj_tfun [OF a1] a2])

lemma tinj_beta:
  assumes 
    a1: "f \<in> X \<zinj> Y" and a2: "(x \<mapsto> y) \<in> f"
  shows 
    "f\<cdot>x = y"
  by (rule tfun_beta [OF tinj_tfun [OF a1] a2])

lemma tinj_range [intro]: 
  assumes 
    a1: "f \<in> X \<zinj> Y" and
    a2: "x \<in> X" 
  shows "f\<cdot>x \<in> Y"
proof -
  from a1 a2 have 
    a3: "(x \<mapsto> f\<cdot>x) \<in> f" 
    by (rule tinj_appl)
  from a1 have 
    a4: "f \<in> X \<zrel> Y" 
    by (auto)
  from a3 a4 show ?thesis 
    by (auto simp add: rel_def)
qed

lemma tinj_inv_pfun [intro]: 
  "f \<in> X \<zinj> Y \<turnstile> f\<^sup>\<sim> \<in> Y \<zpfun> X"
  by (simp add: fun_space_defs)

lemma tinj_inv_functional: 
  "f \<in> X \<zinj> Y \<turnstile> functional (f\<^sup>\<sim>)"
  by (auto simp add: fun_space_defs)

lemma tinj_inv_appl:
  assumes 
    a1: "f \<in> X \<zinj> Y" and a2: "x \<in> X"
  shows 
    "(f\<cdot>x \<mapsto> x) \<in> f\<^sup>\<sim>"
  using a1 a2
  by (simp add: converse_def tinj_appl)

lemma tinj_inv_beta:
  assumes 
    a1: "f \<in> X \<zinj> Y" and a2: "(x \<mapsto> y) \<in> f"
  shows 
    "(f\<^sup>\<sim>)\<cdot>y = x"
  apply (rule pfun_beta [OF tinj_inv_pfun [OF a1]])
  using a1 a2
  apply (simp add: converse_def)
  done

lemma tinj_inj: 
  assumes 
    a1: "f \<in> X \<zinj> Y" and
    a2: "x_d_1 \<in> X" and a3: "x_d_2 \<in> X" and
    a4: "f\<cdot>x_d_1 = f\<cdot>x_d_2"
  shows "x_d_1 = x_d_2"
proof -
  have 
    "x_d_1 
    = (f\<^sup>\<sim>)\<cdot>(f\<cdot>x_d_1)"
    apply (rule sym)
    apply (rule tinj_inv_beta [OF a1])
    apply (rule tinj_appl [OF a1 a2])
    done
  also from a4 have "\<dots> 
    = (f\<^sup>\<sim>)\<cdot>(f\<cdot>x_d_2)" 
    by (simp)
  also have "\<dots> 
    = x_d_2"
    apply (rule tinj_inv_beta [OF a1])
    apply (rule tinj_appl [OF a1 a3])
    done
  finally show ?thesis by this
qed

lemma tinj_inj_iff: 
  assumes 
    a1: "f \<in> X \<zinj> Y" and
    a2: "x_d_1 \<in> X" and a3: "x_d_2 \<in> X"
  shows 
   "f\<cdot>x_d_1 = f\<cdot>x_d_2 \<Leftrightarrow> x_d_1 = x_d_2"
  by (auto simp add: tinj_inj [OF a1 a2 a3])

lemma tinj_unique:
  assumes
    a1: "f \<in> X \<zinj> Y"
  shows
    "(x \<mapsto> y) \<in> f \<Leftrightarrow> x \<in> X \<and> y = f\<cdot>x"
  apply (rule tfun_unique)
  apply (rule tinj_tfun [OF a1])
  done

lemma tinj_f_inv_f_beta:
  assumes
    a1: "f \<in> X \<zinj> Y" and
    a2: "a \<in> X"
  shows
    "(f\<^sup>\<sim>)\<cdot>(f\<cdot>a) = a"
  apply (rule tinj_inv_beta [OF a1])
  apply (rule tinj_appl [OF a1 a2])
  done

lemma tinj_f_f_inv_beta:
  assumes
    a1: "f \<in> X \<zinj> Y" and
    a2: "a \<in> \<zran> f"
  shows
    "f\<cdot>((f\<^sup>\<sim>)\<cdot>a) = a"
  apply (rule tinj_beta [OF a1])
  apply (rule pfun_appl [OF tinj_inv_pfun [OF a1], simplified Z_inverse_mem Z_inverse_dom, OF a2])
  done

lemma tinj_Image_inj_iff:
  assumes
    a1: "f \<in> X \<zinj> Y"
  shows
    "f\<zlImg>U\<zrImg> = f\<zlImg>V\<zrImg> \<Leftrightarrow> U \<inter> X = V \<inter> X"
  apply (simp add: tfun_Image_conv [OF a1 [THEN tinj_tfun]]) 
  apply (auto)+
proof -
  assume
    b1: "{ x | x \<in> X \<and> x \<in> U \<bullet> f\<cdot>x } = { x | x \<in> X \<and> x \<in> V \<bullet> f\<cdot>x }" 
{
  fix
    x
  assume
    b2: "x \<in> U" and
    b3: "x \<in> X"
  from b2 b3 have
    "f\<cdot>x \<in> { x | x \<in> X \<and> x \<in> U \<bullet> f\<cdot>x }"
    by (auto)
  with b1 have
    "f\<cdot>x \<in> { x | x \<in> X \<and> x \<in> V \<bullet> f\<cdot>x }"
    by (simp)
  then obtain x' where
    b4: "x' \<in> X \<and> x' \<in> V \<and> f\<cdot>x = f\<cdot>x'"
    by (auto)
  with b2 b3 have
    "x = x'"
    by (auto intro!: tinj_inj [OF a1])
  with b4 show
    "x \<in> V"
    by (auto)
next
  fix
    x
  assume
    b2: "x \<in> V" and
    b3: "x \<in> X"
  from b2 b3 have
    "f\<cdot>x \<in> { x | x \<in> X \<and> x \<in> V \<bullet> f\<cdot>x }"
    by (auto)
  with b1 have
    "f\<cdot>x \<in> { x | x \<in> X \<and> x \<in> U \<bullet> f\<cdot>x }"
    by (simp)
  then obtain x' where
    b4: "x' \<in> X \<and> x' \<in> U \<and> f\<cdot>x = f\<cdot>x'"
    by (auto)
  with b2 b3 have
    "x = x'"
    by (auto intro!: tinj_inj [OF a1])
  with b4 show
    "x \<in> U"
    by (auto)
}
qed

subsection {* Partial surjections *}

lemma in_psurjI: 
  "\<lbrakk> f \<in> X \<zpfun> Y; \<zran> f = Y \<rbrakk> \<turnstile> f \<in> X \<zpsurj> Y"
  by (simp add: part_surjs_def)

lemma psurj_pfun [intro]: 
  "f \<in> X \<zpsurj> Y \<turnstile> f \<in> X \<zpfun> Y"
  by (auto simp add: part_surjs_def)

lemma DR_psurjI: 
  assumes 
    a1: "functional f" and
    a2: "\<zdom> f \<subseteq> X" and a3: "\<zran> f = Y"
  shows "f \<in> X \<zpsurj> Y"
  using a1 a2 a3
  by (auto simp add: fun_space_defs)

lemma psurj_functional: 
  "f \<in> X \<zpsurj> Y \<turnstile> functional f"
  by (auto simp add: fun_space_defs)

lemma psurj_dom: 
  "f \<in> X \<zpsurj> Y \<turnstile> \<zdom> f \<subseteq> X"
  by (auto simp add: fun_space_defs)

lemma psurj_ran: 
  "f \<in> X \<zpsurj> Y \<turnstile> \<zran> f = Y"
  by (auto simp add: fun_space_defs)

lemma psurj_appl:
  assumes 
    a1: "f \<in> X \<zpsurj> Y" and a2: "x \<in> \<zdom> f"
  shows 
    "(x \<mapsto> f\<cdot>x) \<in> f"
  by (rule pfun_appl [OF psurj_pfun [OF a1] a2])

lemma psurj_beta:
  assumes 
    a1: "f \<in> X \<zpsurj> Y" and a2: "(x \<mapsto> y) \<in> f"
  shows 
    "f\<cdot>x = y"
  by (rule pfun_beta [OF psurj_pfun [OF a1] a2])

lemma Z_psurj_left_inv: 
   "f \<in> X \<zpsurj> Y \<turnstile> f\<^sup>\<sim> \<zfcomp> f = \<zid> Y"
proof -
  assume 
    a1: "f \<in> X \<zpsurj> Y"
  then have 
    a2: "f \<in> X \<zpfun> Y" 
    by (rule psurj_pfun)
  then have a3: 
    "f \<in> X \<zrel> Y" 
    by (rule pfun_rel) 
  from a3 [THEN Z_pfun_left_inv] a2 have 
    "f\<^sup>\<sim> \<zfcomp> f 
     = \<zid> (\<zran> f)"
    by (auto)
  also from a1 have 
    "\<zran> f 
    = Y"
    by (auto simp add: part_surjs_def)
  finally show ?thesis by this
qed

lemma psurj_surjE:
  assumes 
    a1: "f \<in> X \<zpsurj> Y" and
    a2: "y \<in> Y" and
    a3: "(\<And> x \<bullet> \<lbrakk> x \<in> X; f\<cdot>x = y \<rbrakk> \<turnstile> R)"
  shows
    "R"
  using psurj_ran [OF a1] psurj_dom [OF a1] psurj_beta [OF a1] a2 a3
  by (auto)


subsection {* Total surjections *}

lemma in_tsurjI: 
  "\<lbrakk> f \<in> X \<zpsurj> Y; f \<in> X \<ztfun> Y \<rbrakk> \<turnstile> f \<in> X \<zsurj> Y"
  by (simp add: total_surjs_def)

lemma in_tsurjIa: 
  "\<lbrakk> f \<in> X \<zpfun> Y; \<zdom> f = X; \<zran> f = Y \<rbrakk> \<turnstile> f \<in> X \<zsurj> Y"
  by (auto intro: in_tsurjI in_psurjI in_tfunI)

lemma in_tsurjIb: 
  "\<lbrakk> f \<in> X \<ztfun> Y; \<zran> f = Y \<rbrakk> \<turnstile> f \<in> X \<zsurj> Y"
  by (auto intro: in_tsurjI in_psurjI)

lemma tsurj_tfun [intro]: 
  "f \<in> X \<zsurj> Y \<turnstile> f \<in> X \<ztfun> Y"
  by (auto simp add: total_surjs_def)

lemma tsurj_psurj [intro]: 
  "f \<in> X \<zsurj> Y \<turnstile> f \<in> X \<zpsurj> Y"
  by (auto simp add: total_surjs_def)

lemma DR_tsurjI: 
  assumes 
    a1: "functional f" and
    a2: "\<zdom> f = X" and a3: "\<zran> f = Y"
  shows "f \<in> X \<zsurj> Y"
  using a1 a2 a3
  by (auto simp add: fun_space_defs)

lemma tsurj_functional: 
  "f \<in> X \<zsurj> Y \<turnstile> functional f"
  by (auto simp add: fun_space_defs)

lemma tsurj_dom: 
  "f \<in> X \<zsurj> Y \<turnstile> \<zdom> f = X"
  by (auto simp add: fun_space_defs)

lemma tsurj_ran: 
  "f \<in> X \<zsurj> Y \<turnstile> \<zran> f = Y"
  by (auto simp add: fun_space_defs)

lemma tsurj_appl:
  assumes 
    a1: "f \<in> X \<zsurj> Y" and a2: "x \<in> X"
  shows 
    "(x \<mapsto> f\<cdot>x) \<in> f"
  by (rule tfun_appl [OF tsurj_tfun [OF a1] a2])

lemma tsurj_beta:
  assumes 
    a1: "f \<in> X \<zsurj> Y" and a2: "(x \<mapsto> y) \<in> f"
  shows 
   "f\<cdot>x = y"
  by (rule tfun_beta [OF tsurj_tfun [OF a1] a2])

lemma tsurj_range [intro]: 
  assumes 
    a1: "f \<in> X \<zsurj> Y" and
    a2: "x \<in> X" 
  shows 
    "f\<cdot>x \<in> Y"
proof -
  from a1 a2 have 
    a3: "(x \<mapsto> f\<cdot>x) \<in> f" 
    by (rule tsurj_appl)
  from a1 have 
    a4: "f \<in> X \<zrel> Y" 
    by (auto)
  from a3 a4 show 
    ?thesis 
    by (auto simp add: rel_def)
qed


lemma tsurj_surjE:
  assumes 
    a1: "f \<in> X \<zsurj> Y" and
    a2: "y \<in> Y" and
    a3: "(\<And> x \<bullet> \<lbrakk> x \<in> X; f\<cdot>x = y \<rbrakk> \<turnstile> R)"
  shows
    "R"
  using tsurj_ran [OF a1] tsurj_dom [OF a1] tsurj_beta [OF a1] a2 a3
  by (auto)

subsection {* Bijections *}

lemma in_bijI: 
  "\<lbrakk> f \<in> X \<zinj> Y; f \<in> X \<zsurj> Y \<rbrakk> \<turnstile> f \<in> X \<zbij> Y"
  by (auto simp add: bijs_def)

lemma in_bijIa: 
  "\<lbrakk> f \<in> X \<zpinj> Y; \<zdom> f = X; \<zran> f = Y \<rbrakk> \<turnstile> f \<in> X \<zbij> Y"
  by (auto intro: in_bijI in_tinjIa in_tsurjIa)

lemma bij_tinj [intro]: 
  "f \<in> X \<zbij> Y \<turnstile> f \<in> X \<zinj> Y"
  by (auto simp add: bijs_def)

lemma bij_tsurj [intro]: 
  "f \<in> X \<zbij> Y \<turnstile> f \<in> X \<zsurj> Y"
  by (auto simp add: bijs_def)

lemma bij_rel:
  assumes
    a1: "f \<in> X \<zbij> Y"
  shows
    "f \<in> X \<zrel> Y"
  using a1
  by (auto simp add: fun_space_defs)

lemma DR_bijI: 
  assumes 
    a1: "functional f" "functional (f\<^sup>\<sim>)" and
    a2: "\<zdom> f = X" and a3: "\<zran> f = Y"
  shows "f \<in> X \<zbij> Y"
  using a1 a2 a3
  by (auto simp add: fun_space_defs)

lemma bij_functional: 
  "f \<in> X \<zbij> Y \<turnstile> functional f"
  by (auto simp add: fun_space_defs)

lemma bij_inv_functional: 
  "f \<in> X \<zbij> Y \<turnstile> functional (f\<^sup>\<sim>)"
  by (auto simp add: fun_space_defs)

lemma bij_dom: 
  "f \<in> X \<zbij> Y \<turnstile> \<zdom> f = X"
  by (auto simp add: fun_space_defs)

lemmas bij_dom_mem = tinj_dom_mem [OF bij_tinj]

lemma bij_ran: 
  "f \<in> X \<zbij> Y \<turnstile> \<zran> f = Y"
  by (auto simp add: fun_space_defs)

lemmas bij_ran_mem = tinj_ran_mem [OF bij_tinj]

lemma bij_appl:
  assumes 
    a1: "f \<in> X \<zbij> Y" and a2: "x \<in> X"
  shows 
    "(x \<mapsto> f\<cdot>x) \<in> f"
  by (rule tinj_appl [OF bij_tinj [OF a1] a2])

lemma bij_beta:
  assumes 
    a1: "f \<in> X \<zbij> Y" and a2: "(x \<mapsto> y) \<in> f"
  shows 
    "f\<cdot>x = y"
  by (rule tinj_beta [OF bij_tinj [OF a1] a2])

lemma bij_range [intro]: 
  assumes 
    a1: "f \<in> X \<zbij> Y" and
    a2: "x \<in> X" 
  shows "f\<cdot>x \<in> Y"
proof -
  from a1 a2 have 
    a3: "(x \<mapsto> f\<cdot>x) \<in> f" 
    by (rule bij_appl)
  from a1 have 
    a4: "f \<in> X \<zrel> Y" 
    by (auto)
  from a3 a4 show 
    ?thesis 
    by (auto simp add: rel_def)
qed

lemma bij_inv_tinj [intro]: 
  assumes 
    a1: "f \<in> X \<zbij> Y"
  shows 
    "f\<^sup>\<sim> \<in> Y \<zinj> X"
  apply (rule DR_tinjI)
  using a1
  apply (auto simp add: fun_space_defs Z_inverse_idem Z_inverse_dom Z_inverse_ran)
  done

lemma bij_inv_tsurj [intro]: 
  assumes 
    a1: "f \<in> X \<zbij> Y"
  shows 
    "f\<^sup>\<sim> \<in> Y \<zsurj> X"
  apply (rule DR_tsurjI)
  using a1
  apply (auto simp add: fun_space_defs Z_inverse_idem Z_inverse_dom Z_inverse_ran)
  done

lemma Z_bij_tfun_inv_tinj:
  "f \<in> X \<zbij> Y \<Leftrightarrow> f \<in> X \<ztfun> Y \<and> f\<^sup>\<sim> \<in> Y \<zinj> X"
  apply auto
  apply (rule DR_bijI)
  apply (rule tfun_functional [where ?X = "X" and ?Y = "Y"])
  apply (simp_all add: total_funs_def)
  apply (auto simp add: fun_space_defs)
  done

lemma bij_tinj_inv_tinj:
  "f \<in> X \<zbij> Y \<Leftrightarrow> f \<in> X \<zinj> Y \<and> f\<^sup>\<sim> \<in> Y \<zinj> X"
  by (auto simp add: fun_space_defs)

lemma bij_tsurj_inv_tsurj:
  "f \<in> X \<zbij> Y \<Leftrightarrow> f \<in> X \<zsurj> Y \<and> f\<^sup>\<sim> \<in> Y \<zsurj> X"
  by (auto simp add: fun_space_defs)

lemma bij_tfun_inv_tfun:
  "f \<in> X \<zbij> Y \<Leftrightarrow> f \<in> X \<ztfun> Y \<and> f\<^sup>\<sim> \<in> Y \<ztfun> X"
  by (auto simp add: fun_space_defs)

lemma bij_inv_appl:
  assumes 
    a1: "f \<in> X \<zbij> Y" and a2: "x \<in> X"
  shows 
    "(f\<cdot>x \<mapsto> x) \<in> f\<^sup>\<sim>"
  using a1 a2
  by (simp add: converse_def bij_appl)
(*
lemma bij_inv_appl':
  assumes 
    a1: "f \<in> X \<zbij> Y" and a2: "y \<in> Y"
  shows 
    "(y \<mapsto> (f\<^sup>\<sim>)\<cdot>y) \<in> f\<^sup>\<sim>"
  apply (rule functional_appl)
  apply (rule bij_inv_functional [OF a1]) 
  using a2
  apply (simp add: converse_def bij_ran [OF a1, symmetric] Range_def)
  done
*)
lemma bij_inv_beta:
  assumes 
    a1: "f \<in> X \<zbij> Y" and a2: "(x \<mapsto> y) \<in> f"
  shows 
    "(f\<^sup>\<sim>)\<cdot>y = x"
  apply (rule tinj_beta [OF bij_inv_tinj [OF a1]])
  using a1 a2
  apply (simp add: converse_def)
  done

lemma bij_inv_range [intro]: 
  assumes 
    a1: "f \<in> X \<zbij> Y" and
    a2: "y \<in> Y" 
  shows "(f\<^sup>\<sim>)\<cdot>y \<in> X"
  apply (rule tinj_range)
  apply (rule bij_inv_tinj [OF a1])
  apply (rule a2)
  done

lemma bij_inj: 
  assumes 
    a1: "f \<in> X \<zbij> Y" and
    a2: "x_d_1 \<in> X" and a3: "x_d_2 \<in> X" and
    a4: "f\<cdot>x_d_1 = f\<cdot>x_d_2"
  shows "x_d_1 = x_d_2"
proof -
  have 
    "x_d_1 
    = (f\<^sup>\<sim>)\<cdot>(f\<cdot>x_d_1)"
    apply (rule sym)
    apply (rule bij_inv_beta [OF a1])
    apply (rule bij_appl [OF a1 a2])
    done
  also from a4 have "\<dots> 
    = (f\<^sup>\<sim>)\<cdot>(f\<cdot>x_d_2)" 
    by (simp)
  also have "\<dots> 
    = x_d_2"
    apply (rule bij_inv_beta [OF a1])
    apply (rule bij_appl [OF a1 a3])
    done
  finally show 
    ?thesis 
    by this
qed

lemmas bij_inj_iff = tinj_inj_iff [OF bij_tinj]

lemmas bij_inv_inj_iff = tinj_inj_iff [OF bij_inv_tinj]

lemmas bij_f_inv_f_beta = tinj_f_inv_f_beta [OF bij_tinj]

lemma bij_f_f_inv_beta:
  assumes
    a1: "f \<in> X \<zbij> Y" and
    a2: "a \<in> Y"
  shows
    "f\<cdot>((f\<^sup>\<sim>)\<cdot>a) = a"
  using a1 a2 tinj_f_f_inv_beta [OF bij_tinj, OF a1]
  by (auto simp add: bij_ran)

lemma bij_surjE:
  assumes 
    a1: "f \<in> X \<zbij> Y" and
    a2: "y \<in> Y" and
    a3: "(\<And> x \<bullet> \<lbrakk> x \<in> X; f\<cdot>x = y \<rbrakk> \<turnstile> R)"
  shows
    "R"
  using bij_ran [OF a1] bij_dom [OF a1] bij_beta [OF a1] a2 a3
  by (auto)

lemma bij_unique:
  assumes
    a1: "f \<in> X \<zbij> Y"
  shows
    "(x \<mapsto> y) \<in> f \<Leftrightarrow> x \<in> X \<and> y = f\<cdot>x \<and> y \<in> Y \<and> x = (f\<^sup>\<sim>)\<cdot>y"
  using bij_tinj [OF a1, THEN tinj_unique, symmetric] bij_inv_tinj [OF a1, THEN tinj_unique, symmetric]
  by (auto)

subsection {* Determining function space properties *}

text {*

Establishing function space claims about graphs is an important part of
reasoning obout them, so we introduce a collection of introduction
and destruction rules to automate this as much as possible.
We base the rule set on the @{text functional}, @{text "\<zdom>"} and
@{text "\<zran>"} operators. That is, the aim of the reasoning approach is to
translated functiona space claims into claims about the functionality, domain, 
and range of relations.

*}


(*
ML {

Simplifier.simp_modifiers

}

ML {

signature FSPACE_SETUP =
sig
  val fspace_tac : claset -> simpset -> tactic 
  val get_fs : Context.generic -> claset
  val setup : theory -> theory
end;

structure FSpace_Setup : FSPACE_SETUP = 
struct

structure FSset = Generic_Data(
  type T = claset;

  val empty = empty_cs;
  val extend = I;
  val merge = merge_cs;
 ); 

val get_fs = FSset.get;
val put_fs = FSset.put;
val map_fs = FSset.map;

val fsintroN = "fsintro";
val fselimN = "fselim";
val fsdelN = "fsdel";

fun attrib f = Thm.declaration_attribute (fn th => (map_fs (f th)));
val FS_Sintro = attrib (fn thm => fn cs => cs addSIs [thm]);
val FS_Selim = attrib (fn thm => fn cs => cs addSEs [thm]);
val FS_intro = attrib (fn thm => fn cs => cs addIs [thm]);
val FS_elim = attrib (fn thm => fn cs => cs addEs [thm]);
val FS_del = attrib (fn thm => fn cs => cs delrules [thm]);

val attrib_setup = 
  Attrib.setup (Binding.name fsintroN) (Scan.lift (Args.bang >> K FS_Sintro || Scan.succeed FS_intro)) "declaration of function space introduction rules" #>
  Attrib.setup (Binding.name fselimN) (Scan.lift (Args.bang >> K FS_Selim || Scan.succeed FS_elim)) "declaration of function space elimination rules" #>
  Attrib.setup (Binding.name fsdelN) (Scan.succeed FS_del) "remove of function space rules"

fun print_fs ctxt = 
let 
  val cs = get_fs (Context.Proof ctxt)
in
  print_cs cs
end;

val _ =
  Outer_Syntax.improper_command "print_fspaceset" "print context of fspace" 
    Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o
      Toplevel.keep (print_fs o Toplevel.context_of)));

fun fspace_tac cs ss = 
  auto_tac (cs, ss);

fun fspace_meth ctxt = Method.METHOD (fn facts =>
  (ALLGOALS (Method.insert_tac (facts)) THEN
  fspace_tac (get_fs (Context.Proof ctxt)) (Simplifier.simpset_of ctxt)));

val simpN = "simp"

val FS_modifiers =
 Simplifier.simp_modifiers @
 [Args.$$$ fselimN -- Args.bang_colon >> K ((I, FS_Selim): Method.modifier),
  Args.$$$ fselimN -- Args.colon >> K (I, FS_elim),
  Args.$$$ fsintroN -- Args.bang_colon >> K (I, FS_Sintro),
  Args.$$$ fsintroN -- Args.colon >> K (I, FS_intro),
  Args.del -- Args.colon >> K (I, FS_del)];

val FS_method = Method.sections FS_modifiers >> K fspace_meth;

val setup = 
  attrib_setup #> 
  Method.setup @{binding "fspace"} FS_method "functional space infernce"

end;

}

setup {* FSpace_Setup.setup *}
*)

declare_mprover "fspace"

declaration {*

K (MProver.map_cs "inference" (fn cs => #2 (("inference", cs) maddSafter ("use_assumptions", (eresolve_tac [impE, allE] THEN' assume_tac))))) 

*}


text {*

Having setup a framework for automatically establishing
function space claims, we must now populate it with a suitable
collection of inference rules.

*}

lemma dr_relI [mintro!(fspace)]:
  assumes 
    a1: "\<zdom> R \<subseteq> X" "\<zran> R \<subseteq> Y"
  shows 
    "R \<in> X \<zrel> Y"
  using a1
  by (auto simp add: rel_def)

lemma dr_relE [melim!(fspace)]:
  assumes 
    a1: "R \<in> X \<zrel> Y" and
    a2: "\<lbrakk> \<zdom> R \<subseteq> X; \<zran> R \<subseteq> Y \<rbrakk> \<turnstile> P"
  shows 
    "P"
  using a1 a2
  by (auto simp add: rel_def)

lemma dr_pfunI [mintro!(fspace)]:
  assumes
    a1: "functional f" and
    a2: "\<zdom> f \<subseteq> X" and a3: "\<zran> f \<subseteq> Y"
  shows 
    "f \<in> X \<zpfun> Y"
  using a1 a2 a3
  by (auto intro: in_relI simp add: part_funs_def)

lemma dr_pfunE [melim!(fspace)]:
  assumes 
    a1: "f \<in> X \<zpfun> Y" and
    a2: "\<lbrakk> functional f; \<zdom> f \<subseteq> X; \<zran> f \<subseteq> Y \<rbrakk> \<turnstile> R"
  shows 
    "R"
  using a1 a2
  by (auto simp add: part_funs_def rel_def)

lemma dr_pfunD1: 
  "f \<in> X \<zpfun> Y \<turnstile> functional f"
  by (auto simp add: part_funs_def)

lemma dr_pfunD2: 
  "f \<in> X \<zpfun> Y \<turnstile> \<zdom> f \<subseteq> X"
  by (auto simp add: part_funs_def rel_def)

lemma dr_pfunD3: 
  "f \<in> X \<zpfun> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto simp add: part_funs_def rel_def)

lemma dr_tfunI [mintro!(fspace)]:
  assumes
    a1: "functional f" and
    a2: "\<zdom> f = X" and a3: "\<zran> f \<subseteq> Y"
  shows 
    "f \<in> X \<ztfun> Y"
  using a1 a2 a3
  by (auto intro: dr_pfunI simp add: total_funs_def)

lemma dr_tfunE [melim!(fspace)]:
  assumes 
    a1: "f \<in> X \<ztfun> Y" and
    a2: "\<lbrakk> functional f; \<zdom> f = X; \<zran> f \<subseteq> Y \<rbrakk> \<turnstile> R"
  shows 
    "R"
  using a1 a2
  by (auto simp add: fun_space_defs)

lemma dr_tfunD1: 
  "f \<in> X \<ztfun> Y \<turnstile> functional f"
  by (auto simp add: total_funs_def part_funs_def)

lemma dr_tfunD2: 
  "f \<in> X \<ztfun> Y \<turnstile> \<zdom> f = X"
  by (auto simp add: total_funs_def)

lemma dr_tfunD3: 
  "f \<in> X \<ztfun> Y \<turnstile> \<zdom> f \<subseteq> X"
  by (auto simp add: total_funs_def)

lemma dr_tfunD4: 
  "f \<in> X \<ztfun> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto simp add: total_funs_def part_funs_def rel_def)

lemma dr_pinjI [mintro!(fspace)]:
  assumes 
    a1: "functional f" "functional (f\<^sup>\<sim>)" and
    a2: "\<zdom> f \<subseteq> X" "\<zran> f \<subseteq> Y"
  shows 
    "f \<in> X \<zpinj> Y"
  using a1 a2
  by (auto intro: dr_pfunI simp add: part_injs_def)

lemma dr_pinjE [melim!(fspace)]:
  assumes 
    a1: "f \<in> X \<zpinj> Y" and
    a2: "\<lbrakk> functional f; functional (f\<^sup>\<sim>); \<zdom> f \<subseteq> X; \<zran> f \<subseteq> Y \<rbrakk> \<turnstile> R"
  shows 
    "R"
  using a1 a2
  by (auto simp add: fun_space_defs)

lemma dr_pinjD1: 
  "f \<in> X \<zpinj> Y \<turnstile> functional f"
  by (auto simp add: part_injs_def part_funs_def)

lemma dr_pinjD2: 
  "f \<in> X \<zpinj> Y \<turnstile> functional (f\<^sup>\<sim>)"
  by (auto simp add: part_injs_def part_funs_def)

lemma dr_pinjD3: 
  "f \<in> X \<zpinj> Y \<turnstile> \<zdom> f \<subseteq> X"
  by (auto simp add: part_injs_def part_funs_def rel_def)

lemma dr_pinjD4: 
  "f \<in> X \<zpinj> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto simp add: part_injs_def part_funs_def rel_def)

lemma dr_tinjI [mintro!(fspace)]:
  assumes 
    a1: "functional f" "functional (f\<^sup>\<sim>)" and
    a2: "\<zdom> f = X" "\<zran> f \<subseteq> Y"
  shows 
    "f \<in> X \<zinj> Y"
  using a1 a2
  by (auto intro: dr_pfunI dr_tfunI simp add: total_injs_def part_injs_def)

lemma dr_tinjE [melim!(fspace)]:
  assumes 
    a1: "f \<in> X \<zinj> Y" and
    a2: "\<lbrakk> functional f; functional (f\<^sup>\<sim>); \<zdom> f = X; \<zran> f \<subseteq> Y \<rbrakk> \<turnstile> R"
  shows 
    "R"
  using a1 a2
  by (auto simp add: fun_space_defs)

lemma dr_tinjD1: 
  "f \<in> X \<zinj> Y \<turnstile> functional f"
  by (auto dest: dr_pinjD1 simp add: total_injs_def)

lemma dr_tinjD2: 
  "f \<in> X \<zinj> Y \<turnstile> functional (f\<^sup>\<sim>)"
  by (auto dest: dr_pinjD2 simp add: total_injs_def)

lemma dr_tinjD3: 
  "f \<in> X \<zinj> Y \<turnstile> \<zdom> f = X"
  by (auto dest: dr_tfunD2 simp add: total_injs_def)

lemma dr_tinjD4: 
  "f \<in> X \<zinj> Y \<turnstile> \<zdom> f \<subseteq> X"
  by (auto dest: dr_tfunD3 simp add: total_injs_def)

lemma dr_tinjD5: 
  "f \<in> X \<zinj> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto dest: dr_tfunD4 simp add: total_injs_def)

lemma dr_psurjI [mintro!(fspace)]:
  assumes 
    a1: "functional f" and
    a2: "\<zdom> f \<subseteq> X" and a3: "\<zran> f = Y"
  shows "f \<in> X \<zpsurj> Y"
  using a1 a2 a3
  by (auto intro: dr_pfunI simp add: part_surjs_def)

lemma dr_psurjE [melim!(fspace)]:
  assumes 
    a1: "f \<in> X \<zpsurj> Y" and
    a2: "\<lbrakk> functional f; \<zdom> f \<subseteq> X; \<zran> f = Y \<rbrakk> \<turnstile> R"
  shows 
    "R"
  using a1 a2
  by (auto simp add: fun_space_defs)

lemma dr_psurjD1: 
  "f \<in> X \<zpsurj> Y \<turnstile> functional f"
  by (auto dest: dr_pfunD1 simp add: part_surjs_def)

lemma dr_psurjD2: 
  "f \<in> X \<zpsurj> Y \<turnstile> \<zdom> f \<subseteq> X"
  by (auto dest: dr_pfunD2 simp add: part_surjs_def)

lemma dr_psurjD3: 
  "f \<in> X \<zpsurj> Y \<turnstile> \<zran> f = Y"
  by (auto simp add: part_surjs_def)

lemma dr_psurjD4: 
  "f \<in> X \<zpsurj> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto dest: dr_pfunD3 simp add: part_surjs_def)

lemma dr_tsurjI [mintro!(fspace)]:
  assumes 
    a1: "functional f" and
    a2: "\<zdom> f = X" and a3: "\<zran> f = Y"
  shows 
    "f \<in> X \<zsurj> Y"
  using a1 a2 a3
  by (auto intro: dr_psurjI dr_tfunI simp add: total_surjs_def)

lemma dr_tsurjE [melim!(fspace)]:
  assumes 
    a1: "f \<in> X \<zsurj> Y" and
    a2: "\<lbrakk> functional f; \<zdom> f = X; \<zran> f = Y \<rbrakk> \<turnstile> R"
  shows 
    "R"
  using a1 a2
  by (auto simp add: fun_space_defs)

lemma dr_tsurjD1: 
  "f \<in> X \<zsurj> Y \<turnstile> functional f"
  by (auto dest: dr_psurjD1 simp add: total_surjs_def)

lemma dr_tsurjD2: 
  "f \<in> X \<zsurj> Y \<turnstile> \<zdom> f = X"
  by (auto dest: dr_tfunD2 simp add: total_surjs_def)

lemma dr_tsurjD3: 
  "f \<in> X \<zsurj> Y \<turnstile> \<zdom> f \<subseteq> X"
  by (auto dest: dr_tfunD3 simp add: total_surjs_def)

lemma dr_tsurjD4: 
  "f \<in> X \<zsurj> Y \<turnstile> \<zran> f = Y"
  by (auto dest: dr_psurjD3 simp add: total_surjs_def)

lemma dr_tsurjD5: 
  "f \<in> X \<zsurj> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto dest: dr_psurjD4 simp add: total_surjs_def)

lemma dr_bijI [mintro!(fspace)]:
  assumes 
    a1: "functional f" "functional (f\<^sup>\<sim>)"  and
    a2: "\<zdom> f = X" "\<zran> f = Y"
  shows 
    "f \<in> X \<zbij> Y"
  using a1 a2
  by (auto intro: dr_tinjI dr_tsurjI simp add: bijs_def)

lemma dr_bijE [melim!(fspace)]:
  assumes 
    a1: "f \<in> X \<zbij> Y" and
    a2: "\<lbrakk> functional f; functional (f\<^sup>\<sim>); \<zdom> f = X; \<zran> f = Y \<rbrakk> \<turnstile> R"
  shows 
    "R"
  using a1 a2
  by (auto simp add: fun_space_defs)


lemma dr_bijD1: 
  "f \<in> X \<zbij> Y \<turnstile> functional f"
  by (auto dest: dr_tinjD1 simp add: bijs_def)

lemma dr_bijD2: 
  "f \<in> X \<zbij> Y \<turnstile> functional (f\<^sup>\<sim>)"
  by (auto dest: dr_tinjD2 simp add: bijs_def)

lemma dr_bijD3: 
  "f \<in> X \<zbij> Y \<turnstile> \<zdom> f = X"
  by (auto dest: dr_tsurjD2 simp add: bijs_def)

lemma dr_bijD4: 
  "f \<in> X \<zbij> Y \<turnstile> \<zdom> f \<subseteq> X"
  by (auto dest: dr_tsurjD3 simp add: bijs_def)

lemma dr_bijD5: 
  "f \<in> X \<zbij> Y \<turnstile> \<zran> f = Y"
  by (auto dest: dr_tsurjD4 simp add: bijs_def)

lemma dr_bijD6: 
  "f \<in> X \<zbij> Y \<turnstile> \<zran> f \<subseteq> Y"
  by (auto dest: dr_tsurjD5 simp add: bijs_def)

declare
  in_relI [mintro!(fspace)] in_relE [melim!(fspace)]
  subset_refl [mintro(fspace)] subset_trans [mintro(fspace)]

lemmas dr_intros =
  in_relI dr_pfunI dr_tfunI dr_pinjI dr_tinjI dr_psurjI dr_tsurjI dr_bijI

lemmas dr_elims =
  in_relE dr_pfunE dr_tfunE dr_pinjE dr_tinjE dr_psurjE dr_tsurjE dr_bijE

lemmas dr_dests =
  in_relD1 in_relD2
  dr_pfunD1 dr_pfunD2 dr_pfunD3
  dr_tfunD1 dr_tfunD2 dr_tfunD3 dr_tfunD4
  dr_pinjD1 dr_pinjD2 dr_pinjD3 dr_pinjD4
  dr_tinjD1 dr_tinjD2 dr_tinjD3 dr_tinjD4 dr_tinjD5
  dr_psurjD1 dr_psurjD2 dr_psurjD3 dr_psurjD4
  dr_tsurjD1 dr_tsurjD2 dr_tsurjD3 dr_tsurjD4 dr_tsurjD5
  dr_bijD1 dr_bijD2 dr_bijD3 dr_bijD4 dr_bijD5 dr_bijD6

lemmas dr_simps =
  dr_tfunD2 dr_tinjD3 dr_psurjD3 dr_tsurjD2 dr_tsurjD4
  dr_bijD3 dr_bijD5

section {* Relational operations *}

subsection {* Union and intersection *}

lemma inter_functionalL [mintro(fspace)]:
  assumes 
    a1: "functional (\<zdom> g \<zdres> f)"
  shows 
    "functional (f \<inter> g)"
  apply (rule functional_subset [OF a1])
  apply (auto simp add: dres_mem)
  done

lemma inter_functionalR [mintro(fspace)]:
  assumes 
    a1: "functional (\<zdom> f \<zdres> g)"
  shows 
    "functional (f \<inter> g)"
  apply (rule functional_subset [OF a1])
  apply (auto simp add: dres_mem)
  done

lemma inter_functional1:
  assumes 
    a1: "functional f"
  shows 
    "functional (f \<inter> g)"
  using a1
  by (auto elim!: functionalE intro!: functionalI)

lemma inter_functional2:
  assumes 
    a1: "functional g"
  shows 
    "functional (f \<inter> g)"
  using a1
  by (auto elim!: functionalE intro!: functionalI)

lemma inter_in_pfun:
  assumes 
    a1: "f \<in> X \<zpfun> Y" "g \<in> X \<zpfun> Y" 
  shows 
    "f \<inter> g \<in> X \<zpfun> Y"
  using a1
  apply (mauto(fspace))
(* J:
  Here want to be able to blow away the "trivials" left by the following
    apply (mauto(fspace) mintro: inter_functional1)
  Note: remainder blown away by  Domain restriction rules
*)
  apply (auto intro: inter_functional1)
  done

lemma Z_inter_in_pfun:
  "f \<in> X \<zpfun> Y \<and> g \<in> X \<zpfun> Y \<Rightarrow> f \<inter> g \<in> X \<zpfun> Y"
by (mauto(inference) mintro: inter_in_pfun)
(*J: improved!
  apply (msafe(inference))
  apply (auto intro: inter_in_pfun)
  done
*)

lemma Z_inter_in_pinj:
  "f \<in> X \<zpinj> Y \<and> g \<in> X \<zpinj> Y \<Rightarrow> f \<inter> g \<in> X \<zpinj> Y"
  apply (msafe(inference))
  apply (rule in_pinjI)
  apply (rule inter_in_pfun)
  apply (auto intro: pinj_pfun)
  apply (auto simp add: fun_space_defs single_val_def Domain_def functional_def)
  done
(*J:
Why doesn't it apply the in_pinjI!?
  apply (mauto(inference) mintro: in_pinjI inter_in_pfun pinj_pfun msimp add:  fun_space_defs single_val_def Domain_def functional_def)

*)
(*
print_mclasimpset "fspace"
lemma junk: "False = True"
sorry
thm junk[THEN eq_reflection]
declare junk[msimp(fspace)];
print_mclasimpset "fspace"
declare junk[THEN eq_reflection, msimp(fspace)];
print_mclasimpset "fspace"
*)

lemma inter_in_tsurjL:
  assumes
    a1: "\<zdom> g \<zdres> f \<in> X \<zsurj> Y" and
    a2: "X \<zdres> f = X \<zdres> g"
  shows 
    "f \<inter> g \<in> X \<zsurj> Y"
(*J:
  Here is using the hyps_subs_tac ... so, better than no_assms!
*)
  using a1 a2
  apply (mauto(fspace) msimp add: Z_dres_dom)
  apply (simp_all add: set_eq_iff dres_mem)
  apply (auto simp add: dres_mem Domain_iff Range_iff)
  done

lemma inter_in_tsurjR:
  assumes
    a1: "\<zdom> f \<zdres> g \<in> X \<zsurj> Y" and
    a2: "X \<zdres> g = X \<zdres> f"
  shows 
    "f \<inter> g \<in> X \<zsurj> Y"
  using a1 a2
  apply (mauto(fspace) msimp add: Z_dres_dom)
  apply (simp_all add: set_eq_iff dres_mem)
  apply (auto simp add: dres_mem Domain_def Range_def)
  done

lemma union_functional [mintro!(fspace)]:
  assumes 
    a1: "functional f" and 
    a2: "functional g" and
    a3: "(\<zdom> g \<zdres> f) = (\<zdom> f \<zdres> g)" 
  shows 
   "functional (f \<union> g)" 
proof -
  have "f \<union> g 
  = ((\<zdom> g \<zdres> f) \<union> (\<zdom> g \<zdsub> f)) \<union> g"
    by (simp add: Z_dpart_rel)
  also have "\<dots> 
  = ((\<zdom> g \<zdres> f) \<union> (\<zdom> g \<zdsub> f)) \<union> ((\<zdom> f \<zdres> g) \<union> (\<zdom> f \<zdsub> g))"
    by (simp add: Z_dpart_rel)
  also from a3 have "\<dots> 
  = (\<zdom> g \<zdsub> f) \<union> (\<zdom> f \<zdres> g) \<union> (\<zdom> f \<zdsub> g)"
    by (auto)
  finally have a4: "f \<union> g
  = (\<zdom> g \<zdsub> f) \<union> (\<zdom> f \<zdres> g) \<union> (\<zdom> f \<zdsub> g)"
    by (this)
  from a1 a2
  have a5: "functional ((\<zdom> g \<zdsub> f) \<union> (\<zdom> f \<zdres> g) \<union> (\<zdom> f \<zdsub> g))"
    by (auto simp add: functional_def single_val_def dres_def dsub_def Domain_def)
  with a4 show "?thesis" by (simp)
qed
 
lemma union_in_pfun:
  assumes 
    a1: "f \<in> X \<zpfun> Y" and a2: "g \<in> X \<zpfun> Y" and
    a3: "disjoint (\<zdom> f) (\<zdom> g)"
  shows 
    "f \<union> g \<in> X \<zpfun> Y"
proof (rule in_pfunI)
  from a1 a2 show "f \<union> g \<in> X \<zrel> Y"
    by (auto simp add: fun_space_defs)
next
  fix x y_d_1 y_d_2
  assume 
    a4: "(x \<mapsto> y_d_1) \<in> f \<union> g" and a5: "(x \<mapsto> y_d_2) \<in> f \<union> g"
  show 
    "y_d_1 = y_d_2"
  proof (cases "x \<in> \<zdom> f" type: bool)
    assume 
      b1: "x \<in> \<zdom> f"
    with a3 have 
      b2: "x \<notin> \<zdom> g" by (auto simp add: disjoint_def)
    from b1 b2 a4 have 
      b3: "(x \<mapsto> y_d_1) \<in> f"  by (auto)
    from b1 b2 a5 have 
      b4: "(x \<mapsto> y_d_2) \<in> f"  by (auto)
    from b3 b4 a1 a2 show 
      "y_d_1 = y_d_2" 
      by (auto simp add: fun_space_defs)
  next
    assume 
      b1: "x \<notin> \<zdom> f"
    with a3 a4 have 
      b2: "x \<in> \<zdom> g" 
      by (auto)
    from b1 b2 a4 have 
      b3: "(x \<mapsto> y_d_1) \<in> g"  
      by (auto)
    from b1 b2 a5 have 
      b4: "(x \<mapsto> y_d_2) \<in> g"  
      by (auto)
    from b3 b4 a1 a2 show 
      "y_d_1 = y_d_2" 
      by (auto simp add: fun_space_defs)
  qed
qed

lemma Z_union_in_pfun:
  "f \<in> X \<zpfun> Y \<and> g \<in> X \<zpfun> Y \<and> disjoint (\<zdom> f) (\<zdom> g) \<Rightarrow> f \<union> g \<in> X \<zpfun> Y"
by (mauto(inference) mintro: union_in_pfun)
(*J: improved!
  apply (msafe(inference))
  apply (intro union_in_pfun)
  apply simp_all
  done
*)

lemma union_in_tsurj:
  assumes 
    a1: "f1 \<in> X1 \<zsurj> Y1" and
    a2: "f2 \<in> X2 \<zsurj> Y2" and
    a3: "(\<zdom> f2 \<zdres> f1) = (\<zdom> f1 \<zdres> f2)" and
    a4: "X1 \<union> X2 = X" and
    a5: "Y1 \<union> Y2 = Y"
 shows
    "f1 \<union> f2 \<in> X \<zsurj> Y"
 apply (subst a4 [symmetric])
 apply (subst a5 [symmetric])
 using a1 a2 a3
 apply (mauto(fspace) msimp add: set_eq_iff)
(*J: small improved?
 apply (fspace)
 apply (simp add: set_eq_iff)
 apply (auto simp add: dres_mem)
*)
 done

lemma union_in_tsurj_disj:
  assumes 
    a1: "f1 \<in> X1 \<zsurj> Y1" and
    a2: "f2 \<in> X2 \<zsurj> Y2" and
    a3: "disjoint X1 X2" and
    a4: "X1 \<union> X2 = X" and
    a5: "Y1 \<union> Y2 = Y"
 shows
    "f1 \<union> f2 \<in> X \<zsurj> Y"
 apply (rule union_in_tsurj [OF a1 a2 _ a4 a5])
 using a3 tsurj_dom [OF a1, symmetric] tsurj_dom [OF a2, symmetric]
 apply (auto simp add: dres_mem disjoint_def)
 apply (auto simp add: set_eq_iff)
 done

lemma Z_subset_in_pfun:
  "f \<in> X \<zpfun> Y \<and> g \<subseteq> f \<Rightarrow> g \<in> X \<zpfun> Y"
proof (msafe(inference))
  assume 
    a1: "f \<in> X \<zpfun> Y" and 
    a2: "g \<subseteq> f"
  have 
    a3: "\<zdom> g \<subseteq> X"
  proof -
   from a2 have 
     "\<zdom> g
     \<subseteq> \<zdom> f" 
     by auto
   also have "\<dots> 
     \<subseteq> X" 
     by (rule in_relD1 [OF pfun_rel [OF a1]])
   finally show 
     ?thesis 
     by this
  qed
  have 
    a4: "\<zran> g \<subseteq> Y"
  proof -
    from a2 have 
      "\<zran> g 
      \<subseteq> \<zran> f" 
      by auto
    also have "\<dots> 
      \<subseteq> Y" 
      by (rule in_relD2 [OF pfun_rel [OF a1]])
    finally show 
      ?thesis 
      by this
  qed
  have 
    a5: "functional g" 
    by (rule functional_subset [OF pfun_functional [OF a1] a2])
  from a1 a2 a3 a4 a5 show 
    "g \<in> X \<zpfun> Y"
    by (msafe(fspace))
qed

lemma Z_subset_in_pinj:
  "f \<in> X \<zpinj> Y \<and> g \<subseteq> f \<Rightarrow> g \<in> X \<zpinj> Y"
proof (msafe(inference), rule in_pinjI)
  assume 
    b0: "f \<in> X \<zpinj> Y" and b1: "g \<subseteq> f"
  from pinj_pfun [OF b0] have 
    b0': "f \<in> X \<zpfun> Y" 
    by this
  with Z_subset_in_pfun [rule_format] b1 show 
    "g \<in> X \<zpfun> Y" 
    by auto

  fix x_d_1 x_d_2 y
  assume 
    b3: "(x_d_1, y) \<in> g" and b4: "(x_d_2, y) \<in> g"
  from b3 b1 have 
    b5: "(x_d_1, y) \<in> f" 
    by auto
  from b4 b1 have 
    b6: "(x_d_2, y) \<in> f" 
    by auto
  from b5 b6 b0 b0' show 
    "x_d_1 = x_d_2" 
    by (auto simp add: fun_space_defs)
qed

lemma union_in_pinj:
  assumes 
    a1: "f \<in> X \<zpinj> Y" and a2: "g \<in> X \<zpinj> Y" and
    a3: "disjoint (\<zdom> f) (\<zdom> g)" and a4: "disjoint (\<zran> f) (\<zran> g)"
  shows 
    "f \<union> g \<in> X \<zpinj> Y"
proof (rule in_pinjI)
  from a1 a2 a3 show 
    "f \<union> g \<in> X \<zpfun> Y"
    by (auto intro!: union_in_pfun)
next 
  fix y x_d_1 x_d_2
  assume 
    a5: "(x_d_1 \<mapsto> y) \<in> f \<union> g" and a6: "(x_d_2 \<mapsto> y) \<in> f \<union> g"
  show 
    "x_d_1 = x_d_2"
  proof (cases "y \<in> \<zran> f" type: bool)
    assume 
      b1: "y \<in> \<zran> f"
    with a4 have 
      b2: "y \<notin> \<zran> g" 
      by (auto simp add: disjoint_def)
    from b1 b2 a5 have 
      b3: "(x_d_1 \<mapsto> y) \<in> f"  
      by (auto)
    from b1 b2 a6 have
      b4: "(x_d_2 \<mapsto> y) \<in> f"  
      by (auto)
    from b3 b4 a1 a2 show 
      "x_d_1 = x_d_2" 
      by (auto simp add: fun_space_defs)
  next
    assume 
      b1: "y \<notin> \<zran> f"
    with a4 a5 have 
      b2: "y \<in> \<zran> g" 
      by (auto)
    from b1 b2 a5 have 
      b3: "(x_d_1 \<mapsto> y) \<in> g"  
      by (auto)
    from b1 b2 a6 have 
      b4: "(x_d_2 \<mapsto> y) \<in> g"  
      by (auto)
    from b3 b4 a1 a2 show 
      "x_d_1 = x_d_2" 
      by (auto simp add: fun_space_defs)
  qed
qed

lemma rel_union_beta1p:
  assumes 
    a1: "functional (f \<union> g)"
  shows 
    "(f \<union> g)\<cdot>x = \<if> x \<in> \<zdom> f \<then> f\<cdot>x \<else> g\<cdot>x \<fi>"
  apply (cases "x \<in> \<zdom> (f \<union> g)")
  apply (cases "x \<in> \<zdom> f")
proof -
  apply_end (simp add: Z_rel_union_dom)
  assume 
    a2: "x \<in> \<zdom> f"
  show 
    "(f \<union> g)\<cdot>x = f\<cdot>x"
  proof (rule functional_beta [OF a1])
    from a1 have 
      b1: "functional f"
      by (auto simp add: functional_def single_val_def Z_rel_union_dom)
    from b1 a2 have 
      "(x \<mapsto> f\<cdot>x) \<in> f"
      by (rule functional_appl)
    then show 
      "(x \<mapsto> f\<cdot>x) \<in> (f \<union> g)"
      by (auto)
  qed
next
  apply_end (simp add: Z_rel_union_dom)
  assume 
    a2: "x \<in> \<zdom> g"
  show 
    "(f \<union> g)\<cdot>x = g\<cdot>x"
  proof (rule functional_beta [OF a1])
    from a1 have 
      b1: "functional g"
      by (auto simp add: functional_def single_val_def Z_rel_union_dom)
    from b1 a2 have 
      "(x \<mapsto> g\<cdot>x) \<in> g"
      by (rule functional_appl)
    then show 
      "(x \<mapsto> g\<cdot>x) \<in> (f \<union> g)"
      by (auto)
  qed
next
  assume 
    a2: "x \<notin> \<zdom> (f \<union> g)"
  then show 
    ?thesis
    by (simp add: undef_beta [OF a2] undef_beta Z_rel_union_dom)
qed

lemma rel_union_beta1':
  assumes 
    a1: "functional (f \<union> g)" and a2: "x \<in> \<zdom> f"
  shows 
    "(f \<union> g)\<cdot>x = f\<cdot>x"
  using a1 a2
  by (simp add: rel_union_beta1p)

lemma rel_union_beta2p:
  assumes 
    a1: "functional (f \<union> g)"
  shows 
    "(f \<union> g)\<cdot>x = \<if> x \<in> \<zdom> g \<then> g\<cdot>x \<else> f\<cdot>x \<fi>"
  apply (cases "x \<in> \<zdom> (f \<union> g)")
  apply (cases "x \<in> \<zdom> g")
proof -
  apply_end (simp add: Z_rel_union_dom)
  assume 
    a2: "x \<in> \<zdom> g"
  show 
    "(f \<union> g)\<cdot>x = g\<cdot>x"
  proof (rule functional_beta [OF a1])
    from a1 have 
      b1: "functional g"
      by (auto simp add: functional_def single_val_def Z_rel_union_dom)
    from b1 a2 have 
      "(x \<mapsto> g\<cdot>x) \<in> g"
      by (rule functional_appl)
    then show 
      "(x \<mapsto> g\<cdot>x) \<in> (f \<union> g)"
      by (auto)
  qed
next
  apply_end (simp add: Z_rel_union_dom)
  assume 
    a2: "x \<in> \<zdom> f"
  show 
    "(f \<union> g)\<cdot>x = f\<cdot>x"
  proof (rule functional_beta [OF a1])
    from a1 have 
      b1: "functional f"
      by (auto simp add: functional_def single_val_def Z_rel_union_dom)
    from b1 a2 have 
      "(x \<mapsto> f\<cdot>x) \<in> f"
      by (rule functional_appl)
    then show 
      "(x \<mapsto> f\<cdot>x) \<in> (f \<union> g)"
      by (auto)
  qed
next
  assume 
    a2: "x \<notin> \<zdom> (f \<union> g)"
  then show 
    ?thesis
    by (simp add: undef_beta [OF a2] undef_beta Z_rel_union_dom)
qed

lemma rel_union_beta2':
  assumes 
    a1: "functional (f \<union> g)" and a2: "x \<in> \<zdom> g"
  shows 
    "(f \<union> g)\<cdot>x = g\<cdot>x"
  using a1 a2
  by (simp add: rel_union_beta2p)

lemma rel_union_beta1n:
  assumes 
    a1: "functional (f \<union> g)"
  shows 
    "(f \<union> g)\<cdot>x = \<if> x \<notin> \<zdom> g \<then> f\<cdot>x \<else> g\<cdot>x \<fi>"
  apply (simp)
  apply (msafe(inference))
  apply (cases "x \<in> \<zdom> (f \<union> g)")
  using a1
  apply (simp add: Z_rel_union_dom rel_union_beta1p)
  using a1
  apply (simp_all add: Z_rel_union_dom rel_union_beta2p)
  done

lemma rel_union_beta2n:
  assumes 
    a1: "functional (f \<union> g)"
  shows 
    "(f \<union> g)\<cdot>x = \<if> x \<notin> \<zdom> f \<then> g\<cdot>x \<else> f\<cdot>x \<fi>"
  apply (simp)
  apply (msafe(inference))
  apply (cases "x \<in> \<zdom> (f \<union> g)")
  using a1
  apply (simp add: Z_rel_union_dom rel_union_beta2p)
  using a1
  apply (simp_all add: Z_rel_union_dom rel_union_beta1p)
  done
  
lemma rel_union_functionalD1:
  assumes
    a1: "functional (f \<union> g)"
  shows
    "functional f"
  using a1
  by (auto simp add: functional_def single_val_def Z_rel_union_dom)

lemma rel_union_functionalD2:
  assumes
    a1: "functional (f \<union> g)"
  shows
    "functional g"
  using a1
  by (auto simp add: functional_def single_val_def Z_rel_union_dom)

lemma rel_Union_functionalD:
  assumes
    a1: "functional (\<Union>F)" and
    a2: "f \<in> F"
  shows
    "functional f"
  using a1 a2
  by (auto simp add: functional_def single_val_def rel_Union_dom)

lemma rel_Union_functional:
  assumes 
    a1: "\<And> f \<bullet> f \<in> F \<turnstile> functional f" and
    a2: "\<And> f g \<bullet> \<lbrakk> f \<in> F; g \<in> F \<rbrakk> \<turnstile> (\<zdom> g) \<zdres> f = (\<zdom> f) \<zdres> g"
  shows 
    "functional (\<Union>F)"
  apply (rule functionalI)
  apply (auto)
proof -
  fix f g x y_d_1 y_d_2
  assume 
    b1: "f \<in> F" and b2: "g \<in> F" and b3: "(x \<mapsto> y_d_1) \<in> f" and b4: "(x \<mapsto> y_d_2) \<in> g"  
  from a2 [OF b1 b2] b3 b4 [THEN DomainI] have 
    b5: "(x \<mapsto> y_d_1) \<in> g"
    by (auto simp add: dres_def set_eq_def)
  from a1 [OF b2] b5 b4 show 
    "y_d_1 = y_d_2"
    by (rule functionalD)
qed

lemma disj_rel_Union_functional:
  assumes 
    a1: "\<And> f \<bullet> f \<in> F \<turnstile> functional f" and
    a2: "\<And> f g \<bullet> \<lbrakk> f \<in> F; g \<in> F; f \<noteq> g \<rbrakk> \<turnstile> disjoint (\<zdom> g) (\<zdom> f)"
  shows 
    "functional (\<Union>F)"
  apply (rule rel_Union_functional)
  apply (rule a1, assumption)
proof -
  fix
    f g
  assume
    b1: "f \<in> F" and
    b2: "g \<in> F"
  then show
    "(\<zdom> g) \<zdres> f = (\<zdom> f) \<zdres> g"
    apply (cases "g = f")
    apply (simp)
    apply (rule trans [OF dres_elim' dres_elim' [symmetric]])
    apply (rule a2, assumption+)
    apply (rule a2, assumption+)
    apply (auto)
    done
qed

lemma rel_Union_functional':
  assumes 
    a1: "\<And> x \<bullet> p x \<turnstile> functional (F x)" and
    a2: "\<And> x y \<bullet> \<lbrakk> p x; p y \<rbrakk> \<turnstile> (\<zdom> (F y)) \<zdres> (F x) = (\<zdom> (F x)) \<zdres> (F y)"
  shows 
    "functional (\<Union> x | p x \<bullet> F x)"
  apply (rule rel_Union_functional)
  using a1 a2
  apply (auto)
  done

lemma rel_Union_functional'':
  assumes 
    a1: "\<And> x \<bullet> functional (F x)" and
    a2: "\<And> x y \<bullet> (\<zdom> (F y)) \<zdres> (F x) = (\<zdom> (F x)) \<zdres> (F y)"
  shows 
    "functional (\<Union> x \<bullet> F x)"
  apply (rule rel_Union_functional)
  using a1 a2
  apply (auto)
  done

lemma disj_rel_Union_functional':
  assumes 
    a1: "\<And> x \<bullet> b x \<turnstile> functional (f x)" and
    a2: "\<And> x y \<bullet> \<lbrakk> b x; b y; x \<noteq> y \<rbrakk> \<turnstile> disjoint (\<zdom> (f x)) (\<zdom> (f y))"
  shows 
    "functional (\<Union> x | b x \<bullet> f x)"
  apply (rule disj_rel_Union_functional)
  using a1 a2
  apply (auto del: DomainE)
  done

lemma disj_rel_Union_functional'':
  assumes 
    a1: "\<And> x \<bullet> functional (f x)" and
    a2: "\<And> x y \<bullet> x \<noteq> y \<turnstile> disjoint (\<zdom> (f x)) (\<zdom> (f y))"
  shows 
    "functional (\<Union> x \<bullet> f x)"
  apply (rule disj_rel_Union_functional)
  apply (simp_all)
  apply (msafe(inference))
  apply (simp_all)
  apply (intro a1 a2)+
  apply (auto)
  done

lemma rel_Union_beta:
  assumes 
    a1: "functional (\<Union>F)" and a2: "f \<in> F" and a3: "x \<in> \<zdom> f"
  shows 
    "(\<Union>F)\<cdot>x = f\<cdot>x"
proof (rule functional_beta [OF a1])
  from a1 a2 have 
    b1: "functional f"
    by (auto intro: functional_subset)
  from b1 a3 have 
    "(x \<mapsto> f\<cdot>x) \<in> f"
    by (rule functional_appl)
  with a2 show 
    "(x \<mapsto> f\<cdot>x) \<in> (\<Union>F)"
    by (auto)
qed

subsection {* Identity and composition *}

lemma id_functional [mintro!(fspace)]: 
  "functional (\<zid> S)"
  by (auto elim: RangeE DomainE simp add: rel_id_def functional_def single_val_def)

lemma id_conv_functional [mintro!(fspace)]: 
  "functional ((\<zid> S)\<^sup>\<sim>)"
  by (auto elim: RangeE DomainE simp add: rel_id_def functional_def single_val_def)

lemma id_dom:
  "\<zdom> (\<zid> S) = S"
  by (auto elim: RangeE DomainE simp add: rel_id_def)

lemma id_ran: 
  "\<zran> (\<zid> S) = S"
  by (auto elim: RangeE DomainE simp add: rel_id_def)

lemma Z_id_pinj [intro]: 
  "S \<subseteq> X \<turnstile> \<zid> S \<in> X \<zpinj> X"
  by (auto simp add: fun_space_defs rel_id_def)

lemma Z_id_bij [intro]: 
  "\<zid> X \<in> X \<zbij> X"
  by (auto simp add: fun_space_defs rel_id_def)

lemma id_beta:
  assumes 
    a1: "x \<in> X"
  shows 
    "(\<zid> X)\<cdot>x = x"
proof (rule pfun_beta)
  show 
    "(\<zid> X) \<in> X \<zpfun> X"
    by (auto)
  show 
    "(x \<mapsto> x) \<in> (\<zid> X)"
    by (auto simp add: rel_id_def a1)
qed

lemma bcomp_functional [mintro!(fspace)]:
  assumes 
    a1: "functional f" and a2: "functional g"
  shows 
    "functional (g \<zbcomp> f)"
proof (auto intro!: functionalI simp add: rel_bcomp_def)
  fix x y_d_1 y_d_2 z_d_1 z_d_2
  assume 
    a3: "(x \<mapsto> y_d_1) \<in> f" and a4: "(x \<mapsto> y_d_2) \<in> f" and
    a5: "(y_d_1 \<mapsto> z_d_1) \<in> g" and a6: "(y_d_2 \<mapsto> z_d_2) \<in> g"
  from a1 a3 a4 have 
    a7: "y_d_1 = y_d_2"
    by (auto elim!: functionalE)
  with a5 have 
    a8: "(y_d_2 \<mapsto> z_d_1) \<in> g" 
    by (simp)
  with a2 a6 show 
    "z_d_1 = z_d_2" 
    by (auto elim!: functionalE)
qed

lemma bcomp_conv_functional [mintro(fspace)]:
  assumes 
    a1: "functional (f\<^sup>\<sim>)" and a2: "functional (g\<^sup>\<sim>)"
  shows 
    "functional ((g \<zbcomp> f)\<^sup>\<sim>)"
  using a1 a2
  by (simp add: Z_inverse_rel_bcomp, msafe(fspace))
(*J: wouldn't apply previous theorem under msafeif it wasn't added with (mintro!)  !!!?????
BUT would do
  apply (mforce(fspace))
  by (simp add: Z_inverse_rel_bcomp, msafe(fspace))
*)

lemma bcomp_dom [mintro(fspace)]:
  "\<zdom> (g \<zbcomp> f) \<subseteq> \<zdom> f"
  by (auto simp add: rel_bcomp_def Range_def Domain_def)

lemma bcomp_dom2 [mintro(fspace)]:
  assumes 
    a1: "\<zran> f \<subseteq> \<zdom> g"
  shows 
    "\<zdom> (g \<zbcomp> f) = \<zdom> f"
proof (auto simp add: rel_bcomp_def rel_fcomp_def Range_iff Domain_iff)
  fix x y
  assume 
    b1: "(x \<mapsto> y) \<in> f"
  then have 
    "y \<in> \<zran> f" 
    by (auto)
  with a1 have 
    b2: "y \<in> \<zdom> g" 
    by (auto)
  then have 
    "\<exists> z \<bullet> (y \<mapsto> z) \<in> g" 
    by (auto)
  with b1 have 
    b3: "(\<exists> z \<bullet> (x \<mapsto> y) \<in> f \<and> (y \<mapsto> z) \<in> g)" 
    by (auto)
  then show 
    "(\<exists> z y \<bullet> (x \<mapsto> y) \<in> f \<and> (y \<mapsto> z) \<in> g)" 
    by (auto)
qed

lemma bcomp_ran [mintro(fspace)]:
  "\<zran> (g \<zbcomp> f) \<subseteq> \<zran> g"
  by (auto simp add: rel_bcomp_def rel_fcomp_def)

lemma bcomp_ran2 [mintro(fspace)]:
  assumes 
    a1: "\<zdom> g \<subseteq> \<zran> f"
  shows 
    "\<zran> (g \<zbcomp> f) = \<zran> g"
proof (auto simp add: rel_bcomp_def rel_fcomp_def Range_iff Domain_iff)
  fix y z
  assume 
    b1: "(y \<mapsto> z) \<in> g"
  then have 
    "y \<in> \<zdom> g" 
    by (auto)
  with a1 have 
    b2: "y \<in> \<zran> f" 
    by (auto)
  then have 
    "(\<exists> x \<bullet> (x \<mapsto> y) \<in> f)" 
    by (auto)
  with b1 have 
    b3: "(\<exists> x \<bullet> (x \<mapsto> y) \<in> f \<and> (y \<mapsto> z) \<in> g)" 
    by (auto)
  then show 
    "(\<exists> x y \<bullet> (x \<mapsto> y) \<in> f \<and> (y \<mapsto> z) \<in> g)" 
    by (auto)
qed

lemma fcomp_functional [mintro(fspace)]:
  assumes 
    a1: "functional f" and a2: "functional g"
  shows 
    "functional (f\<zfcomp> g)"
  using a1 a2
  apply (simp add: rel_fcomp_def)
  apply (msafe(fspace))
  done
  
lemma bcomp_in_pfunI [intro]: 
  assumes a1: "f \<in> X \<zpfun> Y" and a2: "g \<in> Y \<zpfun> Z"
  shows "g \<zbcomp> f \<in> X \<zpfun> Z"
proof (rule in_pfunI)
  show 
    "g \<zbcomp> f \<in> X \<zrel> Z"
    by (rule bcomp_in_relI, rule a1 [THEN pfun_rel], rule a2 [THEN pfun_rel])
  
  fix x z_d_1 z_d_2
  assume a3: "(x \<mapsto> z_d_1) \<in> g \<zbcomp> f" and a4: "(x \<mapsto> z_d_2) \<in> g \<zbcomp> f"
  from a1 a2 
  have a5: "functional (g \<zbcomp> f)"
    by (msafe(fspace))
  from a5 a3 a4 show 
    "z_d_1 = z_d_2"
    by (simp add: functional_unique)
qed

lemma Z_bcomp_in_pfunI:
  shows "f \<in> X \<zpfun> Y \<and> g \<in> Y \<zpfun> Z \<Rightarrow> g \<zbcomp> f \<in> X \<zpfun> Z"
by (mauto(inference) mintro: bcomp_in_pfunI)
(*J: simplified!
  apply (msafe(inference))
  apply (rule bcomp_in_pfunI)
  apply simp_all
  done
*)

lemma fcomp_in_pfunI [intro]: 
  "\<lbrakk> f \<in> X \<zpfun> Y; g \<in> Y \<zpfun> Z \<rbrakk> \<turnstile> f \<zfcomp> g \<in> X \<zpfun> Z"
  by (auto intro!: bcomp_in_pfunI simp add: rel_fcomp_def)  

lemma bcomp_in_tfunI [intro]: 
  assumes 
    a1: "f \<in> X \<ztfun> Y" and a2: "g \<in> Y \<zpfun> Z" and
    a3: "\<zran> f \<subseteq> \<zdom> g"
  shows "g \<zbcomp> f \<in> X \<ztfun> Z"
proof (rule in_tfunI)
  show 
    "g \<zbcomp> f \<in> X \<zpfun> Z"
    by (rule bcomp_in_pfunI [OF a1 [THEN tfun_pfun] a2])
  have 
    a4: "\<zdom> f = X" 
    by (rule a1 [THEN tfun_dom])
  from a4 show 
    "\<zdom> (g \<zbcomp> f) = X"
  proof (auto)
    fix x y 
    assume 
      b1: "(x \<mapsto> y) \<in> f"
    with a3 have 
      "y \<in> \<zdom> g"
      by (auto)
    with b1 show 
      "x \<in> \<zdom> (g \<zbcomp> f)"
      by (auto simp add: rel_bcomp_def Z_dom_def)
  apply_end (auto simp add: rel_bcomp_def)
  qed
qed

lemma Z_bcomp_in_tfunI:
  "f \<in> X \<ztfun> Y \<and> g \<in> Y \<zpfun> Z \<and> \<zran> f \<subseteq> \<zdom> g \<Rightarrow> g \<zbcomp> f \<in> X \<ztfun> Z"
by (mauto(inference) mintro: bcomp_in_tfunI)
(*J: simplified!
  apply inference
  apply (intro bcomp_in_tfunI)
  apply simp_all
  done
*)

lemma fcomp_in_tfunI [intro]: 
  "\<lbrakk> f \<in> X \<ztfun> Y; g \<in> Y \<zpfun> Z; \<zran> f \<subseteq> \<zdom> g \<rbrakk> \<turnstile> f \<zfcomp> g \<in> X \<ztfun> Z"
  by (auto intro!: bcomp_in_tfunI simp add: rel_fcomp_def)  

lemma bcomp_in_tfunI2 [intro]: 
  assumes 
    a1: "f \<in> X \<ztfun> Y" and a2: "g \<in> Y \<ztfun> Z"
  shows 
    "g \<zbcomp> f \<in> X \<ztfun> Z"
proof -
  from a1 a2 have "\<zran> f \<subseteq> \<zdom> g"
    by (auto simp add: Range_iff Domain_iff fun_space_defs)
  with a1 a2 show ?thesis
    by (auto)
qed

lemma fcomp_in_tfunI2 [intro]: 
  "\<lbrakk> f \<in> X \<ztfun> Y; g \<in> Y \<ztfun> Z \<rbrakk> \<turnstile> f \<zfcomp> g \<in> X \<ztfun> Z"
  by (auto intro!: bcomp_in_tfunI2 simp add: rel_fcomp_def)  

lemma Z_bcomp_in_pinjI [intro]:
  "\<lbrakk> f \<in> X \<zpinj> Y; g \<in> Y \<zpinj> Z \<rbrakk> \<turnstile> g \<zbcomp> f \<in> X \<zpinj> Z"
  by (auto simp add: part_injs_def Z_inverse_rel_bcomp)

lemma fcomp_in_pinjI [intro]:
  "\<lbrakk> f \<in> X \<zpinj> Y; g \<in> Y \<zpinj> Z \<rbrakk> \<turnstile> f \<zfcomp> g \<in> X \<zpinj> Z"
  by (auto simp add: part_injs_def converse_rel_fcomp)

lemma bcomp_in_tinjI [intro]:
  "\<lbrakk> f \<in> X \<zinj> Y; g \<in> Y \<zpinj> Z; \<zran> f \<subseteq> \<zdom> g \<rbrakk> \<turnstile> g \<zbcomp> f \<in> X \<zinj> Z"
  by (auto simp add: total_injs_def)

lemma fcomp_in_tinjI [intro]:
  "\<lbrakk> f \<in> X \<zinj> Y; g \<in> Y \<zpinj> Z; \<zran> f \<subseteq> \<zdom> g \<rbrakk> \<turnstile> f \<zfcomp> g \<in> X \<zinj> Z"
  by (auto simp add: total_injs_def)

lemma bcomp_in_tinjI2 [intro]:
  "\<lbrakk> f \<in> X \<zinj> Y; g \<in> Y \<zinj> Z \<rbrakk> \<turnstile> g \<zbcomp> f \<in> X \<zinj> Z"
  by (auto simp add: total_injs_def)

lemma fcomp_in_tinjI2 [intro]:
  "\<lbrakk> f \<in> X \<zinj> Y; g \<in> Y \<zinj> Z \<rbrakk> \<turnstile> f \<zfcomp> g \<in> X \<zinj> Z"
  by (auto simp add: total_injs_def)

lemma bcomp_in_psurjI [intro]:
  "\<lbrakk> f \<in> X \<zpsurj> Y; g \<in> Y \<zpsurj> Z \<rbrakk> \<turnstile> g \<zbcomp> f \<in> X \<zpsurj> Z"
proof (auto simp add: part_surjs_def Z_rel_bcomp_mem)
  fix b c
  assume a1: "f \<in> X \<zpfun> \<zran> f" and
    a2: "g \<in> \<zran> f \<zpfun> \<zran> g" and
    a3: "(b \<mapsto> c) \<in> g"
  from a2 a3 have "b \<in> \<zran> f"
    by (auto simp add: fun_space_defs)
  with a3 show "c \<in> \<zran> (g \<zbcomp> f)"
    by (auto simp add: Range_iff Domain_iff rel_bcomp_def)
qed

lemma fcomp_in_psurjI [intro]:
  "\<lbrakk> f \<in> X \<zpsurj> Y; g \<in> Y \<zpsurj> Z \<rbrakk> \<turnstile> f \<zfcomp> g \<in> X \<zpsurj> Z"
  by (auto simp add: rel_fcomp_def)

lemma bcomp_in_tsurjI [intro]:
  "\<lbrakk> f \<in> X \<zsurj> Y; g \<in> Y \<zsurj> Z \<rbrakk> \<turnstile> g \<zbcomp> f \<in> X \<zsurj> Z"
  by (auto simp add: total_surjs_def)

lemma fcomp_in_tsurjI [intro]:
  "\<lbrakk> f \<in> X \<zsurj> Y; g \<in> Y \<zsurj> Z \<rbrakk> \<turnstile> f \<zfcomp> g \<in> X \<zsurj> Z"
  by (auto simp add: total_surjs_def)

lemma bcomp_in_bijI [intro]:
  "\<lbrakk> f \<in> X \<zbij> Y; g \<in> Y \<zbij> Z \<rbrakk> \<turnstile> g \<zbcomp> f \<in> X \<zbij> Z"
  by (rule in_bijI, auto)

lemma fcomp_in_bijI [intro]:
  "\<lbrakk> f \<in> X \<zbij> Y; g \<in> Y \<zbij> Z \<rbrakk> \<turnstile> f \<zfcomp> g \<in> X \<zbij> Z"
  by (auto simp add: rel_fcomp_def)

lemma bcomp_beta: 
  assumes 
    a1: "f \<in> X \<zpfun> Y" and 
    a2: "g \<in> Y \<zpfun> Z" and
    a3: "x \<in> \<zdom> (g \<zbcomp> f)"
  shows 
    "(g \<zbcomp> f)\<cdot>x = g\<cdot>(f\<cdot>x)"
proof -
  from a3 have 
    a4: "x \<in> \<zdom> f"
    by (auto simp add: inv_def Domain_iff Z_rel_bcomp_mem)
  from a1 a4 have 
    a5: "(x \<mapsto> f\<cdot>x) \<in> f"
    by (rule pfun_appl)
  from a1 a3 a5 have 
    a6: "f\<cdot>x \<in> \<zdom> g"
    by (auto simp add: part_funs_def rel_bcomp_def pfun_beta Z_dom_def)
  from a2 a6 have 
    a7: "(f\<cdot>x \<mapsto> g\<cdot>(f\<cdot>x)) \<in> g"
    by (rule pfun_appl)
  from a5 a7 have 
    a8: "(x \<mapsto> g\<cdot>(f\<cdot>x)) \<in> (g \<zbcomp> f)"
    by (auto simp add: rel_bcomp_def)
  from a1 a2 have 
    a9: "(g \<zbcomp> f) \<in> X \<zpfun> Z"
    by (auto)
  from a9 a8 show 
    "(g \<zbcomp> f)\<cdot>x = g\<cdot>(f\<cdot>x)"
    by (rule pfun_beta)
qed

lemma fcomp_beta: 
  assumes 
    a1: "f \<in> X \<zpfun> Y" "g \<in> Y \<zpfun> Z" and
    a2: "x \<in> \<zdom> (f \<zfcomp> g)"
  shows 
    "(f \<zfcomp> g)\<cdot>x = g\<cdot>(f\<cdot>x)"
  using a1 a2
  by (auto intro!: bcomp_beta simp add: rel_fcomp_def)  

subsection {* Domain and range restriction *}

lemma dres_functional [mintro(fspace)]:
  "functional f \<turnstile> functional (S \<zdres> f)"
  by (auto simp add: dres_def functional_def single_val_def)

lemma rres_functional [mintro(fspace)]:
  "functional f \<turnstile> functional (f \<zrres> S)"
  by (auto simp add: rres_def functional_def single_val_def)

lemma dsub_functional [mintro(fspace)]:
  "functional f \<turnstile> functional (S \<zdsub> f)"
  by (auto simp add: dsub_def functional_def single_val_def)

lemma rsub_functional [mintro(fspace)]:
  "functional f \<turnstile> functional (f \<zrsub> S)"
  by (auto simp add: rsub_def functional_def single_val_def)

lemma dres_in_pfunI [intro]: 
  assumes a1: "f \<in> \<univ> \<zpfun> Y"
  shows "S \<zdres> f \<in> S \<zpfun> Y"
proof (rule in_pfunI)
  from a1 [THEN pfun_rel] show "S \<zdres> f \<in> S \<zrel> Y"
    by (auto simp add: dres_def rel_def)
  fix x y_d_1 y_d_2
  assume a2: "(x \<mapsto> y_d_1) \<in> S \<zdres> f" and a3: "(x \<mapsto> y_d_2) \<in> S \<zdres> f"
  from a2 have a4: "(x \<mapsto> y_d_1) \<in> f" by (auto simp add: dres_def)
  from a3 have a5: "(x \<mapsto> y_d_2) \<in> f" by (auto simp add: dres_def)
  from a1 a4 a5 show "y_d_1 = y_d_2"
    by (auto simp add: fun_space_defs single_val_def)
qed

lemma Z_dres_in_pfunI:
  "f \<in> X \<zpfun> Y \<Rightarrow> S \<zdres> f \<in> X \<zpfun> Y"
  apply (msafe(inference))
  apply (rule in_pfunI)
  apply (insert pfun_rel)
  apply (auto simp add: dres_def rel_def)
  apply (auto simp add: dres_def fun_space_defs single_val_def)
  done

lemma Z_dres_in_pinjI:
  "f \<in> X \<zpinj> Y \<Rightarrow> S \<zdres> f \<in> X \<zpinj> Y"
proof (msafe(inference), intro in_pinjI)
  assume a1: "f \<in> X \<zpinj> Y"
  show "S \<zdres> f \<in> X \<zpfun> Y"
    apply (intro Z_dres_in_pfunI [rule_format])
    apply (rule pinj_pfun [OF a1])
    done
  fix x_d_1 x_d_2 y
  assume b0: "(x_d_1, y) \<in> S \<zdres> f" and b1: "(x_d_2, y) \<in> S \<zdres> f"
  from b0 have b2: "(x_d_1, y) \<in> f" by (auto simp add: dres_def)
  from b1 have b3: "(x_d_2, y) \<in> f" by (auto simp add: dres_def)
  from a1 b2 b3 show "x_d_1 = x_d_2" 
    by (auto simp add: fun_space_defs single_val_def)
qed


lemma rres_in_pfunI [intro]: 
  assumes a1: "f \<in> X \<zpfun> \<univ>"
  shows "f \<zrres> T \<in> X \<zpfun> T"
proof (rule in_pfunI)
  from a1 [THEN pfun_rel] show "f \<zrres> T \<in> X \<zrel> T"
    by (auto simp add: rres_def rel_def)
  fix x y_d_1 y_d_2
  assume a2: "(x \<mapsto> y_d_1) \<in> f \<zrres> T" and a3: "(x \<mapsto> y_d_2) \<in> f \<zrres> T"
  from a2 have a4: "(x \<mapsto> y_d_1) \<in> f" by (auto simp add: rres_def)
  from a3 have a5: "(x \<mapsto> y_d_2) \<in> f" by (auto simp add: rres_def)
  from a1 a4 a5 show "y_d_1 = y_d_2"
    by (auto simp add: fun_space_defs single_val_def)
qed

lemma Z_rres_in_pfunI:
  "f \<in> X \<zpfun> Y \<Rightarrow> f \<zrres> T \<in> X \<zpfun> Y"
  apply (msafe(inference))
  apply (rule in_pfunI)
  apply (insert pfun_rel, auto simp add: rres_def rel_def)
  apply (auto simp add: rres_def fun_space_defs single_val_def)
  done

lemma Z_rres_in_pinjI:
  "f \<in> X \<zpinj> Y \<Rightarrow> f \<zrres> T \<in> X \<zpinj> Y"
proof (msafe(inference), rule in_pinjI)
  assume a1: "f \<in> X \<zpinj> Y"
  show "f \<zrres> T \<in> X \<zpfun> Y" 
    apply (rule Z_rres_in_pfunI [rule_format])
    apply (rule pinj_pfun [OF a1])
    done
  fix x_d_1 x_d_2 y
  assume b0: "(x_d_1, y) \<in> f \<zrres> T" and b1: "(x_d_2, y) \<in> f \<zrres> T"
  from b0 have b2: "(x_d_1, y) \<in> f" by (auto simp add: rres_def)
  from b1 have b3: "(x_d_2, y) \<in> f" by (auto simp add: rres_def)
  from a1 b2 b3 show "x_d_1 = x_d_2" 
    by (auto simp add: fun_space_defs single_val_def)
qed

lemma dres_beta: 
  assumes 
    a1: "x \<in> X"
  shows 
    "(X \<zdres> f)\<cdot>x = f\<cdot>x"
  using a1
  by (simp add: dres_def fun_appl_def)

lemma dres_beta': 
  assumes 
    a1: "x \<in> X" "g = f"
  shows 
    "(X \<zdres> g)\<cdot>x = f\<cdot>x"
  using a1
  by (simp add: dres_def fun_appl_def)

lemma dsub_beta: 
  assumes 
    a1: "x \<notin> X"
  shows 
    "(X \<zdsub> f)\<cdot>x = f\<cdot>x"
  using a1
  by (simp add: dsub_def fun_appl_def)

lemma rel_Union_dres:
  assumes 
     a1: "functional (\<Union>F)" and 
     a2: "f \<in> F" "X = \<zdom> f"
  shows "X \<zdres> (\<Union>F) = f"
  apply (rule functional_eqI)
  apply (rule functional_subset)
  apply (rule a1)
  defer 1
  apply (rule functional_subset)
  apply (rule a1)
  defer 1
  defer 1
  using a1 a2
  apply (simp add: dres_beta Z_dres_dom rel_Union_beta)
  using a1 a2
  apply (auto simp add: dres_def Z_dom_def)+
  done

lemma rel_union_dres1:
  assumes 
    a1: "functional (f \<union> g)"
  shows 
    "(\<zdom> f)\<zdres>(f \<union> g) = f"
proof (rule functional_eqI)
  from a1 show 
    "functional ((\<zdom> f)\<zdres>(f \<union> g))"
    apply (rule functional_subset)
    apply (auto simp add: dres_def)
    done
  from a1 show 
    "functional f"
    apply (rule functional_subset)
    apply (auto simp add: dres_def)
    done
  show 
    b1: "\<zdom> ((\<zdom> f)\<zdres>(f \<union> g)) = \<zdom> f"
    by (auto simp add: Z_dres_dom Z_rel_union_dom)
  fix x assume 
    b2: "x \<in> \<zdom> ((\<zdom> f)\<zdres>(f \<union> g))"
  with b1 have 
    b3: "x \<in> \<zdom> f" by (simp)
  from b3 have 
    "((\<zdom> f)\<zdres>(f \<union> g))\<cdot>x
    = (f \<union> g)\<cdot>x"
    by (rule dres_beta)
  also from a1 b3 have "\<dots> 
    = f\<cdot>x"
    by (simp add: rel_union_beta1p)
  finally show 
    "((\<zdom> f)\<zdres>(f \<union> g))\<cdot>x  = f\<cdot>x"
    by (this)
qed

lemma rel_union_dres1':
  assumes 
    a1: "functional (f \<union> g)" "X = \<zdom> f"
  shows 
    "X\<zdres>(f \<union> g) = f"
  using a1
  by (simp add: rel_union_dres1) 

lemma rel_union_dres2:
  assumes 
    a1: "functional (f \<union> g)"
  shows 
    "(\<zdom> g)\<zdres>(f \<union> g) = g"
proof -
  from rel_union_dres1 [of g f] a1
  show 
    "(\<zdom> g)\<zdres>(f \<union> g) = g"
    by (simp add: Un_commute)
qed

lemma rel_union_dres2':
  assumes 
    a1: "functional (f \<union> g)" "X = \<zdom> g"
  shows 
    "X\<zdres>(f \<union> g) = g"
  using a1
  by (simp add: rel_union_dres2) 

lemma union_functional_char:
  assumes 
    a1: "functional f" and 
    a2: "functional g" 
  shows 
    "functional (f \<union> g) \<Leftrightarrow> (\<zdom> g \<zdres> f) = (\<zdom> f \<zdres> g)" 
proof (rule iffI)
  assume 
    b1: "functional (f \<union> g)"
  have 
    b2: "functional (\<zdom> g \<zdres> f) " "functional (\<zdom> f \<zdres> g)"
    apply (rule dres_functional)   
    apply (rule functional_subset)
    apply (rule b1)
    apply (simp add: subset_def)
    apply (rule dres_functional)   
    apply (rule functional_subset)
    apply (rule b1)
    apply (simp add: subset_def)
    done
  then show 
    "(\<zdom> g \<zdres> f) = (\<zdom> f \<zdres> g)" 
    apply (rule functional_eqI)
    apply (simp_all add: Z_dres_dom set_eq_def dres_beta)
    apply (msafe(inference))
    apply (rule trans)
    apply (rule rel_union_beta1' [THEN sym], rule b1, assumption)
    apply (rule rel_union_beta2', rule b1, assumption)
    done
next
  assume 
    "(\<zdom> g \<zdres> f) = (\<zdom> f \<zdres> g)"
  with a1 a2 show 
    "functional (f \<union> g)"
    by (rule union_functional)
qed

subsection {* Relational converse *}

lemma dres_conv: 
  "(S \<zdres> f)\<^sup>\<sim> = (f\<^sup>\<sim> \<zrres> S)"
  by (simp add: converse_def dres_def rres_def set_eq_def)

lemma dres_conv_functional [mintro(fspace)]:
  "functional (f\<^sup>\<sim>) \<turnstile> functional ((S \<zdres> f)\<^sup>\<sim>)"
  by (simp add: dres_conv, (mauto(fspace)))
(*J:
Note that the msafe doesn't work... need mauto... 
presumably because the rres_functional not mintro! ????
*)

lemma rres_conv: 
  "(f \<zrres> S)\<^sup>\<sim> = (S \<zdres> f\<^sup>\<sim>)"
  by (simp add: converse_def dres_def rres_def set_eq_def)

lemma rres_conv_functional [mintro(fspace)]:
  "functional (f\<^sup>\<sim>) \<turnstile> functional ((f \<zrres> S)\<^sup>\<sim>)"
  by (simp add: rres_conv, (mauto(fspace)))

lemma dsub_conv: "(S \<zdsub> f)\<^sup>\<sim> = (f\<^sup>\<sim> \<zrsub> S)"
  by (simp add: converse_def dsub_def rsub_def set_eq_def)

lemma dsub_conv_functional [mintro(fspace)]:
  "functional (f\<^sup>\<sim>) \<turnstile> functional ((S \<zdsub> f)\<^sup>\<sim>)"
  by (simp add: dsub_conv, (mauto(fspace)))

lemma rsub_conv: 
  "(f \<zrsub> S)\<^sup>\<sim> = (S \<zdsub> f\<^sup>\<sim>)"
  by (simp add: converse_def dsub_def rsub_def set_eq_def)

lemma rsub_conv_functional [mintro(fspace)]:
  "functional (f\<^sup>\<sim>) \<turnstile> functional ((f \<zrsub> S)\<^sup>\<sim>)"
  by (simp add: rsub_conv, (mauto(fspace)))

lemma bij_tfun_conv: 
  "f \<in> X \<zbij> Y \<Leftrightarrow> f \<in> X \<ztfun> Y \<and> f\<^sup>\<sim> \<in> Y \<ztfun> X"
proof (msafe(inference))
  assume 
    a1: "f \<in> X \<zbij> Y"
  from a1 show 
    "f \<in> X \<ztfun> Y" by (rule bij_tinj [THEN tinj_tfun])
  from a1 [THEN bij_tinj, THEN tinj_pinj] have 
    a2: "f\<^sup>\<sim> \<in> Y \<zpfun> X" 
    by (simp add: pinj_inv_pfun)
  from a1 have 
    a3: "\<zdom> (f\<^sup>\<sim>) = Y"
    by (simp add: Z_inverse_dom, rule bij_tsurj [THEN tsurj_psurj [THEN psurj_ran]])
  from a2 a3 show 
    "f\<^sup>\<sim> \<in> Y \<ztfun> X"
    by (auto simp add: total_funs_def)
next
  assume 
    a1: "f \<in> X \<ztfun> Y" and 
    a2: "f\<^sup>\<sim> \<in> Y \<ztfun> X"
  from a1 a2 have 
    "f \<in> X \<zpinj> Y"
    by (auto intro: tfun_pfun simp add: part_injs_def)
  with a1 have 
    a3: "f \<in> X \<zinj> Y"
    by (simp add: total_injs_def)
  from a1 [THEN tfun_pfun] a2 have 
    "f \<in> X \<zpsurj> Y"
    by (auto simp add: part_surjs_def converse_def total_funs_def part_funs_def rel_def)
  with a1 have a4: 
    "f \<in> X \<zsurj> Y"
    by (simp add: total_surjs_def)
  from a3 a4 show 
    "f \<in> X \<zbij> Y" 
    by (simp add: bijs_def)
qed

(*J: renamed to protect the innocent?
lemma bij_conv_bij [intro]: 
*)
lemma bij_inv_bij [intro]: 
  assumes a1: "f \<in> X \<zbij> Y"
  shows "f\<^sup>\<sim> \<in> Y \<zbij> X"
proof -
  from a1 have "True \<Rightarrow> f \<in> X \<ztfun> Y \<and> f\<^sup>\<sim> \<in> Y \<ztfun> X"
    by (simp add: bij_tfun_conv)
  also have "\<dots> 
  \<Rightarrow> (f\<^sup>\<sim>)\<^sup>\<sim> \<in> X \<ztfun> Y \<and> f\<^sup>\<sim> \<in> Y \<ztfun> X"
    by (auto simp add: inv_def)
  also have "\<dots> 
  \<Rightarrow> f\<^sup>\<sim> \<in> Y \<zbij> X"
    by (simp add: bij_tfun_conv)
  finally show ?thesis by (simp)
qed

lemma bij_right_inv:
  assumes a1: "f \<in> X \<zbij> Y" 
  shows "f \<zfcomp> (f\<^sup>\<sim>) = \<zid> X"
proof -
  from a1 have a2: "f\<^sup>\<sim> \<in> Y \<zpsurj> X"
    by (auto)
  then have "((f\<^sup>\<sim>)\<^sup>\<sim>) \<zfcomp> (f\<^sup>\<sim>) = \<zid> X"
    by (rule Z_psurj_left_inv)
  then show ?thesis
    by (simp add: inv_def)
qed

lemma bij_inv_beta1 [simp]:
  assumes a1: "f \<in> X \<zbij> Y" and a2: "y \<in> Y"
  shows "f\<cdot>((f\<^sup>\<sim>)\<cdot>y) = y"
proof -
  have a3: "((f\<^sup>\<sim>) \<zfcomp> f) \<in> Y \<ztfun> Y"
    by (rule fcomp_in_tfunI [of _ Y X], auto intro: a1)
  from a2 a3 have a4: "y \<in> \<zdom> ((f\<^sup>\<sim>) \<zfcomp> f)" 
    by (simp add: tfun_dom)
  have "f\<cdot>((f\<^sup>\<sim>)\<cdot>y) = ((f\<^sup>\<sim>) \<zfcomp> f)\<cdot>y"
    by (rule sym, rule fcomp_beta [of _ Y X _ Y], auto intro: a1 a4)
  also have "((f\<^sup>\<sim>) \<zfcomp> f) = (\<zid> Y)"
    by (rule Z_psurj_left_inv,  auto intro: a1)
  also from a2 have "(\<zid> Y)\<cdot>y = y"
    by (rule id_beta)
  finally show "f\<cdot>((f\<^sup>\<sim>)\<cdot>y) = y" by (this)
qed

lemma bij_inv_beta2 [simp]:
  assumes a1: "f \<in> X \<zbij> Y" and a2: "x \<in> X"
  shows "(f\<^sup>\<sim>)\<cdot>(f\<cdot>x) = x"
proof -
  from a1 have a3: "(f\<^sup>\<sim>) \<in> Y \<zbij> X"
    by (auto)
  from a3 a2 have "(f\<^sup>\<sim>)\<cdot>(((f\<^sup>\<sim>)\<^sup>\<sim>)\<cdot>x) = x"
    by (simp only: bij_inv_beta1)
  also have "((f\<^sup>\<sim>)\<^sup>\<sim>) = f"
    by (simp add: inv_def)
  finally show ?thesis by (this)
qed

lemma bij_inv_appl':
  assumes a1: "f \<in> X \<zbij> Y" and a2: "y \<in> Y"
  shows "((f\<^sup>\<sim>)\<cdot>y \<mapsto> y) \<in> f"
  apply (subst (2) bij_inv_beta1 [symmetric, OF a1 a2])
  apply (rule bij_appl [OF a1])
  apply (rule bij_inv_range [OF a1 a2])
  done    

lemma bij_inv_inj: 
  assumes 
    a1: "f \<in> X \<zbij> Y" and
    a2: "x_d_1 \<in> Y" and a3: "x_d_2 \<in> Y" and
    a4: "(f\<^sup>\<sim>)\<cdot>x_d_1 = (f\<^sup>\<sim>)\<cdot>x_d_2"
  shows "x_d_1 = x_d_2"
proof -
  have 
    "x_d_1 
    = f\<cdot>((f\<^sup>\<sim>)\<cdot>x_d_1)"
    apply (rule sym)
    apply (rule bij_beta [OF a1])
    apply (rule bij_inv_appl' [OF a1 a2])
    done
  also from a4 have "\<dots> 
    = f\<cdot>((f\<^sup>\<sim>)\<cdot>x_d_2)" 
    by (simp)
  also have "\<dots> 
    = x_d_2"
    apply (rule bij_beta [OF a1])
    apply (rule bij_inv_appl' [OF a1 a3])
    done
  finally show 
    ?thesis 
    by this
qed

lemma bij_1to1 [simp]:
  assumes a1: "f \<in> X \<zbij> Y" and a2: "x \<in> X" and a3: "y \<in> X"
  shows "f\<cdot>x = f\<cdot>y \<Leftrightarrow> x = y"
proof (auto)
  assume a4: "f\<cdot>x = f\<cdot>y"
  then have "(f\<^sup>\<sim>)\<cdot>(f\<cdot>x) = (f\<^sup>\<sim>)\<cdot>(f\<cdot>y)"
    by (simp)
  with a1 a2 a3 show "x = y"
    by (simp)
qed

(*J: doesn't work, but anyway is just bij_conv_bij  !!
I'll rename above!  
lemma bij_inv_bij [intro]: 
  assumes 
    a1: "f \<in> X \<zbij> Y"
  shows 
    "f\<^sup>\<sim> \<in> Y \<zbij> X"
  using a1
  apply (msafe_no_assms(fspace))
*)


subsection {* Relational image *}



lemma pinj_image: 
  assumes a1: "f \<in> X \<zpinj> Y" 
  shows "f\<zlImg>S\<zrImg> = {y | y \<in> \<zran> f \<and> (f\<^sup>\<sim>)\<cdot>y \<in> S}"
proof -
  from a1 have a2: "f\<^sup>\<sim> \<in> Y \<zpfun> X" by (rule pinj_inv_pfun)
  have "f\<zlImg>S\<zrImg> = {x y | (x \<mapsto> y) \<in> f \<and> x \<in> S \<bullet> y}"
    by (auto simp add: Image_def)
  also have "\<dots> = {x y | (y \<mapsto> x) \<in> f\<^sup>\<sim> \<and> x \<in> S \<bullet> y}"
    by (auto)
  also have "\<dots> = {x y | (y \<mapsto> x) \<in> f\<^sup>\<sim> \<and> (f\<^sup>\<sim>)\<cdot>y \<in> S \<bullet> y}"
    by (mclarsimp(wind) msimp add: a2 [THEN pfun_beta])
  also have "\<dots> = {y | y \<in> \<zran> f \<and> (f\<^sup>\<sim>)\<cdot>y \<in> S}"
    by (mclarsimp(wind), auto simp add: eind_def)
  finally show ?thesis by this
qed

lemma Z_tinj_image_inter: "f \<in> X \<zpinj> Y \<turnstile> f\<zlImg>S\<zrImg> \<inter> f\<zlImg>T\<zrImg> = f\<zlImg>S \<inter> T\<zrImg>"
proof -
  assume a1: "f \<in> X \<zpinj> Y"
  have "f\<zlImg>S\<zrImg> \<inter> f\<zlImg>T\<zrImg> 
  = {y |  y \<in> \<zran> f \<and> (f\<^sup>\<sim>)\<cdot>y \<in> S} \<inter> {y |  y \<in> \<zran> f \<and> (f\<^sup>\<sim>)\<cdot>y \<in> T}"
    by (simp add: a1 [THEN pinj_image])
  also have "\<dots> 
  = {y |  y \<in> \<zran> f \<and> (f\<^sup>\<sim>)\<cdot>y \<in> S \<and> (f\<^sup>\<sim>)\<cdot>y \<in> T}"
    by (auto)
  also have "\<dots> 
  = f\<zlImg>S \<inter> T\<zrImg>"
    by (simp add: a1 [THEN pinj_image])
  finally show ?thesis by this
qed


subsection {* Relational override *}

lemma rel_oride_functional [mintro!(fspace)]:
  "\<lbrakk> functional (\<zdom> g \<zdsub> f); functional g \<rbrakk> \<turnstile> functional (f \<oplus> g)"
  by (auto simp add: functional_def single_val_def rel_oride_def dsub_def eind_def)

lemma rel_oride_in_pfunI [intro]: 
  assumes a1: "f \<in> X \<zpfun> Y" and a2: "g \<in> X \<zpfun> Y"
  shows "f \<oplus> g \<in> X \<zpfun> Y"
proof (rule in_pfunI)
  from a1 [THEN pfun_rel] a2 [THEN pfun_rel] 
  show "f \<oplus> g \<in> X \<zrel> Y"
    by (auto simp add: rel_oride_def dsub_def rel_def)
  fix x y_d_1 y_d_2
  assume a3: "(x \<mapsto> y_d_1) \<in> f \<oplus> g" and a4: "(x \<mapsto> y_d_2) \<in> f \<oplus> g"
  show "y_d_1 = y_d_2"
  proof (cases "x \<in> \<zdom> g")
    assume b1: "x \<in> \<zdom> g"
    from a3 b1 have b2: "(x \<mapsto> y_d_1) \<in> g" 
      by (auto simp add: rel_oride_def dsub_def)
    from a4 b1 have b3: "(x \<mapsto> y_d_2) \<in> g" 
      by (auto simp add: rel_oride_def dsub_def)
    from a2 b2 b3 show "y_d_1 = y_d_2"
      by (auto simp add: fun_space_defs single_val_def)
  next
    assume b1: "x \<notin> \<zdom> g"
    from a3 b1 have b2: "(x \<mapsto> y_d_1) \<in> f" 
      by (auto simp add: rel_oride_def dsub_def)
    from a4 b1 have b3: "(x \<mapsto> y_d_2) \<in> f" 
      by (auto simp add: rel_oride_def dsub_def)
    from a1 b2 b3 show "y_d_1 = y_d_2"
      by (auto simp add: fun_space_defs single_val_def)
  qed
qed

lemma Z_rel_oride_in_pfunI:
  "f \<in> X \<zpfun> Y \<and> g \<in> X \<zpfun> Y \<Rightarrow> f \<oplus> g \<in> X \<zpfun> Y"
  apply (msafe(inference))
  apply (intro rel_oride_in_pfunI, simp_all)
  done
 
lemma rel_oride_beta:
  "(g \<oplus> f)\<cdot>x = \<if> x \<in> \<zdom> f \<then> f\<cdot>x \<else> g\<cdot>x \<fi>"
proof (cases "x \<in> \<zdom> f", simp_all)
  assume a1: "x \<in> \<zdom> f"
  then have "\<forall> y \<bullet> (x \<mapsto> y) \<in> (g \<oplus> f) \<Leftrightarrow> (x \<mapsto> y) \<in> f"
    by (simp add: rel_oride_def dsub_def)
  then show "(g \<oplus> f)\<cdot>x = f\<cdot>x"
    by (simp add: fun_appl_def)
next
  assume b1: "x \<notin> \<zdom> f"
  then have "\<forall> y \<bullet> (x \<mapsto> y) \<in> (g \<oplus> f) \<Leftrightarrow> (x \<mapsto> y) \<in> g"
    by (auto simp add: rel_oride_def dsub_def Domain_iff)
  then show "(g \<oplus> f)\<cdot>x = g\<cdot>x"
    by (simp add: fun_appl_def)
qed

lemma Z_rel_oride_beta1: 
  assumes a1: "f \<in> X \<zpfun> Y" and a2: "x \<in> \<zdom> f"
  shows "(g \<oplus> f)\<cdot>x = f\<cdot>x"
proof -
  from a1 a2 have a3: "(x \<mapsto> f\<cdot>x) \<in> f"
    by (rule pfun_appl)
  from a1 a2 have a4: "single_val f x" by (simp add: fun_space_defs)
  then have a5: "single_val (g \<oplus> f) x"
    by (auto simp add: single_val_def rel_oride_def Domain_iff dsub_def)
  from a3 have a6: "(x \<mapsto> f\<cdot>x) \<in> (g \<oplus> f)"
    by (auto simp add: rel_oride_def Domain_iff dsub_def)
  from a5 a6 show "(g \<oplus> f)\<cdot>x = f\<cdot>x"
    by (rule single_val_beta)
qed

lemma Z_rel_oride_beta2: 
  assumes a1: "g \<in> X \<zpfun> Y" and a2: "x \<notin> \<zdom> f" and
a3: "x \<in> \<zdom> g"
  shows "(g \<oplus> f)\<cdot>x = g\<cdot>x"
proof -
  from a1 a3 have a4: "(x \<mapsto> g\<cdot>x) \<in> g"
    by (rule pfun_appl)
  from a1 a3 have a5: "single_val g x" by (simp add: fun_space_defs)
  with a2 have a6: "single_val (g \<oplus> f) x"
    by (auto simp add: single_val_def rel_oride_def Domain_iff dsub_def)
  from a4 a2 have a7: "(x \<mapsto> g\<cdot>x) \<in> (g \<oplus> f)"
    by (auto simp add: rel_oride_def Domain_iff dsub_def)
  from a6 a7 show "(g \<oplus> f)\<cdot>x = g\<cdot>x"
    by (rule single_val_beta)
qed

section {* The @{text "\<glambda>"} operator *}

definition
  glambda :: "['a \<rightarrow> (\<bool> \<times> 'b)] \<rightarrow> ('a \<leftrightarrow> 'b)"
where
  glambda_def: "glambda bt \<defs> {x | fst (bt x) \<bullet> (x \<mapsto> snd (bt x))}"

syntax (xsymbols)
  "_Z_Fun\<ZZ>glambda" :: "[pttrn, logic, logic] \<rightarrow> logic" ("\<glambda> _ | _ \<bullet> _" [0, 0, 1] 1)
  "_Z_Fun\<ZZ>glambda1" :: "[pttrn, logic] \<rightarrow> logic" ("\<glambda> _ \<bullet> _" [0, 1] 1)

syntax (zed)
  "_Z_Fun\<ZZ>glambda" :: "[pttrn, logic, logic] \<rightarrow> logic" ("\<glambda> _ | _ \<bullet> _" [0, 0, 1] 1)
  "_Z_Fun\<ZZ>glambda1" :: "[pttrn, logic] \<rightarrow> logic" ("\<glambda> _ \<bullet> _" [0, 1] 1)

translations
  "_Z_Fun\<ZZ>glambda1 x t" \<rightleftharpoons> "_Z_Fun\<ZZ>glambda x (CONST True) t"
  "_Z_Fun\<ZZ>glambda x b t" \<rightleftharpoons> "CONST Z_Fun.glambda (\<olambda> x \<bullet> _tuple b (_tuple_arg t))"
  "_Z_Fun\<ZZ>glambda x b (_tuple t s)" \<leftharpoondown> "CONST Z_Fun.glambda (\<olambda> x \<bullet> _tuple b (_tuple_args t s))"

lemma gbeta': "\<lbrakk> fst (bt e); snd (bt e) = x \<rbrakk> \<turnstile> (glambda bt)\<cdot>e = x"
  by (auto simp add: glambda_def fun_appl_def)

lemma gbeta: "b e \<turnstile> (\<glambda> x | b x \<bullet> t x)\<cdot>e = t e"
  by (auto simp add: glambda_def fun_appl_def)
  
lemma Z_glambda_beta: "b e \<Rightarrow> (\<glambda> x | b x \<bullet> t x)\<cdot>e = t e"
  by (auto simp add: glambda_def fun_appl_def)

lemma glambda_single_val: "b e \<turnstile> single_val (\<glambda> x | b x \<bullet> t x) e"
  by (auto simp add: glambda_def single_val_def)

lemma glambda_mem: "(u \<mapsto> v) \<in> (\<glambda> x | b x \<bullet> t x) \<Leftrightarrow> b u \<and> v = t u"
  by (auto simp add: glambda_def)

lemma Z_glambda_mem: "(u \<zmapsto> v) \<in> (\<glambda> x | b x \<bullet> t x) \<Leftrightarrow> b u \<and> v = t u"
  by (auto simp add: glambda_def)

lemma Z_glambda_def: "(\<glambda> x | b x \<bullet> t x) \<defs> { x | b x \<bullet> (x \<zmapsto> t x) }"
  by (auto simp add: glambda_def)

lemma glambda_appl: "b e \<turnstile> (e \<mapsto> t e) \<in> (\<glambda> x | b x \<bullet> t x)"
  by (auto simp add: glambda_def)

lemmas glambda_beta = gbeta

lemma glambda_unique: "(e \<mapsto> y) \<in> (\<glambda> x | b x \<bullet> t x) \<Leftrightarrow> b e \<and> y = t e"
  by (auto simp add: glambda_def)

lemma glambda_dom: "\<zdom> (\<glambda> x | b x \<bullet> t x) = {x | b x}"
  by (simp add: glambda_def set_eq_def Domain_iff)

lemma glambda_ran: "\<zran> (\<glambda> x | b x \<bullet> t x) = {x | b x \<bullet> t x}"
  by (simp add: glambda_def set_eq_def Domain_iff Range_iff)

lemma glambda_dres: "X \<zdres> (\<glambda> x | b x \<bullet> t x) = (\<glambda> x | b x \<and> x \<in> X \<bullet> t x)"
  by (auto simp add: dres_def glambda_def)

lemma glambda_dsub: "X \<zdsub> (\<glambda> x | b x \<bullet> t x) = (\<glambda> x | b x \<and> x \<notin> X \<bullet> t x)"
  by (auto simp add: dsub_def glambda_def)

lemma glambda_eq: 
  "(\<glambda> x | a x \<bullet> s x) = (\<glambda> x | b x \<bullet> t x)
  \<Leftrightarrow> (\<forall> x \<bullet> (a x \<Leftrightarrow> b x) \<and> (a x \<Rightarrow> s x = t x))"
  by (auto simp add: glambda_def set_eq_def)

lemma glambda_cong [cong]:
  "\<lbrakk> (\<And> x \<bullet> a x \<Leftrightarrow> b x); (\<And> x \<bullet> b x \<turnstile> s x = t x) \<rbrakk> \<turnstile> (\<glambda> x | a x \<bullet> s x) = (\<glambda> x | b x \<bullet> t x)"
  by (auto simp add: glambda_eq glambda_mem)

lemma [mintro!(wind)]: 
  "{x | a x \<bullet> (x \<mapsto> s x)} = {x | b x \<bullet> (x \<mapsto> t x)} 
  \<turnstile> (\<glambda> x | a x \<bullet> s x) = (\<glambda> x | b x \<bullet> t x)"
  by (auto simp add: set_eq_def glambda_def)

lemma glambda_functional [mintro!(fspace)]: 
  "functional (\<glambda> x | b x \<bullet> t x)"
  by (auto intro!: glambda_single_val simp add: functional_def glambda_dom)

lemma glambda_inv_functional_iff:
  "functional ((\<glambda> x | b x \<bullet> t x)\<^sup>\<sim>) \<Leftrightarrow> (\<forall> x y | b x \<and> b y \<bullet> t x = t y \<Leftrightarrow> x = y)"
  by (auto intro!: functionalI elim!: functionalE simp add: glambda_def)

lemma glambda_inv_functional [mintro!(fspace)]:
  assumes
    a1: "(\<forall> x y | b x \<and> b y \<bullet> t x = t y \<Leftrightarrow> x = y)"
  shows
    "functional ((\<glambda> x | b x \<bullet> t x)\<^sup>\<sim>)"
  using a1
  by (simp add: glambda_inv_functional_iff)

lemma glambda_pfun: 
  assumes 
    a1: "{ x | b x } \<subseteq> X" and a2: "{ x | b x \<bullet> t x } \<subseteq> Y"
  shows 
    "(\<glambda> x | b x \<bullet> t x) \<in> X \<zpfun> Y"
  using a1 a2
  by (mauto(fspace) msimp add: glambda_dom glambda_ran )
(*J: improved!
  apply ((msafe(fspace)))
  using a1 a2
  apply (auto simp add: glambda_dom glambda_ran)
  done
*)

lemma glambda_tfun: 
  assumes 
    a1: "{ x | b x } = X" and 
    a2: "{ x | b x \<bullet> t x } \<subseteq> Y"
  shows 
      "(\<glambda> x | b x \<bullet> t x) \<in> X \<ztfun> Y"
  using a1 a2
  by (mauto(fspace) msimp add: glambda_dom glambda_ran )
(*J: improved!
  apply ((msafe(fspace)))
  using a1 a2
  apply (auto simp add: glambda_dom glambda_ran)
  done
*)

lemma glambda_tfun': 
  "(\<glambda> x | b x \<bullet> t x) \<in> { x | b x } \<ztfun> { x | b x \<bullet> t x }"
  by (mauto(fspace) msimp add: glambda_dom glambda_ran )
(*J: improved!
  apply ((msafe(fspace)))
  apply (auto simp add: glambda_dom glambda_ran)
  done
*)

lemma tfun_cong:
  assumes
    a1: "X \<noteq> \<emptyset>" "X' \<noteq> \<emptyset>" "Y \<noteq> \<emptyset>" "Y' \<noteq> \<emptyset>"
  shows
    "X \<ztfun> Y = X' \<ztfun> Y' \<Leftrightarrow> X = X' \<and> Y = Y'"
proof (mauto(inference))
  assume
    b1: "X \<ztfun> Y = X' \<ztfun> Y'"
  from a1 obtain y where
    b2: "y \<in> Y"
    by (auto)
  from a1 obtain x where
    b3: "x \<in> X"
    by (auto)
  have
    b4 [rule_format]: "(\<forall> Y y \<bullet> y \<in> Y \<Leftrightarrow> (\<glambda> x | x \<in> X \<bullet> y) \<in> X \<ztfun> Y)"
    apply (mauto(inference))
    apply (mauto(fspace) msimp add: glambda_dom glambda_ran glambda_functional)
    using b3
    apply (auto simp add: set_eq_def subset_def)
    done
  from b1 b4 [of "y" "Y"] b2 have
    "\<zdom> (\<glambda> x | x \<in> X \<bullet> y) = X'"
    by (simp add: tfun_dom)
  then show
    b5: "X = X'"
    by (simp add: glambda_dom set_eq_def)
  show
    "Y = Y'"
    using b4 [of _ "Y"] b4 [of _ "Y'", simplified b5] b1
    by (simp add: set_eq_iff b5)
qed  

lemma rel_oride_glambda:
  "(\<glambda> x | a x \<bullet> s x) \<oplus> (\<glambda> x | b x \<bullet> t x)
  = (\<glambda> x | a x \<or> b x \<bullet> \<if> b x \<then> t x \<else> s x \<fi>)"
  apply (rule functional_eqI)
  apply (mforce(fspace))
  apply (mforce(fspace))
  apply (auto simp add: Z_rel_oride_dom_dist glambda_dom rel_oride_beta glambda_beta)
  done

lemma glambda_if_split: 
  "(\<glambda> x | b x \<bullet> if c x then t x else s x)
  = (\<glambda> x | b x \<and> c x \<bullet> t x) \<union> (\<glambda> x | b x \<and> \<not>(c x) \<bullet> s x)"
  by (auto simp add: glambda_def set_eq_def)

lemma glambda_comp_beta:
  "(\<glambda> x | b x \<bullet> (\<glambda> x | c x \<bullet> t x)\<cdot>x)\<cdot>x = (\<glambda> x | b x \<and> c x \<bullet> t x)\<cdot>x"
  apply (cases "b x")
  apply (auto simp add: glambda_beta glambda_dom undef_beta)
  apply (cases "c x")
  apply (auto simp add: glambda_beta glambda_dom undef_beta)
  done

lemma glambda_empty: "(\<glambda> x | False \<bullet> t x) = \<emptyset>"
  by (simp add: glambda_def)  

lemma tfun_setsub_inverse:
assumes
  A1: "f \<in> X \<ztfun> Y" and
  A2: "V \<subseteq> Y"
shows
  "X\<setminus>(f\<^sup>\<sim>)\<zlImg>V\<zrImg> = (f\<^sup>\<sim>)\<zlImg>Y\<setminus>V\<zrImg>"
  using A1 A2
  apply (simp add: set_eq_def Image_iff converse_iff)
  apply ((msafe(fspace)), auto)
proof-
  fix x :: "'a" and y y' :: "'b"
  assume
    Aa1: "functional f" and Aa2: "y \<notin> V" and Aa3: "y' \<in> V" and
    Aa4: "(x\<mapsto>y) \<in> f" and Aa5: "(x\<mapsto>y') \<in> f" 
  with Aa1 [THEN functionalD] have 
    "y = y'" 
    by (auto)
  with Aa2 Aa3 show 
    "\<False>" 
    by (auto)
qed

lemma dres_subset_in_tfunI:
assumes
  A0: "f \<in> X \<ztfun> Y" and 
  A1: "A \<subseteq> X" 
shows
"A\<zdres>f \<in> A \<ztfun> Y"
  apply (rule in_tfunI)
  apply (rule dres_in_pfunI [rule_format])
  using A0
  apply ((msafe(fspace)), simp)
  using A0 A1
  apply (mauto(fspace) msimp add: Z_dres_dom)
(*J: improved
  apply (auto)
*)
done

lemma tfun_eta:
  assumes
    a1: "f \<in> X \<ztfun> Y"
  shows
    "(\<glambda> x | x \<in> X \<bullet> f\<cdot>x) = f"
  apply (rule tfun_eqI [OF glambda_tfun a1])
  apply (auto intro: tfun_range [OF a1] simp add: glambda_beta)
  done

lemma functional_eta:
  assumes
    a1: "functional f"
  shows
    "(\<glambda> x | x \<in> \<zdom> f \<bullet> f\<cdot>x) = f"
  apply (rule functional_eqI [OF glambda_functional a1])
  apply (auto simp add: glambda_beta glambda_mem glambda_dom)
  done
 
section {* Finite function graphs *}

text {*

Finite functions are those represented by a finite set of maplets.

*}

definition
  finite_part_funs :: "['a set, 'b set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  finite_part_funs_def: "finite_part_funs X Y \<defs> {f | f \<in> X \<zpfun> Y \<and> finite (\<zdom> f)}"

notation (xsymbols)
  finite_part_funs (infixr "\<zffun>" 92)

definition
  finite_part_injs :: "['a set, 'b set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  finite_part_injs_def: "finite_part_injs X Y \<defs> X \<zffun> Y \<inter> X \<zpinj> Y"

notation (xsymbols)
  finite_part_injs (infixr "\<zfinj>" 92)

lemma fpfunI [mintro!(fspace)]:
  assumes a1: "f \<in> X \<zpfun> Y" and a2: "finite (\<zdom> f)"
  shows "f \<in> X \<zffun> Y"
  using a1 a2
  by (simp add: finite_part_funs_def)

lemma fpfunE [melim!(fspace)]:
  assumes 
    a1: "f \<in> X \<zffun> Y" and
    a2: "\<lbrakk> f \<in> X \<zpfun> Y; finite (\<zdom> f) \<rbrakk> \<turnstile> R"
  shows 
    "R"
  using a1 a2
  by (auto simp add: finite_part_funs_def)

lemma fpfunD1:
  assumes 
    a1: "f \<in> X \<zffun> Y"
  shows 
    "f \<in> X \<zpfun> Y"
  using a1
  by (simp add: finite_part_funs_def)

lemma fpfunD2:
  assumes 
    a1: "f \<in> X \<zffun> Y"
  shows 
    "finite (\<zdom> f)"
  using a1
  by (simp add: finite_part_funs_def)

lemma fun_finite_dom: 
  assumes 
    a1: "finite f"
  shows 
    "finite (\<zdom> f)"
  apply (rule finite_surj [of "f" "\<zdom> f" "(\<olambda> (x, y) \<bullet> x)", OF a1])
  apply (auto simp add: image_def Domain_iff)
  done

lemma fun_finite_ran: 
  assumes 
    a1: "finite f"
  shows 
    "finite (\<zran> f)"
  apply (rule finite_surj [of "f" "\<zran> f" "(\<olambda> (x, y) \<bullet> y)", OF a1])
  apply (auto simp add: image_def)
  done

lemma fun_image_of_dom:
  assumes 
    a1: "functional f"
  shows 
    "(\<olambda> x \<bullet> (x \<mapsto> f\<cdot>x)) \<lparr> (\<zdom> f) \<rparr> = f"
  by (auto simp add: image_def Domain_iff functional_appl [OF a1] functional_beta [OF a1])

lemma fun_image_inj:
  "inj_on (\<olambda> x \<bullet> (x \<mapsto> f\<cdot>x)) (\<zdom> f)"
  apply (rule inj_onI)
  apply (auto)
  done

lemma dom_finite_fun:
  assumes
    a1: "functional f" and a2: "finite (\<zdom> f)"
  shows 
    "finite f"
  apply (rule finite_surj [of "\<zdom> f" "f" "(\<olambda> x \<bullet> (x \<mapsto> f\<cdot>x))", OF a2])
  apply (simp add: fun_image_of_dom [OF a1])
  done

lemma fun_card_dom:
  assumes 
    a1: "functional f"
  shows 
    "card f = card (\<zdom> f)"
  apply (rule trans [of _ "card (\<olambda> x \<bullet> (x \<mapsto> f\<cdot>x)) \<lparr> (\<zdom> f) \<rparr>" _])
  apply (simp add: fun_image_of_dom [OF a1])
  apply (rule card_image [OF fun_image_inj])
  done

lemma inverse_card:
  "card (R\<^sup>\<sim>) = card R"
proof -
  let 
    ?swap = "(\<olambda> (a, b) \<bullet> (b, a))"
  have
    b1: "R\<^sup>\<sim> = image ?swap R"
    by (auto)
  show
    "?thesis"
    apply (simp add: b1)
    apply (rule card_image)
    apply (rule inj_onI)
    apply (auto)
    done
qed


text {*

Calculating the domain and range of finite graphs is staightforward.

*}

lemma insert_dom: "\<zdom> (insert (x \<mapsto> y) R) = insert x (\<zdom> R)"
  by (blast)

lemma insert_dom': "\<zdom> (insert xy R) = insert (\<fst> xy) (\<zdom> R)"
  apply (cases "xy")
  by (simp add: insert_dom)

lemma insert_ran: "\<zran> (insert (x \<mapsto> y) R) = insert y (\<zran> R)"
  by (blast)

lemma insert_ran': "\<zran> (insert xy R) = insert (\<snd> xy) (\<zran> R)"
  apply (cases "xy")
  by (simp add: insert_dom)

lemma empty_dom: "\<zdom> \<emptyset> = \<emptyset>"
  by (auto)

lemma dom_is_empty: "\<zdom> R = \<emptyset> \<Leftrightarrow> R = \<emptyset>"
  by (auto)

lemma empty_ran: "\<zran> \<emptyset> = \<emptyset>"
  by (auto)

lemma ran_is_empty: "\<zran> R = \<emptyset> \<Leftrightarrow> R = \<emptyset>"
  by (auto)

lemma insert_rinv: "(\<^ins>{:(x \<mapsto> y):}{:f:})\<^sup>\<sim> = \<^ins>{:(y \<mapsto> x):}{:(f\<^sup>\<sim>):}"
  by (auto simp add: converse_def)

lemma empty_rinv: "\<emptyset>\<^sup>\<sim> = \<emptyset>"
  by (auto simp add: converse_def)

lemma insert_functional:
  "functional (\<^ins>{:(x \<mapsto> y):}{:f:}) \<Leftrightarrow> functional f \<and> (x \<notin> \<zdom> f \<or> (x \<mapsto> y) \<in> f)"
proof (msafe(inference))
  assume b1: "functional (\<^ins>{:(x \<mapsto> y):}{:f:})"
  from b1 show "functional f"
    by (auto elim!: functionalE intro!: functionalI)
  from b1 show "x \<notin> \<zdom> f \<or> (x \<mapsto> y) \<in> f"
    by (auto elim!: functionalE)
next
  assume b1: "functional f" and b2: "x \<notin> \<zdom> f"
  then show "functional (\<^ins>{:(x \<mapsto> y):}{:f:})"
    by (auto elim!: functionalE intro!: functionalI)
next
  assume b1: "functional f" and b2: "(x \<mapsto> y) \<in> f"
  from b2 have "\<^ins>{:(x \<mapsto> y):}{:f:} = f"
    by (auto)
  with b1 show "functional (\<^ins>{:(x \<mapsto> y):}{:f:})"
    by (simp)
qed

lemma insert_functionalI [mintro(fspace)]: 
  "\<lbrakk> functional f; x \<notin> \<zdom> f \<rbrakk> 
  \<turnstile> functional (\<^ins>{:(x \<mapsto> y):}{:f:})"
  by (auto simp add: functional_def single_val_def)

lemma insert_rinv_functionalI [mintro(fspace)]: 
  "\<lbrakk> functional (f\<^sup>\<sim>); y \<notin> \<zran> f \<rbrakk> 
  \<turnstile> functional ((\<^ins>{:(x \<mapsto> y):}{:f:})\<^sup>\<sim>)"
  by (auto simp add: functional_def single_val_def)

text {*

Efficiently determining if a finite graph is functional requires an
auxiliary mechanism. The operator @{text pfun_off} determines
partial functions not defined anyway on a given set.

*}

definition
  functional_off :: "['a set, ('a \<leftrightarrow> 'b)] \<rightarrow> \<bool>"
where
  functional_off_def: "functional_off \<defs> \<olambda> A f \<bullet> functional f \<and> disjoint (\<zdom> f) A"

lemma fin_functional0:
  "functional_off \<emptyset> f \<turnstile> functional f"
  by (auto simp add: functional_off_def)

lemma fin_functional1: "functional_off A \<emptyset>"
  by (simp add: functional_off_def functional_def single_val_def disjoint_def)

lemma fin_functional2:
  "\<lbrakk> x \<notin> A; functional_off (\<^ins>{:x:}{:A:}) f \<rbrakk>
  \<turnstile> functional_off A (\<^ins>{:(x \<mapsto> y):}{:f:})"
  by (auto simp add: functional_off_def functional_def single_val_def disjoint_def)

lemmas base_fin_pfunI = fin_functional0 fin_functional1 fin_functional2

lemmas fin_pfunI = dr_intros base_fin_pfunI

lemma fin_sets: 
  "finite \<emptyset>"
  "finite (insert x A) \<Leftrightarrow> finite A"
  by (auto)

lemmas fin_pfun_simp =
  insert_dom insert_ran empty_dom empty_ran
  insert_rinv empty_rinv
  insert_absorb2 insert_commute
  insert_iff empty_iff
  converse_empty converse_insert
  fin_sets

(*
declare_mprover "fin_fspace"

declare fin_pfun_simp[msimp(fin_fspace)]

ML {

local

val fin_pfun_simp = @{thms "fin_pfun_simp"};
val fin_pfun0 = @{thm "fin_functional0"};
val fin_pfun1 = @{thm "fin_functional1"};
val fin_pfun2 = @{thm "fin_functional2"};
fun ss ctxt = (Simplifier.simpset_of ctxt) addsimps fin_pfun_simp;

fun onestep ctxt = (rtac fin_pfun0) ORELSE' (rtac fin_pfun1) ORELSE' (rtac fin_pfun2 THEN' (simp_tac (ss ctxt)));

fun firststep ctxt =
  FSpace_Setup.fspace_tac (FSpace_Setup.get_fs (Context.Proof ctxt)) (ss ctxt);

fun fgtac ctxt = (
  (firststep ctxt) THEN 
  (REPEAT (onestep ctxt 1)));

fun fgmeth ctxt = Method.METHOD (fn facts =>
  ALLGOALS (Method.insert_tac (facts)) THEN
    (fgtac ctxt)); 

val fin_FS_method = Method.sections Simplifier.simp_modifiers >> K fgmeth;

in

val finspace_setup =
  Method.setup (Binding.name "fin_fspace") fin_FS_method
    "determine function space of finite graph"

end

}

setup{ finspace_setup }
*)

lemma empty_functional: "functional \<emptyset>"
  by (mauto(fspace) mintro: fin_pfunI)
(*J: can we do without it this way?
  by (fin_fspace)
*)

lemma singleton_functions:
  "{x} \<ztfun> Y = { y | y \<in> Y \<bullet> {(x \<mapsto> y)}}"
proof (auto)
  fix f
  assume b1: "f \<in> {x} \<ztfun> Y"
  then have b2: "x \<in> \<zdom> f"
    by (mauto(fspace))
  then obtain y where b3: "(x \<mapsto> y) \<in> f"
    by (auto)
  from b1 have b4: "\<forall> a y \<bullet> (a \<mapsto> y) \<in> f \<Rightarrow> (x \<mapsto> y) \<in> f"
    apply (mauto(fspace))
    apply (auto simp add: Domain_iff)
    done
  from b1 b3 have b5: "f = {(x \<mapsto> y)}" "y \<in> Y"
    apply (mauto(fspace))
    apply (auto)
  proof -
    fix a b
    assume c1: "(a \<mapsto> b) \<in> f"
    with b4 have "(x \<mapsto> b) \<in> f" 
      by (auto)
    with b3 b1 show "b = y"
      by (mauto(fspace) melim: functionalE)
(*J: improved
      apply (elim functionalE)
      apply (auto)
      done
*)
  qed
  then show "\<exists> y \<bullet> f = {(x \<mapsto> y)} \<and> y \<in> Y"
    by (auto)
next
  fix y 
  assume b1: "y \<in> Y"
  then show "{(x \<mapsto> y)} \<in> {x} \<ztfun> Y"
    by (mauto(fspace) mintro!: functionalI)
(*J: improved
    apply ((msafe(fspace)))
    apply (auto intro!: functionalI)
    done
*)
qed

text {*

Insertion is just a special case of relational union, so we can specialise
union beta reduction appropriately.

*}

lemma insert_beta:
  assumes 
    a1: "functional (insert (x \<mapsto> a) f)"
  shows 
    "(insert (x \<mapsto> a) f)\<cdot>y = \<if> x = y \<then> a \<else> f\<cdot>y \<fi>"
  apply (insert rel_union_beta2n [of "{(x \<mapsto> a)}" "f"])
  using a1
  apply (simp add: insert_dom empty_dom)
  apply (auto)
  apply (rule functional_beta)
  apply (rule functional_singleton)
  apply (auto)
  done

text {*

However, this does not offer a very efficient approach to calculating beta-reduction 
for finite functions. Instead, we introduce an accumulation operator that extracts
all of the maplets associated with a given argument. If this is a singleton, we
know the result of the function at that argument.

*}  

definition
  pimage :: "[('a \<leftrightarrow> 'b), 'a] \<rightarrow> 'b set"
where
  pimage_def: "pimage f x \<defs> f\<zlImg>{x}\<zrImg>"

lemma insert_pimage1:
  "z = x \<turnstile> pimage (\<^ins>{:(x \<mapsto> y):}{:f:}) z = \<^ins>{:y:}{:pimage f z:}"
  by (auto simp add: pimage_def Image_def)

lemma insert_pimage2:
  "z \<noteq> x \<turnstile> pimage (\<^ins>{:(x \<mapsto> y):}{:f:}) z = pimage f z"
  by (auto simp add: pimage_def Image_def)

lemma empty_pimage:
  "pimage \<emptyset> z = \<emptyset>"
  by (auto simp add: pimage_def Image_def)

lemma funappl_pimage: "f\<cdot>x = (\<mu> y | y \<in> pimage f x)"
  by (auto simp add: pimage_def fun_appl_def)

lemma fin_funappl_pimage: "finite f \<turnstile> f\<cdot>x = (\<mu> y | y \<in> pimage f x)"
  by (auto simp add: pimage_def fun_appl_def)

lemma the_result: "(\<mu> y | y \<in> {z}) = z" 
  by (auto) 

lemmas fin_funappl = insert_pimage1 insert_pimage2 empty_pimage 
  fin_funappl_pimage the_result

lemma empty_oride: "\<emptyset> \<oplus> g = g"
  by (auto simp add: rel_oride_def dsub_def)

lemma insert_oride: "(\<^ins>{:(x \<mapsto> y):}{:f:}) \<oplus> g =
    \<if> x \<in> \<zdom> g \<then> f \<oplus> g
    \<else> \<^ins>{:(x \<mapsto> y):}{:(f \<oplus> g):} \<fi>"
  by (auto simp add: rel_oride_def dsub_def)

lemmas oride_calc = empty_oride insert_oride insert_dom empty_dom

lemma glambda_is_empty: "(\<glambda> x | P x \<bullet> t x) = \<emptyset> \<Leftrightarrow> Collect P = \<emptyset>"
  by (auto simp add: functional_eq_def [OF glambda_functional empty_functional]
    glambda_dom)

section {* Miscellaneous *}

subsection {* Indexed Disjointness and partitioning *}

text {*

An indexed family of sets is disjoint if they have no common elements pairwise.

*}

definition
  iDisjoint :: "('b \<leftrightarrow> 'a set) \<rightarrow> \<bool>" ("\<iDisjoint>")
where
  iDisjoint_def: 
    "iDisjoint 
    \<defs> (\<olambda> CL_X \<bullet> 
        (\<forall> X Y | X \<in> CL_X \<and> Y \<in> CL_X \<and> X \<noteq> Y \<bullet> disjoint (\<snd> X) (\<snd> Y)))"

lemma Z_iDisjoint_def:
  assumes 
    a1: "S \<in> I \<zpfun> \<pset> X"
  shows 
    "\<iDisjoint> S 
    \<defs> (\<forall> i j | \<lch>i, j \<chIn> \<zdom> S\<rch> \<and> i \<noteq> j \<bullet> disjoint (S\<cdot>i) (S\<cdot>j))"
  apply (rule eq_reflection)
  apply (simp add: iDisjoint_def)
proof -
  have "(\<forall> i A j B | (i \<mapsto> A) \<in> S \<and> (j \<mapsto> B) \<in> S \<and> (i = j \<Rightarrow> A \<noteq> B) \<bullet> disjoint A B)

  \<Leftrightarrow> (\<forall> i A j B 
     | (i \<in> \<zdom> S \<and> j \<in> \<zdom> S) \<and> (i \<mapsto> A) \<in> S \<and> (j \<mapsto> B) \<in> S \<and> (i = j \<Rightarrow> A \<noteq> B) 
     \<bullet> disjoint A B)"
    by (mauto(wind) msimp add: Domain_iff)
(*J: improve
    apply (msafe(wind))
    apply (auto simp add: Domain_iff)
    done
*)
  also have "\<dots>
  \<Leftrightarrow> (\<forall> i A j B 
     | i \<in> \<zdom> S \<and> (i \<mapsto> A) \<in> S \<and> j \<in> \<zdom> S \<and> (j \<mapsto> B) \<in> S \<and> (i = j \<Rightarrow> A \<noteq> B) 
     \<bullet> disjoint A B)"
(*J: improve
    apply (msafe(wind))
    apply (auto)
    done
*)
    by (mauto(wind))
  also have "\<dots>
  \<Leftrightarrow> (\<forall> i A j B 
     | i \<in> \<zdom> S \<and> A = S\<cdot>i \<and> j \<in> \<zdom> S \<and> (j \<mapsto> B) \<in> S \<and> (i = j \<Rightarrow> A \<noteq> B) 
     \<bullet> disjoint A B)"
    by (mauto(wind), 
        mauto(inference) msimp add: pfun_beta [OF a1] pfun_appl [OF a1])
(*J: improve
    apply (msafe(wind))
    apply (msafe(inference))
    apply (simp add: pfun_beta [OF a1])
    apply (simp add: pfun_appl [OF a1])
    done
*)
  also have "\<dots>
  \<Leftrightarrow> (\<forall> i A j B 
     | i \<in> \<zdom> S \<and> A = S\<cdot>i \<and> j \<in> \<zdom> S \<and> B = S\<cdot>j \<and> (i = j \<Rightarrow> A \<noteq> B) 
     \<bullet> disjoint A B)"
    by (mauto(wind), 
        mauto(inference) msimp add: pfun_beta [OF a1] pfun_appl [OF a1])
(*J: improve
    apply (msafe(wind))
    apply (msafe(inference))
    apply (simp add: pfun_beta [OF a1])
    apply (simp add: pfun_appl [OF a1])
    done
*)
  also have "\<dots>
  \<Leftrightarrow> (\<forall> i j | i \<in> \<zdom> S \<and> j \<in> \<zdom> S \<and> (i = j \<Rightarrow> S\<cdot>i \<noteq> S\<cdot>j) \<bullet> disjoint (S\<cdot>i) (S\<cdot>j))"
    by (auto)
  also have "\<dots>
  \<Leftrightarrow> (\<forall> i j | i \<in> \<zdom> S \<and> j \<in> \<zdom> S \<and> i \<noteq> j \<bullet> disjoint (S\<cdot>i) (S\<cdot>j))"
    by (mauto(wind))
(*J: improve
    apply (msafe(wind))
    apply auto
    done
*)
  finally show 
  "(\<forall> i A j B | (i \<mapsto> A) \<in> S \<and> (j \<mapsto> B) \<in> S \<and> (i = j \<Rightarrow> A \<noteq> B) \<bullet> disjoint A B)
  \<Leftrightarrow> (\<forall> i j | i \<in> \<zdom> S \<and> j \<in> \<zdom> S \<and> i \<noteq> j \<bullet> disjoint (S\<cdot>i) (S\<cdot>j))"
    by (this)
qed

lemma iDisjoint_glambda:
  assumes a1: "\<iDisjoint> (\<glambda> i | p i \<bullet> X i)" and a2: "x \<in> (\<Union> i | p i \<bullet> X i)"
  shows "(\<exists>\<subone> i | p i \<bullet> x \<in> X i)"
proof -
  from a2 obtain i where b1: "p i" and b2: "x \<in> X i"
    by (auto)
  from a1 b1 b2 have b3: "(\<forall> j | j \<noteq> i \<and> p j \<bullet> x \<notin> X j)"
    by (auto simp add: iDisjoint_def disjoint_def glambda_mem)
  from b1 b2 b3
  show "?thesis"
    apply (intro ex1I [of _ i])
    apply (auto)
    done
qed

definition
  iPartition :: "[('b \<leftrightarrow> 'a set), 'a set] \<rightarrow> \<bool>" ("_ \<iPartition> _" [999, 1000] 999)
where
  iPartition_def: "iPartition CL_X X \<defs> \<iDisjoint> CL_X \<and> \<Union>(\<zran> CL_X) = X"

lemma Z_iPartition_def:
  assumes a1: "S \<in> I \<zpfun> \<pset> X"
  shows "S \<iPartition> T \<defs> \<iDisjoint> S \<and> (\<Union> i | i \<in> \<zdom> S \<bullet> S\<cdot>i) = T"
proof (rule eq_reflection)
  have "S \<iPartition> T 
  \<Leftrightarrow> \<iDisjoint> S \<and> \<Union>(\<zran> S) = T"
    by (simp add: iPartition_def)
  also have "\<dots> 
  \<Leftrightarrow> \<iDisjoint> S \<and> (\<Union> i | i \<in> \<zdom> S \<bullet> S\<cdot>i) = T"
    apply (mclarsimp(wind) mintro!: set_eqI)
    apply (simp add: Domain_iff Range_iff)
    apply (mauto(wind))
    apply (auto simp add: pfun_beta [OF a1])
    done
  finally show "S \<iPartition> T
  \<Leftrightarrow> \<iDisjoint> S \<and> (\<Union> i | i \<in> \<zdom> S \<bullet> S\<cdot>i) = T"
    by (this)
qed

subsection {* Monotonic graph functions *}

text {*

A graph function is monotonic if preserves the (type) ordering on its domain.

*}

definition
  mono_funs :: "[('a::order) set, ('b::order) set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  mono_funs_def: "mono_funs \<defs> (\<olambda> X Y \<bullet> { f | f \<in> X \<ztfun> Y \<and> (\<forall> x y | x \<le> y \<bullet> f\<cdot>x \<le> f\<cdot>y) })"

notation (xsymbols)
  mono_funs (infixr "\<zmfun>" 92)


subsection {* Graph functions and HOL operators *}

text {*

In various situations it is convenient to be able to convert between
operator and graph representations.
Converting from an operator to a graph is a matter of collecting all
the maplets of the operator.
Converting from a graph to an operator is already done by the operator
@{text "(_\<cdot>_)"}, we need only define a new syntax for it.

*}

definition
  graph_of :: "('a \<rightarrow> 'b) \<rightarrow> ('a \<leftrightarrow> 'b)"
where
  graph_of_def: "graph_of f \<defs> (\<glambda> a \<bullet> f a)"

notation (zed)
  graph_of ("\<graphof>")

syntax (zed)
  "_Z_Fun\<ZZ>fun_appl" :: "('a \<leftrightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b)" ("\<opof>")

translations
  "_Z_Fun\<ZZ>fun_appl" \<rightharpoonup> "Z_Fun.fun_appl"

text {*

These mappings form an isomorphism between functions and total-one-to-one
relations.

*}


lemma graph_of_f_tfun: "(\<graphof> f) \<in> \<univ>-['a] \<ztfun> \<univ>-['b]"
  by (rule in_tfunI, rule in_pfunI, 
    auto simp add: graph_of_def glambda_def rel_def Domain_iff)

lemma graph_of_inverse: "\<opof> (\<graphof> f) = f"
  by (rule ext, auto simp add: fun_appl_def graph_of_def glambda_def)

lemma graph_of_inj: "inj \<graphof>"
  by (rule inj_on_inverseI [of _ "\<opof>"], simp add: graph_of_inverse)

lemma fun_of_inverse: 
  assumes 
    a1: "r \<in> \<univ>-['a] \<ztfun> \<univ>-['b]"
  shows 
    "\<graphof> (\<opof> r) = r"
  using a1
proof (auto intro: tfun_appl simp add: graph_of_def glambda_def set_eq_def)
  fix a b assume 
    a2: "(a \<mapsto> b) \<in> r"
  from a1 have 
    a3: "r \<in> \<univ>-['a] \<zpfun> \<univ>-['b]" 
    by (auto)
  from a3 a2 have 
    "r\<cdot>a = b"
    by (rule pfun_beta)
  then show 
    "b = r\<cdot>a" 
    by (simp)
qed

lemma fun_of_inverse_res:
  assumes 
    a1: "r \<in> X \<ztfun> Y"
  shows 
    "X \<zdres> (\<graphof> (\<opof> r)) = r"
  using tfun_beta [OF a1] tfun_dom [OF a1]
  by (auto intro: tfun_appl  simp add: graph_of_def glambda_def dres_def tfun_beta)

lemma fun_of_inv_graph_of: "f \<in> \<univ>-['a] \<ztfun> \<univ>-['b]
  \<turnstile> (inv \<graphof>) f = \<opof> f"
  by (rule inv_f_eq, rule graph_of_inj, rule fun_of_inverse)

lemma fun_of_inj_on_tfun: "inj_on \<opof> (\<univ>-['a] \<ztfun> \<univ>-['b])"
  by (rule inj_on_inverseI [of _ "\<graphof>"], simp add: fun_of_inverse)

lemma graph_of_abs: "\<graphof> f = (\<glambda> x \<bullet> f x)"
  by (simp add: graph_of_def glambda_def)

lemma graph_of_id: "\<graphof> id = \<zid> \<univ>"
  by (simp add: graph_of_def glambda_def id_def rel_id_def)

lemma graph_of_comp: "\<graphof> (f \<circ> g) = (\<graphof> f) \<zbcomp> (\<graphof> g)"
  by (auto simp add: graph_of_def glambda_def o_def rel_bcomp_def)

lemma dres_graph_of: "X \<zdres> (\<graphof> f) = {a | a \<in> X \<bullet> (a \<mapsto> f a)}"
  by (auto simp add: graph_of_def glambda_def dres_def)

lemma rres_graph_of: "(\<graphof> f) \<zrres> Y = {a | f a \<in> Y \<bullet> (a \<mapsto> f a)}"
  by (auto simp add: graph_of_def glambda_def rres_def)

lemma graph_of_f_inj: 
  assumes 
    a1: "inj f"
  shows 
    "(\<graphof> f) \<in> \<univ> \<zinj> \<univ>"
  apply (rule in_tinjI [OF in_pinjI graph_of_f_tfun])
  apply (rule graph_of_f_tfun [THEN tfun_pfun])
  using a1
  apply (auto simp add: graph_of_def glambda_def inj_on_def) 
  done

lemma fun_of_f_inj:
  assumes 
    a1: "r \<in> \<univ> \<zinj> \<univ>"
  shows 
    "inj (\<opof> r)"
proof -
  from a1 have 
    a2: "r \<in> \<univ> \<ztfun> \<univ>"
    by (auto)
  show ?thesis
    apply (rule inj_onI)
    apply (rule pinj_inj)
    using a1 a2
    apply (auto simp add: a2 [THEN tfun_dom])
    done
qed

lemma graph_of_dresf_inj_on: 
  assumes 
    a1: "inj_on f X"
  shows 
    "X \<zdres> (\<graphof> f) \<in> X \<zinj> \<univ>"
  apply (rule in_tinjI [OF in_pinjI])
  using a1
  apply (auto simp add: dres_graph_of fun_space_defs inj_on_def)
  done

lemma fun_of_f_inj_on:
  assumes a1: "r \<in> X \<zinj> \<univ>"
  shows "inj_on (\<opof> r) X"
proof -
  from a1 have a2: "r \<in> X \<ztfun> \<univ>"
    by (auto)
  from a2 [THEN tfun_dom]
  have a3: "X \<subseteq> \<zdom> r"
    by (auto simp add: dres_def)
  show ?thesis
  proof (rule inj_onI, rule pinj_inj [of "r"])
    fix x y
    assume b1a: "x \<in> X" and b1b: "y \<in> X" and
      b2: "r\<cdot>x = r\<cdot>y"
    from a1 show "r \<in> X \<zpinj> \<univ>" by (auto)
    from b1a show "x \<in> \<zdom> r"
      by (simp add: a2 [THEN tfun_dom])
    from b1b show "y \<in> \<zdom> r"
      by (simp add: a2 [THEN tfun_dom])
    assume b3: "r\<cdot>x = r\<cdot>y"
    from a1 have "r \<in> X \<zpfun> \<univ>" by (auto)
    then show "r\<cdot>x = r\<cdot>y"
      by (simp add: b1a b1b b3 dres_beta)
  qed
qed

lemma graph_of_f_surj: 
  assumes 
    a1: "surj f"
  shows 
    "(\<graphof> f) \<in> \<univ> \<zsurj> \<univ>"
  apply (rule in_tsurjI [OF in_psurjI graph_of_f_tfun])
  apply (rule graph_of_f_tfun [THEN tfun_pfun])
  using a1
  apply (auto simp add: graph_of_def glambda_def surj_def Range_iff Domain_iff) 
  done

lemma fun_of_f_surj:
  assumes 
    a1: "r \<in> \<univ>-['a] \<zpsurj> \<univ>-['b]"
  shows 
    "surj (\<opof> r)"
proof (rule surjI [of "\<opof> r" "\<olambda> y \<bullet> (\<some> x | \<^infrel>{:x:}{:r:}{:y:})"])
  fix y::"'b"
  from a1 have "y \<in> \<zran> r"
    by (simp add: psurj_ran)
  then have b0: "\<exists> x \<bullet> \<^infrel>{:x:}{:r:}{:y:}"
    by (auto simp add: Range_iff Domain_iff)
  from b0 [THEN someI_ex] have 
    "(\<some> x | \<^infrel>{:x:}{:r:}{:y:}) \<in> {x | \<^infrel>{:x:}{:r:}{:y:}}"
    by (simp) 
  then have a2: "\<^infrel>{:(\<some> x | \<^infrel>{:x:}{:r:}{:y:}):}{:r:}{:y:}"
    by (auto)
  from a1 have a3: "r \<in> \<univ> \<zpfun> \<univ>"
    by (auto)
  from a3 a2 show "r\<cdot>(\<some> x | \<^infrel>{:x:}{:r:}{:y:}) = y"
    by (simp add: pfun_beta)
qed

lemma graph_of_f_bij: 
  assumes 
    a1: "bij f"
  shows 
    "(\<graphof> f) \<in> \<univ> \<zbij> \<univ>"
  apply (rule in_bijI)
  using a1
  apply (auto intro!: graph_of_f_inj graph_of_f_surj simp add: bij_def)
  done

lemma fun_of_f_bij: 
  assumes a1: "r \<in> \<univ> \<zbij> \<univ>"
  shows "bij (\<opof> r)"
  using a1
  by (auto intro!: fun_of_f_inj fun_of_f_surj  simp add: bij_def)

text {*

Updating of HOL operators can be conveniently expressed by collecting
the updates into a graph. 

*}

definition
  op_oride :: "['a \<rightarrow> 'b, ('a \<leftrightarrow> 'b)] \<rightarrow> ('a \<rightarrow> 'b)"
where
  op_oride_def: "op_oride f g \<defs> (\<olambda> x \<bullet> \<if> x \<in> \<zdom> g \<then> g\<cdot>x \<else> f x \<fi>)"
 
notation (xsymbols output)
  op_oride (infixl "\<oplus>" 65)
 
notation (zed)
  op_oride (infixl "\<oporide>" 65)

lemma op_oride_beta: 
  "(f \<oporide> g) x = (\<if> x \<in> \<zdom> g \<then> g\<cdot>x \<else> f x \<fi>)"
  by (simp add: op_oride_def)

text {*

An over-ride with a singleton graph is the same as a pointwise update.

*}

lemma fun_upd_oride: "f (x := y) = f \<oporide> {(x \<mapsto> y)}"
  by (rule ext, auto simp add: op_oride_beta fun_upd_def Domain_iff fun_appl_def the_equality)

text {*

Successive updates can be resolved in the graph representation world.

*}

lemma op_oride_assoc:
  "(f \<oporide> g) \<oporide> h = f \<oporide> (g \<oplus> h)"
  by (rule ext, simp add: op_oride_beta Z_rel_oride_dom_dist rel_oride_beta)

lemma op_oride_glambda:
  "f \<oporide> (\<glambda> x | b x \<bullet> t x)
  = (\<olambda> x \<bullet> \<if> b x \<then> t x \<else> f x \<fi>)"
  by (simp add: op_oride_def fun_eq_def glambda_dom glambda_beta)

text {*

A @{text "X"}-view of an operator @{text "f"} is the partial function constructed by 
restricting @{text "f"} to @{text "X"}.

*}

definition
  view :: "['A \<rightarrow> 'B, 'A set] \<rightarrow> ('A \<times> 'B) set"
where
  view_def: "view f X \<defs> (\<glambda> x | x \<in> X \<bullet> f x)"

notation (zed)
  view (infixr "\<down>" 100)

lemma view_tfun [mintro!(fspace)]: "functional (f\<down>X)"
  by (unfold view_def, msafe(fspace))

lemma view_mem:
    "(x, y) \<in> f\<down>X \<Leftrightarrow> x \<in> X \<and> y = f x"
  by (auto simp add: view_def glambda_mem)

lemma view_dom: "\<zdom> (f\<down>X) = X"
  by (auto simp add: view_def glambda_dom)

lemma view_ran:
  "\<zran> (f\<down>X) = { x | x \<in> X \<bullet> f x }"
  by (auto simp add: view_mem Z_ran_def)

lemma view_beta: 
  assumes a1: "x \<in> X"
  shows "(f\<down>X)\<cdot>x = f x"
proof (rule functional_beta)
  show "functional (f\<down>X)" by ((msafe(fspace)))
  from a1 show "(x, f x) \<in> (f\<down>X)"
    by (auto simp add: view_def glambda_def)
qed

lemma [mintro!(wind)]:
  "(\<And> x \<bullet> x \<in> X \<turnstile> f x = g x) \<turnstile> f\<down>X = g\<down>X"
  by (auto simp add: view_def glambda_def)

lemma dres_view: "W\<zdres>(f\<down>V) = f\<down>(V \<inter> W)"
  by (auto simp add: dres_def view_def glambda_def)

lemma dsub_view: "W\<zdsub>(f\<down>V) = f\<down>(V - W)"
  by (auto simp add: dsub_def view_def glambda_def)

lemma view_eq:
  "f\<down>V = g\<down>V \<Leftrightarrow> (\<forall> n | n \<in> V \<bullet> f n = g n)"
  by (auto simp add: view_def glambda_eq)

lemma view_rinv:
  assumes
    a1: "f \<in> X \<ztfun> Y"
  shows
    "(fun_appl f)\<down>X = f"
  apply (rule tfun_eqI [OF _ a1])
  apply ((msafe(fspace)))
  apply (simp add: view_dom)
  apply (simp add: view_def)
  apply (auto simp add: view_beta glambda_ran subset_def tfun_range [OF a1])
  done

section {* Maps and graphs *}

definition
  pfun_map :: "('a \<leftrightarrow> 'b) \<rightarrow> ('a, 'b) map"
where
  "pfun_map f = (\<olambda> x \<bullet> \<if> x \<in> \<zdom> f \<then> Some (f\<cdot>x) \<else> None \<fi>)"

definition
  map_pfun :: "('a, 'b) map \<rightarrow> ('a \<leftrightarrow> 'b)"
where
  "map_pfun f = (\<glambda> x | x \<in> dom f \<bullet> the (f x))"

interpretation
  map_pfun: type_definition map_pfun pfun_map "\<univ> \<zpfun> \<univ>"
proof (rule type_definition.intro)
{
  fix
    f
  show
    "map_pfun f \<in> \<univ> \<zpfun> \<univ>"
    by (mauto(fspace) msimp add: map_pfun_def)
} note b1 = this
{
  fix 
    f
  show
    "pfun_map (map_pfun f) = f"
  proof (rule ext)
    fix 
      x
    show
      "pfun_map (map_pfun f) x = f x"
      apply (cases "f x")
      apply (auto simp add: map_pfun_def pfun_map_def glambda_dom glambda_beta)
      done
  qed
next
  fix 
    g
  assume
    b2: "g \<in> \<univ> \<zpfun> \<univ>"
  with b1 [of "pfun_map g"] have 
    b3: "\<zdom> (map_pfun (pfun_map g)) = \<zdom> g"
    apply (mauto(fspace))
    apply (auto simp add: map_pfun_def pfun_map_def glambda_dom Map.dom_def)
    done
  show
    "map_pfun (pfun_map g) = g"
    apply (rule functional_eqI)
    using b1 [of "pfun_map g"] b2 b3
    apply (mauto(fspace))
    apply (rule functional_beta [symmetric])
    apply (assumption)
    apply (simp add: map_pfun_def pfun_map_def glambda_beta Map.dom_def)
    apply (rule functional_appl)
    apply (auto)
    done
}  
qed

text{*

More vacuous case results.

*}

lemma pfun_vacuous:
  "\<emptyset> \<zpfun> Y = {\<emptyset>}"
by (auto simp add: part_funs_def rel_vacuous functional_def)

lemma pfun_vacuous':
  "X \<zpfun> \<emptyset> = {\<emptyset>}"
  by (auto simp add: part_funs_def rel_vacuous' functional_def)

lemma tfun_vacuous:
  "\<emptyset> \<ztfun> Y = {\<emptyset>}"
by (auto simp add: total_funs_def pfun_vacuous)

lemma tfun_vacuous':
  "X \<ztfun> \<emptyset> = \<if> X = \<emptyset> \<then> {\<emptyset>} \<else> {} \<fi>"
  by (auto simp add: total_funs_def pfun_vacuous' functional_def)

lemma tfun_vacuous_iff:
  "X \<ztfun> Y = \<emptyset> \<Leftrightarrow> Y = \<emptyset> \<and> X \<noteq> \<emptyset>"
  apply (rule iffI [symmetric])
  apply (simp add: tfun_vacuous')
proof -
  assume
    b1: "X \<ztfun> Y = \<emptyset>"
  then show
    "Y = \<emptyset> \<and> X \<noteq> \<emptyset>"
    apply (rule contrapos_pp)
    apply (cases "X = \<emptyset>")
    apply (simp add: tfun_vacuous)
    apply (rule nemptyI [of "(\<glambda> x | x \<in> X \<bullet> (\<some> y | y \<in> Y))"])
    apply (mauto(fspace) mintro: glambda_functional msimp add: glambda_dom glambda_ran)
    apply (auto intro: someI2 simp add: nempty_conv)
    done
qed

text {*

Additional utility lemmas.

*}

lemma tfuns_conv:
  "f \<in> X \<ztfun> Y \<Leftrightarrow> \<zdom> f = X \<and> \<zran> f \<subseteq> Y \<and> functional f"
  apply (rule iffI)
  apply (mauto(fspace))
  done

lemma functional_unique_raw:
  "functional f \<Leftrightarrow> (\<forall> x y a \<bullet> (a \<mapsto> x) \<in> f \<and> (a \<mapsto> y) \<in> f \<Rightarrow> x = y)"
  by (auto intro!: functionalI elim!: functionalE)

lemma functional_conv_unique_raw:
  "functional (f\<^sup>\<sim>) \<Leftrightarrow> (\<forall> a b x \<bullet> (a \<mapsto> x) \<in> f \<and> (b \<mapsto> x) \<in> f \<Rightarrow> a = b)"
  by (auto intro!: functionalI elim!: functionalE)

lemma bijs_beta:
  "f \<in> X \<zbij> Y \<Leftrightarrow> \<zdom> f = X \<and> \<zran> f = Y \<and> functional f \<and> functional (f\<^sup>\<sim>)"
  by (mauto(fspace) mintro!: iffI) 

lemma union_in_bij:
  assumes 
    a1: "f \<in> X' \<zbij> Y'" and a2: "g \<in> X'' \<zbij> Y''" and
    a3: "part_list X [X', X'']" and
    a4: "part_list Y [Y', Y'']"
  shows 
    "f \<union> g \<in> X \<zbij> Y"
  using a1 a2 a3 a4
  apply (simp add: part_list_def)
  apply (mauto(fspace) msimp: converse_union Z_rel_union_dom Z_rel_union_ran)
  apply (auto simp add: disjoint_def dres_def Z_dom_def Z_ran_def set_eq_def)
  done

lemma chain_Union_functional:
  assumes
    a1: "subset.chain A C" and
    a2 [rule_format]: "(\<forall> f | f \<in> C \<bullet> functional f)"
  shows
    "functional (\<Union>C)"
  apply (rule rel_Union_functional)
  apply (simp add: a2)
proof -
  fix
    f g
  assume
    b1: "f \<in> C" and
    b2: "g \<in> C"
  from pred_on.chain_total [OF a1 b1 b2] have
    b3: "f \<subseteq> g \<or> g \<subseteq> f"
    by (auto)
  then show
    "\<zdom> g \<zdres> f = \<zdom> f \<zdres> g"
  proof 
    assume
      c1: "f \<subseteq> g"
    then have
      c2: "\<zdom> f \<subseteq> \<zdom> g"
      by (auto)
    have
      c3: "\<zdom> g \<zdres> f = f" 
    proof (auto simp add: dres_mem)
      fix 
        a b
      assume
        d1: "(a \<mapsto> b) \<in> f"
      then have
        d2: "(a \<mapsto> b) \<in> g"
        by (rule c1 [THEN subsetD])
      then show
        "a \<in> \<zdom> g"
        by (auto)
    qed
    have
      c4: "\<zdom> f \<zdres> g = f"
      apply (auto simp add: dres_mem)
      apply (auto)
    proof -
      fix
        a b c
      assume
        d1: "(a \<mapsto> b) \<in> f" and
        d2: "(a \<mapsto> c) \<in> g"
      from d1 c1 have
        d3: "(a \<mapsto> b) \<in> g"
        by (auto)
      from a2 [OF b2, THEN functional_beta, symmetric] d2 d3 have
        d4: "b = c"
        by (auto)
      with d1 show
        "(a \<mapsto> c) \<in> f"
        by (simp)
    qed (auto dest!: c1 [THEN subsetD])
    from c3 c4 show
      "\<zdom> g \<zdres> f = \<zdom> f \<zdres> g"
      by (auto)
  next
    assume
      c1: "g \<subseteq> f"
    then have
      c2: "\<zdom> g \<subseteq> \<zdom> f"
      by (auto)
    have
      c3: "\<zdom> f \<zdres> g = g" 
    proof (auto simp add: dres_mem)
      fix 
        a b
      assume
        d1: "(a \<mapsto> b) \<in> g"
      then have
        d2: "(a \<mapsto> b) \<in> f"
        by (rule c1 [THEN subsetD])
      then show
        "a \<in> \<zdom> f"
        by (auto)
    qed
    have
      c4: "\<zdom> g \<zdres> f = g"
      apply (auto simp add: dres_mem)
      apply (auto)
    proof -
      fix
        a b c
      assume
        d1: "(a \<mapsto> b) \<in> g" and
        d2: "(a \<mapsto> c) \<in> f"
      from d1 c1 have
        d3: "(a \<mapsto> b) \<in> f"
        by (auto)
      from a2 [OF b1, THEN functional_beta, symmetric] d2 d3 have
        d4: "b = c"
        by (auto)
      with d1 show
        "(a \<mapsto> c) \<in> g"
        by (simp)
    qed (auto dest!: c1 [THEN subsetD])
    from c3 c4 show
      "\<zdom> g \<zdres> f = \<zdom> f \<zdres> g"
      by (auto)
  qed
qed

lemma Z_inverse_mono:
  "f\<^sup>\<sim> \<subseteq> g\<^sup>\<sim> \<Leftrightarrow> f \<subseteq> g"
  "f\<^sup>\<sim> \<subset> g\<^sup>\<sim> \<Leftrightarrow> f \<subset> g"
  by (auto simp add: subset_def)

lemma Z_dom_mono:
  "f \<subseteq> g \<turnstile> \<zdom> f \<subseteq> \<zdom> g"
  by (auto)

lemma Z_ran_mono:
  "f \<subseteq> g \<turnstile> \<zran> f \<subseteq> \<zran> g"
  by (auto)

lemma bij_inv_bij_iff:
  "f\<^sup>\<sim> \<in> Y \<zbij> X \<Leftrightarrow> f \<in> X \<zbij> Y"
  using bij_tinj_inv_tinj [of "f" "X" "Y"] bij_tinj_inv_tinj [of "f\<^sup>\<sim>" "Y" "X"]
  by (auto)

lemma disjoint_dres_empty:
  assumes
    a1: "disjoint (\<zdom> f) (\<zdom> g)"
  shows
    "(\<zdom> g) \<zdres> f = (\<zdom> f) \<zdres> g"
  using a1 [THEN disjointD1] a1 [THEN disjointD2]
  apply (auto del: RangeE DomainE simp add: disjoint_def dres_mem)
  apply (auto del: RangeE DomainE dest!: DomainI)
  done

end 
