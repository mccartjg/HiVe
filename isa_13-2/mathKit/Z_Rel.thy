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

header {* Relational basics *}

theory 
  Z_Rel 
  
imports 
  Z_Sets
  Z_Rel_Chap

begin

subsection {* Of graphs and operators *}

text {*

HOL provides a built-in model for functions (value abstractions), embodied by the type
constructor @{text "fun"} and the $\lambda$-constructor. In the following we 
refer to this model as the \emph{operator} model of functions.

The single-valued \emph{graphs} also provide a convenient (and widely used)
mathematical model of functions. This is especially so
when partial or finite functions are of particular interest, as is
often the case in program specification. A graph is a set of pairs describing
the relationship between function argument and function result.

*}

type_synonym
  ('a, 'b) grel = "('a \<times> 'b) set" 

type_notation (xsymbols)
  "Z_Rel.grel" (infixr "\<leftrightarrow>" 0)

text {*

HOL also provides a built-in model for relations, namely as boolean valued operators
of two arguments, @{text "['a, 'b] \<rightarrow> \<bool>"}.\footnote{
As something of an anomaly, 
HOL makes use of the graph model in the pure mathematical theory @{text "Relation"}, 
but the operator model is used exclusively for concrete relations such as
orders}
It is straightforward, though inconvenient, to convert
between graph relations and operator relations.

*}

definition
  op2rel :: "('a \<rightarrow> 'b \<rightarrow> \<bool>) \<rightarrow> ('a \<leftrightarrow> 'b)"
where
  op2rel_def: "op2rel r \<defs> {a b | r a b \<bullet> (a, b)}"

definition
  rel2op :: "('a \<leftrightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b \<rightarrow> \<bool>)"
where
  rel2op_def: "rel2op r \<defs> (\<olambda> a b \<bullet> (a, b) \<in> r)"

notation (zed)
  op2rel ("\<^oprel>{:_:}") and
  rel2op ("\<^relop>{:_:}")

interpretation
  opgrf: type_definition "op2rel" "rel2op" "\<univ>-['a \<leftrightarrow> 'b]"
  apply (unfold type_definition_def)
  apply (msafe(inference))
  apply (simp_all)
proof -
  fix r
  show "rel2op (op2rel r) = r"
    apply (intro ext)
    apply (simp add: op2rel_def rel2op_def)
    done
next
  fix r 
  show "op2rel (rel2op r) = r"
    apply (intro set_eqI)
    apply (auto simp add: op2rel_def rel2op_def)
    done
qed

text {*

In the following we develop a graph model of relations, based on the
Z mathematical toolkit as described by Spivey~\cite{Spivey:ZRef}. 
In the next chapter, we develop a model of single-valued graphs viewed as 
functions.

*}

subsection {* Relation spaces *}

text {*

The relations from @{text X} to @{text Y}~\cite[p 95]{Spivey:ZRef}\cite[p 94]{ZStand02}
are relations over the base types of @{text X} and @{text Y}, with domain in @{text X}
and range in @{text Y}.


*}

definition
  rel :: "['a set, 'b set] \<rightarrow> ('a \<leftrightarrow> 'b) set"
where
  rel_def: "rel X Y \<defs> \<pset> (X \<times> Y)"

notation (xsymbols)
  rel (infixr "\<zrel>" 92)

text {*

It is convenient to define a special syntax for 
pairs~\cite[p 95]{Spivey:ZRef}\cite[p 98]{ZStand02}
when used to define relations.

*}

syntax (zed)
  "_Z_Rel\<ZZ>maplet" :: "['a, 'b] \<rightarrow> ('a \<times> 'b)" ("_ \<mapsto> _" [0,0] 11)

translations
  "_Z_Rel\<ZZ>maplet a b" \<rightharpoonup> "CONST Pair a b"

definition
  Z_maplet :: "['a, 'b] \<rightarrow> ('a \<times> 'b)"
where
  Z_maplet_def [simp]: "Z_maplet x y \<defs> (x, y)"

notation (xsymbols)
  Z_maplet ("_ \<zmapsto> _" [0,0] 11)

lemma Z_maplet_eq_pair:
  "(\<forall> x y | x \<in> X \<and> y \<in> Y \<bullet> (x \<zmapsto> y) = (x, y))"
  by (auto)

text {*

Spivey uses infix relational application in the laws about @{text "\<zdom>"}
and @{text "\<zran>"}, so we introduce a parse syntax for it.

*}

syntax (zed)
  "_Z_Rel\<ZZ>infrel" :: "[logic, logic, logic] \<rightarrow> logic" ("\<^infrel>{:_:}{:_:}{:_:}")
  "_Z_Rel\<ZZ>infrela" :: "[logic, logic, logic] \<rightarrow> logic" ("\<^infrela>{:_:}{:_:}{:_:}")

translations
  "\<^infrel>{:a:}{:R:}{:b:}" \<rightharpoonup> "(a \<mapsto> b) \<in> R"
  "\<^infrela>{:a:}{:R:}{:b:}" \<rightharpoonup> "(a \<mapsto> b) \<in> R"

definition
  Z_inf_rel :: "['a, 'a \<leftrightarrow> 'b, 'b] \<rightarrow> \<bool>"
where
  Z_inf_rel_def [simp]: "Z_inf_rel x R y \<defs> (x \<zmapsto> y) \<in> R"

notation (xsymbols output)
  Z_inf_rel ("_ '__'_ _" [1000, 1000, 1000] 1000)

notation (zed)
  Z_inf_rel ("\<^zinfrel>{:_:}{:_:}{:_:}")

syntax (zed)
  "_Z_Rel\<ZZ>Z_inf_rela" :: "['a, 'a \<leftrightarrow> 'b, 'b] \<rightarrow> \<bool>" ("\<^zinfrela>{:_:}{:_:}{:_:}")

translations
  "\<^zinfrela>{:a:}{:R:}{:b:}" \<rightharpoonup> "\<^zinfrel>{:a:}{:R:}{:b:}"

subsection {* Equality between relations *}

text {*

The various set equality rules work for relations, but it is useful
to have a specialised version of @{text set_eqI} for when @{text auto} is
over eager.

*}

lemma rel_eqI: 
  assumes 
    a1: "(\<And> x y \<bullet> (x \<mapsto> y) \<in> R \<Leftrightarrow> (x \<mapsto> y) \<in> S)"
  shows 
    "R = S"
  using a1
  by (auto)

lemma rel_eq_def: 
  "R = S \<Leftrightarrow> (\<forall> x y \<bullet> (x \<mapsto> y) \<in> R \<Leftrightarrow> (x \<mapsto> y) \<in> S)"
  by (auto intro!: rel_eqI)

subsection {* Domain and range *} 

text {*

Domain and range operators~\cite[p 96]{Spivey:ZRef}\cite[p 98]{ZStand02} are 
already defined. 
We make use of these existing type generic operators,
introducing Z-style syntax for them.


*}

(*
notation (xsymbols output)
  Domain ("\<^bold>d\<^bold>o\<^bold>m") and
  Range ("\<^bold>r\<^bold>a\<^bold>n")
*)

notation (xsymbols)
  Domain ("\<zdom>") and
  Range ("\<zran>")

lemma Z_dom_def:
  "\<zdom> R = { x y | \<^zinfrel>{:x:}{:R:}{:y:} \<bullet> x}"
  by (auto simp add: Domain_unfold)+

lemma Z_ran_def:
  "\<zran> R = { x y | \<^zinfrel>{:x:}{:R:}{:y:} \<bullet> y}"
  unfolding Domain_converse [symmetric]
  by (auto simp add: Domain_unfold)

lemma Z_dom_ran_def:
  "\<forall> R | R \<in> X \<zrel> Y \<bullet> 
    \<zdom> R = { x y | x \<in> X \<and> y \<in> Y \<and> \<^infrel>{:x:}{:R:}{:y:} \<bullet> x} \<and>
    \<zran> R = { x y | x \<in> X \<and> y \<in> Y \<and> \<^infrel>{:x:}{:R:}{:y:} \<bullet> y}"
  by (auto simp add: Z_ran_def Z_dom_def rel_def subset_def)+

lemma rel_dr: "R \<in> X \<zrel> Y \<Leftrightarrow> \<zdom> R \<subseteq> X \<and> \<zran> R \<subseteq> Y"
  by (auto simp add: rel_def)

lemma in_relI: "\<lbrakk> \<zdom> R \<subseteq> X; \<zran> R \<subseteq> Y \<rbrakk> \<turnstile> R \<in> X \<zrel> Y"
  by (auto simp add: rel_def)

lemma in_relE:
  assumes 
    a1: "R \<in> X \<zrel> Y" and
    a2: "\<lbrakk> \<zdom> R \<subseteq> X; \<zran> R \<subseteq> Y \<rbrakk> \<turnstile> P"
  shows "P"
  using a1 a2
  by (auto simp add: rel_def)

lemma rel_dom_mem:
  assumes 
    a1: "r \<in> X \<zrel> Y" and 
    a2: "(x \<mapsto> y) \<in> r"
  shows "x \<in> X"
  using a1 a2
  by (auto simp add: rel_def)

lemma rel_ran_mem:
  assumes 
    a1: "r \<in> X \<zrel> Y" and 
    a2: "(x \<mapsto> y) \<in> r"
  shows "y \<in> Y"
  using a1 a2
  by (auto simp add: rel_def)

lemma rel_memD:
  assumes
    a1: "r \<in> X \<zrel> Y" and
    a2: "(x \<mapsto> y) \<in> r"
  shows
    "x \<in> X \<and> y \<in> Y"
  using a1 a2
  by (auto simp add: rel_def)

lemma rel_memD_dom:
  assumes
    a1: "\<zdom> r \<subseteq> X" and
    a2: "(x \<mapsto> y) \<in> r"
  shows
    "x \<in> X"
  using a1 a2
  by (auto)

lemma rel_memD_ran:
  assumes
    a1: "\<zran> r \<subseteq> Y" and
    a2: "(x \<mapsto> y) \<in> r"
  shows
    "y \<in> Y"
  using a1 a2
  by (auto)

lemma in_relD1: 
  assumes 
    a1: "r \<in> X \<zrel> Y"
  shows 
    "\<zdom> r \<subseteq> X"
  using a1
  by (auto intro: rel_dom_mem)

lemma in_relD2: 
  assumes 
    a1: "r \<in> X \<zrel> Y"
  shows 
    "\<zran> r \<subseteq> Y"
  using a1
  by (auto intro: rel_ran_mem)

lemma Z_in_domD:
  assumes 
    a1: "r \<in> X \<zrel> Y"
  shows "x \<in> \<zdom> r \<Leftrightarrow> (\<exists> y | y \<in> Y \<bullet> \<^zinfrel>{:x:}{:r:}{:y:})"
  using a1
  by (auto simp add: rel_def)

lemma Z_in_ranD:
  assumes 
    a1: "r \<in> X \<zrel> Y"
  shows "y \<in> \<zran> r \<Leftrightarrow> (\<exists> x | x \<in> X \<bullet> \<^zinfrel>{:x:}{:r:}{:y:})"
  using a1
  by (auto simp add: rel_def)


lemma dom_char1: 
  assumes 
    a1: "R \<in> X \<zrel> Y"
  shows "x \<in> \<zdom> R \<Rightarrow> x \<in> X"
  using a1
  by (auto simp add: rel_def)

lemma dom_char2: 
  assumes 
    a1: "R \<in> X \<zrel> Y"
  shows "x \<in> \<zdom> R \<Leftrightarrow> (\<exists> y | y \<in> Y \<bullet> \<^infrel>{:x:}{:R:}{:y:})"
  using a1
  by (auto simp add: rel_def)

lemma ran_char1: 
  assumes 
    a1: "R \<in> X \<zrel> Y"
  shows "y \<in> \<zran> R \<Rightarrow> y \<in> Y"
  using a1
  by (auto simp add: rel_def)

lemma ran_char2: 
  assumes 
    a1: "R \<in> X \<zrel> Y"
  shows "y \<in> \<zran> R \<Leftrightarrow> (\<exists> x | x \<in> X \<bullet> \<^infrel>{:x:}{:R:}{:y:})"
  using a1
  by (auto simp add: rel_def)

lemma rel_min: "R \<in> (\<zdom> R) \<zrel> (\<zran> R)"
  by (auto simp add: rel_def)

lemmas ran_char_min = ran_char2 [OF rel_min]

lemma dom_eind0:
  "\<zdom> (Collect (eind Pt)) = Collect (eind (\<olambda> x \<bullet> (fst (Pt x), fst (snd (Pt x)))))"
  (is "?LHS = ?RHS")
proof (auto simp add: eind_def Z_dom_def)
  fix
    x a xa
  assume
    b1: "(x \<mapsto> a) = snd (Pt xa)" and
    b2: "fst (Pt xa)"
  then show
    "(\<exists> xa \<bullet> x = fst (snd (Pt xa)) \<and> fst (Pt xa))"
    apply (witness "xa")
    apply (cases "Pt xa")
    apply (auto)
    done
next
  fix
    xa
  assume
    b1: "fst (Pt xa)"
  show
    "(\<exists> a x \<bullet> (fst (snd (Pt xa)), a) = snd (Pt x) \<and> fst (Pt x))"
    apply (witness "snd (snd (Pt xa))")
    apply (witness "xa")
    using b1
    apply (cases "Pt xa")   
    apply (auto)
    done
qed

lemma eind_split_dom: "(\<olambda> x \<bullet> (fst (prod_case (\<olambda> a \<bullet> Pt a) x), fst (snd (prod_case (\<olambda> a \<bullet> Pt a) x))))
= prod_case (\<olambda> a x \<bullet> (fst (Pt a x), fst (snd (Pt a x))))"
  by (auto)

lemmas dom_eind = dom_eind0 eind_split_dom

lemma ran_eind0:
  "\<zran> (Collect (eind Pt)) = Collect (eind (\<olambda> x \<bullet> (fst (Pt x), snd (snd (Pt x)))))"
  (is "?LHS = ?RHS")
proof (auto simp add: eind_def Z_ran_def)
  fix
    x a xa
  assume
    b1: "(x \<mapsto> a) = snd (Pt xa)" and
    b2: "fst (Pt xa)"
  then show
    "(\<exists> xa \<bullet> a = snd (snd (Pt xa)) \<and> fst (Pt xa))"
    apply (witness "xa")
    apply (cases "Pt xa")
    apply (auto)
    done
next
  fix
    xa
  assume
    b1: "fst (Pt xa)"
  show
    "(\<exists> a x \<bullet> (a, snd (snd (Pt xa))) = snd (Pt x) \<and> fst (Pt x))"
    apply (witness "fst (snd (Pt xa))")
    apply (witness "xa")
    using b1
    apply (cases "Pt xa")   
    apply (auto)
    done
qed

lemma eind_split_ran: "(\<olambda> x \<bullet> (fst (prod_case (\<olambda> a \<bullet> Pt a) x), snd (snd (prod_case (\<olambda> a \<bullet> Pt a) x))))
= prod_case (\<olambda> a x \<bullet> (fst (Pt a x), snd (snd (Pt a x))))"
  by (auto)

lemmas ran_eind = ran_eind0 eind_split_ran

lemma dom_Collect:
  "y \<in> \<zdom> { x | (\<exists> a \<bullet> p x a) } \<Leftrightarrow> (\<exists> a \<bullet> y \<in> \<zdom> { x | p x a })"
  "y \<in> \<zdom> { x | x = (a \<mapsto> b) \<and> q } \<Leftrightarrow> y = a \<and> q"
  "y \<in> \<zdom> { x | x = (a \<mapsto> b) } \<Leftrightarrow> y = a"
  "y \<in> \<zdom> { (a \<mapsto> b) } \<Leftrightarrow> y = a"
  by (auto simp add: Z_dom_def)

lemma ran_Collect:
  "y \<in> \<zran> { x | (\<exists> a \<bullet> p x a) } \<Leftrightarrow> (\<exists> a \<bullet> y \<in> \<zran> { x | p x a })"
  "y \<in> \<zran> { x | x = (a \<mapsto> b) \<and> q } \<Leftrightarrow> y = b \<and> q"
  "y \<in> \<zran> { x | x = (a \<mapsto> b) } \<Leftrightarrow> y = b"
  "y \<in> \<zran> { (a \<mapsto> b) } \<Leftrightarrow> y = b"
  by (auto simp add: Z_ran_def)

lemma Z_rel_empty_dom_iff:
  "\<zdom> r = \<emptyset> \<Leftrightarrow> r = \<emptyset>"
  by (auto)

lemma Z_rel_empty_ran_iff:
  "\<zran> r = \<emptyset> \<Leftrightarrow> r = \<emptyset>"
  by (auto)


subsection {* Set operations on relations *}

lemma Z_rel_union_in_relI:
  assumes 
    a1: "R_d_1 \<in> X \<zrel> Y" "R_d_2 \<in> X \<zrel> Y"
  shows "R_d_1 \<union> R_d_2 \<in> X \<zrel> Y"
  using a1
  by (auto simp add: rel_def)

lemma Z_rel_inter_in_relI:
  assumes 
     a1: "R_d_1 \<in> X \<zrel> Y" "R_d_2 \<in> X \<zrel> Y"
  shows "R_d_1 \<inter> R_d_2 \<in> X \<zrel> Y"
  using a1
  by (auto simp add: rel_def)
    
lemma Z_rel_union_dom: 
   "\<zdom> (R_d_1 \<union> R_d_2) = (\<zdom> R_d_1) \<union> (\<zdom> R_d_2)"  
  by (auto)

lemma Z_rel_union_ran: 
   "\<zran> (R_d_1 \<union> R_d_2) = (\<zran> R_d_1) \<union> (\<zran> R_d_2)"  
  by (auto)

lemma rel_Union_dom:
  "\<zdom> (\<Union>CL_F) = \<Union>{f | f \<in> CL_F \<bullet> \<zdom> f}"
  by (auto)+

lemma rel_Union_ran:
  "\<zran> (\<Union>CL_F) = \<Union>{f | f \<in> CL_F \<bullet> \<zran> f}"
  by (auto)+

lemma rel_Union_dom':
  "\<zdom> (\<Union> x \<bullet> f x) = \<Union>{x \<bullet> \<zdom> (f x)}"
  "\<zdom> (\<Union> x | b x \<bullet> f x) = \<Union>{ x | b x \<bullet> \<zdom> (f x) }"
  by (auto simp add: Z_dom_def eind_def)

lemma rel_Union_ran':
  "\<zran> (\<Union> x \<bullet> f x) = \<Union>{x \<bullet> \<zran> (f x)}"
  "\<zran> (\<Union> x | b x \<bullet> f x) = \<Union>{ x | b x \<bullet> \<zran> (f x) }"
  by (auto simp add: Z_ran_def eind_def)+
    
lemma Z_rel_inter_dom: 
   "\<zdom> (R_d_1 \<inter> R_d_2) \<subseteq> (\<zdom> R_d_1) \<inter> (\<zdom> R_d_2)"  
  by (auto)

lemma Z_rel_inter_ran: 
   "\<zran> (R_d_1 \<inter> R_d_2) \<subseteq> (\<zran> R_d_1) \<inter> (\<zran> R_d_2)"  
  by (auto)

lemma rel_Inter_dom:
  "\<zdom> (\<Inter>CL_F) \<subseteq> \<Inter>{ f | f \<in> CL_F \<bullet> \<zdom> f }"
  by (auto)+

lemma rel_Inter_ran:
  "\<zran> (\<Inter>CL_F) \<subseteq> \<Inter>{ f | f \<in> CL_F \<bullet> \<zran> f }"
  by (auto)+

lemma Z_rel_insert_dom:
  "\<zdom> (insert (x \<mapsto> y) R) = insert x (\<zdom> R)"
  by (auto)

lemma Z_rel_empty_dom:
  "\<zdom> \<emptyset> = \<emptyset>"
  by (auto)

lemma Z_rel_insert_ran:
  "\<zran> (insert (x \<mapsto> y) R) = insert y (\<zran> R)"
  by (auto)

lemma Z_rel_empty_ran:
  "\<zran> \<emptyset> = \<emptyset>"
  by (auto)

section {* Identity and composition *}

text {*

The relations form a category under relational composition~\cite[p 97]{Spivey:ZRef}\cite[p 98,99]{ZStand02}

*}

definition
  rel_id :: "'a set \<rightarrow> ('a \<leftrightarrow> 'a)"
where
  rel_id_def: "rel_id X \<defs> {x | x \<in> X \<bullet> (x \<mapsto> x)}"

notation (xsymbols)
  relcomp (infixr "\<zfcomp>" 60)

definition
  rel_bcomp :: "['b \<leftrightarrow> 'c, 'a \<leftrightarrow> 'b] \<rightarrow> ('a \<leftrightarrow> 'c)"
where
  rel_bcomp_def: "rel_bcomp Q R \<defs> { a c | (\<exists> b \<bullet> (a \<mapsto> b) \<in> R \<and> (b \<mapsto> c) \<in> Q) \<bullet> (a \<mapsto> c) }"

notation (xsymbols)
  rel_id ("\<zid>") and
  rel_bcomp (infixr "\<zbcomp>" 60)

lemma rel_fcomp_def:
  "R \<zfcomp> Q = Q \<zbcomp> R"
  by (auto simp add: rel_bcomp_def relcomp_def)

lemma Z_rel_id_def:
  "\<zid> X \<defs> { x | x \<in> X \<bullet> x \<zmapsto> x }"
  by (simp add: rel_id_def)

lemma Z_fcomp_comp_def:
  "(\<forall> Q R | Q \<in> X \<zrel> Y \<and> R \<in> Y \<zrel> Z \<bullet>
    \<lch> 
      Q \<zfcomp> R 
    \<chEq> 
      R \<zbcomp> Q 
    \<chEq> 
      { x y z 
      | x \<in> X \<and> y \<in> Y \<and> z \<in> Z \<and> \<^infrel>{:x:}{:Q:}{:y:} \<and> \<^infrel>{:y:}{:R:}{:z:} 
      \<bullet> x \<mapsto> z} \<rch>)"
  apply (msafe(inference))
  apply (simp add: rel_fcomp_def rel_bcomp_def rel_id_def)
  apply (auto simp add: rel_bcomp_def)
proof -
  fix Q R a b y
  assume 
    b0: "Q \<in> X \<zrel> Y" and 
    b1: "(a, y) \<in> Q"
  from rel_dom_mem [OF b0 b1] show 
    "a \<in> X" 
    by this
next
  apply_end (intro exI conjI)
  fix Q R a b y
  assume 
    b0: "Q \<in> X \<zrel> Y" and 
    b2: "R \<in> Y \<zrel> Z" and 
    b3: "(a \<mapsto> y) \<in> Q" and 
    b4: "(y \<mapsto> b) \<in> R"
  show 
    "y \<in> Y"
    "b \<in> Z" 
    "(a \<mapsto> y) \<in> Q"
    "(y \<mapsto> b) \<in> R"
    apply (auto simp add: b3 b4)
    apply (rule rel_ran_mem [OF b0 b3])
    apply (rule rel_ran_mem [OF b2 b4])
    done
qed

lemma Z_fcomp_def:
  "Q \<zfcomp> R \<defs> R \<zbcomp> Q"
  by (simp add: rel_fcomp_def rel_bcomp_def)

lemma Z_bcomp_def:
  "R \<zbcomp> Q \<defs> { x y z | \<^zinfrel>{:x:}{:Q:}{:y:} \<and> \<^zinfrel>{:y:}{:R:}{:z:} \<bullet> x \<zmapsto> z}"
  apply (rule eq_reflection)
  apply (auto simp add: rel_bcomp_def)
  done

lemma id_in_relI: 
  "\<zid> X \<in> X \<zrel> X"
  by (rule in_relI, auto simp add: rel_id_def)

lemma bcomp_in_relI: 
  assumes 
    a1: "Q \<in> X \<zrel> Y" "R \<in> Y \<zrel> Z"
  shows "R \<zbcomp> Q \<in> X \<zrel> Z"
  using a1
  by (auto simp add: rel_dr rel_bcomp_def)+

lemma fcomp_in_relI: 
  assumes 
    a1: "Q \<in> X \<zrel> Y" "R \<in> Y \<zrel> Z"
  shows "Q \<zfcomp> R \<in> X \<zrel> Z"
  using a1
  by (auto simp add: rel_fcomp_def rel_bcomp_def rel_dr)+

lemma Z_rel_id_mem:
  shows 
    Z_rel_id_mema: "(x \<zmapsto> x') \<in> \<zid> X \<Leftrightarrow> \<lch> x \<chEq> x' \<chIn> X \<rch>" and
    Z_rel_id_memb: "(x \<mapsto> x') \<in> \<zid> X \<Leftrightarrow> \<lch> x \<chEq> x' \<chIn> X \<rch>"
  by (auto simp add: rel_id_def)

lemma Z_rel_bcomp_mem:
  shows 
    Z_rel_bcomp_mema: "(x \<zmapsto> z) \<in> P \<zbcomp> Q \<Leftrightarrow> (\<exists> y \<bullet> \<^zinfrel>{:x:}{:Q:}{:y:} \<and> \<^zinfrel>{:y:}{:P:}{:z:})" and
    Z_rel_bcomp_memb: "(x \<mapsto> z) \<in> P \<zbcomp> Q \<Leftrightarrow> (\<exists> y \<bullet> \<^zinfrel>{:x:}{:Q:}{:y:} \<and> \<^zinfrel>{:y:}{:P:}{:z:})"
  by (auto simp add: rel_bcomp_def)

lemma Z_rel_fcomp_mem:
  shows 
    Z_rel_fcomp_mema: 
      "(x \<zmapsto> z) \<in> P \<zfcomp> Q \<Leftrightarrow> (\<exists> y \<bullet> \<^zinfrel>{:x:}{:P:}{:y:} \<and> \<^zinfrel>{:y:}{:Q:}{:z:})" and
    Z_rel_fcomp_memb: 
      "(x \<mapsto> z) \<in> P \<zfcomp> Q \<Leftrightarrow> (\<exists> y \<bullet> \<^zinfrel>{:x:}{:P:}{:y:} \<and> \<^zinfrel>{:y:}{:Q:}{:z:})"
  by (auto simp add: rel_fcomp_def rel_bcomp_def)

lemma Z_rel_bcomp_memI:
  assumes 
    a1: "\<^infrel>{:x:}{:Q:}{:y:}" "\<^infrel>{:y:}{:P:}{:z:}"
  shows "(x \<mapsto> z) \<in> P \<zbcomp> Q"
  using a1
  by (auto simp add: rel_bcomp_def)

lemma Z_rel_fcomp_memI:
  assumes 
    a1: "\<^infrel>{:x:}{:P:}{:y:}" "\<^infrel>{:y:}{:Q:}{:z:}"
  shows "(x \<mapsto> z) \<in> P \<zfcomp> Q"
  using a1
  by (auto simp add: rel_fcomp_def rel_bcomp_def)

lemma Z_rel_fcomp_assoc:
  "(P \<zfcomp> Q) \<zfcomp> R = P \<zfcomp> (Q \<zfcomp> R)"
  by (auto simp add: rel_fcomp_def rel_bcomp_def)+

lemma rel_lident:
  "P \<in> X \<zrel> Y \<turnstile> \<zid> X \<zfcomp> P = P"
  by (auto simp add: rel_id_def rel_fcomp_def rel_bcomp_def rel_def)

lemma Z_rel_lident':
  "\<zid> (\<zdom> P) \<zfcomp> P = P"
  apply (rule rel_lident)
  apply (rule in_relI)
  apply (rule subset_refl)
  apply (rule subset_refl)
  done

lemma rel_rident:
  "P \<in> X \<zrel> Y \<turnstile> P \<zfcomp> \<zid> Y = P"
  by (auto simp add: rel_id_def rel_fcomp_def rel_bcomp_def rel_def)

lemma Z_rel_rident':
  "P \<zfcomp> \<zid> (\<zran> P) = P"
  apply (rule rel_rident)
  apply (rule in_relI)
  apply (rule subset_refl)
  apply (rule subset_refl)
  done

lemma Z_rel_id_fcomp:
  "\<zid> V \<zfcomp> \<zid> W = \<zid> (V \<inter> W)"
  by (auto simp add: rel_id_def rel_fcomp_def rel_bcomp_def)

lemma rel_bcomp_union:
  "(R_d_1 \<union> R_d_2) \<zbcomp> Q = (R_d_1 \<zbcomp> Q) \<union> (R_d_2 \<zbcomp> Q)"
  "R \<zbcomp> (Q_d_1 \<union> Q_d_2) = (R \<zbcomp> Q_d_1) \<union> (R \<zbcomp> Q_d_2)"
  by (auto simp add: rel_bcomp_def)

lemma rel_fcomp_union:
  "(R_d_1 \<union> R_d_2) \<zfcomp> Q = (R_d_1 \<zfcomp> Q) \<union> (R_d_2 \<zfcomp> Q)"
  "R \<zfcomp> (Q_d_1 \<union> Q_d_2) = (R \<zfcomp> Q_d_1) \<union> (R \<zfcomp> Q_d_2)"
  by (auto simp add: rel_fcomp_def rel_bcomp_def)

section {* Domain and range restriction *}

text {*

Domain and range restrictions filter the maplets in a relation according
to whether they fall into (or out of) a domain or range set respectively.

*}

definition
  dres :: "['a set, 'a \<leftrightarrow> 'b] \<rightarrow> ('a \<leftrightarrow> 'b)"
where
  dres_def: "dres U R \<defs> {x y | x \<in> U \<and> \<^infrel>{:x:}{:R:}{:y:} \<bullet> (x \<mapsto> y)}"

definition
  dsub ::"['a set, 'a \<leftrightarrow> 'b] \<rightarrow> ('a \<leftrightarrow> 'b)" 
where
  dsub_def: "dsub U R \<defs> {x y | x \<notin> U \<and> \<^infrel>{:x:}{:R:}{:y:} \<bullet> (x \<mapsto> y)}"

definition
  rres :: "[('a \<leftrightarrow> 'b), 'b set] \<rightarrow> ('a \<leftrightarrow> 'b)"
where
  rres_def: "rres R V \<defs> {x y | y \<in> V \<and> \<^infrel>{:x:}{:R:}{:y:} \<bullet> (x \<mapsto> y)}"

definition
  rsub :: "[('a \<leftrightarrow> 'b), 'b set] \<rightarrow> ('a \<leftrightarrow> 'b)"
where
  rsub_def: "rsub R V \<defs> {x y | y \<notin> V \<and> \<^infrel>{:x:}{:R:}{:y:} \<bullet> (x \<mapsto> y)}"

notation (xsymbols)
  dres (infixr "\<zdres>" 75) and
  dsub (infixr "\<zdsub>" 75) and
  rres (infixl "\<zrres>" 70) and
  rsub (infixl "\<zrsub>" 70)

lemma Z_dres_def:
  "S \<zdres> R \<defs> { x y | x \<in> S \<and> \<^zinfrel>{:x:}{:R:}{:y:} \<bullet> x \<zmapsto> y }"
  by (auto simp add: rel_def dres_def)

lemma Z_rres_def:
  "R \<zrres> T \<defs> { x y | y \<in> T \<and> \<^zinfrel>{:x:}{:R:}{:y:} \<bullet> x \<zmapsto> y }"
  by (auto simp add: rel_def rres_def)

lemma Z_dsub_def:
  "S \<zdsub> R \<defs> { x y | x \<notin> S \<and> \<^zinfrel>{:x:}{:R:}{:y:} \<bullet> x \<zmapsto> y }"
  by (auto simp add: rel_def dsub_def)

lemma Z_rsub_def:
  "R \<zrsub> T \<defs> { x y | y \<notin> T \<and> \<^zinfrel>{:x:}{:R:}{:y:} \<bullet> x \<zmapsto> y }"
  by (auto simp add: rel_def rsub_def)

lemma dres_mem:
  "(x \<mapsto> y) \<in> U \<zdres> R \<Leftrightarrow> x \<in> U \<and> (x, y) \<in> R"
  by (simp add: dres_def)

lemma dsub_mem:
  "(x \<mapsto> y) \<in> U \<zdsub> R \<Leftrightarrow> x \<notin> U \<and> (x, y) \<in> R"
  by (simp add: dsub_def)

lemma rres_mem:
  "(x \<mapsto> y) \<in> R \<zrres> V \<Leftrightarrow> y \<in> V \<and> (x, y) \<in> R"
  by (simp add: rres_def)

lemma rsub_mem:
  "(x \<mapsto> y) \<in> R \<zrsub> V \<Leftrightarrow> y \<notin> V \<and> (x, y) \<in> R"
  by (simp add: rsub_def)

lemma Z_dres_dom: 
  "\<zdom> (U \<zdres> R) = U \<inter> (\<zdom> R)"
  by (auto simp add: dres_def)

lemma Z_rres_ran:
  "\<zran> (R \<zrres> T) = (\<zran> R) \<inter> T"
  by (auto simp add: rres_def)

lemma dsub_dom: 
  "\<zdom> (U \<zdsub> R) = (\<zdom> R) - U"
  by (auto simp add: dsub_def)

lemma rsub_ran:
  "\<zran> (R \<zrsub> U) = (\<zran> R) - U"
  by (auto simp add: rsub_def)

lemma dres_id_char: 
  "U \<zdres> R = \<zid> U \<zfcomp> R"
  by (auto simp add: dres_def rel_id_def rel_fcomp_def rel_bcomp_def)

lemma dres_inter_char: 
  assumes 
    a1: "R \<in> X \<zrel> Y"
  shows "U \<zdres> R = U \<times> Y \<inter> R"
  using a1
  by (auto simp add: rel_def dres_def)

lemma Z_dres_id_inter:
  assumes 
    a1: "R \<in> X \<zrel> Y"
  shows "\<lch>S \<zdres> R \<chEq> \<zid> S \<zfcomp> R \<chEq> (S \<times> Y) \<inter> R \<rch>"
  using a1
  by (auto simp add: rel_def dres_def rel_id_def rel_fcomp_def rel_bcomp_def)

lemma Z_dsub_id_char: 
  "U \<zdsub> R = (\<univ> \<setminus> U) \<zdres> R"
  by (auto simp add: dres_def dsub_def)

lemma rres_id_char: 
  "R \<zrres> V = R \<zfcomp> \<zid> V"
  by (auto simp add: rres_def rel_id_def rel_fcomp_def rel_bcomp_def)

lemma rres_inter_char: 
  assumes 
    a1: "R \<in> X \<zrel> Y"
  shows "R \<zrres> V = R \<inter> X \<times> V"
  using a1
  by (auto simp add: rres_def rel_def)

lemma Z_rres_id_inter:
  assumes 
    a1: "R \<in> X \<zrel> Y"
  shows "\<lch> R \<zrres> T \<chEq> R \<zfcomp> \<zid> T \<chEq> R \<inter> (X \<times> T) \<rch>"
  using a1
  by (auto simp add: rres_def rel_id_def rel_fcomp_def rel_bcomp_def rel_def)

lemma Z_dres_sub_self:
  "S \<zdres> R \<subseteq> R"
  by (auto simp add: dres_def)

lemma Z_rres_sub_self:
  "R \<zrres> T \<subseteq> R"
  by (auto simp add: rres_def)

lemma Z_dsub_sub_self:
  "S \<zdsub> R \<subseteq> R"
  by (auto simp add: dsub_def)

lemma Z_rsub_sub_self:
  "R \<zrsub> T \<subseteq> R"
  by (auto simp add: rsub_def)

lemma Z_rsub_id_char: 
  "R \<zrsub> V = R \<zrres> (\<univ> \<setminus> V)"
  by (auto simp add: rres_def rsub_def)

lemma Z_dr_res_assoc: 
  "(U \<zdres> R) \<zrres> V = U \<zdres> (R \<zrres> V)"
  by (auto simp add: dres_def rres_def)

lemma Z_dres_dist: 
  "U \<zdres> V \<zdres> R = (U \<inter> V) \<zdres> R"
  by (auto simp add: dres_def)

lemma dsub_dist: 
  "U \<zdsub> V \<zdsub> R = (U \<union> V) \<zdsub> R"
  by (auto simp add: dsub_def)

lemma Z_rres_dist: 
  "R \<zrres> U \<zrres> V = R \<zrres> (U \<inter> V)"
  by (auto simp add: rres_def)

lemma rsub_dist: 
  "R \<zrsub> U \<zrsub> V = R \<zrsub> (U \<union> V)"
  by (auto simp add: rsub_def)

lemma Z_dpart_rel: 
  "(U \<zdres> R) \<union> (U \<zdsub> R) = R"
  by (auto simp add: dres_def dsub_def)

lemma dres_union_dist1: 
  "(U \<zdres> R) \<union> (U \<zdres> S) = (U \<zdres> (R \<union> S))"
  by (auto simp add: dres_def)

lemma dres_union_dist2: 
  "(U \<zdres> R) \<union> (V \<zdres> R) = ((U \<union> V) \<zdres> R)"
  by (auto simp add: dres_def)

lemma dsub_union_dist1: 
  "(U \<zdsub> R) \<union> (U \<zdsub> S) = (U \<zdsub> (R \<union> S))"
  by (auto simp add: dsub_def)

lemma dsub_union_dist2: 
  "(U \<zdsub> R) \<union> (V \<zdsub> R) = ((U \<inter> V) \<zdsub> R)"
  by (auto simp add: dsub_def)

lemma dres_elim: 
  assumes 
    a1: "\<zdom> R \<inter> U = \<zdom> R" 
  shows "U \<zdres> R = R"
  using a1
  by (auto simp add: dres_def)

lemma dsub_elim: 
  assumes 
    a1: "disjoint (\<zdom> R) U"
  shows "U \<zdsub> R = R"
  using a1
  by (auto simp add: dsub_def disjoint_def)

lemma dres_elim': 
  assumes 
    a1: "disjoint (\<zdom> R) U"
  shows "U \<zdres> R = \<emptyset>"
  using a1
  apply (auto simp only: dres_def Z_maplet_def disjoint_def Z_dom_def)
  apply (auto simp add: set_eq_def)
  done

lemma dsub_elim': 
  assumes 
    a1: "\<zdom> R \<inter> U = \<zdom> R"
  shows "U \<zdsub> R = \<emptyset>"
  using a1
  apply (auto simp only: dsub_def Z_maplet_def)
  apply (auto simp add: set_eq_def)
  done

lemma dres_restrict_self:
  assumes 
    a1: "\<zdom> R = U" 
  shows "(U \<zdres> R) = R"
  using a1
  by (auto simp add: dres_def Domain_def)

lemma dsub_mono:
  "S \<subseteq> T \<Rightarrow> (T \<zdsub> R) \<subseteq> (S \<zdsub> R)"
  by (auto simp add: dsub_def)

lemma Z_rpart_rel: 
  "(R \<zrres> T) \<union> (R \<zrsub> T) = R"
  by (auto simp add: rres_def rsub_def)

lemma rres_union_dist1: 
  "(R \<zrres> U) \<union> (S \<zrres> U) = ((R \<union> S) \<zrres> U)"
  by (auto simp add: rres_def)

lemma rres_union_dist2: 
  "(R \<zrres> U) \<union> (R \<zrres> V) = (R \<zrres> (U \<union> V))"
  by (auto simp add: rres_def)

lemma rsub_union_dist1: 
  "(R \<zrsub> U) \<union> (S \<zrsub> U) = ((R \<union> S) \<zrsub> U)"
  by (auto simp add: rsub_def)

lemma rsub_union_dist2: 
  "(R \<zrsub> U) \<union> (R \<zrsub> V) = (R \<zrsub> (U \<inter> V))"
  by (auto simp add: rsub_def)

lemma rres_elim: 
  assumes 
    a1: "\<zran> R \<inter> U = \<zran> R" 
  shows "R \<zrres> U = R"
  using a1
  by (auto simp add: rres_def)

lemma rsub_elim: 
  assumes 
    a1: "disjoint (\<zran> R) U"
  shows "R \<zrsub> U = R"
  using a1
  by (auto simp add: rsub_def disjoint_def)

lemma rres_elim': 
  assumes 
    a1: "disjoint (\<zran> R) U"
  shows "R \<zrres> U = \<emptyset>"
  using a1
  apply (auto simp only: rres_def Z_maplet_def disjoint_def)
  apply (auto simp add: set_eq_def)
  done

lemma rsub_elim': 
  assumes 
    a1: "\<zran> R \<inter> U = \<zran> R"
  shows "R \<zrsub> U = \<emptyset>"
  using a1
  apply (auto simp only: rsub_def Z_maplet_def)
  apply (auto simp add: set_eq_def)
  done

lemma rres_restrict_self:
  assumes 
    a1: "\<zran> R = U"
  shows "(R \<zrres> U) = R"
  using a1
  by (auto simp add: rres_def)

lemma dsub_empty: 
  "\<emptyset> \<zdsub> R = R" "X \<zdsub> \<emptyset> = \<emptyset>"
  by (auto simp add: dsub_def)

lemma dres_empty: 
  "\<emptyset> \<zdres> R = \<emptyset>" and "X \<zdres> \<emptyset> = \<emptyset>"
  by (auto simp add: dres_def)

lemma dsub_insert:
  "U \<zdsub> (insert (u \<mapsto> x) R) = \<if> u \<in> U \<then> U \<zdsub> R \<else> insert (u \<mapsto> x) (U \<zdsub> R) \<fi>"
  by (auto simp add: dsub_def)

lemma dres_insert:
  "U \<zdres> (insert (u \<mapsto> x) R) = \<if> u \<in> U \<then> insert (u \<mapsto> x) (U \<zdres> R) \<else> U \<zdres> R \<fi>"
  by (auto simp add: dres_def)

lemma rsub_empty: 
  "R \<zrsub> \<emptyset> = R" and "\<emptyset> \<zrsub> U = \<emptyset>"
  by (auto simp add: rsub_def)

lemma rres_empty: 
  "R \<zrres> \<emptyset> = \<emptyset>" and "\<emptyset> \<zrres> U = \<emptyset>"
  by (auto simp add: rres_def)

lemma rsub_insert:
  "(insert (x \<mapsto> u) R) \<zrsub> U = \<if> u \<in> U \<then> R \<zrsub> U \<else> insert (x \<mapsto> u) (R \<zrsub> U) \<fi>"
  by (auto simp add: rsub_def)

lemma rres_insert:
  "(insert (x \<mapsto> u) R) \<zrres> U = \<if> u \<in> U \<then> insert (x \<mapsto> u) (R \<zrres> U) \<else> R \<zrres> U \<fi>"
  by (auto simp add: rres_def)

section {* Relational converse *}

text {*

The relational converse is already defined in HOL. We introduce Z
style syntax for it and add to the already proved properties.
\cite[p100]{Spivey:ZRef}

*}

notation (xsymbols)
  converse ("_\<^sup>\<sim>" [1000] 999) 

lemma Z_inverse_def:
  "R\<^sup>\<sim> \<defs> { x y | \<^zinfrel>{:x:}{:R:}{:y:} \<bullet> y \<zmapsto> x}"
  apply (rule eq_reflection)
  apply (auto simp add: converse_def rel_def)
  done

lemma Z_inverse_dom: 
  "\<zdom> (R\<^sup>\<sim>) = \<zran> R"
  by (auto simp add: converse_def) 

lemma Z_inverse_ran: 
  "\<zran> (R\<^sup>\<sim>) = \<zdom> R"
  by (auto simp add: converse_def)

lemma converse_in_relI:
  assumes
    a1: "R \<in> X \<zrel> Y"
  shows "R\<^sup>\<sim> \<in> Y \<zrel> X"
  using a1
  by (auto simp add: rel_def converse_def)

lemma Z_inverse_mem:
  shows 
    Z_inverse_mema: "(x \<zmapsto> y) \<in> R\<^sup>\<sim> \<Leftrightarrow> (y \<zmapsto> x) \<in> R" and
    Z_inverse_memb: "(x \<mapsto> y) \<in> R\<^sup>\<sim> \<Leftrightarrow> (y \<mapsto> x) \<in> R"
  by (auto simp add: converse_def)

lemma Z_inverse_idem: "(R\<^sup>\<sim>)\<^sup>\<sim> = R"
  by (auto simp add: converse_def)

lemma Z_inverse_id: "(\<zid> X)\<^sup>\<sim> = \<zid> X"
  by (auto simp add: converse_def rel_id_def)

lemma Z_inverse_rel_bcomp: 
  "(R \<zbcomp> S)\<^sup>\<sim> = (S\<^sup>\<sim> \<zbcomp> R\<^sup>\<sim>)"
  by (auto simp add: rel_bcomp_def)

lemma converse_rel_fcomp: 
  "(R \<zfcomp> S)\<^sup>\<sim> = (S\<^sup>\<sim> \<zfcomp> R\<^sup>\<sim>)"
  by (auto simp add: rel_fcomp_def rel_bcomp_def)

lemma converse_eq_eq:
  "R \<zfcomp> S = S \<zfcomp> R \<Rightarrow> R\<^sup>\<sim> \<zfcomp> S\<^sup>\<sim> = S\<^sup>\<sim> \<zfcomp> R\<^sup>\<sim>"
proof (msafe(inference))
  assume a0: "R \<zfcomp> S = S \<zfcomp> R"
  have "S\<^sup>\<sim> \<zfcomp> R\<^sup>\<sim> = (R \<zfcomp> S)\<^sup>\<sim>" 
    by (simp add: converse_rel_fcomp [THEN sym])
  also have "\<dots> = (S \<zfcomp> R)\<^sup>\<sim>"
    by (simp only: a0)
  also have "\<dots> = R\<^sup>\<sim> \<zfcomp> S\<^sup>\<sim>"
    by (simp add: converse_rel_fcomp)
  finally show "R\<^sup>\<sim> \<zfcomp> S\<^sup>\<sim> = S\<^sup>\<sim> \<zfcomp> R\<^sup>\<sim>" by simp
qed

lemma Z_inverse_lgalois: 
  "\<zid> (\<zdom> R) \<subseteq> R \<zfcomp> R\<^sup>\<sim>"
  by (auto simp add: rel_fcomp_def rel_bcomp_def Domain_def rel_id_def)

lemma Z_inverse_rgalois: 
  "\<zid>(\<zran> R) \<subseteq> R\<^sup>\<sim> \<zfcomp> R"
  by (auto simp add: rel_fcomp_def rel_bcomp_def rel_id_def)

lemma converse_empty:
  "\<emptyset>\<^sup>\<sim> = \<emptyset>"
  by (auto simp add: converse_def)

lemma converse_insert:
  "(insert (x \<mapsto> y) f)\<^sup>\<sim> = insert (y \<mapsto> x) (f\<^sup>\<sim>)"
  by (auto simp add: converse_def)

lemma converse_union:
  "(R \<union> S)\<^sup>\<sim> = R\<^sup>\<sim> \<union> S\<^sup>\<sim>"
  by (auto simp add: converse_def)

lemma converse_Union:
  "(\<Union>R)\<^sup>\<sim> = (\<Union> r | r \<in> R \<bullet> r\<^sup>\<sim>)"
  by (auto simp add: converse_def eind_def)

lemma converse_Union_Collect:
  "(\<Union> X | P X \<bullet> t X)\<^sup>\<sim> = (\<Union> X | P X \<bullet> (t X)\<^sup>\<sim>)"
  "(\<Union> X \<bullet> t X)\<^sup>\<sim> = (\<Union> X \<bullet> (t X)\<^sup>\<sim>)"
  by (auto simp add: converse_Union eind_def)

lemma dsub_rinv:
  "(A \<zdsub> R)\<^sup>\<sim> = (R\<^sup>\<sim>) \<zrsub> A"
  by (auto simp add: dsub_def rsub_def Z_inverse_def)

lemma rsub_rinv:
  "(R \<zrsub> A)\<^sup>\<sim> = A \<zdsub> (R\<^sup>\<sim>)"
  by (auto simp add: dsub_def rsub_def Z_inverse_def)

section {* Relational image *}

text {*

Again relational image is a standard part of HOL. We define some Z syntax
and prove some more lemmas. 
\cite[p101]{Spivey:ZRef} 

*}
 
notation (xsymbols)
  Image ("_\<zlImg>_\<zrImg>" [1000,0] 1000)

lemma Z_Image_def:
  "R\<zlImg>S\<zrImg> = { x y | x \<in> S \<and> \<^zinfrel>{:x:}{:R:}{:y:} \<bullet> y }"
   by (auto simp add: Image_def rel_def)
 
lemma Z_Image_iff: 
  "y \<in> R\<zlImg>U\<zrImg> \<Leftrightarrow> (\<exists> x | x \<in> U \<bullet> \<^zinfrel>{:x:}{:R:}{:y:})"
  by (simp add: Image_def)

lemma Z_Image_dres:
  "R\<zlImg>U\<zrImg> = \<zran> (U \<zdres> R)"
  by (auto simp add: Image_def dres_def)

lemma conv_Image_dom_rel:
  "(S\<^sup>\<sim>)\<zlImg>\<zdom> R\<zrImg> = \<zdom> (S \<zfcomp> R)"
  by (auto simp add: Image_def rel_fcomp_def rel_bcomp_def Z_dom_def)+  

lemma Z_inv_Image_dom_rel:
  "\<zdom> (S \<zfcomp> R) = (S\<^sup>\<sim>)\<zlImg>\<zdom> R\<zrImg>"
  by (auto simp add: conv_Image_dom_rel [THEN sym])

lemma Image_ran_rel:
  "R\<zlImg>\<zran> S\<zrImg> = \<zran> (S \<zfcomp> R)"
   by (auto simp add: Image_def rel_fcomp_def rel_bcomp_def Z_ran_def)+

lemma Z_Image_ran_rel:
  "\<zran> (S \<zfcomp> R) = R\<zlImg>\<zran> S\<zrImg>"
  by (auto simp add: Image_ran_rel [THEN sym])

lemma Z_Image_union:
  "R\<zlImg>U \<union> V\<zrImg> = R\<zlImg>U\<zrImg> \<union> R\<zlImg>V\<zrImg>"
  by (auto simp add: Image_def) 

lemma Z_Image_inter:
  "R\<zlImg>U \<inter> V\<zrImg> \<subseteq> R\<zlImg>U\<zrImg> \<inter> R\<zlImg>V\<zrImg>"
  by (auto simp add: Image_def)

lemma Z_Image_dom:
  "R\<zlImg>\<zdom> R\<zrImg> = \<zran> R"
  by (auto simp add: Image_def)  

lemma conv_Image_ran:
  "(R\<^sup>\<sim>)\<zlImg>\<zran> R\<zrImg> = \<zdom> R"
  by (auto simp add: Image_def)  

lemma Z_dom_Image:
  "\<zdom> R = \<fst>\<lparr>R\<rparr>"
  by (auto simp add: image_def)  

lemma Z_ran_Image:
  "\<zran> R = \<snd>\<lparr>R\<rparr>"
  by (auto simp add: image_def)  


lemma Image_mono:
  "A \<subseteq> B \<turnstile> f\<zlImg>A\<zrImg> \<subseteq> f\<zlImg>B\<zrImg>"
by (auto simp add: Image_def)

lemma Image_rel_fcomp:
  "f\<zlImg>g\<zlImg>B\<zrImg>\<zrImg> = (g\<zfcomp> f)\<zlImg>B\<zrImg>"
by (auto simp add: Image_def rel_fcomp_def rel_bcomp_def)


lemma dres_inv_Image:
  "(((A\<zdres>f)\<^sup>\<sim>)\<zlImg>V\<zrImg>) = (((f\<^sup>\<sim>)\<zlImg>V\<zrImg>) \<inter> A)"
by (auto simp add: dres_def Image_iff converse_iff)



section {* Relational override *}

text {*

The relation @{text "R \<oplus> S"} agrees with @{text "S"} on its domain and with
@{text "R"} elsewhere~\cite[p102]{Spivey:ZRef}.

*}

definition
  rel_oride :: "[('a \<leftrightarrow> 'b), ('a \<leftrightarrow> 'b)] \<rightarrow> ('a \<leftrightarrow> 'b)"
where
  rel_oride_def: "rel_oride R S \<defs> ((\<zdom> S) \<zdsub> R) \<union> S"

notation (xsymbols)
  rel_oride (infixr "\<oplus>" 65)

lemma Z_rel_oride_def:
  "Q \<oplus> R \<defs> ((\<zdom> R) \<zdsub> Q) \<union> R"
  by (simp add: rel_oride_def)

lemma rel_oride_mem:
  "(x \<mapsto> y) \<in> R \<oplus> S \<Leftrightarrow> \<if> x \<in> \<zdom> S \<then> (x \<mapsto> y) \<in> S \<else> (x \<mapsto> y) \<in> R \<fi>"
  by (auto simp add: rel_oride_def dsub_mem)

lemma Z_rel_oride_idem: 
  "R \<oplus> R = R"
  by (auto simp add: rel_oride_def Domain_def dsub_def)

lemma Z_rel_oride_assoc:  
  "(P \<oplus> Q) \<oplus> R = P \<oplus> (Q \<oplus> R)"
  by (auto simp add: rel_oride_def Z_dom_def dsub_def)+

lemma rel_oride_lid: 
  "\<emptyset> \<oplus> R = R"
  by (auto simp add: rel_oride_def Z_dom_def dsub_def)

lemma rel_oride_rid: 
  "R \<oplus> \<emptyset> = R"
  by (auto simp add: rel_oride_def Z_dom_def dsub_def)

lemma Z_rel_oride_id:
  "\<lch> \<emptyset> \<oplus> R \<chEq> R \<oplus> \<emptyset> \<chEq> R \<rch>"
  by (auto simp add: rel_oride_def Z_dom_def dsub_def)

lemma Z_rel_oride_dom_dist: 
  "\<zdom> (Q \<oplus> R) = (\<zdom> Q) \<union> (\<zdom> R)"
  by (auto simp add: rel_oride_def Domain_def dsub_def)

lemma Z_rel_oride_disj: 
  "disjoint (\<zdom> Q) (\<zdom> R) \<turnstile> Q \<oplus> R = Q \<union> R"
  by (auto simp add: rel_oride_def Domain_def dsub_def disjoint_def)

lemma Z_dres_rel_oride_dist: 
  "V \<zdres> (Q \<oplus> R) = (V \<zdres> Q) \<oplus> (V \<zdres> R)"
  by (auto simp add: rel_oride_def Domain_def dsub_def dres_def)

lemma Z_rres_rel_oride_dist: 
  "(Q \<oplus> R) \<zrres> V \<subseteq> (Q \<zrres> V) \<oplus> (R \<zrres> V)"
  by (auto simp add: rel_oride_def Domain_def dsub_def rres_def)

lemma rel_oride_restrict_redistrib:
  assumes 
    a1: "\<zdom> s = V"
  shows "rel_oride (V \<zdres> S) (V \<zdres> s) = (V \<zdres> s)"
  using a1
  apply (simp add: rel_oride_def)
  apply (simp add: Z_dres_dom)
  apply (auto simp add: dsub_def dres_def Domain_def)
  done

lemma rel_oride_ran_dist:
  "\<zran> (f \<oplus> g) \<subseteq> \<zran> f \<union> \<zran> g"
  by (auto simp add: rel_oride_mem Range_def Domain_def)


section {* Reflexive and transitive closures *}

text {*

The reflexive and transitive closure operators are treated in the
standard HOL distribution, but unfortunately do not accomodate the notion of carrier
set for the relation as expected by Z~\cite[p103]{Spivey:ZRef}.

*}

inductive_set ztrancl :: "['a set, ('a \<times> 'a) set] \<rightarrow> ('a \<times> 'a) set" 
  for X :: "'a set" and r :: "('a \<times> 'a) set"
  where
    ztrancl_base [intro, Pure.intro, simp]: "\<lbrakk> (a \<mapsto> b) \<in> r; a \<in> X; b \<in> X \<rbrakk> \<turnstile> (a \<mapsto> b) \<in> ztrancl X r"
  | ztrancl_into_trancl [Pure.intro]: "\<lbrakk> (a \<mapsto> b) \<in> ztrancl X r; c \<in> X; (b \<mapsto> c) \<in> r \<rbrakk> \<turnstile> (a \<mapsto> c) \<in> ztrancl X r"

inductive_set zrtrancl :: "['a set, ('a \<times> 'a) set] \<rightarrow> ('a \<times> 'a) set" 
  for X :: "'a set" and r :: "('a \<times> 'a) set"
  where
    zrtrancl_refl [intro, Pure.intro, simp]: "a \<in> X \<turnstile> (a \<mapsto> a) \<in> zrtrancl X r"
  | zrtrancl_into_rtrancl [Pure.intro]: "\<lbrakk> (a \<mapsto> b) \<in> zrtrancl X r; c \<in> X; (b \<mapsto> c) \<in> r \<rbrakk> \<turnstile> (a \<mapsto> c) \<in> zrtrancl X r"

abbreviation
  sp_ztrancl :: "[('a \<times> 'a) set, 'a set] \<rightarrow> ('a \<times> 'a) set"
where
  "sp_ztrancl R X \<defs> ztrancl X R"

abbreviation
  sp_zrtrancl :: "[('a \<times> 'a) set, 'a set] \<rightarrow> ('a \<times> 'a) set"
where
  "sp_zrtrancl R X \<defs> zrtrancl X R"

notation (xsymbols output)
  sp_ztrancl ("(_\<^sup>+)[_]" [1000] 999) and
  sp_zrtrancl ("(_\<^sup>*)[_]" [1000] 999)

notation (zed)
  sp_ztrancl ("(_\<^ztca>{:_:})" [1000] 999) and
  sp_zrtrancl ("(_\<^zrtca>{:_:})" [1000] 999)

syntax (zed)
  "_Z_Rel\<ZZ>ztrancl" :: "[logic, logic] \<rightarrow> logic"    ("(_\<^ztc>{:_:})" [1000] 999)
  "_Z_Rel\<ZZ>zrtrancl" :: "[logic, logic] \<rightarrow> logic"    ("(_\<^zrtc>{:_:})" [1000] 999)

translations
  "R\<^ztc>{:X:}" \<rightharpoonup> "CONST Z_Rel.sp_ztrancl R X"
  "R\<^zrtc>{:X:}" \<rightharpoonup> "CONST Z_Rel.sp_zrtrancl R X"

theorem ztrancl_induct [consumes 1, induct set: ztrancl]:
  assumes 
    a: "(a \<mapsto> b) \<in> R\<^ztc>{:X:}" and 
    c1: "\<And> x \<bullet> \<lbrakk> x \<in> X; (a \<mapsto> x) \<in> R \<rbrakk> \<turnstile> P x" and
    c2: "\<And> y z \<bullet> \<lbrakk> (a \<mapsto> y) \<in> R\<^ztc>{:X:}; z \<in> X; (y \<mapsto> z) \<in> R; P y \<rbrakk> \<turnstile> P z"
  shows "P b"
proof -
  have "a = a \<Rightarrow> P b"
    apply (rule ztrancl.induct [OF a, of "\<olambda> x y \<bullet> x = a \<Rightarrow> P y"])
    apply (iprover intro: c1 c2)+
    done
  thus ?thesis by iprover
qed

lemma Z_trancl_inc:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows "R \<subseteq> R\<^ztc>{:X:}"
  by (auto intro: rel_dom_mem [OF a1] rel_ran_mem [OF a1] simp add: rel_def)

lemma Z_trancl_fcomp_dist:
  "R\<^ztc>{:X:} \<zfcomp> R\<^ztc>{:X:} \<subseteq> R\<^ztc>{:X:}"
proof (auto simp add: rel_fcomp_def rel_bcomp_def)
  fix a b c
  assume b1: "(a \<mapsto> b) \<in> R\<^ztc>{:X:}" and b2: "(b \<mapsto> c) \<in> R\<^ztc>{:X:}"
  show "(a \<mapsto> c) \<in> R\<^ztc>{:X:}"
    apply (rule ztrancl_induct [OF b2])
    apply (rule ztrancl_into_trancl [OF b1])
    apply (assumption)+
    apply (rule ztrancl_into_trancl)
    apply (assumption)+
    done
qed

lemma trancl_subI:
  assumes 
    a1: "Q \<in> X \<zrel> X" "Q \<zfcomp> Q \<subseteq> Q" "R \<subseteq> Q"
  shows "R\<^ztc>{:X:} \<subseteq> Q"
  using a1
  apply (auto simp add: rel_fcomp_def rel_bcomp_def)
  apply (erule ztrancl.induct)
  apply (auto dest!: subsetD simp add: eind_def)
  done

lemma Z_trancl_subI:
  "Q \<in> X \<zrel> X \<and> Q \<zfcomp> Q \<subseteq> Q \<and> R \<subseteq> Q \<Rightarrow> R\<^ztc>{:X:} \<subseteq> Q"
  by (msafe(inference) mintro!: trancl_subI)

lemma trancl_in_relI:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows "R\<^ztc>{:X:} \<in> X \<zrel> X"
  apply (rule in_relI)
  using a1
  apply (auto elim: ztrancl_induct simp add: rel_def)
  done

lemma Z_trancl_conv:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows "R\<^ztc>{:X:} = (\<Inter> Q | Q \<in> X \<zrel> X \<and> Q \<zfcomp> Q \<subseteq> Q \<and> R \<subseteq> Q)"
proof (rule subset_antisym)
  from Z_trancl_inc [of R] Z_trancl_fcomp_dist [of R] a1 have 
    "R\<^ztc>{:X:} \<in> {Q | Q \<in> X \<zrel> X \<and> Q \<zfcomp> Q \<subseteq> Q \<and> R \<subseteq> Q}"
    by (auto intro: trancl_in_relI Z_trancl_fcomp_dist [THEN subsetD])
  then show 
    "(\<Inter> Q | Q \<in> X \<zrel> X \<and> Q \<zfcomp> Q \<subseteq> Q \<and> R \<subseteq> Q) \<subseteq> R\<^ztc>{:X:}"
    by auto
  have 
    "(\<forall> Q \<bullet> Q \<in> X \<zrel> X \<and> Q \<zfcomp> Q \<subseteq> Q \<and> R \<subseteq> Q \<Rightarrow> R\<^ztc>{:X:} \<subseteq> Q)"
    by (msafe(inference) mintro!: trancl_subI)
  then show 
    "R\<^ztc>{:X:} \<subseteq> (\<Inter> Q | Q \<in> X \<zrel> X \<and> Q \<zfcomp> Q \<subseteq> Q \<and> R \<subseteq> Q)"
    by (auto)+
qed

theorem zrtrancl_induct [consumes 1, induct set: zrtrancl]:
  assumes 
    a: "(a \<mapsto> b) \<in> R\<^zrtc>{:X:}" and 
    cases: 
      "a \<in> X \<turnstile> P a" 
      "\<And> y z \<bullet> \<lbrakk> (a \<mapsto> y) \<in> R\<^zrtc>{:X:}; z \<in> X; (y \<mapsto> z) \<in> R; P y \<rbrakk> \<turnstile> P z"
  shows "P b"
proof -
  have "a = a \<Rightarrow> P b"
    apply (rule zrtrancl.induct [OF a, of "(\<olambda> x y \<bullet> x = a \<Rightarrow> P y)"])
    apply (iprover intro: cases)+
    done
  thus ?thesis by iprover
qed

lemma Z_zrtrancl_id:
  "\<zid> X \<subseteq> R\<^zrtc>{:X:}"
  by (auto simp add: rel_id_def)

lemma zrtrancl_id_mem [intro]:
  "a \<in> X \<turnstile> (a \<mapsto> a) \<in> R\<^zrtc>{:X:}"
  apply (insert Z_zrtrancl_id [of R])
  apply (auto)
  done

lemma Z_zrtrancl_inc:
  assumes
    a1: "R \<in> X \<zrel> X"
  shows "R \<subseteq> R\<^zrtc>{:X:}"
  apply (auto)
  apply (rule zrtrancl_into_rtrancl)
  apply (rule zrtrancl_refl)
  using a1
  apply (auto simp add: rel_def)
  done

lemma zrtrancl_inc_mem [intro]:
  assumes
    a1: "R \<in> X \<zrel> X" "(x \<mapsto> y) \<in> R"
  shows "(x \<mapsto> y) \<in> R\<^zrtc>{:X:}"
  apply (insert Z_zrtrancl_inc [of R])
  using a1
  apply (auto simp add: rel_def)
  done

lemma Z_zrtrancl_fcomp_dist:
  "R\<^zrtc>{:X:} \<zfcomp> R\<^zrtc>{:X:} \<subseteq> R\<^zrtc>{:X:}"
proof (auto simp add: rel_fcomp_def rel_bcomp_def)
  fix x y z
  assume b1: "(x \<mapsto> y) \<in> R\<^zrtc>{:X:}" and b2: "(y \<mapsto> z) \<in> R\<^zrtc>{:X:}"
  from b2 b1 show "(x \<mapsto> z) \<in> R\<^zrtc>{:X:}"
    apply (induct)
    apply (auto elim: zrtrancl_induct intro: zrtrancl_into_rtrancl)
    done
qed

lemma zrtrancl_subI:
  assumes a1: "\<zid> X \<subseteq> Q" and a2: "R \<subseteq> Q" and a3: "Q \<zfcomp> Q \<subseteq> Q"
  shows "R\<^zrtc>{:X:} \<subseteq> Q"
  apply (auto simp add: rel_id_def rel_fcomp_def rel_bcomp_def)
  apply (erule zrtrancl.induct)
proof -
  fix x assume b1: "x \<in> X"
  with a1 show 
    "(x \<mapsto> x) \<in> Q"
    by (auto simp add: rel_id_def)
next
  fix x y z
  assume b1: "(x \<mapsto> y) \<in> Q" and b2: "(y \<mapsto> z) \<in> R"
  from b2 a2 have b3: 
    "(y \<mapsto> z) \<in> Q"
    by (auto)
  with b1 a3 show 
    "(x \<mapsto> z) \<in> Q"
    by (auto dest!: subsetD simp add: rel_fcomp_def rel_bcomp_def eind_def)
qed

lemma Z_zrtrancl_subI:
  shows "\<zid> X \<subseteq> Q \<and> R \<subseteq> Q \<and> Q \<zfcomp> Q \<subseteq> Q \<Rightarrow> R\<^zrtc>{:X:} \<subseteq> Q"
  by (msafe(inference) mintro!: zrtrancl_subI)

lemma zrtrancl_in_relI:
  assumes a1: "R \<in> X \<zrel> X"
  shows "R\<^zrtc>{:X:} \<in> X \<zrel> X"
  apply (rule in_relI)
  apply (auto)
proof -
  fix x y
{ assume "(x \<mapsto> y) \<in> R\<^zrtc>{:X:}"
  then show "x \<in> X"
    apply (induct)
    apply (auto)
    done
next
  assume "(y \<mapsto> x) \<in> R\<^zrtc>{:X:}"
  then show "x \<in> X"
    apply (induct)
    apply (auto simp add: rel_def)
    done
}
qed

lemma Z_zrtrancl_conv:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "R\<^zrtc>{:X:} = (\<Inter> Q | Q \<in> X \<zrel> X \<and> \<zid> X \<subseteq> Q \<and> R \<subseteq> Q \<and> Q \<zfcomp> Q \<subseteq> Q)"
proof (rule subset_antisym)
  from Z_zrtrancl_id [of X R] Z_zrtrancl_inc [OF a1] Z_zrtrancl_fcomp_dist [of X R] zrtrancl_in_relI [OF a1]
  have 
    "R\<^zrtc>{:X:} \<in> {Q | Q \<in> X \<zrel> X \<and> \<zid> X \<subseteq> Q \<and> R \<subseteq> Q \<and> Q \<zfcomp> Q \<subseteq> Q}"
    by (auto)
  then show 
    "(\<Inter> Q |  Q \<in> X \<zrel> X \<and> \<zid> X \<subseteq> Q \<and> R \<subseteq> Q \<and> Q \<zfcomp> Q \<subseteq> Q) \<subseteq> R\<^zrtc>{:X:}"
    by (auto)
  have 
    "\<forall> Q \<bullet>  Q \<in> X \<zrel> X \<and> \<zid> X \<subseteq> Q \<and> R \<subseteq> Q \<and> Q \<zfcomp> Q \<subseteq> Q \<Rightarrow> R\<^zrtc>{:X:} \<subseteq> Q"
    by (msafe(inference) mintro!: zrtrancl_subI)
  then show 
    "R\<^zrtc>{:X:} \<subseteq> (\<Inter> Q | Q \<in> X \<zrel> X \<and> \<zid> X \<subseteq> Q \<and> R \<subseteq> Q \<and> Q \<zfcomp> Q \<subseteq> Q)"
    by (auto)+
qed

lemma Z_trancl_zrtrancl_def:
  "\<forall> R | R \<in> X \<zrel> X \<bullet> 
    R\<^ztc>{:X:} = (\<Inter> Q | Q \<in> X \<zrel> X \<and> R \<subseteq> Q \<and> Q \<zfcomp> Q \<subseteq> Q) \<and>
    R\<^zrtc>{:X:} = (\<Inter> Q | Q \<in> X \<zrel> X \<and> \<zid> X \<subseteq> Q \<and> R \<subseteq> Q \<and> Q \<zfcomp> Q \<subseteq> Q)"
   by (auto simp add: Z_trancl_conv Z_zrtrancl_conv)

lemma Z_trancl_def:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows "R\<^ztc>{:X:} \<defs> (\<Inter> Q | Q \<in> X \<zrel> X \<and> R \<subseteq> Q \<and> Q \<zfcomp> Q \<subseteq> Q)"
  apply (rule eq_reflection)
  using a1
  apply (auto simp add: Z_trancl_conv)
  done

lemma Z_zrtrancl_def:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows "R\<^zrtc>{:X:} \<defs> (\<Inter> Q | Q \<in> X \<zrel> X \<and> \<zid> X \<subseteq> Q \<and> R \<subseteq> Q \<and> Q \<zfcomp> Q \<subseteq> Q)"
  apply (rule eq_reflection)
  using a1
  apply (simp add: Z_zrtrancl_conv)
  done

lemma zrtrancl_dom [simp]:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "\<zdom> (R\<^zrtc>{:X:}) = X"
  apply (insert zrtrancl_in_relI [OF a1])
  apply (auto simp add: rel_def)
  done

lemma zrtrancl_ran [simp]:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "\<zran> (R\<^zrtc>{:X:}) = X"
  apply (insert zrtrancl_in_relI [OF a1])
  apply (auto simp add: rel_def)
  done

lemma zrtrancl_decomp1:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "R\<^zrtc>{:X:} = R\<^ztc>{:X:} \<union> \<zid> X"
proof (rule subset_antisym)
  show 
    "R\<^zrtc>{:X:} \<subseteq> R\<^ztc>{:X:} \<union> \<zid> X"
  proof (rule zrtrancl_subI)
    show 
      "\<zid> X \<subseteq> R\<^ztc>{:X:} \<union> \<zid> X"
      by (auto)
    from Z_zrtrancl_inc [OF a1] a1 show 
      "R \<subseteq> R\<^ztc>{:X:} \<union> rel_id X"
      by (auto intro!: ztrancl_base simp add: rel_def)
    from 
      Z_trancl_fcomp_dist [of X R] trancl_in_relI [OF a1, THEN rel_lident] 
      zrtrancl_in_relI [OF a1] id_in_relI [of "X"]
    show 
      "(R\<^ztc>{:X:} \<union> \<zid> X) \<zfcomp> (R\<^ztc>{:X:} \<union> \<zid> X) \<subseteq> R\<^ztc>{:X:} \<union> \<zid> X"
      apply (simp only: rel_fcomp_union rel_lident)
      apply (auto)
      apply (simp add: rel_fcomp_def rel_bcomp_def rel_id_def)
      done
  qed
  show 
    "R\<^ztc>{:X:} \<union> \<zid> X \<subseteq> R\<^zrtc>{:X:}"
    by (auto elim!: ztrancl_induct simp add: Z_trancl_conv Z_zrtrancl_conv [OF a1])+
qed

lemma zrtrancl_decomp2:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "R\<^zrtc>{:X:} = (R \<union> \<zid> X)\<^ztc>{:X:}"
proof (rule subset_antisym)
  show 
    "R\<^zrtc>{:X:} \<subseteq> (R \<union> \<zid> X)\<^ztc>{:X:}"
    apply (rule zrtrancl_subI)
    apply (rule subset_trans [of _ "R \<union> \<zid> X" _])
    apply (fast)
    apply (rule Z_trancl_inc)
    apply (rule Z_rel_union_in_relI [OF a1 id_in_relI])
    apply (rule subset_trans [of _ "R \<union> \<zid> X" _])
    apply (fast)
    apply (rule Z_trancl_inc)
    apply (rule Z_rel_union_in_relI [OF a1 id_in_relI])
    apply (rule Z_trancl_fcomp_dist)
    done
  show 
    "(R \<union> \<zid> X)\<^ztc>{:X:} \<subseteq> R\<^zrtc>{:X:}"
    apply (rule trancl_subI)
    apply (rule zrtrancl_in_relI [OF a1])
    apply (rule Z_zrtrancl_fcomp_dist)
    apply (insert Z_zrtrancl_inc [OF a1] Z_zrtrancl_id)
    apply (auto)
    done
qed

lemma Z_zrtrancl_decomp:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "\<lch> R\<^zrtc>{:X:} \<chEq> R\<^ztc>{:X:} \<union> \<zid> X \<chEq> (R \<union> \<zid> X)\<^ztc>{:X:} \<rch>"
proof (simp, intro conjI)
  show 
    b0: "R\<^zrtc>{:X:} = R\<^ztc>{:X:} \<union> \<zid> X" 
    by (rule zrtrancl_decomp1 [OF a1])
  have 
    "R\<^zrtc>{:X:} = (R \<union> \<zid> X)\<^ztc>{:X:}" 
    by (rule zrtrancl_decomp2 [OF a1])
  with b0 show 
    "R\<^ztc>{:X:} \<union> \<zid> X = (R \<union> \<zid> X)\<^ztc>{:X:}" 
    by simp
qed

lemma zrtrancl_trancl_inc:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "R\<^ztc>{:X:} \<subseteq> R\<^zrtc>{:X:}"
  apply (insert zrtrancl_decomp1 [OF a1])
  apply (auto)
  done

lemma z_transitive_closure_trans [trans]:
  assumes
    a1: "R \<in> X \<zrel> X"
  shows 
    zrtrancl_trans: 
      "\<lbrakk> (x \<mapsto> y) \<in> R\<^zrtc>{:X:}; (y \<mapsto> z) \<in> R\<^zrtc>{:X:} \<rbrakk> \<turnstile> (x \<mapsto> z) \<in> R\<^zrtc>{:X:}" and
    r_into_zrtrancl: 
      "\<lbrakk> (x \<mapsto> y) \<in> R; (y \<mapsto> z) \<in> R\<^zrtc>{:X:} \<rbrakk> \<turnstile> (x \<mapsto> z) \<in> R\<^zrtc>{:X:}" and
    zrtrancl_into_r: 
      "\<lbrakk> (x \<mapsto> y) \<in> R\<^zrtc>{:X:}; (y \<mapsto> z) \<in> R \<rbrakk> \<turnstile> (x \<mapsto> z) \<in> R\<^zrtc>{:X:}" and
    trancl_into_zrtrancl: 
      "\<lbrakk> (x \<mapsto> y) \<in> R\<^ztc>{:X:}; (y \<mapsto> z) \<in> R\<^zrtc>{:X:} \<rbrakk> \<turnstile> (x \<mapsto> z) \<in> R\<^zrtc>{:X:}" and
    zrtrancl_into_trancl: 
      "\<lbrakk> (x \<mapsto> y) \<in> R\<^zrtc>{:X:}; (y \<mapsto> z) \<in> R\<^ztc>{:X:} \<rbrakk> \<turnstile> (x \<mapsto> z) \<in> R\<^zrtc>{:X:}"
  apply (insert a1 Z_zrtrancl_fcomp_dist [of X R] zrtrancl_trancl_inc [OF a1])
  apply (auto dest!: subsetD simp add: rel_fcomp_def rel_bcomp_def eind_def)
  done

lemma ztrancl_decomp1:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "R\<^ztc>{:X:} = R\<zfcomp> R\<^zrtc>{:X:}"
  apply (subst zrtrancl_decomp1 [OF a1])
  apply (simp add: rel_fcomp_union rel_rident [OF a1])
  apply (rule subset_antisym)
proof -
  show 
    "R\<^ztc>{:X:} \<subseteq> (R\<zfcomp> R\<^ztc>{:X:}) \<union> R"
    apply (simp add: rel_fcomp_def rel_bcomp_def subset_def)
    apply (msafe(inference))
    apply (erule ztrancl_induct)
    apply (simp)
    apply (rule disjI1)
    apply (msafe(inference))
  proof -
    fix x y_d_1 y_d_2 z
    assume 
      b1: "(x \<mapsto> y_d_1) \<in> R" and 
      b2: "(y_d_1 \<mapsto> y_d_2) \<in> R\<^ztc>{:X:}" and
      b3: "z \<in> X" "(y_d_2 \<mapsto> z) \<in> R"
    then show 
      "(\<exists> y \<bullet> (x \<mapsto> y) \<in> R \<and> (y \<mapsto> z) \<in> R\<^ztc>{:X:})"
      apply (witness "y_d_1")
      apply (auto intro: ztrancl_into_trancl)
      done
  next
    fix x y z
    assume 
      "(x \<mapsto> y) \<in> R" "z \<in> X" "(y \<mapsto> z) \<in> R"
    with a1 show 
      "(\<exists> y \<bullet> (x \<mapsto> y) \<in> R \<and> (y \<mapsto> z) \<in> R\<^ztc>{:X:})"
      apply (witness "y")
      apply (auto intro: ztrancl_into_trancl ztrancl_base simp add: rel_def)
      done
  qed
  from a1 show 
    "(R\<zfcomp> R\<^ztc>{:X:}) \<union> R \<subseteq> R\<^ztc>{:X:}"
    apply (auto simp add: rel_fcomp_def rel_bcomp_def subset_def rel_def)
    apply (erule ztrancl_induct)
    apply (auto intro: ztrancl_into_trancl ztrancl_base)
    done
qed

lemma trancl_decomp2:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "R\<^ztc>{:X:} = R\<^zrtc>{:X:}\<zfcomp> R"
  apply (simp add: ztrancl_decomp1 [OF a1])
  apply (subst zrtrancl_decomp1 [OF a1])
  apply (subst zrtrancl_decomp1 [OF a1])
  apply (simp add: rel_fcomp_union rel_rident [OF a1] rel_lident [OF a1])
proof -
  have 
    "R\<zfcomp> R\<^ztc>{:X:} = R\<^ztc>{:X:}\<zfcomp> R"
  proof (auto simp add: rel_fcomp_def rel_bcomp_def)
    fix x y z
    assume 
      c1: "(x \<mapsto> y) \<in> R" and 
      c2: "(y \<mapsto> z) \<in> R\<^ztc>{:X:}"
    from c2 have 
      "(x \<mapsto> y) \<in> R \<Rightarrow> (\<exists> y \<bullet> (x \<mapsto> y) \<in> R\<^ztc>{:X:} \<and> (y \<mapsto> z) \<in> R)"
      apply (induct)
      apply (msafe(inference))
    proof -
      fix z
      assume 
        "(x \<mapsto> y) \<in> R" "(y \<mapsto> z) \<in> R"
      then show 
        "(\<exists> y \<bullet> (x \<mapsto> y) \<in> R\<^ztc>{:X:} \<and> (y \<mapsto> z) \<in> R)"
        apply (witness "y")
        apply (auto intro: subsetD [OF Z_trancl_inc [OF a1]])
        done
    next
      fix y_d_1 y_d_2 z
      assume 
        "(x \<mapsto> y_d_1) \<in> R\<^ztc>{:X:}" "(y_d_1 \<mapsto> y_d_2) \<in> R" "(y_d_2 \<mapsto> z) \<in> R"
      with a1 show 
        "(\<exists> y \<bullet> (x \<mapsto> y) \<in> R\<^ztc>{:X:} \<and> (y \<mapsto> z) \<in> R)"
        apply (witness "y_d_2")
        apply (auto intro: ztrancl_into_trancl ztrancl_base simp add: rel_def)
        done
    qed
    with c1 show 
      "(\<exists> y \<bullet> (x \<mapsto> y) \<in> R\<^ztc>{:X:} \<and> (y \<mapsto> z) \<in> R)"
      by (auto)
  next
    fix x y z
    assume 
      c1: "(x \<mapsto> y) \<in> R\<^ztc>{:X:}" and 
      c2: "(y \<mapsto> z) \<in> R"
    from c1 have 
      "(\<forall> z \<bullet> (y \<mapsto> z) \<in> R \<Rightarrow> (\<exists> y \<bullet> (x \<mapsto> y) \<in> R \<and> (y \<mapsto> z) \<in> R\<^ztc>{:X:}))"
      apply (induct)
      apply (msafe(inference))
    proof -
      fix y z
      assume 
        "(x \<mapsto> y) \<in> R" "(y \<mapsto> z) \<in> R"
      with a1 show 
        "(\<exists> y \<bullet> (x \<mapsto> y) \<in> R \<and> (y \<mapsto> z) \<in> R\<^ztc>{:X:})"
        apply (witness "y")
        apply (auto intro: subsetD [OF Z_trancl_inc [OF a1]])
        done
    next
      fix y_d_1 y_d_3 z
      assume 
        c1: "(\<forall> z \<bullet> (y_d_1 \<mapsto> z) \<in> R \<Rightarrow> (\<exists> y \<bullet> (x \<mapsto> y) \<in> R \<and> (y \<mapsto> z) \<in> R\<^ztc>{:X:}))" and 
        c2: "(y_d_1 \<mapsto> y_d_3) \<in> R" and 
        c3: "(y_d_3 \<mapsto> z) \<in> R"
      from c1 c2 obtain y_d_2 where 
        "(x \<mapsto> y_d_2) \<in> R" and "(y_d_2 \<mapsto> y_d_3) \<in> R\<^ztc>{:X:}"
        by (auto)
      with c3 a1 show 
        "(\<exists> y \<bullet> (x \<mapsto> y) \<in> R \<and> (y \<mapsto> z) \<in> R\<^ztc>{:X:})"
        apply (witness "y_d_2")
        apply (auto intro: ztrancl_into_trancl ztrancl_base simp add: rel_def)
        done
    qed
    with c2 show 
      "(\<exists> y \<bullet> (x \<mapsto> y) \<in> R \<and> (y \<mapsto> z) \<in> R\<^ztc>{:X:})"
      by (auto)
  qed
  then show 
    "(R\<zfcomp> R\<^ztc>{:X:}) \<union> R = (R\<^ztc>{:X:}\<zfcomp> R) \<union> R"
    by (simp)
qed

lemma Z_trancl_decomp:
  assumes
    a1: "R \<in> X \<zrel> X"
  shows 
    "\<lch> R\<^ztc>{:X:} \<chEq> R\<zfcomp> R\<^zrtc>{:X:} \<chEq> R\<^zrtc>{:X:}\<zfcomp> R \<rch>"
proof (simp, rule conjI)
  show 
    b0: "R\<^ztc>{:X:} = R\<zfcomp> R\<^zrtc>{:X:}" 
    by (rule ztrancl_decomp1 [OF a1])
  have 
    "R\<^ztc>{:X:} = R\<^zrtc>{:X:}\<zfcomp> R" 
    by (rule trancl_decomp2 [OF a1])
  with b0 show 
    "R\<zfcomp> R\<^zrtc>{:X:} = R\<^zrtc>{:X:}\<zfcomp> R" 
    by simp
qed

lemma Z_trancl_idem: 
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "(R\<^ztc>{:X:})\<^ztc>{:X:} = R\<^ztc>{:X:}"
  apply (auto)
  apply (erule ztrancl_induct)
  apply (simp)
  apply (rule subsetD [OF Z_trancl_fcomp_dist])
  apply (simp add: Z_rel_fcomp_memI)
  apply (rule ztrancl_base)
  using a1
  apply (auto elim!: ztrancl_induct simp add: rel_def)
  done

lemma Z_zrtrancl_idem: 
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "(R\<^zrtc>{:X:})\<^zrtc>{:X:} = R\<^zrtc>{:X:}"
  apply (auto)
  apply (erule zrtrancl_induct)
  apply (auto)
  apply (rule zrtrancl_trans [OF a1])
  using a1
  apply (auto simp add: zrtrancl_in_relI)
  done

lemma Z_zrtrancl_Image:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "X \<subseteq> (R\<^zrtc>{:X:})\<zlImg>X\<zrImg>"
  using a1
  by (auto simp add: Image_def rel_def)

lemma Z_rel_zrtrancl_Image:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "R\<zlImg>(R\<^zrtc>{:X:})\<zlImg>X\<zrImg>\<zrImg> \<subseteq> (R\<^zrtc>{:X:})\<zlImg>X\<zrImg>"
  using a1
  by (auto simp add: Image_def rel_def)

lemma rel_ztrancl_mono:
  assumes 
    a1: "R \<in> X \<zrel> X" "U \<subseteq> V" "R\<zlImg>V\<zrImg> \<subseteq> V"
  shows 
    "(R\<^zrtc>{:X:})\<zlImg>U\<zrImg> \<subseteq> V"
  apply (rule order_trans [of _ "(R\<^zrtc>{:X:})\<zlImg>V\<zrImg>"])
  using a1
  apply (auto simp add: Image_def)
  apply (erule zrtrancl_induct)
  apply (auto)
  done

lemma Z_rel_ztrancl_mono:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "U \<subseteq> V \<and> R\<zlImg>V\<zrImg> \<subseteq> V \<Rightarrow> (R\<^zrtc>{:X:})\<zlImg>U\<zrImg> \<subseteq> V"
  apply (msafe(inference) mintro!: rel_ztrancl_mono)
  using a1
  apply (simp_all)
  done

text{*

Don't die wondering: the vacuous case!

*}


lemma rel_vacuous:
  "\<emptyset> \<zrel> Y = {\<emptyset>}"
  by (simp add: rel_def)

lemma rel_vacuous':
  "X \<zrel> \<emptyset> = {\<emptyset>}"
  by (simp add: rel_def)

lemma vacuous_inv:
  "\<emptyset>\<^sup>\<sim> = \<emptyset>"
  by (simp add: Z_inverse_def)

lemma vacuous_Image:
  "\<emptyset>\<zlImg>V\<zrImg> = \<emptyset>"
  "R\<zlImg>\<emptyset>\<zrImg> = \<emptyset>"
  by (auto simp add: Z_Image_def)

end
