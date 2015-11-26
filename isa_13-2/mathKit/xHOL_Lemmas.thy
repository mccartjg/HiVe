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
  xHOL_Lemmas 

  
imports 
  xHOL_TypeDef

begin

text {*

We introduce a variety of results and operators in support of logical reasoning and
modelling.

*}

(* section {* Unwanted simplifier/reasoner rules *}

declare eq_id_iff [simp del] -- Multivariate_Analysis *)

section {* Boolean operators *}

subsection {* Quantifiers *}

text {*

It is often useful to be able to massage quantified expressions to one normal form or another.
The following results are useful to this end.

*}

lemma ex_conv: 
  "(\<exists> x \<bullet> P x) = (\<not> (\<forall> x \<bullet> \<not>(P x)))"
  by (auto)

lemma all_conv: 
  "(\<forall> x \<bullet> P x) = (\<not> (\<exists> x \<bullet> \<not>(P x)))"
  by (auto)

lemma xall_simps [simp]:
  "(\<forall> x \<bullet> (x = t \<Rightarrow> P x) \<and> Q x) \<Leftrightarrow> P t \<and> (\<forall> x \<bullet> Q x)"
  "(\<forall> x \<bullet> Q x \<and> (x = t \<Rightarrow> P x)) \<Leftrightarrow> (\<forall> x \<bullet> Q x) \<and> P t"
  by (auto)

lemma xex_simps [simp]:
  "(\<exists> x \<bullet> (x = t \<and> P x) \<or> Q x) \<Leftrightarrow> P t \<or> (\<exists> x \<bullet> Q x)"
  "(\<exists> x \<bullet> Q x \<or> (x = t \<and> P x)) \<Leftrightarrow> (\<exists> x \<bullet> Q x) \<or> P t"
  by (auto)

text {*

The standard simplification set pushes quantifiers into to their narrowest scope,
but sometimes it is more useful to go the other way.

*}

lemma all_simps':
  "\<And> P Q \<bullet> (\<forall> x \<bullet> P x) \<and> Q \<Leftrightarrow> (\<forall> x \<bullet> P x \<and> Q)"
  "\<And> P Q \<bullet> P \<and> (\<forall> x \<bullet> Q x) \<Leftrightarrow> (\<forall> x \<bullet> P \<and> Q x)"
  "\<And> P Q \<bullet> (\<forall> x \<bullet> P x) \<or> Q \<Leftrightarrow> (\<forall> x \<bullet> P x \<or> Q)"
  "\<And> P Q \<bullet> P \<or> (\<forall> x \<bullet> Q x) \<Leftrightarrow> (\<forall> x \<bullet> P \<or> Q x)"
  "\<And> P Q \<bullet> ((\<exists> x \<bullet> P x) \<Rightarrow> Q) \<Leftrightarrow> (\<forall> x \<bullet> P x \<Rightarrow> Q)"
  "\<And> P Q \<bullet> (P \<Rightarrow> (\<forall> x \<bullet> Q x)) \<Leftrightarrow> (\<forall> x \<bullet> P \<Rightarrow> Q x)"
  by (auto)

lemma ex_simps':
  "\<And> P Q \<bullet> (\<exists> x \<bullet> P x) \<and> Q \<Leftrightarrow> (\<exists> x \<bullet> P x \<and> Q)"
  "\<And> P Q \<bullet> P \<and> (\<exists> x \<bullet> Q x) \<Leftrightarrow> (\<exists> x \<bullet> P \<and> Q x)"
  "\<And> P Q \<bullet> (\<exists> x \<bullet> P x) \<or> Q \<Leftrightarrow> (\<exists> x \<bullet> P x \<or> Q)"
  "\<And> P Q \<bullet> P \<or> (\<exists> x \<bullet> Q x) \<Leftrightarrow> (\<exists> x \<bullet> P \<or> Q x)"
  "\<And> P Q \<bullet> ((\<forall> x \<bullet> P x) \<Rightarrow> Q) \<Leftrightarrow> (\<exists> x \<bullet> P x \<Rightarrow> Q)"
  "\<And> P Q \<bullet> (P \<Rightarrow> (\<exists> x \<bullet> Q x)) \<Leftrightarrow> (\<exists> x \<bullet> P \<Rightarrow> Q x)"
  by (auto)

lemma all_conj_dist:
  "\<And> P Q \<bullet> (\<forall> x \<bullet> P x \<and> Q x) \<Leftrightarrow> (\<forall> x \<bullet> P x) \<and> (\<forall> x \<bullet> Q x)"
  "\<And> P Q \<bullet> (\<forall> x | A x \<bullet> P x \<and> Q x) \<Leftrightarrow> (\<forall> x | A x \<bullet> P x) \<and> (\<forall> x | A x \<bullet> Q x)"
  by (auto)

lemma ex_disj_dist:
  "\<And> P Q \<bullet> (\<exists> x \<bullet> P x \<or> Q x) \<Leftrightarrow> (\<exists> x \<bullet> P x) \<or> (\<exists> x \<bullet> Q x)"
  "\<And> P Q \<bullet> (\<exists> x | A x \<bullet> P x \<or> Q x) \<Leftrightarrow> (\<exists> x | A x \<bullet> P x) \<or> (\<exists> x | A x \<bullet> Q x)"
  by (auto)

subsection {* The one-point rule *}

text {*

The one point rule is often useful.

*}

lemma one_point: 
  shows
    one_point_all: "(\<forall> x | x = v \<bullet> P x) \<Leftrightarrow> P v" and
    one_point_ex: "(\<exists> x | x = v \<bullet> P x) \<Leftrightarrow> P v"
  by (auto)

subsection {* Boolean term normalisation *}

text {*

The following are useful for normalising boolean expressions.

*}

lemma
  bool_rules:
    "a \<Rightarrow> a" 
    "True \<or> a" 
    "a \<or> True"
    "a \<and> b \<Leftrightarrow> b \<and> a" 
    "(a \<and> b) \<and> c \<Leftrightarrow> a \<and> (b \<and> c)" 
    "a \<and> (b \<and> c) \<Leftrightarrow> b \<and> (a \<and> c)"
    "a \<or> b \<Leftrightarrow> b \<or> a" 
    "(a \<or> b) \<or> c \<Leftrightarrow> a \<or> (b \<or> c)" 
    "a \<or> (b \<or> c) \<Leftrightarrow>  b \<or> (a \<or> c)"
    "a \<and> (b \<or> c) \<Leftrightarrow> (a \<and> b) \<or> (a \<and> c)"
  by (auto)
    
lemma if_bool:
  "\<if> b \<then> c \<else> d \<fi> \<Leftrightarrow> (b \<and> c) \<or> (\<not>b \<and> d)"
  by (auto)

lemma If_eq:
  "\<if> b \<then> x \<else> y \<fi> = z \<Leftrightarrow> (b \<and> x = z) \<or> (\<not>b \<and> y = z)"
  "z = \<if> b \<then> x \<else> y \<fi> \<Leftrightarrow> (b \<and> x = z) \<or> (\<not>b \<and> y = z)"
  by (auto)

lemma iff_imp_dist:
  "((P \<Rightarrow> Q) \<Leftrightarrow> (P \<Rightarrow> R)) \<Leftrightarrow> (P \<Rightarrow> (Q \<Leftrightarrow> R))"
  by (auto)


subsection {* Boolean inference *}

text {*

The following are a collection of useful boolean inference rules.

*}

lemma not_inject:
  "(\<not>P \<Leftrightarrow> \<not>Q) \<Leftrightarrow> (P \<Leftrightarrow> Q)"
  by (auto)

lemma not_antimono:
  "(\<not>P \<Rightarrow> \<not>Q) \<Leftrightarrow> (Q \<Rightarrow> P)"
  by (auto)

lemma iff_conv_conj_imp_n1:
  "P = Q \<Leftrightarrow> (P \<Rightarrow> Q) \<and> (\<not>P \<Rightarrow> \<not>Q)"
  by (auto)

lemma iff_conv_conj_imp_n2:
  "P = Q \<Leftrightarrow> (Q \<Rightarrow> P) \<and> (\<not>Q \<Rightarrow> \<not>P)"
  by (auto)

lemma convolute_conj:
  assumes
    a0: "P1 \<and> \<not>Q1" and
    a1: "P1 \<turnstile> P2" and
    a2: "Q2 \<turnstile> Q1"
  shows
    "P2 \<and> \<not>Q2"
  using a0 a1 a2
  by (auto)

lemma contrapos_pn: 
  "\<lbrakk> Q; P \<turnstile> \<not>Q \<rbrakk> \<turnstile> \<not>P"
  by (auto)

lemma imp_imp_elim [simp]: 
  "A \<Rightarrow> B \<Rightarrow> C \<Leftrightarrow> A \<and> B \<Rightarrow> C"
  by (auto)

lemma disjCI':
  assumes a1: "\<not>P \<turnstile> Q"
  shows "P \<or> Q"
  using a1
  by (auto)

lemma disjCE:
  assumes a1: "P \<or> Q" "P \<turnstile> R" "\<lbrakk> \<not>P; Q \<rbrakk> \<turnstile> R"
  shows "R"
  using a1
  by (auto)

lemma disjCE':
  assumes a1: "Q \<or> P" "P \<turnstile> R" "\<lbrakk> \<not>P; Q \<rbrakk> \<turnstile> R"
  shows "R"
  using a1
  by (auto)

subsection {* Support for boolean calculational proofs *}

lemma [trans]: "\<lbrakk>a \<Rightarrow> b; b \<Rightarrow> c \<rbrakk> \<turnstile> a \<Rightarrow> c"
  by (auto)
  
lemma [trans]: "\<lbrakk>a \<Rightarrow> b; b = c \<rbrakk> \<turnstile> a \<Rightarrow> c"
  by (auto)

lemma [trans]: "\<lbrakk>a = b; b \<Rightarrow> c \<rbrakk> \<turnstile> a \<Rightarrow> c"
  by (auto)

subsection {* Conjunction in inference rules *}

lemma conj_idem:
  "P \<and> P \<Leftrightarrow> P"
  "P \<and> P \<and> Q \<Leftrightarrow> P \<and> Q"
  by (auto)

lemmas conj_ac' = conj_ac conj_idem

lemma conj_rulify [rulify]:
  "(A \<and> B \<turnstile> R) \<defs> (\<lbrakk> A; B \<rbrakk> \<turnstile> R)"
  apply (rule)
  apply (auto)
  done

section {* Sets *}

subsection {* Set comprehension *}

text {*

The following rules are useful in simplifying formulae involving
set comprehensions.

*}

lemma CollectI':
  assumes
    a1: "P x"
  shows
    "x \<in> Collect P"
  by (auto simp add: a1)

lemma CollectqI:
  assumes
    a1: "P x"
  shows
    "x \<in> { x | P x}"
  by (auto simp add: a1)

lemma CollectD':
  assumes
    a1: "x \<in> Collect P"
  shows
    "P x"
  using a1
  by (auto)

lemma CollectqD:
  assumes
    a1: "x \<in> { x | P x}"
  shows
    "P x"
  using a1
  by (auto)

lemma image_conv:
  "f\<lparr>X\<rparr> = { x | x \<in> X \<bullet> f x }"
  by (auto simp add: image_def)

lemma range_conv:
  "range f = { x \<bullet> f x }"
  by (auto simp add: image_def)

lemma Collect_image:
  "f\<lparr>{x | P x}\<rparr> = {x | P x \<bullet> f x}"
  by (auto simp add: image_def)

lemma Collect_image':
  "f\<lparr>{x | P x \<bullet> g x}\<rparr> = {x | P x \<bullet> f (g x)}"
  by (auto simp add: image_def)+

lemma Collect_eq:
  "{ x | P x } = { x | Q x } \<Leftrightarrow> P = Q"
  by (auto simp add: set_eq_iff)

(*
lemma [simp]: 
  "Collect (split p) = split p"
  "x \<in> split p \<Leftrightarrow> (split p) x"
  by (auto simp add: mem_def)
*)

lemma comp_simp [simp]:
  "\<And> P Q t \<bullet> (\<forall> x | (\<exists> a \<bullet> x = t a \<and> P a) \<bullet> Q x)  = (\<forall> a | P a \<bullet> Q (t a))"
  "\<And> P Q t \<bullet> (\<forall> x | (\<exists> a b \<bullet> x = t a b \<and> P a b) \<bullet> Q x)  = (\<forall> a b | P a b \<bullet> Q (t a b))"
  "\<And> P Q t \<bullet> (\<exists> x | (\<exists> a \<bullet> x = t a \<and> P a) \<bullet> Q x) = (\<exists> a | P a \<bullet> Q (t a))"
  "\<And> P Q t \<bullet> (\<exists> x | (\<exists> a b \<bullet> x = t a b \<and> P a b) \<bullet> Q x) = (\<exists> a b | P a b \<bullet> Q (t a b))"
  "\<And> Q t \<bullet> (\<forall> x | (\<exists> a \<bullet> x = t a) \<bullet> Q x) = (\<forall> a \<bullet> Q (t a))"
  "\<And> Q t \<bullet> (\<forall> x | (\<exists> a b \<bullet> x = t a b) \<bullet> Q x) = (\<forall> a b \<bullet> Q (t a b))"
  "\<And> Q t \<bullet> (\<exists> x | (\<exists> a \<bullet> x = t a) \<bullet> Q x) = (\<exists> a \<bullet> Q (t a))"
  "\<And> Q t \<bullet> (\<exists> x | (\<exists> a b \<bullet> x = t a b) \<bullet> Q x) = (\<exists> a b \<bullet> Q (t a b))"
  by (auto)

lemma set_comp_cong:
  assumes a1: "{x | P x \<bullet> f x} = {y | Q y \<bullet> g y}"
  shows "{x | P x \<bullet> t (f x)} = {y | Q y \<bullet> t (g y)}" 
proof -
  have " {x | P x \<bullet> t (f x)} = t\<lparr>{x | P x \<bullet> f x}\<rparr>"
    by (auto simp add: image_def eind_def)
  also note a1
  also have "t\<lparr>{y | Q y \<bullet> g y}\<rparr> = {y | Q y \<bullet> t (g y)}"
    by (auto simp add: image_def eind_def)
  finally show ?thesis
    by (this)
qed

text {*

Some rules for massaging set comprehensions into the schema-text form.

*}

lemma eind_norm1:
  "C (\<olambda> z \<bullet> (\<exists> a \<bullet> z = f a \<and> P a)) = C (eind (prod_case (\<olambda> a (_::unit) \<bullet> (P a, f a))))"
  "C (\<olambda> z \<bullet> (\<exists> a \<bullet> P a \<and> z = f a)) = C (eind (prod_case (\<olambda> a (_::unit) \<bullet> (P a, f a))))"
  "C (\<olambda> z \<bullet> (\<exists> a \<bullet> f a = z \<and> P a)) = C (eind (prod_case (\<olambda> a (_::unit) \<bullet> (P a, f a))))"
  "C (\<olambda> z \<bullet> (\<exists> a \<bullet> P a \<and> f a = z)) = C (eind (prod_case (\<olambda> a (_::unit) \<bullet> (P a, f a))))"
  "C (eind (prod_case (\<olambda> a (_::unit) \<bullet> ((\<exists> b \<bullet> a = f b \<and> P2 a b), g a))))
  = C (eind (prod_case (\<olambda> b (_::unit) \<bullet> (P2 (f b) b, g (f b)))))"
  by (auto intro!: arg_cong [of _ _ "C"] simp add: eind_def)

lemma eind_norm2:
  "C (\<olambda> z \<bullet> (\<exists> a b \<bullet> z = f a b \<and> P a b)) 
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b (_::unit) \<bullet> (P a b, f a b))))))"
  "C (\<olambda> z \<bullet> (\<exists> a b \<bullet> P a b \<and> z = f a b)) 
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b (_::unit) \<bullet> (P a b, f a b))))))"
  "C (\<olambda> z \<bullet> (\<exists> a b \<bullet> f a b = z \<and> P a b))
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b (_::unit) \<bullet> (P a b, f a b))))))"
  "C (\<olambda> z \<bullet> (\<exists> a b \<bullet> P a b \<and> f a b = z))
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b (_::unit) \<bullet> (P a b, f a b))))))"
  "C (eind (prod_case (\<olambda> a (_::unit) \<bullet> ((\<exists> b \<bullet> P a b), g a))))
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b (_::unit) \<bullet> (P a b, g a))))))"
  "C (eind (prod_case (\<olambda> a (_::unit) \<bullet> ((\<exists> b c \<bullet> a = f2 b c \<and> P2 a b c), g2 a))))
  = C (eind (prod_case (\<olambda> b \<bullet> (prod_case (\<olambda> c (_::unit) \<bullet> (P2 (f2 b c) b c, g2 (f2 b c)))))))"
  "C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b (_::unit) \<bullet> ((\<exists> c \<bullet> a = f3 b c \<and> P3 a b c), g3 a b))))))
  = C (eind (prod_case (\<olambda> b \<bullet> (prod_case (\<olambda> c (_::unit) \<bullet> (P3 (f3 b c) b c, g3 (f3 b c) b))))))"
  "C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b (_::unit) \<bullet> ((\<exists> c \<bullet> b = f4 a c \<and> P4 a b c), g4 a b))))))
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> c (_::unit) \<bullet> (P4 a (f4 a c) c, g4 a (f4 a c)))))))"
  by (auto intro!: arg_cong [of _ _ "C"] simp add: eind_def)

lemma eind_norm3:
  "C (\<olambda> z \<bullet> (\<exists> a b c \<bullet> z = f a b c \<and> P a b c)) 
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b \<bullet> (prod_case (\<olambda> c (_::unit) \<bullet> (P a b c, f a b c))))))))"
  "C (\<olambda> z \<bullet> (\<exists> a b c \<bullet> P a b c \<and> z = f a b c)) 
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b \<bullet> (prod_case (\<olambda> c (_::unit) \<bullet> (P a b c, f a b c))))))))"
  "C (\<olambda> z \<bullet> (\<exists> a b c \<bullet> f a b c = z \<and> P a b c))
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b \<bullet> (prod_case (\<olambda> c (_::unit) \<bullet> (P a b c, f a b c))))))))"
  "C (\<olambda> z \<bullet> (\<exists> a b c \<bullet> P a b c \<and> f a b c = z))
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b \<bullet> (prod_case (\<olambda> c (_::unit) \<bullet> (P a b c, f a b c))))))))"
  "C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b (_::unit) \<bullet> ((\<exists> c \<bullet> P a b c), g a b))))))
  = C (eind (prod_case (\<olambda> a \<bullet> (prod_case (\<olambda> b \<bullet> (prod_case (\<olambda> c (_::unit) \<bullet> (P a b c, g a b))))))))"
  by (auto intro!: arg_cong [of _ _ "C"] simp add: eind_def)

lemmas eind_norm = eind_norm1 eind_norm2 eind_norm3

setup {*

Simplifier.map_theory_simpset (fn ctxt =>
let

fun is_eq_tm (Const(@{const_name "HOL.eq"}, _) $ _ $ _) = true
  | is_eq_tm _ = false;

fun is_ex_tm (Const(@{const_name "HOL.Ex"}, _) $ _) = true
  | is_ex_tm _ = false;

fun eqterm_ord (t, u) =
    case (is_eq_tm t, is_eq_tm u) of
      (true, false) => LESS
    | (false, true) => GREATER
    | _ => (
      case (is_ex_tm t, is_ex_tm u) of
        (true, false) => LESS
      | (false, true) => GREATER
      | _ => (
        case (t, u) of
          (Abs (_, T, t), Abs(_, U, u)) =>
          (prod_ord eqterm_ord Term_Ord.typ_ord ((t, T), (u, U)))
        | _ => (
          case int_ord (size_of_term t, size_of_term u) of
            EQUAL =>
            let val (f, ts) = strip_comb t and (g, us) = strip_comb u in
              (prod_ord Term_Ord.hd_ord eqterms_ord ((f, ts), (g, us)))
            end
          | ord => ord)))
and eqterms_ord (ts, us) = list_ord eqterm_ord (ts, us)

fun eq_termless tu = (eqterm_ord tu = LESS);

in
  ctxt |> Simplifier.set_termless eq_termless
end)

*}

lemma eind_comp':
  "(\<exists> a \<bullet> x = f a \<and> (\<exists> b \<bullet> a = g b \<and> P a b))
  \<Leftrightarrow> (\<exists> b \<bullet> x = f (g b) \<and> P (g b) b)"
  "(\<exists> a \<bullet> x = f a \<and> (\<exists> b \<bullet> a = g b \<and> P a b) \<and> Q a)
  \<Leftrightarrow> (\<exists> b \<bullet> x = f (g b) \<and> P (g b) b \<and> Q (g b))"
  by (auto)

lemma eind_comp'':
  "(\<exists> a \<bullet> f a = x \<and> (\<exists> b \<bullet> a = g b \<and> P a b))
  \<Leftrightarrow> (\<exists> b \<bullet> f (g b) = x \<and> P (g b) b)"
  "(\<exists> a \<bullet> f a = x \<and> (\<exists> b \<bullet> a = g b \<and> P a b) \<and> Q a)
  \<Leftrightarrow> (\<exists> b \<bullet> f (g b) = x \<and> P (g b) b \<and> Q (g b))"
  by (auto)

lemmas eind_comp = conj_ac eind_comp' eind_comp''

lemma eind_split:
  "eind (prod_case (\<olambda> ab::'a \<times> 'b \<bullet> Pt ab)) 
  = eind (prod_case (\<olambda> a \<bullet> prod_case (\<olambda> b \<bullet> Pt (a, b))))"
  by (auto simp add: eind_def)

text {*

This can be used only as a subst or with instantiated type variables.

*}

lemma eind_commute:
  "eind (prod_case (\<olambda> a \<bullet> prod_case (\<olambda> b \<bullet> Pt a b)))
  = eind (prod_case (\<olambda> b \<bullet> prod_case (\<olambda> a \<bullet> Pt a b)))"
  by (auto simp add: eind_def)


subsection {* Set quantifiers *}

text {*

The operators @{text "Ball"} and @{text "Bex"} are anamolous specialisations of the more general
schema-text mechanism introduced in Section~\ref{sec:schematext}. We add their defining equations to
the simplification set to minimise their impact on proof development.

*}

lemmas [simp] = Ball_def Bex_def

lemma [simp]:
  "SUPR X f = (\<Union> x | x \<in> X \<bullet> f x)"
  "INFI X f = (\<Inter> x | x \<in> X \<bullet> f x)"
  apply (unfold SUP_def INF_def)
  apply (auto simp add: eind_def)
  done

subsection {* Subset goals *}

text {*

Reasoning about sets in a calulation style is not well supported in the standard HOL library.

We begin with a useful reasoning set for subset goals.

*}

lemma 
  subset_rules:
    "A \<subseteq> A"
    "A \<subseteq> C \<turnstile> A \<subseteq> C \<union> B" 
    "A \<subseteq> C \<turnstile> A \<subseteq> B \<union> C"
    "A \<subseteq> C \<turnstile> A \<inter> B \<subseteq> C" 
    "A \<subseteq> C \<turnstile> B \<inter> A \<subseteq> C"
    "A \<subseteq> B \<turnstile> A \<inter> B = A" 
    "A \<subseteq> B \<turnstile> B \<inter> A = A"
    "A \<subseteq> B \<turnstile> A \<union> B = B" 
    "A \<subseteq> B \<turnstile> B \<union> A = B"
  by (auto)

subsection {* Non-emptiness *}

text {*

Usually the point of presuming the non-emptiness of a set is ensure the existence of a witness.
The following results help with injecting this fact into a proof state.

*}

lemma nempty_conv:
  "A \<noteq> \<emptyset> \<Leftrightarrow> (\<exists> x \<bullet> x \<in> A)"
  "\<emptyset> \<noteq> A \<Leftrightarrow> (\<exists> x \<bullet> x \<in> A)"
  by (auto)

lemma nemptyI:
  "x \<in> A \<turnstile> A \<noteq> \<emptyset>"
  by (auto simp add: nempty_conv)

lemma nemptyE:
  "\<lbrakk> A \<noteq> \<emptyset>; (\<And> x \<bullet> x \<in> A \<turnstile> R) \<rbrakk> \<turnstile> R"
  by (auto simp add: nempty_conv)

text {*

Likewise for non-universality.

*}

lemma nuniv_conv:
  "A \<noteq> \<univ> \<Leftrightarrow> (\<exists> x \<bullet> x \<notin> A)"
  "\<univ> \<noteq> A \<Leftrightarrow> (\<exists> x \<bullet> x \<notin> A)"
  by (auto)

lemma nunivI:
  "x \<notin> A \<turnstile> A \<noteq> \<univ>"
  by (auto simp add: nuniv_conv)

lemma insert_univ [simp]:
  "insert x UNIV = UNIV"
  by (auto)

lemma nunivE:
  "\<lbrakk> A \<noteq> \<univ>; (\<And> x \<bullet> x \<notin> A \<turnstile> R) \<rbrakk> \<turnstile> R"
  by (auto simp add: nuniv_conv)

text {*

Similar results based on cardinality.

*}

lemma card_nempty_conv:
  assumes a1: "finite A"
  shows 
    "0 < card A \<Leftrightarrow> A \<noteq> \<emptyset>"
    "0 \<noteq> card A \<Leftrightarrow> A \<noteq> \<emptyset>"
    "card A \<noteq> 0 \<Leftrightarrow> A \<noteq> \<emptyset>"
  using a1
  by (auto)

text {*

A couple of similar results for subset premises.

*}

lemma psubset_neq:
  "A \<subset> B \<turnstile> (\<exists> x \<bullet> x \<in> B \<and> x \<notin> A)"
  by (auto)

lemma psubsetI_wit:
  "\<lbrakk> x \<in> B; x \<notin> A; A \<subseteq> B \<rbrakk> \<turnstile> A \<subset> B"
  by (rule psubsetI, assumption, rule contrapos_pp, assumption, auto)

subsection {* Miscellaneous set results *}

text {*

Often it is useful to rewrite set equalities in situ so as to avoid adopting 
an inference based reasoning.
This has to be done with care as it also renders such equalities useless as simplifier rules.

*}

lemma set_eq_def: 
  "A = B \<Leftrightarrow> (\<forall> x \<bullet> x \<in> A \<Leftrightarrow> x \<in> B)"
  by (auto)

text {*

The following are a collection of useful set results. 

*}

lemma ins_comm [simp]: 
  "\<^ins>{:x:}{:(\<^ins>{:y:}{:A:}):} = \<^ins>{:y:}{:(\<^ins>{:x:}{:A:}):}"
  by (auto)

lemma split_Collect_mem_eq [simp]: 
  "{ x y | (x, y) \<in> r \<bullet> (x, y) } = r"
  by (auto)

lemma [simp]: "X \<subseteq> Y \<inter> Z \<Leftrightarrow> X \<subseteq> Y \<and> X \<subseteq> Z"
  by (auto)  

lemma [simp]: "(B - A) \<inter> A = \<emptyset>"
  by (auto)

lemma inter_union_dist_absorb:
  "A \<inter> (A \<union> B) = A"
  by (auto)

subsection {* Set windowing *}

text {*

We need support for window reasoning on set expressions.
The mechanism adopted is to convert set relations to boolean relations about
set membership. An alternative approach might have been to more directly attack the structure of
set comprehensions, thus restricting consideration to sets of that form, but this would involve
considerably more effort.

*}

(*
lemma [mintro!(wind)]: "(\<And> x \<bullet> x \<in> A \<Leftrightarrow> x \<in> B) \<turnstile> A = B"
  by (auto)

lemma [mintro!(wind)]: "(\<And> x \<bullet> x \<in> A \<Rightarrow> x \<in> B) \<turnstile> A \<subseteq> B"
  by (auto)

lemma [mintro!(wind)]: "(\<And> x \<bullet> x \<in> B \<Leftarrow> x \<in> A) \<turnstile> B \<supseteq> A"
  by (auto simp add: ge_def)

declare mem_Collect_eq [msimp(wind) add]

lemma [msimp("wind")]: "x \<in> Collect P \<Leftrightarrow> P x"
  by (auto)
*)

lemma [msimp("wind")]: "x \<in> A \<inter> B \<Leftrightarrow> x \<in> A \<and> x \<in> B"
  by (auto)

lemma [msimp("wind")]: "x \<in> A \<union> B \<Leftrightarrow> x \<in> A \<or> x \<in> B"
  by (auto)

lemma [msimp("wind")]: "x \<in> \<Inter>CL_A \<Leftrightarrow> (\<forall> A | A \<in> CL_A \<bullet> x \<in> A)"
  by (auto)

lemma [msimp("wind")]: "x \<in> \<Union>CL_A \<Leftrightarrow> (\<exists> A | A \<in> CL_A \<bullet> x \<in> A)"
  by (auto)

lemma [msimp("wind")]: "x \<in> -A \<Leftrightarrow> x \<notin> A"
  by (auto)

lemma subset_def:
  "A \<subseteq> B \<Leftrightarrow> (\<forall> a \<bullet> a \<in> A \<Rightarrow> a \<in> B)"
  by (auto)

lemma finite_mem_induct [case_names empty insert, induct set: finite]:
  assumes 
    a1: "finite F" and
    a2: "P \<emptyset>" and
    a3: "(\<And> x F \<bullet> \<lbrakk> finite F; x \<notin> F; P F \<rbrakk> \<turnstile> P (insert x F))"
  shows "P F"
proof -
  from a1
  show "P F"
  using a2 a3
    apply (induct set: finite)
    apply auto
    done
qed

section {* Choice operators *}


lemma eind_the_equality:
  assumes
    a1: "fst (Pt a)" and
    a2: "(\<And> x \<bullet> fst (Pt x) \<turnstile> snd (Pt x) = v)"
  shows
    "The (eind Pt) = v"
  apply (rule the_equality)
  apply (auto intro: exI [of _ "a"] simp add: a1 a2)
  done

lemma eind_theI2:
  assumes
    a1: "fst (Pt a)" and
    a2: "(\<And> x \<bullet> fst (Pt x) \<turnstile> snd (Pt x) = snd (Pt a))" and
    a3: "\<And> x \<bullet> fst (Pt x) \<turnstile> P (snd (Pt x))"
  shows
    "P (The (eind Pt))"
  using a1
  by (auto intro: theI2 a2 a3 simp add: eind_def)

lemma eind_theI2':
  assumes
    a1: "(\<exists>\<subone> x \<bullet> fst (Pt x))" and
    a2: "\<And> x \<bullet> fst (Pt x) \<turnstile> P (snd (Pt x))"
  shows
    "P (The (eind Pt))"
  using a1  
  by (auto intro: a2 eind_theI2)

lemma eind_someI2:
  assumes
    a1: "fst (Pt a)" and
    a2: "\<And> x \<bullet> fst (Pt x) \<turnstile> P (snd (Pt x))"
  shows
    "P (Eps (eind Pt))"
  using a1
  by (auto intro: someI2 a2 simp add: eind_def)

lemma eind_someI2_ex:
  assumes
    a1: "(\<exists> x \<bullet> fst (Pt x))" and
    a2: "\<And> x \<bullet> fst (Pt x) \<turnstile> P (snd (Pt x))"
  shows
    "P (Eps (eind Pt))"
  using a1
  by (auto intro: someI2 a2 simp add: eind_def)

(*
lemma set_the_equality: 
  assumes prema: "a \<in> X"
      and premx: "\<And> x \<bullet> x \<in> X \<turnstile> x = a"
  shows "The X = a"
  apply (rule the_equality)
  apply (rule prema [simplified mem_def])
  apply (rule premx [simplified mem_def])
  apply (assumption)
  done

lemma collect_the_equality: 
  assumes prema: "P a"
      and premx: "\<And> x \<bullet> P x \<turnstile> x = a"
  shows "The (Collect P) = a"
  apply (rule set_the_equality)
  apply (simp add: prema)
  apply (rule premx)
  apply (simp)
  done

lemma set_theI:
  assumes "a \<in> X" and "\<And> x \<bullet> x \<in> X \<turnstile> x = a"
  shows "The X \<in> X"
  by (iprover intro: prems set_the_equality [THEN ssubst])

lemma collect_theI:
  assumes "P a" and "\<And> x \<bullet> P x \<turnstile> x = a"
  shows "P (The (Collect P))"
  by (iprover intro: prems collect_the_equality [THEN ssubst])

lemma set_theI': "(\<existsone> x \<bullet> x \<in> X) \<turnstile> The X \<in> X"
  apply (erule ex1E)
  apply (erule set_theI)
  apply (erule allE)
  apply (erule mp)
  apply assumption
  done

lemma collect_theI': "(\<existsone> x \<bullet> P x) \<turnstile> P (The (Collect P))"
  apply (erule ex1E)
  apply (erule collect_theI)
  apply (erule allE)
  apply (erule mp)
  apply assumption
  done

lemma set_theI2:
  assumes "a \<in> X" "\<And> x \<bullet> x \<in> X \<turnstile> x = a" "\<And> x \<bullet> x \<in> X \<turnstile> Q x"
  shows "Q (The X)"
  by (iprover intro: prems set_theI)

lemma collect_theI2:
  assumes "P a" "\<And> x \<bullet> P x \<turnstile> x = a" "\<And> x \<bullet> P x \<turnstile> Q x"
  shows "Q (The (Collect P))"
  by (iprover intro: prems collect_theI)

lemma set_the1_equality: "\<lbrakk> (\<existsone> x \<bullet> x \<in> X); a \<in> X \<rbrakk> \<turnstile> The X = a"
  apply (rule set_the_equality)
  apply  assumption
  apply (erule ex1E)
  apply (erule all_dupE)
  apply (drule mp)
  apply  assumption
  apply (erule ssubst)
  apply (erule allE)
  apply (erule mp)
  apply assumption
  done 

lemma collect_the1_equality: "\<lbrakk> (\<existsone> x \<bullet> P x); P a \<rbrakk> \<turnstile> The (Collect P) = a"
  apply (rule collect_the_equality)
  apply  assumption
  apply (erule ex1E)
  apply (erule all_dupE)
  apply (drule mp)
  apply  assumption
  apply (erule ssubst)
  apply (erule allE)
  apply (erule mp)
  apply assumption
  done 

lemma set_the_singleton [simp]: "The {x} = x"
  apply (rule set_the_equality)
  apply (auto)
  done

lemma set_someI: 
  "x \<in> X \<turnstile> Eps X \<in> X"
  apply (simp add: mem_def)
  apply (erule someI)
  done 

lemma collect_someI: 
  "P x \<turnstile> P (Eps (Collect P))"
  apply (simp add: Collect_def)
  apply (erule someI)
  done 

lemma set_someI_ex [elim?]: "\<exists> x \<bullet> x \<in> X \<turnstile> Eps X \<in> X"
  apply (erule exE)
  apply (erule set_someI)
  done 

lemma set_someI_nempty [elim?]: 
    "X \<noteq> \<emptyset> \<turnstile> Eps X \<in> X"
  apply (rule set_someI_ex)
  apply (simp add: nempty_conv)
  done

lemma collect_someI_ex [elim?]: "(\<exists> x \<bullet> P x) \<turnstile> P (Eps (Collect P))"
  apply (erule exE)
  apply (erule collect_someI)
  done 

lemma set_someI2: "\<lbrakk> a \<in> X;  (\<And> x \<bullet> x \<in> X \<turnstile> Q x) \<rbrakk> \<turnstile> Q (Eps X)"
  by (blast intro: set_someI)

lemma collect_someI2: "\<lbrakk> P a;  (\<And> x \<bullet> P x \<turnstile> Q x) \<rbrakk> \<turnstile> Q (Eps (Collect P))"
  by (blast intro: collect_someI)

lemma set_some_equality: "\<lbrakk> a \<in> X; (\<And> x \<bullet> x \<in> X \<turnstile> x = a) \<rbrakk> \<turnstile> Eps X = a"
  by (blast intro: set_someI)

lemma collect_some_equality: "\<lbrakk> P a; (\<And> x \<bullet> P x \<turnstile> x = a) \<rbrakk> \<turnstile> Eps (Collect P) = a"
  by (blast intro: collect_someI)

lemma set_some1_equality: "\<lbrakk> (\<existsone> x \<bullet> x \<in> X); a \<in> X \<rbrakk> \<turnstile> Eps X = a"
  by (blast intro: set_some_equality)

lemma collect_some1_equality: "\<lbrakk> (\<existsone> x \<bullet> P x); P a  \<rbrakk> \<turnstile> Eps (Collect P) = a"
  by (blast intro: collect_some_equality)

lemma set_some_eq_ex: "(Eps X) \<in> X \<Leftrightarrow> (\<exists> x \<bullet> x \<in> X)"
  by (blast intro: set_someI)

lemma collect_some_eq_ex: "P (Eps (Collect P)) \<Leftrightarrow> (\<exists> x \<bullet> P x)"
  by (blast intro: collect_someI)

lemma set_some_eq_singleton [simp]: "Eps {a} = a"
  apply (rule set_some_equality)
  apply (auto)
  done
*)

(*
lemma [mintro!("wind")]: "(\<And> x \<bullet> A x \<Leftrightarrow> B x) \<turnstile> (\<epsilon> x | A x) = (\<epsilon> x | B x)"
  by (auto)

lemma [mintro!("wind")]: "(\<And> x \<bullet> A x \<Leftrightarrow> B x) \<turnstile> (\<mu> x | A x) = (\<mu> x | B x)"
  by (auto)
*)

lemma eind_LeastI2_order:
  fixes
    Pt :: "'b \<rightarrow> (\<bool> \<times> ('a::order))"
  shows
  "\<lbrakk> fst (Pt x);
     (\<And> y \<bullet> fst (Pt y) \<turnstile> snd (Pt x) \<le> snd (Pt y));
     (\<And> x \<bullet> \<lbrakk> fst (Pt x); \<forall> y \<bullet> fst (Pt y) \<Rightarrow> snd (Pt x) \<le> snd (Pt y) \<rbrakk> \<turnstile> Q (snd (Pt x))) \<rbrakk>
   \<turnstile> Q (Least (eind Pt))"
  apply (rule LeastI2_order [where Q = "Q"])
  apply (auto simp add: eind_def)
  done

lemma eind_Least_equality:
  fixes
    Pt :: "'b \<rightarrow> (\<bool> \<times> ('a::order))"
  shows
  "\<lbrakk> fst (Pt a); snd (Pt a) = k; (\<And> x \<bullet> fst (Pt x) \<turnstile> snd (Pt a) \<le> snd (Pt x)) \<rbrakk> 
  \<turnstile> Least (eind Pt) = k"
  apply (rule Least_equality)
  apply (auto simp add: eind_def)
  done

lemma eind_wellorder_Least_lemma:
  fixes
    Pt :: "'b \<rightarrow> (\<bool> \<times> ('a::wellorder))"
  assumes 
    a1: "fst (Pt a)"
  shows 
     eind_LeastI: "(\<exists> x \<bullet> fst (Pt x) \<and> Least (eind Pt) = snd (Pt x))" and 
     eind_Least_le: "Least (eind Pt) \<le> snd (Pt a)"
  using wellorder_Least_lemma [of "(\<olambda> x \<bullet> eind Pt x)", of "snd (Pt a)"] a1
  by (auto simp add: eind_def)

lemma eind_LeastI2_ex: 
  fixes
    Pt :: "'b \<rightarrow> (\<bool> \<times> ('a::wellorder))"
  assumes 
    a1: "(\<exists> a \<bullet> fst (Pt a))" and
    a2: "\<And> x \<bullet> fst (Pt x) \<turnstile> Q (snd (Pt x))"
  shows
    "Q (Least (eind Pt))"
proof -
  from a1 obtain a where
    b1: "fst (Pt a)"
    by (auto)
  from eind_LeastI [of "Pt" "a"] b1 obtain a' where
    b2:"fst (Pt a')" and
    b3: "Least (eind Pt) = snd (Pt a')"
    by (auto)
  from a2 [OF b2] show
    "Q (Least (eind Pt))"
    by (simp add: b3)
qed

(*
lemma set_LeastI2_order:
  "\<lbrakk> (x::'a::order) \<in> X;
     (\<And> y \<bullet> y \<in> X \<turnstile> x \<le> y);
     (\<And> x \<bullet> \<lbrakk> x \<in> X; \<forall> y \<bullet> y \<in> X \<Rightarrow> x \<le> y \<rbrakk> \<turnstile> Q x) \<rbrakk>
   \<turnstile> Q (Least X)"
  apply (unfold Least_def mem_def)
  apply (rule theI2)
  apply (blast intro: order_antisym)+
  done

lemma collect_LeastI2_order:
  "\<lbrakk> P (x::'a::order);
     (\<And> y \<bullet> P y \<turnstile> x \<le> y);
     (\<And> x \<bullet> \<lbrakk> P x; \<forall> y \<bullet> P y \<Rightarrow> x \<le> y \<rbrakk> \<turnstile> Q x) \<rbrakk>
   \<turnstile> Q (Least (Collect P))"
  apply (unfold Least_def Collect_def)
  apply (rule theI2)
  apply (blast intro: order_antisym)+
  done

lemma set_Least_equality:
  "\<lbrakk> (k::'a::order) \<in> X; (\<And> x \<bullet> x \<in> X \<turnstile> k \<le> x) \<rbrakk> \<turnstile> Least X = k"
  apply (simp add: Least_def mem_def)
  apply (rule the_equality)
  apply (auto intro!: order_antisym)
  done

lemma collect_Least_equality:
  "\<lbrakk> P (k::'a::order); (\<And> x \<bullet> P x \<turnstile> k \<le> x) \<rbrakk> \<turnstile> Least (Collect P) = k"
  apply (simp add: Least_def Collect_def)
  apply (rule the_equality)
  apply (auto intro!: order_antisym)
  done

lemma wellorder_set_Least_lemma:
  fixes k :: "'a :: wellorder"
  assumes a1: "k \<in> X"
  shows set_LeastI: "(Least X) \<in> X" and set_Least_le: "Least X \<le> k"
  using wellorder_Least_lemma [of "(\<olambda> x \<bullet> x \<in> X)", OF a1]
  by (auto simp add: mem_def)

lemma wellorder_collect_Least_lemma:
  fixes k :: "'a :: wellorder"
  assumes a1: "P k"
  shows collect_LeastI: "P (Least (Collect P))" and collect_Least_le: "Least (Collect P) \<le> k"
  using wellorder_Least_lemma [of "P", OF a1]
  by (auto  simp add: Collect_def) 

-- "The following 3 lemmas are due to Brian Huffman"
lemma set_LeastI_ex: 
  "(\<exists> x::'a::wellorder \<bullet> x \<in> X) \<turnstile> Least X \<in> X"
  apply (erule exE)
  apply (erule set_LeastI)
  done

lemma collect_LeastI_ex: 
  "(\<exists> x::'a::wellorder \<bullet> P x) \<turnstile> P (Least (Collect P))"
  apply (erule exE)
  apply (erule collect_LeastI)
  done

lemma set_LeastI2:
  "\<lbrakk> (a::'a::wellorder) \<in> X; (\<And> x \<bullet> x \<in> X \<turnstile> Q x) \<rbrakk> \<turnstile> Q (Least X)"
  by (blast intro: set_LeastI)

lemma collect_LeastI2:
  "\<lbrakk> P (a::'a::wellorder); (\<And> x \<bullet> P x \<turnstile> Q x) \<rbrakk> \<turnstile> Q (Least (Collect P))"
  by (blast intro: collect_LeastI)

lemma not_less_set_Least: "[| k < (Least X) |] ==> (k::'a::wellorder) \<notin> X"
apply (simp (no_asm_use) del: linorder_not_le add: linorder_not_le [symmetric])
apply (erule contrapos_nn)
apply (erule set_Least_le)
done                                                                            

lemma not_less_collect_Least: "[| k < (Least (Collect P)) |] ==> \<not>(P (k::'a::wellorder))"
apply (simp (no_asm_use) del: linorder_not_le add: linorder_not_le [symmetric])
apply (erule contrapos_nn)
apply (erule collect_Least_le)
done

lemma set_Least_singleton:
  "Least {x::('a::order)} = x"
  apply (rule set_Least_equality)
  apply (auto)
  done
*)

subsection {* Forcing set membership *}

lemma forceI:
  assumes a1: "A \<noteq> \<emptyset>"
  shows "force A x \<in> A"
  using a1
  apply (simp add: force_def nempty_conv)
  apply (msafe(inference))
  apply (rule someI_ex)
  apply (auto)
  done

lemma forceI':
  assumes a1: "a \<in> A"
  shows "force A x \<in> A"
  apply (rule forceI)
  using a1
  apply (auto)
  done

lemma forceE:
  assumes a1: "x \<in> A"
  shows "force A x = x"
  using a1
  by (simp add: force_def)

lemma (in type_definition) forceI:
  "force A x \<in> A"
  apply (rule forceI')
  apply (rule Rep)
  done

lemma (in type_definition) forceE:
  "force A (Rep x) = Rep x"
  apply (rule forceE)
  apply (rule Rep)
  done

subsection {* Composing images *}

text {*

Some useful rules for reasoning about operator images.

*}

lemma Pow_image:
  "\<pset> \<circ> (image g) = image (image g) \<circ> \<pset>"
  "\<pset> \<circ> (image g \<circ> f) = image (image g) \<circ> \<pset> \<circ> f"
  "\<pset> ((image g) X) = (image (image g)) (\<pset> X)"
  by (auto intro!: ext simp add: image_Pow_surj)

lemma image_comp_dist:
  "image (f \<circ> g) = (image f) \<circ> (image g)"
  by (auto intro!: ext simp add: image_conv)+

lemma image_dist: 
  "(\<olambda> x \<bullet> f (g x))\<lparr>X\<rparr> = f\<lparr>g\<lparr>X\<rparr>\<rparr>"
  by (auto simp add: image_conv)+

text {*

Without the @{text "op \<circ>"} operator to match to, the simplifier will not kick in.

Currently the only fix is to instantiation @{text "image_dist"} with the necessary arguements. It might be possible at some point to define simplifier procedure to do the instantiation.

*}

lemma image_aggregate:
  "(image f) \<circ> (image g) = image (f \<circ> g)"
  "image f (image g X) = image (f \<circ> g) X"
  by (auto intro!: ext simp add: image_conv)+

lemma image_id:
  "image id = id"
  by (auto intro!: ext)

lemma image_map_pair:
  "(image (f \<par> g)) \<circ> (\<olambda> (X, Y) \<bullet> X \<times> Y) = (\<olambda> (X, Y) \<bullet> X \<times> Y) \<circ> ((image f) \<par> (image g))"
  "(f \<par> g)\<lparr>X \<times> Y\<rparr> = f\<lparr>X\<rparr> \<times> g\<lparr>Y\<rparr>"
  apply (rule ext)
  apply (auto simp add: map_pair_def image_conv)+
  done

subsection {* Distributed union/intersection and schema texts *}


lemma Union_Collect:
  "(\<Union> X Y | P X Y \<bullet> t X Y) = (\<Union> X \<bullet> (\<Union> Y | P X Y \<bullet> t X Y))"
  "(\<Union> X Y \<bullet> t X Y) = (\<Union> X \<bullet> (\<Union> Y \<bullet> t X Y))"
  by (auto)+

lemma Inter_Collect:
  "(\<Inter> X Y | P X Y \<bullet> t X Y) = (\<Inter> X \<bullet> (\<Inter> Y | P X Y \<bullet> t X Y))"
  "(\<Inter> X Y \<bullet> t X Y) = (\<Inter> X \<bullet> (\<Inter> Y \<bullet> t X Y))"
  by (auto)+

section {* Miscellaneous results *}

subsection {* Orders *}

text {*

Some inference rules for making use of order results.

*}

lemma order_lessI:
  "\<lbrakk> (x::'a::order) \<noteq> y; x \<le> y \<rbrakk> \<turnstile> x < y"
  by (simp add: order_less_le)

lemma order_neq_le_less:
  "(x::'a::order) \<noteq> y \<turnstile> x \<le> y \<Leftrightarrow> x < y"
  by (simp add: order_less_le)

lemma order_lessE:
  "\<lbrakk> x < y; ((x::'a::order) \<le> y \<turnstile> R) \<rbrakk> \<turnstile> R"
  by (simp add: order_less_le)

lemma linorder_le_cases:
  "\<lbrakk> (x::'a::linorder) \<le> y \<turnstile> R; y \<le> x \<turnstile> R \<rbrakk> \<turnstile> R"
  by (insert linorder_linear [of x y], blast)

text {*

Composition preserves monotonicity.

*}

lemma mono_mono_comp:
  assumes a1: "mono f" and a2: "mono g"
  shows "mono (f \<circ> g)"
  using a1 a2
  by (auto intro!: monoI dest!: monoD)

subsection {* Functions *}

text {*

As for set equality, a definition-style theorem relating to functional
equality is useful in calculation reasoning.

*}

lemma fun_eq_def: "f = g \<Leftrightarrow> (\<forall> x \<bullet> f x = g x)"
  by (auto intro!: ext)

text {*

We prove some useful facts about operator ranges.

*}

lemma rangeD: "x \<in> range f \<turnstile> \<exists> y \<bullet> x = f y"
  by (simp add: image_def Bex_def)

lemma 
  range_f_inv_f: "range (f \<circ> inv f) = range f"
  apply (simp add: set_eq_def image_def)
  apply (msafe_no_assms(inference))
proof -
  fix y y'
  assume 
    "y = f (inv f y')"
  then show 
     "\<exists> x \<bullet> y = f x"
    apply (witness "(inv f) y'")
    apply (auto)
    done
next
  fix x y
  assume 
    b1: "y = f x"
  have 
    "f x \<in> range f"
    by (auto)
  then have 
    "f (inv f (f x)) = f x"
    by (rule f_inv_into_f)
  then show 
    "\<exists> y' \<bullet> y = f (inv f y')"
    apply (witness "f x")
    apply (auto simp add: b1)
    done
qed

text {*

Proofs of left-commutativity for associative-commutative operators
are niggling, so we pre-pot the result.

*}

lemma AC_LC:
  assumes 
    A: "\<And> x y z \<bullet> f (f x y) z = f x (f y z)" and 
    C: "\<And> x y \<bullet> f x y = f y x"
  shows 
    "\<And> x y \<bullet> f x (f y z) = f y (f x z)"
proof -
  fix x y
  have 
    "f x (f y z) 
    = f (f x y) z"
    by (simp add: A)
  also have "\<dots> 
    = f (f y x) z"
    by (simp add: C)
  also have "\<dots>
    = f y (f x z)"
    by (simp add: A)
  finally show 
    "f x (f y z) = f y (f x z)" 
    by this
qed

lemma AC_LC':
  assumes 
    A: "f (f x y) z = f x (f y z)" and 
    C: "f x y = f y x" and 
    A': "f (f y x) z = f y (f x z)"
  shows 
    "f x (f y z) = f y (f x z)"
  by (simp add: A [symmetric] C A')

subsection {* Cardinality results *}

text {*

Cantor's Theoerem states that the set type is always strictly larger
than the underlying type (recall that types in HOL are always
non-empty).

*}

theorem Cantor': 
  fixes
    f :: "'a \<rightarrow> 'a set" and
    X :: "'a set"
  shows
    "(\<exists> Y | Y \<in> \<pset> X \<bullet> Y \<notin> f\<lparr>X\<rparr>)"
proof (witness "{x | x \<in> X \<and> x \<notin> f x}", msafe(inference))
  let ?S = "{x | x \<in> X \<and> x \<notin> f x}"
  show 
    "?S \<in> \<pset> X"
    by (auto)
  show 
    "?S \<notin> f\<lparr>X\<rparr>"
  proof (rule notI)
    assume 
      "?S \<in> f\<lparr>X\<rparr>"
    thus 
      "\<False>"
    proof
      fix 
        y
      assume 
        d1: "?S = f y" and
        d2: "y \<in> X"
      from d1 show 
        ?thesis
      proof (rule equalityCE)
        assume 
          in_S: "y \<in> ?S" and
          in_fy: "y \<in> f y"
        from in_S have 
          notin_fy: "y \<notin> f y" 
          by (simp)
        from notin_fy in_fy show 
          ?thesis
          by contradiction
      next
        assume 
          notin_S: "y \<notin> ?S" and
          notin_fy: "y \<notin> f y"
        from notin_S d2 have 
          in_fy: "y \<in> f y"
          by auto
        from notin_fy in_fy show 
          ?thesis
          by contradiction
      qed
    qed
  qed
qed

lemmas Cantor = Cantor' [of "\<univ>", simplified]

lemma Cantor_cor': 
  "\<not>(\<exists> f::'a set \<rightarrow> 'a \<bullet> f\<lparr>\<pset> X\<rparr> \<subseteq> X \<and> inj_on f (\<pset> X))"
proof (auto)
  fix 
    f::"'a set \<rightarrow> 'a"
  assume 
    a1: "inj_on f (\<pset> X)" and
    a2: "f\<lparr>\<pset> X\<rparr> \<subseteq> X"
  from Cantor' [of "X" "inv_into (\<pset> X) f"] obtain Y where
    b1: "Y \<in> \<pset> X" and
    b2: "Y \<notin> (inv_into (\<pset> X) f)\<lparr>X\<rparr>"
    by (auto)
  from a2 b1 have
    b3: "Y \<in> (inv_into (\<pset> X) f)\<lparr>X\<rparr>"
    apply (subst inv_into_f_f [OF a1 b1, symmetric])
    apply (auto)
    done
  from b2 b3 show 
    "\<False>"
    by (contradiction)
qed

lemma Cantor_cor: "\<not>(\<exists> f::'a set \<rightarrow> 'a \<bullet> inj f)"
  using Cantor_cor' [of "\<univ>"]
  by (auto)

theorems comp_inj =
  comp_inj_on [OF _ subset_inj_on [OF _ subset_UNIV], of _ "UNIV"]

theorem ninj_onD:
  "\<not> (inj_on f A) \<turnstile> \<exists> x | x \<in> A \<bullet> \<exists> y | y \<in> A \<bullet> f x = f y \<and> x \<noteq> y"
  by (unfold inj_on_def, auto)

lemma subset_inj [intro]:
  assumes
    a1: "inj f"
  shows
    "inj_on f A"
  apply (rule subset_inj_on [OF a1])
  apply (auto)
  done

text {*

Rewrite versions of the axiom of choice are useful in calculational proofs. 

*}

lemma ax_choice_eq: 
  "(\<forall> x \<bullet> (\<exists> y \<bullet> P x y)) \<Leftrightarrow> (\<exists> f \<bullet> (\<forall> x \<bullet> P x (f x)))"
  by (auto elim!: someI)

lemma qual_ax_choice_eq: 
  "(\<forall> x | Q x \<bullet> (\<exists> y \<bullet> P x y)) \<Leftrightarrow> (\<exists> f \<bullet> (\<forall> x | Q x \<bullet> P x (f x)))"
  by (auto elim!: someI)

lemma ax_choice1_eq: 
  "(\<forall> x \<bullet> (\<exists>\<subone> y \<bullet> P x y)) \<Leftrightarrow> (\<exists>\<subone> f \<bullet> (\<forall> x \<bullet> P x (f x)))"
  apply (simp add: Ex1_def ax_choice_eq)
  apply (msafe(wind))
  apply (msafe(inference))
  apply (fast)
  apply (rule ext)
  apply (simp)
proof -
  fix 
    f x y
  assume
    b1: "P x y" and
    b2: "(\<forall> a \<bullet> P a (f a))" and
    b3: "(\<forall> g \<bullet> (\<forall> a \<bullet> P a (g a)) \<Rightarrow> g = f)"
  from b1 b2 have 
    b4: "(\<forall> a \<bullet> P a ((f (x := y)) a))"
    by (auto)
  have
    b5: "f (x := y) = f"
    apply (rule b3 [rule_format])
    apply (rule b4 [rule_format])
    done
  from b5 [THEN fun_cong, of "x"] show
    "y = f x"
    by (auto)
qed

subsection {* Numbers *}

text {*

We specialise some useful natural number results to the natural number embedding
function @{text "of_nat"}.

*}

lemmas of_nat_lessI [iff] = 
  lessI [THEN less_imp_of_nat_less, simplified]

lemmas of_nat_less_SucI = 
  less_SucI [THEN less_imp_of_nat_less, simplified]

lemmas of_nat_zero_less_Suc [iff] = 
  zero_less_Suc [THEN less_imp_of_nat_less, simplified]

lemmas of_nat_Suc_not_Zero =
  Suc_not_Zero [THEN of_nat_eq_iff [THEN not_inject [THEN iffD2], THEN iffD2], simplified]

lemmas of_nat_Zero_not_Suc =
  Zero_not_Suc [THEN of_nat_eq_iff [THEN not_inject [THEN iffD2], THEN iffD2], simplified]

lemmas of_nat_Suc_neq_Zer0 =
  Suc_neq_Zero [OF of_nat_eq_iff [THEN iffD1], simplified]

lemmas of_nat_Zero_neq_Suc =
  Zero_neq_Suc [OF of_nat_eq_iff [THEN iffD1], simplified]

subsection {* Option *}

lemma 
  option_if:  
    "\<if> b \<then> Some x \<else> None \<fi> = None \<Leftrightarrow> \<not> b"
    "\<if> b \<then> Some x \<else> None \<fi> = Some y \<Leftrightarrow> b \<and> x = y"
  by (auto)

subsection {* List lemmas *}

lemma (in type_definition) Abs_inverse_map:
  assumes
    a1: "set Ts \<subseteq> A" 
  shows
    "map (Rep \<circ> Abs) Ts = Ts"
  apply (rule map_idI)
  apply (simp)
  apply (rule Abs_inverse)
  using a1
  apply (auto)
  done

lemma (in type_definition) Rep_inverse_map:
    "map (Abs \<circ> Rep) Ts = Ts"
  by (simp add: Rep_inverse_raw)

lemma map_map_rev:
  "map (f \<circ> g) xs = map f (map g xs)"
  "map (\<olambda> x \<bullet> f (g x)) xs = map f (map g xs)"
  by (auto)

lemma sort_key_is_nil [simp]:
  "sort_key f xs = [] \<Leftrightarrow> xs = []"
  apply (cases xs)
  apply (auto)
  done

lemma list_all2_mono':
  assumes
    a1: "p \<le> q" 
  shows
    "list_all2 p \<le> list_all2 q"
  using a1 list_all2_mono [of "p" _ _ "q"]
  by (auto simp add:  le_fun_def le_bool_def)

lemma list_all2_monoI [intro?]:
  "list_all2 P xs ys \<turnstile> (\<And> x y \<bullet> \<lbrakk> x \<in> set xs; y \<in> set ys;  P x y \<rbrakk> \<turnstile> Q x y) \<turnstile> list_all2 Q xs ys"
  apply (induct xs arbitrary: ys, simp)
  apply (case_tac ys, auto)
  done

lemma list_all2_img:
  assumes
    a2: "(\<forall> x y \<bullet>  x \<in> X \<and> p x y \<Rightarrow> y \<in> Y)" and
    a1: "set xs \<subseteq> X" and
    a3: "list_all2 p xs ys" 
  shows
    "set ys \<subseteq> Y"
proof -
  have
    "(\<forall> ys \<bullet> set xs \<subseteq> X \<and> list_all2 p xs ys \<Rightarrow> set ys \<subseteq> Y)" (is "(\<forall> ys \<bullet> ?Ps xs ys)")
  proof (induct "xs")
    show
      "(\<forall> ys \<bullet> ?Ps [] ys)"
      by (auto)
  next
    fix
      x xs
    assume
      c1: "(\<forall> ys \<bullet> ?Ps xs ys)"
    show
      "(\<forall> ys \<bullet> ?Ps (x # xs) ys)"
    proof (rule allI)
      fix
        ys
      from c1 [rule_format] show
        "?Ps (x # xs) ys"
        apply (cases "ys")
        apply (auto intro: a2 [rule_format])
        done
    qed
  qed
  with a1 a3 show
    "?thesis"
    by (auto)
qed

end
