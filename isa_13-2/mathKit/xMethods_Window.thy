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

header {* The \isa{wind} Method *}

theory 
  xMethods_Window 
  
imports
  xHOL_Syntax
  xMethods_Multi_Prover

begin

text {*

When reasoning calculationally it is useful to be able
to derive implications through manipulation of subterms.
This relies on the monotonicity properties of the various 
constructors and enables a simple form of window inference.

*}

subsection {* Theory data support *}

text {*

Our approach to supporting windowing is to introduce a new
reasoning set containing all the introduction rules needed
to decompose relational goals.
We also find it useful to include some simplifier rules to
transform goals into simple logical terms. This can greatly
reduce the number of windowing rules needed, by removing the
need to reproduce all of the logic windowing rules in different
contexts. The obvious case is in normalising set membership goals.

*}

declare_mprover "wind"

(*  not safe

declaration {*

K (MProver.map_cs "wind" (fn cs => #2 (("wind", cs) maddSafter ("window into function arguments", MProver.farg_tac)))) 

*}

declaration {*

K (MProver.map_cs "wind" (fn cs => #2 (("wind", cs) maddSafter ("window into monotonic functions in the premises", (resolve_tac [@{thm monoD}] THEN' assume_tac))))) 

*}

*)

subsection {* Some Boolean windowing rules *}

text {*

Initially, we populate the windowing reasoning set with the basic boolean
window inference rules. These rules describe the interactions between the
implication and logic equivalence relations and the basic boolean operators.

*}

declare conj_ac [msimp(wind)]

lemma [mintro!(wind)]: "(C \<turnstile> A \<Rightarrow> B) \<turnstile> A \<and> C \<Rightarrow> B \<and> C"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Rightarrow> B) \<turnstile> A \<and> C \<Rightarrow> C \<and> B"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Rightarrow> B) \<turnstile> C \<and> A \<Rightarrow> C \<and> B"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Rightarrow> B) \<turnstile> C \<and> A \<Rightarrow> B \<and> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> A \<Rightarrow> A \<and> B"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> A \<Rightarrow> B \<and> A"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> A \<and> B \<Rightarrow> A"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> B \<and> A \<Rightarrow> A"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Leftrightarrow> B) \<turnstile> A \<and> C \<Leftrightarrow> B \<and> C"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Leftrightarrow> B) \<turnstile> A \<and> C \<Leftrightarrow> C \<and> B"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Leftrightarrow> B) \<turnstile> C \<and> A \<Leftrightarrow> C \<and> B"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Leftrightarrow> B) \<turnstile> C \<and> A \<Leftrightarrow> B \<and> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> A \<and> B \<Leftrightarrow> A"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> B \<and> A \<Leftrightarrow> A"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> A \<Leftrightarrow> A \<and> B"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> A \<Leftrightarrow> B \<and> A"
  by (auto)

declare disj_ac [msimp(wind)]

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A \<Rightarrow> B) \<turnstile> A \<or> C \<Rightarrow> B \<or> C"
  by (auto)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A \<Rightarrow> B) \<turnstile> A \<or> C \<Rightarrow> C \<or> B"
  by (auto)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A \<Rightarrow> B) \<turnstile> C \<or> A \<Rightarrow> C \<or> B"
  by (auto)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A \<Rightarrow> B) \<turnstile> C \<or> A \<Rightarrow> B \<or> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> C) \<turnstile> A \<or> C \<Rightarrow> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> C) \<turnstile> C \<or> A \<Rightarrow> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> C) \<turnstile> C \<Rightarrow> A \<or> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> C) \<turnstile> C \<Rightarrow> C \<or> A"
  by (auto)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A \<Leftrightarrow> B) \<turnstile> A \<or> C \<Leftrightarrow> B \<or> C"
  by (auto)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A \<Leftrightarrow> B) \<turnstile> A \<or> C \<Leftrightarrow> C \<or> B"
  by (auto)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A \<Leftrightarrow> B) \<turnstile> C \<or> A \<Leftrightarrow> C \<or> B"
  by (auto)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A \<Leftrightarrow> B) \<turnstile> C \<or> A \<Leftrightarrow> B \<or> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> C) \<turnstile> A \<or> C \<Leftrightarrow> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> C) \<turnstile> C \<or> A \<Leftrightarrow> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> C) \<turnstile> C \<Leftrightarrow> A \<or> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> C) \<turnstile> C \<Leftrightarrow> C \<or> A"
  by (auto)

lemma [mintro!(wind)]: "A \<Rightarrow> B \<turnstile> \<not> B \<Rightarrow> \<not> A"
  by (auto)

lemma [mintro!(wind)]: "A \<Leftrightarrow> B \<turnstile> \<not> B \<Leftrightarrow> \<not> A"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Rightarrow> B) \<turnstile> (C \<Rightarrow> A) \<Rightarrow> (C \<Rightarrow> B)"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> \<not> A) \<turnstile> (C \<Rightarrow> A) \<Rightarrow> \<not> C"
  by (auto)

lemma [mintro!(wind)]: "\<not> C \<Rightarrow> (C \<Rightarrow> B)"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Leftrightarrow> B) \<turnstile> (C \<Rightarrow> A) \<Leftrightarrow> (C \<Rightarrow> B)"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> \<not>A) \<turnstile> (C \<Rightarrow> A) \<Leftrightarrow> \<not>C"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> \<not>B) \<turnstile> \<not>C \<Leftrightarrow> (C \<Rightarrow> B)"
  by (auto)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A \<Rightarrow> B) \<turnstile> (B \<Rightarrow> C) \<Rightarrow> (A \<Rightarrow> C)"
  by (blast)

lemma [mintro!(wind)]: "C \<Rightarrow> (A \<Rightarrow> C)"
  by (blast)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> B) \<turnstile> (B \<Rightarrow> C) \<Rightarrow> C"
  by (blast)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A \<Leftrightarrow> B) \<turnstile> (A \<Rightarrow> C) \<Leftrightarrow> (B \<Rightarrow> C)"
  by (auto)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> B) \<turnstile> C \<Leftrightarrow> (B \<Rightarrow> C)"
  by (auto)

lemma [mintro!(wind)]: "(\<not> C \<turnstile> A) \<turnstile> (A \<Rightarrow> C) \<Leftrightarrow> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<Leftrightarrow> B) \<turnstile> (C \<Leftrightarrow> A) \<Rightarrow> (C \<Leftrightarrow> B)"
  by (auto)

lemma [mintro!(wind)]: "(A \<Leftrightarrow> B) \<turnstile> (C \<Leftrightarrow> A) \<Rightarrow> (B \<Leftrightarrow> C)"
  by (auto)

lemma [mintro!(wind)]: "(A \<Leftrightarrow> B) \<turnstile> (A \<Leftrightarrow> C) \<Rightarrow> (B \<Leftrightarrow> C)"
  by (auto)

lemma [mintro!(wind)]: "(A \<Leftrightarrow> B) \<turnstile> (A \<Leftrightarrow> C) \<Rightarrow> (C \<Leftrightarrow> B)"
  by (auto)

lemma [mintro!(wind)]: "A \<turnstile> (C \<Leftrightarrow> A) \<Rightarrow> C"
  by (blast)

lemma [mintro!(wind)]: "A \<turnstile> (A \<Leftrightarrow> C) \<Rightarrow> C"
  by (auto)

lemma [mintro!(wind)]: "B \<turnstile> C \<Rightarrow> (C \<Leftrightarrow> B)"
  by (auto)

lemma [mintro!(wind)]: "B \<turnstile> C \<Rightarrow> (B \<Leftrightarrow> C)"
  by (auto)

lemma [mintro!(wind)]: "(A \<Leftrightarrow> B) \<turnstile> (C \<Leftrightarrow> A) \<Leftrightarrow> (C \<Leftrightarrow> B)"
  by (auto)

lemma [mintro!(wind)]: "(A \<Leftrightarrow> B) \<turnstile> (C \<Leftrightarrow> A) \<Leftrightarrow> (B \<Leftrightarrow> C)"
  by (auto)

lemma [mintro!(wind)]: "(A \<Leftrightarrow> B) \<turnstile> (A \<Leftrightarrow> C) \<Leftrightarrow> (B \<Leftrightarrow> C)"
  by (auto)

lemma [mintro!(wind)]: "(A \<Leftrightarrow> B) \<turnstile> (A \<Leftrightarrow> C) \<Leftrightarrow> (C \<Leftrightarrow> B)"
  by (auto)

lemma [mintro!(wind)]: "A \<turnstile> (C \<Leftrightarrow> A) \<Leftrightarrow> C"
  by (auto)

lemma [mintro!(wind)]: "B \<turnstile> C \<Leftrightarrow> (B \<Leftrightarrow> C)"
  by (auto)

lemma [mintro!(wind)]: "A \<turnstile> (A \<Leftrightarrow> C) \<Leftrightarrow> C"
  by (auto)

lemma [mintro!(wind)]: "B \<turnstile> C \<Leftrightarrow> (C \<Leftrightarrow> B)"
  by (auto)

lemma [mintro!(wind)]: "(\<And> x \<bullet> A x \<Rightarrow> B x) \<turnstile> (\<forall> x \<bullet> A x) \<Rightarrow> (\<forall> x \<bullet> B x)"
  by (auto)

lemma [mintro!(wind)]: "(\<And> x \<bullet> A x \<Leftrightarrow> B x) \<turnstile> (\<forall> x \<bullet> A x) \<Leftrightarrow> (\<forall> x \<bullet> B x)"
  by (auto)

lemma [mintro!(wind)]: "(\<And> x \<bullet> A x \<Rightarrow> B x) \<turnstile> (\<exists> x \<bullet> A x) \<Rightarrow> (\<exists> x \<bullet> B x)"
  by (auto)

lemma [mintro!(wind)]: "(\<And> x \<bullet> A x \<Leftrightarrow> B x) \<turnstile> (\<exists> x \<bullet> A x) \<Leftrightarrow> (\<exists> x \<bullet> B x)"
  by (auto)

lemma [mintro!(wind)]: "(\<And> x \<bullet> A x \<Leftrightarrow> B x) \<turnstile> (\<exists>\<subone> x \<bullet> A x) \<Leftrightarrow> (\<exists>\<subone> x \<bullet> B x)"
  by (auto)

lemma [mintro!(wind)]: "y = z \<turnstile> x = y \<Leftrightarrow> x = z"
  by (auto)

lemma [mintro!(wind)]: "y = z \<turnstile> y = x \<Leftrightarrow> x = z"
  by (auto)

lemma [mintro!(wind)]: "y = z \<turnstile> x = y \<Leftrightarrow> z = x"
  by (auto)

lemma [mintro!(wind)]: "y = z \<turnstile> y = x \<Leftrightarrow> z = x"
  by (auto)

lemma [mintro!(wind)]: "(b \<turnstile> A = C) \<turnstile> \<if> b \<then> A \<else> B \<fi> = \<if> b \<then> C \<else> B \<fi>"
  by (auto)

lemma [mintro!(wind)]: "(\<not>b \<turnstile> B = C) \<turnstile> \<if> b \<then> A \<else> B \<fi> = \<if> b \<then> A \<else> C \<fi>"
  by (auto)

lemma [mintro!(wind)]: "(b = c) \<turnstile> \<if> b \<then> A \<else> B \<fi> = \<if> c \<then> A \<else> B \<fi>"
  by (auto)

lemma [mintro!(wind)]: 
  fixes
    Pf :: "'a \<rightarrow> 'b \<rightarrow> \<bool> \<times> 'c" and
    Qg :: "'a \<rightarrow> 'b \<rightarrow> \<bool> \<times> 'c"
  assumes
    a1: "(\<And> x \<bullet> eind (Pf x) = eind (Qg x))"
  shows
    "eind (prod_case Pf) = eind (prod_case Qg)"
  apply (rule ext)
  apply (auto simp add: eind_def)
proof -
  fix
    a b
  assume
    b1: "fst (Pf a b)"
  show
    "(\<exists> a' b' \<bullet> snd (Pf a b) = snd (Qg a' b') \<and> fst (Qg a' b'))"
    apply (rule exI [of _ "a"])
    apply (subst a1 [of "a", simplified eind_def, THEN fun_cong, of "snd (Pf a b)", symmetric]) 
    apply (rule exI [of _ "b"])
    apply (simp add: b1)
    done
next
  fix
    a b
  assume
    b1: "fst (Qg a b)"
  show
    "(\<exists> a' b' \<bullet> snd (Qg a b) = snd (Pf a' b') \<and> fst (Pf a' b'))"
    apply (rule exI [of _ "a"])
    apply (subst a1 [of "a", simplified eind_def, THEN fun_cong, of "snd (Qg a b)"]) 
    apply (rule exI [of _ "b"])
    apply (simp add: b1)
    done
qed

lemma [mintro!(wind)]: 
  "(Q \<turnstile> u = v) \<turnstile> eind (\<olambda> _ \<bullet> (Q, u)) = eind (\<olambda> _ \<bullet> (Q, v))"
  by (auto simp add: eind_def)

lemma [mintro!(wind)]: 
  "(Q \<Leftrightarrow> P) \<turnstile> eind (\<olambda> _ \<bullet> (Q, u)) = eind (\<olambda> _ \<bullet> (P, u))"
  by (auto simp add: eind_def)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> Collect P = Collect Q"
  by (auto)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> Inf P = Inf Q"
  by (auto)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> Sup P = Sup Q"
  by (auto)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> Inter P = Inter Q"
  by (auto)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> Union P = Union Q"
  by (auto)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> The P = The Q"
  by (auto)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> Eps P = Eps Q"
  by (auto)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> Least P = Least Q"
  by (auto)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> Greatest P = Greatest Q"
  by (auto)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> Setsum P = Setsum Q"
  by (auto)

lemma [mintro!(wind)]: "(\<And> x \<bullet> x \<in> P \<turnstile> t x = u x) \<turnstile> setsum t P = setsum u P"
  by (auto)

lemma [mintro!(wind)]: "P = Q \<turnstile> setsum t P = setsum t Q"
  by (auto)

lemma [mintro!(wind)]: "(P = Q) \<turnstile> Setprod P = Setprod Q"
  by (auto)

lemma [mintro!(wind)]: "(\<And> x \<bullet> x \<in> P \<turnstile> t x = u x) \<turnstile> setprod t P = setprod u P"
  by (auto)

lemma [mintro!(wind)]: "P = Q \<turnstile> setprod t P = setprod t Q"
  by (auto)

end
