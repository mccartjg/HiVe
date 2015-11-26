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

theory Cartesian_Universe
  
imports 
  Z_Toolkit

begin

text {*

The Cartesian closure of a type @{text 'a} is the disjoint union of
the class of types that can be constructed from @{text 'a} using the
@{text set} and @{text "(_ \<times> _)"} constructors. This class of types
can be indexed by the following datatype.

*}

datatype 
  CT = catom | cset CT | cprod CT CT

text {*

We can associate a Cartesian type with every element of @{text CT} as
follows.
\begin{quote}
@{text "('a ctype_of) catom = 'a"}\\
@{text "('a ctype_of) (cset t) = (('a ctype_of) t) set"} \\
@{text "('a ctype_of) (cprod t_d_1 t_d_2) = (('a ctype_of) t_d_1) \<times> (('a ctype_of) t_d_2)"}
\end{quote}
The Cartesian universe generated by @{text 'a} is then
\begin{quote}
@{text "'a cartuniv = \<Sum> t \<bullet> ('a ctype_of) t"}
\end{quote}
Unfortunately, we can't use this approach to construct @{text "'a cartuniv"}
in Isabelle/HOL, because type constructors can not depend upon term values.
Instead we must proceed axiomatically, but with care.

*}

subsection {* Constructing the Cartesian Universe *}

text {*

For each HOL type @{text "'a"}, we introduce a new type @{text "'a cartuniv"},
the Cartesian Universe of @{text "'a"}.

*}

typedecl
  'a cartuniv

text {*

The type is constructed inductively as follows.
An injection @{text "atom_of"}
of the type argument @{text 'a} into @{text "'a cartuniv"} constructs the
atomic elements of the set universe.
Two other operators @{text "set_of"} and @{text "prod_of"} are then
used inductively to construct injective images of each Cartesian type.
The @{text "set_of"} operator is type tagged in order to ensure that
empty sets of different types are distinguished.


For this construction to be isomorphic to 
@{text "\<Sum> t \<bullet> ('a ctype_of) t"}
as desired, the images of each of these injections
must be disjoint and they must collectively
cover @{text "'a cartuniv"}.

In order to express these properties, 
we find it convenient to introduce the
@{text carrier_set} operator to perform an 
analogous function to that of @{text ctype_of} above.
For each type tag @{text t},
@{text "carrier_set t"} collects all of the elements of 
the @{text "'a cartuniv"} image of @{text "('a ctype_of) t"}.
This can be defined inductively on the structure of the carrier set
tags.

In order to ensure that @{text "'a cartuniv"} is no bigger than 
@{text "\<Sum> t \<bullet> ('a ctype_of) t"},
we require that @{text "'a cartuniv"} be the disjoint
union of the carrier sets.

In order to ensure that @{text "'a cartuniv"} is no smaller than 
@{text "\<Sum> t \<bullet> ('a ctype_of) t"},
we require the @{text atom_of} constructor to be injective and the
inductive constructors @{text set_of} and @{text prod_of}
to be injective on each of the carrier sets.

Finally, although not strictly necessary,
we require that @{text "set_of t"} always map into 
@{text "\<chi> (cset t)"}, even for arguments outside of
@{text "\<pset> (\<chi> t)"}, since this simplifies some calculations.
Additionally, we require that @{text "set_of t"} depend only on the @{text "t"}
elements of a set.

*}

axiomatization
  atom_of :: "'a => 'a cartuniv" and
  set_of :: "[CT, ('a cartuniv) set] \<rightarrow> ('a cartuniv)" and
  prod_of :: "(('a cartuniv) \<times> ('a cartuniv)) \<rightarrow> ('a cartuniv)" and
  carrier_set :: "CT \<rightarrow> ('a cartuniv) set" ("\<chi>")
where
  chi_catom: "\<chi> catom = atom_of\<lparr>\<univ>-['a]\<rparr>" and
  chi_cset: "\<chi> (cset t) = (set_of t)\<lparr>\<pset> (\<chi> t)\<rparr>" and
  chi_cprod: "\<chi> (cprod t_d_1 t_d_2) = prod_of\<lparr>(\<chi> t_d_1) \<times> (\<chi> t_d_2)\<rparr>" and
  inj_atom_of: "inj atom_of" and
  inj_on_set_of_t: "inj_on (set_of t) (\<pset> (\<chi> t))" and
  inj_on_prod_of: "inj_on prod_of ((\<chi> t_d_1) \<times> (\<chi> t_d_2))" and
  carrier_disjoint: "((\<chi> t_d_1) Int (\<chi> t_d_2)) \<noteq> \<emptyset> \<Leftrightarrow> t_d_1 = t_d_2" and
  carrier_cover: "\<univ>-['a cartuniv] = \<Union> {t \<bullet> \<chi> t}" and
  set_of_restrict: "set_of t (A \<inter> \<chi> t) = set_of t A"

lemmas chi_def [simp del] = chi_catom chi_cset chi_cprod

lemma chi_catom_mem:
  "a \<in> \<chi> catom \<Leftrightarrow> (\<exists> x \<bullet> a = atom_of x)"
  by (auto simp add: chi_def)

lemma chi_cset_mem:
  "a \<in> \<chi> (cset t) \<Leftrightarrow> (\<exists> x \<bullet> a = set_of t x \<and> x \<subseteq> \<chi> t)"
  by (auto simp add: chi_def)

lemma chi_cprod_mem:
  "a \<in> \<chi> (cprod t t') \<Leftrightarrow> (\<exists> x y \<bullet> a = prod_of (x, y) \<and> x \<in> \<chi> t \<and> y \<in> \<chi> t')"
  by (auto simp add: chi_def)

lemmas chi_mem = chi_catom_mem chi_cset_mem chi_cprod_mem

lemma
  set_of_ran: "set_of t A \<in> \<chi> (cset t)"
  apply (simp add: chi_cset)
  apply (simp add: image_def)
  apply (witness "A \<inter> \<chi> t")
  apply (auto simp add: set_of_restrict)
  done

text {*

The fact that we restrict the injectivity of @{text set_of} is
critical to ensuring that @{text "'a cartuniv"} is a conservative
extension to HOL, since it allows the cardinality of @{text "'a cartuniv"} 
to be strictly less than @{text "('a cartuniv) set"}. 
In fact, it is easy to construct an inductive model theoretic argument that
\begin{quote}
@{text "\<^EP>{:\<chi> t:}{:\<^UNIV>-[('a ctype_of) t]:}"}
\end{quote}
for all @{text "t"}.
\begin{itemize}
\item
Clearly, from @{text "inj_atom_of"} and 
the definition of @{text "\<chi> catom"},
we have @{text "\<^EP>{:\<chi> catom:}{:\<^UNIV>-['a]:}"}.

\item
Assume @{text "\<^EP>{:\<chi> t:}{:\<^UNIV>-[('a ctype_of) t]:}"},
then with @{text "inj_set_of"} and the definition of 
@{text "\<chi> (cset t)"}, we have 
\begin{quote}
@{text "\<^EP>{:\<chi> (cset t):}{:\<^UNIV>-[(('a ctype_of) t) set]:}"}.
\end{quote}

\item
Assume @{text "\<^EP>{:\<chi> t_d_1:}{:\<^UNIV>-[('a ctype_of) t_d_1]:}"}
and @{text "\<^EP>{:\<chi> t_d_2:}{:\<^UNIV>-[('a ctype_of) t_d_2]:}"},
then with @{text "inj_prod_of"} 
and the definition of @{text "\<chi> (cprod t_d_1 t_d_2)"}
we have that 
\begin{quote}
@{text "\<^EP>{:\<chi> (cprod t_d_1 t_d_2):}{:\<^UNIV>-[(('a ctype_of) t_d_1) \<times> (('a ctype_of) t_d_2)]:}"}.
\end{quote}
\end{itemize}
Thus, with @{text carrier_disjoint} and @{text carrier_cover} we can
deduce that 
\begin{quote}
@{text "\<^EP>{:('a cartuniv):}{:(\<^UNIV>-[\<Sigma> t \<bullet> ('a ctype_of) t]):}"}.
\end{quote}

*} 

lemma carrierI: "\<exists> t \<bullet> a \<in> \<chi> t"
proof -
  have "a \<in> \<univ>" by (auto)
  then show ?thesis
    by (auto simp add: carrier_cover)
qed

lemma carrier_nemp: "\<exists> a \<bullet> a \<in> \<chi> T"
proof (induct T)
  have "\<exists> x::'a \<bullet> \<True>" by (auto)
  then have "\<exists> x::'a \<bullet> atom_of x \<in> \<chi> catom" by (auto simp add: chi_catom)
  then show "\<exists> a::'a cartuniv \<bullet> a \<in> \<chi> catom" by (auto)
next
  apply_end (msafe(inference))
  fix T::CT and a::"'a cartuniv"
  assume a1: "a \<in> \<chi> T"
  then have "{a} \<in> \<pset> (\<chi> T)"
    by (auto)
  then have "set_of T {a} \<in> \<chi> (cset T)"
    by (auto simp add: chi_cset)
  then show "\<exists> a::'a cartuniv \<bullet> a \<in> \<chi> (cset T)"
    by (auto)
next
  fix T::CT and a::"'a cartuniv" and
      T'::CT and a'::"'a cartuniv"
  assume a1: "a \<in> \<chi> T" and a2: "a' \<in> \<chi> T'"
  then have "prod_of (a, a') \<in> \<chi> (cprod T T')"
    by (auto simp add: chi_cprod)
  then show "\<exists> a::'a cartuniv \<bullet> a \<in> \<chi> (cprod T T')"
    by (auto)
qed

lemma carrier_nuniv: "\<exists> a \<bullet> a \<notin> \<chi> T"
proof -
  have "\<exists> T' \<bullet> T' \<noteq> T"   
    by (induct T type: CT, auto)
  also have "(\<exists> T' \<bullet> T' \<noteq> T)
  \<Leftrightarrow> (\<exists> T' \<bullet> \<chi> T' \<inter> \<chi> T = \<emptyset>-['a cartuniv])"
  proof (mauto(wind))
    fix T'::CT
    have "T' \<noteq> T \<Leftrightarrow> \<not>(\<chi> T' \<inter> \<chi> T \<noteq> \<emptyset>)"
      by (simp add: carrier_disjoint)
    then show "T' \<noteq> T \<Leftrightarrow> \<chi> T' \<inter> \<chi> T = \<emptyset>"
      by (auto)
  qed
  also have "\<dots> 
  \<Leftrightarrow> (\<exists> T' \<bullet> \<chi> T' \<inter> \<chi> T = \<emptyset>-['a cartuniv] \<and> (\<exists> a::'a cartuniv \<bullet> a \<in> \<chi> T'))"
    by (mauto(wind), rule carrier_nemp)
  also have "\<dots> 
  \<Leftrightarrow> (\<exists> T' (a::'a cartuniv) \<bullet> \<chi> T' \<inter> \<chi> T = \<emptyset>-['a cartuniv] \<and> a \<in> \<chi> T')"
    by (auto)
  also have "\<dots> 
  \<Rightarrow> (\<exists> T' (a::'a cartuniv) (b::'a cartuniv) \<bullet> \<chi> T' \<inter> \<chi> T = \<emptyset>-['a cartuniv] \<and> a \<notin> \<chi> T)"
    by (mauto(wind))
  finally show "(\<exists> (a::'a cartuniv) \<bullet> a \<notin> \<chi> T)"
    by (auto)
qed

lemma inj_prod_of: "inj (prod_of-['a])"
proof -
  let ?prod_of = "prod_of-['a]"
  have "\<forall> t_d_1 t_d_2 \<bullet> inj_on ?prod_of (\<chi> t_d_1 \<times> \<chi> t_d_2)"
    by (auto intro: inj_on_prod_of)
  have "inj_on ?prod_of (\<Union> {t_d_1 t_d_2 \<bullet> \<chi> t_d_1 \<times> \<chi> t_d_2})"
  proof (rule inj_onI, auto)
    fix a a' b b' t_d_1 t_d_2 
    assume b1: "?prod_of (a, b) = ?prod_of (a', b')" and
      b2: "a \<in> \<chi> t_d_1" and b3: "b \<in> \<chi> t_d_2"
    from b2 b3 have "prod_of (a, b) \<in> \<chi> (cprod t_d_1 t_d_2)"
      by (auto simp add: chi_cprod)
    with b1 have b4: "prod_of (a', b') \<in> \<chi> (cprod t_d_1 t_d_2)"
      by (auto)
    have "\<exists> t_d_1' t_d_2' \<bullet> a' \<in> \<chi> t_d_1' \<and> b' \<in> \<chi> t_d_2'"
      by (auto intro: carrierI)
    then have b5: "a' \<in> \<chi> t_d_1 \<and> b' \<in> \<chi> t_d_2"
    proof (msafe(inference))
      fix t_d_1' t_d_2'
      assume c1: "a' \<in> \<chi> t_d_1'" and c2: "b' \<in> \<chi> t_d_2'"
      then have "prod_of (a', b') \<in> \<chi> (cprod t_d_1' t_d_2')"
        by (auto simp add: chi_cprod)
      with b4 have "\<chi> (cprod t_d_1 t_d_2) \<inter> \<chi> (cprod t_d_1' t_d_2') \<noteq> (\<emptyset>-['a cartuniv])"
        by (auto)
      then have c3: "t_d_1' = t_d_1 \<and> t_d_2' = t_d_2"
        by (auto simp only: carrier_disjoint)
      from c1 c3 show "a' \<in> \<chi> t_d_1" by (auto)
      from c2 c3 show "b' \<in> \<chi> t_d_2" by (auto)
    qed
    from b1 have b6: "(a, b) = (a', b')"
    proof (rule inj_on_prod_of [THEN inj_onD])
      from b2 b3 show "(a,b) \<in> \<chi> t_d_1 \<times> \<chi> t_d_2"
        by (auto)
      from b5 show "(a',b') \<in> \<chi> t_d_1 \<times> \<chi> t_d_2"
        by (auto)
    qed
    from b6 show "a = a'" by (auto)
    from b6 show "b = b'" by (auto)
  qed
  also have "(\<Union> {t_d_1 t_d_2 \<bullet> \<chi> t_d_1 \<times> \<chi> t_d_2}) = \<univ>-['a cartuniv \<times> 'a cartuniv]"
    by (auto intro: carrierI)
  finally show ?thesis by this
qed

lemma prod_of_eq:
  "prod_of (a, b) = prod_of (a', b') \<Leftrightarrow> a = a' \<and> b = b'"
  by (auto dest!: inj_prod_of [THEN injD])

lemma carrier_eq: 
  assumes a1: "a \<in> \<chi> s"
  shows "a \<in> \<chi> t \<Leftrightarrow> t = s"
  using a1
proof (auto)
  assume a2: "a \<in> \<chi> t"
  with a1 have "\<chi> s \<inter> \<chi> t \<noteq> (\<emptyset>-['a cartuniv])"
    by (auto)
  then show "t = s" by (auto simp add: carrier_disjoint)
qed

lemma carrier_eqI: 
  assumes a1: "a \<in> \<chi> s"
  shows "a \<in> \<chi> t \<turnstile> t = s"
  by (simp add: carrier_eq [OF a1])

lemma inj_set_of: "inj set_of"
proof (rule inj_onI)
  let ?set_of = "set_of-['a]"
  fix s t
  assume a1: "?set_of s = ?set_of t"
  have a2: "?set_of s \<emptyset> \<in> \<chi> (cset s)"
    by (auto simp add: chi_cset)
  from a1 have "?set_of s \<emptyset> = ?set_of t \<emptyset>"
    by (simp)
  then have a3: "?set_of s \<emptyset> \<in> \<chi> (cset t)"
    by (auto simp add: chi_cset)
  from a2 a3 have "((\<chi> (cset s)) Int (\<chi> (cset t))) \<noteq> (\<emptyset>-['a cartuniv])"
    by (auto)
  then have "cset s = cset t"
    by (rule carrier_disjoint [THEN iffD1])
  then show "s = t" by (auto)
qed

lemma set_of_eq_restrict: 
  assumes a1: "A \<subseteq> \<chi> s" and a2: "B \<subseteq> \<chi> t" 
  shows "set_of s A = set_of t B \<Leftrightarrow> s = t \<and> A = B"
proof (msafe_no_assms(inference))
  assume a3: "set_of s A = set_of t B"
  from a1 a2 have "set_of s A \<in> \<chi> (cset s) \<and> set_of t B \<in> \<chi> (cset t)"
    by (auto simp add: chi_cset)
  with a3 have "\<chi> (cset s) \<inter> \<chi> (cset t) \<noteq> (\<emptyset>-['a cartuniv])"
    by (auto) 
  then have "cset s = cset t" by (simp only: carrier_disjoint)
  then show a4: "s = t" by (auto)
  show "A = B"
    apply (rule inj_on_set_of_t [THEN inj_onD])
    apply (insert a4 a1 a2 a3)
    by (auto)
next
  assume "s = t" "A = B"
  then show "set_of s A = set_of t B" by (simp)
qed

lemma set_of_eq: 
  "set_of s A = set_of t B \<Leftrightarrow> s = t \<and> A \<inter> \<chi> s = B \<inter> \<chi> t"
proof -
  have b1: 
    "set_of s A = set_of t B
    \<Leftrightarrow> set_of s (A \<inter> \<chi> s) = set_of t (B \<inter> \<chi> t)"
    by (simp add: set_of_restrict)
  have 
    b2a: "A \<inter> \<chi> s \<subseteq> \<chi> s" and 
    b2b: "B \<inter> \<chi> t \<subseteq> \<chi> t"
    by (auto)
  from b1 set_of_eq_restrict [OF b2a b2b]
  show 
    ?thesis
    by (simp)
qed
  
lemmas [simp] =  
  inj_atom_of [THEN inj_eq]
  inj_on_set_of_t [THEN inj_on_iff]
  set_of_eq
  prod_of_eq

lemma atom_setE: 
  assumes 
    a1: "atom_of x = set_of t A"
  shows 
    "P" 
proof -
  have a2: "atom_of x \<in> \<chi> catom"
    by (auto simp add: chi_catom)
  have a3: "set_of t A \<in> \<chi> (cset t)"
    by (rule set_of_ran)
  from a1 a2 a3 have "atom_of x \<in> \<chi> catom \<inter>  \<chi> (cset t)"
    by (simp)
  then have "\<chi> catom \<inter>  \<chi> (cset t) \<noteq> (\<emptyset>-['a cartuniv])"
    by (auto)
  then have a4: "catom = cset t"
    by (simp only: carrier_disjoint)
  have a5: "catom \<noteq>  cset t" by (auto)
  from a4 a5 show P by (contradiction)
qed

lemma atom_setF [simp]: 
   "atom_of x = set_of t A \<Leftrightarrow> False"
  by (auto elim: atom_setE)

lemma set_atomF [simp]: 
   "set_of t A = atom_of x \<Leftrightarrow> False"
  by (auto elim: atom_setE [OF sym])

lemma atom_prodE: 
  assumes 
    a1: "atom_of x = prod_of (b,c)"
  shows 
    "P" 
proof -
  have 
    a2: "atom_of x \<in> \<chi> catom"
    by (auto simp add: chi_catom)
  from carrierI [of b] carrierI [of c]
  have
    a3: "(\<exists> s t \<bullet> prod_of (b, c) \<in> \<chi> (cprod s t))"
    by (auto simp add: chi_cprod)
  from a1 a2 a3 have 
    "(\<exists> s t \<bullet> atom_of x \<in> \<chi> catom \<inter> \<chi> (cprod s t))"
    by (simp)
  then show 
    "P"
  proof (msafe(inference))
    fix s t 
    assume
      b1: "atom_of x \<in> \<chi> catom \<inter> \<chi> (cprod s t)"
    then have 
      "\<chi> catom \<inter>  \<chi> (cprod s t) \<noteq> (\<emptyset>-['a cartuniv])"
      by (auto)
    then have 
      b2: "catom = cprod s t"
      by (simp only: carrier_disjoint)
    have 
      b3: "catom \<noteq>  cprod s t" 
      by (auto)
    from b2 b3 show 
      P 
      by (contradiction)
  qed
qed

lemma atom_prodF [simp]: 
  "atom_of x = prod_of (b, c) \<Leftrightarrow> False"
  by (auto elim: atom_prodE)

lemma prod_atomF [simp]: 
  "prod_of (b, c) = atom_of x \<Leftrightarrow> False"
  by (auto elim: atom_prodE [OF sym])

lemma set_prodE: 
  assumes 
    a1: "set_of t A = prod_of (b, c)"
  shows 
    "P" 
proof -
  have 
    a2: "set_of t A \<in> \<chi> (cset t)"
    by (rule set_of_ran)
  from carrierI [of b] carrierI [of c]
  have 
    a3: "\<exists> r s \<bullet> prod_of (b, c) \<in> \<chi> (cprod r s)"
    by (auto simp add: chi_cprod)
  from a1 a2 a3 have 
    "(\<exists> r s \<bullet> set_of t A \<in> \<chi> (cset t) \<inter> \<chi> (cprod r s))"
    by (simp)
  then show "P"
  proof (msafe(inference))
    fix r s
    assume 
      b1: "set_of t A \<in> \<chi> (cset t) \<inter> \<chi> (cprod r s)"
    then have 
      "\<chi> (cset t) \<inter>  \<chi> (cprod r s) \<noteq> (\<emptyset>-['a cartuniv])"
      by (auto)
    then have 
      b2: "cset t = cprod r s"
      by (simp only: carrier_disjoint)
    have 
      b3: "cset t \<noteq>  cprod r s" 
      by (auto)
    from b2 b3 show 
      P 
      by (contradiction)
  qed
qed

lemma set_prodF [simp]:
  "set_of t A = prod_of (b, c) \<Leftrightarrow> False"
  by (auto elim: set_prodE)

lemma prod_setF [simp]: 
  "prod_of (b, c) = set_of t A \<Leftrightarrow> False"
  by (auto elim: set_prodE [OF sym])

subsection {* Typing *}

text {*

%Since @{text "'a cartuniv"} is, in a sense, 
%closed under products and power sets we can define these operators here as
%monomorphic functions. In order to do this we begin by introducing some
%technical operators.

The properties of the @{text "\<chi>"} operator mean that @{text "CT"} can be
used as a form of typing system on @{text "'a cartuniv"}.

*}

definition
  ct_of :: "'a cartuniv \<rightarrow> CT"
where
  ct_of_def: "ct_of a \<defs> (\<mu> t | a \<in> \<chi> t)"

lemma ct_of_eq:
  "a \<in> \<chi> t \<turnstile> ct_of a = t"
proof (auto intro!: the_equality simp add: ct_of_def)
  fix t' assume 
    "a \<in> \<chi> t" "a \<in> \<chi> t'"
  with carrier_disjoint show 
    "t' = t"
    by (auto)
qed

lemma ct_of_char: 
  "a \<in> \<chi> (ct_of a)"
  using carrier_disjoint carrier_cover [simplified set_eq_def]
  apply (simp add: ct_of_def)
  apply (rule theI')
  apply (auto)
  done

lemma ct_of_conv: 
  "ct_of a = t \<Leftrightarrow> a \<in> \<chi> t"
proof (msafe_no_assms(inference))
  assume 
    b1: "ct_of a = t"
  from ct_of_char [of a]
  show 
    "a \<in> \<chi> t" 
    by (simp add: b1)
next
  assume 
    a1: "a \<in> \<chi> t"
  with ct_of_eq [of a t] show 
    "ct_of a = t"
    by (auto)
qed

lemma ct__of_atom [simp]: 
  "ct_of (atom_of x) = catom"
  by (simp add: ct_of_conv chi_catom)

lemma ct_of_set [simp]: 
  "ct_of (set_of t A) = cset t"
  by (insert set_of_ran [of t A], simp add: ct_of_conv)

lemma ct_of_prod [simp]: 
  "ct_of (prod_of (b, c)) = cprod (ct_of b) (ct_of c)"
proof - 
  have 
    "b \<in> \<chi> (ct_of b) \<and> c \<in> \<chi> (ct_of c) \<and> prod_of (b, c) = prod_of (b, c)"
    by (simp add: ct_of_char)
  then show 
    ?thesis
    by (auto simp add: chi_cprod ct_of_conv image_def)
qed

subsection {* Cartesian induction *}

text {*

The typing scheme described above gives us a handle to do case and induction
proofs on @{text "'a cartuniv"}.

*}

lemma cartuniv_exhaust: 
  "(\<exists> x \<bullet> a = atom_of x) \<or> 
  (\<exists> A t \<bullet> a = set_of t A \<and> A \<subseteq> \<chi> t) \<or> 
  (\<exists> b c s t \<bullet> a = prod_of (b, c) \<and> b \<in> \<chi> s \<and> c \<in> \<chi> t)"
proof -
  have 
    a1: "ct_of a = catom \<or> (\<exists> t \<bullet> ct_of a = cset t) \<or> (\<exists> s t \<bullet> ct_of a = cprod s t)"
    by (cases "ct_of a" type: CT, auto)
  then show 
    ?thesis
    apply (simp only: ct_of_conv image_def)
  proof (msafe_no_assms(inference))
    fix x assume
      b1: "a \<in> \<chi> catom"
    then show 
      ?thesis 
      by (auto simp add: chi_catom)
  next
    fix t assume 
      b1: "a \<in> \<chi> (cset t)"
    then have 
      "(\<exists> A \<bullet> a = set_of t A)"
      by (auto simp add: chi_cset)
    with b1 show 
      ?thesis 
      by (auto simp add: chi_cset)
  next
    fix s t assume 
      b1: "a \<in> \<chi> (cprod s t)"
    then have 
      "(\<exists> b c \<bullet> a = prod_of (b, c) \<and> b \<in> \<chi> s \<and> c \<in> \<chi> t)"
      by (auto simp add: chi_cprod)
    with b1 show 
      ?thesis 
      by (blast)
  qed
qed

theorem cartuniv_cases: 
  assumes 
    a1: "\<And> x \<bullet> a = atom_of x \<turnstile> P a" and
    a2: "\<And> A t \<bullet> \<lbrakk> a = set_of t A; A \<subseteq> \<chi> t \<rbrakk> \<turnstile> P a" and
    a3: "\<And> b c s t \<bullet> \<lbrakk> a = prod_of (b, c); b \<in> \<chi> s; c \<in> \<chi> t \<rbrakk> \<turnstile> P a"
  shows 
    "P a"
proof -
  from cartuniv_exhaust [of a] show 
    "P a"
  proof (elim disjE exE conjE)
    fix x assume 
      "a = atom_of x"
    then show 
      "P a" 
      by (rule a1)
  next
    fix A t assume 
      "a = set_of t A" "A \<subseteq> \<chi> t"
    then show 
      "P a" 
      by (rule a2)
  next
    fix b c s t 
    assume 
      "a = prod_of (b, c)" "b \<in> \<chi> s" "c \<in> \<chi> t"
    then show 
      "P a" 
      by (rule a3)
  qed
qed

lemmas [cases type: cartuniv] = cartuniv_cases

text {*

In order to prove the induction theorem, we first introduce a measure
on @{text "'a cartuniv"} induced by @{text CT}.

*}

fun
  rank :: "CT \<rightarrow> \<nat>"
where
  "rank catom = 0"
| "rank (cset t) = Suc (rank t)"
| "rank (cprod s t) = Suc (max (rank s) (rank t))"

theorem cartuniv_induct: 
  assumes 
    a1: "\<And> x \<bullet> P (atom_of x)" and
    a2: "\<And> A t \<bullet> \<lbrakk> A \<subseteq> \<chi> t; (\<forall> a | a \<in> A \<bullet> P a) \<rbrakk> \<turnstile> P (set_of t A)" and
    a3: "\<And> b c s t \<bullet> \<lbrakk> b \<in> \<chi> s; c \<in> \<chi> t; P b; P c \<rbrakk> \<turnstile> P (prod_of (b, c))"
  shows 
    "P a"
proof (induct a rule: measure_induct [where ?f = "rank \<circ> ct_of"])
  fix 
    a::"'a cartuniv"
  assume 
    a4: "\<forall> b \<bullet> (rank \<circ> ct_of) b < (rank \<circ> ct_of) a \<Rightarrow> P b"
  show 
    "P a"
  proof (cases type: cartuniv)
    fix x 
    assume 
      "a = atom_of x"
    with a1 show 
      "P a" 
      by (simp)
  next
    fix A t 
    assume 
      b1: "a = set_of t A" and 
      b2: "A \<subseteq> \<chi> t"
    from b1 have 
      b3: "ct_of a = cset t"
      by (simp)
    from b2 have 
      b4: "(\<forall> b | b \<in> A \<bullet> ct_of b = t)"
      by (auto simp add: ct_of_conv)
    with b3 have 
      b5: "(\<forall> b | b \<in> A \<bullet> (rank \<circ> ct_of) b < (rank \<circ> ct_of) a)"
      by (auto)
    with a4 have 
      "(\<forall> b | b \<in> A \<bullet> P b)"
      by (auto)
    with b2 show 
      "P a" 
      by (auto intro: a2 simp add: b1) 
  next
    fix b c s t
    assume 
      b1: "a = prod_of (b, c)" and
      b2: "b \<in> \<chi> s" and b3: "c \<in> \<chi> t"
    then have 
      b4: "ct_of a = cprod s t"
      by (auto simp add: ct_of_conv)
    from b2 have 
      b5: "ct_of b = s"
      by (auto simp add: ct_of_conv)
    from b3 have 
      b6: "ct_of c = t"
      by (auto simp add: ct_of_conv)
    have 
      b7: "P b"  
      by (rule  a4 [rule_format], auto simp add: b4 b5 max_def)
    have 
      b8: "P c"  
      by (rule  a4 [rule_format], auto simp add: b4 b6 max_def)
    from b2 b3 b7 b8 show 
      "P a"
      apply (auto intro: a2 simp add: b1)
      apply (rule a3, assumption+)
    done
  qed
qed

lemmas [induct type: cartuniv] = cartuniv_induct

section {* Functions in the Cartesian Universe *}

text {*

The structure of the Cartesian Universe gives us the ability to 
create a mirror of the entirety of set theory if we so choose.
We see no compelling reason to go through the whole of this
development, but we do see a value for identifying function-like objects
in the Universe and defining a facility for using them in a function role.

*}

definition
  CU_set :: "'a cartuniv \<rightarrow> ('a cartuniv) set"
where
  CU_set_def: "CU_set v \<defs> (\<mu> S T | S \<subseteq> \<chi> T \<and> v = set_of T S \<bullet> S)"

definition
  CU_pair :: "'a cartuniv \<rightarrow> ('a cartuniv) \<times> ('a cartuniv)"
where
  CU_pair_def: "CU_pair v \<defs> (\<mu> a b | v = prod_of (a, b) \<bullet> (a, b))"

lemma CU_set_restrict:
  "S \<subseteq> \<chi> t \<turnstile> CU_set (set_of t S) = S"
  apply (simp add: CU_set_def)
  apply (rule the_equality)
  apply (auto)
  done

lemma CU_set:
  "CU_set (set_of t S) = S \<inter> \<chi> t"
  apply (simp  add: CU_set_def)
  apply (rule the_equality)
  apply (auto)
  done

lemma 
  assumes 
    a1: "s \<in> \<chi> (cset t)"
  shows 
    CU_set_inv: "set_of t (CU_set s) = s" and
    CU_set_char: "CU_set s \<subseteq> \<chi> t"
proof -
  from a1 have b1: "(\<exists>\<subone> S \<bullet> (\<exists> t \<bullet> S \<subseteq> \<chi> t \<and> s = set_of t S))"
    by (auto simp add: image_def subset_rules chi_cset)
  from theI' [OF b1] obtain t' where 
    b2: "CU_set s \<subseteq> \<chi> t'" "s = set_of t' (CU_set s)"
    by (auto simp  add: CU_set_def chi_cset image_def eind_def)
  from a1 b2 carrier_disjoint [of t t'] have 
    "t' = t"
    by (auto simp add: chi_cset)
  with b2 show 
     "set_of t (CU_set s) = s"
     "CU_set s \<subseteq> \<chi> t"
    by (auto simp add: CU_set_def)
qed

lemma set_of_char:
  assumes 
    a1: "S \<subseteq> \<chi> t"
  shows 
    "set_of t S \<in> \<chi> (cset t)"
  using a1
  by (simp add: chi_cset)

lemma CU_pair:
  "CU_pair (prod_of (a, b)) = (a, b)"
  by (simp add: CU_pair_def eind_def)

lemma CU_pair_inv:
  assumes a1: "s \<in> \<chi> (cprod T T')"
  shows "prod_of (CU_pair s) = s"
proof -
  from a1 have b1: "(\<exists>\<subone> ab \<bullet> (\<exists> a b \<bullet> ab = (a, b) \<and> s = prod_of (a, b)))"
    apply (simp add: image_def chi_cprod)
    apply (msafe_no_assms(inference))
    apply (rule ex1I)
    apply (auto)
    done
  from b1 [THEN theI'] obtain a b where 
    b2: "CU_pair s = (a, b) \<and> s = prod_of (a, b)"
    by (auto simp add: CU_pair_def eind_def)
  then show ?thesis
    by (auto)
qed

lemma CU_pair_char:
  assumes 
    a1: "s \<in> \<chi> (cprod T T')"
  shows 
    "CU_pair s \<in> \<chi> T \<times> \<chi> T'"
proof -
  from a1 obtain a b where 
    b1: "s = prod_of (a, b)" and 
    b2: "a \<in> \<chi> T" and 
    b3: "b \<in> \<chi> T'"
    by (auto simp add: chi_cprod)
  then show 
    ?thesis
    by (auto simp add: CU_pair)
qed

lemma prod_of_char:
  assumes 
    a1: "ab \<in> \<chi> T \<times> \<chi> S"
  shows 
    "prod_of ab \<in> \<chi> (cprod T S)"
  using a1
  by (simp add: chi_cprod)

definition
  graph_CU :: "[CT, CT, ('a cartuniv) \<leftrightarrow> ('a cartuniv)] \<rightarrow> 'a cartuniv"
where
  graph_CU_def: "graph_CU T S f \<defs> set_of (cprod T S) { x y | (x \<mapsto> y) \<in> f \<bullet> prod_of (x, y)}"

definition
  CU_graph :: "'a cartuniv \<rightarrow> ('a cartuniv) \<leftrightarrow> ('a cartuniv)"
where
  CU_graph_def: "CU_graph v \<defs> {m | m \<in> CU_set v \<bullet> CU_pair m}"

notation (zed)
  CU_graph ("\<cugraphof>{:_:}")

lemma graph_CU_char:
  assumes 
    a1: "f \<in> \<chi> T \<zrel> \<chi> T'"
  shows 
    "graph_CU T T' f \<in> \<chi> (cset (cprod T T'))"
proof -
  from a1 have 
    b1: "{ x y | (x \<mapsto> y) \<in> f \<bullet> prod_of (x, y)} \<subseteq> \<chi> (cprod T T')"
    by (auto simp add: rel_def chi_cprod)
  from set_of_char [OF b1]
  show 
    ?thesis
    by (simp add: graph_CU_def)
qed

lemma graph_CU_restrict:
  "graph_CU T T' (f \<inter> (\<chi> T \<times> \<chi> T')) = graph_CU T T' f"
  by (auto simp add: graph_CU_def set_of_restrict [of "cprod T S" "{ x y | (x \<mapsto> y) \<in> f \<bullet> prod_of (x, y)}"] chi_cset chi_cprod)

lemma graph_CU_ran:
  "graph_CU T T' f \<in> \<chi> (cset (cprod T T'))"
proof -
  have 
    b1: "graph_CU T T' (f \<inter> (\<chi> T \<times> \<chi> T')) \<in> \<chi> (cset (cprod T T'))"
    apply (rule graph_CU_char)
    apply (auto simp add: rel_def)
    done
  then show 
    ?thesis 
    by (simp add: graph_CU_restrict)
qed

lemma CU_graph_char:
  assumes 
    a1: "f \<in> \<chi> (cset (cprod T T'))"
  shows 
    "CU_graph f \<in> \<chi> T \<zrel> \<chi> T'"
proof (auto simp add: CU_graph_def rel_def)
  fix a b m
  assume 
    b1: "(a \<mapsto> b) = CU_pair m" and 
    b2: "m \<in> CU_set f"
  from b2 CU_set_char [OF a1] have 
    b3: "m \<in> \<chi> (cprod T T')"
    by (auto)
  from b1 CU_pair_char [OF b3]
  show 
    "a \<in> \<chi> T" "b \<in> \<chi> T'"
    by (auto)
qed

lemma CU_graph:
  assumes 
    a1: "f \<in> \<chi> T \<zrel> \<chi> S"
  shows 
    "CU_graph (graph_CU T S f) = f"
proof -
  from a1 have 
    "{ x y | (x \<mapsto> y) \<in> f \<bullet> prod_of (x, y)} \<subseteq> \<chi> (cprod T S)"
    by (auto simp add: graph_CU_def image_def Pow_def rel_def chi_def)
  then show 
    ?thesis
    apply (auto simp add: CU_graph_def graph_CU_def CU_set_restrict CU_pair eind_def subset_def)
    apply (auto intro!: exI simp add: CU_pair)
    done
qed

lemma CU_graph_inv':
  assumes 
    a1: "f \<in> \<chi> (cset (cprod T S))"
  shows 
    "graph_CU T S (CU_graph f) = f"
proof -
  have 
    "graph_CU T S (CU_graph f)
    = set_of (cprod T S) {x y m | (x, y) = CU_pair m \<and> m \<in> CU_set f \<bullet> prod_of (x, y)}"
    by (simp add: graph_CU_def CU_graph_def eind_def)
  also have 
    "{x y m | (x, y) = CU_pair m \<and> m \<in> CU_set f \<bullet> prod_of (x, y)} 
    = CU_set f"
  proof (auto intro!: exI simp add: eind_def eind_comp)
    fix m
    assume 
      c1: "m \<in> CU_set f"
    with a1 have 
      c2: "m \<in> \<chi> (cprod T S)"
      by (auto simp add: CU_set_restrict chi_cset)
    then have 
      c3: "prod_of (CU_pair m) = m"
      by (rule CU_pair_inv)
    from c1 c3 show 
      "prod_of (CU_pair m) \<in> CU_set f"
      by (simp)
    from c3 show 
      "m = prod_of(\<fst> (CU_pair m), \<snd> (CU_pair m))"
      by (simp add: surjective_pairing [symmetric])
  qed (simp add: surjective_pairing [symmetric])
  also from a1 have 
    "set_of (cprod T S) (CU_set f) = f"
    by (rule CU_set_inv)
  finally show 
    ?thesis
    by (this)
qed

definition
  CT_rel :: "[CT, CT] \<rightarrow> 'a cartuniv set"
where
  CT_rel_def: "CT_rel T S \<defs> {r | r \<in> \<chi> T \<zrel> \<chi> S \<bullet> graph_CU T S r}"

definition
  CU_rel :: "'a cartuniv set"
where
  CU_rel_def: "CU_rel \<defs> (\<Union> T S \<bullet> CT_rel T S)"

lemma CT_rel_conv:
  "CT_rel T S = \<chi> (cset (cprod T S))"
proof (auto)
  fix f
  assume 
    b1: "f \<in> CT_rel T S"
  show 
    "f \<in> \<chi> (cset (cprod T S))"
  proof -
    from b1
    obtain r where 
      c1: "r \<in> \<chi> T \<zrel> \<chi> S" and  
      c2: "f = graph_CU T S r"
      by (auto simp add: CT_rel_def)
    from graph_CU_char [OF c1]
    show   
      ?thesis
      by (simp add: c2)
  qed
next
  fix r
  assume 
    b1: "r \<in> \<chi> (cset (cprod T S))"
  show 
    "r \<in> CT_rel T S"
    apply (simp add: CT_rel_def)
    apply (witness "CU_graph r")
    apply (simp add: CU_graph_inv' b1 CU_graph_char)
    done
qed

lemma graph_CU_rel:
  assumes 
    a1: "f \<in> \<chi> T \<zrel> \<chi> T'"
  shows 
    "graph_CU T T' f \<in> CT_rel T T'"
  using a1
  by (auto simp add: CT_rel_def) 

lemma CU_graph_inv:
  assumes 
    a1: "f \<in> CT_rel T S"
  shows 
    "graph_CU T S (CU_graph f) = f"
  using a1
  by (simp add: CU_graph_inv' CT_rel_conv)

lemma graph_CU_eq:
  assumes 
    a1: "r \<in> \<chi> T \<zrel> \<chi> S" and 
    a2: "r' \<in> \<chi> T' \<zrel> \<chi> S'"
  shows 
    "graph_CU T S r = graph_CU T' S' r' \<Leftrightarrow> T = T' \<and> S = S' \<and> r = r'"
proof -
  from a1 have 
    b1: "{ x y | (x \<mapsto> y) \<in> r \<bullet> prod_of (x, y)} \<subseteq> \<chi> (cprod T S)"
    by (auto simp add: graph_CU_def image_def Pow_def rel_def chi_def)
  from a2 have 
    b2: "{ x y | (x \<mapsto> y) \<in> r' \<bullet> prod_of (x, y)} \<subseteq> \<chi> (cprod T' S')"
    by (auto simp add: graph_CU_def image_def Pow_def rel_def chi_def)
  show 
    ?thesis
    apply (simp only: graph_CU_def rel_def set_of_eq_restrict [OF b1 b2])
    apply (auto)
  proof -
    assume 
      c1: "{ x y | (x \<mapsto> y) \<in> r \<bullet> prod_of (x, y) } = { x y | (x \<mapsto> y) \<in> r' \<bullet> prod_of (x, y) }"
    fix a b 
  { assume 
      c2: "(a \<mapsto> b) \<in> r"
    then have 
      "(prod_of (a, b)) \<in> { x y | (x \<mapsto> y) \<in> r \<bullet> prod_of (x, y) }"
      by (auto)
    then have 
      "(prod_of (a, b)) \<in> { x y | (x \<mapsto> y) \<in> r' \<bullet> prod_of (x, y) }"
      by (simp add: c1)
    then obtain a' b' where 
      "(a' \<mapsto> b') \<in> r' \<and> prod_of (a, b) = prod_of (a', b')"
      by (auto)
    then show 
      "(a \<mapsto> b) \<in> r'"
      by (auto simp add: inj_prod_of [THEN injD])
  next
    assume 
      c2: "(a \<mapsto> b) \<in> r'"
    then have 
      "(prod_of (a, b)) \<in> { x y | (x \<mapsto> y) \<in> r' \<bullet> prod_of (x, y) }"
      by (auto)
    then have 
      "(prod_of (a, b)) \<in> { x y | (x \<mapsto> y) \<in> r \<bullet> prod_of (x, y) }"
      by (simp add: c1)
    then obtain a' b' where 
      "(a' \<mapsto> b') \<in> r \<and> prod_of (a, b) = prod_of (a', b')"
      by (auto)
    then show 
      "(a \<mapsto> b) \<in> r"
      by (auto simp add: inj_prod_of [THEN injD])
  }
  qed
qed

definition
  CT_fun :: "[CT, CT] \<rightarrow> 'a cartuniv set"
where
  CT_fun_def: "CT_fun T S \<defs> {r | r \<in> \<chi> T \<ztfun> \<chi> S \<bullet> graph_CU T S r}"

definition
  CU_fun :: "'a cartuniv set"
where
  CU_fun_def: "CU_fun \<defs> (\<Union> T S \<bullet> CT_fun T S)"

lemma CU_graph_tfun:
  assumes 
    a1: "f \<in> CT_fun T S"
  shows 
    "CU_graph f \<in> \<chi> T \<ztfun> \<chi> S"
  using a1
  by (auto simp add: CT_fun_def CU_graph [OF pfun_rel [OF tfun_pfun]])

lemma graph_CU_tfun:
  assumes 
    a1: "f \<in> \<chi> T \<ztfun> \<chi> S"
  shows 
    "graph_CU T S f \<in> CT_fun T S"
  using a1
  by (auto simp add: CT_fun_def)

abbreviation
  op_CU :: "[CT, CT, ('a cartuniv) \<rightarrow> ('a cartuniv)] \<rightarrow> 'a cartuniv"
where
  "op_CU T S f \<defs> graph_CU T S (\<graphof> f)"

abbreviation
  CU_op :: "('a cartuniv) \<rightarrow> ('a cartuniv) \<rightarrow> ('a cartuniv)"
where
  "CU_op v \<defs> \<opof> (CU_graph v)"

notation (xsymbols output)
  CU_op  ("_\<cdot>_")

notation (zed)
  CU_op ("_\<cappl>_" [999,1000] 999)

lemma op_CU_char:
  "op_CU T T' f \<in> \<chi> (cset (cprod T T'))"
  by (simp add: graph_CU_ran)

lemma op_CU_ran:
  assumes 
    a1: "f\<down>(\<chi> T) \<in> \<chi> T \<ztfun> \<chi> T'"
  shows 
    "op_CU T T' f \<in> CT_fun T T'"
  apply (simp add: CT_fun_def)
  apply (witness "(\<graphof> f) \<inter> (\<chi> T \<times> \<chi> T')")
  apply (simp add: graph_CU_restrict)
  apply (rule subst [of "f\<down>(\<chi> T)" "(\<graphof> f) \<inter> (\<chi> T \<times> \<chi> T')"])
  using a1
  apply (auto simp add: view_def graph_of_def glambda_mem)
  apply (auto dest!: tfun_range simp add: glambda_beta)
  done

lemma CU_op_char:
  assumes 
    a1: "f \<in> CT_fun T T'"
  shows 
    "(CU_op f)\<down>(\<chi> T) \<in> \<chi> T \<ztfun> \<chi> T'"
  apply (mauto(fspace))
  apply (simp add: view_dom)
  apply (auto simp add: view_def glambda_mem tfun_range [OF CU_graph_tfun [OF a1]])
  done

lemma CU_op_beta:
  assumes 
    a1: "f \<in> CT_fun T T'" and 
    a2: "x \<in> \<chi> T"
  shows 
    "f\<cappl>x \<in> \<chi> T'"
  apply (rule tfun_range)
  apply (rule CU_graph_tfun)
  apply (rule a1)
  apply (rule a2)
  done
  
lemmas [simp del] =  
  inj_atom_of [THEN inj_eq]
  inj_on_set_of_t [THEN inj_on_iff]
  set_of_eq
  prod_of_eq

end
