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
  Ordinal 
  
imports 
  Z_Fun 
  Orders

begin


text {*

Ordinal numbers are used to treat set cardinality and to develop
notions of induction and recursion.

The strong typing constraints of Higher Order Logic make it impossible
to develop a monolithic construction of the ordinal numbers. Instead
it is necessary to adopt a type generic approach to the ordinals,
constrcuting a specific ordinal type for each HOL type.
The ordinals over @{typ "'a"}
must be a type with cardinality at least that of @{typ "'a"} and with a natural
well-ordering.

To do this we begin by adopting sets over @{typ "'a"} as the basic model.
Ordinal successor is defining to add a new element to a set and
ordinal limit as distributed union.
The ordinals over @{typ "'a"} are then isomorphic to the smallest
collection of sets over @{typ "'a"} which
is closed under successors and limits.

*}

definition
  osuc_Rep :: "'a set \<rightarrow> 'a set" 
where
  osuc_Rep_def: "osuc_Rep B \<defs> (B \<union> { (\<some> y | y \<notin> B) })"

definition
  olim_Rep :: "('a set) set \<rightarrow> 'a set" 
where
  olim_Rep_def: "olim_Rep CL_B \<defs> (\<Union>{ B | B \<in> CL_B })"

definition
  ordinal :: "('a set) set" 
where
  ordinal_def: "ordinal \<defs> 
    \<Inter>{CL_B::(('a set) set) |
      (\<forall> B | B \<in> CL_B \<bullet> osuc_Rep B \<in> CL_B) \<and> 
      (\<forall> CL_C | CL_C \<subseteq> CL_B \<bullet> olim_Rep CL_C \<in> CL_B)}"

(*
abbreviation
  ordinals :: "'a set set" where 
  "ordinals \<defs> 
    \<Inter>{CL_B::(('a set) set) |
      (\<forall> B | B \<in> CL_B \<bullet> osuc_Rep B \<in> CL_B) \<and> 
      (\<forall> CL_C | CL_C \<subseteq> CL_B \<bullet> olim_Rep CL_C \<in> CL_B)}"
*)

typedef
  'a ordinal = "ordinal :: 'a set set"
(*
    "\<Inter>{CL_B::(('a set) set)|
      (\<forall> B | B \<in> CL_B \<bullet> osuc_Rep B \<in> CL_B) \<and> 
      (\<forall> CL_C | CL_C \<subseteq> CL_B \<bullet> olim_Rep CL_C \<in> CL_B)}"
*)
proof -
  let ?B = "\<emptyset>"
  have "?B \<in> \<Inter>{ CL_B::(('a set) set) |
    (\<forall> B | B \<in> CL_B \<bullet> osuc_Rep B \<in> CL_B) \<and>
   (\<forall> CL_C | CL_C \<subseteq> CL_B \<bullet> olim_Rep CL_C \<in> CL_B)}"
    (is "?B \<in> ?O")
  proof (simp, rule allI, rule impI, elim conjE)
    fix "CL_B"
    assume 
      a1: "(\<forall> (B :: 'a set) | B \<in> CL_B \<bullet> osuc_Rep B \<in> CL_B)" and
      a2: "(\<forall> (CL_C :: 'a set set) | CL_C \<subseteq> CL_B \<bullet> olim_Rep CL_C \<in> CL_B)"
    have 
      b: "{} \<subseteq> CL_B \<Rightarrow> olim_Rep {} \<in> CL_B"
      by (rule a2 [THEN allE [of _ "{}"]])
    have 
      "({} \<in> CL_B) 
      = (olim_Rep {} \<in> CL_B)"
      by (simp add: olim_Rep_def)
    also have "\<dots> 
      = ({} \<subseteq> CL_B \<Rightarrow> olim_Rep {} \<in> CL_B)"
      by (simp)
    finally show 
      "{} \<in> CL_B" 
      by (simp add: b)
  qed
  then show 
    "(\<exists> (B :: 'a set) \<bullet> B \<in> ordinal)"
    by (unfold ordinal_def, witness "?B")
(*
  then show 
    "(\<exists> B \<bullet> B \<in> ?O)"
    by (witness "?B")
*)
qed

interpretation ord: type_definition "Rep_ordinal" "Abs_ordinal" "ordinal"
  by (rule type_definition_ordinal)
(*
interpretation ord: type_definition "Rep_ordinal" "Abs_ordinal" "(\<Inter> CL_B | (\<forall> B \<bullet> B \<in> CL_B \<Rightarrow> osuc_Rep B \<in> CL_B) \<and> (\<forall>CL_C\<subseteq>CL_B. olim_Rep CL_C \<in> CL_B))"
  by (rule type_definition_ordinal)
*)
section {* Representational constructions and lemmas *}

text {*

Before developing and investigating the necessary properties of
the ordinals, we must first pause to establish some lemmas that
will help in treating the particular ordinal representation we have
chosen.

First we observe that the typedef construction of the ordinals has
introduced a corresponding collection of @{text "'a"} sets @{term ordinal}.
This set is the justification for introducing the 
@{text "'a ordinal"} type. 
The typedef construction also introduced injective mappings
between @{text "'a ordinal"} and @{term ordinal}, 
making them set isomorphic.

*}

lemma Abs_ordinal_inj:
  "inj_on Abs_ordinal ordinal"
  by (rule inj_on_inverseI [of _ "Rep_ordinal"])
    (auto simp add: Abs_ordinal_inverse)

lemma Rep_ordinal_inj:
  "inj Rep_ordinal"
  by (rule inj_on_inverseI [of _ "Abs_ordinal"])
    (auto simp add: Rep_ordinal_inverse)

lemma Abs_ordinal_range_char:
  "Abs_ordinal\<lparr>ordinal\<rparr> = (UNIV::'a ordinal set)"
proof (auto simp add: image_def Bex_def)
  fix b::"'a ordinal"
  have "Rep_ordinal b \<in> ordinal \<and> b = Abs_ordinal (Rep_ordinal b)"
    by (simp add: Rep_ordinal Rep_ordinal_inverse)
  then show "\<exists> B \<bullet> B \<in> ordinal \<and> b = Abs_ordinal B"
    by (auto)
qed

lemma Rep_ordinal_range_char:
  "range Rep_ordinal = (ordinal::'a set set)"
proof (auto simp add: image_def Bex_def Rep_ordinal)
  fix B::"'a set"
  assume a1: "B \<in> ordinal"
  then have "B = Rep_ordinal (Abs_ordinal B)"
    by (simp add: Abs_ordinal_inverse)
  then show "(\<exists> b \<bullet> B = Rep_ordinal b)"
    by (auto)
qed

  
text {*

Using this representation we can define the basic ordinal constructors,
@{text "\<ozero>"},
@{text "\<osuc>"},
@{text "\<olim>"}, and
@{text "\<omax>"} on the
ordinals in the obvious ways.

*}

definition
  osuc :: "'a ordinal \<rightarrow> 'a ordinal"
where
  osuc_def: "osuc \<defs> (\<olambda> n \<bullet> Abs_ordinal (osuc_Rep (Rep_ordinal n)))"

notation (xsymbols)
  osuc ("\<osuc>")

definition
  olim :: "('a ordinal) set \<rightarrow> 'a ordinal"
where
  olim_def: "olim \<defs> (\<olambda> nn \<bullet> Abs_ordinal (olim_Rep { n | n \<in> nn \<bullet> Rep_ordinal n }))"

notation (xsymbols)
  olim ("\<olim>")

definition
  ozero :: "'a ordinal"
where
  ozero_def: "ozero \<defs> (\<olim> \<emptyset>)"

notation (xsymbols)
  ozero ("\<ozero>")

definition
  omax :: "'a ordinal"
where
  omax_def: "omax \<defs> \<olim> \<univ>"

notation (xsymbols)
  omax ("\<omax>")

text {*

The first representational results we require deal with the closure
of the @{term ordinal} set under successors and limits.

*}

lemma osuc_ordinalI:
  "B \<in> ordinal \<turnstile> osuc_Rep B \<in> ordinal"
proof -
  assume 
    a: "B \<in> ordinal"
  have 
    "B \<in> ordinal \<Rightarrow> osuc_Rep B \<in> ordinal"
    by (simp add: ordinal_def)
  then show 
    "osuc_Rep B \<in> ordinal" 
    by (rule) (rule a)
qed

lemma olim_ordinalI:
  "CL_B \<subseteq> ordinal \<turnstile> olim_Rep CL_B \<in> ordinal"
proof -
  assume a: "CL_B \<subseteq> ordinal"
  show "olim_Rep CL_B \<in> ordinal" (is "?P ordinal")
  proof -
    have c: "?P (Inter { CL_B |
      (\<forall> B | B \<in> CL_B \<bullet> osuc_Rep B \<in> CL_B) &
      (\<forall> CL_C | CL_C \<subseteq> CL_B \<bullet> olim_Rep CL_C \<in> CL_B)})"
      (is "?P (Inter { CL_B | ?QA CL_B \<and> ?QB CL_B })")
    proof (rule InterI, simp, elim conjE)
      fix CL_C
      assume 
        da: "?QA CL_C" and 
        db: "?QB CL_C"
      show "olim_Rep CL_B \<in> CL_C"
      proof (rule db [THEN [2] mp], rule impI, elim allE [of _ CL_B], elim impE)
        show "CL_B \<subseteq> CL_C"
        proof (rule a [THEN [2] mp], auto simp add: subset_def)
          fix x
          assume
            ea: "(\<forall> x | x \<in> CL_B \<bullet> x \<in> ordinal)" and 
            eb: "x \<in> CL_B"
          then have 
            ec: "x \<in> ordinal"
            by (auto)
          have
            ed: "x \<in> ordinal \<turnstile> x \<in> CL_C"
            by (simp add: ordinal_def, elim allE [of _ CL_C])
              (simp add: da db)
          show 
            "x \<in> CL_C"
            by (rule ed) (rule ec)
        qed
      qed (assumption)
    qed
    show 
      "?P ordinal"
       by (rule c [THEN [2] ssubst [of _ _ ?P]]) (simp add: ordinal_def)
  qed
qed

text {*

Further more @{term ordinal} is the smallest set closed under both
operations.

*}

lemma ord_char: 
  "\<lbrakk> 
    (\<forall> B | B \<in> CL_B \<bullet> osuc_Rep B \<in> CL_B);
    (\<forall> CL_C | CL_C \<subseteq> CL_B \<bullet> olim_Rep CL_C \<in> CL_B);
    CL_B \<subset> ordinal 
  \<rbrakk> \<turnstile> \<False>"
  by (auto simp add: ordinal_def Inter_eq)

lemma ord_char_eq: 
  "\<lbrakk> 
    (\<forall> B | B \<in> CL_B \<bullet> osuc_Rep B \<in> CL_B);
    (\<forall> CL_C | CL_C \<subseteq> CL_B \<bullet> olim_Rep CL_C \<in> CL_B);
    CL_B \<subseteq> ordinal 
  \<rbrakk> \<turnstile> CL_B = ordinal"
proof -
  assume
    a: "(\<forall> B | B \<in> CL_B \<bullet> osuc_Rep B \<in> CL_B)"
       "(\<forall> CL_C | CL_C \<subseteq> CL_B \<bullet> olim_Rep CL_C \<in> CL_B)"
       "CL_B \<subseteq> ordinal"
  have 
    b: "CL_B \<subset> ordinal \<or> CL_B = ordinal"
    apply (rule order_le_less [THEN iffD1])
    apply (rule a(3))
  done
  show 
    "CL_B = ordinal"
  proof (rule b [THEN [2] mp], rule impI, elim disjE)
    assume 
      c1: "CL_B \<subset> ordinal"
    show 
      "CL_B = ordinal"
      by (rule ord_char [THEN FalseE]) (rule a c1)+
  next
    assume 
      "CL_B = ordinal" 
    then show 
      "CL_B = ordinal"
      by (this)
  qed
qed

text {*

Next we introduce some lemmas dealing with distributing the
ordinal constructors through the abstraction and representation
mappings.

*}

lemma osuc_conv:
  "B \<in> ordinal \<turnstile> \<osuc> (Abs_ordinal B) = Abs_ordinal (osuc_Rep B)"
proof -
  assume a1: "B \<in> ordinal"
  have 
    "\<osuc> (Abs_ordinal B)
    = Abs_ordinal (osuc_Rep (Rep_ordinal (Abs_ordinal B)))"
    by (simp add: osuc_def)
  also have "\<dots>
    = Abs_ordinal (osuc_Rep B)"
    by (simp add: a1 [THEN Abs_ordinal_inverse])
  finally show 
    ?thesis
    by (this)
qed

lemma Rosuc_conv:
  "Rep_ordinal (\<osuc> b) = osuc_Rep (Rep_ordinal b)"
  by (simp add: osuc_def 
    Rep_ordinal [THEN osuc_ordinalI [THEN Abs_ordinal_inverse]])

lemma olim_conv:
  "CL_B \<subseteq> ordinal \<turnstile> \<olim> (Abs_ordinal\<lparr>CL_B\<rparr>) = Abs_ordinal (olim_Rep CL_B)"
proof -
  assume a1: "CL_B \<subseteq> ordinal"
  have a2: "\<forall> B \<bullet> B \<in> CL_B \<Rightarrow>  Rep_ordinal (Abs_ordinal B) = B"
    by (clarify, rule Abs_ordinal_inverse, rule a1 [THEN subsetD], assumption)
  have " \<olim> (Abs_ordinal\<lparr>CL_B\<rparr>)
  = Abs_ordinal (olim_Rep ({b | b \<in> Abs_ordinal\<lparr>CL_B\<rparr> \<bullet> Rep_ordinal b}))"
    by (auto simp add: olim_def)
  also have "{b | b \<in> Abs_ordinal\<lparr>CL_B\<rparr> \<bullet> Rep_ordinal b}
  = 
    {B | B \<in> CL_B \<bullet> Rep_ordinal (Abs_ordinal B)}"
    by (auto simp add: image_def Bex_def eind_def)
  also  have "{B | B \<in> CL_B \<bullet> Rep_ordinal (Abs_ordinal B)}
  = 
    CL_B"
  proof (auto simp add: a2 [rule_format])
    fix 
      B 
    assume
      b1: "B \<in> CL_B"
    then have 
      "B = Rep_ordinal (Abs_ordinal B) \<and> B \<in> CL_B"
      by (simp add: a2 [rule_format])
    then show 
      "(\<exists> B' \<bullet> B = Rep_ordinal (Abs_ordinal B') \<and> B' \<in> CL_B)"
      by (auto)
  qed
  finally show 
    ?thesis 
    by (this)
qed

lemma Rolim_conv:
  "Rep_ordinal (\<olim> bb) = olim_Rep { b | b \<in> bb\<bullet>Rep_ordinal b }"
  by (simp add: olim_def, rule olim_ordinalI [THEN Abs_ordinal_inverse])
     (auto intro: Rep_ordinal)

text {*

The way in which @{term ordinal} is constructed ensures that
eventually every element of is chosen to be inserted in an
ordinal representation. In fact there is a least such set in
ordinal.

*}

definition
  oindex :: "'a \<rightarrow> 'a ordinal"
where
  oindex_def: 
    "oindex x \<defs> \<olim> { b | x \<notin> Rep_ordinal b }"

lemma oindex_under: "x \<notin> Rep_ordinal (oindex x)"
  by (auto simp add: Rolim_conv olim_Rep_def oindex_def)
  
lemma ordinal_cover: "x \<in> Rep_ordinal (\<osuc> (oindex x))"
proof -
  let ?Lx = "olim_Rep {B | B \<in> ordinal \<and> x \<notin> B}"
  let ?NLx = "(\<some> y | y \<notin> ?Lx)"
  let ?SLx = "osuc_Rep ?Lx"
  have a1: "x \<notin> ?Lx"
    by (auto simp add: olim_Rep_def)
  have a2: "\<not> ?SLx \<subseteq> ?Lx"
    by (simp add: subset_def Bex_def, rule exI [of _ ?NLx],
      rule conjI, simp add: osuc_Rep_def,
      rule someI, rule a1)
  have a3: "?SLx \<in> ordinal"
    by (rule osuc_ordinalI, rule olim_ordinalI, auto)
  from a2
  have "x \<in> ?SLx"
    by (rule contrapos_np, simp add: a3, auto intro: a3 simp add: a3 olim_Rep_def)
  also have "?SLx = Rep_ordinal (\<osuc> (oindex x))"
    apply (simp add: oindex_def Rolim_conv Rosuc_conv)
    apply (rule arg_cong [of _ _ osuc_Rep])
    apply (rule arg_cong [of _ _ olim_Rep])
    apply (auto simp add: Rep_ordinal ord.Rep_char)
    done
  finally show 
    ?thesis 
    by this
qed

lemma ozero_conv:
  "\<ozero> = Abs_ordinal {}"
  by (simp add: ozero_def olim_def olim_Rep_def)

lemma omax_conv:
  "(\<omax>::'a ordinal) = (Abs_ordinal UNIV)"
proof (simp add: omax_def)
  have 
    "olim UNIV
    = olim (Abs_ordinal\<lparr>ordinal::'a set set\<rparr>)"
    by (simp add: Abs_ordinal_range_char)
  also have "\<dots> 
    = Abs_ordinal (olim_Rep (ordinal::'a set set))"
    by (rule olim_conv, auto)
  also have 
    "olim_Rep (ordinal::'a set set) 
    = UNIV"
    by (auto simp add: olim_Rep_def Bex_def, rule exI, rule conjI,
      rule Rep_ordinal, rule ordinal_cover)
  finally show 
    "olim UNIV = Abs_ordinal (UNIV::'a set)"
    by (this)
qed

lemma Rozero_conv:
  "Rep_ordinal \<ozero> = {}"
  by (simp add: ozero_def Rolim_conv olim_Rep_def)

lemma Romax_conv:
  "Rep_ordinal (\<omax>::'a ordinal) = UNIV"
proof -
  have "Rep_ordinal (\<omax>::'a ordinal) = 
    Rep_ordinal (Abs_ordinal (olim_Rep (range Rep_ordinal)))"
    by (simp add: omax_def olim_def image_def eind_def)
  also have "\<dots> = olim_Rep (range Rep_ordinal)"
    by (rule olim_ordinalI [THEN Abs_ordinal_inverse]) 
      (auto intro: Rep_ordinal)
  also have "\<dots> = UNIV"
    apply (rule set_eqI)
    apply (simp add: olim_Rep_def)
    apply (rule exI)
    apply (rule ordinal_cover)
    done
  finally show 
    ?thesis 
    by (this)
qed

lemma ozero_neq_omax:
  "(ozero::'a ordinal) \<noteq> omax"
  by (simp add: omax_conv ozero_conv,
   rule contrapos_nn [of "(UNIV::'a set) = \<emptyset>"], rule UNIV_not_empty, 
   rule Abs_ordinal_inj [THEN inj_onD])
     (auto simp add: Romax_conv [THEN sym] Rozero_conv [THEN sym] Rep_ordinal)

section {* Cantor's theorem for ordinals *}

text {*

An important fact about the ordinals is that for every type @{typ "'a"} there
is an ordinal type strictly bigger than @{typ "'a"}.

The first step to proving this is to show that there is an injection
from @{typ "'a"} to @{text "'a ordinal"}.

*}

lemma ord_inj:
  "inj (oindex::'a \<rightarrow> 'a ordinal)"
proof (rule inj_onI, simp)
  fix
    x::'a and y
  assume 
    a1: "oindex x = oindex y"
  from oindex_under [of x] ordinal_cover [of x]
  have 
    "x 
    = (\<some> z | z \<notin> Rep_ordinal(oindex x))"
    by (auto simp add: Rolim_conv olim_Rep_def Rosuc_conv osuc_Rep_def)
  also from a1 have "\<dots> 
    = (\<some> z | z \<notin> Rep_ordinal(oindex y))"
    by (simp)
  also from oindex_under [of y] ordinal_cover [of y]
  have "\<dots> 
    = y"
    by (auto simp add: Rolim_conv olim_Rep_def Rosuc_conv osuc_Rep_def)
  finally show 
    "x = y" 
    by this
qed

text {*

Now we observe that if there is an injection from @{text "('a set) ordinal"}
to @{typ "'a"}
that there must also be an injection from @{text "'a set"} to @{typ "'a"}, in
contradiction of Cantor's theorem.

*}

lemma ord_Cantor:
  "\<not>(\<exists>f::('a set)ordinal \<rightarrow> 'a\<bullet>inj f)"
proof (rule notI, elim exE)
  fix f::"('a set)ordinal \<rightarrow> 'a"
  assume a1: "inj f"
  from ord_inj a1 have "inj (f \<circ> oindex)" by (rule comp_inj)
  thus "\<False>" by (rule exI [THEN Cantor_cor [THEN notE]])
qed

lemma ord_Cantor2:
  "\<not> inj (f::('a set)ordinal \<rightarrow> 'a)"
  by (insert ord_Cantor, auto)

section {* The ordinal well-order *}

text {*

The order on the ordinals is that induced by the subset order on its
set representation.

*}

instantiation
  ordinal :: (type) "ord"
begin

definition
  ole_def: "a \<le> b \<defs> Rep_ordinal a \<subseteq> Rep_ordinal b"

definition
  olt_def: "a < b \<defs> Rep_ordinal a \<subset> Rep_ordinal b"

instance
  by (intro_classes)

end

instance
  ordinal :: (type) "order"
  apply (intro_classes)
  apply (unfold ole_def olt_def)
proof -
  fix A show 
    "Rep_ordinal A \<subseteq> Rep_ordinal A"
    by (auto)
next
  fix A B C
  assume 
    b1: "Rep_ordinal A \<subseteq> Rep_ordinal B" and
    b2: "Rep_ordinal B \<subseteq> Rep_ordinal C"
  then show 
    "Rep_ordinal A \<subseteq> Rep_ordinal C"
    by (auto)
next
  fix A B 
  assume 
    b1: "Rep_ordinal A \<subseteq> Rep_ordinal B" and
    b2: "Rep_ordinal B \<subseteq> Rep_ordinal A"
  then have "Rep_ordinal A = Rep_ordinal B" 
    by (rule equalityI)
  then show "A = B"
    by (simp add: ord.Rep_inject)
next
  fix A B 
  have 
    "Rep_ordinal A \<subset> Rep_ordinal B
    \<Leftrightarrow> Rep_ordinal A \<subseteq> Rep_ordinal B \<and> Rep_ordinal A \<noteq> Rep_ordinal B"
    by (simp add: order_less_le)
  also have "\<dots>
    \<Leftrightarrow> Rep_ordinal A \<subseteq> Rep_ordinal B \<and> \<not> (Rep_ordinal B \<subseteq> Rep_ordinal A)"
    by (mauto(wind))
(*    apply (simp add: ord.Rep_inject, auto) 
    done
*)
  finally show 
    "Rep_ordinal A < Rep_ordinal B
    \<Leftrightarrow> Rep_ordinal A \<subseteq> Rep_ordinal B \<and> \<not> (Rep_ordinal B \<subseteq> Rep_ordinal A)"
    by (this)  
qed

text {*

We need a few structural lemmas on the ordinal order.

*}

lemma ozero_lb:
  "\<ozero> \<le> b"
  by (simp add: ole_def Rozero_conv)

lemma ozero_eq:
  "a \<le> \<ozero> \<Leftrightarrow> a = \<ozero>"
  by (auto intro: order_antisym ozero_lb)

lemma ozero_bot:
  "\<not>(a < \<ozero>)"
  by (simp add: olt_def Rozero_conv)

lemma nonzero_conv:
  "(\<ozero> < a) = (a \<noteq> \<ozero>)"
  by (insert ozero_lb [of a], auto simp add: order_less_le)

lemma nonzeroI:
  assumes
    a1: "b < a"
  shows
    "a \<noteq> \<ozero>"
  using a1
  by (auto simp add: ozero_bot)

lemma zero_cases [case_names zero nonzero]:
  "\<lbrakk> \<ozero> = a \<turnstile> R;  \<ozero> < a \<turnstile> R \<rbrakk> \<turnstile> R"
  by (rule disjE, rule ozero_lb [unfolded order_le_less 
    [THEN eq_reflection]], auto)

lemma omax_ub:
  "b \<le> \<omax>"
  by (simp add: ole_def Romax_conv)

lemma omax_eq:
  "\<omax> \<le> a \<Leftrightarrow> a = \<omax>"
  by (auto intro: order_antisym omax_ub)

lemma omax_top:
  "\<not>(\<omax> < a)"
  by (auto simp add: olt_def Romax_conv)

lemma nonmax_conv:
  "a < \<omax> \<Leftrightarrow> a \<noteq> \<omax>"
  by (insert omax_ub [of a], auto simp add: order_less_le)

lemma nonmaxI:
  assumes
    a1: "a < b"
  shows
    "a \<noteq> \<omax>"
  using a1
  by (auto simp add: omax_top)

lemma max_cases [case_names nonmax max]:
  "\<lbrakk> a < \<omax> \<turnstile> R;  a = \<omax> \<turnstile> R \<rbrakk> \<turnstile> R"
  by (rule disjE, rule omax_ub [unfolded order_le_less 
    [THEN eq_reflection]], auto)

lemmas nonzero_omax = ozero_neq_omax

lemma nonzero_omax':
  "\<ozero> < \<omax>"
  apply (simp add: nonzero_conv)
  apply (subst Rep_ordinal_inject [symmetric])
  apply (simp add: Romax_conv Rozero_conv)
  done

text {*

The linearity of the ordinals depends on the fact that there
are not ordinal representations between the representations 
of an ordinal and its successor.

*}

lemma pre_osuc_char:
   "\<lbrakk> B \<in> ordinal; (\<And> C \<bullet> C \<in> ordinal \<turnstile> C \<subseteq> B \<or> B \<subseteq> C) \<rbrakk>
     \<turnstile> { C | C \<in> ordinal \<and> (C \<subseteq> B \<or> osuc_Rep B \<subseteq> C) } = ordinal"
proof -
  assume 
    a: "B \<in> ordinal" and
    b: "(\<And> C \<bullet> C \<in> ordinal \<turnstile> C \<subseteq> B \<or> B \<subseteq> C)"
  let 
    ?ORD = "{ C | C \<in> ordinal \<and> (C \<subseteq> B \<or> osuc_Rep B \<subseteq> C) }" and
    ?OSI = "(\<olambda> CL_B::('a set) set \<bullet> (\<forall> B \<bullet> B \<in> CL_B \<Rightarrow> osuc_Rep B \<in> CL_B))" and
    ?OLI = "(\<olambda> CL_B::('a set) set \<bullet> (\<forall> CL_C \<bullet> CL_C \<subseteq> CL_B \<Rightarrow> olim_Rep CL_C \<in> CL_B))"
  have sb: "?OSI ?ORD"
  proof (rule allI, rule impI)
    fix C::"'a set" 
    assume 
      co: "C \<in> ?ORD"
    have 
      x1: "C \<in> ordinal"
      by (rule co [THEN [2] mp]) (simp)
    have 
      x2: "(C \<subset> B \<or> C = B \<or> osuc_Rep B \<subseteq> C)"
      by (rule co [THEN [2] mp]) (simp add: order_le_less)
    have 
      x3: "osuc_Rep C \<subseteq> B \<or> B \<subset> osuc_Rep C"
      by (insert x1 [THEN osuc_ordinalI [THEN b]], simp add: order_le_less,
        elim disjE, auto)
    show 
      "osuc_Rep C \<in> ?ORD"
    proof (simp, rule conjI)
      show
        "osuc_Rep C \<in> ordinal"
        by (rule osuc_ordinalI) (rule x1)
      show 
        "osuc_Rep C \<subseteq> B \<or> osuc_Rep B \<subseteq> osuc_Rep C" (is ?A)
      proof (rule x2 [THEN [2] mp], rule impI, elim disjE)
        assume 
          y1: "C \<subset> B"
        show 
          "?A"
        proof (rule disjI1, rule x3 [THEN [2] mp], rule impI, elim disjE)
          assume 
            "osuc_Rep C \<subseteq> B"
          then show 
            "osuc_Rep C \<subseteq> B" 
            by (this)
        next
          assume 
            y2: "B \<subset> osuc_Rep C"
          then have
            y3: "B \<subseteq> osuc_Rep C \<and> B \<noteq> osuc_Rep C"
            by (simp add: less_le)
          show 
            "osuc_Rep C \<subseteq> B"
          proof (rule notE [of "B = osuc_Rep C"])
            show 
              "B \<noteq> osuc_Rep C"
              by (rule y3 [THEN conjunct2])
            show 
              "B = osuc_Rep C"
            proof (rule subset_antisym, rule y3 [THEN conjunct1],
              auto simp add: subset_def osuc_Rep_def)
              let 
                ?X = "(\<some> x | x \<notin> C)" and
                ?Y = "(\<some> y | y \<in> B \<and> y \<notin> C)"
              have 
                z1: "?Y \<in> B \<and> ?Y \<notin> C"
                by (rule some_eq_ex [THEN iffD2])
                  (rule y1 [THEN psubset_neq])
              have 
                z2: "?Y \<in> osuc_Rep C"
                by (rule y2 [THEN psubset_imp_subset [THEN subsetD]])
                  (rule z1 [THEN conjunct1])
              have 
                z3:
                  "\<And> y \<bullet> 
                    \<lbrakk> y \<in> osuc_Rep C; y \<notin> C \<rbrakk>
                    \<turnstile> ?X = y"
                by (simp add: osuc_Rep_def)
              have 
                z4: "?X = ?Y"
                by (rule z2 [THEN z3]) (rule z1 [THEN conjunct2])
              then show 
                "?X \<in> B"
                by (simp) (rule z1 [THEN conjunct1])
            next
              fix
                x 
              assume
                g1: "x \<in> C"
              with y1 show "x \<in> B" 
                by (auto)
            qed
          qed
        qed
      next
        assume 
          "C = B" 
        then show 
          "?A" 
          by (simp)
      next
        assume 
          d1: "osuc_Rep B \<subseteq> C"
        then show 
          "?A"
          apply (intro disjI2)
          apply (rule order_trans [OF d1])
          apply (auto simp add: osuc_Rep_def)
          done
      qed
    qed
  qed
  have 
    lb: "?OLI ?ORD"
  proof (rule allI, rule impI)
    fix 
      CL_C::"('a set)set" 
    assume 
      y1: "CL_C \<subseteq> ?ORD"
    have 
      y2: "\<forall> C | C \<in> CL_C \<bullet> C \<in> ordinal"
      by (rule y1 [THEN [2] mp], simp add: subset_def)
    have 
      y3 : 
        "(\<forall> C | C \<in> CL_C \<bullet> C \<subseteq> B) \<or>
        (\<exists> C \<bullet> C \<in> CL_C \<and> osuc_Rep B \<subseteq> C)"
    proof (rule disjCI, simp, rule allI, rule impI, elim allE,
      elim impE, assumption)
      fix
        C::"'a set"
      assume 
        x: "C \<in> CL_C" "\<not> osuc_Rep B \<subseteq> C"
      have 
        y: "C \<subseteq> B \<or> osuc_Rep B \<subseteq> C"
        by (rule y1 [THEN [2] mp], rule impI,
          simp add: subset_def Ball_def, elim allE [of _ C])
          (simp add: x)
      show 
        "C \<subseteq> B"
        by (rule y [THEN [2] mp], simp add: x)
    qed
    show 
      "olim_Rep CL_C \<in> ?ORD"
    proof (rule CollectI, rule conjI)
      show 
        "olim_Rep CL_C \<in> ordinal"
        by (rule olim_ordinalI) (rule y2 [folded Ball_def subset_eq])
      show 
        "olim_Rep CL_C \<subseteq> B \<or> osuc_Rep B \<subseteq> olim_Rep CL_C"
        (is "?X \<or> ?Y")
      proof (rule y3 [THEN [2] mp], rule impI, elim disjE)
        assume 
          x: "\<forall> C \<bullet> C \<in> CL_C \<Rightarrow> C \<subseteq> B"
        show 
          "?X \<or> ?Y"
          by (rule disjI1, rule x [THEN [2] mp], rule impI)
            (simp add: olim_Rep_def Union_eq subset_def, auto)
      next
        assume 
          x: "(\<exists> C \<bullet> C \<in> CL_C \<and> osuc_Rep B \<subseteq> C)"
        show 
          "?X \<or> ?Y"
          by (rule disjI2, rule x [THEN [2] mp], rule impI)
            (simp add: olim_Rep_def Union_eq subset_def, auto)
      qed
    qed
  qed
  have
    x: "?ORD \<subseteq> ordinal"
    by (simp add: subset_def)
  show 
    "?ORD = ordinal"
    by (rule x [THEN lb [THEN sb [THEN ord_char_eq]]])
qed

text {*

The ordinals are linear.

*}

instance 
    ordinal :: (type) "linorder"
proof (intro_classes)
  let 
    ?OSI = "\<olambda>CL_B::('a set) set\<bullet>\<forall>B\<bullet>B \<in> CL_B \<Rightarrow> osuc_Rep B \<in> CL_B" and
    ?OLI = "\<olambda>CL_B::('a set) set\<bullet>\<forall>CL_C\<bullet>CL_C \<subseteq> CL_B \<Rightarrow> olim_Rep CL_C \<in> CL_B" and
    ?LIN = "{B::'a set|B \<in> ordinal \<and> (\<forall>C\<bullet>C \<in> ordinal \<Rightarrow> C \<subseteq> B \<or> B \<subseteq> C)}" and 
    ?ORD = "\<olambda>B::'a set\<bullet>{C|C \<in> ordinal \<and> (C \<subseteq> B \<or> osuc_Rep B \<subseteq> C)}"
  have 
    a: "?OSI ?LIN"
  proof (rule allI, rule impI)
    fix 
      B::"'a set" 
    assume 
      aa: "B \<in> ?LIN"
    have 
      aaa: "B \<in> ordinal"
      by (rule aa [THEN [2] mp]) (simp)
    have 
      aab: "\<And> C \<bullet> C \<in> ordinal \<turnstile> C \<subseteq> B \<or> B \<subseteq> C"
      by (rule aa [THEN [2] mp], simp add: order_le_less)
    have 
      ae: "?ORD B = ordinal"
      by (rule aaa [THEN pre_osuc_char], rule aab, assumption)
    show 
      "osuc_Rep B \<in> ?LIN"
    proof (rule CollectI, rule conjI, rule aaa [THEN osuc_ordinalI], 
      rule allI, rule impI)
      fix 
        C::"'a set" 
      assume 
        x: "C \<in> ordinal"
      then have 
        y: "C \<in> ?ORD B" 
        by (simp add: ae)
      have 
        z: "C \<subseteq> B \<or> osuc_Rep B \<subseteq> C"
        by (rule conjunct2) (rule y [THEN CollectD])
      show 
        "C \<subseteq> osuc_Rep B \<or> osuc_Rep B \<subseteq> C" (is "?X")
      proof (rule z [THEN [2] mp], rule impI, elim disjE)
        assume 
          x: "C \<subseteq> B" 
        show 
          "?X"
          by (rule disjI1, rule x [THEN subset_trans]) 
            (simp add: osuc_Rep_def subset_def)
      next
        assume 
          "osuc_Rep B \<subseteq> C" 
        then show 
          "?X" 
          by (simp)
      qed
    qed
  qed
  have 
    b: "?OLI ?LIN"
  proof (rule allI, rule impI, rule CollectI, rule conjI)
    fix
      CL_C::"('a set)set" 
    assume 
      x: "CL_C \<subseteq> ?LIN"
    show 
      "olim_Rep CL_C \<in> ordinal"
      by (rule olim_ordinalI, rule x [THEN [2] mp], simp add: subset_def)
    show 
      "(\<forall> B \<bullet> B \<in> ordinal \<Rightarrow> B \<subseteq> olim_Rep CL_C \<or> olim_Rep CL_C \<subseteq> B)"
    proof (rule allI, rule impI)
      fix 
        B::"'a set" 
      assume 
        y: "B \<in> ordinal"
      have 
        ba: 
         "(\<forall> C | C \<in> CL_C \<bullet> C \<subseteq> B) \<or>
          (\<exists> C | C \<in> CL_C \<bullet> B \<subseteq> C)"
      proof (rule disjCI, simp, rule allI, rule impI, elim allE, 
        elim impE, assumption)
        fix 
          C::"'a set"
        assume 
          z1: "C \<in> CL_C" and
          z2: "\<not> B \<subseteq> C"
        have 
          baa: "C \<subseteq> B \<or> B \<subseteq> C"
          by (insert z1 [THEN x [THEN subsetD [THEN CollectD]]],
            elim conjE, elim allE [of _ B], elim impE, rule y)
            (force)
        show 
          "C \<subseteq> B"
        proof (insert baa, elim disjE)
          assume 
            "C \<subseteq> B"
          then show 
            "C \<subseteq> B" 
            by (auto)
        next
          assume 
            z3: "B \<subseteq> C" 
          show 
           "C \<subseteq> B"
            by (rule z3 [THEN contrapos_pp]) (rule z2)
        qed
      qed
      show 
        "B \<subseteq> olim_Rep CL_C \<or> olim_Rep CL_C \<subseteq> B" (is "?X")
      proof (insert ba, elim disjE)
        assume 
          bx: "\<forall>C|C \<in> CL_C \<bullet> C \<subseteq> B"
        show 
          "?X"
        proof (rule disjI2, 
          auto simp add: olim_Rep_def Union_eq subset_def)
          fix 
            x::"'a" and
            C::"'a set"
          assume 
            by1: "C \<in> CL_C" and 
            by2: "x \<in> C"
          show 
            "x \<in> B"
            by (insert bx [THEN spec [of _ C]], elim impE, rule by1,
              rule by2 [THEN [2] subsetD])(assumption)
        qed
      next
        assume 
          bx: "(\<exists> C \<bullet> C \<in> CL_C \<and> B \<subseteq> C)"
        show 
          "?X"
          by (rule disjI1, insert bx, elim exE) 
            (auto simp add: olim_Rep_def Union_eq subset_def)
      qed
    qed
  qed
  have 
    c: "?LIN \<subseteq> ordinal" 
    by (simp add: subset_def)
  have 
    d: "?LIN = ordinal" 
    by (rule c [THEN b [THEN a [THEN ord_char_eq]]])
  fix 
    x::"'a ordinal" and 
    y::"'a ordinal"
  let 
    ?X = "Rep_ordinal x" and 
    ?Y = "Rep_ordinal y"
  show 
    "x \<le> y \<or> y \<le> x"
  proof (simp add: ole_def)
    have 
      xa: "?Y \<in> ?LIN"
      by (simp add: d) (rule Rep_ordinal)
    have
      xb: "(\<forall> x | x \<in> ordinal \<bullet> x \<subseteq> ?Y \<or> ?Y \<subseteq> x)"
      by (rule conjunct2) (rule xa [THEN CollectD])
    show 
      "?X \<subseteq> ?Y \<or> ?Y \<subseteq> ?X"
      by (insert xb [THEN spec [of _ "?X"]], elim impE)
       (auto intro: Rep_ordinal)
  qed
qed

instantiation 
  ordinal :: (type) lat
begin

definition
  inf_ordinal_def: "(op &&) \<defs> (\<olambda> (x::'a ordinal) y \<bullet> \<if> x \<le> y \<then> x \<else> y \<fi>)"

definition
  sup_ordinal_def: "(op ||) \<defs> (\<olambda> (x::'a ordinal) y \<bullet> \<if> x \<le> y \<then> y \<else> x \<fi>)"

instance
  by (intro_classes)

end

instance 
  ordinal :: (type) linlat
  apply (intro_classes)
  apply (auto simp add: inf_ordinal_def sup_ordinal_def)
  done

text {*

We finish this section with some more structural results about the
ordinal order.

The linearity of the ordinals gives a useful corollary to
Cantor's theorem.

*}

lemma ord_Cantor_cor:
  fixes
    f::"'a set ordinal \<rightarrow> 'a"
  shows
    "(\<exists> a b \<bullet> a < b \<and> f a = f b)"
proof (insert ord_Cantor2 [THEN ninj_onD [of "f"]], auto)
  fix 
    a::"'a set ordinal" and 
    b::"'a set ordinal"
  assume 
    a1: "f a = f b" and 
    a2: "a \<noteq> b"
  have 
    a3: "a < b \<or> b < a"
    by (insert linorder_less_linear [of a b], auto simp add: a2)
  show 
    "(\<exists> a b \<bullet> a < b \<and> f a = f b)"
  proof (cases rule: a3 [THEN disjE])
    assume 
      b1: "a < b"
    show 
      "(\<exists> a b \<bullet> a < b \<and> f a = f b)"
      by (rule exI [of _ a], rule exI [of _ b], simp add: b1 a1)
  next
    assume 
      b1: "b < a"
    show 
      "(\<exists> a b \<bullet> a < b \<and> f a = f b)"
      by (rule exI [of _ b], rule exI [of _ a], simp add: b1 a1)
  qed
qed

text {*

There are no ordinals between an ordinal and its successor.

*}

lemma osuc_char:
  fixes
    b::"'a ordinal" and
    c::"'a ordinal"
  assumes
    a1: "(c::'a ordinal) < b"
  shows
    "\<osuc> c \<le> b"
proof -
  let 
    ?B = "Rep_ordinal b" and
    ?C = "Rep_ordinal c"
  let 
    ?Sc = "\<osuc> c" and
    ?SC = "osuc_Rep ?C"
  have 
    a: "Rep_ordinal ?Sc = ?SC"
    by (simp add: osuc_def 
      Rep_ordinal [THEN osuc_ordinalI [THEN Abs_ordinal_inverse]])
  have 
    b: "{ A | A : ordinal & (A <= ?C \<or> osuc_Rep ?C <= A) } = ordinal"
  proof (rule pre_osuc_char, rule Rep_ordinal)
    fix 
      A::"'a set"
    assume 
      ao: "A \<in> ordinal"
    let 
      ?CL_A = "Abs_ordinal A"
    have 
      x: "?CL_A \<le> c \<or> c \<le> ?CL_A"
      by (rule linorder_linear)
    show 
      "A \<subseteq> ?C \<or> ?C \<subseteq> A"
      by (insert x, simp add: ole_def ao [THEN Abs_ordinal_inverse])
  qed
  have 
    c: "\<And> A \<bullet> A \<in> ordinal \<turnstile> (A \<subseteq> ?C \<or> osuc_Rep ?C \<subseteq> A)"
    by (rule conjunct2, rule b [THEN equalityD2 [THEN subsetD [THEN CollectD]]],
      assumption)
  have 
    d: "\<not> c < b \<or> \<osuc> c \<le> b"
    by (simp add: linorder_not_less osuc_def ole_def
      Rep_ordinal [THEN osuc_ordinalI [THEN Abs_ordinal_inverse]], 
      rule c, rule Rep_ordinal)
  show 
    "\<osuc> c <= b"
    by (insert d, elim disjE, elim notE, rule a1, assumption)
qed

lemma osuc_char2:
  fixes
    b::"'a ordinal" and
    c::"'a ordinal"
  assumes
    a1: "(c::'a ordinal) < \<osuc> b"
  shows 
    "c \<le> b"
  using a1
  by (rule contrapos_pp)
     (simp only: linorder_not_less linorder_not_le, rule osuc_char)

text {*

The successor function is strictly increasing, except at @{term "\<omax>"}.

*}

lemma osuc_nondec:
  "b \<le> \<osuc> b"
  by (simp add: ole_def Rosuc_conv osuc_Rep_def) (auto)

lemma osuc_omax:
  "\<osuc> \<omax> = \<omax>"
  by (rule order_antisym, rule omax_ub, rule osuc_nondec)

lemma osuc_idem_char:
  "\<osuc> a = a \<Leftrightarrow> a = \<omax>"
  apply (simp add: osuc_def ord.Abs_connect_on osuc_ordinalI Rep_ordinal)
  apply (auto simp add: osuc_Rep_def Romax_conv)
  apply (rule ord.Rep_eqI)
  apply (simp add: Romax_conv)
  apply (rule contrapos_pp, assumption)
proof - 
  assume 
    "Rep_ordinal a \<noteq> \<univ>"
  then have 
    "(\<exists> x \<bullet> x \<notin> Rep_ordinal a)"
    by (auto)
  then have 
    "(\<some> y | y \<notin> Rep_ordinal a) \<notin> Rep_ordinal a"
    by (rule someI_ex)
  then show 
    "insert (\<some> y | y \<notin> Rep_ordinal a) (Rep_ordinal a) \<noteq> Rep_ordinal a"
    by (auto)
qed

lemma osuc_incr:
  assumes 
    a1: "a \<noteq> \<omax>"
  shows 
    "a < \<osuc> a"
proof -
  let 
    ?A = "Rep_ordinal a" 
  let
    ?NA = "\<some> y | y \<notin> ?A"
  have 
    a2: "?NA \<notin> ?A"
    apply (simp add: some_eq_ex [of "(\<olambda> x \<bullet> x \<notin> ?A)"])
    apply (rule a1 [THEN contrapos_pp]) 
    apply (auto simp add: omax_def olim_def olim_Rep_def eind_norm [of "(\<olambda> x \<bullet> Union (Collect x))"])
  proof -
    assume 
      b1: "\<forall> y \<bullet> y \<in> ?A"
    let 
      ?X = "(\<Union> n \<bullet> Rep_ordinal n)"
    have 
      "?A 
      = UNIV"
      by (auto) (rule b1 [THEN allE])
    also have "\<dots> 
      = ?X"
      by (rule subset_UNIV [THEN [2] subset_antisym], simp add: subset_def, 
        rule allI, rule exI [of _ a], rule b1 [rule_format])
    finally have 
      b2: "?A = ?X"
      by (this)  
    have 
      "a 
      = Abs_ordinal (?A)"
      by (rule Rep_ordinal_inverse [THEN sym])
    also have "\<dots> 
      = Abs_ordinal ?X"
      by (rule b2 [THEN arg_cong])
    finally show 
      "a = Abs_ordinal ?X"
      by (this)
  qed
  have 
    a3: "?A \<subset> osuc_Rep ?A"
    proof (rule psubsetI_wit [of "?NA"])
      show 
        "?NA \<in> osuc_Rep ?A" 
        by (simp add: osuc_Rep_def)
      show 
        "?NA \<notin> ?A" 
        by (rule a2)
      show 
        "?A \<subseteq> osuc_Rep ?A"
        by (auto simp add: osuc_Rep_def)
    qed
  show 
    "a < \<osuc> a"
    by (simp add: olt_def osuc_def Rep_ordinal 
      [THEN osuc_ordinalI [THEN Abs_ordinal_inverse]])
      (rule a3)
qed

lemma osuc_mono:
  assumes 
    a1: "b \<noteq> \<omax>" and 
    a2: "c < b"
  shows 
    "\<osuc> c < \<osuc> b"
proof -
  from a2 have b1: 
    "\<osuc> c
    \<le> b"
    by (rule osuc_char)
  also from a1 have "\<dots> 
    < \<osuc> b"
    by (rule osuc_incr)
  finally show 
    "\<osuc> c < \<osuc> b"
    by (this)
qed

lemma osuc_less_le:
  "a \<noteq> \<omax> \<turnstile> (b < \<osuc> a) = (b \<le> a)"
  by (rule osuc_char2 [THEN iffI], assumption)
    (rule osuc_incr [THEN [2] order_le_less_trans], auto)

lemma ozero_less_osuc:
  "\<ozero> < \<osuc> b"
  apply (cases "\<ozero> = b")
  apply (simp add: osuc_incr [OF ozero_neq_omax])
  apply (rule less_le_trans [OF _ osuc_nondec])
  apply (simp add: nonzero_conv)
  done

lemma dist_osuc:
  assumes
    a1: "\<osuc> a = \<osuc> b" and
    a2: "a \<noteq> \<omax>" and 
    a3: "b \<noteq> \<omax>"
  shows
    "a = b"
proof (rule a1 [THEN contrapos_pp], simp add: linorder_neq_iff, elim disjE)
  assume 
    b1: "a < b"
  then have 
    b2: "\<osuc> a \<le> b"
    by (rule osuc_char)
  show 
    "\<osuc> a < \<osuc> b \<or> \<osuc> b < \<osuc> a"
    by (rule disjI1) 
      (rule a3 [THEN osuc_incr [THEN b2 [THEN order_le_less_trans]]])
next
  assume 
    b1: "b < a"
  then have 
    b2: "\<osuc> b \<le> a" 
    by (rule osuc_char)
  show 
    "\<osuc> a < \<osuc> b \<or> \<osuc> b < \<osuc> a"
    by (rule disjI2) 
       (rule a2 [THEN osuc_incr [THEN b2 [THEN order_le_less_trans]]])
qed


text {*

Each ordinal is either a successor or a limit ordinal.

*}

lemma ord_min:
  "(\<exists> c \<bullet> b = \<osuc> c) \<or> (\<exists> cc \<bullet> b = \<olim> cc)"
proof -
  have 
    a: "b = \<olim> {b}"
    by (simp add: osuc_def olim_def osuc_Rep_def olim_Rep_def
      Rep_ordinal_inverse)
  then have 
    "(\<exists> cc \<bullet> b = \<olim> cc)"
    by (witness "{b}")
  then show 
    ?thesis 
    by (rule)
qed

text {*

Limit ordinals are lubs.

*}

lemma olim_char:
  "b \<in> bb \<turnstile> b \<le> \<olim> bb"
  by (auto simp add: ole_def Rolim_conv olim_Rep_def)

lemma olim_min:
  "(\<forall> b | b \<in> bb \<bullet> b \<le> x) \<turnstile> \<olim> bb \<le> x"
  by (auto simp add: ole_def Rolim_conv olim_Rep_def)

lemma olim_eq:
  assumes 
    a1: "(\<And> b \<bullet> b \<in> bb \<turnstile> b \<le> x)" and 
    a2: "(\<And> y \<bullet> (\<forall> b | b \<in> bb \<bullet> b \<le> y) \<turnstile> x \<le> y)"
  shows 
    "olim bb = x"
  apply (rule order_antisym)
  apply (rule olim_min)
  apply (msafe_no_assms(inference))
  apply (rule a1)
  apply (assumption)
  apply (rule a2)
  apply (auto intro: olim_char)
  done

text {*

A limit ordinal is an ordinal which is the limit of all the ordinals
below it.
Every ordinal is either a limit or a successor.
Only @{term "\<omax>"} can be both, and if
@{term "\<omax>"} is a limit, then
it is only a successor of itself.

*}

definition
  is_limit :: "'a ordinal \<rightarrow> bool"
where
  is_limit_def: "is_limit b \<defs> b = \<olim> { c | c < b }"

lemma is_limit_ozero:
  "is_limit \<ozero>"
  apply (simp add: is_limit_def ozero_def)
  apply (rule arg_cong [of _ _ "\<olim>"])
  apply (fold ozero_def)
  apply (insert ozero_lb)
  apply (auto simp only: linorder_not_le [THEN sym])
  done

lemma limit_suc_disj:
  "(a::'a ordinal) \<noteq> \<omax> \<turnstile> (is_limit a = (\<forall> b \<bullet> a \<noteq> \<osuc> b))"
proof (auto)
  fix b::"'a ordinal"
  assume 
    nsbm: "\<osuc> b \<noteq> \<omax>" and
    sbl: "is_limit(\<osuc> b)"
  let 
    ?B = "Rep_ordinal b"
  let 
    ?NB = "\<some> y | y \<notin> ?B"
  have 
    ob: "?B \<in> ordinal" 
    by (rule Rep_ordinal)
  then have 
    osb: "osuc_Rep ?B \<in> ordinal" 
    by (rule osuc_ordinalI)
  have 
    ol: "olim_Rep {n | n < \<osuc> b \<bullet> Rep_ordinal n} \<in> ordinal"
    by (rule olim_ordinalI) (auto simp add: subset_def Rep_ordinal)
  have 
    aa: "?NB \<notin> ?B"
    by (rule some_eq_ex [THEN iffD2], rule contrapos_pp, rule nsbm, 
      simp add: omax_conv osuc_def osuc_Rep_def
      olim_def olim_Rep_def,
      rule arg_cong [of _ _ "Abs_ordinal"], rule set_eqI, simp)
  have 
    "osuc_Rep ?B 
    = Rep_ordinal (\<osuc> b)"
    by (simp add: osuc_def osb [THEN Abs_ordinal_inverse])
  also have "\<dots> 
    = Rep_ordinal (\<olim> { C | C < \<osuc> b })"
    by (rule arg_cong [of _ _ "Rep_ordinal"])
      (rule sbl [unfolded is_limit_def])
  also have "\<dots> 
    = olim_Rep { C | C \<in> ordinal \<and> C \<subseteq> ?B }"
  proof (simp add: olim_def ol [THEN Abs_ordinal_inverse],
    rule arg_cong [of _ _ "olim_Rep"], rule Collect_cong, rule iffI,
    simp add: olt_def  osuc_def osb [THEN Abs_ordinal_inverse] Rep_ordinal,
    elim exE, elim conjE, simp add: Rep_ordinal)
    fix 
      C::"'a set" and 
      n::"'a ordinal"
    let 
      ?N = "Rep_ordinal n"
    assume 
      x1: "C = ?N" and
      x2: "?N \<subset> osuc_Rep ?B"
    have 
      x3: "?N \<subseteq> ?B \<or> ?B \<subseteq> ?N"
      by (insert linorder_linear [of n b], simp add: ole_def)
    show 
      "?N \<subseteq> ?B"
      by (insert x3, elim disjE, assumption) 
        (insert x2, 
        auto simp add: osuc_Rep_def psubset_eq Ball_def)
  next
    apply_end (simp)
    fix 
      C::"'a set"
    assume 
      x: "C \<in> ordinal \<and> C \<subseteq> ?B"
    show 
      "(\<exists> n \<bullet> C = Rep_ordinal n \<and> n < \<osuc> b)"
      by (rule exI [of _ "Abs_ordinal C"], 
        simp add: x [THEN conjunct1 [THEN Abs_ordinal_inverse]] 
        olt_def osuc_def osb [THEN Abs_ordinal_inverse],
        rule x [THEN conjunct2 [THEN subset_psubset_trans]], 
        rule aa [THEN [2] psubsetI_wit])
        (auto simp add: osuc_Rep_def subset_def)
  qed
  finally have 
    ab1:"osuc_Rep ?B = olim_Rep { C | C \<in> ordinal \<and> C \<subseteq> ?B}"
    by (this)
  have 
    ab: "?NB \<in> ?B"
    by (insert ab1 [THEN equalityD1]) 
      (auto simp add: osuc_Rep_def olim_Rep_def)
  show
    "\<False>"
    by (rule ab [THEN aa [THEN notE]])
next
  assume 
    am: "a \<noteq> \<omax>" and 
    nas: "(\<forall> b \<bullet> a \<noteq> \<osuc> b)"
  show 
    "is_limit a"
  proof (simp add: is_limit_def)
    let 
      ?La = "\<olim> { c | c < a }" and
      ?A = "Rep_ordinal a"
    let 
      ?LA = "olim_Rep { C | C \<in> ordinal \<and> C \<subset> ?A }"
    let 
      ?NA = "(\<some> y | y \<notin> ?A)" and
      ?NLA = "(\<some> y | y \<notin> ?LA)"
    have 
      x1: "?LA \<in> ordinal"
      by (rule olim_ordinalI) (auto simp add: subset_def)
    have 
      x2: "osuc_Rep ?LA \<in> ordinal"
      by (rule x1 [THEN osuc_ordinalI])
    have 
      x3: "olim_Rep { n | n < a \<bullet> Rep_ordinal n } \<in> ordinal"
      by (rule olim_ordinalI) (auto simp add: subset_def Rep_ordinal)
    have 
      x4: "Rep_ordinal ?La = ?LA"
      apply (simp add: olim_def x3 [THEN Abs_ordinal_inverse])
      apply (rule arg_cong [of _ _ olim_Rep])
      apply (rule Collect_cong)
      apply (msafe_no_assms(inference))
      apply (simp_all add: Rep_ordinal olt_def)
      apply (fast intro: Rep_ordinal)
      apply (fast)
    proof -
      fix 
        x::"'a set"
      assume 
        y1: "x \<in> ordinal" and
        y2: "x \<subset> ?A"
      show 
        "(\<exists> n \<bullet> x = Rep_ordinal n \<and> Rep_ordinal n \<subset> ?A)"
        by (rule exI [of _ "Abs_ordinal x"], 
            simp add: y1 [THEN  Abs_ordinal_inverse]) (rule y2)
    qed
    have 
      x5: "?LA \<subseteq> ?A"
      by (auto simp add: subset_def psubset_eq olim_Rep_def)
    have 
      x6: "osuc_Rep ?LA \<noteq> ?LA"
    proof (rule notI, rule notE [of "?NLA \<in> ?LA"])
      assume 
        "osuc_Rep ?LA = ?LA"
      then have 
        y1: "osuc_Rep ?LA \<subseteq> ?LA"
        by (rule equalityD1)
      show 
        "?NLA \<notin> ?LA"
      proof (rule someI [of _ "?NA"],
             rule someI2 [of "\<olambda> a \<bullet> a \<notin> ?A" ?NA])
        show 
          "?NA \<notin> ?A"
        proof (simp add: some_eq_ex [of "\<olambda>a\<bullet>a \<notin> ?A"],
               rule am [THEN contrapos_pp], simp)
          assume 
            y2: "\<forall> y \<bullet> y \<in> ?A"
          have 
            "a
            = Abs_ordinal ?A" 
            by (rule Rep_ordinal_inverse [THEN sym])
          also have "\<dots> 
            = Abs_ordinal UNIV"
            by (insert y2)  
               (rule arg_cong [of _ _ "Abs_ordinal"], auto)
          also have "\<dots>
            = \<omax>" 
            by (rule omax_conv [THEN sym])
          finally show 
            "a = \<omax>" 
            by (this)
        qed
        fix 
          x::'a
        assume 
          y3: "x \<notin> ?A"
        show 
          "x \<notin> ?LA"
          by (rule y3 [THEN contrapos_nn], insert x5, 
            auto simp add: subset_def Ball_def)
      qed
      show  
        "?NLA \<in> ?LA"
        by (insert y1)
           (auto simp add: osuc_Rep_def subset_def Ball_def)
    qed
    have 
      a: "a \<le> \<osuc> ?La"
    proof (simp del: linorder_not_less add: linorder_not_less [THEN sym] osuc_def x4,
           simp add: x1 [THEN Abs_ordinal_inverse] 
           x2 [THEN Abs_ordinal_inverse] 
           olt_def olim_def,
           rule x6 [THEN contrapos_nn])
      assume 
        y1: "osuc_Rep ?LA \<subset> ?A"
      have 
        y2: "osuc_Rep ?LA \<in> { C | C \<in> ordinal \<and> C \<subset> ?A}"
        by (rule CollectI) (rule y1 [THEN x2 [THEN conjI]])
      show 
        "osuc_Rep ?LA = ?LA"
      proof (rule subset_antisym)
        have 
          y3: "\<And> C \<bullet> C \<in> { C | C \<in> ordinal \<and> C \<subset> ?A} \<turnstile> C \<subseteq> ?LA"
          by (auto simp add: olim_Rep_def Union_eq 
              subset_def psubset_eq)
        show 
          "osuc_Rep ?LA \<subseteq> ?LA"
          by (rule y2 [THEN y3])
        show 
          "?LA \<subseteq> osuc_Rep ?LA"
          by (auto simp add: osuc_Rep_def subset_def)
      qed
    qed
    have 
      b: "a < \<osuc> ?La"
      by (rule order_less_le [THEN iffD2], rule a [THEN conjI])
        (rule nas [THEN allE])
    show 
      "a = ?La"
    proof (rule order_antisym)
      show 
        "a \<le> ?La"
      proof (rule b [THEN contrapos_pp], 
             simp add: linorder_not_le linorder_not_less)
        assume 
          "?La < a"
        then show 
          "\<osuc> ?La \<le> a" 
          by (rule osuc_char)
      qed
    next
      show 
        "?La \<le> a"
        by (simp add: ole_def x4) 
          (auto simp add: olim_def olim_Rep_def psubset_eq)
    qed
  qed
qed

lemma limit_notsucI:
  assumes 
    a2: "is_limit a" and
    a1: "a \<noteq> \<omax>"
  shows
    "a \<noteq> \<osuc> b"
proof -
  from a1 a2 have 
    a3: "(\<forall> b \<bullet> a \<noteq> \<osuc> b)"
    by (rule limit_suc_disj [THEN iffD1])
  show 
   "a \<noteq> \<osuc> b" 
   by (rule a3 [rule_format])
qed

lemma limit_notsucE:
  "\<lbrakk> is_limit a; a = \<osuc> b \<rbrakk> \<turnstile> a = \<omax>"
  apply (rule contrapos_pp)
  defer 1
  apply (rule limit_notsucI)
  apply (auto)
  done

lemma limit_omax_notsuc:
  assumes 
    a1: "is_limit (\<omax>::'a ordinal)"
  shows 
    "\<osuc> (b::'a ordinal) = \<omax> \<Leftrightarrow> b = \<omax>"
proof (msafe_no_assms(inference))
  assume 
    b1: "\<osuc> b = \<omax>"
  from a1 have 
    b2: "\<omax> = \<olim> { a | a < \<osuc> b }"
    by (simp add: b1 is_limit_def)
  then have 
    "Rep_ordinal \<omax> = Rep_ordinal (\<olim> { a | a < \<osuc> b })"
    by (simp)
  then obtain 
    c 
  where 
    b3: "c < \<osuc> b" and 
    b4: "(\<some> y | y \<notin> Rep_ordinal b) \<in> Rep_ordinal c"
    by (auto simp add: Romax_conv Rolim_conv olim_Rep_def)
  from b3 have 
    b5: "c \<le> b"
    by (simp add: osuc_char2)
  with b4 have
    b6: "(\<some> y | y \<notin> Rep_ordinal b) \<in> Rep_ordinal b"
    by (auto simp add: ole_def)
  with Rep_ordinal [THEN osuc_ordinalI, of b] have 
   "\<osuc> b = b"
    by (auto simp add: osuc_def Rosuc_conv osuc_Rep_def ord.Abs_connect_on)
  then show 
    "b = \<omax>"
    by (simp add: b1)
next
  assume 
    "b = \<omax>"
  then show 
    "\<osuc> b = \<omax>"
    by (simp add: osuc_omax)
qed

lemma limit_notsuc:
  assumes 
    a1: "is_limit a"
  shows 
    "\<osuc> b = a \<Leftrightarrow> b = \<omax> \<and> a = \<omax>"
proof (cases "a = \<omax>")
  assume 
    b1: "a = \<omax>"
  from osuc_omax limit_omax_notsuc a1 b1 show 
   "\<osuc> b = a \<Leftrightarrow> b = \<omax> \<and> a = \<omax>"
    by (auto)
next
  assume 
    b1: "a \<noteq> \<omax>"
  from limit_notsucI [OF a1 b1] b1 show 
    "\<osuc> b = a \<Leftrightarrow> b = \<omax> \<and> a = \<omax>"
    by (auto simp add: b1)
qed

lemma ord_part:
  "is_limit a \<or> (\<exists> b \<bullet> b \<noteq> \<omax> \<and> a = \<osuc> b)" (is "?P a")
proof (cases "a = \<omax>")
  assume 
    a1: "a \<noteq> \<omax>"
  show 
    "?P a"
  proof (cases "is_limit a")
    assume 
      "is_limit a" 
    then show 
      "?P a" 
      by (auto)
  next
    assume 
      b1: "\<not> is_limit a" 
    show 
      "?P a"
    proof (rule disjI2, rule b1 [THEN contrapos_np], 
           simp add: a1 [THEN limit_suc_disj])
      assume 
        c1: "(\<forall> b \<bullet> b = \<omax> \<or> a \<noteq> \<osuc> b)"
      show 
        "(\<forall> b \<bullet> a \<noteq> \<osuc> b)"
      proof (rule c1 [THEN contrapos_pp], simp, elim exE)
        fix 
          b::"'a ordinal"
        assume 
          d1: "a = \<osuc> b"
        show 
          "(\<exists> b \<bullet> b \<noteq> \<omax> \<and> a = \<osuc> b)"
       proof (rule exI [of _ b], simp add: d1, 
              rule order_less_le [THEN iffD1 [THEN conjunct2]])
          show 
            "b < \<omax>"
          proof (rule order_le_less_trans [of _ a], simp add: d1)
            show 
             "b \<le> osuc b"
              by (auto simp add: ole_def Rosuc_conv osuc_Rep_def)
            show 
              "a < \<omax>"
              by (simp add: order_less_le a1 omax_ub)
          qed
        qed
      qed
    qed
  qed
next
  assume 
    a1: "a = \<omax>"
  show 
    "?P a"
  proof (cases "is_limit a")
    assume 
      "is_limit a" 
    then show 
      "?P a" 
      by (auto)
  next
    assume 
      b1: "\<not>(is_limit a)"
    let 
      ?X = "\<olim> { b::'a ordinal | b < \<omax> }"
    have 
      b2: "?X \<noteq> \<omax>"
      by (rule contrapos_nn,
          rule b1 [unfolded is_limit_def a1 [THEN eq_reflection]])
         (rule sym)
    show 
      "?P a"
    proof (rule disjI2, simp add: a1, rule exI [of _ ?X], rule conjI)
      show 
        "?X \<noteq> \<omax>" 
      by (rule b2)
      show 
        "\<omax> = \<osuc> ?X"
      proof (rule omax_ub [THEN [2] order_antisym])
        show 
          "\<omax> \<le> \<osuc> ?X"
          by (rule b2 [THEN osuc_incr [THEN contrapos_pp]], 
            simp add: linorder_not_less linorder_not_le)
            (rule olim_char, simp)
      qed
    qed
  qed
qed
  
lemma le_is_limit_osuc_le:
  assumes 
    a2: "is_limit a" and 
    a3: "b < a"
  shows 
    "\<osuc> b < a"
proof -
  from a3 have 
    a4: "\<osuc> b \<le> a" 
    by (rule osuc_char)
  from a3 have 
    a5: "b \<noteq> \<omax>"
    apply (rule contrapos_pn)
    using omax_top [of a]
    apply (simp)
    done
  from a2 a5 have 
    a5: "\<osuc> b \<noteq> a"
    by (simp add: limit_notsuc)
  with a4 
  show 
    "\<osuc> b < a"
    by (simp add: order_less_le)
qed

lemma le_is_limit_osuc_le_iff:
  assumes 
    a2: "is_limit a"
  shows 
    "\<osuc> b < a \<Leftrightarrow> b < a"
  by (auto intro: le_is_limit_osuc_le [OF a2] le_less_trans [OF osuc_nondec])

text {*

This allows us to reason about ordinals by case analysis on the
successor/limit taxonomy.

*}

lemmas ord_basecases [case_names limit successor] = ord_part [THEN disjE]

lemma ord_case_disj:
  "is_limit (a::'a ordinal) = (\<forall> b \<bullet> a = \<osuc> b \<Rightarrow> b = \<omax>)"
proof (cases a rule: max_cases)
  assume 
    a1: "a < omax"
  have 
    a2: "is_limit a = (\<forall> b \<bullet> a \<noteq> \<osuc> b)"
    by (rule limit_suc_disj) (rule a1 [THEN nonmax_conv [THEN iffD1]])
  show 
    ?thesis
  proof (simp add: a2, rule iffI)
    assume 
      "(\<forall> b \<bullet> a \<noteq> \<osuc> b)"
    then show 
      "(\<forall> b \<bullet> a = \<osuc> b \<Rightarrow> b = \<omax>)"
      by (auto)
  next
    assume 
      b1: "(\<forall> b \<bullet> a = \<osuc> b \<Rightarrow> b = \<omax>)"
    show 
      "(\<forall> b \<bullet> a \<noteq> \<osuc> b)"
    proof (rule allI, rule a1 [THEN nonmax_conv [THEN iffD1 [THEN contrapos_nn]]])
      fix 
        b::"'a ordinal"
      assume 
        c1: "a = osuc b"
      have 
        c2: "b = \<omax>"
        by (rule allE, rule b1, elim impE, rule c1, assumption)
      then show 
        "a = \<omax>"
        by (simp add: c1) (rule osuc_omax)
    qed
  qed
next
  let 
    ?X = "{c::'a ordinal|c < \<omax>}"
  assume 
    a1: "a = \<omax>"
  then show 
    ?thesis
  proof (auto simp add: is_limit_def)
    fix 
      b::"'a ordinal"
    assume 
      b1: "\<omax> = \<olim> ?X" and
      b2: "\<omax> = \<osuc> b"
    show 
      "b = \<omax>"
    proof (rule order_antisym, rule omax_ub, rule b1 [THEN ssubst],
           rule olim_min, auto simp add: Ball_def)
      fix 
        c::"'a ordinal" 
      assume 
        c1: "c < \<omax>"
      show 
        "c \<le> b"
        by (rule c1 [THEN contrapos_pp], 
            simp add: linorder_not_le linorder_not_less b2)
            (rule osuc_char)
    qed
  next
    assume 
      b1: "(\<forall> b::'a ordinal \<bullet> \<omax> = \<osuc> b \<Rightarrow> b = \<omax>)"
    have 
      b2: "\<omax> = \<osuc> (\<olim> ?X)"
    proof (rule omax_ub [THEN [2] order_antisym])
      show 
        "\<omax> \<le> \<osuc> (\<olim> ?X)"
      proof (cases "\<olim> ?X" rule: max_cases)
        assume 
          c1: "\<olim> ?X < \<omax>"
        show 
          "\<omax> \<le> \<osuc> (\<olim> ?X)"
          by (rule osuc_incr [THEN contrapos_pp],
              rule c1 [THEN nonmax_conv [THEN iffD1]],
              simp add: linorder_not_less linorder_not_le)
              (rule olim_char, simp)
      next
        assume 
          "\<olim> ?X = \<omax>"
        then show 
          "\<omax> \<le> \<osuc> (\<olim> ?X)"
          by (simp) (rule osuc_nondec)
      qed
    qed
    show 
      "\<omax> = \<olim> ?X"
      by (rule b1 [THEN allE], elim impE, rule b2, simp)
  qed
qed

text {*

Finally we establish that the ordinals are well-founded.

*}

definition
  orel :: "('a ordinal * 'a ordinal)set"
where
  orel_def: "orel \<defs> { (a::'a ordinal) b | a < b \<bullet> (a \<mapsto> b) }"

lemma orelI:
  "a < b \<turnstile> (a \<mapsto> b) \<in> orel"
  by (auto simp add: orel_def)
  
lemma orelD:
  "(a \<mapsto> b) \<in> orel \<turnstile> a < b"
  by (auto simp add: orel_def)

lemma ord_wf [iff]:
  "wf orel"
proof (auto simp add: wf_eq_minimal orel_def)
  fix 
    Q::"('a ordinal) set" and 
    b::"'a ordinal"
  assume 
    a1: "b \<in> Q"
  let 
    ?QI = "{b | (\<forall> a | a \<in> Q \<bullet> b \<le> a)}"
  let 
    ?W = "olim ?QI"
  let
    ?NW = "\<some> y | y \<notin> Rep_ordinal ?W"
  have 
    a2: "\<And> a::'a ordinal \<bullet> a \<in> Q \<turnstile> ?W \<le> a"
  proof -
    fix 
      a::"'a ordinal"
    assume 
      b1: "a \<in> Q"
    show 
      "?W \<le> a"
      by (rule olim_min, auto simp add: Ball_def, 
          elim allE [of _ a] b1 [THEN [2] impE], assumption)
  qed
  show 
    "(\<exists> c | c \<in> Q \<bullet> (\<forall> a | a < c \<bullet> a \<notin> Q))"
  proof (rule exI [of _ ?W], rule conjI)
    show 
      "?W \<in> Q"
    proof (insert omax_ub [of ?W], simp add: order_le_less, elim disjE, 
           auto simp del: order_le_less simp add: order_le_less [THEN sym])
      assume 
        c1: "?W < \<omax>"
      have 
        c2: "?W < \<osuc> ?W"
        by (rule osuc_incr) 
           (rule c1 [THEN disjI1 [THEN linorder_neq_iff [THEN iffD2]]])
      show 
        "?W \<in> Q"
      proof (rule c2 [THEN contrapos_pp], simp add: linorder_not_less)
        assume 
          d1: "?W \<notin> Q"
        show 
          "\<osuc> ?W \<le> ?W"
        proof (rule olim_char, rule CollectI, 
          rule allI, rule impI, rule osuc_char, 
          rule order_less_le [THEN iffD2], rule conjI)
          fix 
            a::"'a ordinal"
          assume 
            e1: "a \<in> Q"
          show 
            "?W \<le> a"
            by (rule e1 [THEN a2])
          show 
            "?W \<noteq> a"
            by (rule d1 [THEN contrapos_np], simp, rule e1)
        qed
      qed
    next
      assume 
        c1: "?W = \<omax>"
      have 
        c2: "\<omax> = b"
      proof (rule order_antisym)
        show 
          "\<omax> \<le> b"
          by (simp add: c1 [THEN sym], rule a1 [THEN a2])
        show 
          "b \<le> \<omax>"
          by (rule omax_ub)
      qed
      show 
        "\<omax> \<in> Q" 
        by (simp add: c2) (rule a1)
    qed
    show 
      "(\<forall> a | a < ?W \<bullet> a \<notin> Q)"
    proof (rule allI, rule impI)
      fix 
        a::"'a ordinal"
      assume 
        c1: "a < ?W"
      show 
        "a \<notin> Q"
        by (rule c1 [THEN contrapos_pn], simp add: linorder_not_less, rule a2) 
           (assumption)
    qed
  qed
qed

(*J: problem with legacy syntax! *)
lemma J_remove_split_pattern_SetCompr:
  "(Collect (\<olambda> (x, y) \<bullet>  P x y)) = {x y | P x y \<bullet> x \<mapsto> y}"
by auto

instance
  ordinal :: (type) wellorder
proof(rule wf_wellorderI, subst J_remove_split_pattern_SetCompr)
  from ord_wf show 
(*    "wf { (x , y::'a ordinal) | x < y }" *)
    "wf { x  (y::'a ordinal) | x < y \<bullet> (x , y)}"
    by (simp add: orel_def)
  show 
    "OFCLASS('a ordinal, linorder_class)"
    by intro_classes
qed

section {* Induction and recursion *}

text {*

The ordinals admit an induction theorem.

*}

theorem ord_baseinduct [case_names successor limit]:
  fixes
    a::"'a ordinal"
  assumes
    a1: "\<And> a \<bullet> \<lbrakk>a \<noteq> \<omax>; P a\<rbrakk> \<turnstile> P (\<osuc> a)" and
    a2: "\<And> a \<bullet> \<lbrakk>is_limit a; (\<forall> b | b < a \<bullet> P b) \<rbrakk> \<turnstile> P a"
  shows
    "P a"
proof (rule ord_wf [THEN wf_induct], simp add: orel_def)
  fix
    a::"'a ordinal"
  assume 
    a3: "(\<forall> b | b < a \<bullet> P b)"
  show 
   "P a"
  proof (cases a rule: ord_basecases)
    assume 
     "is_limit a"
    then show 
      "P a"
      by (rule a2) (rule a3)
  next
    assume 
      b1: "(\<exists> b \<bullet> b \<noteq> \<omax> \<and> a = \<osuc> b)"
    let 
      ?B = "(\<some> b | b \<noteq> \<omax> \<and> a = \<osuc> b)"
    have 
      b2: "?B \<noteq> \<omax>"
      by (rule conjunct1) (rule b1 [THEN some_eq_ex [THEN iffD2]])
    have 
      b3: "a = \<osuc> ?B"
      by (rule conjunct2) (rule b1 [THEN some_eq_ex [THEN iffD2]])
    show 
      "P a"
    proof (rule b3 [THEN ssubst], rule b2 [THEN a1])
      show 
        "P ?B"
        by (rule a3 [THEN allE [of _ ?B]], elim impE, auto) 
           (rule b3 [THEN ssubst], rule b2 [THEN osuc_incr])
    qed
  qed
qed

text {*

We now introduce the notion of ordinal recursion and show that it is
well-defined.

*}

definition
  ocase :: "['b \<rightarrow> 'a ordinal \<rightarrow> 'b, 'b set \<rightarrow> 'a ordinal \<rightarrow> 'b,
    'a ordinal \<rightarrow> 'b] \<rightarrow> ('a ordinal \<rightarrow> 'b)"
where
  ocase_def: "ocase g1 g2 f \<defs> (\<olambda> a \<bullet> (
    \<if> (S a) 
      \<then> g1 (f (X a)) (X a)
      \<else> g2 { b | b < a \<bullet> f b } a
    \<fi>
  \<where> 
      S = (\<olambda> a::'a ordinal \<bullet> (\<exists> b \<bullet> b \<noteq> \<omax> \<and> a = \<osuc> b));
      X = (\<olambda> a::'a ordinal \<bullet> (\<some> b | b \<noteq> \<omax> \<and> a = \<osuc> b))))"

definition
  orec :: "['b \<rightarrow> 'a ordinal \<rightarrow> 'b, 'b set \<rightarrow> 'a ordinal \<rightarrow> 'b] \<rightarrow> 
    ('a ordinal \<rightarrow> 'b)"
where
  orec_def: "orec g1 g2 \<defs> wfrec orel (ocase g1 g2)"

lemma orec_unwind:
  "orec g1 g2 (a::'a ordinal) 
  = ocase g1 g2 (cut (orec g1 g2) orel a) a"
  by (simp add: orec_def Let_def)
     (rule refl [THEN eq_reflection [THEN ord_wf [THEN [2] def_wfrec]]])
     
lemma osuc_unwind:
  assumes 
    a1: "a \<noteq> \<omax>" 
  shows
    "orec g1 g2 (\<osuc> a) = g1 (orec g1 g2 a) a"
  using a1
proof (subst orec_unwind [of _ _ "\<osuc> a"],
       auto simp add: ocase_def Let_def)
  fix 
    b::"'a ordinal"
  assume
    a2: "b \<noteq> \<omax>" and
    a3: "\<osuc> a = \<osuc> b"
  have 
    a4: "a = b" 
    by (rule a2 [THEN a1 [THEN a3 [THEN dist_osuc]]])
  let 
    ?SP = "(\<olambda> c \<bullet> c \<noteq> \<omax> \<and> \<osuc> b = \<osuc> c)"
  let 
    ?SW = "(\<some> c | ?SP c)"
  have 
    a5: "?SW \<noteq> \<omax> \<and> \<osuc> b = \<osuc> ?SW"
    by (rule conjI [THEN someI [of ?SP]], rule a2, rule refl)
  have 
    a6: "?SW = b"
    by (rule sym, rule a2 [THEN [2] dist_osuc], rule a5 [THEN conjunct2],
        rule a5 [THEN conjunct1])
  have 
    a7: "(b, \<osuc> b) \<in> orel"
    by (simp add: orel_def, rule a2 [THEN osuc_incr])
  show 
    "g1 (cut (orec g1 g2) orel (\<osuc> b) ?SW) ?SW = g1 (orec g1 g2 a) a"
    by (simp add: a4 a6 a7 [THEN cut_apply])
qed

lemma olim_unwind:
  fixes
    a::"'a ordinal"
  assumes 
    a1: "is_limit a"
  shows
    "orec g1 g2 a = g2 {b | b < a \<bullet> orec g1 g2 b} a"
  using a1
proof (subst orec_unwind [of _ _ a],
       auto simp add: ocase_def Let_def, elim notE,
       simp add: ord_case_disj)
  assume 
    a2: "(\<forall> b::'a ordinal \<bullet> b = \<omax> \<or> a \<noteq> \<osuc> b)"
  have 
    a3: "\<And> b \<bullet> b < a \<turnstile> cut (orec g1 g2) orel a b = orec g1 g2 b"
    by (rule cut_apply) (simp add: orel_def)
  have 
    a4: "{ b | b < a \<bullet> cut (orec g1 g2) orel a b } = { b | b < a \<bullet> orec g1 g2 b }"
    apply (auto simp add: a3 eind_def)
    apply (rule exI)
    apply (auto simp add: a3 eind_def)
    done
  then show 
    "g2 {b | b < a \<bullet> cut (orec g1 g2) orel a b} a 
    = g2 {b | b < a \<bullet> orec g1 g2 b} a" 
    by (simp)
qed

lemma ozero_unwind:
  "orec g1 (\<olambda> H a \<bullet> \<if> a = \<ozero> \<then> x \<else> g2 H \<fi>) \<ozero> = x"
  by (simp add: is_limit_ozero [THEN olim_unwind])

lemma olimnz_unwind:
  "\<lbrakk> \<ozero> < a; is_limit a \<rbrakk> \<turnstile> 
    orec g1 (\<olambda> H a \<bullet> \<if> a = \<ozero> \<then> x \<else> g2 H \<fi>) a =
      g2 {b | b < a \<bullet> orec g1 (\<olambda> H a \<bullet> \<if> a = \<ozero> \<then> x \<else> g2 H \<fi>) b}"
  by (simp add: olim_unwind nonzero_conv)

theorem ord_rec:
  "(\<exists>\<subone> f::'a ordinal \<rightarrow> 'b \<bullet>
    (\<forall> a \<bullet> a \<noteq> \<omax> \<Rightarrow> f (\<osuc> a) = g1 (f a) a) \<and>
    (\<forall> a \<bullet> is_limit a \<Rightarrow> f a = g2 {b | b < a \<bullet> f b} a))"
proof (rule ex1I [of _ "orec g1 g2"], auto)
  fix 
    a::"'a ordinal"
  assume 
    "a \<noteq> \<omax>"
  then show 
    "orec g1 g2 (osuc a) = g1 (orec g1 g2 a) a"
    by (rule osuc_unwind)
next
  fix 
    a::"'a ordinal"
  assume 
    "is_limit a"
  then show 
    "orec g1 g2 a = g2 {b | b < a \<bullet> orec g1 g2 b} a"
    by (rule olim_unwind)
next
  fix 
    f::"'a ordinal \<rightarrow> 'b"
  assume 
    a1: "(\<forall> a \<bullet> a \<noteq> \<omax> \<Rightarrow> f (\<osuc> a) = g1 (f a) a)" and
    a2: "(\<forall> a \<bullet> is_limit a \<Rightarrow> f a = g2 {b | b < a \<bullet> f b} a)"
  have 
    a3: "\<And> a \<bullet> a \<noteq> \<omax> \<turnstile> f (\<osuc> a) = g1 (f a) a"
    by (rule a1 [THEN allE], elim impE, auto)
  have 
    a4: "\<And> a \<bullet> is_limit a \<turnstile> f a = g2 {b | b < a \<bullet> f b} a"
    by (rule a2 [THEN allE], elim impE, auto)
  show 
    "f = orec g1 g2"
  proof (rule ext)
    fix 
      a::"'a ordinal"
    show 
      "f a = orec g1 g2 a"
    proof (induct a rule: ord_baseinduct)
      fix 
        a::"'a ordinal"
      assume 
        c1: "a \<noteq> \<omax>" and
        c2: "f a = orec g1 g2 a"
      have 
        c3: "f (osuc a) = g1 (f a) a" 
        by (rule c1 [THEN a3])
      have  
        c4: "orec g1 g2 (osuc a) = g1 (orec g1 g2 a) a"
        by (rule c1 [THEN osuc_unwind])
      show 
        "f (osuc a) = orec g1 g2 (osuc a)" 
        by (simp add: c2 c3 c4)
    next
      fix 
        a::"'a ordinal"
      assume 
        c1: "is_limit a" and
        c2: "(\<forall> b | b < a \<bullet> f b = orec g1 g2 b)"
      have 
        c3: "f a = g2 {b | b < a \<bullet> f b} a" 
        by (rule c1 [THEN a4])
      have 
        c4: "orec g1 g2 a = g2 {b | b < a \<bullet> orec g1 g2 b} a"
        by (rule c1 [THEN olim_unwind])
      have 
        c5: "\<And> b \<bullet> b < a \<turnstile> f b = orec g1 g2 b"
        by (rule c2 [THEN allE], elim impE, auto)
      have 
        c6: "{b | b < a \<bullet> f b} = {b | b < a \<bullet> orec g1 g2 b}"
      proof (auto intro: Collect_cong)
        fix 
          b::"'a ordinal"
        assume 
          d1: "b < a"
        show 
          "(\<exists> c \<bullet> f b = orec g1 g2 c \<and> c < a)"
          by (rule exI [of _ b], simp add: d1 [THEN c5] d1)
      next
        fix 
          b::"'a ordinal"
        assume 
          d1: "b < a"
        show 
          "(\<exists> c \<bullet> orec g1 g2 b = f c \<and> c < a)"
          by (rule exI [of _ b], simp add: d1 [THEN c5] d1)
      qed
      show 
        "f a = orec g1 g2 a"
        by (simp add: c3 c4 c6)
    qed
  qed
qed


lemma ord_cases [case_names zero successor limit]:
  "\<lbrakk> 
    \<ozero> = a \<turnstile> R; 
    \<exists> b \<bullet> b \<noteq> \<omax> \<and> a = \<osuc> b \<turnstile> R;  
    \<lbrakk>\<ozero> < a; is_limit a\<rbrakk> \<turnstile> R
   \<rbrakk> \<turnstile> R"
  by (rule ord_basecases, rule zero_cases, auto)

lemma ord_induct [case_names zero successor limit]:
  assumes 
    a1: "P \<ozero>" and
    a2: "\<And> a \<bullet> \<lbrakk>a \<noteq> \<omax>; P a\<rbrakk> \<turnstile> P (\<osuc> a)" and
    a3: "\<And> a \<bullet> \<lbrakk>\<ozero> < a; is_limit a; \<forall> b | b < a \<bullet> P b \<rbrakk> \<turnstile> P a"
  shows
    "P a"
proof (induct a rule: ord_baseinduct)
  fix 
    a::"'a ordinal"
  assume 
    "a \<noteq> \<omax>" "P a"
  then show 
    "P (\<osuc> a)" 
    by (rule a2)
next
  fix 
    a::"'a ordinal"
  assume 
    b1: "is_limit a" and
    b2: "\<forall> b | b < a \<bullet> P b"
  show 
   "P a"
  proof (cases a rule: zero_cases)
    assume 
      "\<ozero> = a" 
    with a1 show 
      "P a" 
      by (simp)
  next
    assume 
      "\<ozero> < a" 
    with b1 b2 a3 show 
      "P a" 
      by (auto)
  qed
qed

lemmas [cases type: ordinal] = ord_cases

lemmas [induct type: ordinal] = ord_induct

section {* A transfinite set induction theorem *}

text {*

Many properties of finite sets are best proved by showing their 
invariance under insertion and applying finite set induction.
By using ordinal induction we can extend this approach to apply
to transfinite sets as well.

*}

theorem trans_finite_induct:
  assumes 
    a1: "P \<lbot>-['a::clattice]" and
    a2: "\<And> B \<bullet> \<lbrakk> B < A; P B \<rbrakk> \<turnstile> (\<exists> C | \<lch>B \<chLt> C \<chLe> A\<rch> \<bullet> P C)" and
    a3: "\<And> CL_B \<bullet> \<lbrakk>chain CL_B; (\<forall> B | B \<in> CL_B \<bullet> B \<le> A \<and> P B)\<rbrakk> \<turnstile> P (\<lSup>CL_B)"
  shows 
    "P A"
proof -

txt {*

The proof progresses by ordinal induction on an increasing ordinal sequence 
os approximations of @{text A}. 
The sequence is chosen so that, initially, it is an increasing
sequence of strict subsets of @{text A} that satisfy @{text P}. 
The inductive hypotheses ensure that it is always possible to extend such
a sequence.
If the sequence is long enough then
is must eventually actually attain @{text A} (by Cantor's lemma) and we
observe that the inductive hypotheses also ensure that the very first element
to achieve @{text A} also satisfies @{text P},
hence @{text "P A"}.

*}

  let
    ?NX = "\<olambda> B C \<bullet> \<lch>B \<chLt> C \<chLe> A\<rch> \<and> P C"
  let
    ?CL_A_d_s = "\<olambda> (B::'a) (a::('a set) ordinal) \<bullet>
      \<if> B < A \<and> P B \<then> (\<some> C | ?NX B C) \<else> B \<fi>" and
    ?CL_A_d_l = "\<olambda> (CL_B::'a set) (a::('a set) ordinal) \<bullet> 
      \<if> a = \<ozero> \<then> \<lbot> \<else> \<lSup>CL_B \<fi>"
  let ?CL_A = "orec ?CL_A_d_s ?CL_A_d_l"

txt {*

First note that every successor of an element which satisfies @{text P}
is strictly larger.

*}

{
  fix 
    a::"('a set) ordinal"
  assume 
    b1: "?CL_A a < A" and 
    b2: "a \<noteq> \<omax>" and 
    b3: "P (?CL_A a)"
  from b1 b3 have 
    "(\<exists> C \<bullet> ?NX (?CL_A a) C)"
    by (rule a2)
  then have 
    "?NX (?CL_A a) (\<some> C | ?NX (?CL_A a) C)"
    by (rule someI_ex)
  then have 
    b4: "?CL_A a < (\<some> C | ?NX (?CL_A a) C)" 
    by (auto)
  from b1 have
    b5: "?CL_A a \<noteq> A" 
    by (auto)
  from b1 b2 b3 b5 b4 have 
    "?CL_A a < ?CL_A (\<osuc> a)" 
    by (simp add: osuc_unwind)
} note a4 = this

txt {*

In addition, the entire sequence is monotonic.

*}

  have 
    a5: "mono ?CL_A"
  proof (rule monoI)
    fix 
      a::"('a set) ordinal" and 
      b::"('a set) ordinal"
    assume 
      b1: "a \<le> b"
    let 
      ?Q = "(\<olambda> b \<bullet> (\<forall> a | a \<le> b \<bullet> ?CL_A a \<le> ?CL_A b))"
    have 
      "(\<forall> a | a \<le> b \<bullet> ?CL_A a \<le> ?CL_A b)"
      apply (rule ord_induct [where ?P = "?Q"])
      apply (msafe_no_assms(inference))
    proof -
      fix 
        a::"('a set) ordinal"
      assume 
        "a \<le> \<ozero>"
      then have 
        "a = \<ozero>" 
        by (simp add: ozero_eq)
      then show 
        "?CL_A a \<le> ?CL_A \<ozero>"
        by (simp)
    next
      fix 
        a::"('a set) ordinal" and 
        b::"('a set) ordinal"
      assume 
        c1: "b \<noteq> \<omax>" and 
        c2: "?Q b" and 
        c3: "a \<le> \<osuc> b"
      show 
        "?CL_A a \<le> ?CL_A (\<osuc> b)"
      proof (cases "a < \<osuc> b")
        assume 
          d1: "a < \<osuc> b"
        then have 
          d2: "a \<le> b" 
          by (rule osuc_char2)
        with c2 have 
          "?CL_A a \<le> ?CL_A b" 
          by (auto)
        also from a4 c1 have 
          "?CL_A b \<le> ?CL_A (\<osuc> b)"
        proof (cases "(?CL_A b) < A \<and> P (?CL_A b)")
          assume 
            e1: "(?CL_A b) < A \<and> P (?CL_A b)"
          with c1 a4 have 
            "?CL_A b < ?CL_A (\<osuc> b)"
            by (auto)
          then show 
            "?CL_A b \<le> ?CL_A (\<osuc> b)"
            by (simp add: order_less_le)
        next
          assume 
            e1: "\<not>((?CL_A b) < A \<and> P (?CL_A b))"
          have 
            "?CL_A (\<osuc> b) = ?CL_A b"
            by (simp add: osuc_unwind [OF c1] e1)
          then show 
            "?CL_A b \<le> ?CL_A (\<osuc> b)"
            by (auto)
        qed
        finally show 
          "?CL_A a \<le> ?CL_A (\<osuc> b)" 
          by (this)
      next
        assume 
          d1: "\<not>(a < \<osuc> b)"
        with c3 have 
          d2: "a = \<osuc> b"
          by (simp add: order_le_less)
        then show 
          "?CL_A a \<le> ?CL_A (\<osuc> b)" 
          by (simp)
      qed
    next
      fix 
        b::"('a set) ordinal" and 
        c::"('a set) ordinal"
      assume 
        c1: "\<ozero> < c" and 
        c2: "is_limit c" and
        c3: "\<forall> b | b < c \<bullet> ?Q b" and 
        c4: "b \<le> c"
      show 
        "?CL_A b \<le> ?CL_A c"
      proof (cases "b = c")
        assume 
          d1: "b = c"
        then show 
          "?CL_A b \<le> ?CL_A c" 
          by (simp)
      next
        assume 
          d1: "b \<noteq> c"
        with c4 have 
          d2: "b < c" 
          by (simp add: order_le_less)
        from c1 c2 have 
          "?CL_A c = \<lSup> { b | b < c \<bullet> ?CL_A b }"
          by (simp add: olimnz_unwind)
        with d2 show 
          "?CL_A b \<le> ?CL_A c"
          using Sup_ub [of "?CL_A b" "{ b | b < c \<bullet> ?CL_A b }"]
          by (auto)
      qed
    qed
    with b1 show 
      "?CL_A a \<lle> ?CL_A b" 
      by (auto)
  qed

txt {*

Now we observe that every element of the sequence is a subset of @{text A}, and
that if it is not @{text A} it satisfies @{text P}.

*}

{
  fix 
    a::"('a set) ordinal"
  let 
    ?Q = "(\<olambda> a \<bullet> ?CL_A a \<lle> A \<and> (?CL_A a \<llt> A \<Rightarrow> P (?CL_A a)))"
  have 
    "?Q a"
  proof (rule ord_induct [where ?P = "?Q"])
    have 
      "?CL_A \<ozero> = \<lbot>"
      by (simp add: ozero_unwind)
    with a1 show 
      "?Q \<ozero>" 
      using bot_lb
      by (auto)
  next
    apply_end (elim conjE)
    fix 
      a::"('a set) ordinal"
    assume 
      b1: "a \<noteq> \<omax>" and 
      b2: "?CL_A a \<lle> A" and 
      b3: "?CL_A a \<llt> A \<Rightarrow> P (?CL_A a)"
    let 
      ?C = "(\<some> C | ?NX (?CL_A a) C)"
    have 
      "?CL_A a \<lle> A" 
      by (rule b2)
    also have 
      "?CL_A a \<lle> A
      \<Rightarrow> ?CL_A a \<llt> A \<or> ?CL_A a = A"
      by (auto)
    also from b3 have "\<dots>
      \<Rightarrow> (?CL_A a \<llt> A \<and> P (?CL_A a)) \<or> ?CL_A a = A"
      by (mauto(wind))
    also from b1 b2 have "\<dots> 
      \<Rightarrow> (?CL_A a \<llt> A \<and> P (?CL_A a) \<and> ?CL_A (\<osuc> a) = ?C) \<or> ?CL_A a = A"
      by (mauto(wind), simp add: osuc_unwind)
    also from b1 have "\<dots> 
      \<Rightarrow> (?CL_A a \<llt> A \<and> P (?CL_A a) \<and> ?CL_A (\<osuc> a) = ?C) 
         \<or> ?CL_A a = A \<and> ?CL_A a \<lle> ?CL_A (\<osuc> a) \<and> ?CL_A (\<osuc> a) \<lle> A"
      apply (mauto(wind))
      apply (simp add: osuc_unwind)
      done
    also have "\<dots> 
      \<Rightarrow> (?CL_A a \<llt> A \<and> P (?CL_A a) \<and> ?CL_A (\<osuc> a) = ?C) \<or> ?CL_A (\<osuc> a) = A"
      by (auto)
    finally show 
      "?Q (\<osuc> a)"
    proof (elim disjE conjE)
      assume 
        c1: "?CL_A a \<llt> A" and 
        c2: "P (?CL_A a)" and
        c3: "?CL_A (\<osuc> a) = ?C"
      from c1 c2 have 
        "(\<exists> C \<bullet> ?NX (?CL_A a) C)"
        by (rule a2)
      then have 
        "?NX (?CL_A a) ?C"
        by (rule someI_ex)
      with c3 have 
        c4: "?NX (?CL_A a) (?CL_A (\<osuc> a))"
        by (simp)
      from c4 show 
        "?Q (\<osuc> a)" 
        by (auto)
    next
      assume 
        c1: "?CL_A (\<osuc> a) = A"
      then show 
        "?Q (\<osuc> a)" 
         by (auto)
    qed
  next
    fix 
      a::"('a set) ordinal"    
    assume 
      b1: "\<ozero> < a" and 
      b2: "is_limit a" and
      b3: "\<forall> b | b < a \<bullet> ?Q b"
    from b1 b2 have 
      b4: "?CL_A a = \<lSup> { b | b \<llt> a \<bullet> ?CL_A b }"
      by (simp add: olimnz_unwind)
    from b3 b4 have 
      b5: "?CL_A a \<lle> A"
      by (auto intro: Sup_lub simp add: eind_def)
    have
      b6: "?CL_A a \<llt> A \<Rightarrow> P (?CL_A a)"
    proof (simp only: b4, rule impI)
      assume 
        c1: "\<lSup> { b | b < a \<bullet> ?CL_A b } \<llt> A"
      have 
        c2: "chain { b | b < a \<bullet> ?CL_A b }"
      proof (intro chainI, simp_all add: mem_Collect_eq, msafe_no_assms(inference), simp_all)
        from b1 show 
          "(\<exists> b \<bullet> b < a)" 
          by (auto)
        fix 
          a::"('a set) ordinal" and 
          b::"('a set) ordinal"
        have 
          "a \<le> b \<or> b \<le> a" 
          by (rule linorder_linear)
        with a5 [THEN monoD] show 
          "?CL_A a \<lle> ?CL_A b \<or> ?CL_A b \<lle> ?CL_A a"
          by (auto)
      qed
      have 
        "(\<forall> b | b < a \<bullet> ?CL_A b \<llt> A)"
        by (auto intro!: le_less_trans [OF _ c1] Sup_ub)
      with b3 have 
        "(\<forall> b | b < a \<bullet> ?CL_A b \<lle> A \<and> P (?CL_A b))"
        by (auto)
      then have 
        c3: "(\<forall> B | B \<in> {b | b < a \<bullet> ?CL_A b} \<bullet> B \<lle> A \<and> P B)"
        by (auto)
      from c2 c3 show "P (\<lSup> {b | b < a \<bullet> ?CL_A b})"
        by (rule a3)
    qed
    from b5 b6 show 
      "?Q a" 
      by (auto)
  qed
} note a6 = this

txt {*

From Cantor's theorem, we know that @{text "?CL_A"} is not an injection,
hence it eventually limits to @{text A}.

*}

  have 
    "(\<exists> a b \<bullet> a < b \<and> ?CL_A a = ?CL_A b)"
    by (rule ord_Cantor_cor)
  then have 
    a7: "(\<exists> a \<bullet> ?CL_A a = A)"
  proof (msafe_no_assms(inference))
    fix a b
    assume 
      b1: "a < b" and 
      b2: "?CL_A a = ?CL_A b"
    from b1 omax_ub have 
      "a < \<omax>" 
      by (rule order_less_le_trans)
    then have 
      b3: "a \<noteq> \<omax>" 
      by (simp add: nonmax_conv)
    from b1 have 
      b4: "\<osuc> a \<le> b" 
      by (rule osuc_char)
    with a5 have 
      b5: "?CL_A (\<osuc> a) \<lle> ?CL_A b"
      by (rule monoD)
    have 
      "\<not>(?CL_A a \<llt> A)"
    proof (rule notI)
      assume 
        c1: "?CL_A a \<llt> A"
      with a6 have 
        c2: "P (?CL_A a)" 
        by (auto)
      from c1 b3 c2 have
        c3: "?CL_A a \<llt> ?CL_A (\<osuc> a)" 
        by (rule a4)
      from c3 b5 have  
        "?CL_A a \<llt> ?CL_A b" 
        by (rule order_less_le_trans)
      then have 
        c4: "?CL_A a \<noteq> ?CL_A b"  
        by (simp add: order_less_le)
      from c4 b2 show 
        "\<False>" 
        by (contradiction)
    qed
    with a6 [of a] have b6: "?CL_A a = A" 
      by (auto simp add: linorder_not_less order_le_less)
    then show 
      "(\<exists> a \<bullet> ?CL_A a = A)" 
      by (auto)
  qed

txt {*

Now suppose that @{text "?a"} is the first element with value @{text A}.

*}

  let 
    ?a = "(\<LEAST> a | ?CL_A a = A)"

txt {*

Clearly, every element before @{text "?a"} is a strict subset of @{text A},
and hence the inductive hypotheses ensure @{text "P A"}.

*}

  from a7 have 
    a8: "?CL_A ?a = A" 
    by (msafe_no_assms(inference)) (rule LeastI)
  have 
    a9: "\<forall> b | b < ?a \<bullet> ?CL_A b \<llt> A"
  proof (msafe_no_assms(inference)) 
    fix b
    assume 
      b1: "b < ?a"
    from b1 a6 have 
      b2: "?CL_A b \<lle> A" 
      by (auto simp add: order_less_le)
    from b1 have 
      b3: "\<not>(?CL_A b = A)" 
      by (rule not_less_Least)
    from b2 b3 show 
      "?CL_A b \<llt> A" 
      by (auto simp add: order_le_less)
  qed
  have 
    "P (?CL_A ?a)"
  proof (cases "?a")
    assume 
      b1: "\<ozero> = ?a"
    from b1 [THEN sym] a1 show 
      "P (?CL_A ?a)"
      by (simp add: ozero_unwind)
  next
    assume 
      b1: "(\<exists> b \<bullet> b \<noteq> \<omax> \<and> ?a = \<osuc> b)"
    then show 
      "P (?CL_A ?a)"
    proof (msafe_no_assms(inference))
      fix 
        b
      assume 
        c1: "b \<noteq> \<omax>" and 
        c2: "?a = \<osuc> b"
      from c1 have 
        c3: "b < ?a" 
        by (simp add: c2, rule osuc_incr)
      with a9 have 
        c4: "?CL_A b \<llt> A"                              
        by (auto) 
      with a6 have 
        c5: "P (?CL_A b)" 
        by (auto)
      from c1 c2 c4 c5 have 
        c6: "?CL_A ?a = (\<some> C | ?NX (?CL_A b) C)"
        by (simp add: osuc_unwind order_less_le)
      from c4 c5 have 
        "(\<exists> C \<bullet> ?NX (?CL_A b) C)"
        by (rule a2)
      then have 
        "?NX (?CL_A b) (\<some> C | ?NX (?CL_A b) C)"
        by (rule someI_ex)
      with c6 show 
        "P (?CL_A ?a)" 
        by (auto)
    qed
  next
    assume 
      b1: "\<ozero> < ?a" and 
      b2: "is_limit ?a"
    from b1 b2 have 
      b3: "?CL_A ?a = \<lSup>{ b | b < ?a \<bullet> ?CL_A b }"
      by (simp add: olimnz_unwind)
    show 
      "P (?CL_A ?a)"
    proof (simp add: b3, rule a3)
      show 
        "chain { b | b < ?a \<bullet> ?CL_A b }"
      proof (rule chainI, simp_all add: mem_Collect_eq, msafe_no_assms(inference), simp_all)
        from b1 show    
          "(\<exists> b \<bullet> b < ?a)" 
          by (auto)
        fix  
          a::"('a set) ordinal" and 
          b::"('a set) ordinal"
        have 
          "a \<le> b \<or> b \<le> a" 
          by (rule linorder_linear)
        with a5 [THEN monoD] show 
          "?CL_A a \<lle> ?CL_A b \<or> ?CL_A b \<lle> ?CL_A a"
          by (auto)
      qed
      from a6 a9 show 
        "(\<forall> B | B \<in> {b | b < ?a \<bullet> ?CL_A b} \<bullet> B \<lle> A \<and> P B)"
        by (auto)
    qed
  qed
  with a8 show 
    "P A" 
    by (simp)
qed

theorem trans_finset_induct:
  assumes 
    a1: "P \<emptyset>-['a]" and
    a2: "\<And> B \<bullet> \<lbrakk> B \<subset> A; P B \<rbrakk> \<turnstile> (\<exists> C | \<lch>B \<chSubset> C \<chSubseteq> A\<rch> \<bullet> P C)" and
    a3: "\<And> CL_B \<bullet> \<lbrakk>chain CL_B; (\<forall> B | B \<in> CL_B \<bullet> B \<subseteq> A \<and> P B)\<rbrakk> \<turnstile> P (\<Union>CL_B)"
  shows 
    "P A"
    apply (rule trans_finite_induct [where A = "A"])
    using a1 a2 a3
    apply (simp_all add: bot_set_def Sup_set_def eind_def)
    done

section {* Fixed points as ordinal limits *}

definition
  oapprox :: "['a::clattice \<rightarrow> 'a, ('a set) ordinal] \<rightarrow> ('a \<rightarrow> 'a)"
where
  oapprox_def: "oapprox f a \<defs> 
    (orec (\<olambda> g a x \<bullet> f (g x)) 
      (\<olambda> H a \<bullet> \<if> a = \<ozero> \<then> (\<olambda> x \<bullet> x) \<else> (\<olambda> x \<bullet> (\<lSUP> h | h \<in> H \<bullet> h x)) \<fi>) a)"
 
notation (xsymbols)
  oapprox ("_\<oapprox>\<^bsup>_\<^esup>" [1000,0] 1000)

lemma oapprox_ozero: "f\<oapprox>\<^bsup>\<ozero>\<^esup> x = x"
  by (auto simp add: oapprox_def ozero_unwind)

lemma oapprox_osuc: 
  assumes 
    a1: "a \<noteq> \<omax>"
  shows 
    "f\<oapprox>\<^bsup>\<osuc> a\<^esup> x = f(f\<oapprox>\<^bsup>a\<^esup> x)"
  using a1
  by (auto simp add: oapprox_def osuc_unwind)

lemma oapprox_nzolim: 
  assumes 
    a1: "\<ozero> < a" "is_limit a"
  shows 
    "f\<oapprox>\<^bsup>a\<^esup> x = (\<lSUP> b | b < a \<bullet> f\<oapprox>\<^bsup>b\<^esup> x)"
  using a1
  by (simp add: oapprox_def olimnz_unwind eind_def eind_comp)

lemmas oapprox_conv = oapprox_ozero oapprox_osuc oapprox_nzolim

lemma oapprox_mono:
  assumes 
    a1: "f \<in> \<mh>" and 
    a2: "b \<le> a"
  shows 
    "f\<oapprox>\<^bsup>b\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
proof -
  txt {*
  The proof proceeds by induction on the proposition that the approximations
  are linearly-ordered.
  *}
  have 
    a3: "\<forall> a b c \<bullet> b \<le> a \<and> c \<le> b \<Rightarrow> f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot>"
  proof (rule allI)
    fix 
      a::"'a set ordinal"
    show 
      "(\<forall> b c \<bullet> b \<le> a \<and> c \<le> b \<Rightarrow> f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot>)" (is "?P a")
    proof (induct a)
      fix 
        a::"'a set ordinal"
    case zero
      show 
        "(\<forall> b c \<bullet> b \<le> \<ozero> \<and> c \<le> b \<Rightarrow> f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot>)"
        proof (auto)
          fix 
            b::"('a set) ordinal" and 
            c::"('a set) ordinal" 
          assume 
            c1: "b \<le> \<ozero>" and 
            c2: "c \<le> b"
          from c2 c1 have 
            c3: "c \<le> \<ozero>" 
            by (rule order_trans)
          then have 
            c4: "c = \<ozero>" 
            by (simp add: ozero_eq)
          from c1 have 
            c5: "b = \<ozero>" 
            by (simp add: ozero_eq)
          from c4 c5 show 
            "f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot>" 
            by (simp)
        qed
    next
      fix 
        a::"'a set ordinal"
      assume 
        c1: "a \<noteq> \<omax>" and
        c2: "(\<forall> b c \<bullet> b \<le> a \<and> c \<le> b \<Rightarrow> f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot>)"
      have 
        c3: "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>\<osuc> a\<^esup> \<lbot>"
      proof (cases a rule: zero_cases)
      case zero
        from zero show 
          "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>\<osuc> a\<^esup> \<lbot>"
          by (auto simp add: oapprox_def ozero_unwind bot_lb)
      next 
      case nonzero
        have 
          "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> (\<lSUP> c|c < a\<bullet>f(f\<oapprox>\<^bsup>c\<^esup> \<lbot>))"
        proof (cases a)
        case zero
          with nonzero show 
            "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> (\<lSUP> c | c < a \<bullet> f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>))"
            by (auto)
        next 
        case successor
          from successor show 
            "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> (\<lSUP> c | c < a \<bullet> f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>))"
          proof (elim exE, auto)
            fix 
              b::"'a set ordinal" 
            assume 
              f1: "b \<noteq> \<omax>"
            have 
              "f\<oapprox>\<^bsup>\<osuc> b\<^esup> \<lbot> 
              \<lle> (\<lSUP> c | c \<le> b \<bullet> f(f\<oapprox>\<^bsup>c\<^esup> \<lbot>))"
              by (simp add: oapprox_def f1 [THEN osuc_unwind], rule Sup_ub, auto)
            also have "\<dots> 
              = (\<lSUP> c | c < \<osuc> b \<bullet> f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>))"
            proof (rule arg_cong [of _ _ "\<lSup>"], auto)
              fix 
                c::"'a set ordinal" 
              assume 
                g1: "c \<le> b"
              show 
                "(\<exists> c' \<bullet> f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>) = f (f\<oapprox>\<^bsup>c'\<^esup> \<lbot>) \<and> c' < \<osuc> b)"
                by (rule exI [of _ c], auto) 
                   (rule f1 [THEN [2] osuc_incr [THEN [2] order_le_less_trans]],
                   rule g1)
            next
              fix 
                c::"'a set ordinal" 
              assume 
                g1: "c < \<osuc> b"
              show 
                "(\<exists> c' \<bullet> f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>) = f (f\<oapprox>\<^bsup>c'\<^esup> \<lbot>) \<and> c' \<le> b)"
                by (rule exI [of _ c], auto) 
                   (rule g1 [THEN osuc_char2])
            qed
            finally show 
              "f\<oapprox>\<^bsup>\<osuc> b\<^esup> \<lbot> \<lle> (\<lSUP> c | c < \<osuc> b \<bullet> f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>))"
              by (this)
          qed
        next 
        case limit
          from limit show 
            "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> (\<lSUP> c | c < a \<bullet> f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>))"
            apply (auto simp add: oapprox_def olimnz_unwind intro!: order_eq_refl)
            apply (fold oapprox_def)
            apply (intro order_antisym)
            apply (auto intro!: Sup_lub simp add: eind_def eind_comp)
            apply (auto intro!: Sup_lub simp add: eind_norm [of "(\<olambda> x \<bullet> lSup (Collect x))"])
          proof -
            fix 
              c::"'a set ordinal"
            assume 
              g1: "\<ozero> < a" and
              g2: "is_limit a" and
              g3: "c < a"
            have 
              g4: "c \<noteq> \<omax>"
              by (simp add: nonmax_conv [THEN sym], rule g3 [THEN order_less_trans])
                 (simp add: nonmax_conv c1)
            show 
              "f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> (\<lSUP> c | c < a \<bullet> f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>))"
            proof (rule order_trans [of _ "f\<oapprox>\<^bsup>\<osuc> c\<^esup> \<lbot>"])
              show 
                "f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>\<osuc> c\<^esup> \<lbot>"
                by (intro c2 [rule_format], auto intro!: g3 [THEN osuc_char] osuc_nondec)
            next
              from g4 show 
                "f\<oapprox>\<^bsup>\<osuc> c\<^esup> \<lbot> \<lle> (\<lSUP> c | c < a \<bullet> f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>))"
                by (auto simp add: oapprox_def osuc_unwind intro!: Sup_ub exI [of _ c] g3)
            qed
            have 
              "f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>) 
              = f\<oapprox>\<^bsup>\<osuc> c\<^esup> \<lbot>"
              by (simp add: oapprox_def g4 [THEN osuc_unwind])
            also have "\<dots> 
              \<lle> (\<lSUP> h | (\<exists> c' \<bullet> h = f\<oapprox>\<^bsup>c'\<^esup> \<and> c' < a) \<bullet> h \<lbot>)"
            proof (auto intro!: Sup_ub exI [of _ "f\<oapprox>\<^bsup>\<osuc> c\<^esup>"]
                   exI [of _ "\<osuc> c"])
              show 
                "\<osuc> c < a"
                apply (simp add: order_less_le)
                apply (intro conjI)
                apply (rule g3 [THEN osuc_char])  
                apply (simp add: g2 [THEN limit_notsuc] c1)
                done
            qed
            finally show 
              "f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>) \<lle> (\<lSUP> c' | c' < a \<bullet> f\<oapprox>\<^bsup>c'\<^esup> \<lbot>)"
              by (auto simp add: eind_def eind_comp)
          qed
        qed
        also from a1 [THEN mh_Sup, of "{ c | c < a \<bullet> f\<oapprox>\<^bsup>c\<^esup> \<lbot> }"] have "\<dots> 
          \<lle> f (\<lSUP> c | c < a \<bullet> f\<oapprox>\<^bsup>c\<^esup> \<lbot>)"
          by (simp add: eind_def eind_comp)
        also have "\<dots> 
          \<lle> f (f\<oapprox>\<^bsup>a\<^esup> \<lbot>)"
          apply (rule a1 [THEN mhD])
          apply (rule Sup_lub)
          apply (auto intro!: c2 [rule_format])
          done
        also have "\<dots> 
          \<lle> f\<oapprox>\<^bsup>\<osuc> a\<^esup> \<lbot>"
          by (simp add: oapprox_def c1 [THEN osuc_unwind])
        finally show 
          "f\<oapprox>\<^bsup>a\<^esup> \<lbot>  \<lle> f\<oapprox>\<^bsup>\<osuc> a\<^esup> \<lbot>"
          by (this)
      qed
      show 
        "(\<forall> b c \<bullet> b \<le> \<osuc> a \<and> c \<le> b \<Rightarrow> f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot>)"
        apply (simp add: order_le_less)
        apply (msafe_no_assms(inference)) 
        apply (simp_all (no_asm) add: order_le_less [THEN sym])
        apply (auto)
        apply (rule c2 [rule_format])
        apply (rule osuc_char2)
        apply (assumption)
        apply (rule order_less_imp_le)
        apply (assumption)
        apply (rule order_trans)
        apply (rule c2 [rule_format])
        apply (rule order_refl)
        apply (rule osuc_char2)
        apply (auto intro!: c3)
        done
    next
      fix 
        a::"'a set ordinal"
      assume 
        b1: "\<ozero> < a" and
        b2: "is_limit a" and
        b3: "(\<forall> a' \<bullet> a' < a \<Rightarrow> (\<forall> b c \<bullet> b \<le> a' \<and> c \<le> b \<Rightarrow> f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot>))"    
      show 
        "(\<forall> b c \<bullet> b \<le> a \<and> c \<le> b \<Rightarrow> f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot>)"
        apply (simp add: order_le_less)
        apply (msafe_no_assms(inference))
        apply (simp_all (no_asm) add: order_le_less [THEN sym])
        apply (auto)
        apply (rule b3 [rule_format])
        apply (auto)
      proof -
        fix 
          c::"'a set ordinal"
        assume 
          c1: "c < a"
        show 
          "f\<oapprox>\<^bsup>c\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
        proof (simp add: oapprox_def b2 [THEN olim_unwind]
               b1 [THEN order_less_le [THEN iffD1 [THEN conjunct2 [THEN not_sym]]]], 
               fold oapprox_def, rule Sup_ub, auto simp add: eind_comp)
          show 
            "(\<exists> b \<bullet> f\<oapprox>\<^bsup>c\<^esup> \<lbot> = f\<oapprox>\<^bsup>b\<^esup> \<lbot> \<and> b < a)"
            by (rule exI [of _ c], auto intro: c1)
        qed
      qed
    qed
  qed
  show 
    "f\<oapprox>\<^bsup>b\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
    by (rule a3 [rule_format], auto intro!: a2)
qed

lemma oapprox_chain:
  assumes
    a1: "f \<in> \<mh>"
  shows
    "chain { a::('a::clattice) set ordinal \<bullet> f\<oapprox>\<^bsup>a\<^esup> \<lbot> }"
  apply (rule chainI)
  apply (simp_all)
  apply (mauto(inference))
proof -
  fix
    a :: "'a set ordinal" and
    b :: "'a set ordinal"
  from linear [of "a" "b"] show
    "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot> 
     \<or>
     f\<oapprox>\<^bsup>b\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
    by (mauto(inference) mintro: oapprox_mono [OF a1] disjI1 disjI2)
qed

lemma oapprox_max: 
  assumes 
    a1: "\<forall> a b | a \<le> b \<bullet> f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot>"
  shows 
    "(\<exists> b \<bullet> (\<lSUP> a \<bullet> f\<oapprox>\<^bsup>a\<^esup> \<lbot>) = f\<oapprox>\<^bsup>b\<^esup> \<lbot>)"
proof (insert ord_Cantor_cor [of "\<olambda> a \<bullet> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"], msafe_no_assms(inference))
  fix 
    a b
  assume 
    a2: "a < b" and
    a3: "f\<oapprox>\<^bsup>a\<^esup> \<lbot> = f\<oapprox>\<^bsup>b\<^esup> \<lbot>"
  from a2 have 
    "\<osuc> a \<le> b"
    by (rule osuc_char)
  with a1 a3 have 
    a4: "f\<oapprox>\<^bsup>(\<osuc> a)\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
    by (auto)
  from a1 have 
    a5: "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>(\<osuc> a)\<^esup> \<lbot>"
    by (auto intro: osuc_nondec)
  from a5 a4 have 
    a6: "f\<oapprox>\<^bsup>a\<^esup> \<lbot> = f\<oapprox>\<^bsup>(\<osuc> a)\<^esup> \<lbot>"
    by (rule order_antisym)
  from a2 omax_ub [of b] have 
    "a < \<omax>" 
    by (rule order_less_le_trans)
  then have  
    a7: "a \<noteq> \<omax>" by (simp add: nonmax_conv)
  {
  fix 
    c
  have 
    a4: "a \<le> c \<Rightarrow> f\<oapprox>\<^bsup>c\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
  proof (induct c type: ordinal, msafe_no_assms(inference))
    assume 
      b1: "a \<le> \<ozero>"
    then have 
      b2: "a = \<ozero>" 
      by (simp add: ozero_eq)
    then show 
      "f\<oapprox>\<^bsup>\<ozero>\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
      by (simp)
  next
    fix 
      c
    assume 
      b1: "c \<noteq> \<omax>" and 
      b2: "a \<le> c \<Rightarrow>  f\<oapprox>\<^bsup>c\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup> \<lbot>" and
      b3: "a \<le> \<osuc> c"
    show 
      "f\<oapprox>\<^bsup>\<osuc> c\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
    proof (cases "a < \<osuc> c")
      assume 
        c1: "a < \<osuc> c"
      then have 
        "a \<le> c" 
        by (rule osuc_char2)
      with b2 have 
        c2: "f\<oapprox>\<^bsup>c\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup> \<lbot>" 
        by (auto)
      from b1 have 
        "f\<oapprox>\<^bsup>(\<osuc> c)\<^esup> \<lbot> 
        = f (f\<oapprox>\<^bsup>c\<^esup> \<lbot>)"
        by (simp add: oapprox_conv)
      also from c2 have "\<dots> 
        = f (f\<oapprox>\<^bsup>a\<^esup> \<lbot>)" 
        by (simp)
      also from a7 have "\<dots> 
        = f\<oapprox>\<^bsup>(\<osuc> a)\<^esup> \<lbot>"
        by (simp add: oapprox_conv)
      also from a6 have "\<dots> 
        = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
        by (simp)
      finally show 
        "f\<oapprox>\<^bsup>(\<osuc> c)\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
        by (this)
    next
      assume 
        c1: "\<not> (a < \<osuc> c)"
      then have 
        "\<osuc> c \<le> a" 
        by (simp add: linorder_not_less)
      with b3 have 
        "a = \<osuc> c" 
        by (rule order_antisym)
      then show 
        "f\<oapprox>\<^bsup>(\<osuc> c)\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
        by (simp)
    qed
  next
    fix 
      c 
    assume 
      b1: "\<ozero> < c" and 
      b2: "is_limit c" and
      b3: "\<forall> d | d < c \<bullet> a \<le> d \<Rightarrow> f\<oapprox>\<^bsup>d\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup> \<lbot>" and
      b4: "a \<le> c"
    show 
      "f\<oapprox>\<^bsup>c\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup>\<lbot>"
    proof (cases "a < c", simp_all only: linorder_not_less)
      assume 
        c1: "a < c"
      from b1 b2 have 
        "f\<oapprox>\<^bsup>c\<^esup> \<lbot> 
        = (\<lSUP> d | d < c \<bullet> f\<oapprox>\<^bsup>d\<^esup> \<lbot>)"
        by (simp add: oapprox_conv)
      also have "\<dots> 
        = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
      proof (rule Sup_eq, auto)
        fix 
          d 
        assume  
          d1: "d < c"
        show 
          "f\<oapprox>\<^bsup>d\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
        proof (cases "a \<le> d", simp_all add: linorder_not_le)
          assume 
            e1: "a \<le> d"
          from b3 [rule_format, OF d1 e1] show 
            "f\<oapprox>\<^bsup>d\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
            by (auto)
        next
          assume 
            e1: "d < a"
          with a1 show 
            "f\<oapprox>\<^bsup>d\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
            by (auto intro: order_less_imp_le)
        qed
      next
        fix 
          y
        assume 
          d1: "\<forall> d | d < c \<bullet> f\<oapprox>\<^bsup>d\<^esup>  \<lbot> \<lle> y"
        with c1 show 
          "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> y"
          by (auto)
      qed
      finally show 
        "f\<oapprox>\<^bsup>c\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
        by (this)
    next
      assume 
        c1: "c \<le> a"
      with b4 have 
        "a = c" 
        by (rule order_antisym)
      then show 
        "f\<oapprox>\<^bsup>c\<^esup> \<lbot> = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
        by (simp)
    qed
  qed
  } note a8 = this
  have 
    "(\<lSUP> b \<bullet> f\<oapprox>\<^bsup>b\<^esup> \<lbot>) = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
  proof (rule Sup_eq, auto)
    fix 
      b
    show 
      "f\<oapprox>\<^bsup>b\<^esup> \<lbot> \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
    proof (cases "a \<le> b", simp_all add: linorder_not_le)
      assume 
        b1: "a \<le> b"
      with a8 [of b] show 
        ?thesis
        by (auto)
    next
      assume 
        b1: "b < a"
      with a1 show 
        ?thesis
        by (auto intro: order_less_imp_le)
    qed
  qed
  then show 
    ?thesis 
    by (auto)
qed

lemma fapprox_lb_lfp:
  assumes 
    a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>"
  shows 
    "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> (\<lLFP> x \<bullet> f x)"
  apply (simp add: lfp_char [OF a1])
  apply (rule Inf_glb, auto)
proof -
  fix 
    x::'a
  assume 
    a2: "f x \<lle> x"
  show 
    "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> x" (is "?P a")
  proof (induct a)
  case zero
    show 
      "f\<oapprox>\<^bsup>\<ozero>\<^esup> \<lbot> \<lle> x"
      by (simp add: oapprox_def ozero_unwind bot_lb)
  next
    fix 
      a::"'a set ordinal"
    assume 
      b1: "a \<noteq> \<omax>" and 
      b2: "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> x"
    have 
      "f\<oapprox>\<^bsup>\<osuc> a\<^esup> \<lbot> 
      = f (f\<oapprox>\<^bsup>a\<^esup> \<lbot>)"
      by (simp add: oapprox_def b1 [THEN osuc_unwind])
    also have "\<dots> 
      \<lle> f x"
      by (rule b2 [THEN a1 [THEN mhD]])
    also have "\<dots> 
      \<lle> x"
      by (rule a2)
    finally show 
      "f\<oapprox>\<^bsup>\<osuc> a\<^esup> \<lbot> \<lle> x"
      by (this)
  next
    fix 
      a::"'a set ordinal"
    assume 
      b1: "\<ozero> < a" and
      b2: "is_limit a" and 
      b3: "\<forall> b \<bullet> b < a \<Rightarrow> f\<oapprox>\<^bsup>b\<^esup> \<lbot> \<lle> x"
    show 
      "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> x"
      by (simp add: oapprox_def b2 [THEN olim_unwind] b1 [THEN nonzero_conv [THEN iffD1]], 
          rule Sup_lub, auto, fold oapprox_def, rule b3 [rule_format], assumption)
  qed
qed

theorem lfp_limit:
  assumes 
    a1: "(f::('a::clattice) \<rightarrow> 'a) \<in> \<mh>" 
  shows 
    "(\<exists> a \<bullet> (\<lLFP> x \<bullet> f x) = f\<oapprox>\<^bsup>a\<^esup> \<lbot>)"
proof (insert ord_Cantor_cor [of "(\<olambda> a \<bullet> f\<oapprox>\<^bsup>a\<^esup> \<lbot>)"], auto)
  fix 
    a::"'a set ordinal" and 
    b::"'a set ordinal"
  assume  
    a2: "a < b" and
    a3: "f\<oapprox>\<^bsup>a\<^esup> \<lbot> = f\<oapprox>\<^bsup>b\<^esup> \<lbot>"
  have 
    a4: "a \<noteq> \<omax>"
    by (simp add: nonmax_conv [THEN sym],
        rule a2 [THEN omax_ub [THEN [2] order_less_le_trans]])
  show 
    "(\<exists> a \<bullet> (\<lLFP> x \<bullet> f x) = f\<oapprox>\<^bsup>a\<^esup> \<lbot>)"
  proof (rule exI [of _ a], rule order_antisym)
    show 
      "(\<lLFP> x \<bullet> f x) \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
      apply (simp add: lfp_def)
      apply (rule Inf_lb)
      apply (auto simp add: fp_set_def, rule order_antisym)
    proof -
      have 
        "f (f\<oapprox>\<^bsup>a\<^esup> \<lbot>) 
        = f\<oapprox>\<^bsup>\<osuc> a\<^esup> \<lbot>"
        by (simp add: oapprox_def a4 [THEN osuc_unwind])
      also have "\<dots> 
        \<lle> f\<oapprox>\<^bsup>b\<^esup> \<lbot>"
        by (rule a1 [THEN oapprox_mono], rule a2 [THEN osuc_char])
      also have "\<dots> 
        =  f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
        by (rule a3 [THEN sym])
      finally show 
        "f (f\<oapprox>\<^bsup>a\<^esup> \<lbot>) \<lle> f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
        by (this)
    next
      have 
        "f\<oapprox>\<^bsup>a\<^esup> \<lbot> 
        \<lle> f\<oapprox>\<^bsup>\<osuc> a\<^esup> \<lbot>"
        by (rule a1 [THEN oapprox_mono], rule osuc_nondec)
      also have "\<dots> 
        = f (f\<oapprox>\<^bsup>a\<^esup> \<lbot>)"
        by (simp add: oapprox_def a4 [THEN osuc_unwind])     
      finally show 
        "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> f (f\<oapprox>\<^bsup>a\<^esup> \<lbot>)"
        by (this)
    qed
  next
    show 
      "f\<oapprox>\<^bsup>a\<^esup> \<lbot> \<lle> (\<lLFP> x \<bullet> f x)"
      by (rule fapprox_lb_lfp [OF a1])
  qed
qed

lemma oapprox_fun_mh:
  fixes
    f::"(('a::clattice) \<rightarrow> ('b::clattice)) \<rightarrow> ('a \<rightarrow> 'b)"
  assumes 
    a1: "f \<in> \<mh>" and
    a2: "(\<And> x \<bullet> x \<in> \<mh> \<turnstile> (f x) \<in> \<mh>)"
  shows 
    "(f\<oapprox>\<^bsup>a\<^esup> \<lbot>) \<in> \<mh>" (is "?P a")
proof (induct a)
  show 
    "(f\<oapprox>\<^bsup>\<ozero>\<^esup> \<lbot>) \<in> \<mh>"
    by (simp add: oapprox_def ozero_unwind bot_fun_def monotonic_ops_def mono_def)
next
  fix 
    a::"('a \<rightarrow> 'b) set ordinal"
  assume 
    b1: "a \<noteq> \<omax>" and
    b2: "(f\<oapprox>\<^bsup>a\<^esup> \<lbot>) \<in> \<mh>"
  have 
    "(f (f\<oapprox>\<^bsup>a\<^esup> \<lbot>)) \<in> \<mh>" 
    by (rule b2 [THEN a2])
  then show 
    "(f\<oapprox>\<^bsup>\<osuc> a\<^esup> \<lbot>) \<in> \<mh>"
    by (simp add: oapprox_def b1 [THEN osuc_unwind])
next
  fix 
    a::"('a \<rightarrow> 'b) set ordinal"
  assume 
    b1: "\<ozero> < a" and
    b2: "is_limit a" and
    b3: "\<forall> b \<bullet> b < a \<Rightarrow> (f\<oapprox>\<^bsup>b\<^esup> \<lbot>) \<in> \<mh>"
  have 
    b4: "a \<noteq> \<ozero>"
    by (simp add: nonzero_conv [THEN sym] b1) 
  show 
    "(f\<oapprox>\<^bsup>a\<^esup> \<lbot>) \<in> \<mh>"
    apply (simp add: oapprox_def b2 [THEN olim_unwind] b4, fold oapprox_def)
    apply (rule Sup_mh)
    apply (auto intro!: b3 [rule_format]) 
    done 
qed


theorem lfp_fun_mh:
  fixes
    f::"(('a::clattice) \<rightarrow> ('b::clattice)) \<rightarrow> ('a \<rightarrow> 'b)"
  assumes 
    a1: "f \<in> \<mh>" and
    a2: "(\<And> x \<bullet> x \<in> \<mh> \<turnstile> (f x) \<in> \<mh>)"
  shows 
    "(\<lLFP> x \<bullet> f x) \<in> \<mh>"
  by (insert lfp_limit [of f], auto simp add: a1, rule oapprox_fun_mh)
     (rule a1, rule a2, assumption)

lemma lfp_ord_induct:
  assumes
    a1: "f \<in> \<mh>" and
    a2: "P (f\<oapprox>\<^bsup>\<ozero>\<^esup> \<lbot>)" and
    a3: "\<And> b \<bullet> P (f\<oapprox>\<^bsup>b\<^esup> \<lbot>) \<turnstile> P (f\<oapprox>\<^bsup>\<osuc> b\<^esup> \<lbot>)" and
    a4: "\<And> a \<bullet> \<lbrakk> is_limit a; (\<forall> b | b < a \<bullet> P (f\<oapprox>\<^bsup>b\<^esup> \<lbot>)) \<rbrakk> \<turnstile> P(f\<oapprox>\<^bsup>a\<^esup> \<lbot>)"
  shows
    "P (\<lLFP> x \<bullet> f x)"
  using lfp_limit [OF a1]
  apply (auto)
  apply (rule ord_induct)
  using a2 a3 a4
  apply (auto)
  done

lemma lfp_unfold_induct:
  fixes
    f :: "('a::clattice) \<rightarrow> 'a"
  assumes
    a1: "f \<in> \<mh>" and
    a2: "P (f \<lbot>)" and
    a3: "\<And> x \<bullet> P x \<turnstile> P (f x)" and
    a4: "\<And> X \<bullet> \<lbrakk> X \<noteq> \<emptyset>; (\<forall> x | x \<in> X \<bullet> P (f x)) \<rbrakk> \<turnstile> P(\<lSUP> x | x \<in> X \<bullet> f x)"
  shows
    "P (\<lLFP> x \<bullet> f x)"
proof -
{ 
  fix
    a :: "'a set ordinal"
  have 
    "\<ozero> < a \<Rightarrow> P(f\<oapprox>\<^bsup>a\<^esup> \<lbot>)" (is "?P a")
  proof (induct "a")
    show
      "?P \<ozero>"
      by (simp)
  next
    fix
      a :: "'a set ordinal"
    assume
      c1: "a \<noteq> \<omax>" and
      c2: "?P a"
    show
      "?P (\<osuc> a)"
      apply (cases "a = \<ozero>")
      using a2 
      apply (simp add: oapprox_conv osuc_incr nonzero_omax)
      using c1 c2 a3 [of "f\<oapprox>\<^bsup>a\<^esup> \<lbot>"]
      apply (auto simp add: oapprox_conv osuc_incr nonzero_conv [symmetric])
      done
  next
    fix
      a :: "'a set ordinal"
    assume
      c0: "\<ozero> < a" and
      c1: "is_limit a" and
      c2: "\<forall> b | b < a \<bullet> ?P b"
    let
      ?X = "{ b | b < a \<bullet> f\<oapprox>\<^bsup>b\<^esup> \<lbot>}"
    have
      c3: "P(\<lSUP> x | x \<in> ?X \<bullet> f x)"
      apply (rule a4)
      using c0
      apply (auto)
    proof -
      fix
        b :: "'a set ordinal"
      assume
        d1: "b < a"
      from c1 d1 have
        d3: "\<osuc> b < a"
        by (rule le_is_limit_osuc_le)
      have
        d4: "\<ozero> < \<osuc> b"
        by (rule ozero_less_osuc)
      with d3 have
        d5: "P (f\<oapprox>\<^bsup>\<osuc> b\<^esup> \<lbot>)"
        by (rule c2 [rule_format])
      with less_le_trans [OF d1 omax_ub] show
        "P (f (f\<oapprox>\<^bsup>b\<^esup> \<lbot>))"
        by (simp add: oapprox_conv nonmax_conv)
    qed
    have
      "{ x | x \<in> ?X \<bullet> f x } 
      = { b | b < a \<bullet> f\<oapprox>\<^bsup>\<osuc> b\<^esup> \<lbot>}"
      apply (simp add: eind_def eind_comp)
      apply (mauto(wind) mintro!: ext)
      apply (auto simp add: oapprox_osuc [OF nonmaxI])
      done
    also have "\<dots>
      = { b c | b < a \<and> c = \<osuc> b \<bullet> f\<oapprox>\<^bsup>c\<^esup> \<lbot>}"
      by (auto)
    also from le_is_limit_osuc_le_iff [OF c1] have "\<dots>
      = { b c | \<osuc> b < a \<and> c = \<osuc> b \<bullet> f\<oapprox>\<^bsup>c\<^esup> \<lbot>}"
      by (auto)
    also  have "\<dots>
      = { b c | c < a \<and> c = \<osuc> b \<bullet> f\<oapprox>\<^bsup>c\<^esup> \<lbot>}"
      by (auto)
    also have "\<dots>
      = { c | c < a \<and> (\<exists> b \<bullet> c = \<osuc> b) \<bullet> f\<oapprox>\<^bsup>c\<^esup> \<lbot>}"
      by (auto simp add: eind_def)
    also have "\<dots>
      = { b | b < a \<and> \<not>(is_limit b) \<bullet> f\<oapprox>\<^bsup>b\<^esup> \<lbot>}"
      apply (simp add: ord_case_disj)
      apply (mauto(wind) mintro!: nonmaxI mintro: le_less_trans [OF osuc_nondec])
      done
    also have "\<lSup> \<dots>
      = \<lSup> { b | b < a \<bullet> f\<oapprox>\<^bsup>b\<^esup> \<lbot>}"
      apply (rule antisym)
      apply (rule Sup_sub)
      apply (simp add: subset_def)
      apply (fast)
      apply (rule Sup_lub)
      apply (auto)
    proof -
      fix
        b :: "'a set ordinal"
      assume
        d1: "b < a"
      show
        "f\<oapprox>\<^bsup>b\<^esup> \<lbot> 
        \<lle> \<lSup> { b | b < a \<and> \<not>(is_limit b) \<bullet> f\<oapprox>\<^bsup>b\<^esup> \<lbot>}"
        apply (cases "is_limit b")
        apply (rule order_trans)
        apply (rule oapprox_mono [OF a1])
        apply (rule osuc_nondec)
        apply (rule Sup_ub)
        apply (simp)
        apply (witness "\<osuc> b")
        using 
          d1 le_is_limit_osuc_le_iff [OF c1, of "b"] 
          ord_case_disj [of "\<osuc> b"] nonmaxI [of "b" "a"] (***)
        apply (fast)
        apply (rule Sup_ub)
        using d1
        apply (auto)
        done
    qed
    finally show
      "?P a"   
      using c1 c3
      by (simp add: oapprox_conv eind_def)
  qed
} note b1 = this
  show
    "?thesis"
    using lfp_limit [OF a1]
  proof (elim exE)
    fix
      a :: "'a set ordinal"
    assume
      c1: "(\<lLFP> x \<bullet> f x) = f\<oapprox>\<^bsup>a\<^esup> \<lbot>"
    show
      "?thesis"
      apply (cases "a = \<ozero>")
      using lfp_fold [OF a1] a2 c1
      apply (simp add: oapprox_ozero)
      using c1 b1 [of "a"]
      apply (simp add: nonzero_conv)
      done
  qed
qed

(*
lemma lfp_unfold_induct:
  assumes
    a1: "f \<in> \<mh>" and
    a2: "P \<lbot>" and
    a3: "\<And> x \<bullet> P x \<turnstile> P (f x)" and
    a4: "\<And> X \<bullet> (\<forall> x | x \<in> X \<bullet> P x) \<turnstile> P(\<lSup> X)"
  shows
    "P (\<lLFP> x \<bullet> f x)"
proof -
{
  fix
    a
  have
    b1: "P (f\<^oapp>{:a:} \<lbot>)"
    apply (induct "a")
    apply (auto simp add: oapprox_conv)
    apply (rule a2)
    apply (rule a3)
    apply (assumption)
    apply (rule a4)
    apply (auto)
    done
} with lfp_limit [OF a1] show
    "?thesis"
    by (auto)
qed
*)

(*
lemma oapprox_fun_botj:
  assumes a1: "mono (f::(('a::clattice) \<rightarrow> ('b::clattice)) \<rightarrow> ('a \<rightarrow> 'b))" and
    a2: "(\<And> x \<bullet> botj x \<turnstile>  botj (f x))"
  shows " botj (f\<^oapp>{:a:} \<lbot>)" (is "?P a");
proof (induct ?P a);
  show "botj (f\<^oapp>{:\<ozero>:} \<lbot>)";
    by (simp add: oapprox_def ozero_unwind bot_fun_conv botj_def);
  next;
    fix a::"('a \<rightarrow> 'b) set ordinal";
    assume b1: "a \<noteq> \<omax>" and
      b2: "botj (f\<^oapp>{:a:} \<lbot>)";
    have "botj (f(f\<^oapp>{:a:} \<lbot>))" by (rule b2 [THEN a2]);
    then show "botj (f\<^oapp>{:\<osuc> a:} \<lbot>)";
      by (simp add: oapprox_def b1 [THEN osuc_unwind]);
  next;
    fix a::"('a \<rightarrow> 'b) set ordinal";
    assume b1: "\<ozero> < a" and
      b2: "is_limit a" and
      b3: "\<forall>b\<bullet>b < a \<implies> botj (f\<^oapp>{:b:} \<lbot>)";
    have b4: "a \<noteq> \<ozero>";
      by (simp add: nonzero_conv [THEN sym] b1);
    show "botj (f\<^oapp>{:a:} \<lbot>)";
      by (simp add: oapprox_def b2 [THEN olim_unwind] b4, fold oapprox_def,
        simp add: botj_def Sup_fun_conv, rule Sup_eq, rule order_eq_refl, auto,
        fold botj_def, auto intro!: b3 [rule_format] bot_lb);
  qed;
qed;

lemma lfp_fun_botj:
  "\<lhyps> mono (f::(('a::clattice) \<rightarrow> ('b::clattice)) \<rightarrow> ('a \<rightarrow> 'b));
    (\<And>x\<bullet>botj x \<proves> botj (f x)) \<rhyps> \<proves>
    botj (\<lLFP>x\<bullet>f x)";
proof -;
  assume a1: "mono f" and
    a2: "\<And>x\<bullet>botj x \<proves> botj (f x)";
  show "botj (\<lLFP>x\<bullet>f x)";
    by (insert lfp_limit [of f], auto simp add: a1, rule oapprox_fun_botj)
      (rule a1, rule a2, assumption);
qed;
*)

end
