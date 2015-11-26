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

header {* Extensions to the \isa{type{\isacharunderscore}definition} locale *}

theory 
  xHOL_TypeDef
  
imports
  xHOL_Lemmas_Chap

begin

text {*

The @{text Typedef} theory gives some useful rules for reasoning
about type definitions and organises them into a locale framework. 
In this section we introduce an theorem attribute for instantiating these 
rules and extend the locale with some more useful results.

*}

subsection {* Instantiating @{text "type_definition"} theorems *}

ML {*

local

  fun tdi_apply get Tnm =
  let                                                                             
    fun mk_thm x thm =
    let
      val tydef_T = get x (("type_definition_"^Tnm));
    in
      tydef_T RS thm
    end;
  in
    Thm.rule_attribute mk_thm
  end;

in

val TDINST_setup =
  Attrib.setup (Binding.name "TDINST") 
    (Scan.lift Args.name >> tdi_apply (fn ctxt => (Global_Theory.get_thm (Context.theory_of ctxt))))
    "positional instantiation of theorem";
end;

*}

setup {* TDINST_setup *}

subsection {* Some derived @{text "type_definition"} lemmas *}

context type_definition

begin

lemma Rep_image:
  "{ x | x \<in> X \<bullet> Rep x } \<subseteq> A"
  by (auto simp add: Rep)

lemma Rep_image':
  "{ x \<bullet> Rep x } \<subseteq> A"
  by (auto simp add: Rep)

lemma Rep_eqI: 
  assumes a1: "Rep x = Rep y"
  shows "x = y"
  using a1
  by (simp add: Rep_inject)

lemma Rep_eqI':
  assumes a1: "x = y"
  shows "Rep x = Rep y"
  using a1
  by (simp)

lemma Abs_eq_onI: 
  assumes 
    a1: "x \<in> A" "y \<in> A" "Abs x = Abs y"
  shows 
    "x = y"
  using a1
  by (simp add: Abs_inject)

lemma Abs_eq_onI':
  assumes 
    a1: "x = y"
  shows 
    "Abs x = Abs y"
  using a1
  by (simp)

lemma Rep_connect_on: 
  assumes 
    a1: "y \<in> A"
  shows 
    "(Rep x = y) \<Leftrightarrow> (x = Abs y)"
proof -
  from type_definition_axioms a1 have 
    "Rep x = y
    \<Leftrightarrow> Abs (Rep x) = Abs y"
    by (simp add: Abs_inject Rep)
  also from type_definition_axioms have "\<dots>
    \<Leftrightarrow> x = Abs y"
    by (simp add: Rep_inverse)
  finally show ?thesis
    by (this)
qed

lemma Abs_connect_on: 
  assumes 
    a1: "x \<in> A"
  shows 
    "(Abs x = y) \<Leftrightarrow> (x = Rep y)"
proof -
  from type_definition_axioms have 
  "Abs x = y
  \<Leftrightarrow> Rep (Abs x) = Rep y"
    by (simp add: Rep_inject Rep)
  also from type_definition_axioms a1 have "\<dots>
  \<Leftrightarrow> x = Rep y"
    by (simp add: Abs_inverse)
  finally show ?thesis
    by (this)
qed

lemma Rep_inj: 
  "inj Rep"
  by (auto intro!: inj_onI simp add: Rep_inject)

lemma Abs_inj_on:  
  "inj_on Abs A"
  by (auto intro!: inj_onI simp add: Abs_inject)

lemma Rep_onto_on:
  assumes 
    a1: "y \<in> A"
  shows 
    "\<exists> x \<bullet> y = Rep x"
proof -
  from a1 have a2: "y = Rep (Abs y)" by (simp add: Abs_inverse)
  from a2 show ?thesis by (auto)
qed

lemma Abs_onto_on:
  "\<exists> y \<bullet> y \<in> A \<and> x = Abs y"
proof -
  have a1: "Rep x \<in> A" by (rule Rep)
  have a2: "Abs (Rep x) = x" by (simp add: Rep_inverse)
  from a1 a2 show ?thesis by (auto)
qed

lemma Rep_char:
  "(y \<in> A) = (\<exists> x \<bullet> y = Rep x)"
by (auto intro: Rep_onto_on Rep)

lemma Rep_nonempty:
  "A \<noteq> \<emptyset>"
proof -
  obtain x::'b where True by (auto)
  have "Rep x \<in> A" by (rule Rep)
  then show ?thesis by (auto)
qed

lemma Rep_inverse_raw:
  "Abs \<circ> Rep = id"
  by (auto intro!: ext simp add: Rep_inverse)

lemma (in type_definition) Rep_inverse_image:
  "Abs\<lparr>Rep\<lparr>X\<rparr>\<rparr> = X"
  by (auto simp add: image_def Rep_inverse)

lemma Abs_inverse_image_on:
  assumes
    a1: "X \<subseteq> A"
  shows
    "Rep\<lparr>Abs\<lparr>X\<rparr>\<rparr> = X"
  using a1
  by (auto simp add: image_def Abs_inverse subset_eq)

lemma Rep_image_eq_iff:
  "Rep\<lparr>X\<rparr> = Rep\<lparr>Y\<rparr> \<Leftrightarrow> X = Y"
  by (rule inj_image_eq_iff [OF Rep_inj])

lemma Abs_image_eq_iff_on:
  assumes
    a1: "X \<subseteq> A" and 
    a2: "Y \<subseteq> A"
  shows
    "Abs\<lparr>X\<rparr> = Abs\<lparr>Y\<rparr> \<Leftrightarrow> X = Y"
  apply (rule inj_on_Un_image_eq_iff)
  apply (rule subset_inj_on)
  apply (rule Abs_inj_on)
  using a1 a2
  apply (auto)
  done

lemma Abs_image_connect_on:
  assumes
    a1: "X \<subseteq> A"
  shows
    "Abs\<lparr>X\<rparr> \<subseteq> Y \<Leftrightarrow> X \<subseteq> Rep\<lparr>Y\<rparr>"
  apply (auto simp add: image_def subset_eq Rep_inverse)
  apply (rule bexI)
  apply (rule Abs_inverse [symmetric])
  using a1
  apply (auto)
  done

lemma Abs_image_connect_eq_on:
  assumes
    a1: "X \<subseteq> A"
  shows
    "Abs\<lparr>X\<rparr> = Y \<Leftrightarrow> X = Rep\<lparr>Y\<rparr>"
  apply (subst (2) Abs_inverse_image_on [symmetric, OF a1])
  apply (simp add: Rep_image_eq_iff)
  done

lemma Rep_image_connect_on:
  assumes
    a1: "X \<subseteq> A"
  shows
    "Rep\<lparr>Y\<rparr> \<subseteq> X \<Leftrightarrow> Y \<subseteq> Abs\<lparr>X\<rparr>"
  apply (auto simp add: image_def subset_eq)
  apply (rule bexI)
  apply (rule Rep_inverse [symmetric])
  using a1
  apply (auto elim!: ballE simp add: Abs_inverse)
  done

lemma Rep_image_connect_eq_on:
  assumes
    a1: "X \<subseteq> A"
  shows
    "Rep\<lparr>Y\<rparr> = X \<Leftrightarrow> Y = Abs\<lparr>X\<rparr>"
  apply (subst Abs_inverse_image_on [symmetric, OF a1])
  apply (simp add: Rep_image_eq_iff)
  done

lemma Rep_image_Int:
  "Rep\<lparr>X \<inter> Y\<rparr> = Rep\<lparr>X\<rparr> \<inter> Rep\<lparr>Y\<rparr>"
  by (rule image_Int [OF Rep_inj])

lemma Abs_image_Int_on:
  assumes
    a1: "X \<subseteq> A" and 
    a2: "Y \<subseteq> A"
  shows
    "Abs\<lparr>X \<inter> Y\<rparr> = Abs\<lparr>X\<rparr> \<inter> Abs\<lparr>Y\<rparr>"
  by (rule inj_on_image_Int [OF Abs_inj_on a1 a2])

lemma all_Abs_iff:
  "(\<forall> x \<bullet> P x) \<Leftrightarrow> (\<forall> y \<bullet> P (Abs y))"
  apply (auto)
  apply (subst Rep_inverse [symmetric])
  apply (auto)
  done

lemma ex_Abs_iff:
  "(\<exists> x \<bullet> P x) \<Leftrightarrow> (\<exists> y \<bullet> P (Abs y))"
  apply (auto)
  apply (subst (asm) Rep_inverse [symmetric])
  apply (auto)
  done

end

locale epi_type_definition =
  fixes Rep and Abs
  assumes 
    Rep_surj: "range Rep = \<univ>" and 
    Rep_inverse: "Abs (Rep x) = x"

sublocale epi_type_definition \<subseteq> TD: type_definition "Rep" "Abs" "\<univ>"
proof (rule type_definition.intro)
  fix
    x :: "'b"
  from Rep_surj show
    "Rep x \<in> \<univ>" 
    by (auto)
  from Rep_inverse show
    "Abs (Rep x) = x"
    by (auto)
next
  fix 
    y :: "'a"
  from Rep_surj obtain x where
    "y = Rep x"
    by (auto)
  then show
    "Rep (Abs y) = y"
    by (simp add: Rep_inverse)
qed

lemma (in type_definition) epiI:
  assumes
    a1: "A = \<univ>"
  shows 
    "epi_type_definition Rep Abs"
  apply (rule epi_type_definition.intro)
  using a1 Rep_range Rep_inverse
  apply (auto)
  done

context epi_type_definition

begin

lemma Abs_inverse:
  "Rep (Abs r) = r"
  by (simp add: TD.Abs_inverse)

lemma Abs_inject:
  "(Abs x = Abs y) \<Leftrightarrow> (x = y)"
  by (simp add: TD.Abs_inject)

lemma Rep_cases [cases set]:
  assumes 
    hyp: "!!x. y = Rep x ==> P"
  shows 
    "P"
  apply (rule TD.Rep_cases)
  apply (auto intro: hyp)
  done

lemma Abs_cases [cases type]:
  assumes 
    r: "\<And> y \<bullet> x = Abs y \<turnstile> P"
  shows 
    "P"
  apply (rule TD.Abs_cases)
  apply (auto intro: r)
  done

lemma Rep_induct [induct set]:
  assumes 
    hyp: "!!x. P (Rep x)"
  shows 
    "P y"
  apply (rule TD.Rep_induct)
  apply (auto intro: hyp)
  done

lemma Abs_induct [induct type]:
  assumes
    r: "\<And> y \<bullet> P (Abs y)"
  shows 
   "P x"
  apply (rule TD.Abs_induct)
  apply (auto intro: r)
  done

lemmas Abs_surj = TD.Abs_image

lemma Abs_inverse_raw:
  "Rep \<circ> Abs = id"
  by (auto intro!: ext simp add: TD.Abs_inverse)

lemma Abs_inj:
  "inj Abs"
  using TD.Abs_inj_on
  by (simp)

lemma Abs_eqI: 
  assumes 
    a1: "Abs x = Abs y"
  shows 
    "x = y"
  apply (rule TD.Abs_eq_onI)
  apply (auto simp add: a1)
  done

lemma Rep_connect: 
  "(Rep x = y) \<Leftrightarrow> (x = Abs y)"
  apply (rule TD.Rep_connect_on)
  apply (simp)
  done

lemma Abs_connect: 
  "(Abs x = y) \<Leftrightarrow> (x = Rep y)"
  apply (rule TD.Abs_connect_on)
  apply (simp)
  done

lemma Rep_onto:
  "\<exists> x \<bullet> y = Rep x"
  apply (rule TD.Rep_onto_on)
  apply (simp)
  done

lemma Abs_onto:
  "\<exists> y \<bullet> x = Abs y"
  using TD.Abs_onto_on [of "x"]
  apply (auto)
  done

lemma Abs_inverse_image:
  "Rep\<lparr>Abs\<lparr>X\<rparr>\<rparr> = X"
  apply (rule TD.Abs_inverse_image_on)
  apply (simp)
  done

lemma Abs_image_eq_iff:
  "Abs\<lparr>X\<rparr> = Abs\<lparr>Y\<rparr> \<Leftrightarrow> X = Y"
  apply (rule TD.Abs_image_eq_iff_on)
  apply (auto)
  done

lemma Abs_image_connect:
  "Abs\<lparr>X\<rparr> \<subseteq> Y \<Leftrightarrow> X \<subseteq> Rep\<lparr>Y\<rparr>"
  apply (rule TD.Abs_image_connect_on)
  apply (auto)
  done

lemma Abs_image_connect_eq:
  "Abs\<lparr>X\<rparr> = Y \<Leftrightarrow> X = Rep\<lparr>Y\<rparr>"
  apply (rule TD.Abs_image_connect_eq_on)
  apply (auto)
  done

lemma Rep_image_connect:
  "Rep\<lparr>Y\<rparr> \<subseteq> X \<Leftrightarrow> Y \<subseteq> Abs\<lparr>X\<rparr>"
  apply (rule TD.Rep_image_connect_on)
  apply (auto)
  done

lemma Rep_image_connect_eq:
  "Rep\<lparr>Y\<rparr> = X \<Leftrightarrow> Y = Abs\<lparr>X\<rparr>"
  apply (rule TD.Rep_image_connect_eq_on)
  apply (auto)
  done

lemma Abs_image_Int:
  "Abs\<lparr>X \<inter> Y\<rparr> = Abs\<lparr>X\<rparr> \<inter> Abs\<lparr>Y\<rparr>"
  apply (rule TD.Abs_image_Int_on)
  apply (auto)
  done

lemma all_Rep_iff:
  "(\<forall> x \<bullet> P (Rep x)) \<Leftrightarrow> (\<forall> y \<bullet> P y)"
  apply (auto)
  apply (subst Abs_inverse [symmetric])
  apply (auto)
  done

lemma ex_Rep_iff:
  "(\<exists> x \<bullet> P (Rep x)) \<Leftrightarrow> (\<exists> y \<bullet> P y)"
  apply (auto)
  apply (subst (asm) Abs_inverse [symmetric])
  apply (auto)
  done

end

end
