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

theory Value_Types 

imports 
  Equipotence
  Cartesian_Universe

begin

text {*

In a sense, having the value space be a disjoint union of all the
allowed value types is something of an overkill. In fact, all that
is required is that any given value type can be embedded in the
the value space. For example, in actual computer languages there is 
really only one basic type, essentially the machine word, and all
other types are virtual in the sense that they are formed by re-interpretting
the meaning of a word. Aiding in the search for a suitable value
space is HOL's extensional approach to the introduction of type constructors.
The preferred method is to define new types via a representation set
in some existing type. In fact, in the existing HOL library there appear
to be only four basic type constructors, functions, booleans, 
the so-called {\em individuals}
(basic to the development of number systems) and sets. All other 
types (including datatypes) are constructed using representation sets built 
from these basic constructors.  In fact, even the booleans are easily embedded
in the individuals, which are countably infinite.
 
As described above, 
the Cartesian Universe constructor takes an atomic type and constructs
a space large enough to contain disjoint images of all the
types built using the atomic type. the product constructor, and the
set constructor. The Cartesian Universe built from the 
individuals is a space large enough to encompass  
all of the types of standard HOL. Functions can be modelled  
as sets of pairs. 

*}

typedef 
  VAL = "\<univ>-[ind cartuniv]"
  by (auto)

(*

lemma VAL_undef:
  "set_The \<emptyset> = Abs_VAL (set_The \<emptyset>)"
  apply (rule set_the_equality)
  sorry

axioms
  VAL_undef: "set_The \<emptyset> = Abs_VAL (set_The \<emptyset>)"
*)


interpretation
  VAL: epi_type_definition "Rep_VAL" "Abs_VAL"
  apply (rule type_definition.epiI)
  apply (rule type_definition_VAL)
  apply simp
  done

text {*

In order to easily control the class of value types allowed in HiVe,
we introduce an axiomatic class to represent all types that have
have an injection @{text "\<vinj>"} into @{text VAL}. We also introduce
and associated projection @{text "\<vproj>"}.

Our approach to modelling this follows similar lines to that adopted for the
@{text order} axclass, we introduce a dummy class @{text "vtype"} for which
@{text "\<vinj>"} is defined. The desired class is then the subclass
@{text "valtype"} of @{text "vtype"} for which @{text "\<vinj>"} is injective.

We use this approach so that we can have fine control over the value of 
@{text "\<vinj>"} for some type important type constructors, notably 
@{text ind} and @{text set}. 
*}

class vtype = typerep +

fixes
  vinj :: "'a \<rightarrow> VAL" 

begin

definition
  vproj :: "VAL \<rightarrow> 'a"
where
  vproj_def: "vproj \<defs> inv vinj"

notation (xsymbols output)
  vinj ("\<nu>\<iota>") and
  vproj ("\<nu>\<pi>")

notation (zed)
  vinj ("\<vinj>") and
  vproj ("\<vproj>")

end

class
  valtype = vtype +
assumes
  vinj_inj: "inj \<vinj>"

lemma (in valtype) vinj_inverse: "\<vproj> (\<vinj> x) = x"
  by (auto simp add: vproj_def vinj_inj [THEN inv_f_f])

(*
lemma vinj_inverse: "\<vproj> (\<vinj>-['a::valtype] x) = x"
  by (auto simp add: vproj_def vinj_inj [THEN inv_f_f])
*)

lemma (in valtype) vinj_o_inverse:
  "\<vproj> \<circ> \<vinj> = id"
  by (simp add: vproj_def vinj_inj)

lemma (in valtype) vproj_inverse: 
  "x \<in> range \<vinj> 
  \<turnstile> \<vinj> (\<vproj> x) = x"
  by (simp add: vproj_def f_inv_into_f [of _ _ "\<univ>"])

instantiation 
  VAL :: vtype

begin

definition
  VAL_vinj_def: "\<vinj>-[VAL] \<defs> id"

instance
  by (intro_classes)

end

instance
  VAL :: valtype
  apply (intro_classes)
  apply (auto simp add: VAL_vinj_def)
  done

text {*

For the purposes of performing the injection proofs, generally we find it more
convenient (especially in the case of datatype constructors) to argue
on an abstract cardinality level. To allow this we introduce parallel
axiomatic classes @{text vcard}, for types with cardinality less than
@{text VAL}, and @{text svcard}, for those with cardinality less than
some rank of @{text VAL}.

*}

class
  vcard = typerep +
assumes
  vcard: "\<^sEP>{:\<univ>:}{:\<univ>-[VAL]:}"

lemma vcardI': 
  fixes 
    f::"'a \<rightarrow> VAL"
  assumes 
    a1: "inj f"
  shows 
    "OFCLASS('a, vcard_class)"
proof (intro_classes)
  from a1 have 
    "(\<graphof> f) \<in> \<univ> \<zinj> \<univ>"
    by (rule graph_of_f_inj)
  then show 
    "\<^sEP>{:\<univ>-['a]:}{:\<univ>-[VAL]:}"
    by (auto simp add: subequipotent_def)
qed

instance
  valtype \<subseteq> vcard
  apply (rule vcardI')
  apply (rule vinj_inj)
  done

lemma vcard_inj_ex: 
  "(\<exists> f::('a::vcard) \<rightarrow> VAL \<bullet> inj f)"
proof -
  from vcard obtain f where 
    "f \<in> \<univ>-['a] \<zinj> \<univ>-[VAL]"
    by (auto simp add: subequipotent_def)
  then have 
    b2: "inj (\<opof> f)"
    apply (intro fun_of_f_inj)
    apply (mauto(fspace))
    done
  then show 
    ?thesis 
    by (auto)
qed

text {*

While the existence on an injection is sufficient to provide 
the required type embedding @{text "\<vinj>"}
into @{text VAL} it is not sufficient to ensure that set and function
values can be used as value types. To ensure this we must introduce
stronger class restrictions, namely that the image of
the injection is completely enclosed in a single cartesion rank.
To achieve this we introduce another axiomatic class, the strong
value types @{text "svcard"}.

We require visibility of the rank structure of @{text VAL}, made invisible by the
type definition mechanism.

*}

definition
  vrank :: "CT \<rightarrow> VAL set"
where
  "vrank T \<defs> Abs_VAL\<lparr>\<chi>-[ind] T\<rparr>"

no_notation
  carrier_set ("\<chi>")

notation
  vrank ("\<chi>")

lemma vrank_disjoint: 
  "((\<chi> t_d_1) \<inter> (\<chi> t_d_2)) \<noteq> \<emptyset> \<Leftrightarrow> t_d_1 = t_d_2"
  apply (subst carrier_disjoint [symmetric])
  apply (auto simp add: vrank_def VAL.Abs_inject)
  done

lemma vrank_cover: 
  "\<univ>-[VAL] = \<Union> {t \<bullet> \<chi> t}"
proof -
  have 
    "\<univ>-[VAL]
    = Abs_VAL \<lparr>\<univ>-[ind cartuniv]\<rparr>"
    using VAL.Rep_inverse [symmetric]
    by (auto simp add: image_def)
  also  have 
    "\<univ>-[ind cartuniv]
    = \<Union> {t \<bullet> carrier_set t}"
    by (rule carrier_cover [where ?'a = "ind"])
  also have 
    "Abs_VAL \<lparr>\<Union> {t \<bullet> carrier_set t}\<rparr>
    = \<Union> {t \<bullet> \<chi> t}"
    by (auto simp add: vrank_def eind_def)
  finally show
    ?thesis
    by (this)
qed

lemma vrank_nemp: 
  "(\<exists> a \<bullet> a \<in> \<chi> T)"
proof -
  from carrier_nemp obtain x::"ind cartuniv" where
    "x \<in> carrier_set T"
    by (auto)
  then show
    "?thesis"
    apply (witness "Abs_VAL x")
    apply (auto simp add: vrank_def VAL.Rep_inverse)
    done
qed

lemma vrank_nuniv: 
  "(\<exists> a \<bullet> a \<notin> \<chi> T)"
proof -
  from carrier_nuniv obtain x::"ind cartuniv" where
    "x \<notin> carrier_set T"
    by (auto)
  then show
    "?thesis"
    apply (witness "Abs_VAL x")
    apply (elim contrapos_nn)
    apply (auto simp add: vrank_def image_def VAL.Abs_inject)
    done
qed

lemma vrank_eq: 
  assumes 
    a1: "a \<in> \<chi> s"
  shows 
    "a \<in> \<chi> t \<Leftrightarrow> t = s"
  apply (subst carrier_eq [of "Rep_VAL a", symmetric])
  using a1
  apply (auto simp add: vrank_def VAL.Abs_inverse)
  done

lemma vrankI: "(\<exists> t \<bullet> a \<in> \<chi> t)"
proof -
  from carrierI obtain t where
    "Rep_VAL a \<in> carrier_set t"
    by (auto)
  then show
    "(\<exists> t \<bullet> a \<in> \<chi> t)"
    apply (witness "t")
    apply (auto simp add: vrank_def image_def VAL.Rep_inverse)
    done
qed

lemma vrank_eqI: 
  assumes 
    a1: "a \<in> \<chi> s"
  shows 
    "a \<in> \<chi> t \<turnstile> t = s"
  by (simp add: vrank_eq [OF a1])

class
  svcard = typerep +
assumes
  svcard: "(\<exists> T \<bullet> \<^sEP>{:\<univ>-['a]:}{:\<chi> T:})"

instance 
  svcard \<subseteq> vcard
proof (intro_classes)
  from svcard obtain T where
    "\<^sEP>{:\<univ>-['a]:}{:\<chi> T:}"
    by (auto) 
  also have
    "\<^sEP>{:\<chi> T:}{:\<univ>-[VAL]:}"
    apply (rule subset_subequipotent)
    apply (auto)
    done
  finally show 
    "\<^sEP>{:\<univ>-['a]:}{:\<univ>-[VAL]:}"
    by (this)
qed

lemma svcardI': 
  fixes
    f::"'a \<rightarrow> VAL" and 
    T::CT
  assumes
    a1: "inj f" and 
    a2: "range f \<subseteq> \<chi> T"
  shows 
    "OFCLASS('a, svcard_class)"
proof (intro_classes)
  from a1 have 
    "(\<graphof> f) \<in> \<univ> \<zinj> \<univ>"
    by (rule graph_of_f_inj)
  with a2 have 
    "(\<graphof> f) \<in> \<univ> \<zinj> (\<chi> T)"
    apply (mauto(fspace))
    apply (auto simp add: graph_of_def glambda_ran)
    done
  then show
    "(\<exists> T \<bullet> \<^sEP>{:\<univ>-['a]:}{:\<chi> T:})"
    by (auto simp add: subequipotent_def)
qed

lemma svcard_inj_ex: 
  "(\<exists> f::('a::svcard) \<rightarrow> VAL \<bullet> inj f \<and> (\<exists> T \<bullet> range f \<subseteq> \<chi> T))" (is "(\<exists> f \<bullet> ?P f)")
proof -
  from svcard obtain f T where 
    b1: "f \<in> \<univ>-['a] \<zinj> (\<chi> T)"
    by (auto simp add: subequipotent_def)
  then have 
    b2: "inj (\<opof> f)"
    apply (intro fun_of_f_inj)
    apply (mauto(fspace))
    done
  from b1 have 
    b3: "range (\<opof> f) \<subseteq> \<chi> T"
    by (auto)
  from b2 b3 have 
    "?P (\<opof> f)"
    by (auto)
  then show 
    ?thesis 
    by (auto)
qed

text {*

On the basis of the class constraints on @{text "vcard"}, we are able
to introduce a default value injection for each such type.
Since the exact value of this injection is unimportant, we define it 
through the Hilbert choice operator, requiring only that it be
injective and that where possible its range has a uniform Cartesian type.

*}

context typerep

begin

definition
  cinj :: "'a \<rightarrow> VAL"
where
  cinj_typerep_def: "cinj \<defs> 
    \<if> (\<exists> T \<bullet> \<^sEP>{:\<univ>-['a]:}{:\<chi> T:}) \<then>
      (\<some> f | inj f \<and> (\<exists> T \<bullet> range f \<subseteq> \<chi> T))
    \<elif> \<^sEP>{:\<univ>-['a]:}{:\<univ>-[VAL]:} \<then> 
      (\<some> f | inj f)
    \<else>
      (\<some> f | range f = \<univ>-[VAL])
    \<fi>"

end

context vcard

begin

lemma cinj_vcard_cases:
  "cinj = (\<some> f | inj f) \<or> (\<exists> T \<bullet> \<^sEP>{:\<univ>-['a]:}{:\<chi> T:} \<and> cinj = (\<some> f | inj f \<and> (\<exists> T \<bullet> range f \<subseteq> \<chi> T)))"
  using vcard
  by (simp add: cinj_typerep_def)

lemma cinj_inj: 
  "inj cinj"  (is "?P cinj")
  using cinj_vcard_cases
  apply (msafe(inference))
proof -
  from vcard obtain f where 
   "f \<in> \<univ>-['a] \<zinj> \<univ>-[VAL]"
    by (auto simp add: subequipotent_def)
  then have 
    b2: "inj (\<opof> f)"
    apply (intro fun_of_f_inj)
    apply (mauto(fspace))
    done
  assume
    b3: "cinj = (\<some> f | ?P f)"
  from b2 show 
    "inj cinj"
    apply (simp add: b3)
    by (rule someI [of ?P])
next
  fix
    T
  assume
    b1: "\<^sEP>{:\<univ>-['a]:}{:\<chi> T:}" and
    b2: "cinj = (\<some> f | inj f \<and> (\<exists> T \<bullet> range f \<subseteq> \<chi> T))" (is "cinj = (\<some> f | ?Q f)")
  from b1 obtain f where 
    b3: "f \<in> \<univ>-['a] \<zinj> \<chi> T"
    by (auto simp add: subequipotent_def)
  then have 
    b4: "inj (\<opof> f)"
    apply (intro fun_of_f_inj)
    apply (mauto(fspace))
    done
  from b3 have 
    b5: "range (\<opof> f) \<subseteq> \<chi> T"
    by (auto)
  from b4 b5 have 
    "?Q (\<opof> f)"
    by (auto)
  then have 
    "?Q cinj"    
    apply (simp add: b2)
    by (rule someI [of ?Q])
  then show
    "?P cinj"
    by (auto)
qed

end

abbreviation
  scinj :: "('a::svcard) \<rightarrow> VAL"
where
  "scinj \<defs> cinj"

lemma
  scinj_def: "scinj = (\<some> f | inj f \<and> (\<exists> T \<bullet> range f \<subseteq> \<chi> T))"
  using svcard
  by (auto simp add: cinj_typerep_def)

definition
  scCT_of :: "('a::svcard) itself \<rightarrow> CT"
where
  scCT_of_def: "scCT_of TYPE('a::svcard) \<defs> (\<mu> T | range (scinj::'a \<rightarrow> VAL) \<subseteq> \<chi> T)"

syntax (zed)
  "_scCT" :: "logic" ("\<^scCT>")
  "_scCTa" :: "type \<rightarrow> logic" ("\<^scCT>[:_:]")

translations
  "\<^scCT>" \<rightharpoonup> "CONST Value_Types.scCT_of \<arb>"
  "\<^scCT>[:'a:]" \<rightharpoonup> "CONST Value_Types.scCT_of TYPE('a)"

lemma scinj_char: 
    "inj scinj-['a::svcard] \<and> (\<exists> T \<bullet> range scinj-['a::svcard] \<subseteq> \<chi> T)" 
      (is "?P scinj")
proof (unfold scinj_def)
  from svcard obtain f T where b1: "f \<in> \<univ>-['a] \<zinj> \<chi> T"
    by (auto simp add: subequipotent_def)
  then have b2: "inj (\<opof> f)"
    apply (intro fun_of_f_inj)
    apply (mauto(fspace))
    done
  from b1 have b3: "range (\<opof> f) \<subseteq> \<chi> T"
    by (auto)
  from b2 b3 have "?P (\<opof> f)"
    by (auto)
  then show "?P (\<some> f | ?P f)"
    by (rule someI [of ?P])
qed

lemma scinj_inj: 
  "inj scinj"
  by (simp add: cinj_inj)

lemma scinj_bound_inj': 
  "(\<exists>\<subone> T \<bullet> range scinj  \<subseteq> \<chi> T)"
proof -
  from scinj_char
  obtain T where b1: "range scinj-['a]  \<subseteq> \<chi> T"
    by (auto)
  show "\<exists>\<subone> T \<bullet> range scinj-['a]  \<subseteq> \<chi> T"
  proof (rule ex1I)
    from b1 show "range scinj-['a]  \<subseteq> \<chi> T"
      by (this)
  next
    fix S
    assume c1: "range scinj-['a] \<subseteq> \<chi> S"
    with b1 have "scinj-['a] \<arb> \<in> \<chi> S" "scinj-['a] \<arb> \<in> \<chi> T"
      by (auto)
    then have "\<chi> S \<inter> \<chi> T \<noteq> \<emptyset>"
      by (auto)
    then show "S = T"
      by (simp add: vrank_disjoint)
  qed
qed

lemma scinj_bound_inj: 
  "(\<exists> T \<bullet> range scinj \<subseteq> \<chi> T)"
  using scinj_bound_inj'
  by (auto)

lemma scinj_bound_scCT: 
  "range (scinj-['a::svcard]) \<subseteq> \<chi> \<^scCT>[:'a::svcard:]"
  apply (simp add: scCT_of_def)
  apply (rule theI' [OF scinj_bound_inj'])
  done

text {* 

The @{text "svcard"} class has strong enough properties to ensure
closure under the set and function type constructors and we can thus
show that it encompasses the entirety of the base HOL type algebra.

We also find it useful to introduce a strengthened version of 
@{text "valtype"} where the range on the value injection is
contained in a single rank.

*}

class
  svaltype = valtype +
assumes
  bound_vinj: "\<exists> T \<bullet> range \<vinj> \<subseteq> (\<chi> T)"

instance
  svaltype \<subseteq> svcard
proof (intro_classes)
  from bound_vinj obtain T where 
    "range \<vinj>-['a] \<subseteq> (\<chi> T)"
    by (auto)
  with vinj_inj [THEN graph_of_f_inj]
  have 
    "(\<graphof> \<vinj>-['a]) \<in> \<univ>-['a] \<zinj> (\<chi> T)"
    apply (mauto(fspace))
    apply (auto simp add: graph_of_def glambda_def Range_def Domain_def) 
    done
  then show 
    "(\<exists> T \<bullet> \<^sEP>{:\<univ>-['a]:}{:((\<chi> T)::VAL set):})"
    by (auto simp add: subequipotent_def)
qed

lemma svaltype_bound_unique: 
  "(\<exists>\<subone> T \<bullet> range \<vinj>-['a::svaltype] \<subseteq> (\<chi> T))"
proof -  
  show 
    ?thesis
    apply (intro ex_ex1I [OF bound_vinj] vrank_disjoint [THEN iffD1])
  proof -
    fix T_d_1 T_d_2
    assume 
      c1: "range \<vinj>-['a] \<subseteq> (\<chi> T_d_1)" "range \<vinj>-['a] \<subseteq> (\<chi> T_d_2)"
    obtain x where 
      c2: "x \<in> \<univ>-['a]" 
      by (auto)
    from c1 c2 have 
      c3: "\<vinj> x \<in> \<chi> T_d_1"
      by (auto)
    from c1 c2 have 
      c4: "\<vinj> x \<in> \<chi> T_d_2"
      by (auto)
    from c3 c4 show 
      "\<chi> T_d_1 \<inter> \<chi> T_d_2 \<noteq> \<emptyset>"
      apply (simp add: nempty_conv)
      apply (auto)
      done
  qed
qed


text {* 

The image of any element under @{text "\<vinj>"} has a unique Cartesian
type, so we can uniquely associate each object of class @{text "vtype"} with
a Cartesian type.

*}

definition
  CT_of_val :: "('a::vtype) \<rightarrow> CT"
where
  CT_of_val_def: "CT_of_val x \<defs> (\<mu> t | \<vinj> x \<in> \<chi> t)"

text {*

The range of any type in class @{text "svaltype"} is contained in a Cartesion type.

*}

definition
  CT_of :: "('a::svaltype) itself \<rightarrow> CT"
where
  CT_of_def: "CT_of TYPE('a::svaltype) \<defs> (\<mu> t | range \<vinj>-['a] \<subseteq> \<chi> t)"

syntax
  "_CT" :: "type \<rightarrow> logic" ("\<^CT>{:_:}")

translations
  "\<^CT>{:'a:}" \<rightleftharpoons> "CONST Value_Types.CT_of TYPE('a)"

lemma CT_of_val_char: 
  "\<vinj> x \<in> \<chi> (CT_of_val x)" (is "?P (CT_of_val x)")
proof -
  from vrankI obtain t where 
    b1: "\<vinj> x \<in> \<chi> t"
    by (auto)
  with vrank_eq 
  show 
    "?thesis"
    by (auto intro!: theI [of "?P"] simp add: CT_of_val_def)
qed

text {*

We note that the elements of an @{text "svaltype"} type have uniform
Cartesian type.

*}

lemmas CT_of_char = svaltype_bound_unique [THEN theI', folded CT_of_def]

lemmas CT_of_unique = the1_equality [OF svaltype_bound_unique, symmetric, folded CT_of_def]

lemma CT_of_val_eq: 
  fixes 
    x::"'a::svaltype"
  shows 
    "CT_of_val x = \<^CT>{:'a:}"
proof -
  from bound_vinj obtain T where 
    b1: "range \<vinj>-['a] \<subseteq> \<chi> T"
    by (auto)
  from b1 have 
    b2: "\<vinj> x \<in> \<chi> T"
    by (auto)
  from CT_of_val_char [of "x"] CT_of_unique [OF b1] vrank_eq [OF b2] show
    ?thesis
    by (auto simp add: eind_def)
qed

lemma CT_of_char': 
  fixes 
    "x"::"'a::svaltype"
  shows
    "\<vinj> x \<in> \<chi> \<^CT>{:'a::svaltype:}"
  using CT_of_val_char [of "x"]
  by (simp add: CT_of_val_eq)

lemma CT: 
  "range \<vinj>-['a::svaltype] \<subseteq> \<chi> \<^CT>{:'a::svaltype:}"
  by (rule CT_of_char)

lemma CT': 
  "(\<exists> T \<bullet> range \<vinj>-['a::vtype] \<subseteq> \<chi> T) \<turnstile> range \<vinj>-['a::vtype] \<subseteq> \<chi> (CT_of_val (a::'a))"
proof (msafe_no_assms(inference))
  fix T assume 
    b1: "range \<vinj>-['a] \<subseteq> \<chi> T"
  show 
    "range \<vinj>-['a] \<subseteq> \<chi> (CT_of_val a)"
  proof (auto)
    fix x::'a
    from b1 have 
      c1: "\<vinj>-['a] x \<in> \<chi> T" and 
      c2: "\<vinj>-['a] a \<in> \<chi> T"
      by (auto)
    from CT_of_val_char [of "x"] CT_of_val_char [of "a"] 
      vrank_eq [OF c1] vrank_eq [OF c2] b1
    have 
      "T = CT_of_val a"
      by (auto)
    with c1 show 
      "\<vinj>-['a] x \<in> \<chi> (CT_of_val a)"
      by (simp)
  qed
qed

lemma ransvinj_nuniv: 
  "(\<exists> a \<bullet> a \<notin> range \<vinj>-['a::svaltype])"
proof -
  have 
    "(\<exists> T \<bullet> range \<vinj>-['a] \<subseteq> \<chi> T)" 
    by (rule bound_vinj)
  also have 
    "(\<exists> T \<bullet> range \<vinj>-['a] \<subseteq> \<chi> T)
    \<Leftrightarrow> (\<exists> T \<bullet> range \<vinj>-['a] \<subseteq> \<chi> T \<and> (\<exists> a::VAL \<bullet> a \<notin> \<chi> T))"
    by (auto intro!: vrank_nemp vrank_nuniv)
  also have "\<dots>
    \<Leftrightarrow> (\<exists> T (a::VAL) \<bullet> range \<vinj>-['a] \<subseteq> \<chi> T \<and> a \<notin> \<chi> T)"
    by (auto)
  also have "\<dots>
    \<Rightarrow> (\<exists> T (a::VAL) \<bullet> range \<vinj>-['a] \<subseteq> \<chi> T \<and> a \<notin> range \<vinj>-['a])"
    by (mauto(wind))
  finally show 
    "(\<exists> (a::VAL) \<bullet> a \<notin> range \<vinj>-['a])"
    by (auto)
qed

lemma CT_eq:
  assumes
    a1: "range \<vinj>-['a::svaltype] \<subseteq> \<chi> T"
  shows
    "\<^CT>{:'a:} = T"
  by (simp add: CT_of_unique [OF a1])

subsection {* Cartesion constructors *}

text {*

We pause to lift the @{text cartuniv} rank constructors to @{text "VAL"}.

*}

definition
  vatom_of :: "ind => VAL" 
where
  "vatom_of i \<defs> Abs_VAL (atom_of i)"

definition
  vset_of :: "[CT, VAL set] \<rightarrow> VAL" 
where
  "vset_of T CL_V \<defs> Abs_VAL (set_of T Rep_VAL\<lparr>CL_V\<rparr>)"

definition
  vprod_of :: "(VAL \<times> VAL) \<rightarrow> VAL" 
where
  "vprod_of uv \<defs> Abs_VAL (prod_of (Rep_VAL (fst uv), Rep_VAL (snd uv)))"

lemma vrank_catom:
  "\<chi> catom = vatom_of\<lparr>UNIV-[ind]\<rparr>"
  by (auto simp add: vatom_of_def vrank_def image_def chi_catom_mem)

lemma vrank_cset:
  "\<chi> (cset T) = (vset_of T)\<lparr>\<pset> (\<chi> T)\<rparr>"
  apply (simp add: vrank_def vset_of_def [abs_def] Pow_image image_comp_dist chi_cset image_dist [of "(\<olambda> CL_V \<bullet> Abs_VAL (set_of T CL_V))" "image Rep_VAL"] image_dist [of "Abs_VAL" "set_of T"])
  apply (simp add: image_aggregate VAL.Abs_inverse_raw image_id)
  done

lemma vrank_cprod:
  "\<chi> (cprod T S) = vprod_of\<lparr>(\<chi> T) \<times> (\<chi> S)\<rparr>"
  apply (simp add: vrank_def chi_cprod vprod_of_def [abs_def] image_comp_dist image_dist [of "Abs_VAL" "(\<olambda> uv \<bullet> prod_of (Rep_VAL (fst uv), Rep_VAL (snd uv)))"] image_dist [of "prod_of" "(\<olambda> uv \<bullet> (Rep_VAL (fst uv), Rep_VAL (snd uv)))"] map_pair_def [symmetric, simplified split_def] image_map_pair)
  apply (simp add: image_aggregate VAL.Abs_inverse_raw)
  done

lemma vprod_of_split:
  "vprod_of (u, v) = Abs_VAL (prod_of (Rep_VAL u, Rep_VAL v))"
  by (auto simp add: vprod_of_def)

lemma inj_vatom_of: 
  "inj vatom_of"
  using inj_atom_of [where ?'a = "ind", THEN injD] VAL.Abs_inject
  by (auto intro!: injI simp add: vatom_of_def)

lemmas vatom_of_eq = inj_vatom_of [THEN inj_eq]

lemma inj_vprod_of: 
  "inj vprod_of"
  apply (rule injI)
  using inj_prod_of [where ?'a = "ind", THEN inj_eq] VAL.Abs_inject VAL.Rep_inject
  apply (auto simp add: vprod_of_split)
  done

lemmas vprod_of_eq = inj_vprod_of [THEN inj_eq]

lemma vset_of_eq: 
  "vset_of s A = vset_of t B \<Leftrightarrow> s = t \<and> A \<inter> \<chi> s = B \<inter> \<chi> t"
  apply (simp add: vset_of_def vrank_def VAL.Abs_inject set_of_eq)
  apply (subst VAL.Rep_image_eq_iff [symmetric])
  apply (simp add: VAL.Rep_image_Int VAL.Abs_inverse_image)
  done

lemma inj_on_vset_of_t: 
  "inj_on (vset_of t) (\<pset> (\<chi> t))"
  apply (rule inj_onI)
  apply (auto simp add: vset_of_eq)
  done

lemma vatom_of_rank:  
  "vatom_of i \<in> \<chi> catom"
  by (auto simp add: vatom_of_def vrank_def image_def chi_catom_mem)

lemma vprod_of_rank:
  assumes 
    a1: "a \<in> \<chi> T" and
    a2: "b \<in> \<chi> S"
  shows 
    "vprod_of (a, b) \<in> \<chi> (cprod T S)"
proof -
  from a1 a2 have
    b1: "(Rep_VAL a, Rep_VAL b) \<in> carrier_set T \<times> carrier_set S"
    by (auto simp add: vrank_def VAL.Abs_inverse)
  from prod_of_char [OF b1] show
    "?thesis"
    by (simp add: vprod_of_def vrank_def)
qed

lemma vprod_of_rank':
  assumes 
    a1: "ab \<in> \<chi> T \<times> \<chi> S"
  shows 
    "vprod_of ab \<in> \<chi> (cprod T S)"
  using a1 vprod_of_rank [of "fst ab" _ "snd ab"]
  by (auto)

lemma vset_of_rank:
  assumes 
    a1: "S \<subseteq> \<chi> t"
  shows 
    "vset_of t S \<in> \<chi> (cset t)"
proof -
  from a1 have
    b1: "Rep_VAL\<lparr>S\<rparr> \<subseteq> carrier_set t"
    by (simp add: vrank_def VAL.Rep_image_connect)
  from set_of_char [OF b1] show
    "?thesis"
    by (simp add: vset_of_def vrank_def)
qed

subsection {* Some basic @{text vtype} instance proofs *}

text {*

Firstly, we observe the @{text "\<bool>"} and @{text ind} are in @{text svcard} 
and that the @{text set} and @{text "\<times>"} constructors preserve
@{text svcard}.

*}

instance
  bool :: svcard
proof (intro_classes)
  let ?f = "(\<olambda> b::\<bool> \<bullet> \<if> b \<then> vatom_of (Suc_Rep Zero_Rep) \<else> vatom_of Zero_Rep \<fi>)"
  note Suc_Rep_not_Zero_Rep [of Zero_Rep]
  then have 
    b1: "inj ?f" 
    by (auto simp add: inj_on_def inj_vatom_of [THEN inj_eq]) -- "@{text atom_of} primrec"
  have 
    "range ?f \<subseteq> \<chi> catom"
    by (auto simp add: vatom_of_rank)
  with graph_of_f_inj [OF b1]
  show 
    "(\<exists> T \<bullet> \<^sEP>{:\<univ>-[\<bool>]:}{:((\<chi> T)::VAL set):})"
    apply (witness "catom")
    apply (simp add: subequipotent_def)
    apply (witness "\<graphof> ?f")
    apply (mauto(fspace))
    apply (auto simp add: graph_of_def glambda_ran eind_def)
    done
qed

text {* 

The next step is to define a value injection for @{text "\<bool>"} and
to show that it is a bound injection. Since we have no particular need to
control the value of the Boolean value injection, we use it as a demonstration of
our general approach to defining the value injection, setting it equal to 
@{text scinj}.

*}

instantiation (* type: bool *)
  bool :: svaltype
begin

definition
  bool_vinj_def: "\<vinj>-[\<bool>] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: bool_vinj_def)
  done

end

text {*

This same technique, with essentially the same strong value type
instance proof can be used for any strong cardinality type.

Next we consider the individuals, a type which we do want to have control
over the value injection since we wish to have the basic Cartesian
universe types mapped to their natural image in @{text VAL}. Since, we
wish to separately define the value injection, we directly show that 
@{text ind} is in @{text svaltype}, thus indirectly establishing its
membership of @{text svcard}.

*}

instantiation (* type: Nat.ind *)
  Nat.ind :: svaltype
begin

definition
  ind_vinj_def: "\<vinj>-[ind] \<defs> vatom_of"

instance 
proof (intro_classes, unfold ind_vinj_def)
  show "inj vatom_of"
    by (rule inj_vatom_of)
  show "\<exists> T \<bullet> range vatom_of \<subseteq> \<chi> T"
    apply (witness "catom")
    apply (auto simp add: vatom_of_rank)
    done
qed

end

lemma CT_ind:
  "\<^CT>{:ind:} = catom"
  apply (rule CT_eq)
  apply (auto simp add: ind_vinj_def vatom_of_rank)
  done

text {*

We use similar techniques for both the set constructor and the product
constructor, though we also show that products preserve @{text valtype} as
well.

*}

lemma vprod_card:
  fixes 
    f_d_1::"'a_d_1 \<rightarrow> VAL" and 
    f_d_2::"'a_d_2 \<rightarrow> VAL" and 
    T_d_1::CT and 
    T_d_2::CT
  assumes 
    a1: "inj f_d_1" "inj f_d_2" and 
    a2: "range f_d_1 \<subseteq> (\<chi> T_d_1)" "range f_d_2 \<subseteq> (\<chi> T_d_2)"
  shows 
    "inj (\<olambda> (x_d_1, x_d_2) \<bullet>  vprod_of (f_d_1 x_d_1, f_d_2 x_d_2)) \<and> 
    range (\<olambda> (x_d_1, x_d_2) \<bullet> vprod_of (f_d_1 x_d_1, f_d_2 x_d_2)) \<subseteq> \<chi> (cprod T_d_1 T_d_2)" 
    (is "inj ?f \<and> range ?f \<subseteq> \<chi> ?T")
proof (msafe_no_assms(inference))
  show "inj ?f"
    apply (rule inj_onI)
    apply (auto intro: a1 [THEN inj_onD] simp add: vprod_of_eq)
    done
  from a2 show "range ?f \<subseteq> \<chi> ?T" 
    by (auto simp add: image_def subset_def vrank_cprod vprod_of_def)
qed

instance 
  prod :: (svcard, svcard) svcard
proof -
  have b1: "inj scinj-['a]" "inj scinj-['b]"
    by (auto intro!: scinj_inj)
  have b2: "(\<exists> T \<bullet> range scinj-['a] \<subseteq> \<chi> T)" "(\<exists> T \<bullet> range scinj-['b] \<subseteq> \<chi> T)"
    by (auto intro!: scinj_bound_inj)
  from vprod_card [OF b1 b2 [THEN someI_ex]] 
  show "OFCLASS('a \<times> 'b, svcard_class)"
    apply (intro svcardI')
    apply (mauto(inference))
    done
qed

instantiation (* type: * *)
  prod :: (svaltype, svaltype) svaltype
begin

definition
  prod_vinj_def: "\<vinj>-['a \<times> 'b] \<defs> (\<olambda> (a, b) \<bullet> vprod_of (\<vinj> a, \<vinj> b))"

instance
proof (intro_classes)
  have b1: 
    "range \<vinj>-['a] \<subseteq> \<chi> (\<mu> T | range \<vinj>-['a] \<subseteq> \<chi> T)" 
    "range \<vinj>-['b] \<subseteq> \<chi> (\<mu> T | range \<vinj>-['b] \<subseteq> \<chi> T)"
    apply (rule svaltype_bound_unique [THEN theI'])
    apply (rule svaltype_bound_unique [THEN theI'])
    done
  from vprod_card [OF vinj_inj vinj_inj b1]
  show "inj \<vinj>-['a \<times> 'b]" 
    by (auto simp add: prod_vinj_def)
  from vprod_card [OF vinj_inj vinj_inj b1]
  show "\<exists> T \<bullet> range \<vinj>-['a \<times> 'b] \<subseteq> \<chi> T"
    apply (msafe_no_assms(inference))
    apply (witness "cprod (\<mu> T | range \<vinj>-['a] \<subseteq> \<chi> T) (\<mu> T | range \<vinj>-['b] \<subseteq> \<chi> T)")
    apply (simp add: prod_vinj_def)
    done
qed

end

lemma CT_prod: 
  "\<^CT>{:('a::svaltype) \<times> ('b::svaltype):} = cprod \<^CT>{:'a::svaltype:} \<^CT>{:'b::svaltype:}"
proof -
  have b1: "range \<vinj>-['a] \<subseteq> \<chi> \<^CT>{:'a:}"
    by (rule CT)
  have b2: "range \<vinj>-['b] \<subseteq> \<chi> \<^CT>{:'b:}"
    by (rule CT)
  from b1 b2 show ?thesis
    apply (intro CT_eq)
    apply (auto simp add: prod_vinj_def image_def subset_def vrank_cprod)
    done
qed


text {*

A prime driver in our development of the value types classes is to ensure that the function embedding can be properly understood at the @{text "VAL"} level, even in the absence of knowledge of the underlying domain and range types. 
To achieve this we need to craft the value embedding to a particular form. 
This form is based on functional graphs with uniformly ranked domain and range. 
Such graphs can be embedding in @{text "VAL"} as a relation ranked value and a suitable application operator defined.

We start by using the domain and range type embeddings to construct a graph over @{text "VAL"}. 

*}

definition
  VAL_graph :: "(('a::svaltype) \<rightarrow> ('b::svaltype)) \<rightarrow> (VAL \<leftrightarrow> VAL)"
where
  VAL_graph_def: "VAL_graph f \<defs> { a \<bullet> (\<vinj>-['a] a, \<vinj>-['b] (f a)) }"

lemma VAL_graph_dom_char:
  "\<zdom> (VAL_graph-['a::svaltype,'b::svaltype] f) \<subseteq> \<chi> \<^CT>{:'a::svaltype:}"
  by (auto intro: CT_of_char' simp add: VAL_graph_def)

lemma VAL_graph_ran_char:
  "\<zran> (VAL_graph (f::('a::svaltype) \<rightarrow> ('b::svaltype))) \<subseteq> \<chi> \<^CT>{:'b::svaltype:}"
  by (auto intro: CT_of_char' simp add: VAL_graph_def)

lemma VAL_graph_rel: 
  "VAL_graph (f::('a::svaltype) \<rightarrow> ('b::svaltype)) \<in> \<chi> \<^CT>{:'a::svaltype:} \<zrel> \<chi> \<^CT>{:'b::svaltype:}"
  apply (mauto(fspace))
  apply (intro VAL_graph_dom_char VAL_graph_ran_char)+
  done

lemma VAL_graph_functional:
  "functional (VAL_graph f)"
proof -
  have 
    b1: "inj \<vinj>-['a]" 
    by (rule vinj_inj)
  have 
    b2: "inj \<vinj>-['b]" 
    by (rule vinj_inj)
  show ?thesis
    by (auto intro!: functionalI simp add: VAL_graph_def inj_eq [OF b1] inj_eq [OF b2])
qed

lemma VAL_graph_beta:
  "(VAL_graph (f::('a::svaltype) \<rightarrow> ('b::svaltype)))\<cdot>(\<vinj>-['a::svaltype] x) = \<vinj>-['b::svaltype] (f x)"
  apply (rule functional_beta)
  apply (rule VAL_graph_functional)
  apply (auto simp add: VAL_graph_def)
  done

lemma VAL_graph_tfun: 
  "VAL_graph (f::('a::svaltype) \<rightarrow> ('b::svaltype)) \<in> (range \<vinj>-['a::svaltype]) \<ztfun> (range \<vinj>-['b::svaltype])"
proof -
  show ?thesis
    apply (mauto(fspace))
    apply (rule VAL_graph_functional)
    apply (auto simp add: VAL_graph_def prod_vinj_def eind_def)
    done
qed

lemma range_VAL_graph_is_tfun:
  "range VAL_graph-['a::svaltype, 'b::svaltype] = (range \<vinj>-['a::svaltype]) \<ztfun> (range \<vinj>-['b::svaltype])"
  apply (auto)
  apply (rule VAL_graph_tfun)
proof -
  fix 
    f 
  assume
    b1: "f \<in> (range \<vinj>-['a::svaltype]) \<ztfun> (range \<vinj>-['b::svaltype])"
  have 
    b2: "VAL_graph (\<olambda> x \<bullet> \<vproj>-['b] (f\<cdot>(\<vinj>-['a] x))) \<in> range VAL_graph-['a::svaltype, 'b::svaltype]"
    by (rule rangeI)
  have 
    b3: "VAL_graph (\<olambda> x \<bullet> \<vproj>-['b] (f\<cdot>(\<vinj>-['a] x))) \<in> (range \<vinj>-['a::svaltype]) \<ztfun> (range \<vinj>-['b::svaltype])"
    by (rule VAL_graph_tfun)
  have 
    b4: "f = VAL_graph (\<olambda> x \<bullet> \<vproj>-['b] (f\<cdot>(\<vinj>-['a] x)))"
    apply (rule tfun_eqI [OF b1 b3])
    apply (rule tfun_beta [OF b3, symmetric])
    apply (auto simp add: VAL_graph_def vproj_inverse [OF tfun_range [OF b1]])
    done
  then show
    "f \<in> range VAL_graph-['a::svaltype, 'b::svaltype]"
    by (simp add: rangeI)
qed

lemma VAL_graph_inj: 
  "inj VAL_graph-['a::svaltype,'b::svaltype]"
proof (rule injI)
  fix f g
  assume c1: "VAL_graph-['a,'b] f = VAL_graph-['a,'b] g"
  note c3 = VAL_graph_functional [of "f"]
  show "f = g"
  proof (rule ext)
    fix x
    have d1: "(\<vinj>-['a] x, \<vinj>-['b] (f x)) \<in> VAL_graph f"
      by (auto simp add: VAL_graph_def)
    have d2: "(\<vinj>-['a] x, \<vinj>-['b] (g x)) \<in> VAL_graph f"
      apply (simp add: c1)
      apply (auto simp add: c1 VAL_graph_def)
      done
    from c3 [THEN functionalD, OF d1 d2]
    have "\<vinj>-['b] (f x) = \<vinj>-['b] (g x)"
      by (this)
    with vinj_inj [THEN injD]
    show "f x = g x"
      by (auto)
  qed
qed

text {* 

We directly prove that @{text "VAL_graph"} induces an appropriate embedding for function types.

*}

definition
  graph_VAL :: "[CT, CT, (VAL \<leftrightarrow> VAL)] \<rightarrow> VAL"
where
  "graph_VAL T T' \<defs> Abs_VAL \<circ> (graph_CU T T') \<circ> image (Rep_VAL \<par> Rep_VAL)"

lemma graph_VAL_vrank:
  assumes
    a1: "R \<in> \<chi> T \<zrel> \<chi> T'"
  shows
    "graph_VAL T T' R \<in> \<chi> (cset (cprod T T'))"
proof -
  from a1 have
    "image (Rep_VAL \<par> Rep_VAL) R \<in> carrier_set T \<zrel> carrier_set T'"
    apply (auto simp add: vrank_def rel_def subset_def image_def)
    apply (auto elim!: allE impE simp add: VAL.Abs_inverse)
    done
  then have
    "((graph_CU T T') \<circ> image (Rep_VAL \<par> Rep_VAL)) R \<in> carrier_set (cset (cprod T T'))"
    by (simp add: graph_CU_char)
  then have
    "(Abs_VAL \<circ> (graph_CU T T') \<circ> image (Rep_VAL \<par> Rep_VAL)) R \<in> \<chi> (cset (cprod T T'))"
    by (simp add: vrank_def)
  then show 
    "?thesis"
    by (simp add: graph_VAL_def)
qed
  
lemma map_pair_inj:
  assumes 
    a1: "inj f" and
    a2: "inj g"
  shows 
    "inj (f \<par> g)"
  using a1 [THEN injD] a2 [THEN injD]
  by (auto intro!: injI simp add: map_pair_def)

lemma image_inj:
  assumes 
    a1: "inj f"
  shows
    "inj (image f)"
proof (rule injI)
  fix
    X Y
  assume
    b1: "f\<lparr>X\<rparr> = f\<lparr>Y\<rparr>"
  show
    "X = Y"
    apply (simp add: set_eq_iff)
    apply (rule allI)
  proof -
    fix
      x
    have
      "x \<in> X
      \<Leftrightarrow> f x \<in> f\<lparr>X\<rparr>"
      using a1 [THEN injD]
      by (auto simp add: image_conv)
    also have "\<dots>
      \<Leftrightarrow> f x \<in> f\<lparr>Y\<rparr>"
      by (simp add: b1)
    also have "\<dots>
      \<Leftrightarrow> x \<in> Y"
      using a1 [THEN injD]
      by (auto)
    finally show
      "x \<in> X \<Leftrightarrow> x \<in> Y"
      by (this)
  qed
qed

lemma graph_VAL_inj:
  "inj_on (graph_VAL T T') (\<chi> T \<zrel> \<chi> T')"
  unfolding graph_VAL_def
  apply (rule comp_inj_on [OF _ comp_inj_on])
proof -
  show
    "inj_on (image (Rep_VAL \<par> Rep_VAL)) (\<chi> T \<zrel> \<chi> T')"
    apply (rule subset_inj_on)
    apply (rule image_inj)
    apply (rule map_pair_inj)
    apply (intro VAL.Rep_inj)+
    apply (auto)
    done
  have
    b1 [rule_format]: "(\<forall> R | R \<in> \<chi> T \<zrel> \<chi> T' \<bullet> (image (Rep_VAL \<par> Rep_VAL)) R \<in> (carrier_set T) \<zrel> (carrier_set T'))"
    apply (auto simp add: vrank_def rel_def image_def map_pair_def subset_def)
    apply (auto elim!: allE impE simp add: VAL.Abs_inverse)
    done
  show
    "inj_on (graph_CU T T') (image (Rep_VAL \<par> Rep_VAL))\<lparr>\<chi> T \<zrel> \<chi> T'\<rparr>"
    apply (rule inj_onI)
    apply (elim imageE)
    apply (simp add: graph_CU_eq b1)
    done
  show
    "inj_on Abs_VAL ((graph_CU T T')\<lparr>(image (Rep_VAL \<par> Rep_VAL))\<lparr>\<chi> T \<zrel> \<chi> T'\<rparr>\<rparr>)"
    apply (rule subset_inj_on)
    apply (rule VAL.Abs_inj)
    apply (auto)
    done
qed

lemma set_card:
  fixes f::"'a \<rightarrow> VAL" and T::CT
  assumes a1: "inj f" and a2: "range f \<subseteq> (\<chi> T::VAL set)"
  shows "inj (\<olambda> X \<bullet> vset_of T (f\<lparr>X\<rparr>)) \<and> range (\<olambda> X \<bullet> vset_of T (f\<lparr>X\<rparr>)) \<subseteq> \<chi> (cset T)"
proof (msafe_no_assms(inference))
  let ?set_of = "(vset_of T)::VAL set \<rightarrow> VAL"
  let ?vinjimage = "\<olambda> X::('a set) \<bullet> f\<lparr>X\<rparr>"
  let ?g = "\<olambda> X::('a set) \<bullet> ?set_of (?vinjimage X)"
  have b1: "inj ?vinjimage"
  proof (intro inj_onI)
    fix X Y 
    assume c1: "f\<lparr>X\<rparr> = f\<lparr>Y\<rparr>"
    then have "(inv f)\<lparr>f\<lparr>X\<rparr>\<rparr> = (inv f)\<lparr>f\<lparr>Y\<rparr>\<rparr>"
      by (simp)
    then have "((inv f) \<circ> f)\<lparr>X\<rparr> = ((inv f) \<circ> f)\<lparr>Y\<rparr>"
      by (simp add: image_compose)
    then show "X = Y"
      by (simp add: inj_iff [THEN iffD1, OF a1]) 
  qed
  from a2 have b2: "range ?vinjimage \<subseteq> \<pset> (\<chi> T)"
    by (auto)
  have b3: "inj (?set_of \<circ> ?vinjimage)" 
    apply (intro comp_inj_on)
    apply (rule b1)
    apply (rule subset_inj_on)
    apply (rule inj_on_vset_of_t)
    apply (rule b2)
    done
  then show "inj ?g"
    by (simp add: o_def)
  have "range ?g = (vset_of T)\<lparr>(range ?vinjimage)\<rparr>"
  by auto
  then show "range ?g \<subseteq> \<chi> (cset T)"
    apply (simp add: vrank_cset)
    apply (rule image_mono)
    apply (rule b2)
    done
qed

instantiation (* type: set *)
  "set" :: (svaltype) svaltype
begin

definition
  set_vinj_def: "\<vinj>-['a set] \<defs> (\<olambda> X \<bullet> vset_of \<^CT>{:'a:} (\<vinj>-['a]\<lparr>X\<rparr>))"

instance
proof (intro_classes)
  have 
    b1: "range \<vinj>-['a] \<subseteq> \<chi> \<^CT>{:'a:}"
    by (rule CT_of_char)
  from set_card [OF vinj_inj b1]
  show "inj \<vinj>-['a set]" 
    by (auto simp add: set_vinj_def)
  from set_card [OF vinj_inj b1]
  show "\<exists> T \<bullet> range \<vinj>-['a set] \<subseteq> \<chi> T"
    apply (msafe_no_assms(inference))
    apply (witness "cset \<^CT>{:'a:}")
    apply (simp add: set_vinj_def)
    done
qed

end


instance
  set :: (svcard) svcard
proof -
  have b1: "inj (scinj::'a \<rightarrow> VAL)"
    by (rule scinj_inj)
  have b2: "\<exists> T \<bullet> range (scinj::'a \<rightarrow> VAL) \<subseteq> \<chi> T"
    by (rule scinj_bound_inj)
  from set_card [OF b1 b2 [THEN someI_ex]] 
  show "OFCLASS('a set, svcard_class)"
    apply (intro svcardI')
    apply (mauto(inference))
    done
qed

instance
  set :: (vtype) vtype
  by (intro_classes)

lemma CT_set: 
  "\<^CT>{:('a::svaltype) set:} = cset \<^CT>{:'a:}"
proof -
  have b1: "range \<vinj>-['a] \<subseteq> \<chi> \<^CT>{:'a:}"
    by (rule CT)
  show ?thesis
    apply (rule CT_eq)
    apply (simp add: set_vinj_def subset_def image_def vrank_cset)
    apply (mauto(inference))
  proof -
    fix X::"'a set"
    from b1 show 
      "\<exists> Y \<bullet> 
        (\<forall> y \<bullet> y \<in> Y \<Rightarrow> y \<in> \<chi> \<^CT>{:'a:}) \<and>
        vset_of \<^CT>{:'a:} {y | (\<exists> x \<bullet> x \<in> X \<and> y = \<vinj> x)} = vset_of \<^CT>{:'a:} Y"
      apply (witness "\<vinj>\<lparr>X\<rparr>")
      apply (auto simp add: image_def subset_def)
      done
  qed
qed


instantiation (* type: fun *)
  "fun" :: (svaltype, svaltype) svaltype
begin

definition
  fun_vinj_def: "\<vinj> \<defs> (graph_VAL \<^CT>{:'a:} \<^CT>{:'b:}) \<circ> VAL_graph"

instance
proof (intro_classes)
  have 
    b1: "inj_on (graph_VAL \<^CT>{:'a:} \<^CT>{:'b:}) (range VAL_graph-['a,'b])"
    apply (rule subset_inj_on)
    apply (rule graph_VAL_inj)
    apply (auto simp add: VAL_graph_rel)
    done
  show 
    "inj \<vinj>-['a \<rightarrow> 'b]"
    apply (simp add: fun_vinj_def)
    apply (rule comp_inj_on [OF VAL_graph_inj b1])
    done
next
  from graph_VAL_vrank [of _ "\<^CT>{:'a:}" "\<^CT>{:'b:}", OF VAL_graph_rel] show
    "(\<exists> T \<bullet> range \<vinj>-['a \<rightarrow> 'b] \<subseteq> \<chi> T)"
    apply (witness "cset (cprod \<^CT>{:'a:} \<^CT>{:'b:})")
    apply (auto simp add: fun_vinj_def)
    done
qed

end
(*
definition
  VAL_appl :: "[VAL, VAL] \<rightarrow> VAL" ("_\<vappl>_" [999,1000] 999)
where
  "v \<vappl> u \<defs> Abs_VAL ((Rep_VAL v) \<cappl> (Rep_VAL u))"
*)

definition
  VAL_appl :: "[VAL, VAL] \<rightarrow> VAL" ("_\<vappl>_" [999,1000] 999)
where
  "v \<vappl> u \<defs> 
    \<if> (Rep_VAL u) \<in> \<zdom> (CU_graph (Rep_VAL v)) 
    \<then> Abs_VAL ((Rep_VAL v) \<cappl> (Rep_VAL u))
    \<else> (The (funK \<False>))
    \<fi>"

notation (xsymbols output)
  VAL_appl  ("_ \<nu>\<cdot> _" [999,1000] 999)

(*
lemma graph_VAL_inv_raw:
  assumes
    a1: "f \<in> \<chi> CT1 \<zpfun> \<chi> CT2"
  shows
    "VAL_appl (graph_VAL CT1 CT2 f) = \<opof> f"
proof (rule ext)
  fix
    x :: "VAL"
  from a1 have
    b1: "{ a b | (a, b) \<in> f \<bullet> (Rep_VAL a, Rep_VAL b) } \<in> carrier_set CT1 \<zpfun> carrier_set CT2"
    apply (mauto(fspace))
    apply (auto dest!: rel_memD [OF a1 [THEN pfun_rel]] simp add: vrank_def image_conv VAL.Abs_inverse)
    apply (auto intro!: functionalI elim!: functionalE simp add: VAL.Rep_inject)
    done
  have
    b2: "{ a b | (a, b) \<in> f \<bullet> (Rep_VAL a, Rep_VAL b) }\<cdot>(Rep_VAL x) = Rep_VAL (f\<cdot>x)"
  proof (cases "x \<in> \<zdom> f")
    assume
      c1: "x \<in> \<zdom> f"
    show
      "?thesis"
      apply (rule pfun_beta [OF b1])
      apply (simp add: VAL.Rep_inject)
      apply (rule pfun_appl [OF a1 c1])
      done
  next
    assume
      c1: "x \<notin> \<zdom> f"
    then have
      c2: "(Rep_VAL x) \<notin> \<zdom> { a b | (a, b) \<in> f \<bullet> (Rep_VAL a, Rep_VAL b) }"
      by (auto simp add: VAL.Rep_inject)
    from c1 c2  show
      "?thesis"
      apply (simp add: undef_beta)
      by (simp add: undef_beta VAL_undef VAL.Abs_inverse)
  qed
  show
    "(graph_VAL CT1 CT2 f)\<vappl>x = f\<cdot>x"
    by (simp add: VAL_appl_def graph_VAL_def VAL.Abs_inverse map_pair_def image_conv CU_graph [OF b1 [THEN pfun_rel]] b2 VAL.Rep_inverse)
qed
*)

lemma graph_VAL_inv_raw:
  assumes
    a1: "f \<in> \<chi> CT1 \<zpfun> \<chi> CT2"
  shows
    "VAL_appl (graph_VAL CT1 CT2 f) = \<opof> f"
proof (rule ext)
  fix
    x :: "VAL"
  from a1 have
    b1: "{ a b | (a, b) \<in> f \<bullet> (Rep_VAL a, Rep_VAL b) } \<in> carrier_set CT1 \<zpfun> carrier_set CT2"
    apply (mauto(fspace))
    apply (auto dest!: rel_memD [OF a1 [THEN pfun_rel]] simp add: vrank_def image_conv VAL.Abs_inverse)
    apply (auto intro!: functionalI elim!: functionalE simp add: VAL.Rep_inject)
    done
  have
    b2: "{ a b | (a, b) \<in> f \<bullet> (Rep_VAL a, Rep_VAL b) }\<cdot>(Rep_VAL x) = 
         \<if> x \<in> \<zdom> f \<then> Rep_VAL (f\<cdot>x) \<else> The (funK \<False>) \<fi>"
  proof (cases "x \<in> \<zdom> f")
    assume
      c1: "x \<in> \<zdom> f"
    then show
      "?thesis"
      apply simp
      apply (rule pfun_beta [OF b1])
      apply (simp add: VAL.Rep_inject)
      apply (rule pfun_appl [OF a1 c1])
      done
  next
    assume
      c1: "x \<notin> \<zdom> f"
    then have
      c2: "(Rep_VAL x) \<notin> \<zdom> { a b | (a, b) \<in> f \<bullet> (Rep_VAL a, Rep_VAL b) }"
      by (auto simp add: VAL.Rep_inject)
    from c1 c2 show
      "?thesis"
      by (simp add: undef_beta eind_def funK_def)
  qed
  show
    "(graph_VAL CT1 CT2 f)\<vappl>x = f\<cdot>x"
    apply (cases "x \<in> \<zdom> f")
    apply (simp add: 
              VAL_appl_def graph_VAL_def VAL.Abs_inverse map_pair_def image_conv 
              CU_graph [OF b1 [THEN pfun_rel]] b2 VAL.Rep_inverse eind_split)
    apply (simp add: Domain_iff VAL.Rep_inject)
    apply (simp add: VAL_appl_def graph_VAL_def)
    apply (simp add: 
              VAL_appl_def graph_VAL_def VAL.Abs_inverse map_pair_def 
              image_conv CU_graph [OF b1 [THEN pfun_rel]] b2 VAL.Rep_inverse eind_split funK_def)
    apply (simp add: undef_beta)
    apply (simp add: Domain_iff VAL.Rep_inject)
    done
qed

lemma graph_VAL_inv:
  assumes
    a1: "f \<in> \<chi> CT1 \<zpfun> \<chi> CT2" and
    a2: "x \<in> \<zdom> f"
  shows
    "(graph_VAL CT1 CT2 f)\<vappl>x = f\<cdot>x"
  by (simp add: graph_VAL_inv_raw [OF a1]) 

lemma VAL_beta2:
  "(\<vinj>-[('a::svaltype) \<rightarrow> ('b::svaltype)] f) \<vappl> (\<vinj>-['a::svaltype] x) 
  = \<vinj>-['b::svaltype] (f x)"
proof -
  have 
    "(\<vinj> f) \<vappl> (\<vinj> x)
    = Abs_VAL 
        (((CU_graph 
          \<circ> (graph_CU \<^CT>{:'a:} \<^CT>{:'b:}) 
          \<circ> image (Rep_VAL \<par> Rep_VAL) \<circ> VAL_graph) f)
        \<cdot>(Rep_VAL (\<vinj> x)))"
    apply (simp add: fun_vinj_def graph_VAL_def VAL_appl_def VAL.Abs_inverse)
    apply (subst CU_graph)
    using VAL_graph_rel [of "f"]
    apply (mauto(fspace))
    apply (auto simp add: vrank_def  VAL.Abs_inverse)
    using VAL_graph_tfun [of "f"] CT_of_char' [of "x"]
    apply (mauto(fspace))
    apply (auto simp add: image_conv rel_def VAL.Abs_inverse VAL.Rep_inject CT_of_char' Domain_iff 
              eind_def)
    done
  also from VAL_graph_rel [of f] have 
    "(CU_graph \<circ> (graph_CU \<^CT>{:'a:} \<^CT>{:'b:}) \<circ> image (Rep_VAL \<par> Rep_VAL) \<circ> VAL_graph) f
    = (image (Rep_VAL \<par> Rep_VAL) \<circ> VAL_graph) f"
    apply (simp)
    apply (rule CU_graph)
    apply (auto simp add: vrank_def map_pair_def image_conv rel_def VAL.Abs_inverse)
    done
  also have  
    "((image (Rep_VAL \<par> Rep_VAL) \<circ> VAL_graph) f)\<cdot>(Rep_VAL (\<vinj> x))
    = Rep_VAL ((VAL_graph f)\<cdot>(\<vinj> x))"
    apply (rule functional_beta)
    using VAL_graph_functional [of "f", THEN functionalD] VAL_graph_tfun [of f] CT_of_char' [of "x"]
    apply (mauto(fspace))
    apply (auto intro!: functionalI functional_appl [OF VAL_graph_functional] simp add: map_pair_def image_conv VAL.Rep_inject)
    done
  finally show 
    "?thesis"
    by (simp add: VAL.Rep_inverse VAL_graph_beta)
qed

text {*

In order to demonstrate that the @{text fun} operator preserves
@{text svcard}, we use the fact that it is isomorphic to the total
graphs, a type readily embedded in a Cartesian universe rank. 
To simplify this proof, and others to follow we introduce an intermediate
lemma that the existence of a total injective graph into a type of
class @{text svcard} is enough to establish a claim to be in @{text svcard}.

*}

lemma rep_vcardI:
  "\<^sEP>{:\<univ>-['a]:}{:\<univ>-['b::vcard]:} \<turnstile> OFCLASS('a, vcard_class)"
proof (intro_classes, simp add: subequipotent_def)
  assume a1: "\<exists> f \<bullet> f \<in> \<univ>-['a] \<zinj> \<univ>-['b]"
  from vcard have a2: "\<exists> f \<bullet> f \<in> \<univ>-['b] \<zinj> \<univ>-[VAL]"
    by (simp add: subequipotent_def)
  from a1 a2 show "\<exists> f \<bullet> f \<in> \<univ>-['a] \<zinj> \<univ>-[VAL]"
  proof (msafe_no_assms(inference))
    fix inj_d_a inj_d_b
    assume b1: "inj_d_a \<in> \<univ>-['a] \<zinj> \<univ>-['b]" and 
      b2: "inj_d_b \<in> \<univ>-['b] \<zinj> \<univ>-[VAL]"
    let ?inj = "inj_d_a \<zfcomp> inj_d_b"
    from b1 b2 have "?inj \<in> \<univ> \<zinj> \<univ>"
      by (auto intro!: fcomp_in_tinjI simp add: tinj_tfun [THEN tfun_dom])
    then show "\<exists> f \<bullet> f \<in> \<univ>-['a] \<zinj> \<univ>-[VAL]"
      by (auto)
  qed
qed

lemma rep_vcardIa:
  "f \<in> \<univ>-['a] \<zinj> \<univ>-['b::vcard] \<turnstile> OFCLASS('a, vcard_class)"
  by (rule rep_vcardI, auto simp add: subequipotent_def)


lemma rep_vcardIb:
  "inj (f::('a \<rightarrow> 'b::vcard)) \<turnstile> OFCLASS('a, vcard_class)"
  by (rule rep_vcardIa, rule graph_of_f_inj)

lemma rep_svcardI:
  "\<^sEP>{:\<univ>-['a]:}{:\<univ>-['b::svcard]:} \<turnstile> OFCLASS('a, svcard_class)"
proof (intro_classes, simp add: subequipotent_def)
  assume a1: "\<exists> f \<bullet> f \<in> \<univ>-['a] \<zinj> \<univ>-['b]"
  from svcard have a2: "\<exists> T f \<bullet> f \<in> \<univ>-['b] \<zinj> (\<chi> T::VAL set)"
    by (simp add: subequipotent_def)
  from a1 a2 show "\<exists> T f \<bullet> f \<in> \<univ>-['a] \<zinj> ((\<chi> T)::VAL set)"
    (is "\<exists> T f \<bullet> ?Q T f")
  proof (msafe_no_assms(inference))
    fix T f g
    assume b1: "f \<in> \<univ>-['a] \<zinj> \<univ>-['b]" and
      b2: "g \<in> \<univ>-['b] \<zinj> (\<chi> T::VAL set)"
    let ?f = "f \<zfcomp> g" 
    from b2 have b3: "\<zran> ?f \<subseteq> \<chi> T"
      by (mauto(fspace))
    from b1 b2 have "?f \<in> \<univ> \<zinj> \<univ>"
      apply (intro fcomp_in_tinjI)
      apply (auto simp add: tinj_tfun [THEN tfun_dom])
      apply (mauto(fspace))
      done
    with b3 have "?f \<in> \<univ> \<zinj> \<chi> T"
      by (auto dest: dr_tinjD1 dr_tinjD2 intro!: dr_tinjI
        simp add: tinj_tfun [THEN tfun_dom])
    then have "(\<exists> f \<bullet> ?Q T f)" 
      by (auto)
    then show "(\<exists> T f \<bullet> ?Q T f)" 
      by (auto)
  qed
qed

lemma rep_svcardIa:
  "f \<in> \<univ>-['a] \<zinj> \<univ>-['b::svcard] \<turnstile> OFCLASS('a, svcard_class)"
  by (rule rep_svcardI, auto simp add: subequipotent_def)


lemma rep_svcardIb:
  "inj (f::('a \<rightarrow> 'b::svcard)) \<turnstile> OFCLASS('a, svcard_class)"
  by (rule rep_svcardIa, rule graph_of_f_inj)

text {*

Now it is straightforward to observe that @{text "\<graphof>"} is the
necessary injection in the case of a function space.

NB Can't use simple proof in absence of Set type.

*}

(*
instance
  "fun" :: (svcard, svcard)svcard
  apply (rule rep_svcardIb [of "\<graphof>"])
  apply (rule graph_of_inj)
*)

lemma fun_card:
  fixes 
    f::"'a \<rightarrow> VAL" and S::CT and
    g::"'b \<rightarrow> VAL" and T::CT
  assumes
    a1: "inj f" and 
    a2: "range f \<subseteq> (\<chi> S::VAL set)" and
    a3: "inj g" and 
    a4: "range g \<subseteq> (\<chi> T::VAL set)"
  shows 
    "inj (\<olambda> F \<bullet> vset_of (cprod S T) ({ x \<bullet> vprod_of (f x, g (F x))})) \<and> 
     range (\<olambda> F \<bullet> vset_of (cprod S T) ({ x \<bullet> vprod_of (f x, g (F x))})) \<subseteq> \<chi> (cset (cprod S T))"
    (is "inj ?CL_G \<and> range ?CL_G \<subseteq> \<chi> (cset (cprod S T))")
proof (msafe_no_assms(inference))
  let ?set_of = "(\<olambda> X::VAL set \<bullet> vset_of (cprod S T) X)"
  let ?prod_img = "(\<olambda> X::(VAL \<times> VAL) set \<bullet> vprod_of\<lparr>X\<rparr>)"
  let ?mk_graph = "(\<olambda> F \<bullet> { x \<bullet> (f x, g (F x))})"
  let ?CL_F = "?set_of \<circ> ?prod_img \<circ> ?mk_graph"
  have 
    "?prod_img \<circ> ?mk_graph = (\<olambda> F \<bullet> { x \<bullet> vprod_of (f x, g (F x))})"
    apply (rule ext)
    apply (auto simp add: eind_def)
    done
  then have 
    "?CL_G
    = ?set_of \<circ> (?prod_img \<circ> ?mk_graph)"
    apply (simp)
    apply (simp add: comp_def)
    done
  also have "\<dots> 
    = ?CL_F"
    by (simp add: o_assoc)
  finally have 
    b0: "?CL_G = ?CL_F"
    by (simp)
  have 
    b1: "inj ?mk_graph"
  proof (rule injI)
    fix F G 
    assume 
      c1: "{ x \<bullet> (f x, g (F x))} = { x \<bullet> (f x, g (G x))}"
    from a1 [THEN injD] have 
      c3: "functional { x \<bullet> (f x, g (F x))}"
      apply (intro functionalI)
      apply (auto)
      done
    show 
      "F = G"
    proof (rule ext)
      fix x
      have 
        d1: "(f x, g (F x)) \<in> { x \<bullet> (f x, g (F x))}"
        by (auto)
      have 
        d2: "(f x, g (G x)) \<in> { x \<bullet> (f x, g (F x))}"
        by (auto simp add: c1)
      from c3 [THEN functionalD, OF d1 d2] have 
        "g (F x) = g (G x)"
        by (this)
      with a3 [THEN injD]
      show 
        "F x = G x"
        by (auto)
    qed
  qed
  from a2 a4 have 
    b1': "range ?mk_graph \<subseteq> (\<pset> ((\<chi> S) \<times> (\<chi> T)))"
    by (auto)
  have 
    "inj_on ?prod_img (\<pset> ((\<chi> S) \<times> (\<chi> T)))"
  proof (rule inj_onI)
    fix X Y 
    assume 
      d1: "X \<in> \<pset> ((\<chi> S) \<times> (\<chi> T))" and
      d2: "Y \<in> \<pset> ((\<chi> S) \<times> (\<chi> T))" and
      d3: "?prod_img X = ?prod_img Y"
    show 
      "X = Y"
    proof (auto)
      fix x y
      assume 
        e1: "(x, y) \<in> X"
      with d3 [symmetric] have 
        e2: "vprod_of (x, y) \<in> ?prod_img Y"
        by (auto)
      then obtain x' y' 
      where 
        e3: "(x', y') \<in> Y" and
        e4: "vprod_of (x, y) = vprod_of (x', y')"
        by (auto)
      from e4 have 
        "(x, y) = (x', y')"
        by (rule inj_vprod_of [THEN injD])
      with e3 
      show 
        "(x, y) \<in> Y"
        by (simp)
    next
      fix x y
      assume 
        e1: "(x, y) \<in> Y"
      with d3 have 
        e2: "vprod_of (x, y) \<in> ?prod_img X"
        by (auto)
      then obtain x' y' 
      where 
        e3: "(x', y') \<in> X" and
        e4: "vprod_of (x, y) = vprod_of (x', y')"
        by (auto)
      from e4 have 
        "(x, y) = (x', y')"
        by (rule inj_vprod_of [THEN injD])
      with e3 
      show 
        "(x, y) \<in> X"
        by (simp)
    qed
  qed
  with b1' have
    b2: "inj_on ?prod_img (range ?mk_graph)"
    by (auto intro: subset_inj_on)
  from b1' have 
    b2': "?prod_img\<lparr>range ?mk_graph\<rparr> \<subseteq> \<pset> (\<chi> (cprod S T))"
    by (auto simp add: vrank_cprod eind_def)
  have 
    "inj_on ?set_of (\<pset> (\<chi> (cprod S T)))"
    by (rule inj_on_vset_of_t)
  with b2' have 
    b3: "inj_on ?set_of (?prod_img\<lparr>range ?mk_graph\<rparr>)"
    by (auto intro: subset_inj_on)
  have 
    "inj ?CL_F"
    apply (rule comp_inj_on)
    apply (rule b1)
    apply (rule comp_inj_on)
    apply (rule b2)
    apply (rule b3)
    done
  then 
  show 
    "inj ?CL_G"
    by (simp add: b0)
  have 
    "range ?CL_F 
    = ?set_of\<lparr>?prod_img\<lparr>range ?mk_graph\<rparr>\<rparr>"
    by (simp add: image_compose)
  also have "\<dots> 
    \<subseteq> ?set_of\<lparr>\<pset> (\<chi> (cprod S T))\<rparr>"
    apply (rule image_mono)
    apply (rule b2')
    done
  also have "\<dots> 
    = \<chi> (cset (cprod S T))"
    by (simp add: vrank_cset)
  finally 
  show 
    "range ?CL_G \<subseteq> \<chi> (cset (cprod S T))"
    by (simp add: b0)
qed

instance
  "fun" :: (svcard, svcard) svcard
proof (intro svcardI')
  have 
    b1: "inj (scinj::'a \<rightarrow> VAL)"
    by (rule scinj_inj)
  have 
    b1': "range (scinj::'a \<rightarrow> VAL) \<subseteq> \<chi> (\<^scCT>[:'a:])"
    by (rule scinj_bound_scCT)
  have 
    b2: "inj (scinj::'b \<rightarrow> VAL)"
    by (rule scinj_inj)
  have 
    b2': "range (scinj::'b \<rightarrow> VAL) \<subseteq> \<chi> (\<^scCT>[:'b:])"
    by (rule scinj_bound_scCT)
  let ?inj = "(\<olambda> F::('a \<rightarrow> 'b) \<bullet> vset_of (cprod \<^scCT>[:'a:] \<^scCT>[:'b:]) ({ x \<bullet> vprod_of (scinj x, scinj (F x))}))"
  from fun_card [OF b1 b1' b2 b2']
  show 
    "inj ?inj"
    "range ?inj \<subseteq> \<chi> (cset (cprod \<^scCT>[:'a:] \<^scCT>[:'b:]))"
    by (auto)
qed

text {*

The default approach to introducing new types in HOL is through the
definition of a representation set. Association between definitional
types and their representation set is indicated by the 
@{text type_definition} predicate. One consequence of the
@{text type_definition} predicate is the existence of an injection
into the representation set, so if the representation set is from 
an existing @{text svcard}, the representation axiom immediately
establishes the new type in the @{text svcard} class.

*}

lemmas type_def_vcardI = type_definition.Rep_inj [THEN rep_vcardIb]
lemmas type_def_svcardI = type_definition.Rep_inj [THEN rep_svcardIb]

text {*

Some important examples of definitional types are @{text unit}, 
disjoint sums, @{text "\<nat>"}, @{text "\<real>"}, and the ordinals.

*}

instance
  "unit" :: svcard
  by (rule type_def_svcardI, rule type_definition_unit)

instantiation (* type: Product_Type.unit *)
  Product_Type.unit :: svaltype
begin

definition
  unit_vinj_def: "\<vinj>-[unit] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: unit_vinj_def)
  done

end

instance
  sum :: (svcard, svcard)svcard
  by (rule type_def_svcardI, rule type_definition_sum)

instantiation (* type: + *)
  sum :: (svaltype, svaltype)svaltype
begin

definition
  sum_vinj_def: "\<vinj>-[('a::svaltype) + ('b::svaltype)] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: sum_vinj_def)
  done

end

instance
  nat :: svcard
  by (rule type_def_svcardI, rule type_definition_nat)

instantiation (* type: nat *)
  nat :: svaltype
begin

definition
  nat_vinj_def: "\<vinj>-[nat] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: nat_vinj_def)
  done

end

instance
  int :: svcard
  apply (rule rep_svcardIb)
  apply (rule type_definition_int [THEN type_definition.Rep_inj])
  done

instantiation (* type: Int.int *)
  Int.int :: svaltype
begin

definition
  int_vinj_def: "\<vinj>-[int] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: int_vinj_def)
  done

end

text {*

HOL datatypes are just a special class of definitional types,
but proving them instances of @{text svcard} is complicated by
the fact that they are represented in the @{text "Datatype_Universe.Node"}
type, which is hidden in the default HOL distribution. In order,
do instance proofs for datatypes, we prove that the embedding
injection can span an intermediate type.

*}

lemma datatype_span:
  assumes
    a1: "type_definition (Rep_d_1::'b \<rightarrow> 'c) Abs_d_1 A_d_1" and
    a2: "type_definition (Rep_d_2::'a \<rightarrow> 'b set) Abs_d_2 A_d_2"
  shows "\<^sEP>{:\<univ>-['a]:}{:\<univ>-['c set]:}"
proof -
  from a1 have a3: "inj Rep_d_1" by (rule type_definition.Rep_inj)
  from a2 have a4: "inj Rep_d_2" by (rule type_definition.Rep_inj)
  let ?f = "\<olambda> a \<bullet> Rep_d_1\<lparr>Rep_d_2 a\<rparr>"
  have "inj ?f"
  proof (auto intro!: inj_onI)
    fix x y
    assume b1: "Rep_d_1\<lparr>Rep_d_2 x\<rparr> = Rep_d_1\<lparr>Rep_d_2 y\<rparr>"
    with a3 have "Rep_d_2 x = Rep_d_2 y"
      by (simp add: inj_image_eq_iff)
    with a4 show "x = y" by (simp add: inj_eq)
  qed
  then have "\<graphof> ?f \<in> \<univ> \<zinj> \<univ>"
    by (rule graph_of_f_inj)
  then show ?thesis
    by (auto simp add: subequipotent_def)
qed

lemmas data_svcardI =
  type_definition_node [THEN datatype_span, THEN rep_svcardI]

text {*

Proving datatype instances of @{text vcard} is now trivial.

*}

instance
  num :: svcard
  by (rule data_svcardI, rule type_definition_num)

instantiation (* type: Num.num *)
  Num.num :: svaltype
begin

definition
  num_vinj_def: "\<vinj>-[num] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: num_vinj_def)
  done

end

instance
  option :: (svcard)svcard
  by (rule data_svcardI, rule type_definition_option)

instantiation (* type: Option.option *)
  Option.option :: (svaltype)svaltype
begin

definition
  option_vinj_def: "\<vinj>-[('a::svaltype)option] \<defs> scinj"

instance
  apply (intro_classes)
  apply (auto intro!: scinj_inj scinj_bound_inj simp add: option_vinj_def)
  done

end

text {*

The @{text list} datatype is such a common and useful type constructor
that we find it useful to ensure that it preserves @{text valtype} as well as 
@{text svaltype}.

*}

fun
  linj :: "['a \<rightarrow> VAL, VAL, 'a list] \<rightarrow> VAL"
where
  "linj f a [] = vprod_of (\<vinj>-[\<nat>] 0, a)"
| "linj f a (x#y) = vprod_of (\<vinj>-[\<nat>] 1, vprod_of (f x, linj f a y))"

lemma linj_inj:
  assumes a1: "inj f"
  shows "inj (linj f a)"
proof (rule inj_onI)
  fix x::"'a list" and y::"'a list"
  assume c1: "linj f a x = linj f a y"
  have c2: "inj (vinj::\<nat> \<rightarrow> VAL)" by (rule vinj_inj)
  have "\<forall> y | linj f a x = linj f a y \<bullet> x = y"
  proof (induct x)
    show "\<forall> y | linj f a [] = linj f a y \<bullet> [] = y"
    proof (msafe_no_assms(inference))
      fix y assume "linj f a [] = linj f a y"
      with c2 show "[] = y"
        by (cases y, auto simp add: inj_on_iff vprod_of_eq)
    qed
  next
    fix x::"'a" and l::"'a list"
    assume d1: "\<forall> l' | linj f a l = linj f a l' \<bullet> l = l'"
    show "\<forall> l' | linj f a (x#l) = linj f a l' \<bullet> (x#l) = l'"
    proof (msafe_no_assms(inference))
      fix l'::"'a list" assume e1: "linj f a (x#l) = linj f a l'"
      with c2 a1 d1 show "(x#l) = l'"
        by (cases l', simp_all add: inj_on_iff vprod_of_eq)
    qed
  qed
  with c1 show "x = y"
    by (auto)
qed

instance
  list :: (vcard)vcard
proof (intro_classes, simp add: subequipotent_def)
  let ?linj = "linj (cinj::'a \<rightarrow> VAL) arbitrary"
  from cinj_inj have "inj ?linj"
    by (rule linj_inj)
  then have "\<graphof> ?linj \<in> \<univ> \<zinj> \<univ>"
    by (rule graph_of_f_inj)  
   then show "\<exists> f \<bullet> f \<in> \<univ>-['a list] \<zinj> \<univ>-[VAL]"
    by (auto)
qed

instance
  list :: (svcard)svcard
  by (rule data_svcardI, rule type_definition_list)

instantiation (* type: List.list *)
  List.list :: (valtype)valtype
begin

definition
  list_vinj_def: "\<vinj>-['a list] \<defs> 
    (\<olambda> l \<bullet> 
      \<if> \<exists> T \<bullet> range \<vinj>-['a] \<subseteq> \<chi> T
      \<then> 
        (\<olambda> f \<bullet> vset_of (cprod \<^CT>{:\<nat>:} (CT_of_val \<arb>-['a])) 
          {(n::\<nat>) (x::'a) | (n \<mapsto> x) \<in> f \<bullet> vprod_of (\<vinj> n, \<vinj>x)})
          (\<glambda> n | n \<in> {0..<(length l)} \<bullet> nth l n)
      \<else> linj \<vinj>-['a] \<arb> l
      \<fi>)"

instance
  apply (intro_classes)
  apply (cases "\<exists> T \<bullet> range \<vinj>-['a] \<subseteq> \<chi> T")
proof -
  fix T
  assume 
    b1: "\<exists> T \<bullet> range \<vinj>-['a] \<subseteq> \<chi> T"
  let 
    ?J = "(\<olambda> f \<bullet> vset_of (cprod \<^CT>{:\<nat>:} (CT_of_val \<arb>-['a])) 
          {(n::\<nat>) (x::'a) | (n \<mapsto> x) \<in> f \<bullet> vprod_of (\<vinj> n, \<vinj>x)})"
  have 
    b2: "inj ?J"
  proof (rule inj_onI)
    fix 
      f::"\<nat> \<leftrightarrow> 'a" and 
      g::"\<nat> \<leftrightarrow> 'a"
    assume 
      c1: "?J f = ?J g"
    from b1 have 
      c2: "range \<vinj>-['a] \<subseteq> \<chi> (CT_of_val \<arb>-['a])"
      by (auto intro!: CT')
    have c3: "range \<vinj>-[\<nat>] \<subseteq> \<chi> \<^CT>{:\<nat>:}"
      by (rule CT)
    have 
      c4: "{(n::\<nat>) (x::'a) | (n \<mapsto> x) \<in> f \<bullet> vprod_of (\<vinj> n, \<vinj>x)} 
          = {(n::\<nat>) (x::'a) | (n \<mapsto> x) \<in> g \<bullet> vprod_of (\<vinj> n, \<vinj>x)}"
      (is "?X f = ?X g")
      apply (rule inj_onD)
      apply (rule inj_on_vset_of_t)
      apply (rule c1)
      apply (simp_all only: Pow_iff subset_def)
      apply (insert c2 c3)
      apply (auto simp add: image_def vrank_cprod)
      done
    show "f = g"
      apply (simp add: set_eq_def)
      apply (intro allI)
    proof -
      fix n::"\<nat>" and x::"'a"
      have "(n \<mapsto> x) \<in> f
      \<Leftrightarrow> vprod_of (\<vinj> n, \<vinj> x) \<in> ?X f"
      proof (auto simp add: vprod_of_eq)
        fix n'::"\<nat>" and x'::"'a"
        assume e1: "\<vinj> n = \<vinj> n'" and e2: "\<vinj> x = \<vinj> x'" and
          e3: "(n' \<mapsto> x') \<in> f"
        have e4: "n = n'"
          apply (rule inj_onD)
          apply (rule vinj_inj)
          apply (rule e1)
          apply (auto)
          done
        have e5: "x = x'"
          apply (rule inj_onD)
          apply (rule vinj_inj)
          apply (rule e2)
          apply (auto)
          done
        from e3 e4 e5 show "(n \<mapsto> x) \<in> f"
          by (simp)
      qed
      also from c4 have "\<dots> 
      \<Leftrightarrow> vprod_of (\<vinj> n, \<vinj> x) \<in> ?X g"
        by (simp add: eind_def)
      also have "\<dots>
      \<Leftrightarrow> (n \<mapsto> x) \<in> g"
      proof (auto simp add: vprod_of_eq)
        fix n'::"\<nat>" and x'::"'a"
        assume e1: "\<vinj> n = \<vinj> n'" and e2: "\<vinj> x = \<vinj> x'" and
          e3: "(n' \<mapsto> x') \<in> g"
        have e4: "n = n'"
          apply (rule inj_onD)
          apply (rule vinj_inj)
          apply (rule e1)
          apply (auto)
          done
        have e5: "x = x'"
          apply (rule inj_onD)
          apply (rule vinj_inj)
          apply (rule e2)
          apply (auto)
          done
        from e3 e4 e5 show "(n \<mapsto> x) \<in> g"
          by (simp)
      qed
      finally show "(n \<mapsto> x) \<in> f \<Leftrightarrow> (n \<mapsto> x) \<in> g" 
        by (this)
    qed
  qed
  have b3: "inj (\<olambda> l::'a list \<bullet> (\<glambda> n | n \<in> {0..<(length l)} \<bullet> nth l n))" (is "inj ?I") 
  proof (rule inj_onI)
    fix k l
    assume c1: "?I k = ?I l"
    have c2: "\<forall> k l \<bullet> ?I k = ?I l \<Leftrightarrow> (\<forall> m x \<bullet> m < length k \<and> nth k m = x \<Leftrightarrow> m < length l \<and> nth l m = x)"
      by (auto simp add: glambda_def set_eq_def)
    have c3: "\<forall> k l \<bullet> ?I k = ?I l \<Rightarrow> length k = length l"
    proof (msafe_no_assms(inference))
      fix k l assume d1: "?I k = ?I l"
      with c2 have d2: "(\<forall> m \<bullet> m < length k \<Leftrightarrow> m < length l)"
        by (auto)
      then show "length k = length l"       
        apply (rule contrapos_pp)
        apply (simp add: nat_neq_iff)
        apply (msafe_no_assms(inference))
        apply (witness "length k")
        apply (auto)
        done
    qed
    with c2 have c4: "\<forall> k l \<bullet> ?I k = ?I l \<Rightarrow> (length k = length l) \<and> (\<forall> m x \<bullet> m < length k \<and> nth k m = x \<Leftrightarrow> m < length k \<and> nth l m = x)"
      by (auto)
    have c5: "\<forall> l \<bullet> (length k = length l) \<and> (\<forall> m x \<bullet> m < length k \<and> nth k m = x \<Leftrightarrow> m < length k \<and> nth l m = x) \<Rightarrow> k = l" (is "\<forall> l \<bullet> ?P k l")
    proof (induct "k")
      show "\<forall> l \<bullet> ?P [] l"
        by (auto simp add: glambda_def)
    next
      fix x k
      assume d1: "\<forall> l \<bullet> ?P k l" 
      show "\<forall> l \<bullet> ?P (x#k) l"
      proof (rule allI)
        fix l show "?P (x#k) l"
        proof (induct l)
          show "?P (x#k) []"
          proof (msafe_no_assms(inference))
            assume e1: "length (x#k) = length ([]::'a list)"
            then show "(x#k) = []"
              by (auto)
          qed
        next
          fix y l
          show "?P (x#k) (y#l)"
          proof (auto)
            assume e1: "length k = length l" and
              e2: "\<forall> m  z \<bullet> m < Suc (length l) \<and> nth (x#k) m = z \<Leftrightarrow> m < Suc (length l) \<and> nth (y#l) m = z"
            from e2 [rule_format, of "0" "x"]
            show "x = y"
              by (simp)
            from e2 
            have e3: "\<forall> m z \<bullet> 1 \<le> m \<and> m < Suc (length l) \<and> nth (x#k) m = z \<Leftrightarrow> 1 \<le> m \<and> m < Suc (length l) \<and> nth (y#l) m = z"
              by (auto)
            have "\<forall> m z \<bullet> 1 \<le> (Suc m) \<and> Suc m < Suc (length l) \<and> nth (x#k) (Suc m) = z \<Leftrightarrow> 1 \<le> (Suc m) \<and> Suc m < Suc (length l) \<and> nth (y#l) (Suc m) = z"
              apply (rule allI)
              apply (simp only: e3)
              apply (auto)
              done
            then have "\<forall> m z \<bullet> m < (length l) \<and> nth k m = z \<Leftrightarrow> m < (length l) \<and> nth l m = z"
              by (simp)
            with e1 d1
            show "k = l"
             by (auto)
          qed 
        qed
      qed
    qed
    from c5 [rule_format] c4 [rule_format, OF c1]
    show "k = l"
      by (auto)
  qed
  have b4: "inj (?J \<circ> ?I)"
    apply (rule comp_inj_on)
    apply (rule b3)
    apply (rule subset_inj_on [OF b2])
    apply (auto)
    done
  with b1 show "inj \<vinj>-['a list]"
    by (simp add: list_vinj_def comp_def)
next
  assume 
    b1: "\<not>(\<exists> T \<bullet> range \<vinj>-['a] \<subseteq> \<chi> T)"
  have 
    "inj (linj \<vinj>-['a] \<arb>)"
    apply (rule linj_inj)
    apply (rule vinj_inj)
    done
  with b1 show 
    "inj \<vinj>-['a list]"
    by (simp add: list_vinj_def comp_def)
qed

end

instance
  list :: (svaltype)svaltype
proof (intro_classes)
  have b1: "range \<vinj>-['a] \<subseteq> \<chi> \<^CT>{:'a:}"
    by (rule CT)
  have b2: "range \<vinj>-[\<nat>] \<subseteq> \<chi> \<^CT>{:\<nat>:}"
    by (rule CT)
  {
  fix l::"'a list"
  from b1 b2 have "\<vinj>-['a list] l \<in> \<chi> (cset (cprod \<^CT>{:\<nat>:} \<^CT>{:'a:}))"
    apply (auto simp add: list_vinj_def vrank_cset)
    apply (simp add: image_conv subset_def CT_of_val_eq)
    apply (witness "{n x | (n, x) \<in> (\<glambda> n | n < length l \<bullet> l ! n) \<bullet> vprod_of (vinj n, vinj x)}")
    apply (auto simp add: vrank_cprod)
    done
  }
  then have 
    "range \<vinj>-['a list] \<subseteq> \<chi> (cset (cprod \<^CT>{:\<nat>:} \<^CT>{:'a:}))"
    by (auto)
  then show 
    "\<exists> T \<bullet> range \<vinj>-['a list] \<subseteq> \<chi> T"
    apply (witness "cset (cprod \<^CT>{:\<nat>:} \<^CT>{:'a:})")
    apply (assumption)
    done
qed

text {*

So when a new type is added by definition or as a datatype,
it is a simple matter of using the appropriate proof outline to
make the new type usable in system specifications. This process can easily
be automated by the HiVe tool.

*}

end
