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

theory Value_Cardinals

imports
  Value_Types

begin

text {*

We have the following requirements.

A cardinal domain sufficiently large to measure and compare the size of all HOL sets.

A cardinal domain that is closed under set sum, product and power set.

The first criteria is satisfied by @{text "VAL cardinal"}, 
but this does not correspond to a cartesian closed collection of sets. 
Instead, we need to restrict to cardinals corresponding to well ranked subsets of @{text "VAL"}.

*}

definition
  rsets :: "VAL set set"
where
  "rsets \<defs> {T X | X \<subseteq> \<chi> T \<bullet> X}"  

lemma rsets_memI_ex:
  assumes
    a1: "(\<exists> T \<bullet> X \<subseteq> \<chi> T)"
  shows
    "X \<in> rsets"
  using a1
  by (auto simp add: rsets_def)

lemma rsets_memI:
  assumes
    a1: "X \<subseteq> \<chi> T"
  shows
    "X \<in> rsets"
  using a1
  by (auto simp add: rsets_def)

lemma rsets_memD:
  assumes
    a1: "X \<in> rsets" and
    a2: "X \<noteq> \<emptyset>"
  shows
    "(\<exists>\<subone> T \<bullet> X \<subseteq> \<chi> T)"
  apply (rule ex_ex1I)
  using a1
  apply (simp add: rsets_def)
proof -
  fix
    T T'
  assume
    b1: "X \<subseteq> \<chi> T" and
    b2: "X \<subseteq> \<chi> T'"
  from a2 obtain x where
    b3: "x \<in> X"
    by (auto)
  from b3 b1 b2 have 
    "x \<in> \<chi> T \<inter> \<chi> T'"
    by (auto)
  then show
    "T = T'"
    apply (intro carrier_disjoint [THEN iffD1])
    apply (simp add: vrank_def nempty_conv)
    apply (witness "Rep_VAL x")
    apply (auto simp add: image_def VAL.Abs_inject VAL.Abs_inverse)
    done
qed

definition
  CT_of_rset :: "VAL set \<rightarrow> CT"
where
  "CT_of_rset X \<defs> (\<mu> T | X \<subseteq> \<chi> T)"

lemma CT_of_rset_char:
  assumes
    a1: "X \<in> rsets"
  shows
    "X \<subseteq> \<chi> (CT_of_rset X)"
  unfolding CT_of_rset_def
  apply (cases "X \<noteq> \<emptyset>")
  apply (rule theI' [OF rsets_memD])
  apply (auto simp add: a1)
  done

interpretation
  rsets_sub: sub_setrel "\<univ>" "subequipotent" "rsets"
  by (auto simp add: sub_setrel_def sub_setrel_axioms_def X_setrel_def Y_carrier_def setrel_def' carrier_def' rel_def rsets_def)

interpretation
  rsets_pre: preorder "rsets" "\<^subord>{:subequipotent:}{:rsets:}"
  by (rule rsets_sub.sub_preorderI [OF cardpre.preorder])

lemma rsets_default_equiv:
  "default_equiv \<^subord>{:subequipotent:}{:rsets:} = \<^subord>{:equipotent:}{:rsets:}"
  using equipotent_default [where ?'a = "VAL"]
  by (auto simp add: default_equiv_def subset_order_def rel2op_def op2rel_def fun_eq_iff)

interpretation
  rsets_cong: order_cong "rsets" "\<^subord>{:subequipotent:}{:rsets:}" "\<^subord>{:equipotent:}{:rsets:}"
  apply (simp add: rsets_default_equiv [symmetric]) 
  apply (rule rsets_pre.default_order_congI)
  done

typedef
  vcardinal =  "\<^qspace>{:rsets:}{:\<^subord>{:equipotent:}{:rsets:}:}"
  by (auto simp add: rsets_def quot_set_def)

interpretation
   vcard: type_definition "Rep_vcardinal" "Abs_vcardinal" "\<^qspace>{:rsets:}{:\<^subord>{:equipotent:}{:rsets:}:}"
  by (rule type_definition_vcardinal)

lemma Rep_vcardinal_subset_rsets:
  "Rep_vcardinal a \<subseteq> rsets"
  using vcard.Rep [of "a"]
  by (auto simp add: rsets_cong.quot_class_mem)

lemmas Rep_vcardinal_mem_rsets = Rep_vcardinal_subset_rsets [THEN subsetD]

lemmas Rep_vcardinal_mem = rsets_cong.quot_class_mem [OF vcard.Rep]

definition
  vrank_char :: "vcardinal \<rightarrow> VAL set"
where
  "vrank_char a \<defs> \<^qchar>{:Rep_vcardinal a:}{:\<^subord>{:equipotent:}{:rsets:}:}"

lemma vrank_char_wdef [simp]:
  "vrank_char a \<in> rsets"
  "\<^eclass>{:vrank_char a:}{:\<^subord>{:equipotent:}{:rsets:}:} \<in> \<^qspace>{:rsets:}{:\<^subord>{:equipotent:}{:rsets:}:}"
  apply (unfold vrank_char_def)
  apply (rule rsets_cong.quot_char_mem [OF vcard.Rep, THEN Rep_vcardinal_mem_rsets])
  apply (simp add: rsets_cong.quot_char_class vcard.Rep)
  done

lemma Rep_vcardinal_char:
  "Rep_vcardinal a = \<^eclass>{:vrank_char a:}{:\<^subord>{:equipotent:}{:rsets:}:}"
  using vcard.Rep [of "a"]
  by (simp add: rsets_cong.quot_char_class vrank_char_def [abs_def])

lemma vrank_char_equipotent_iff:
  "\<^EP>{:vrank_char a:}{:vrank_char b:} \<Leftrightarrow> a = b"
  apply (auto simp add: equipotent_refl)
  apply (subst vcard.Rep_inject [symmetric])
  apply (simp add: Rep_vcardinal_char rsets_cong.equiv_class_eq)
  apply (simp add: subset_order_conv)
  done

definition
  vrank_card :: "VAL set \<rightarrow> vcardinal"
where
  "vrank_card A \<defs> Abs_vcardinal \<^eclass>{:A:}{:\<^subord>{:equipotent:}{:rsets:}:}"

lemma vrank_card_wdef [simp]:
  assumes
    a1: "A \<in> rsets"
  shows
    "\<^eclass>{:A:}{:\<^subord>{:equipotent:}{:rsets:}:} \<in> \<^qspace>{:rsets:}{:\<^subord>{:equipotent:}{:rsets:}:}"
  using a1
  by (simp add: rsets_cong.quot_set_mem_ec)

lemma vrank_char_inverse:
  "vrank_card (vrank_char a) = a"
  by (simp add: vrank_char_def vrank_card_def rsets_cong.quot_char_class vcard.Rep_inverse rsets_cong.quot_char_class [OF vcard.Rep])

lemma vrank_card_inverse:
  assumes
    a1: "A \<in> rsets"
  shows
    "\<^EP>{:vrank_char (vrank_card A):}{:A:}"
  using rsets_cong.quot_class_char [OF a1]
  by (simp add: vrank_char_def vrank_card_def vcard.Abs_inverse [OF quot_setI [OF a1]] subset_order_conv)

lemma vrank_card_inverse_iff:
  assumes
    a1: "A \<in> rsets"
  shows
    "\<^EP>{:vrank_char (vrank_card A):}{:B:} \<Leftrightarrow> \<^EP>{:A:}{:B:}"
    "\<^EP>{:B:}{:vrank_char (vrank_card A):} \<Leftrightarrow> \<^EP>{:B:}{:A:}"
    "\<^sEP>{:vrank_char (vrank_card A):}{:B:} \<Leftrightarrow> \<^sEP>{:A:}{:B:}"
    "\<^sEP>{:B:}{:vrank_char (vrank_card A):} \<Leftrightarrow> \<^sEP>{:B:}{:A:}"
  by (auto intro: vrank_card_inverse [OF a1] vrank_card_inverse [OF a1, THEN equipotent_sym] equipotent_trans subeq_eq_trans eq_subeq_trans simp add: a1)

lemma vrank_card_inverse_cong:
  assumes
    a1: "A \<in> rsets" and
    a2: "\<^EP>{:A:}{:A':}"
  shows
  "\<^EP>{:vrank_char (vrank_card A):}{:A':}"
  apply (rule equipotent_trans [OF _ a2])
  apply (rule vrank_card_inverse [OF a1])
  done

lemma vrank_card_inject:
  assumes
    a1: "A \<in> rsets" and
    a2: "B \<in> rsets"
  shows
    "vrank_card A = vrank_card B \<Leftrightarrow> \<^EP>{:A:}{:B:}"
  using a1 a2
  by (simp add: vrank_card_def vcard.Abs_inject rsets_cong.equiv_class_eq subset_order_conv)

lemma vrank_card_injectI:
  assumes
    a1: "A \<in> rsets" and
    a2: "B \<in> rsets" and
    a3: "\<^EP>{:A:}{:B:}"
  shows
    "vrank_card A = vrank_card B"
  using a3 vrank_card_inject [OF a1 a2]
  by (simp)

definition
  vrank_CT :: "vcardinal \<rightarrow> CT"
where
  "vrank_CT a \<defs> CT_of_rset (vrank_char a)"

lemma vrank_CT:
  "vrank_char a \<subseteq> \<chi>(vrank_CT a)"
  by (simp add: vrank_CT_def CT_of_rset_char)

lemma vrank_CT_unique:
  assumes
    a1: "vrank_char a \<noteq> \<emptyset>" and
    a2: "vrank_char a \<subseteq> \<chi> T"
  shows 
    "T = vrank_CT a"
proof -
  note CT_unique = the1_equality [OF rsets_memD, OF _ a1, symmetric]
  from CT_unique [OF _ a2] CT_unique [OF _ vrank_CT] show
    "?thesis"
    by (simp)
qed

text {*

The order is essentially the cardinal order, corresponding to the sub-equipotent order on the underlying sets.

*}

interpretation
  rsets_order: order "\<^qspace>{:rsets:}{:\<^subord>{:equipotent:}{:rsets:}:}" "\<^quotord>{:\<^subord>{:subequipotent:}{:rsets:}:}{:\<^subord>{:equipotent:}{:rsets:}:}"
  apply (simp only: rsets_default_equiv [symmetric])
  apply (rule partial_order.orderIa)
  apply (rule rsets_pre.default_quotient_poI)
  apply (simp add: rsets_default_equiv quot_set_mem)
  apply (msafe_no_assms(inference))
  apply (simp)
proof -
  fix
    X and Y
  assume
    b1: "X \<in> rsets" and
    b2: "Y \<in> rsets"
  from linear_sEP [of X Y] b1 b2 show
    "\<^quotord>{:\<^subord>{:subequipotent:}{:rsets:}:}{:\<^subord>{:equipotent:}{:rsets:}:} \<^eclass>{:X:}{:\<^subord>{:equipotent:}{:rsets:}:} \<^eclass>{:Y:}{:\<^subord>{:equipotent:}{:rsets:}:} \<or>
     \<^quotord>{:\<^subord>{:subequipotent:}{:rsets:}:}{:\<^subord>{:equipotent:}{:rsets:}:} \<^eclass>{:Y:}{:\<^subord>{:equipotent:}{:rsets:}:} \<^eclass>{:X:}{:\<^subord>{:equipotent:}{:rsets:}:}"
    apply (simp add: quot_order_def rel2op_def op2rel_def subset_order_def quot_set_def)
    apply (msafe_no_assms(inference))
    apply (rule disjI1)
    apply (fast)
    apply (rule disjI2)
    apply (fast)
    done
qed

instantiation
  vcardinal :: "ord"
begin

definition
  lesseq_vcardinal_def_raw: "\<opleT>-[vcardinal] \<defs> induce_ord Rep_vcardinal (\<^quotord>{:\<^subord>{:subequipotent:}{:rsets:}:}{:\<^subord>{:equipotent:}{:rsets:}:})"

definition
  less_vcardinal_def_raw: "\<opltT>-[vcardinal] \<defs> derefl \<opleT>"

instance
  by (intro_classes)

end

lemma subequipotence_quot_class_char:
  assumes
    a1: "X \<in> rsets" and
    a2: "Y \<in> rsets"
  shows
    "\<^sEP>{:\<^qchar>{:\<^eclass>{:X:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:\<^qchar>{:\<^eclass>{:Y:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:\<^subord>{:equipotent:}{:rsets:}:}:}
   \<Leftrightarrow> \<^sEP>{:X:}{:Y:}"
proof -
  from rsets_cong.quot_class_char [OF a1] have 
    b1: "\<^EP>{:\<^qchar>{:\<^eclass>{:X:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:X:}"
    by (simp add: subset_order_conv)
  from rsets_cong.quot_class_char [OF a2] have 
    b2: "\<^EP>{:\<^qchar>{:\<^eclass>{:Y:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:Y:}"
    by (simp add: subset_order_conv)
  from b1 have 
    "\<^sEP>{:\<^qchar>{:\<^eclass>{:X:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:\<^qchar>{:\<^eclass>{:Y:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:\<^subord>{:equipotent:}{:rsets:}:}:}
    \<Leftrightarrow> \<^sEP>{:X:}{:\<^qchar>{:\<^eclass>{:Y:}{:\<^subord>{:equipotent:}{:rsets:}:}:}{:\<^subord>{:equipotent:}{:rsets:}:}:}"
     by (auto intro: eq_subeq_trans subeq_eq_trans equipotent_sym)
  also from b2 have "\<dots>
    \<Leftrightarrow> \<^sEP>{:X:}{:Y:}"
      by (auto intro: eq_subeq_trans subeq_eq_trans equipotent_sym)
  finally show
    "?thesis"
    by (this)
qed

lemma
  lesseq_vcardinal_def: "a \<le> (b::vcardinal) \<Leftrightarrow> \<^sEP>{:vrank_char a:}{:vrank_char b:}"
  apply (simp add: lesseq_vcardinal_def_raw induce_ord_def quot_order_def rel2op_def del: ex_simps)
(*
  apply (simp add: lesseq_vcardinal_def_raw induce_ord_def quot_order_def rel2op_def ex_simps' del: ex_simps)
*)
  apply (subst Rep_vcardinal_char [of a])
  apply (subst Rep_vcardinal_char [of b])
  apply (auto intro!: exI rsets_cong.reflD intro: subeq_eq_trans eq_subeq_trans equipotent_sym simp add: rsets_cong.equiv_class_eq subset_order_conv equipotent_refl)
  done

text {*

This order is linear.

*}

instance
  vcardinal :: "linorder"
  apply (rule typedefs_linorder_classI [OF vcard.type_definition_axioms _ lesseq_vcardinal_def_raw [unfolded atomize_eq] less_vcardinal_def_raw [unfolded atomize_eq]])
  apply (rule rsets_order.order)
  done

definition
  vcard :: "('a::svaltype) set \<rightarrow> vcardinal"
where
  "vcard A \<defs> vrank_card (\<vinj>-['a]\<lparr>A\<rparr>)"

lemma vcard_wdef [simp]:
  fixes
    A :: "('a::svaltype) set"
  shows
    "\<vinj>\<lparr>A\<rparr> \<in> rsets"
proof -
  from bound_vinj obtain T where
    b1: "range \<vinj>-['a] \<subseteq> \<chi> T"
    by (auto)
  then have
    b2: "\<vinj>-['a]\<lparr>A\<rparr> \<subseteq> \<chi> T"
    by (auto)
  then show  
    b3: "\<vinj>\<lparr>A\<rparr> \<in> rsets"
    by (auto simp add: rsets_def)
qed

lemma vcard_equipotent:
  "vcard A = vcard B \<Leftrightarrow> \<^EP>{:A:}{:B:}"
  apply (simp add: vcard_def vrank_card_def vcard.Abs_inject card_of_equipotent rsets_cong.equiv_class_eq vcard.Abs_inject)
  apply (simp add: subset_order_def rel2op_def op2rel_def)
  apply (rule inj_on_equipotent_image_inject)
  apply (rule subset_inj_on [OF vinj_inj subset_UNIV])+
  done

lemma vcard_subequipotent:
  "vcard A \<le> vcard B \<Leftrightarrow> \<^sEP>{:A:}{:B:}"
  apply (simp add: vcard_def vrank_card_def vrank_char_def lesseq_vcardinal_def vcard.Abs_inverse subequipotence_quot_class_char)
  apply (rule inj_on_subequipotent_image_inject)
  apply (rule subset_inj_on [OF vinj_inj subset_UNIV])+
  done

instantiation
  vcardinal :: "zero"

begin

definition
  "0-[vcardinal] \<defs> vrank_card (\<emptyset>-[VAL])"

instance
  by (intro_classes)

end

lemma zero_wdef [simp]:
  "\<emptyset>-[VAL] \<in> rsets"
  by (simp add: rsets_def)

lemma vcard_zero_empty:
  "vcard \<emptyset>-['a::svaltype] = 0"
  by (simp add: zero_vcardinal_def vcard_def)

lemma vcard_zero_empty_iff:
  "vcard X = 0 \<Leftrightarrow> X = \<emptyset>-['a::svaltype]"
  by (simp add: zero_vcardinal_def vcard_def vrank_card_inject equipotent_empty_iff)

lemma vcardinal_zero_bot:
  "0-[vcardinal] \<le> v"
  using empty_bot [of "vrank_char v"]
  apply (simp add: zero_vcardinal_def lesseq_vcardinal_def)
  apply (rule eq_subeq_trans [OF vrank_card_inverse])
  apply (auto)
  done

lemma vcardinal_zero_glb:
  "v \<le> 0-[vcardinal] \<Leftrightarrow> v = 0"
   apply (simp add: zero_vcardinal_def lesseq_vcardinal_def vrank_card_inverse_iff empty_glb)
   apply (subst (2) vrank_char_inverse [of v, symmetric])
   apply (simp add: vrank_card_inject equipotent_empty_iff)
   done 

instantiation
  vcardinal :: "one"

begin

definition
  "1-[vcardinal] \<defs> vrank_card ({vatom_of \<arb>})"

instance
  by (intro_classes)

end

lemma one_wdef [simp]:
  "{vatom_of \<arb>} \<in> rsets"
  apply (simp add: rsets_def)
  apply (witness "catom")
  apply (rule vatom_of_rank)
  done

lemma vcard_one_singleton:
  "vcard {x::'a::svaltype} = 1"
  using vcard_wdef [of "{x}", simplified]
  apply (simp add: one_vcardinal_def vcard_def vrank_card_inject)
  apply (rule equipotentI [of "{(\<vinj> x \<mapsto> vatom_of \<arb>)}"])
  apply (mauto(fspace) mintro: fin_pfunI)
  apply (mstep(fspace) mintro: fin_pfunI | simp)+
  apply (mauto_full(fspace) mintro: fin_pfunI msimp add: fin_pfun_simp)
  done

lemma vcard_one_singleton_iff:
  "vcard X = 1 \<Leftrightarrow> (\<exists> x \<bullet> X = {x::'a::svaltype})"
  apply (simp add: one_vcardinal_def vcard_def vrank_card_inject equipotent_singleton_iff)
  apply (auto)
proof -
  fix 
    x
  assume
    b1: "\<vinj>\<lparr>X\<rparr> = {x}"
  then have
    "\<vproj>-['a]\<lparr>\<vinj>-['a]\<lparr>X\<rparr>\<rparr> = \<vproj>\<lparr>{x}\<rparr>"
    by (simp)
  then have
    "X = \<vproj>\<lparr>{x}\<rparr>"
    by (simp add: image_aggregate vinj_o_inverse)
  then show
    "(\<exists> x \<bullet> X = {x})"
    by (auto)
qed

instantiation
  vcardinal :: "plus"

begin

definition
  "x + (y::vcardinal) 
  \<defs> vrank_card 
      (vprod_of\<lparr>
        vprod_of\<lparr> {\<vinj> \<True>} \<times> (vrank_char x)\<rparr> \<times> {(\<some> v | v \<in> vrank_char y)} 
        \<union> vprod_of\<lparr>{\<vinj> \<False>} \<times> {(\<some> v | v \<in> vrank_char x)}\<rparr> \<times> (vrank_char y)\<rparr>)"

instance
  by (intro_classes)

end

lemma vcardinal_plus_wdef [simplified, simp]:
  assumes
    a1: "X \<in> rsets" and
    a2: "Y \<in> rsets"
  shows
    "vprod_of\<lparr>vprod_of\<lparr>
      {\<vinj> \<True>} \<times> X\<rparr> \<times> {\<some> x | x \<in> Y} \<union> vprod_of\<lparr>{\<vinj> \<False>} \<times> {\<some> x | x \<in> X}\<rparr> \<times> Y\<rparr> \<in> rsets"
proof -
  from CT_of_char' [of "\<True>"] have 
    b1: "{\<vinj> \<True>} \<subseteq> \<chi> \<^CT>{:\<bool>:}"
    by (auto)
  from CT_of_char' [of "\<False>"] have 
    b2: "{\<vinj> \<False>} \<subseteq> \<chi> \<^CT>{:\<bool>:}"
    by (auto)
  from a1 obtain T where
    b3: "X \<subseteq> \<chi> T"
    by (auto simp add: rsets_def)
  from a2 obtain T' where
    b4: "Y \<subseteq> \<chi> T'"
    by (auto simp add: rsets_def)
  from vrankI [of "\<some> x | x \<in> X"] obtain t where
    b5: "{\<some> x | x \<in> X} \<subseteq> \<chi> t"
    by (auto)
  from vrankI [of "\<some> x | x \<in> Y"] obtain t' where
    b6: "{\<some> x | x \<in> Y} \<subseteq> \<chi> t'"
    by (auto)
  show
    "?thesis"
  proof (multi_cases "X = \<emptyset>" "Y = \<emptyset>")
    assume
      c1: "X = \<emptyset>" and
      c2: "Y = \<emptyset>"
    then show
      "?thesis"
      by (simp add: rsets_def)
  next
    assume
      c1: "X = \<emptyset>" and
      c2: "Y \<noteq> \<emptyset>"
    with b2 b4 b5 show
      "?thesis"
      apply (simp add: rsets_def)
      apply (witness "cprod (cprod (\<^CT>{:\<bool>:}) t) T'")
      apply (auto simp add: vrank_cprod)
      done
  next
    assume
      c1: "X \<noteq> \<emptyset>" and
      c2: "Y = \<emptyset>"
    with b1 b3 b6 show
      "?thesis"
      apply (simp add: rsets_def)
      apply (witness "cprod (cprod (\<^CT>{:\<bool>:}) T) t'")
      apply (auto simp add: vrank_cprod)
      done
  next
    assume
      c1: "X \<noteq> \<emptyset>" and
      c2: "Y \<noteq> \<emptyset>"
    from c1 [simplified nempty_conv, THEN someI_ex] b3 have 
      c3: "{\<some> x | x \<in> X} \<subseteq> \<chi> T"
      by (auto)
    from c2 [simplified nempty_conv, THEN someI_ex] b4 have 
      c4: "{\<some> x | x \<in> Y} \<subseteq> \<chi> T'"
      by (auto)
    from b1 b2 b3 b4 c3 c4 show
      "?thesis"
      apply (simp add: rsets_def)
      apply (witness "cprod (cprod (\<^CT>{:\<bool>:}) T) T'")
      apply (auto simp add: vrank_cprod)
      done
  qed
qed

lemma vrank_char_plus:
  "\<^EP>{:vrank_char (a + (b::vcardinal)):}{:vrank_char a <+> vrank_char b:}"
proof (unfold plus_vcardinal_def)
  let ?X = "vrank_char a"
  let ?Y = "vrank_char b" 
  have 
    "\<^EP>{:vrank_char (vrank_card (vprod_of\<lparr>
               vprod_of\<lparr>{\<vinj> \<True>} \<times> ?X\<rparr> \<times> {(\<some> v | v \<in> ?Y)} 
               \<union> vprod_of\<lparr>{\<vinj> \<False>} \<times> {(\<some> v | v \<in> ?X)}\<rparr> \<times> ?Y\<rparr>))
    :}{:vprod_of\<lparr>{\<vinj> \<True>} \<times> ?X\<rparr> \<times> {(\<some> v | v \<in> ?Y)} 
        \<union> vprod_of\<lparr>{\<vinj> \<False>} \<times> {(\<some> v | v \<in> ?X)}\<rparr> \<times> ?Y:}" (is "\<^EP>{:?LHS:}{:_:}")
    apply (intro 
             cartesian_equipotent_intros vrank_card_inverse_cong 
             subset_inj [OF inj_vprod_of])
    apply (simp)
    done
  also have
    "\<^EP>{:\<dots>
    :}{:(vprod_of\<lparr>{\<vinj> \<True>} \<times> ?X\<rparr> \<times> {(\<some> v | v \<in> ?Y)}) 
         <+> (vprod_of\<lparr>{\<vinj> \<False>} \<times> {(\<some> v | v \<in> ?X)}\<rparr> \<times> ?Y):}"
    apply (rule equipotent_sym)
    apply (intro cartesian_equipotent_intros)
    apply (auto simp add: 
             image_def inj_vprod_of [THEN inj_eq] vinj_inj [THEN inj_eq] disjoint_def)
    done
  also have
    "\<^EP>{:\<dots>
    :}{:?X <+> {(\<some> v | v \<in> ?X)} \<times> ?Y:}"
    by (intro 
          cartesian_equipotent_intros vrank_card_inverse_cong 
          inj_vprod_of [THEN subset_inj] vinj_inj [THEN subset_inj] vcard_wdef)
  also have
    "\<^EP>{:\<dots>
    :}{:?X <+> ?Y:}" (is "\<^EP>{:_:}{:?RHS:}")
    by (intro cartesian_equipotent_intros)
  finally show
    "\<^EP>{:?LHS:}{:?RHS:}"
    by (this)
qed

lemma vrank_char_plus_cong:
  assumes 
    a1: "\<^EP>{:vrank_char a:}{:A:}" and
    a2: "\<^EP>{:vrank_char b:}{:B:}" 
  shows
    "\<^EP>{:vrank_char (a + (b::vcardinal)):}{:A <+> B:}"
  apply (rule equipotent_trans [OF vrank_char_plus])
  apply (intro cartesian_equipotent_intros a1 a2)
  done

lemma vcard_plus_def:
  "vcard X + vcard Y = vcard (X <+> Y)"
proof (simp add: vcard_def vrank_char_equipotent_iff [symmetric])
  have 
    "\<^EP>{:vrank_char ((vrank_card \<vinj>\<lparr>X\<rparr>) + (vrank_card \<vinj>\<lparr>Y\<rparr>))
    :}{:vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>) <+> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>):}" (is "\<^EP>{:?LHS:}{:_:}")
    by (rule vrank_char_plus)
  also have 
    "\<^EP>{:\<dots>
    :}{:X <+> Y:}"
    by (intro cartesian_equipotent_intros subset_inj [OF vinj_inj] vrank_card_inverse_cong vcard_wdef)
  also have 
    "\<^EP>{:\<dots>
    :}{:vrank_char (vrank_card \<vinj>\<lparr>X <+> Y\<rparr>):}" (is "\<^EP>{:_:}{:?RHS:}")
    apply (rule equipotent_sym)
    apply (intro cartesian_equipotent_intros subset_inj [OF vinj_inj] vrank_card_inverse_cong vcard_wdef)
    done
  finally show
    "\<^EP>{:?LHS:}{:?RHS:}"
    by (this)
qed

lemmas vcard_Plus = vcard_plus_def [symmetric]

instance vcardinal :: comm_monoid_add
proof (intro_classes)
  fix
    a :: "vcardinal" and
    b :: "vcardinal" and
    c :: "vcardinal"
  show
    "(a + b) + c = a + (b + c)"
  proof (simp add: vrank_char_equipotent_iff [symmetric])
    have 
      "\<^EP>{:vrank_char ((a + b) + c)
      :}{:((vrank_char a) <+> (vrank_char b)) <+> (vrank_char c):}"
      by (intro cartesian_equipotent_intros vrank_char_plus_cong)
    also have 
      "\<^EP>{:\<dots>
      :}{:(vrank_char a) <+> ((vrank_char b) <+> (vrank_char c)):}"
      by (rule equipotent_Plus_assoc)
    also have 
      "\<^EP>{:\<dots>
      :}{:vrank_char (a + (b + c)):}"
      apply (rule equipotent_sym)
      apply (intro cartesian_equipotent_intros vrank_char_plus_cong)
      done
    finally show
      "\<^EP>{:vrank_char ((a + b) + c):}{:vrank_char (a + (b + c)):}"
      by (this)
  qed
next
  fix
    a :: "vcardinal" and
    b :: "vcardinal"
  show
    "a + b = b + a"
  proof (simp add: vrank_char_equipotent_iff [symmetric])
    have 
      "\<^EP>{:vrank_char (a + b) 
      :}{:(vrank_char a) <+> (vrank_char b):}"
      by (intro cartesian_equipotent_intros vrank_char_plus_cong)
    also have 
      "\<^EP>{:\<dots>
      :}{:(vrank_char b) <+> (vrank_char a):}"
      by (rule equipotent_Plus_com)
    also have 
      "\<^EP>{:\<dots>
      :}{:vrank_char (b + a):}"
      apply (rule equipotent_sym)
      apply (intro cartesian_equipotent_intros vrank_char_plus_cong)
      done
    finally show
      "\<^EP>{:vrank_char (a + b):}{:vrank_char (b + a):}"
      by (this)
  qed
next
  fix
    a :: "vcardinal"
  show
    "0 + a = a" 
  proof (simp add: vrank_char_equipotent_iff [symmetric])
    have 
      "\<^EP>{:vrank_char (0 + a)
      :}{:(vrank_char 0) <+> (vrank_char a):}"
      by (intro cartesian_equipotent_intros vrank_char_plus_cong)
    also have 
      "\<^EP>{:\<dots>
      :}{:\<emptyset>-[VAL] <+> vrank_char a:}"
      apply (intro cartesian_equipotent_intros)
      apply (simp add: zero_vcardinal_def vcard_def vrank_card_inverse)
      done
    also have 
      "\<^EP>{:\<dots>
      :}{:vrank_char a:}"
      by (intro cartesian_equipotent_intros)
    finally show
      "\<^EP>{:vrank_char (0 + a):}{:vrank_char a:}"
      by (this)
  qed
qed

instantiation
  vcardinal :: "times"

begin

definition
  "x * (y::vcardinal) \<defs> vrank_card (vprod_of\<lparr>(vrank_char x) \<times> (vrank_char y)\<rparr>)"

instance
  by (intro_classes)

end

lemma vcard_times_wdef [simp]:
  assumes
    a1: "X \<in> rsets" and
    a2: "Y \<in> rsets"
  shows
    "vprod_of\<lparr>X \<times> Y\<rparr> \<in> rsets"
proof -
  from a1 obtain T where
    b1: "X \<subseteq> \<chi> T"
    by (auto simp add: rsets_def)
  from a2 obtain T' where
    b2: "Y \<subseteq> \<chi> T'"
    by (auto simp add: rsets_def)
  from b1 b2 show
    "?thesis"
    apply (simp add: rsets_def)
    apply (witness "cprod T T'")
    apply (auto simp add: vrank_cprod)
    done
qed

lemma vrank_char_times:
  "\<^EP>{:vrank_char (a * (b::vcardinal)):}{:vrank_char a \<times> vrank_char b:}"
  by (auto intro!: cartesian_equipotent_intros vrank_card_inverse_cong subset_inj [OF inj_vprod_of] simp add: times_vcardinal_def)

lemma vcard_times_def:
  "vcard X * vcard Y = vcard (X \<times> Y)"
  apply (subst vrank_char_equipotent_iff [symmetric])
  apply (rule equipotent_trans [OF vrank_char_times])
proof -
  have 
    "\<^EP>{:vrank_char (vcard X) \<times> vrank_char (vcard Y)
    :}{:X \<times> Y:}"
    by (auto intro!: cartesian_equipotent_intros vrank_card_inverse_cong subset_inj [OF vinj_inj] simp add: vcard_def)
  also have 
    "\<^EP>{:\<dots>
    :}{:vrank_char (vcard (X \<times> Y)):}"
    apply (rule equipotent_sym)
    apply (auto intro!: cartesian_equipotent_intros vrank_card_inverse_cong subset_inj [OF vinj_inj] simp add: vcard_def)
    done
  finally show
    "\<^EP>{:vrank_char (vcard X) \<times> vrank_char (vcard Y):}{:vrank_char (vcard (X \<times> Y)):}"
    by (this)
qed

instance
  vcardinal :: "comm_monoid_mult"
proof (intro_classes)
  fix 
    a :: "vcardinal" and
    b :: "vcardinal" and
    c :: "vcardinal"
  show
    "(a * b) * c = a * (b * c)"
  proof (subst vrank_char_equipotent_iff [symmetric])
    have 
      "\<^EP>{:vrank_char ((a * b) * c)
    :}{:((vrank_char a) \<times> (vrank_char b)) \<times> (vrank_char c):}"
      by (auto intro!: cartesian_equipotent_intros equipotent_trans [OF vrank_char_times])
    also have 
      "\<^EP>{:\<dots>
      :}{:(vrank_char a) \<times> ((vrank_char b) \<times> (vrank_char c)):}"   
      by (rule equipotent_prod_assoc) 
    also have 
      "\<^EP>{:\<dots>
      :}{:vrank_char (a * (b * c)):}"   
      apply (rule equipotent_sym)
      apply (auto intro!: cartesian_equipotent_intros equipotent_trans [OF vrank_char_times])
      done
    finally show
      "\<^EP>{:vrank_char ((a * b) * c):}{:vrank_char (a * (b * c)):}"
      by (this)
  qed
next
  fix 
    a :: "vcardinal" and
    b :: "vcardinal"
  show
    "a * b = b * a"
  proof (subst vrank_char_equipotent_iff [symmetric])
    have 
      "\<^EP>{:vrank_char (a * b)
    :}{:(vrank_char a) \<times> (vrank_char b):}"
      by (auto intro!: cartesian_equipotent_intros equipotent_trans [OF vrank_char_times])
    also have 
      "\<^EP>{:\<dots>
    :}{:(vrank_char b) \<times> (vrank_char a):}"
      by (rule equipotent_prod_com)
    also have 
      "\<^EP>{:\<dots>
    :}{:vrank_char (b * a):}"
      apply (rule equipotent_sym)
      apply (auto intro!: cartesian_equipotent_intros equipotent_trans [OF vrank_char_times])
      done
    finally show
      "\<^EP>{:vrank_char (a * b):}{:vrank_char (b * a):}"
      by (this)
  qed
next
  fix 
    a :: "vcardinal"
  show
    "1 * a = a"
  proof (subst vrank_char_equipotent_iff [symmetric])
    have 
      "\<^EP>{:vrank_char (1 * a)
    :}{:{vatom_of \<arb>} \<times> (vrank_char a):}"
      by (auto intro!: cartesian_equipotent_intros vrank_card_inverse_cong equipotent_trans [OF vrank_char_times] simp add: one_vcardinal_def simp del: finite_cross)
    also have 
      "\<^EP>{:\<dots>
    :}{:vrank_char a:}"
      by (auto intro!: cartesian_equipotent_intros simp del: finite_cross)
    finally show 
      "\<^EP>{:vrank_char (1 * a):}{:vrank_char a:}"
      by (this)
  qed
qed

instance
  vcardinal :: comm_semiring_1
proof (intro_classes)
  fix 
    a :: "vcardinal" and
    b :: "vcardinal" and
    c :: "vcardinal"
  show
    "(a + b) * c = (a * c) + (b * c)"
  proof (subst vrank_char_equipotent_iff [symmetric])
    have
      "\<^EP>{:vrank_char ((a + b) * c)
    :}{:((vrank_char a) <+> (vrank_char b)) \<times> (vrank_char c):}"
      by (auto intro!: cartesian_equipotent_intros equipotent_trans [OF vrank_char_times] equipotent_trans [OF vrank_char_plus])
    also have 
      "\<^EP>{:\<dots>
    :}{:((vrank_char a) \<times> (vrank_char c)) <+> ((vrank_char b) \<times> (vrank_char c)):}"
      apply (rule equipotentI [of "(\<glambda> (xy, z) | (xy, z) \<in> ((vrank_char a) <+> (vrank_char b)) \<times> (vrank_char c) \<bullet> \<case> xy \<of> Inl x \<longrightarrow> Inl (x, z) | Inr y \<longrightarrow> Inr (y, z) \<esac>)"])
      apply (mauto_full(fspace) msimp add: split_def glambda_dom glambda_ran)
      apply (auto)
      apply (auto split: sum.splits)
      done
    also have 
      "\<^EP>{:\<dots>
    :}{:vrank_char ((a * c) + (b * c)):}"
      apply (rule equipotent_sym)
      apply (auto intro!: cartesian_equipotent_intros equipotent_trans [OF vrank_char_times] equipotent_trans [OF vrank_char_plus])
      done
    finally show 
      "\<^EP>{:vrank_char ((a + b) * c):}{:vrank_char ((a * c) + (b * c)):}"
      by (this)
  qed
next
  fix 
    a :: "vcardinal" 
  show
    "0 * a = 0"
  proof (subst vrank_char_equipotent_iff [symmetric])
    have
      "\<^EP>{:vrank_char (0 * a)
    :}{:\<emptyset>-[VAL] \<times> (vrank_char a):}"
      apply (intro cartesian_equipotent_intros equipotent_trans [OF vrank_char_times])
      apply (auto intro!: cartesian_equipotent_intros vrank_card_inverse_cong simp add: zero_vcardinal_def)
      done
    also have 
      "\<^EP>{:\<dots>
      :}{:vrank_char 0:}"
      apply (rule equipotent_sym)
      apply (auto intro!: cartesian_equipotent_intros vrank_card_inverse_cong equipotent_empty simp add: zero_vcardinal_def)
      done
    finally show 
      "\<^EP>{:vrank_char (0 * a):}{:vrank_char 0:}"
      by (this)
  qed
  then show
    "a * 0 = 0"
    by (simp add: mult_commute)
next
  show
    "0-[vcardinal] \<noteq> 1"
    apply (simp add: zero_vcardinal_def one_vcardinal_def vrank_card_inject equipotent_def)
    apply (rule set_eqI)
    apply (auto)
    apply (mauto(fspace))
    done 
qed

instance
  vcardinal :: "power"
  by (intro_classes)

term "(vcard X)\<xexp>\<^bzup>n\<^ezup>"

lemma vcard_power_def:
  fixes
    X :: "('a::svaltype) set"
  shows
    "(vcard X)\<xexp>\<^bzup>n\<^ezup> = vcard ({0..<n} \<ztfun> X)"
proof (induct "n" type: nat)
  show 
    "(vcard X)\<xexp>\<^bzup>0\<^ezup> = vcard ({0..<0-[\<nat>]} \<ztfun> X)"
    apply (simp add: vcard_one_singleton_iff)
    apply (witness "\<emptyset>-[\<nat> \<times> 'a]")
    apply (auto)
    apply (mauto_full(fspace) mintro: fin_pfunI)
    done
next
  fix 
    n :: "\<nat>"
  assume
    b1: "(vcard X)\<xexp>\<^bzup>n\<^ezup> = vcard ({0..<n} \<ztfun> X)"
  have
    b2: "\<^EP>{:{0..<Suc n} \<ztfun> X:}{:X \<times> ({0..<n} \<ztfun> X):}"
    apply (rule equipotentI [of "(\<glambda> f | f \<in> {0..<Suc n} \<ztfun> X \<bullet> (f\<cdot>n, {n} \<zdsub> f))"])
    apply (mauto_full(fspace) msimp add: glambda_dom glambda_ran)
    apply (msafe_no_assms(inference))
    apply (simp_all)
  proof -
    fix 
      f g
    assume
      c1: "f \<in> {0..<Suc n} \<ztfun> X" and
      c2: "g \<in> {0..<Suc n} \<ztfun> X" and
      c3: "f\<cdot>n = g\<cdot>n" and
      c4: "{n} \<zdsub> f = {n} \<zdsub> g"
    show
      "f = g"
      apply (rule tfun_eqI [OF c1 c2])
      apply (auto)
    proof -
      fix 
        j
      assume
        d1: "j < Suc n"
      from c4 have 
        d2: "({n} \<zdsub> f)\<cdot>j = ({n} \<zdsub> g)\<cdot>j"
        by (simp)
      with d1 c3 show
        "f\<cdot>j = g\<cdot>j"
        by (auto simp add: dsub_beta less_Suc_eq)
    qed
  next
    show 
      "{ f | f \<in> {0..<Suc n} \<ztfun> X \<bullet> (f\<cdot>n, {n} \<zdsub> f) } = X \<times> ({0..<n} \<ztfun> X)"
    proof (auto intro!: tfun_range)
      fix
        f
      assume
        d1: "f \<in> {0..<Suc n} \<ztfun> X"
      then show
        "{n} \<zdsub> f \<in> {0..<n} \<ztfun> X"
        apply (mauto(fspace))
        apply (auto simp add: dsub_mem dsub_dom subset_def ran_char2 [OF rel_min])
        done
    next
      fix
        x f'
      assume
        d1: "x \<in> X" and
        d2: "f' \<in> {0..<n} \<ztfun> X"
      then show
        "(\<exists> f \<bullet> x = f\<cdot>n \<and> f' = {n} \<zdsub> f \<and> f \<in> {0..<Suc n} \<ztfun> X)"
        apply (witness "f' \<union> {(n \<mapsto> x)}")
        apply (msafe_no_assms(inference))
      proof -
        from d1 d2 show
          f1: "f' \<union> {(n \<mapsto> x)} \<in> {0..<Suc n} \<ztfun> X" 
          apply (mauto_full(fspace) mintro: fin_pfunI)
          apply (auto)
          done
        from f1 [THEN tfun_functional] show
          "x = (f' \<union> {(n \<mapsto> x)})\<cdot>n"
          by (simp add: insert_beta)
        from d2 [THEN tfun_dom] show
          "f' = {n} \<zdsub> (f' \<union> {(n \<mapsto> x)})"
          by (auto simp add: dsub_mem)
      qed
    qed
  qed
  from b1 b2 [THEN equipotent_sym] show 
    "(vcard X)\<xexp>\<^bzup>Suc n\<^ezup> = vcard ({0..<Suc n} \<ztfun> X)"
    by (simp add: vcard_times_def vcard_equipotent)
qed

definition
  vpower :: "[vcardinal, vcardinal] \<rightarrow> vcardinal" (infixr "\<vpow>" 80)
where
  "v\<vpow>u \<defs> vrank_card ((graph_VAL (vrank_CT u) (vrank_CT v))\<lparr>vrank_char u \<ztfun> vrank_char v\<rparr>)"

lemma vpower_wdef [simp]:
  assumes
    a1: "X \<in> rsets" and
    a2: "Y \<in> rsets"
  shows
    "(graph_VAL (CT_of_rset Y) (CT_of_rset X))\<lparr>Y \<ztfun> X\<rparr> \<in> rsets"
  apply (rule rsets_memI [of _ "cset (cprod (CT_of_rset Y) (CT_of_rset X))"])
  apply (auto intro!: graph_VAL_vrank)
  using CT_of_rset_char [OF a1] CT_of_rset_char [OF a2]
  apply (mauto(fspace))
  done

lemma vcard_vpower:
  fixes 
    X :: "('a::svaltype) set" and
    Y :: "('b::svaltype) set"
  shows
    "(vcard X)\<vpow>(vcard Y) = vcard (Y \<ztfun> X)"
proof (simp add: vpower_def vcard_def vrank_card_inject vrank_CT_def)
  have 
    "\<^EP>{:(graph_VAL (CT_of_rset (vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>))) (CT_of_rset (vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>))))\<lparr>vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>)\<rparr>
    :}{:vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>):}" (is "\<^EP>{:?LHS:}{:_:}")
    apply (rule equipotentIinj_on' [THEN equipotent_sym])
    apply (rule subset_inj_on [OF graph_VAL_inj])
    apply (auto)
    apply (mauto_full(fspace) msimp add: CT_of_rset_char)
    done
  also have "\<^EP>{:\<dots>
    :}{:\<vinj>\<lparr>Y\<rparr> \<ztfun> \<vinj>\<lparr>X\<rparr>:}"
  proof -
    have 
      c1: "\<^EP>{:vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>):}{:\<vinj>\<lparr>Y\<rparr>:}"
      by (simp add: vrank_card_inverse)
    then obtain f where
      c2: "f \<in> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) \<zbij> \<vinj>\<lparr>Y\<rparr>"
      by (auto simp add: equipotent_def)
    have 
      c3: "\<^EP>{:vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>):}{:\<vinj>\<lparr>X\<rparr>:}"
      by (simp add: vrank_card_inverse)
    then obtain g where
      c4: "g \<in> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>) \<zbij> \<vinj>\<lparr>X\<rparr>"
      by (auto simp add: equipotent_def)
    show ?thesis
      apply (rule equipotentI [of "(\<glambda> h | h \<in> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>) \<bullet> ((fun_appl f) \<par> (fun_appl g))\<lparr>h\<rparr>)"])
      apply (mauto_full(fspace) msimp add: glambda_dom glambda_ran)
      apply (msafe_no_assms(inference))
    proof -
      fix
        h k
      assume
        d1: "((fun_appl f) \<par> (fun_appl g))\<lparr>h\<rparr> = ((fun_appl f) \<par> (fun_appl g))\<lparr>k\<rparr>" and
        d2: "h \<in>  vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>)" and
        d3: "k \<in>  vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>)"
      show
        "h = k"
      proof (auto)
        fix
          x y
        assume
          e1: "(x \<mapsto> y) \<in> h"
        then have 
          "(f\<cdot>x \<mapsto> g\<cdot>y) \<in> ((fun_appl f) \<par> (fun_appl g))\<lparr>h\<rparr>"
          by (auto simp add: map_pair_def image_conv)
        with d1 have 
          "(f\<cdot>x \<mapsto> g\<cdot>y) \<in> ((fun_appl f) \<par> (fun_appl g))\<lparr>k\<rparr>"
          by (simp)
        then show
          "(x \<mapsto> y) \<in> k"
        proof (auto simp add: map_pair_def image_conv)
          fix 
            a b
          assume 
            f1: "f\<cdot>x = f\<cdot>a" and
            f2: "g\<cdot>y = g\<cdot>b" and
            f3: "(a \<mapsto> b) \<in> k"
          from f1 e1 f3 have 
            f4: "x = a"
            by (simp add:  bij_inj_iff [OF c2] tfun_dom_mem [OF d2] tfun_dom_mem [OF d3])
          from f2 e1 f3 have 
            f5: "y = b"
            by (simp add:  bij_inj_iff [OF c4] tfun_ran_mem [OF d2] tfun_ran_mem [OF d3])
          from f3 f4 f5 show
            "(x \<mapsto> y) \<in> k"
            by (auto)
        qed
      next
        fix
          x y
        assume
          e1: "(x \<mapsto> y) \<in> k"
        then have 
          "(f\<cdot>x \<mapsto> g\<cdot>y) \<in> ((fun_appl f) \<par> (fun_appl g))\<lparr>k\<rparr>"
          by (auto simp add: map_pair_def image_conv)
        with d1 have 
          "(f\<cdot>x \<mapsto> g\<cdot>y) \<in> ((fun_appl f) \<par> (fun_appl g))\<lparr>h\<rparr>"
          by (simp)
        then show
          "(x \<mapsto> y) \<in> h"
        proof (auto simp add: map_pair_def image_conv)
          fix 
            a b
          assume 
            f1: "f\<cdot>x = f\<cdot>a" and
            f2: "g\<cdot>y = g\<cdot>b" and
            f3: "(a \<mapsto> b) \<in> h"
          from f1 e1 f3 have 
            f4: "x = a"
            by (simp add:  bij_inj_iff [OF c2] tfun_dom_mem [OF d2] tfun_dom_mem [OF d3])
          from f2 e1 f3 have 
            f5: "y = b"
            by (simp add:  bij_inj_iff [OF c4] tfun_ran_mem [OF d2] tfun_ran_mem [OF d3])
         from f3 f4 f5 show
            "(x \<mapsto> y) \<in> h"
            by (auto)
        qed
      qed
    next
      show 
        "{h 
        | h \<in> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>) 
        \<bullet> ((fun_appl f) \<par> (fun_appl g))\<lparr>h\<rparr>}
        = \<vinj>\<lparr>Y\<rparr> \<ztfun> \<vinj>\<lparr>X\<rparr>"
      proof (auto)
        fix 
          h 
        assume
          e1: "h \<in> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>)"
        show
          "((fun_appl f) \<par> (fun_appl g))\<lparr>h\<rparr> \<in> \<vinj>\<lparr>Y\<rparr> \<ztfun> \<vinj>\<lparr>X\<rparr>"
        proof (mauto_full(fspace) msimp add: map_pair_def image_conv eind_split)
          show 
            "functional { a b | (a \<mapsto> b) \<in> h \<bullet> (f\<cdot>a \<mapsto> g\<cdot>b) }"
            apply (auto intro!: functionalI simp add: bij_inj_iff [OF c2] tfun_dom_mem [OF e1])
            apply (auto dest!: tfun_beta [OF e1, symmetric])
            done
          from bij_range [OF c2 tfun_dom_mem [OF e1]] show
            "\<zdom> { a b | (a \<mapsto> b) \<in> h \<bullet> (f\<cdot>a \<mapsto> g\<cdot>b) } = { y | y \<in> Y \<bullet> \<vinj> y }"
          proof (auto simp add: Z_dom_def eind_def)
            fix
              y
            assume
              g1: "y \<in> Y"
            then have
              g2: "\<vinj> y \<in> \<vinj>\<lparr>Y\<rparr>"
              by (rule imageI)
            then have 
              g3: "(f\<^sup>\<sim>)\<cdot>(\<vinj> y) \<in> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>)" 
              by (rule bij_inv_range [OF c2])
            then have
              g4: "h\<cdot>((f\<^sup>\<sim>)\<cdot>(\<vinj> y)) \<in> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>)" 
              by (rule tfun_range [OF e1])
            then have
              g5: "g\<cdot>(h\<cdot>((f\<^sup>\<sim>)\<cdot>(\<vinj> y))) \<in> \<vinj>\<lparr>X\<rparr>"
              by (rule bij_range [OF c4])
            show
              "(\<exists> y' a \<bullet> \<vinj> y = f\<cdot>a \<and> (\<exists> b \<bullet> y' = g\<cdot>b \<and> (a, b) \<in> h))"
              apply (witness "g\<cdot>(h\<cdot>((f\<^sup>\<sim>)\<cdot>(\<vinj> y)))")
              apply (witness "(f\<^sup>\<sim>)\<cdot>(\<vinj> y)")
              apply (simp add:  bij_f_f_inv_beta [OF c2, OF g2])
              apply (witness "h\<cdot>((f\<^sup>\<sim>)\<cdot>(\<vinj> y))")
              apply (simp add: tfun_appl [OF e1 g3])
              done
          qed
          from bij_range [OF c4 tfun_ran_mem [OF e1]] show
            "\<zran> { a b | (a \<mapsto> b) \<in> h \<bullet> (f\<cdot>a \<mapsto> g\<cdot>b) } \<subseteq> { x | x \<in> X \<bullet> \<vinj> x }"
            by (auto simp add: eind_def)
        qed
      next
        fix
          k
        assume
          e1: "k \<in> \<vinj>\<lparr>Y\<rparr> \<ztfun> \<vinj>\<lparr>X\<rparr>"
        show
          "(\<exists> h \<bullet> k = ((fun_appl f) \<par> (fun_appl g))\<lparr>h\<rparr> \<and> h \<in> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>))"
          apply (witness "((fun_appl (f\<^sup>\<sim>)) \<par> (fun_appl (g\<^sup>\<sim>)))\<lparr>k\<rparr>")
          apply (msafe_no_assms(inference))
        proof -
          show
            "k = ((fun_appl f) \<par> (fun_appl g))\<lparr>((fun_appl (f\<^sup>\<sim>)) \<par> (fun_appl (g\<^sup>\<sim>)))\<lparr>k\<rparr>\<rparr>"
            by (auto 
                 intro!: exI 
                 simp add: 
                   map_pair_def image_conv bij_f_f_inv_beta [OF c2, OF tfun_dom_mem [OF e1]] 
                   bij_f_f_inv_beta [OF c4, OF tfun_ran_mem [OF e1]] eind_def)
          show
            "((fun_appl (f\<^sup>\<sim>)) \<par> (fun_appl (g\<^sup>\<sim>)))\<lparr>k\<rparr> \<in> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>)"
          proof (mauto_full(fspace))
            show 
              "functional ((fun_appl (f\<^sup>\<sim>)) \<par> (fun_appl (g\<^sup>\<sim>)))\<lparr>k\<rparr>"
              apply (auto intro!: functionalI simp add: bij_inv_inj_iff [OF c2] tfun_dom_mem [OF e1] bij_inv_inj_iff [OF c4] tfun_ran_mem [OF e1])
              apply (auto dest!: tfun_beta [OF e1, symmetric])
              done
            show
              "\<zdom> ((fun_appl (f\<^sup>\<sim>)) \<par> (fun_appl (g\<^sup>\<sim>)))\<lparr>k\<rparr> = vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>)"
            proof (auto simp add: bij_inv_range [OF c2] tfun_dom_mem [OF e1])
              fix 
                y' 
              assume
                i1: "y' \<in> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>)"
              show
                "y' \<in> \<zdom> ((fun_appl (f\<^sup>\<sim>)) \<par> (fun_appl (g\<^sup>\<sim>)))\<lparr>k\<rparr>"
                apply (auto simp add: map_pair_def image_conv Domain_iff)
                apply (witness "(g\<^sup>\<sim>)\<cdot>(k\<cdot>(f\<cdot>y'))")
                apply (witness "f\<cdot>y'")
                apply (simp add: bij_f_inv_f_beta [OF c2 i1])
                apply (witness "k\<cdot>(f\<cdot>y')")
                apply (simp add: tfun_appl [OF e1] bij_range [OF c2 i1])
                done
            qed
            show
              "\<zran> ((fun_appl (f\<^sup>\<sim>)) \<par> (fun_appl (g\<^sup>\<sim>)))\<lparr>k\<rparr> \<subseteq> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>)"
              by (auto simp add: bij_inv_range [OF c4] tfun_ran_mem [OF e1])
          qed
        qed
      qed
    next
      fix
        h k
      assume
        d1: "h = k" and
        d2: "h \<in> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) 
                   \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>)" and
        d3: "k \<in> vrank_char (vrank_card \<vinj>\<lparr>Y\<rparr>) 
                   \<ztfun> vrank_char (vrank_card \<vinj>\<lparr>X\<rparr>)"
      show
        "((fun_appl f) \<par> (fun_appl g))\<lparr>h\<rparr> 
        = ((fun_appl f) \<par> (fun_appl g))\<lparr>k\<rparr>"
        by (simp add: d1)
    qed
  qed
  also have "\<^EP>{:\<dots>
    :}{:\<vinj>\<lparr>Y \<ztfun> X\<rparr>:}"
    apply (rule 
             equipotentI 
               [of "(\<glambda> f 
                    | f \<in> \<vinj>-['b]\<lparr>Y\<rparr> \<ztfun> \<vinj>-['a]\<lparr>X\<rparr> 
                    \<bullet> \<vinj>-['b \<leftrightarrow> 'a]
                        (\<glambda> y | y \<in> Y \<bullet> \<vproj>-['a](f\<cdot>(\<vinj>-['b] y))))"])
    apply (mauto_full(fspace) msimp add: glambda_dom glambda_ran)
    apply (msafe_no_assms(inference))
  proof -
    fix 
      h k
    assume 
      c1: "h \<in> \<vinj>\<lparr>Y\<rparr> \<ztfun> \<vinj>\<lparr>X\<rparr>" and
      c2: "k \<in> \<vinj>\<lparr>Y\<rparr> \<ztfun> \<vinj>\<lparr>X\<rparr>" and
      c3: "\<vinj>-['b \<leftrightarrow> 'a](\<glambda> y | y \<in> Y \<bullet> \<vproj>-['a](h\<cdot>(\<vinj>-['b] y))) 
          = \<vinj>-['b \<leftrightarrow> 'a](\<glambda> y | y \<in> Y \<bullet> \<vproj>-['a](k\<cdot>(\<vinj>-['b] y)))"
    from c1 c2 show
      "h = k"
    proof (rule tfun_eqI)
      fix 
        y'
      assume
        d1: "y' \<in> \<vinj>-['b]\<lparr>Y\<rparr>"
      then obtain y :: "'b" where
        d2: "y \<in> Y" and
        d3: "y' = \<vinj>-['b] y"
        by (auto)
      note c3
      also have 
       "(\<vinj>-['b \<leftrightarrow> 'a](\<glambda> y | y \<in> Y \<bullet> \<vproj>-['a](h\<cdot>(\<vinj>-['b] y))) 
        = \<vinj>-['b \<leftrightarrow> 'a](\<glambda> y | y \<in> Y \<bullet> \<vproj>-['a](k\<cdot>(\<vinj>-['b] y))))
        \<Rightarrow> ((\<glambda> y | y \<in> Y \<bullet> \<vproj>-['a](h\<cdot>(\<vinj>-['b] y))) 
           = (\<glambda> y | y \<in> Y \<bullet> \<vproj>-['a](k\<cdot>(\<vinj>-['b] y))))"
        by (simp add:  vinj_inj [THEN inj_on_iff])
      also have "\<dots>
        \<Rightarrow> (\<forall> y | y \<in> Y \<bullet> \<vproj>-['a](h\<cdot>(\<vinj>-['b] y)) = \<vproj>-['a](k\<cdot>(\<vinj>-['b] y)))"
        by (simp add: glambda_eq)
      also have "\<dots>
        \<Rightarrow> (\<forall> y | y \<in> Y \<bullet> h\<cdot>(\<vinj>-['b] y) = k\<cdot>(\<vinj>-['b] y))"
        apply (msafe_no_assms(wind))
        apply (msafe_no_assms(inference))
        apply (rule inj_onD [OF inj_on_inv_into [of _ _ "UNIV", OF eq_refl, OF refl]])
        apply (simp add: vproj_def)
        apply (auto intro: subsetD [OF _ tfun_range [OF c1]] subsetD [OF _ tfun_range [OF c2]] d1)
        done
      finally show
        "h\<cdot>y' = k\<cdot>y'"
        using d2 d3
        by (auto)
    qed
  next
    show
      "{ f | f \<in> \<vinj>-['b]\<lparr>Y\<rparr> \<ztfun> \<vinj>-['a]\<lparr>X\<rparr> 
           \<bullet> \<vinj>-['b \<leftrightarrow> 'a](\<glambda> y | y \<in> Y \<bullet> \<vproj>-['a](f\<cdot>(\<vinj>-['b] y)))}
      = \<vinj>\<lparr>Y \<ztfun> X\<rparr>"
    proof (auto intro!: imageI)
      fix 
        f
      assume
        e1: "f \<in> \<vinj>-['b]\<lparr>Y\<rparr> \<ztfun> \<vinj>-['a]\<lparr>X\<rparr>"
      show
        "(\<glambda> y | y \<in> Y \<bullet> \<vproj>-['a](f\<cdot>(\<vinj>-['b] y))) \<in> Y \<ztfun> X"
        apply (mauto_full(fspace) msimp add: glambda_dom glambda_ran)
        apply (auto)
      proof -
        fix
          y
        assume
          f1: "y \<in> Y"
        then have
          "\<vinj> y \<in> \<vinj>\<lparr>Y\<rparr>"
          by (auto)
        with e1 have
          "f\<cdot>(\<vinj>-['b] y) \<in> \<vinj>-['a]\<lparr>X\<rparr>"
          by (rule tfun_range)
        then obtain x where
          "x \<in> X" "f\<cdot>(\<vinj>-['b] y) = \<vinj>-['a] x" 
          by (auto)
        then show
          "\<vproj>-['a](f\<cdot>(\<vinj>-['b] y)) \<in> X"
          by (auto simp add: vinj_inverse)       
      qed
    next
      fix
        g 
      assume
        e1: "g \<in> Y \<ztfun> X"
      show
        "(\<exists> f \<bullet> 
          \<vinj> g 
          = \<vinj> (\<glambda> y 
                    | y \<in> Y 
                    \<bullet> \<vproj>-['a](f\<cdot>(\<vinj>-['b] y))) \<and> 
                      f \<in> \<vinj>-['b]\<lparr>Y\<rparr> \<ztfun> \<vinj>-['a]\<lparr>X\<rparr>)"
        apply (witness "(\<glambda> y' 
                        | y' \<in> \<vinj>-['b]\<lparr>Y\<rparr> 
                        \<bullet> \<vinj>-['a] (g\<cdot>(\<vproj> y')))")
        apply (msafe_no_assms(inference))
        apply (mauto_full(fspace) msimp add: glambda_dom glambda_ran)
        apply (auto 
                 intro!: 
                   imageI 
                 simp add: 
                   vinj_inj [THEN inj_on_iff] 
                   glambda_mem tfun_dom_mem [OF e1] glambda_beta vinj_inverse 
                   tfun_beta [OF e1] tfun_appl [OF e1] tfun_range [OF e1])
        done
    qed
  qed (simp)
  finally show
    "\<^EP>{:(graph_VAL 
      (CT_of_rset (vrank_char (vrank_card \<vinj>-['b]\<lparr>Y\<rparr>))) 
      (CT_of_rset (vrank_char (vrank_card \<vinj>-['a]\<lparr>X\<rparr>))))
        \<lparr>vrank_char (vrank_card \<vinj>-['b]\<lparr>Y\<rparr>) 
          \<ztfun> vrank_char (vrank_card \<vinj>-['a]\<lparr>X\<rparr>)\<rparr>
    :}{:\<vinj>-['b \<leftrightarrow> 'a]\<lparr>Y \<ztfun> X\<rparr>:}"
    by (this)
qed

lemma vpow_vcard_distinct:
  fixes
    X :: "('a::svaltype) set"
  shows
    "(vcard \<univ>-[\<bool>]) \<vpow> (vcard X) \<noteq> (vcard X)"
  using Cantor_cor_graphs [of "\<univ>-[\<bool>]" "X"]
  apply (rule contrapos_nn)
  apply (auto elim!: equipotentE simp add: vcard_vpower vcard_equipotent subequipotent_refl)
  done

text {*

The strictly greater cardinality of power sets (and other function spaces) 
leads to a countable hierarchy of infinite cardinalities.

The first infinite cardinal is the countable cardinal @{text "\<^aleph>[:0:]"} 
and each successor infinite cardinal is the cardinality of its predecessor's power set.

This covers all the cardinals of @{text "vcardinal"}, because it is
constructed from the naturals using finite cross products and power sets. 
Larger cardinals would be possible if a larger base were used.\footnote{
The underspecification of the @{text "ind"} type means that this is not strictly true, 
in the sense that @{text "ind"} has some arbitrary cardinality, bounded below by the naturals. 
Perhaps @{text "ind"} should not be used as the base set for @{text "VAL"}?}
 We do not currently provide a proof of this, but expect to return as time permits.

Note that the cardinality of the reals (@{text "\<real>"}) must, 
in our model, be @{text "\<^aleph>[:1:]"}, although again 
we do not pause to establish this formally.

*}

primrec
  aleph :: "\<nat> \<rightarrow> vcardinal" ("\<^aleph>[:_:]")
where
  aleph_0:   "\<^aleph>[:0:] = vcard \<univ>-[nat]" |
  aleph_Suc: "\<^aleph>[:Suc n:] = (vcard \<univ>-[\<bool>]) \<vpow> \<^aleph>[:n:]"

notation (xsymbols output)
  aleph ("\<aleph>\<^bsub>_\<^esub>" [1000] 999)

section {* Cardinality calculations *}
(*
instantiation
  vcardinal :: number

begin
  
definition
  "number_of n \<defs> \<if> n < 0 \<then> 0 \<else> vcard {0..<n} \<fi>"

instance
  by (intro_classes)

end
*)

instance vcardinal :: numeral ..

(*
lemma vcardinal_numeral_0_eq_0 [simp]:
  "numeral 0 = 0-[vcardinal]"
  by (simp add: number_of_vcardinal_def vcard_zero_empty_iff Int.Pls_def)
*)

(*

B: I suspect all the number_of stuff is now redundant?

*)

lemma "((numeral Num.One)::vcardinal) = 1-[vcardinal]"
  by (simp)

lemma 
  "(8::vcardinal) + 0 = 8"
  "(8::vcardinal) + 1 = 9"
  "(8::vcardinal) + 4 = 12"
  "(8::vcardinal) + 11 = 19"
  by (auto)

lemma 
  "(8::vcardinal) * 0 = 0"
  "(8::vcardinal) * 1 = 8"
  "(8::vcardinal) * 4 = 32"
  "(8::vcardinal) * 11 = 88"
  by (auto)

lemma
  "power (8::vcardinal) 0 = 1"
  "power (8::vcardinal) 1 = 8"
  "power (8::vcardinal) 4 = 4096"
  by (auto)
    
(*

B: Generalising some of the card rules to vcard may be useful?

*)

lemma disjoint_insert:
  assumes
    a1: "x \<notin> A"
  shows
    "{x} \<inter> A = \<emptyset>"
  using a1
  by (auto)

lemma vcard_union_disjoint:
  assumes 
    a1: "disjoint A B"
  shows
    "vcard (A \<union> B) = vcard A + vcard B"
proof -
  have
    "vcard A + vcard B
    = vcard (A <+> B)"
    by (simp add: vcard_Plus)
  also from equipotent_Plus_union [OF a1] have "\<dots>
    = vcard (A \<union> B)"
    by (simp add: vcard_equipotent)
  finally show
    "?thesis"
     by (simp)
qed

lemma vcard_insert_disjoint:
  assumes
    a1: "x \<notin> A"
  shows
    "vcard (insert x A) = (vcard A) + 1"
  using vcard_union_disjoint [simplified disjoint_def, OF disjoint_insert [OF a1]]
  by (simp add: vcard_one_singleton [of "x", symmetric] add_ac)

lemma vcard_insert_if:
  "vcard (insert x A) = (if x \<in> A then vcard A else (vcard A) + 1)"
  by (auto simp add: vcard_insert_disjoint insert_absorb)

lemma
  "vcard {0-[\<nat>], 1, 2, 3, 4} = 5"
  by (simp add: vcard_insert_if vcard_zero_empty) 

lemma
  "vcard {0-[\<nat>], 1, 4, 2, 4, 3, 4, 4, 2} = 5"
  by (simp add: vcard_insert_if vcard_zero_empty) 

(* B: Interval counting also works, more or less out of the box. *)

lemma finite_vcard [simp]:
  assumes
    a1: "finite A"
  shows
    "vcard A = of_nat (card A)"
  apply (rule finite_induct [OF a1])
  apply (auto simp add: vcard_zero_empty vcard_insert_if add_ac)
  done

lemma 
  "vcard {..<(5::\<nat>)} = 5"
  "vcard {..(5::\<nat>)} = 6"
  "vcard {0..<(5::\<nat>)} = 5"
  "vcard {3..<(5::\<nat>)} = 2"
  "vcard {10..<(5::\<nat>)} = 0"
  "vcard {0..(5::\<nat>)} = 6"
  "vcard {3..(5::\<nat>)} = 3"
  "vcard {10..(5::\<nat>)} = 0"
  "vcard {0<..<(5::\<nat>)} = 4"
  "vcard {3<..<(5::\<nat>)} = 1"
  "vcard {10<..<(5::\<nat>)} = 0"
  "vcard {0<..(5::\<nat>)} = 5"
  "vcard {3<..(5::\<nat>)} = 2"
  "vcard {10<..(5::\<nat>)} = 0"
  by (auto)

lemma 
  "vcard {0..<(5::\<int>)} = 5"
  "vcard {3..<(5::\<int>)} = 2"
  "vcard {10..<(5::\<int>)} = 0"
  "vcard {0..(5::\<int>)} = 6"
  "vcard {3..(5::\<int>)} = 3"
  "vcard {10..(5::\<int>)} = 0"
  "vcard {0<..<(5::\<int>)} = 4"
  "vcard {3<..<(5::\<int>)} = 1"
  "vcard {10<..<(5::\<int>)} = 0"
  "vcard {0<..(5::\<int>)} = 5"
  "vcard {3<..(5::\<int>)} = 2"
  "vcard {10<..(5::\<int>)} = 0"
  by (auto)

(*
lemma vcard_zero_interval:
  "vcard {0..<0-[\<int>]} = 0-[vcardinal]"
  by (simp add: vcard_zero_empty_iff)

lemma vcardinal_numeral_1_eq_1 [simp]:
  "Numeral1 = 1-[vcardinal]"
  by (simp add: numeral_One)

lemma Inl_Plus_mem:
  "Inl a \<in> A <+> B \<Leftrightarrow> a \<in> A"
  by (auto)

lemma Inr_Plus_mem:
  "Inr b \<in> A <+> B \<Leftrightarrow> b \<in> B"
  by (auto)

(*J: may be ok... note that I was experimenting quickly, need some support thms to get it

But I don't really understand this "numeral" stuff yet!
*)

lemma number_of_vcardinal:
  "numeral n = vcard {0-[\<int>]..<(numeral n)}"
  apply (induct n rule: num_induct)
  apply simp
  apply (simp add: ivl_disj_int_one atLeastLessThan_def)
  apply (subst vcard_one_singleton [THEN sym])
term "\<^prid>{:4:}"

defer
  apply (simp only: numeral_inc vcard_plus_def vcard_equipotent not_less)
thm vcard_plus_def
  done


lemma add_vcardinal_number_of [simp]:
     "(number_of-[vcardinal] v) + number_of v' =  
         (if v < Int.Pls then number_of v'  
          else if v' < Int.Pls then number_of v  
          else number_of (v + v'))"
  apply (simp add: number_of_vcardinal_def Int.Pls_def vcard_plus_def vcard_equipotent not_less)
  apply (msafe_no_assms(inference))
  apply (rule equipotentI [of "(\<glambda> nm | nm \<in> {0..<v} <+> {0..<v'} \<bullet> \<case> nm \<of> Inl n \<longrightarrow> n | Inr m \<longrightarrow> v + m \<esac>)"])
  apply (mauto_full(fspace) msimp add: glambda_dom glambda_ran)
  apply (auto)
  apply (auto split: sum.splits simp add: Inl_Plus_mem Inr_Plus_mem not_less)
proof -
  fix 
    x :: "\<int>"
  assume
    b1: "0 \<le> v" and
    b2: "0 \<le> v'" and
    b3: "0 \<le> x" and
    b4: "x < v + v'"
  then show
    "(\<exists> nm \<bullet>
       (\<forall> a \<bullet> nm = Inl a \<Rightarrow> x = a \<and> 0 \<le> a \<and> a < v) \<and>
       (\<forall> b \<bullet> nm = Inr b \<Rightarrow> x = v + b \<and> 0 \<le> b \<and> b < v'))"
    apply (cases "x < v")
    apply (witness "Inl-[\<int>,\<int>] x")
    apply (auto simp add: not_less)
    apply (witness "Inr-[\<int>,\<int>] (x - v)")
    apply (auto)
    done
qed


lemma vcardinal_number_of_add_1 [simp]:
  "number_of v + (1-[vcardinal]) =
    (if v < Int.Pls then 1 else number_of (Int.succ v))"
  apply (simp add: vcardinal_numeral_1_eq_1 [symmetric] add_vcardinal_number_of del: vcardinal_numeral_1_eq_1)
  apply (auto simp add: not_less Int.Pls_def Int.Bit1_def Int.succ_def)
  done

lemma vcardinal_1_add_number_of [simp]:
  "(1-[vcardinal]) + number_of v  =
    (if v < Int.Pls then 1 else number_of (Int.succ v))"
  using vcardinal_number_of_add_1 [of v]
  by (simp add: add_commute)

lemma vcardinal_1_add_1 [simp]: 
   "1-[vcardinal] + 1 = 2"
  by (simp add: vcardinal_numeral_1_eq_1 [symmetric] del: vcardinal_numeral_1_eq_1)

lemma unique_quotient_remainder_int:
  fixes
    n :: "\<int>"
  assumes
    a1: "0 < n" and
    a2: "0 \<le> a" and
    a3: "0 \<le> b" "b < n" and
    a4: "0 \<le> a'" and
    a5: "0 \<le> b'" "b' < n"
  shows
    "a * n + b = a' * n + b' \<Leftrightarrow> a = a' \<and> b = b'"
proof (auto)
  assume
    b1: "a * n + b = a' * n + b'"
  from b1 assms have
    b2: "divmod_int_rel (a * n + b) n (a, b)"
    by (auto simp add: divmod_int_rel_def algebra_simps)
  from b1 assms have
    b3: "divmod_int_rel (a * n + b) n (a', b')"
    by (auto simp add: divmod_int_rel_def algebra_simps)
  from a1 b2 b3 show
    "a = a'" "b = b'"
    by (auto intro: unique_quotient unique_remainder)
qed

lemma unique_quotient_remainder_nat:
  fixes
    n :: "\<nat>"
  assumes
    a1: "b < n" and
    a2: "b' < n"
  shows
    "a * n + b = a' * n + b' \<Leftrightarrow> a = a' \<and> b = b'"
proof (auto)
  assume
    b1: "a * n + b = a' * n + b'"
  from b1 assms have
    b2: "divmod_nat_rel (a * n + b) n (a, b)"
    by (auto simp add: divmod_nat_rel_def algebra_simps)
  from b1 assms have
    b3: "divmod_nat_rel (a * n + b) n (a', b')"
    by (auto simp add: divmod_nat_rel_def algebra_simps)
  from divmod_nat_rel_unique [OF b2 b3] show
    "a = a'" "b = b'"
    by (auto)
qed
    
lemma mult_vcardinal_number_of [simp]:
     "(number_of-[vcardinal] v) * number_of v' =  
       (if v < Int.Pls then 0 else number_of (v * v'))"
  apply (multi_cases "v = 0" "v' = 0")
  apply (auto elim!: neqE simp add: number_of_vcardinal_def Int.Pls_def vcard_times_def vcard_equipotent vcard_zero_empty_iff not_less equipotent_empty zero_le_mult_iff)
proof -
  assume
    b1: "0 < v" and
    b2: "0 < v'"
  let 
    ?f = "(\<glambda> (n::\<int>, m::\<int>) | (n, m) \<in> ({0..<v} \<times> {0..<v'}) \<bullet> \<if> v \<le> v' \<then> n * v' + m \<else> m * v + n \<fi>)"
  show
    "\<^EP>{:{0..<v} \<times> {0..<v'}:}{:{0..<v * v'}:}"
  proof (rule equipotentI [of "?f"])
    show
      "?f \<in> ({0..<v} \<times> {0..<v'}) \<zbij> {0..<v * v'}"
    proof (rule dr_bijI)
      show
        "functional ?f"
        by (mauto_full(fspace) msimp add: split_def zero_le_mult_iff not_le)
      show
        "functional (?f\<^sup>\<sim>)"
        apply (mauto_full(fspace) msimp add: split_def zero_le_mult_iff unique_quotient_remainder_int not_less not_le)
        apply (auto)
        done
      show
        "\<zdom> ?f = ({0..<v} \<times> {0..<v'})"
        by (auto simp add: glambda_dom split_def)
      show
        "\<zran> ?f = {0..<v * v'}"
      proof (rule antisym)
        show
          "\<zran> ?f \<subseteq> {0..<v * v'}"
          apply (auto simp add: glambda_ran split_def not_less not_le set_eq_def mult_nonneg_nonneg add_nonneg_nonneg)
          apply (rule less_le_trans [of _ "(v' - 1) * v + v", OF add_le_less_mono]) 
          apply (simp add: mult_compare_simps)
          apply (simp)
          apply (simp add: mult_compare_simps algebra_simps)
          apply (rule less_le_trans [of _ "(v - 1) * v' + v'", OF add_le_less_mono]) 
          apply (simp add: mult_compare_simps)
          apply (simp)
          apply (simp add: mult_compare_simps algebra_simps)
          apply (rule less_le_trans [of _ "(v' - 1) * v + v", OF add_le_less_mono]) 
          apply (simp add: mult_compare_simps)
          apply (simp)
          apply (simp add: mult_compare_simps algebra_simps)
          done
        show
          "{0..<v * v'} \<subseteq> \<zran> ?f"
          apply (rule subsetI)
          apply (cases "v \<le> v'")
        proof -
          fix 
            "x" :: "\<int>"
          assume
            c1: "v \<le> v'" and
            c2: "x \<in> {0..<v * v'}"
          from c1 c2 b1 b2 have 
            "((x div v', x mod v') \<mapsto> x) \<in> ?f"
            apply (auto simp add: glambda_mem split_def pos_imp_zdiv_nonneg_iff)
            apply (rule le_less_trans [of _ "(-1 + v * v') div v'"])
            apply (rule zdiv_mono1)
            apply (auto simp add: div_eq_minus1)
            done
          then show 
            "x \<in> \<zran> ?f" 
            by (auto)
        next
          fix 
            "x" :: "\<int>"
          assume
            c1: "\<not>(v \<le> v')" and
            c2: "x \<in> {0..<v * v'}"
          from c1 c2 b1 b2 have 
            "((x mod v, x div v) \<mapsto> x) \<in> ?f"
            apply (auto simp add: glambda_mem split_def pos_imp_zdiv_nonneg_iff not_le)
            apply (rule le_less_trans [of _ "(-1 + v * v') div v"])
            apply (rule zdiv_mono1)
            apply (auto simp add: div_eq_minus1)
            done
          then show 
            "x \<in> \<zran> ?f" 
            by (auto)
        qed
      qed
    qed
  qed
qed

lemma eq_vcardinal_number_of [simp]:
  "number_of-[vcardinal] v = number_of-[vcardinal] v' 
  \<Leftrightarrow> 
    \<if>
      neg (number_of-[\<int>] v) 
    \<then>
      (number_of-[\<int>] v') \<le> 0
    \<elif>
      neg (number_of-[\<int>] v') 
    \<then>
      (number_of-[\<int>] v) = 0
    \<else>
      v = v'
    \<fi>"
  unfolding number_of_vcardinal_def number_of_is_id neg_def
  by (auto simp add: vcard_equipotent equipotent_int_interval_iff vcard_zero_empty_iff not_less split: if_splits)

lemma le_vcardinal_number_of [simp]:
  "number_of-[vcardinal] v \<le> number_of-[vcardinal] v' 
  \<Leftrightarrow> (\<if> v \<le> v' \<then> True \<else> v \<le> Int.Pls \<fi>)"
  unfolding number_of_vcardinal_def number_of_is_id neg_def Int.Pls_def
  by (auto simp add: not_less vcard_subequipotent subequipotent_int_interval_iff vcardinal_zero_bot vcardinal_zero_glb not_le vcard_zero_empty_iff) 

lemma less_vcardinal_number_of [simp]:
  "number_of-[vcardinal] v < number_of-[vcardinal] v' 
  \<Leftrightarrow> (\<if> v < v' \<then> Int.Pls < v' \<else> \<False> \<fi>)"
  apply (subst less_le)
  apply (subst le_vcardinal_number_of)
  apply (subst eq_vcardinal_number_of)
  unfolding number_of_vcardinal_def number_of_is_id neg_def Int.Pls_def
  apply (auto)
  done

lemma eq_vcardinal_number_of_0 [simp]:
  "number_of-[vcardinal] v = 0-[vcardinal] \<Leftrightarrow> v \<le> Int.Pls"
  unfolding number_of_vcardinal_def number_of_is_id neg_def Int.Pls_def
  by (auto simp add: vcard_zero_empty_iff)

lemma eq_0_vcardinal_number_of [simp]:
  "0-[vcardinal] = number_of-[vcardinal] v \<Leftrightarrow> v \<le> Int.Pls"
  unfolding number_of_vcardinal_def number_of_is_id neg_def Int.Pls_def
  by (auto simp add: vcard_zero_empty_iff)

lemma less_0_vcardinal_number_of [simp]:
  "0-[vcardinal] < number_of v \<Leftrightarrow> Int.Pls < v"
  apply (subst less_le)
  unfolding number_of_vcardinal_def number_of_is_id neg_def Int.Pls_def
  apply (auto simp add: vcardinal_zero_bot vcardinal_zero_glb vcard_zero_empty_iff)
  done

lemma neg_imp_vcardinal_number_of_eq_0: 
  "neg (number_of-[\<int>] v) \<turnstile> number_of-[vcardinal] v = 0-[vcardinal]"
  by (simp del: vcardinal_numeral_0_eq_0 add: vcardinal_numeral_0_eq_0 [symmetric])

lemma power_vcardinal_number_of_even:
  fixes 
    z :: "vcardinal"
  shows 
    "z ^ number_of (Int.Bit0 w) = (let w = z ^ (number_of w) in w * w)"
  unfolding Let_def Bit0_def nat_number_of_def number_of_is_id
  apply (cases "0 \<le> w")
  apply (simp only: nat_add_distrib power_add)
  apply (simp)
  done

lemma power_vcardinal_number_of_odd:
  fixes 
    z :: "vcardinal"
  shows 
    "z ^ number_of (Int.Bit1 w) 
    = (if (0::int) <= number_of w then (let w = z ^ (number_of w) in z * w * w) else 1)"
  unfolding Let_def Bit1_def nat_number_of_def number_of_is_id
  apply (cases "0 \<le> w")
  apply (simp only: mult_assoc nat_add_distrib power_add)
  apply (simp)
  apply (simp add: not_le mult_2 [symmetric] add_assoc)
  done

lemmas power_vcardinal_number_of_even_number_of [simp] 
   = power_vcardinal_number_of_even [of "number_of v", standard]

lemmas power_vcardinal_number_of_odd_number_of [simp] 
   = power_vcardinal_number_of_odd [of "number_of v", standard]
*)

end
