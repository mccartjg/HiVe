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
  Z_Numbers
  
imports
  Z_Fun
  Orders
  Z_Numbers_Chap

begin

section {* Number types *}

text {*

The number domain for Z is an abstract set @{text "\<arithmos>"}, pronounced
``arithmos''. The basic requirement for arithmos is that it have an injective,
homomorphic embedding of the integers. Isabelle declares homomorphic embeddings
of the naturals and integers, but does not require they be injective. We declare
strengthenings of these embeddings and lift natural number and integer lemmas to 
these embeddings.

*}

text {*

We require @{text "\<arithmos>"} to have certain algebraic properties, namely that it be a commutative
ring with order and that it admit a homomorphic embedding of the integers. Our approach is to
consider the axiomatic type class of all such types and to develop our support for Z numbers
in a type generic fashion. This allows us to delay as long as possible the decision as to the particular
type adopted to serve as @{text "\<arithmos>"}.

Note that the Isabelle @{text "linordered_idom"} class now incorporates @{text "comm_ring_1"}.

*}

class
  znumbers = linordered_idom

text {* 

Each @{text "znumbers"} type contains compatible algebraic embeddings of the naturals and the integers.

*}

definition
  zArith :: "('a::znumbers) set" 
where
  zArith_def: "zArith \<defs> \<univ>"

definition
  zNats :: "('a::znumbers) set"
where
  zNats_def: "zNats \<defs> range of_nat"

definition
  zNats1 :: "('a::znumbers) set"
where
  zNats1_def: "zNats1 \<defs> zNats \<setminus> {0}"

definition
  zInts :: "('a::znumbers) set"
where
  zInts_def: "zInts \<defs> range of_int"

(* Is this sensible? Should we just use these HOL versions? *)

no_notation (xsymbols)
  Nats  ("\<nat>")

no_notation (xsymbols)
  Ints  ("\<int>")

notation (xsymbols)
  zArith ("\<arithmos>") and
  zNats ("\<nat>") and
  zNats1 ("\<nat>\<subone>") and
  zInts ("\<int>")

lemma zNatsE:
  "\<lbrakk> n \<in> \<nat>; \<And> n' \<bullet> n = of_nat n' \<turnstile> R \<rbrakk> \<turnstile> R"
  by (auto simp add: zNats_def)

lemma zNats1E:
  "\<lbrakk> n \<in> \<nat>\<subone>; \<And> n' \<bullet> \<lbrakk> n = of_nat n'; 0 < n' \<rbrakk> \<turnstile> R \<rbrakk> \<turnstile> R"
  by (auto simp add: zNats1_def zNats_def)

lemma zNats_zNats1:
  "n \<in> \<nat>\<subone> \<turnstile> n \<in> \<nat>"
  by (simp add: zNats1_def)

lemma zIntsE:
  "\<lbrakk> n \<in> \<int>; \<And> n' \<bullet> n = of_int n' \<turnstile> R \<rbrakk> \<turnstile> R"
  by (auto simp add: zInts_def)

lemma zInts_zNats:
  "n \<in> \<nat> \<turnstile> n \<in> \<int>"
  apply (auto simp add: zNats_def zInts_def image_def)
  apply (rule exI)
  apply (rule of_int_of_nat_eq [THEN sym])
  done

text {*

These embeddings are isomorphisms.

*}


definition
  nat_of :: "('a::znumbers) \<rightarrow> \<nat>"
where
  nat_of_def: "nat_of \<defs> inv of_nat"

definition
  int_of :: "('a::znumbers) \<rightarrow> \<int>"
where
  int_of_def: "int_of \<defs> inv of_int"

lemma of_nat_inj: "inj (of_nat::\<nat> \<rightarrow> ('a::linordered_idom))"
  apply (rule inj_onI)
  apply (simp)
  done

interpretation zNats: type_definition "of_nat" "nat_of" "zNats"
  apply (rule type_definition.intro)
  apply (auto simp add: zNats_def nat_of_def inv_f_f [OF of_nat_inj])
  done

declare nat_induct [induct type: nat]

text {*

We prove a collection of rules for determining membership of @{text "zNats"} by structural recursion.

*}

lemma zNats_0 [simp]: "0 \<in> zNats"
  by (simp add: zNats_def)

lemma zNats_1 [simp]: "1 \<in> zNats"
  apply (simp add: zNats_def)
  apply (rule range_eqI)
  apply (rule of_nat_1 [symmetric])
  done

lemma zNats_add [simp]: "\<lbrakk> a \<in> zNats; b \<in> zNats \<rbrakk> \<turnstile> a + b \<in> zNats"
  apply (auto simp add: zNats_def)
  apply (rule range_eqI)
  apply (rule of_nat_add [symmetric])
  done

lemma zNats_diff [simp]: 
  "\<lbrakk> a \<in> zNats; b \<in> zNats; b \<le> a \<rbrakk> \<turnstile> a - b \<in> zNats"
  apply (auto simp add: zNats_def)
  apply (rule range_eqI)
  apply (rule of_nat_diff [symmetric])
  apply (assumption)
  done

lemma zNats_mult [simp]: "\<lbrakk> a \<in> zNats; b \<in> zNats \<rbrakk> \<turnstile> a * b \<in> zNats"
  apply (auto simp add: zNats_def)
  apply (rule range_eqI)
  apply (rule of_nat_mult [symmetric])
  done

lemma zNats_of_nat [simp]: "of_nat x \<in> zNats"
  by (auto simp add: zNats_def)

lemma zNats1_zNats_pos: "a \<in> zNats1 \<Leftrightarrow> a \<in> zNats \<and> 0 \<noteq> a"
  by (auto simp add: zNats1_def)

lemmas zNats_norm = 
  zNats_0 zNats_1 zNats_add zNats_diff zNats_mult zNats_of_nat
  zNats1_zNats_pos

text {*

We prove a collection of rules for calculating @{text "nat_of"} by structural recursion.

*}

lemma nat_of_0:
  "nat_of 0 = 0"
  apply (rule zNats.Rep_eqI)
  apply (subst zNats.Abs_inverse [OF zNats_0])
  apply (simp)
  done

lemma nat_of_1:
  "nat_of 1 = 1"
  apply (rule zNats.Rep_eqI)
  apply (subst zNats.Abs_inverse [OF zNats_1])
  apply (simp)
  done

lemma nat_of_add:
  assumes a1: "m \<in> zNats" and a2: "n \<in> zNats"
  shows "nat_of (m + n) = nat_of m + nat_of n"
  apply (rule zNats.Rep_eqI)
  apply (subst zNats.Abs_inverse [OF zNats_add [OF a1 a2]])
  using a1 a2
  apply (simp add: zNats.Abs_inverse)
  done

lemma nat_of_mult:
  assumes a1: "m \<in> zNats" and a2: "n \<in> zNats"
  shows "nat_of (m * n) = nat_of m * nat_of n"
  apply (rule zNats.Rep_eqI)
  apply (subst zNats.Abs_inverse [OF zNats_mult [OF a1 a2]])
  using a1 a2
  apply (simp add: of_nat_mult zNats.Abs_inverse)
  done

lemma nat_of_less_iff:
  assumes a1: "m \<in> zNats" and a2: "n \<in> zNats"
  shows "nat_of m < nat_of n \<Leftrightarrow> m < n"
  apply (subst (2) zNats.Abs_inverse [OF a1, THEN sym])
  apply (subst (2) zNats.Abs_inverse [OF a2, THEN sym])
  apply (simp)
  done

lemma nat_of_le_iff:
  assumes a1: "m \<in> zNats" and a2: "n \<in> zNats"
  shows "nat_of m \<le> nat_of n \<Leftrightarrow> m \<le> n"
  apply (subst (2) zNats.Abs_inverse [OF a1, THEN sym])
  apply (subst (2) zNats.Abs_inverse [OF a2, THEN sym])
  apply (simp)
  done  

lemma nat_of_diff:
  assumes a1: "m \<in> zNats" and a2: "n \<in> zNats" and a3: "n \<le> m"
  shows "nat_of (m - n) = nat_of m - nat_of n"
  apply (rule zNats.Rep_eqI)
  apply (subst zNats.Abs_inverse [OF zNats_diff [OF a1 a2 a3]])
  using a1 a2 a3
  apply (simp add: of_nat_diff zNats.Abs_inverse nat_of_le_iff)
  done

lemmas nat_of_norm = 
  zNats_norm
  nat_of_less_iff [THEN sym] nat_of_le_iff [THEN sym] zNats.Abs_inject [THEN sym]
  nat_of_0 nat_of_1 nat_of_mult nat_of_add nat_of_diff

text {*

We introduce an induction rule and other useful facts about @{text "zNats"}.

*}

lemma zNats_induct [induct set: zNats]:
  assumes 
    a1: "n \<in> zNats" and 
    a2: "P 0" and
    a3: "\<And> m \<bullet> \<lbrakk> m \<in> zNats; P m \<rbrakk> \<turnstile> P (m + 1)"
  shows "P n"
  using a1 
proof (auto simp add: zNats_def image_def)
  from a3 have a3': "\<And> m \<bullet> \<lbrakk> m \<in> zNats; P m \<rbrakk> \<turnstile> P (1 + m )"
    by (simp add: add_commute)
  fix m'
  show "P (of_nat m')"
    apply (induct m')
    apply (simp_all add: of_nat_0 of_nat_1 of_nat_add a2 a3')
    done
qed

lemma zNats1_pos:
  assumes 
    a1: "n \<in> zNats"
  shows 
    "n \<in> zNats1 \<Leftrightarrow> 0 < n"
  using a1 
  by (auto simp add: zNats1_def zNats_def)

lemma zNats_neq0_conv:
  assumes a1: "n \<in> zNats"
  shows "(n \<noteq> 0) \<Leftrightarrow> (0 < n)"
  apply (rule zNatsE [OF a1])
  apply (simp)
  done

lemma zNats_not_gr0:
  assumes a1: "n \<in> zNats"
  shows "\<not>(0 < n) \<Leftrightarrow> n = 0"
  apply (rule zNatsE [OF a1])
  apply (simp)
  done

lemma zNats_le_noteq_zero:
  assumes 
    a1: "m \<in> zNats" and 
    a2: "n \<in> zNats" and 
    a3: "m \<le> n" "m \<noteq> 0"
  shows "n \<noteq> 0"
  using a1 a2 a3
  by (auto simp add: zNats_def)


lemma zNats_Suc_le_eq:
  assumes 
    a1: "m \<in> zNats" and 
    a2: "n \<in> zNats"
  shows 
    "m + 1 \<le> n \<Leftrightarrow> m < n"
  by (simp add: nat_of_norm a1 a2 Suc_le_eq)

lemma zNats_mult_is_0: 
  assumes a1: "m \<in> zNats" and a2: "n \<in> zNats"
  shows "m * n = 0 \<Leftrightarrow> m = 0 \<or> n = 0"
  by (simp add: nat_of_norm a1 a2)

lemma zNats_add_is_0: 
  assumes a1: "m \<in> zNats" and a2: "n \<in> zNats"
  shows "m + n = 0 \<Leftrightarrow> m = 0 \<and> n = 0"
  by (simp add: nat_of_norm a1 a2 add_is_0)

lemma zNats_le_0_eq:
  assumes a1: "m \<in> zNats"
  shows "m \<le> 0 \<Leftrightarrow> m = 0"
  by (simp add: nat_of_norm a1 le_0_eq)

lemma zNats_le0: 
  assumes a1: "m \<in> zNats"
  shows "0 \<le> m"
  by (simp add: nat_of_norm a1 le0)

lemma zNats_add_mult_distrib: 
  assumes a1: "m \<in> zNats" "n \<in> zNats" "k \<in> zNats"
  shows "(m + n) * k = (m * k) + (n * k)"
  by (simp add: nat_of_norm a1 add_mult_distrib)

lemma zNats_add_mult_distrib2: 
  assumes a1: "m \<in> zNats" "n \<in> zNats" "k \<in> zNats"
  shows "k * (m + n) = (k * m) + (k * n)"
  by (simp add: nat_of_norm a1 add_mult_distrib2)

lemma zNats_mult_le_mono1: 
  assumes a1: "m \<in> zNats" "n \<in> zNats" "k \<in> zNats"
  shows "m \<le> n \<turnstile> m * k \<le> n * k"
  by (simp add: nat_of_norm a1 mult_le_mono1)

lemma zNats_mult_le_mono2: 
  assumes a1: "m \<in> zNats" "n \<in> zNats" "k \<in> zNats"
  shows "m \<le> n \<turnstile> k * m \<le> k * n"
  by (simp add: nat_of_norm a1 mult_le_mono2)

lemma zNats_diff_mult_distrib: 
  assumes a1: "m \<in> zNats" "n \<in> zNats" "k \<in> zNats" "n \<le> m"
  shows "(m - n) * k = (m * k) - (n * k)"
  using a1
  by (simp add: nat_of_norm zNats_mult_le_mono1 diff_mult_distrib)

lemma zNats_diff_mult_distrib2: 
  assumes a1: "m \<in> zNats" "n \<in> zNats" "k \<in> zNats" "n \<le> m"
  shows "k * (m - n) = (k * m) - (k * n)"
  using a1
  by (simp add: nat_of_norm zNats_mult_le_mono1 diff_mult_distrib2)

text {*

The set @{text "zInts"} is isomorphic to the integer type.

*}

lemma of_int_inj: "inj (of_int::\<int> \<rightarrow> ('a::znumbers))"
  apply (rule inj_onI)
  apply (simp)
  done

interpretation zInts: type_definition "of_int" "int_of" "zInts"
  apply (rule type_definition.intro)
  apply (auto simp add: zInts_def int_of_def inv_f_f [OF of_int_inj])
  done

declare int_induct [induct type: int]

text {*

We introduce rules for determining membership of @{text "zInts"} by structural recursion.

*}
 
lemma zInts_0 [simp]: "0 \<in> zInts"
  by (simp add: zInts_def)

lemma zInts_1 [simp]: "1 \<in> zInts"
  apply (simp add: zInts_def)
  apply (rule range_eqI)
  apply (rule of_int_1 [symmetric])
  done

lemma zInts_number_of [simp]:
  "(numeral n) \<in> zInts"
proof -
  have "(of_int (numeral n::int)::'a) \<in> zInts"
    apply (simp add: zInts_def)
    apply (rule range_eqI)
    apply (rule of_int_numeral [THEN sym])
  done
  moreover have "(of_int (numeral n::int)) = (numeral n::'a)"
    by (simp add: of_int_numeral)
  ultimately show ?thesis 
    by (simp)
qed

lemma zInts_neg_number_of [simp]:
  "(neg_numeral n) \<in> zInts"
proof -
  have "(of_int (neg_numeral n::int)::'a) \<in> zInts"
    apply (simp add: zInts_def)
    apply (rule range_eqI)
    apply (rule of_int_neg_numeral [THEN sym])
  done
  moreover have "(of_int (neg_numeral n::int)) = (neg_numeral n::'a)"
    by (simp add: of_int_neg_numeral)
  ultimately show ?thesis 
    by (simp)
qed

lemma zInts_minus [simp]: "a \<in> zInts \<turnstile> -a \<in> zInts"
  apply (auto simp add: zInts_def)
  apply (rule range_eqI)
  apply (rule of_int_minus [symmetric])
  done

lemma zInts_add [simp]: "\<lbrakk> a \<in> zInts; b \<in> zInts \<rbrakk> \<turnstile> a+b \<in> zInts"
  apply (auto simp add: zInts_def)
  apply (rule range_eqI)
  apply (rule of_int_add [symmetric])
  done

lemma zInts_diff [simp]: 
  "\<lbrakk> a \<in> zInts; b \<in> zInts \<rbrakk> \<turnstile> a - b \<in> zInts"
  apply (auto simp add: zInts_def)
  apply (rule range_eqI)
  apply (rule of_int_diff [symmetric])
  done

lemma zInts_mult [simp]: "\<lbrakk> a \<in> zInts; b \<in> zInts \<rbrakk> \<turnstile> a*b \<in> zInts"
  apply (auto simp add: zInts_def)
  apply (rule range_eqI)
  apply (rule of_int_mult [symmetric])
  done

lemma zInts_of_nat [simp]: "of_nat x \<in> zInts"
  apply (rule zInts_zNats)
  apply (rule zNats_of_nat)
  done

lemma zInts_of_int [simp]: "of_int x \<in> zInts"
  by (auto simp add: zInts_def)

lemma zNats_diff_zInts:
  "\<lbrakk> a \<in> zInts; b \<in> zInts; a \<le> b \<rbrakk> \<turnstile> b - a \<in> zNats"
  apply (auto simp add: zInts_def zNats_def)
  apply (rule range_eqI)
  apply (rule trans)
  apply (rule of_int_diff [symmetric])
  apply (rule of_nat_nat [symmetric])
  apply (subst (asm) le_add_iff2 [of "1::\<int>" _ "0" "0", simplified])
  apply (auto)
  done

lemma zNats_0_le_zInts:
  "\<lbrakk> b \<in> zInts; 0 \<le> b \<rbrakk> \<turnstile> b \<in> zNats"
  using zNats_diff_zInts [of 0 b]
  by (simp)

lemma zInts_zNats_nonneg: "a \<in> zNats \<Leftrightarrow> a \<in> zInts \<and> 0 \<le> a"
  apply (auto)
  apply (rule zInts_zNats)
  apply (auto intro: zNats_0_le_zInts zNats_le0)
  done

lemma zInts_zNats1_pos: "a \<in> zNats1 \<Leftrightarrow> a \<in> zInts \<and> 0 < a"
  by (auto simp add: zNats1_zNats_pos zInts_zNats_nonneg)

lemmas zInts_norm = 
  zInts_zNats_nonneg zInts_zNats1_pos
  zInts_0 zInts_1 zInts_number_of zInts_neg_number_of zInts_minus zInts_add zInts_diff zInts_mult zInts_of_int

text {*

We introduce rules for calculating @{text "int_of"} by structural recursion.

*}

lemma int_of_0:
  "int_of 0 = 0"
  apply (rule zInts.Rep_eqI)
  apply (subst zInts.Abs_inverse [OF zInts_0])
  apply (simp)
  done

lemma int_of_1:
  "int_of 1 = 1"
  apply (rule zInts.Rep_eqI)
  apply (subst zInts.Abs_inverse [OF zInts_1])
  apply (simp)
  done

lemma int_of_number_of:
  "int_of (numeral n::'a::znumbers) = numeral n"
proof -
  have "of_int (numeral n) = (numeral n::'a)"
    by (simp add: of_int_numeral)
  then have "int_of (numeral n::'a) = int_of (of_int (numeral n)::'a)"
    by (simp)
  then show ?thesis
    apply (subst (asm) zInts.Rep_inverse)
    apply simp
  done
qed

lemma int_of_neg_number_of:
  "int_of (neg_numeral n::'a::znumbers) = neg_numeral n"
proof -
  have "of_int (neg_numeral n) = (neg_numeral n::'a)"
    by (simp add: of_int_neg_numeral)
  then have "int_of (neg_numeral n::'a) = int_of (of_int (neg_numeral n)::'a)"
    by (simp)
  then show ?thesis
    apply (subst (asm) zInts.Rep_inverse)
    apply simp
  done
qed

lemma int_of_add:
  assumes a1: "m \<in> zInts" and a2: "n \<in> zInts"
  shows "int_of (m + n) = int_of m + int_of n"
  apply (rule zInts.Rep_eqI)
  apply (subst zInts.Abs_inverse [OF zInts_add [OF a1 a2]])
  using a1 a2
  apply (simp add: zInts.Abs_inverse)
  done

lemma int_of_mult:
  assumes a1: "m \<in> zInts" and a2: "n \<in> zInts"
  shows "int_of (m * n) = int_of m * int_of n"
  apply (rule zInts.Rep_eqI)
  apply (subst zInts.Abs_inverse [OF zInts_mult [OF a1 a2]])
  using a1 a2
  apply (simp add: zInts.Abs_inverse)
  done

lemma int_of_less_iff:
  assumes a1: "m \<in> zInts" and a2: "n \<in> zInts"
  shows "int_of m < int_of n \<Leftrightarrow> m < n"
  apply (subst (2) zInts.Abs_inverse [OF a1, THEN sym])
  apply (subst (2) zInts.Abs_inverse [OF a2, THEN sym])
  apply (simp)
  done

lemma int_of_le_iff:
  assumes a1: "m \<in> zInts" and a2: "n \<in> zInts"
  shows "int_of m \<le> int_of n \<Leftrightarrow> m \<le> n"
  apply (subst (2) zInts.Abs_inverse [OF a1, THEN sym])
  apply (subst (2) zInts.Abs_inverse [OF a2, THEN sym])
  apply (simp)
  done  

lemma int_of_diff:
  assumes a1: "m \<in> zInts" and a2: "n \<in> zInts"
  shows "int_of (m - n) = int_of m - int_of n"
  apply (rule zInts.Rep_eqI)
  apply (subst zInts.Abs_inverse [OF zInts_diff [OF a1 a2]])
  using a1 a2
  apply (simp add: zInts.Abs_inverse)
  done

lemma Z_zNats_zInts_conv:
  "zNats \<defs> { n | n \<in> zInts \<and> 0 \<le> n}"
  apply (rule eq_reflection)
  apply (auto simp add: zInts_zNats_nonneg)
  done

lemma zNats1_zInts_conv:
  "zNats1 = { n | n \<in> zInts \<and> 0 < n}"
  by (auto simp only: zInts_zNats1_pos)

lemmas int_of_norm = 
  zInts_norm Z_zNats_zInts_conv
  int_of_less_iff [THEN sym] int_of_le_iff [THEN sym] zInts.Abs_inject [THEN sym]
  int_of_0 int_of_1 int_of_number_of int_of_neg_number_of int_of_mult int_of_add int_of_diff

text {*

We introduce an induction rule and other useful facts about the integers.

*}

lemma zInts_induct [induct set: zInts]:
  assumes 
    a1: "n \<in> zInts" and 
    a2: "P 0" and
    a3: "\<And> m \<bullet> \<lbrakk> m \<in> zInts; P m \<rbrakk> \<turnstile> P (m + 1)" and
    a4: "\<And> m \<bullet> \<lbrakk> m \<in> zInts; P m \<rbrakk> \<turnstile> P (m - 1)"
  shows "P n"
  using a1 
proof (auto simp add: zInts_def image_def)
  fix m'
  show "P (of_int m')"
    apply (induct m' rule: Int.int_induct)
    apply (simp_all add: of_int_numeral)
  proof -
    from a2 show
      "P (of_int 0)"
      by (simp)
  next
    fix 
      k :: "\<int>"
    assume 
      b1: "P (of_int k)"
    with a3 show
      "P (of_int k + 1)"
      by (auto)
  next
    fix 
      k :: "\<int>"
    assume 
      b1: "P (of_int k)"
    with a4 show
      "P (of_int k - 1)"
      by (auto)
  qed
qed

lemma zNats_int_of_ge_0:
  "a \<in> zNats \<turnstile> 0 \<le> int_of a"
  apply (simp add: int_of_norm)
  apply (subst int_of_0 [THEN sym])
  apply (subst int_of_le_iff)
  apply (simp add: int_of_norm)+
  done

lemma zInts_not_less:
  assumes 
    a1: "m \<in> zInts" "n \<in> zInts"
  shows 
    "\<not>(m < n) \<Leftrightarrow> n \<le> m"
  using a1
  by (simp add: int_of_norm linorder_not_less)

lemma zInts_not_le:
  assumes  
    a1: "m \<in> zInts" "n \<in> zInts"
  shows 
    "\<not>(m \<le> n) \<Leftrightarrow> n < m"
  using a1
  by (simp add: int_of_norm linorder_not_le)

lemma zero_le_diff:
  assumes
    a1: "(n::'a::linordered_idom) \<le> m"
  shows 
    "0 \<le> m - n"
  apply (insert a1)
  apply (subst (asm) le_add_iff2 [of "1::'a" _ "0" "0", simplified])
  apply (auto)
  done

lemma zInts_less_add1_eq: 
  assumes 
    a1: "m \<in> zInts" "n \<in> zInts"
  shows 
    "m < n + 1 \<Leftrightarrow> m < n \<or> m = n"
  using a1
  apply (simp add: int_of_norm)
  apply arith
  done

lemma zInts_add1_le_eq: 
  assumes 
    a1: "m \<in> zInts" "n \<in> zInts"
  shows "m + 1 \<le> n \<Leftrightarrow> m < n"
  using a1
  apply (simp add: int_of_norm)
  apply arith
  done

lemma zInts_le_diff1_eq [simp]:  
  assumes 
    a1: "m \<in> zInts" "n \<in> zInts"
  shows 
    "m \<le> n - 1 \<Leftrightarrow>  m < n"
  using a1
  by (simp add: int_of_norm)

lemma zInts_le_add1_eq_le [simp]:  
  assumes 
    a1: "m \<in> zInts" "n \<in> zInts"
  shows "m < n + 1 \<Leftrightarrow> m \<le> n"
  using a1
  by (simp add: int_of_norm)

lemma zInts_one_le_iff_zero_less:   
  assumes
    a1: "m \<in> zInts"
  shows 
    "1 \<le> m \<Leftrightarrow> 0 < m"
  using a1
  apply (simp add: int_of_norm)
  apply arith
  done

lemma zInts_le_le_eq:
  assumes 
    a1: "m \<in> zInts" "n \<in> zInts" "m \<le> n" "n \<le> m"
  shows 
    "m = n"
  using a1
  by (simp add: int_of_norm)

text {*

The Z definition of the naturals is the smallest set containing @{text "0"} and all its successors.
The integers are the union of the naturals and their additive inverses.

*}


lemma Z_zNats_def:
  "zNats \<defs> (\<Inter> N | 0 \<in> N \<and> (\<forall> x | x \<in> N \<bullet> x + 1 \<in> N))"
  apply (rule eq_reflection)
  apply (rule subset_antisym [OF Inter_greatest [rule_format] Inter_lower])
  apply (simp_all)
  apply (simp add: zNats_def image_def subset_def)
  apply (msafe(inference))
proof -
  fix N::"'a set" and x::"\<nat>"
  assume 
    b1: "0 \<in> N" and 
    b2: "(\<forall> x | x \<in> N \<bullet> x + 1 \<in> N)"
  show "of_nat x \<in> N"
    apply (induct x type: nat)
    using b1 b2
    apply (simp_all)
    apply (subst add_commute)
    apply (auto)
    done
qed

lemma Z_zInts_def:
  "zInts \<defs> { z | z \<in> zArith \<and> (\<exists> x | x \<in> zNats \<bullet> z = x \<or> z = -x) }"
  apply (rule eq_reflection)
  apply (simp add: zArith_def zInts_def zNats_def image_def)
  apply (auto)
proof -
  fix z::"\<int>"
  show "(\<exists> x::\<nat> \<bullet> of_int z = of_nat x \<or> of_int z = -(of_nat x))"
  proof (cases "0 \<le> z")
    assume "0 \<le> z"
    then show ?thesis
      apply (witness "nat z")
      apply (simp add: of_nat_nat)
      done
  next
    assume c1: "\<not>(0 \<le> z)"
    then have c2: "0 \<le> -z"
      by (auto)
    then show ?thesis
      apply (witness "(nat (-z))")
      apply (simp add: of_nat_nat)
      done
  qed
next
  fix x::"\<nat>"
  show "(\<exists> z::\<int> \<bullet> ((of_nat x)::'a) = of_int z)" 
    apply (witness "(of_nat x)::\<int>")
    apply (simp add: of_int_of_nat_eq)
    done
  show "(\<exists> z::\<int> \<bullet> - ((of_nat x)::'a) = of_int z)"
    apply (witness "- (of_nat x)::\<int>")
    apply (induct x type: nat)
    apply (auto)
    done
qed

section {* Modulo and Integer Division *}

definition
  zmod :: "['a::znumbers , 'a] \<rightarrow> 'a" ("_ \<zmod> _" [70, 71] 70)
where
  zmod_def: "X \<zmod> Y \<defs> of_int ((int_of X) mod (int_of Y))"

definition
  zdiv :: "['a::znumbers, 'a] \<rightarrow> 'a" ("_ \<zdiv> _" [70, 71] 70)
where
  zdiv_def: "X \<zdiv> Y \<defs> of_int ((int_of X) div (int_of Y))"

lemma zInts_zmod:
  assumes 
    a1: "a \<in> zInts" "b \<in> zInts"
  shows 
    "a \<zmod> b \<in> zInts"
  using a1
  by (auto simp add: zInts_def zmod_def)

lemma int_of_zmod:
  assumes a1: "a \<in> zInts" and a2: "b \<in> zInts"
  shows "int_of (a \<zmod> b) = (int_of a) mod (int_of b)"
  apply (rule zInts.Rep_eqI)
  apply (subst zInts.Abs_inverse [OF zInts_zmod [OF a1 a2]])
  apply (simp add: zmod_def)
  done

lemma zInts_mod_ge_0:
  assumes a1: "a \<in> zInts" and a2: "b \<in> zInts" and a3: "0 < b" 
  shows "0 \<le> a \<zmod> b"
proof -
  from a2 a3 have "(0::int) < int_of b" by (simp add: int_of_norm)
  then show ?thesis by (auto simp add: zmod_def)
qed

lemma zInts_mod_le_b:
  assumes a1: "a \<in> zInts" and a2: "b \<in> zInts" and a3: "0 < b" 
  shows "a \<zmod> b < b"
proof -
  from a2 a3 have "(0::int) < int_of b" by (simp add: int_of_norm)
  then show ?thesis
  apply (subst int_of_less_iff [THEN sym])
  apply (rule zInts_zmod [OF a1 a2])
  apply (rule a2)
  apply (simp add: int_of_zmod [OF a1 a2])
  done
qed

  
lemma Z_mod_bounds:
  assumes 
    a1: "a \<in> zInts" "b \<in> zInts"
  shows 
    "0 < b \<Rightarrow> (0 \<le> (a \<zmod> b)) \<and> ((a \<zmod> b) < b)"
  using a1
  by (simp add: zInts_mod_le_b zInts_mod_ge_0)

lemma zInts_zdiv:
  assumes 
    a1: "a \<in> zInts" "b \<in> zInts"
  shows 
    "a \<zdiv> b \<in> zInts"
  using a1
  by (auto simp add: zInts_def zdiv_def)

lemma int_of_zdiv:
  assumes a1: "a \<in> zInts" and a2: "b \<in> zInts"
  shows "int_of (a \<zdiv> b) = int_of a div int_of b"
  apply (rule zInts.Rep_eqI)
  apply (subst zInts.Abs_inverse [OF zInts_zdiv [OF a1 a2]])
  apply (simp add: zdiv_def)
  done

lemma Z_div_mod_reconstr:
  assumes a1: "a \<in> zInts" and a2: "b \<in> zInts"
  shows "b \<noteq> 0 \<Rightarrow> a = (b*(a \<zdiv> b)) + (a \<zmod> b)"
proof (msafe(inference))
  assume b0: "b \<noteq> 0"
  have 
    "a 
    = of_int (int_of a)"
    by (rule zInts.Abs_inverse [OF a1, THEN sym])
  also have "\<dots> 
    = of_int(int_of b*(int_of a div int_of b) + (int_of a mod int_of b))"
    by (simp add: int_of_norm)
  also have "\<dots> 
    = of_int(int_of b*(int_of a div int_of b) + int_of(a \<zmod> b))"
    by (simp only: int_of_zmod [OF a1 a2])
  also have "\<dots> 
    = of_int(int_of b*int_of (a \<zdiv> b) + int_of(a \<zmod> b))"
    by (simp only: int_of_zdiv [OF a1 a2])
  also have "\<dots> 
    = of_int (int_of (b*(a \<zdiv> b)) + int_of (a \<zmod> b))"
    by (simp only: int_of_mult [OF a2 zInts_zdiv [OF a1 a2]])
  also have "\<dots> 
    = of_int (int_of (b*(a \<zdiv> b) + (a \<zmod> b)) )"
    apply (subst int_of_add)
    apply (rule zInts_mult [OF a2 zInts_zdiv [OF a1 a2]])
    apply (rule zInts_zmod [OF a1 a2])
    by simp
  also have "\<dots> 
    = b*(a \<zdiv> b) + (a \<zmod> b)"
    apply (subst zInts.Abs_inverse)
    apply (rule zInts_add [OF zInts_mult [OF a2 zInts_zdiv [OF a1 a2]] zInts_zmod [OF a1 a2]])
    by simp
  finally show 
    "a =  b*(a \<zdiv> b) + (a \<zmod> b)" 
    by this
qed

lemma Z_div_reduce:
  assumes a1: "a \<in> zInts" and a2: "b \<in> zInts" and a3: "c \<in> zInts"
  shows "b \<noteq> 0 \<and> c \<noteq> 0 \<Rightarrow> (c * a) \<zdiv> (c * b) = a \<zdiv> b"
proof (msafe(inference))
  assume b0: "b \<noteq> 0" and b1: "c \<noteq> 0"
  from b1 have b1': "int_of c \<noteq> 0" by (simp add: int_of_norm a3)
  then show "(c * a) \<zdiv> (c * b) = a \<zdiv> b"
    apply (simp add: zdiv_def)
    apply (simp add: int_of_mult [OF a3 a1])
    using a1 a2
    apply (simp add: int_of_mult [OF a3 a2])
    done
qed

section {* The Successor Graph *}

text {*

Z defines the successor function in a graph theoretic view.

*} 

definition
  zsucc :: "'a::znumbers \<leftrightarrow> 'a" ("\<zsucc>")
where
  Z_zsucc_def: "\<zsucc> \<defs> (\<glambda> n | n \<in> zNats \<bullet> n + 1)"

lemma Z_zsucc_beta:
  "\<forall> (n::'a::znumbers) | n \<in> zNats \<bullet> \<zsucc>\<cdot>n = n + 1"
  by (auto simp add: Z_zsucc_def glambda_beta)

lemma zsucc_bij:
  "\<zsucc> \<in> zNats \<zbij> zNats1"
  apply (msafe(fspace))
  apply (auto intro!: functionalI simp add: Z_zsucc_def glambda_mem glambda_ran)
proof -
  fix n::'a
  assume b1: "n \<in> zNats"
  then show "n + 1 \<in> zNats1"
    by (auto simp add: zNats1_def zNats_add_is_0)
next
  fix n::'a
  assume b1: "n \<in> zNats1"
  then show "(\<exists> m \<bullet> n = m + 1 \<and> m \<in> zNats)"
    apply (witness "n - 1")
    apply (auto simp add: nat_of_norm zNats1_def)
    done
qed

lemma zsucc_ran [simp]:
  assumes a1: "n \<in> zNats"
  shows "\<zsucc>\<cdot>n \<in> zNats"
  apply (insert zsucc_bij)
  apply (rule tfun_range [OF _ a1])
  apply (mauto(fspace) msimp add: zNats1_def)
  done

lemma zsucc_beta:
  assumes a1: "n \<in> zNats"
  shows "\<zsucc>\<cdot>n = n + 1"
  using a1
  by (auto simp add: Z_zsucc_def glambda_beta)

lemma nat_of_zsucc:
  assumes a1: "n \<in> zNats"
  shows "nat_of (\<zsucc>\<cdot>n) = Suc (nat_of n)"
  using a1
  by (simp add: nat_of_norm zsucc_beta)


section {* Iteration *}

text {*

HOL already defines a relational iteration operator, but, as per the transitive closure operator,
it does not take account of a carrier set as the Z operator does nor is it defined over the 
full integer space~\cite[p110]{Spivey:ZRef}.
Thus we are forced to redefine a Z compliant version of iteration.

*}

fun
  zpow :: "['a set, \<nat>, 'a \<leftrightarrow> 'a] \<rightarrow> ('a \<leftrightarrow> 'a)" ("zpow")
where
  "zpow X 0 R = \<zid> X"
| "zpow X (Suc n) R = R \<zfcomp> (zpow X n R)" 

definition
  ziter :: "['a set, 'b::znumbers, 'a \<leftrightarrow> 'a] \<rightarrow> ('a \<leftrightarrow> 'a)"
where
  ziter_def: 
    "ziter X n R \<defs> 
      \<if> 0 \<le> n 
      \<then> zpow X (nat (abs (int_of n))) R 
      \<else> zpow X (nat (abs (int_of n))) (R\<^sup>\<sim>) 
      \<fi>"

syntax (xsymbols)
  "_Z_Numbers\<ZZ>ziter" :: "[logic, logic, logic] \<rightarrow> logic" ("_\<^bzup>_\<^ezup>[_]" [1000] 999)

translations
  "_Z_Numbers\<ZZ>ziter R n X" \<rightleftharpoons> "CONST Z_Numbers.ziter X n R"

lemma zpow_in_relI:
  assumes a1: "R \<in> X \<zrel> X"
  shows "zpow X n R \<in> X \<zrel> X"
  apply (induct n)
  using a1
  apply (auto intro: id_in_relI fcomp_in_relI)
  done

lemma ziter_in_relI:
  assumes a1: "R \<in> X \<zrel> X" and a2: "n \<in> zInts"
  shows "R\<^bzup>n\<^ezup>[X] \<in> X \<zrel> X"
  apply (cases "0 \<le> n")
  using a1
  apply (auto simp add: ziter_def zpow_in_relI converse_in_relI)
  done

lemma zpow_zero:
  "zpow X 0 R = \<zid> X"
  by (simp)

lemma Z_ziter_zero_def:
  "R\<^bzup>0\<^ezup>[X] \<defs> \<zid> X"
  by (simp add: ziter_def int_of_0)
 
lemma Z_ziter_zero:
  "R\<^bzup>0\<^ezup>[X] = \<zid> X"
  by (simp add: Z_ziter_zero_def)

lemma zpow_one:
  assumes a1: "R \<in> X \<zrel> X"
  shows "zpow X (Suc 0) R = R"
  by (simp add: rel_rident [OF a1])

lemma Z_ziter_one:
  assumes a1: "R \<in> X \<zrel> X"
  shows "R\<^bzup>1\<^ezup>[X] = R"
  by (simp add: ziter_def rel_rident [OF a1] int_of_1)

lemma zpow_two:
  assumes a1: "R \<in> X \<zrel> X"
  shows "zpow X (Suc (Suc 0)) R = R \<zfcomp> R"
  by (simp add: rel_rident [OF a1])


lemma Z_ziter_two:
  assumes a1: "R \<in> X \<zrel> X"
  shows "R\<^bzup>2\<^ezup>[X] = R \<zfcomp> R"
proof -
  have b1: "nat (abs (int_of 2)) = Suc (Suc 0)"
    by (simp add: int_of_norm)
  show ?thesis by (simp add: ziter_def b1 rel_rident [OF a1])
qed


lemma Z_ziter_minus_one:
  assumes a1: "R \<in> X \<zrel> X"
  shows "R\<^bzup>-1\<^ezup>[X] = R\<^sup>\<sim>"
proof -
  have b1: "nat (abs (int_of -1)) = Suc 0"
    by (simp add: int_of_norm)
  show ?thesis by (simp add: b1 ziter_def rel_rident [OF a1 [THEN converse_in_relI]])
qed

lemma abs_nonneg_neg:
 assumes a1: "n \<in> zNats" 
 shows "abs (int_of (-n)) = int_of n"
proof -
  have b0: "-n = 0 - n" by auto
  from a1 have b1: "0 \<le> int_of n"
    by (auto simp add: Z_zNats_zInts_conv int_of_norm)
  from a1 b1 show ?thesis
    apply (subst b0)
    apply (subst int_of_diff)
    apply (simp_all add: int_of_norm)
    done
qed


lemma Z_ziter_minus_k_def:
  assumes a1: "R \<in> X \<zrel> X" and a2: "k \<in> zNats"
  shows "R\<^bzup>-k\<^ezup>[X] \<defs> (R\<^sup>\<sim>)\<^bzup>k\<^ezup>[X]"
proof (rule eq_reflection)
  from Z_zNats_zInts_conv a2 have b1: "k \<in> zInts" and b2: "0 \<le> k" by auto

  from b1 b2 have b2': "0 \<le> int_of k" by (simp add: int_of_norm)

  have "nat (abs (int_of (-k))) = nat (int_of k)"
    by (simp add: abs_nonneg_neg [OF a2])
    
  with b1 b2 show 
    "R\<^bzup>-k\<^ezup>[X] = (R\<^sup>\<sim>)\<^bzup>k\<^ezup>[X]"
    apply (simp add: ziter_def)
    apply (simp add: int_of_norm)
    done
qed

lemma Z_ziter_minus_k:
  assumes a1: "R \<in> X \<zrel> X" and a2: "k \<in> zNats"
  shows "R\<^bzup>-k\<^ezup>[X] = (R\<^sup>\<sim>)\<^bzup>k\<^ezup>[X]"
  using a1 a2
  by (simp add: Z_ziter_minus_k_def)

lemma zpow_fcomp_com:
  assumes a1: "R \<in> X \<zrel> X"
  shows "R \<zfcomp> (zpow X n R) = (zpow X n R) \<zfcomp> R"
proof (induct n)
  from a1 show "R \<zfcomp> (zpow X 0 R) = (zpow X 0 R) \<zfcomp> R"
    by (simp add: rel_rident rel_lident)
next
  fix n 
  assume a1: "R \<zfcomp> (zpow X n R) = (zpow X n R) \<zfcomp> R"
  have "R \<zfcomp> (zpow X (Suc n) R) = R \<zfcomp> (R \<zfcomp> (zpow X n R))"
    by (simp)
  also from a1 have "\<dots> = R \<zfcomp> ((zpow X n R) \<zfcomp> R)"
    by (simp)
  also have "\<dots> = (R \<zfcomp> (zpow X n R)) \<zfcomp> R"
    by (simp add: Z_rel_fcomp_assoc)
  also have "\<dots> = (zpow X (Suc n) R) \<zfcomp> R"
    by (simp)
  finally show "R \<zfcomp> (zpow X (Suc n) R) = (zpow X (Suc n) R) \<zfcomp> R"
    by (this)
qed

lemma ziter_fcomp_com:
  assumes a1: "R \<in> X \<zrel> X" and a2: "0 \<le> n"
  shows "R \<zfcomp> R\<^bzup>n\<^ezup>[X] = R\<^bzup>n\<^ezup>[X] \<zfcomp> R"
  using a1 a2
  by (simp add: ziter_def zpow_fcomp_com [OF a1])

lemma ziter_fcomp_com':
  assumes a1: "R \<in> X \<zrel> X" and a2: "n < 0"
  shows "R\<^sup>\<sim> \<zfcomp> R\<^bzup>n\<^ezup>[X] = R\<^bzup>n\<^ezup>[X] \<zfcomp> R\<^sup>\<sim>"
  using a1 a2
  by (simp add: ziter_def zpow_fcomp_com [OF a1 [THEN converse_in_relI]])

lemma zpow_iterl:
  assumes a1: "R \<in> X \<zrel> X"
  shows "zpow X (Suc n) R = R \<zfcomp> (zpow X n R)"
  by (simp)

lemma zpow_iterr:
  assumes a1: "R \<in> X \<zrel> X"
  shows "zpow X (Suc n) R = (zpow X n R) \<zfcomp> R"
  by (simp add: zpow_fcomp_com [OF a1])

lemma Z_ziter_iter_def:
  assumes a1: "R \<in> X \<zrel> X" and a2: "0 \<le> n" and a3: "n \<in> zInts"
  shows "R\<^bzup>n+1\<^ezup>[X] \<defs> R \<zfcomp> R\<^bzup>n\<^ezup>[X]"
proof (rule eq_reflection)
  from a2 have b0: "\<not> (n < 0)" by (simp add: int_of_norm a3)
  have b1: "nat (abs (int_of (n + 1))) = Suc (nat (abs (int_of n)))"
    apply (subst int_of_add [OF a3 zInts_1])
    using a1 a2 a3
    apply (simp add: int_of_norm)
    done
  show "R\<^bzup>n+1\<^ezup>[X] = R \<zfcomp> R\<^bzup>n\<^ezup>[X]"
    by (simp add: ziter_def b0 a2 b1 a3)
qed

lemma Z_ziter_iter:
  assumes 
    a1: "R \<in> X \<zrel> X" "0 \<le> n" "n \<in> zInts"
  shows 
    "R\<^bzup>n+1\<^ezup>[X] = R \<zfcomp> R\<^bzup>n\<^ezup>[X]"
  using a1
  by (simp add: Z_ziter_iter_def)

lemma Z_ziter_iter':
  assumes 
    a1: "R \<in> X \<zrel> X" "0 \<le> n" "n \<in> zInts"
  shows 
    "R\<^bzup>n+1\<^ezup>[X] = R\<^bzup>n\<^ezup>[X] \<zfcomp> R"
  using a1
  by (simp add: Z_ziter_iter ziter_fcomp_com)

lemma Z_ziter_def:
  "(\<forall> R | R \<in> X \<zrel> X \<bullet> 
    R\<^bzup>0\<^ezup>[X] = \<zid> X \<and>
    (\<forall> n | n \<in> zNats \<bullet> R\<^bzup>n+1\<^ezup>[X] = R \<zfcomp> R\<^bzup>n\<^ezup>[X]) \<and>
    (\<forall> k | k \<in> zNats \<bullet> R\<^bzup>-k\<^ezup>[X] = (R\<^sup>\<sim>)\<^bzup>k\<^ezup>[X]))"
  apply (intro allI)
  apply (msafe(inference))
  apply (simp add: Z_ziter_zero)
  apply (simp add: Z_zNats_zInts_conv)
  apply (simp add: Z_ziter_iter)
  apply (intro Z_ziter_minus_k)
  apply (simp add: zNats_def)
  apply (assumption)
  done

lemma zpow_converse:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
   "zpow X n (R\<^sup>\<sim>) = (zpow X n R)\<^sup>\<sim>"
  apply (induct n)
  apply (simp add: Z_inverse_id)
  using a1
  apply (simp add: converse_rel_fcomp zpow_fcomp_com)
  done

lemma Z_ziter_converse:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "(R\<^sup>\<sim>)\<^bzup>n\<^ezup>[X] = (R\<^bzup>n\<^ezup>[X])\<^sup>\<sim>"
  apply (cases "0 \<le> n")
  using a1
  apply (auto simp add: ziter_def zpow_converse)
  done

lemma zpow_add_dist:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "zpow X (n + m) R = zpow X n R \<zfcomp> zpow X m R"
  apply (induct n)
  using a1
  apply (simp add: zpow_zero rel_lident [OF zpow_in_relI])
  apply (simp add: Z_rel_fcomp_assoc)
  done

lemma Z_ziter_add_dist:
  assumes 
    a1: "R \<in> X \<zrel> X" and 
    a2: "0 \<le> n" and 
    a3: "0 \<le> m" and 
    a4: "n \<in> zInts" and 
    a5: "m \<in> zInts"
  shows 
    "R\<^bzup>n+m\<^ezup>[X] = R\<^bzup>n\<^ezup>[X] \<zfcomp> R\<^bzup>m\<^ezup>[X]"
proof -
  from a2 have a2': "0 \<le> int_of n" by (simp add: int_of_norm a4)
  from a3 have a3': "0 \<le> int_of m" by (simp add: int_of_norm a5)

  from a2' a3' have "0 \<le> int_of n + int_of m" by arith
  then have b0: "nat (abs (int_of (n + m))) = nat (abs (int_of n)) + nat (abs (int_of m))"
    apply (simp add: int_of_norm a4 a5)
    apply (simp add: nat_add_distrib a2' a3')
    done
  with a1 a2 a3 a4 a5 show ?thesis
    by (simp add: ziter_def zpow_add_dist b0)
qed

(*
lemma ziter_add_dist_counter:
  "{(0::'a::znumbers \<mapsto> 1::'a::znumbers), (1 \<mapsto> 1)}\<^ziter>{:((1::'a::znumbers) + (-1::'a::znumbers)):}{:{0,1}:} \<noteq> {(0 \<mapsto> 1), (1 \<mapsto> 1)}\<^ziter>{:1::'a::znumbers:}{:{0,1}:} \<zfcomp> {(0 \<mapsto> 1), (1 \<mapsto> 1)}\<^ziter>{:-1:}{:{0,1}:}"
proof -
  have "{(0 \<mapsto> 1), (1 \<mapsto> 1)} \<in> {0,1} \<zrel> {0,1}"
    by (auto simp add: rel_def)
  then show "?thesis"
  apply (auto simp add: ziter_zero ziter_one ziter_minus_one rel_eq_def)
  apply (witness "0::'a")
  apply (witness "1::'a")
  apply (simp add: Z_rel_id_mem Z_rel_fcomp_mem Z_inverse_mem)
  done
qed
*)

lemma zpow_mult_dist:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "zpow X (n * m) R = zpow X m (zpow X n R)"
  apply (induct m)
  using a1
  apply (simp add: zpow_zero rel_lident [OF zpow_in_relI])
  using a1
  apply (simp add: zpow_add_dist)
  done

lemma Z_ziter_mult_dist:
  assumes 
    a1: "R \<in> X \<zrel> X" and 
    a2: "0 \<le> n" and 
    a3: "0 \<le> m" and 
    a4: "n \<in> zInts" and 
    a5: "m \<in> zInts"
  shows 
    "R\<^bzup>n*m\<^ezup>[X] = (R\<^bzup>n\<^ezup>[X])\<^bzup>m\<^ezup>[X]"
proof -
  from a2 have a2': "0 \<le> int_of n" by (simp add: int_of_norm a4)
  from a3 have a3': "0 \<le> int_of m" by (simp add: int_of_norm a5)

  from a2' a3' have b1: "0 \<le> (int_of n) * (int_of m)" by (simp add: mult_nonneg_nonneg)

  have b0: "0 \<le> n * m"
    apply (subst int_of_le_iff [OF zInts_0, THEN sym])
    apply (rule zInts_mult [OF a4 a5])
    apply (simp add: int_of_0)
    apply (simp add: int_of_norm a4 a5)
    apply (simp add: b1)
    done

  have b2: "nat (int_of n * int_of m) = (nat (int_of n)) * (nat (int_of m))"
    apply (insert a2' a3')
    apply (simp add: nat_mult_distrib)
    done

  show ?thesis
    apply (simp add: ziter_def a2 a3 b0)
    apply (simp add: int_of_mult [OF a4 a5] a2' a3' b1)
    using a1
    apply (simp add: zpow_mult_dist b2)
    done
qed


lemma trancl_zpow:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "R\<^ztc>{:X:} = (\<Union> k | 1 \<le> k \<bullet> zpow X k R)"
  apply (rule rel_eqI)
  apply (simp)
  apply (msafe(inference))
proof -
  fix x y 
  assume b1: "(x \<mapsto> y) \<in> R\<^ztc>{:X:}"
  then show "(\<exists> k | Suc 0 \<le> k \<bullet> (x \<mapsto> y) \<in> zpow X k R)"
  proof (rule ztrancl_induct)
    fix y
    assume "(x \<mapsto> y) \<in> R"
    with zpow_one [OF a1] show "(\<exists> k | Suc 0 \<le> k \<bullet> (x \<mapsto> y) \<in> zpow X k R)"
      apply (witness "1::\<nat>")
      apply (simp)
      done
  next
    apply_end (msafe(inference))
    fix y z k
    assume "(x \<mapsto> y) \<in> R\<^ztc>{:X:}" and "(y \<mapsto> z) \<in> R" and "Suc 0 \<le> k" and "(x \<mapsto> y) \<in> zpow X k R"
    with zpow_iterr [OF a1, of k] show "(\<exists> k | Suc 0 \<le> k \<bullet> (x \<mapsto> z) \<in> zpow X k R)"
      apply (witness  "Suc k")
      apply (auto simp add: Z_rel_fcomp_mem)
      done
  qed
next
  fix x y k
  assume b1: "Suc 0 \<le> k" and b2: "(x \<mapsto> y) \<in> zpow X k R"
  have "\<forall> x y \<bullet> Suc 0 \<le> k \<and> (x \<mapsto> y) \<in> zpow X k R \<Rightarrow> (x \<mapsto> y) \<in> R\<^ztc>{:X:}"
  proof (induct k)
    show "\<forall> x y \<bullet> Suc 0 \<le> 0 \<and> (x \<mapsto> y) \<in> zpow X 0 R \<Rightarrow> (x \<mapsto> y) \<in> R\<^ztc>{:X:}"
      by (simp)
  next
    fix k
    assume c1: "\<forall> x y \<bullet> Suc 0 \<le> k \<and> (x \<mapsto> y) \<in> zpow X k R \<Rightarrow> (x \<mapsto> y) \<in> R\<^ztc>{:X:}"
    with rel_dom_mem [OF a1] rel_ran_mem [OF a1]
    show "\<forall> x y \<bullet> Suc 0 \<le> Suc k \<and> (x \<mapsto> y) \<in> zpow X (Suc k) R \<Rightarrow> (x \<mapsto> y) \<in> R\<^ztc>{:X:}"
      apply (simp add: Z_rel_fcomp_mem)
      apply (msafe(inference))
      apply (cases "k = 0")
      using a1
      apply (auto simp add: Z_rel_id_mem rel_def ztrancl_base)
      apply (rule subsetD [OF Z_trancl_fcomp_dist])
      apply (rule Z_rel_fcomp_memI)
      apply (rule ztrancl_base)
      apply (auto)
      done
  qed
  with b1 b2
  show "(x \<mapsto> y) \<in> R\<^ztc>{:X:}"
    by (auto)
qed


lemma Z_ziter_ztrancl:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "R\<^ztc>{:X:} = (\<Union> (k::'a::znumbers) | 1 \<le> k \<and> k \<in> zInts \<bullet> R\<^bzup>k\<^ezup>[X])"
  apply (simp add: trancl_zpow [OF a1])
  apply (rule rel_eqI)
  apply simp
  apply (msafe(inference))
proof -
  fix x y k
  assume b0: "Suc 0 \<le> k"  and b1: "(x, y) \<in> zpow X k R"
  have k: "nat_of (of_nat k) = k"
    by (simp add: nat_of_def inv_def)

  from b0 have b0': "(1::'a) \<le> of_nat k" 
    by (simp add: nat_of_norm k)

  have k': "nat (abs (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k))) = k"
  proof -
    have g_0: "0 < int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k)"
    proof -
      from b0 have d0: "0 < k" by auto
      then have d1: "(0::'a) < (of_nat::\<nat>\<rightarrow>'a::znumbers) k" by (simp add: nat_of_norm)
      with d0 show "0 < int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k)" 
        apply (subst int_of_0 [THEN sym])
        apply (subst int_of_less_iff)
        apply (simp_all add: int_of_norm nat_of_norm)
        done
    qed
    then have 
      c0: "abs (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k)) = int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k)"
      by simp
    have c1: "k = nat (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k))"
    proof -
      have d0: "int k = int (nat (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k)))"
        apply (rule nat_induct [where ?n = k])
        apply (simp add: int_nat_eq int_of_0)
      proof -
        fix n
        assume e0: "int n = int (nat (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) n)))"
        show "int (Suc n) = int (nat (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) (Suc n))))"
          apply (simp add: int_of_norm)
          apply (msafe(inference))
          apply (rule nat_induct [where ?n = "n"])
          apply (simp add:  int_of_0)
          apply (simp add: int_of_norm)
          proof-
            have "0 \<le> ((int_of :: 'a \<rightarrow> int) ((of_nat::\<nat>\<rightarrow>'a::znumbers) n))"
              by (rule zNats_int_of_ge_0, simp)
            then show "0 \<le> 1 + ((int_of :: 'a \<rightarrow> int) ((of_nat::\<nat>\<rightarrow>'a::znumbers) n))"
              by simp
          qed
       qed
      show ?thesis
        apply (rule int_int_eq [THEN sym, THEN iffD2])
        apply (simp only: d0)
        done
    qed
    show ?thesis
      apply (simp add: c0)
      apply (subst c1 [THEN sym])
      apply simp
      done
  qed
  show "(\<exists> k::'a | 1 \<le> k \<bullet> k \<in> zInts \<and> (x, y) \<in> R\<^bzup>k\<^ezup>[X])"
    apply (witness "of_int (int k)::'a")
    apply (simp add: ziter_def)
    apply (simp add: b0')
    apply (subst k')
    apply (simp add: b1)
    done
next
  fix x y 
  fix k::'a
  assume b0: "(1::'a) \<le> k" and b1: "(x, y) \<in> R\<^bzup>k\<^ezup>[X]" and b2: "k \<in> zInts"
  from b0 have b0': "(0::'a) \<le> k"
    by (simp add: int_of_norm)
  have b3: "Suc (0::\<nat>) \<le> nat (abs (int_of k))"
  proof -
    from b0 have "int_of (1::'a) \<le> int_of k" by (simp add: int_of_norm b2)
    then have c1: "1 \<le> int_of k" by (simp add: int_of_1)
    then have c2: "abs (int_of k) = int_of k" by simp
    from c1 show ?thesis    
      by (simp add: c2)
  qed
  from b1 have b4: "(x, y) \<in> zpow X (nat (abs (int_of k))) R"
    by (simp add: ziter_def b0')
  show "\<exists> k::\<nat> | Suc 0 \<le> k \<bullet> (x, y) \<in> zpow X k R"
    apply (witness "nat (abs (int_of k))")
    apply (simp add: b3 b4)
    done
qed

lemma zpow_ztrancl:
  assumes 
    a1: "R \<in> X \<zrel> X"
  shows 
    "R\<^zrtc>{:X:} = (\<Union> k::\<nat> \<bullet> zpow X k R)"
  apply (subst zrtrancl_decomp1 [OF a1])
  apply (rule rel_eqI)
  apply simp
  apply (msafe(inference))
proof -
  fix x y
  assume b0: "(x, y) \<in> R\<^ztc>{:X:}"
  then show "\<exists> k \<bullet> (x, y) \<in> zpow X k R"
  proof (rule ztrancl_induct)
    fix y
    assume "y \<in> X" "(x, y) \<in> R"
    with zpow_one [OF a1] show "\<exists> k \<bullet> (x, y) \<in> zpow X k R"
      apply (witness "1::\<nat>")
      by simp
  next
    apply_end (msafe(inference))
    fix y z 
    fix k::\<nat>
    assume "(x \<mapsto> y) \<in> R\<^ztc>{:X:}" and "z \<in> X" "(y \<mapsto> z) \<in> R" and "(x \<mapsto> y) \<in> zpow X k R"
    with zpow_iterr [OF a1, of k] show "\<exists> k::\<nat> \<bullet> (x \<mapsto> z) \<in> zpow X k R"
      apply (witness  "Suc k")
      by (auto simp add: Z_rel_fcomp_mem)
  qed
next
  fix x y
  assume b0: "(x, y) \<in> \<zid> X"
  then show "\<exists> k \<bullet> (x, y) \<in> zpow X k R"
    apply (witness "0::\<nat>")
    by (simp add: zpow_zero)
next
  fix x y k
  assume 
    b0: "(x, y) \<in> zpow X k R"

  have b1: "k = 0 \<Rightarrow> (x, y) \<in> \<zid> X"
  proof (msafe_no_assms(inference))
    assume c0: "k = 0"
    from b0 c0 show "(x, y) \<in> \<zid> X"
      by (simp add: zpow_zero)
  qed

  have b2: "k \<noteq> 0 \<Rightarrow> (x, y) \<in> R\<^ztc>{:X:}"
  proof (msafe(inference))
    assume c0: "k \<noteq> 0" then have c0': "Suc 0 \<le> k" by auto
    have "\<forall> x y \<bullet> Suc 0 \<le> k \<and> (x \<mapsto> y) \<in> zpow X k R \<Rightarrow> (x \<mapsto> y) \<in> R\<^ztc>{:X:}"
    proof (induct k)
      show "\<forall> x y \<bullet> Suc 0 \<le> 0 \<and> (x \<mapsto> y) \<in> zpow X 0 R \<Rightarrow> (x \<mapsto> y) \<in> R\<^ztc>{:X:}"
        by (simp)
    next
      fix k
      assume c1: "\<forall> x y \<bullet> Suc 0 \<le> k \<and> (x \<mapsto> y) \<in> zpow X k R \<Rightarrow> (x \<mapsto> y) \<in> R\<^ztc>{:X:}"
      then show "\<forall> x y \<bullet> Suc 0 \<le> Suc k \<and> (x \<mapsto> y) \<in> zpow X (Suc k) R \<Rightarrow> (x \<mapsto> y) \<in> R\<^ztc>{:X:}"
        apply (simp add: Z_rel_fcomp_mem)
        apply (msafe(inference))
        apply (cases "k = 0")
        apply (simp add: Z_rel_id_mem)
        apply (rule ztrancl_base)
        apply (auto simp add: rel_ran_mem [OF a1] rel_dom_mem [OF a1])
        apply (rule subsetD [OF Z_trancl_fcomp_dist])
        apply (rule Z_rel_fcomp_memI)
        apply (rule ztrancl_base)
        apply (assumption)
        apply (simp_all add: rel_ran_mem [OF a1] rel_dom_mem [OF a1])
        done
    qed
    with b0 c0' show "(x, y) \<in> R\<^ztc>{:X:}" by simp
  qed

  from b1 b2 show "(x, y) \<in> R\<^ztc>{:X:} \<or>  (x, y) \<in> \<zid> X"
    apply (cases "k = 0")
    apply simp_all
    done
qed

lemma Z_ziter_zrtrancl:
  assumes a1: "R \<in> X \<zrel> X"
  shows "R\<^zrtc>{:X:} = (\<Union> (k::'a::znumbers) | 0 \<le> k \<and> k \<in> zInts \<bullet> R\<^bzup>k\<^ezup>[X])"
  apply (subst zpow_ztrancl [OF a1])
  apply (rule rel_eqI)
  apply simp
  apply (msafe(inference))
proof -
  fix x y 
  fix k::\<nat>
  assume b0: "(x, y) \<in> zpow X k R"
  have b1: "nat (abs (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k))) = k"
  proof -
    have ge_0: "0 \<le> int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k)"
    proof -
      have d0: "0 \<le> k" by auto
      then have "(0::'a) \<le> (of_nat::\<nat>\<rightarrow>'a::znumbers) k" by (simp add: nat_of_norm)
      with d0 show "0 \<le> int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k)"
        apply (subst int_of_0 [THEN sym])
        apply (subst int_of_le_iff)
        apply (simp_all add: int_of_norm nat_of_norm)
        done
    qed
    then have c0: "abs (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k)) = int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k)" by simp
    have c1: "k = nat (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k))"
    proof  -
      have d0: "int k = int (nat (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) k)))"
        apply (rule nat_induct [where ?n = "k"]) 
        apply (simp add: int_nat_eq int_of_0)
        proof -
          fix n
          assume e0: "int n = int (nat (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) n)))"
          show "int (Suc n) = int (nat (int_of ((of_nat::\<nat>\<rightarrow>'a::znumbers) (Suc n))))"
            apply (simp add: int_of_norm)
            apply (msafe(inference))
            apply (rule nat_induct [where ?n = "n"])
            apply (simp add:  int_of_0)
            apply (simp add: int_of_norm)
            proof-
              have "0 \<le> ((int_of :: 'a \<rightarrow> int) ((of_nat::\<nat>\<rightarrow>'a::znumbers) n))"
                by (rule zNats_int_of_ge_0, simp)
              then show "0 \<le> 1 + ((int_of :: 'a \<rightarrow> int) ((of_nat::\<nat>\<rightarrow>'a::znumbers) n))"
                by simp
            qed
         qed
         show ?thesis
           apply (rule int_int_eq [THEN sym, THEN iffD2])
           apply (simp only: d0)
           done
       qed
       show ?thesis
         apply (simp add: c0)
         apply (subst c1 [THEN sym])
         apply simp
         done
    qed

  show "\<exists> (k::'a::znumbers) | 0 \<le> k \<bullet> k \<in> zInts \<and> (x, y) \<in> R\<^bzup>k\<^ezup>[X]"
    apply (witness "of_int (int k)::'a")
    apply (simp add: ziter_def)
    apply (subst b1)
    apply (simp add: b0)
    done
next
  fix x y 
  fix k::'a
  assume b0: "(0::'a) \<le> k" and b1: "(x, y) \<in> R\<^bzup>k\<^ezup>[X]" and b2: "k \<in> zInts"
  have b3: "(0::\<nat>) \<le> nat (abs (int_of k))"
  proof -
    from b0 have "int_of (0::'a) \<le> int_of k" by (simp add: int_of_norm b2)
    then have c1: "0 \<le> int_of k" by (simp add: int_of_0)
    then have c2: "abs (int_of k) = int_of k" by simp
    from c1 show ?thesis by (simp add: c2)
  qed
  from b1 have b4: "(x, y) \<in> zpow X (nat (abs (int_of k))) R"
    by (simp add: ziter_def b0)
  show "\<exists> k::\<nat> \<bullet> (x, y) \<in> zpow X k R"
    apply (witness "nat (abs (int_of k))")
    apply (simp add: b3 b4)
    done
qed

lemma zpow_fcomp_comm:
  assumes 
    a1: "R \<in> X \<zrel> X" and 
    a2: "S \<in> X \<zrel> X" and 
    a3: "R \<zfcomp> S = S \<zfcomp> R"
  shows "zpow X k R \<zfcomp> S = S \<zfcomp> zpow X k R"
proof (induct k)
  from a1 a2 show 
    "(zpow X 0 R) \<zfcomp> S = S \<zfcomp> (zpow X 0 R)"
    by (simp add: zpow_zero rel_lident rel_rident)
next
  fix k
  assume
    b0: "zpow X k R \<zfcomp> S = S \<zfcomp> zpow X k R"
 
  have "(zpow X (Suc k) R) \<zfcomp> S = (zpow X k R \<zfcomp> R) \<zfcomp> S"
    by (simp only: zpow_iterr [OF a1])
  also have "\<dots> = (zpow X k R) \<zfcomp> (R \<zfcomp> S)"
    by (simp add: Z_rel_fcomp_assoc)
  finally have b1: "(zpow X (Suc k) R) \<zfcomp> S = (zpow X k R) \<zfcomp> (R \<zfcomp> S)" by this

  have "S \<zfcomp> zpow X (Suc k) R = (S \<zfcomp> ((zpow X k R) \<zfcomp> R))"
    by (simp only: zpow_iterr [OF a1])
  also have "\<dots> = (S \<zfcomp> zpow X k R) \<zfcomp> R"
    by (simp add: Z_rel_fcomp_assoc)
  also have "\<dots> = (zpow X k R \<zfcomp> S) \<zfcomp> R"
    by (simp add: b0 [THEN sym])
  also have "\<dots> = zpow X k R \<zfcomp> (S \<zfcomp> R)"
    by (simp add: Z_rel_fcomp_assoc)
  also have "\<dots> = zpow X k R \<zfcomp> (R \<zfcomp> S)"
    by (simp add: a3)
  finally have b2: "S \<zfcomp> zpow X (Suc k) R = zpow X k R \<zfcomp> (R \<zfcomp> S)" by this

  from b1 b2 show "(zpow X (Suc k) R) \<zfcomp> S = S \<zfcomp> zpow X (Suc k) R" by simp
qed


lemma fcomp_zpower:
  assumes a1: "R \<in> X \<zrel> X" and a2: "S \<in> X \<zrel> X"
  shows "(R \<zfcomp> S = S \<zfcomp> R) \<Rightarrow> zpow X k (R \<zfcomp> S) = (zpow X k R) \<zfcomp> (zpow X k S)"
  apply (msafe(inference))
proof (induct k)
  show "(R \<zfcomp> S = S \<zfcomp> R) \<turnstile> zpow X 0 (R \<zfcomp> S) = (zpow X 0 R) \<zfcomp> (zpow X 0 S)"
    by (simp add: zpow_zero Z_rel_id_fcomp)
next
  apply_end (msafe(inference))
  fix k::\<nat> 
  assume a3: "R \<zfcomp> S = S \<zfcomp> R" and b0: "R \<zfcomp> S = S \<zfcomp> R \<turnstile> zpow X k (R \<zfcomp> S) = (zpow X k R) \<zfcomp> (zpow X k S)"
  from a3 b0 have b0': "zpow X k (R \<zfcomp> S) = (zpow X k R) \<zfcomp> (zpow X k S)" by auto

  have comm: "(zpow X (Suc k) S) \<zfcomp> R = R \<zfcomp> zpow X (Suc k) S"
    apply (subst zpow_fcomp_comm)
    apply (simp_all add: a2 a1 a3)
    done

  have "zpow X (Suc k) (R \<zfcomp> S) = (zpow X k (R \<zfcomp> S)) \<zfcomp> (R \<zfcomp> S)"
    by (simp add: zpow_iterr [THEN sym, OF fcomp_in_relI [where ?X = "X" and ?Z = "X", OF a1 a2]])
  also have "\<dots> = ((zpow X k R) \<zfcomp> (zpow X k S)) \<zfcomp> (R \<zfcomp> S)"
    by (simp add: b0')
  also have "\<dots> = ((zpow X k R) \<zfcomp> (zpow X k S)) \<zfcomp>  S \<zfcomp> R"
    by (simp add: a3)
  also have "\<dots> = (zpow X k R) \<zfcomp> ((zpow X k S) \<zfcomp> S) \<zfcomp> R"
    by (simp add: Z_rel_fcomp_assoc)
  also have "\<dots> = (zpow X k R) \<zfcomp> (zpow X (Suc k) S) \<zfcomp> R"
    by (simp add: zpow_iterr [THEN sym, OF a2])
  also have "\<dots> = (zpow X k R) \<zfcomp> (R \<zfcomp> zpow X (Suc k) S)"
    by (simp only: comm)
  also have "\<dots> = (zpow X k R \<zfcomp> R) \<zfcomp> zpow X (Suc k) S"   
    by (simp add: Z_rel_fcomp_assoc)
  also have "\<dots> = zpow X (Suc k) R \<zfcomp> zpow X (Suc k) S"
    by (simp only: zpow_iterr [OF a1])
  finally show "zpow X (Suc k) (R \<zfcomp> S) = zpow X (Suc k) R \<zfcomp> zpow X (Suc k) S"
    by this
qed

lemma fcomp_conv_zpower:
  assumes a1: "R \<in> X \<zrel> X" and a2: "S \<in> X \<zrel> X" and a3: "R \<zfcomp> S = S \<zfcomp> R"
  shows "zpow X k ((S \<zfcomp> R)\<^sup>\<sim>) = zpow X k (R\<^sup>\<sim>) \<zfcomp> zpow X k (S\<^sup>\<sim>)"
  apply (subst fcomp_zpower [rule_format, THEN sym])
  apply (rule converse_in_relI [OF a1])
  apply (rule converse_in_relI [OF a2])
  apply (rule converse_eq_eq [rule_format, OF a3])
  apply (simp add: converse_rel_fcomp)
  done

lemma Z_fcomp_ziter:
  assumes a1: "R \<in> X \<zrel> X" and a2: "S \<in> X \<zrel> X"
  shows "R \<zfcomp> S = S \<zfcomp> R \<Rightarrow> (R \<zfcomp> S)\<^bzup>k\<^ezup>[X] = R\<^bzup>k\<^ezup>[X] \<zfcomp> S\<^bzup>k\<^ezup>[X]"
  apply (msafe(inference))
  apply (simp add: ziter_def)
  apply (insert fcomp_zpower [rule_format, OF a1 a2])
  apply simp_all
  apply (msafe(inference))
  apply (simp add: fcomp_conv_zpower [OF a1 a2])
  done

section {* Set size operator *}

definition
  zcard :: "'a set \<rightarrow> ('b :: znumbers)"
where
  zcard_def: "zcard X \<defs> of_nat (card X)"

notation (xsymbols)
  zcard ("\<zcard>")

lemma zNats_zcard:
  "\<zcard>A \<in> zNats"
  by (simp add: zcard_def zNats_norm)

lemma zInts_zcard:
  "\<zcard>A \<in> zInts"
  by (rule zInts_zNats [OF zNats_zcard])

lemma nat_of_zcard:
  "nat_of (\<zcard>X) = card X"
  by (simp add: zcard_def zNats.Rep_inverse)

lemma int_of_zcard:
  "int_of (\<zcard>X) = int (card X)"
  apply (simp add: zInts.Abs_connect_on [OF zInts_zcard])
  apply (simp add: zcard_def zNats.Rep_inverse)
  done

lemma zcard_range [simp]:
  "\<zcard>X \<in> zNats"
  by (simp add: zcard_def zNats_def)

lemma zcard_nempty_conv:
  assumes 
    a1: "finite A"
  shows
    "0 < \<zcard>A \<Leftrightarrow> A \<noteq> \<emptyset>"
    "0 \<noteq> \<zcard>A \<Leftrightarrow> A \<noteq> \<emptyset>"
    "\<zcard>A \<noteq> 0 \<Leftrightarrow> A \<noteq> \<emptyset>"
  using a1
  by (auto simp add: zcard_def)

lemma zcard_empty [simp]: "\<zcard>\<emptyset> = 0"
  apply (insert card_empty)
  apply (simp add: zcard_def)
  done

lemma zcard_infinite [simp]: "~ finite A ==> \<zcard>A = 0"
  apply (insert card_infinite [of A])
  apply (simp add: zcard_def)
  done

lemma zcard_insert_disjoint [simp]:
  assumes a1: "finite A" "x \<notin> A" 
  shows "\<zcard>(insert x A) = (\<zcard>A) + 1"
  apply (insert card_insert_disjoint [OF a1])
  apply (simp add: zcard_def)
  done

lemma zcard_insert_if:
  assumes a1: "finite A"
  shows "\<zcard>(insert x A) = (if x:A then \<zcard>A else (\<zcard>A) + 1)"
  apply (insert card_insert_if [OF a1])
  apply (simp add: zcard_def)
  done

lemma zcard_image_le: 
  assumes a1: "finite A"
  shows "\<zcard>(f\<lparr>A\<rparr>) \<le> \<zcard>A"
  apply (insert card_image_le [OF a1, of f])
  apply (simp add: zcard_def)
  done

lemma zcard_image: 
  assumes a1: "inj_on f A"
  shows "\<zcard>(f\<lparr>A\<rparr>) = \<zcard>A"
  apply (insert card_image [OF a1])
  apply (simp add: zcard_def)
  done

lemma zcard_Image:
  assumes a1: "f \<in> A \<zbij> B"
  shows "\<zcard>B = \<zcard>A"
proof -
  let ?f = "fun_appl f"
  from a1 have b1: "B = (?f\<lparr>A\<rparr>)"
    apply (mauto(fspace) msimp add: image_def functional_beta)
    apply (auto simp add: image_def functional_beta)
    done
  have b2: "inj_on ?f A"
    apply (rule inj_onI)
    apply (simp add: bij_1to1 [OF a1])
    done
  show "\<zcard>B = \<zcard>A"
    apply (simp add: b1)
    apply (rule zcard_image [OF b2])
    done
qed

lemma fun_zcard_dom:
  assumes a1: "functional f"
  shows "\<zcard>f = \<zcard>(\<zdom> f)"
  by (simp add: zcard_def fun_card_dom [OF a1])

lemma card_eq_bij:
  assumes a1: "finite A" and a2: "finite B" and a3: "card A = card B"
  shows "(\<exists> f \<bullet> f \<in> A \<zbij> B)"
proof -
  from a1 have "(\<forall> B | finite B \<and> card A = card B \<bullet> (\<exists> f \<bullet> f \<in> A \<zbij> B))" (is "?P A")
  proof (induct A rule: finite_induct)
    show "?P {}"
      apply (auto)
      apply (witness "\<emptyset>-['a \<times> 'c]")   
      apply (mauto(fspace) msimp add: vacuous_inv mintro: empty_functional)
      done
  next
    fix A x
    assume b1: "finite A" and b2: "x \<notin> A" and b3: "?P A"
    show "?P (insert x A)"
    proof (msafe(inference))
      fix B::"'c set"
      assume c1: "finite B" and c2: "card (insert x A) = card B"
      from b1 c2 [symmetric] have "card B \<noteq> 0"
        by (auto)
      with c1 have "B \<noteq> \<emptyset>"
        by (auto)
      then obtain y where c3: "y \<in> B"
        by (auto)
      let ?B = "B - {y}"
      from c1 have c4: "finite ?B"
        by (auto)
      have c5: "y \<notin> ?B"
        by (auto)
      from c3 have c6: "(insert y ?B) = B"
        by (auto)
      with c2 have "card (insert x A) = card (insert y ?B)"
        by (simp)
      with card_insert_disjoint [OF b1 b2] card_insert_disjoint [OF c4 c5]
      have "Suc (card A) = Suc (card ?B)"
        by (simp)
      then have c7: "card A = card ?B"
        by (auto)
      with c4 b3 obtain f where c8: "f \<in> A \<zbij> ?B"
        by (blast)
      with b2 c3 c5 show "(\<exists> f \<bullet> f \<in> insert x A \<zbij> B)"
        apply (witness "insert (x \<mapsto> y) f")
        apply (elim dr_bijE)
        apply (intro dr_bijI)
        apply (simp add: insert_functionalI)
        apply (simp add: converse_insert insert_functionalI Z_inverse_dom)
        apply (simp add: insert_dom)
        apply (auto simp add: insert_ran)
        done
    qed
  qed
  with a1 a2 a3 show 
    ?thesis
    by (auto)
qed

lemma zcard_eq_bij:
  assumes 
    a1: "finite A" and 
    a2: "finite B" and 
    a3: "\<zcard>A = \<zcard>B"
  shows 
    "(\<exists> f \<bullet> f \<in> A \<zbij> B)"
  apply (rule card_eq_bij)
  using a1 a2 a3
  apply (auto simp add: zcard_def)
  done

lemma zcard_union_inter: 
  assumes 
    A1: "finite A" and 
    A2: "finite B"
  shows
    "((\<zcard>A)::'a::znumbers) + \<zcard>B = \<zcard>(A \<union> B) + \<zcard>(A \<inter> B)"
proof-
  have
    "nat_of (((\<zcard>A)::'a) + (\<zcard>B::'a))
    = nat_of ((\<zcard>A)::'a) + nat_of ((\<zcard>B)::'a)"
    by (rule zNats_zcard [THEN zNats_zcard [THEN nat_of_add]])
  also have "... 
    = card A + card B"
    by (simp add: nat_of_zcard)
  also have "... 
    = card (A \<union> B) + card (A \<inter> B)"
    by (rule card_Un_Int [OF A1 A2])
  also have "... 
    = nat_of ((\<zcard>(A \<union> B))::'a) + nat_of ((\<zcard>(A \<inter> B))::'a)"
    by (simp add: nat_of_zcard)
  also have "... 
    = nat_of (((\<zcard>(A \<union> B))::'a) + ((\<zcard>(A \<inter> B))::'a))"
    by (rule zNats_zcard [THEN zNats_zcard [THEN nat_of_add], THEN sym])
  finally have
    Ra1: 
      "nat_of (((\<zcard>A)::'a) + (\<zcard>B::'a)) 
      = nat_of (((\<zcard>(A \<union> B))::'a) + ((\<zcard>(A \<inter> B))::'a))"
    by simp
  then show 
    ?thesis
    apply (subst zNats.Abs_inject [THEN sym])
    apply simp_all
  done
qed
  

lemma zcard_union_disjoint: 
  assumes A1: "finite A" and A2: "finite B" and A3: "A \<inter> B = \<emptyset>"
  shows
  "\<zcard>(A \<union> B) = ((\<zcard>A)::'a::znumbers) + \<zcard>B"
  apply (subst zcard_union_inter [OF A1 A2])
  apply (simp add: A3)
done

lemma Z_zcard_union:
  assumes a1: "finite S" and a2: "finite T"
  shows 
    "((\<zcard>(S \<union> T))::'a::znumbers) 
    = (\<zcard>S) + (\<zcard>T) - (\<zcard>(S \<inter> T))"
proof -
  from a1 a2 have 
    "((\<zcard>S)::'a::znumbers) + \<zcard>T 
    = \<zcard>(S \<union> T) + \<zcard>(S \<inter> T)" 
    by (simp only:  zcard_union_inter)
  with a1 a2 show 
    ?thesis 
    by (simp add: nat_of_norm)
qed

section {* Numeric ranges *}

definition
  zint_range :: "['a::znumbers, 'a] \<rightarrow> 'a set"
where
  zint_range_def: "zint_range \<defs> (\<olambda> n m \<bullet> { k | k \<in> zInts \<and> \<lch>n \<chLe> k \<chLe> m\<rch> })"

notation (xsymbols)
  zint_range (infixl ".." 110)


lemma Z_zint_range_def:
  "a..b \<defs> {k | k \<in> zInts \<and> \<lch>a \<chLe> k \<chLe> b\<rch> }"
  by (auto simp add: zint_range_def)


lemma zint_range_mem [simp]:
  "k \<in> n..m \<Leftrightarrow> k \<in> zInts \<and> \<lch>n \<chLe> k \<chLe> m\<rch>"
  by (simp add: zint_range_def)

lemma zint_range_zNats:
  assumes 
    a1: "n \<in> zNats" "m \<in> zNats" "k \<in> n..m"
  shows 
    "k \<in> zNats"
  using a1
  by (auto simp add: Z_zNats_zInts_conv zint_range_def)

lemma nat_of_zint_range_mem:
  assumes 
    a1: "n \<in> zNats" "m \<in> zNats"
  shows 
    "k \<in> zNats \<and> nat_of k \<in> {nat_of n..nat_of m} \<Leftrightarrow> k \<in> n..m"
  using a1
  by (auto simp add: zint_range_def nat_of_le_iff Z_zNats_zInts_conv)

lemma zint_range_of_nat:
  assumes a1: "n \<in> zNats" "m \<in> zNats"
  shows "n..m = of_nat\<lparr>{nat_of n..nat_of m}\<rparr>"
proof (rule set_eqI)
  fix k::'a
  have "k \<in> n..m \<Leftrightarrow> k \<in> zNats \<and> nat_of k \<in> {nat_of n..nat_of m}"
    by (simp only: nat_of_zint_range_mem [OF a1])
  also have "\<dots> \<Leftrightarrow> k \<in> zNats \<and> (of_nat (nat_of k)::'a) \<in> of_nat\<lparr>{nat_of n..nat_of m}\<rparr>"
    by (auto simp add: image_def zNats.Abs_inverse zNats.Rep_inverse)
  also have "\<dots> \<Leftrightarrow> k \<in> zNats \<and> k \<in> of_nat\<lparr>{nat_of n..nat_of m}\<rparr>"
    apply (msafe(wind))
    apply (auto simp add:  zNats.Abs_inverse)
    done
  also have "\<dots> \<Leftrightarrow> k \<in> of_nat\<lparr>{nat_of n..nat_of m}\<rparr>"
    by (auto simp add: zNats_def)
  finally show "k \<in> n..m \<Leftrightarrow> k \<in> of_nat\<lparr>{nat_of n..nat_of m}\<rparr>"
    by (this)
qed

lemma zint_range_zInts:
  assumes 
    a1: "n \<in> \<int>" "m \<in> \<int>" "k \<in> n..m"
  shows 
    "k \<in> \<int>"
  using a1
  by (auto simp add: zint_range_def)

lemma int_of_zint_range_mem:
  assumes 
    a1: "n \<in> \<int>" "m \<in> \<int>"
  shows 
    "k \<in> \<int> \<and> int_of k \<in> {int_of n..int_of m} \<Leftrightarrow> k \<in> n..m"
  using a1
  by (auto simp add: zint_range_def int_of_le_iff)

lemma zint_range_of_int:
  assumes a1: "n \<in> \<int>" "m \<in> \<int>"
  shows "n..m = of_int\<lparr>{int_of n..int_of m}\<rparr>"
proof (rule set_eqI)
  fix k::'a
  have "k \<in> n..m \<Leftrightarrow> k \<in> zInts \<and> int_of k \<in> {int_of n..int_of m}"
    by (simp only: int_of_zint_range_mem [OF a1])
  also have "\<dots> \<Leftrightarrow> k \<in> zInts \<and> (of_int (int_of k)::'a) \<in> of_int\<lparr>{int_of n..int_of m}\<rparr>"
    by (auto simp add: image_def zInts.Abs_inverse)
  also have "\<dots> \<Leftrightarrow> k \<in> zInts \<and> k \<in> of_int\<lparr>{int_of n..int_of m}\<rparr>"
    apply (msafe(wind))
    apply (auto simp add: zInts.Abs_inverse)
    done
  also have "\<dots> \<Leftrightarrow> k \<in> of_int\<lparr>{int_of n..int_of m}\<rparr>"
    by (auto simp add: zInts_def)
  finally show "k \<in> n..m \<Leftrightarrow> k \<in> of_int\<lparr>{int_of n..int_of m}\<rparr>"
    by (this)
qed

lemma zint_range_empty:
  assumes 
    a1: "n \<in> \<int>" "m \<in> \<int>" "m < n"
  shows 
    "n..m = \<emptyset>"
  using a1
  by (auto simp add: zint_range_def)

lemma Z_zint_range_empty:
  assumes 
    a1: "n \<in> \<int>" "m \<in> \<int>"
  shows 
    "m < n \<Rightarrow> n..m = \<emptyset>"
  using a1
  by (simp add: zint_range_empty)

lemma zint_range_singleton:
  assumes 
    a1: "a \<in> \<int>"
  shows 
    "a..a = {a}"
  using a1
  by (auto simp add: zint_range_def)

lemma zint_range_mono:
  assumes 
    a1: 
      "n\<^sub>1 \<in> \<int>" "m\<^sub>1 \<in> \<int>" "n\<^sub>2 \<in> \<int>" "m\<^sub>2 \<in> \<int>" 
      "n\<^sub>2 \<le> n\<^sub>1" "m\<^sub>1 \<le> m\<^sub>2"
  shows 
    "n\<^sub>1..m\<^sub>1 \<subseteq> n\<^sub>2..m\<^sub>2"
  using a1
  by (auto simp add: zint_range_def)

lemma zint_range_eq:
  assumes
    a1: "n_d_1 \<in> \<int>" "m_d_1 \<in> \<int>" "n_d_2 \<in> \<int>" "m_d_2 \<in> \<int>" "n_d_2 = n_d_1" "m_d_1 = m_d_2"
  shows 
    "n_d_1..m_d_1 = n_d_2..m_d_2"
  using a1
  by (auto simp add: zint_range_def)

lemma zint_range_add1:
  assumes 
    a1: "n \<in> \<int>" "m \<in> \<int>" "n \<le> m + 1"
  shows 
    "n..(m+1) = insert (m + 1) (n..m)"
  using a1
  apply (auto simp add: zint_range_def)
  apply (simp add: order_neq_le_less)
  done

lemma zint_range_finite:
  assumes 
    a1: "n \<in> \<int>" and
    a2: "m \<in> \<int>"
  shows 
    "finite (n..m)"
  by (simp add: zint_range_of_int [OF a1 a2])

lemma bounded_subset_zNats:
  assumes a1: "S \<subseteq> \<nat>" and a2: "\<exists> x | x \<in> \<nat> \<bullet> (\<forall> n | n \<in> S \<bullet> n < x)"
  shows "finite S"
proof -
  from a2 obtain x where 
    b0: "x \<in> \<nat>" and 
    b1: "\<forall> n | n \<in> S \<bullet> n < x" 
    by auto

  from a2 have b2: "S \<subseteq> zint_range 0 x"
    apply (simp add: zint_range_def)
    using a1 a2 b0 b1
    apply (auto simp add: Z_zNats_zInts_conv)
    done

  from b0 a1 have "x \<in> zInts" by (auto simp add: Z_zNats_zInts_conv)
  then show ?thesis
    apply (intro finite_subset [OF b2])
    apply (rule zint_range_finite)
    apply (auto simp add: int_of_norm)
    done
qed


lemma zint_range_zcard:
  assumes 
    a1: "n \<in> zInts" "m \<in> zInts" "n \<le> m"
  shows 
    "\<zcard>(n..m) = (m - n) + 1"
proof -
  let ?f = "(\<olambda> x \<bullet> of_nat x + n)"
  have b1: "n..m = ?f\<lparr>{0..nat_of (m-n)}\<rparr>"
  proof (rule set_eqI)
    fix k
    from a1 show "k \<in> n..m \<Leftrightarrow> k \<in> ?f\<lparr>{0..nat_of (m-n)}\<rparr>"
      apply (simp add: zint_range_def image_def)
      apply (auto)
      apply (witness "nat_of (k - n)")
      apply (simp add: zNats.Abs_inverse nat_of_le_iff zNats_diff_zInts)
      apply (subst (asm) of_nat_le_iff [THEN sym])
      apply (subst (asm) zNats.Abs_inverse)
      apply (simp add: zNats_diff_zInts)
      apply (auto)
      done
  qed
  have b2: "\<zcard>(n..m) = \<zcard>({0..nat_of (m-n)})"
    apply (simp only: b1)
    apply (rule zcard_image)
    apply (rule inj_onI)
    apply (auto)
    done
  from card_atLeastAtMost [of "0" "nat_of (m-n)"]
  have b3: "zcard ({0..nat_of (m-n)}) = of_nat (Suc (nat_of (m-n)))"
    by (simp add: zcard_def)
  from a1 show 
    ?thesis
    by (auto simp add: b2 b3 zNats.Abs_inverse zNats_diff_zInts)
qed

lemma zint_range_zcard_from_0:
  assumes a1: "m \<in> zNats"
  shows "\<zcard>(0..m) = m + 1"
  using a1 zint_range_zcard [of 0 m]
  by (simp add: zInts_zNats_nonneg)

lemma zint_range_zcard_from_1:
  assumes a1: "m \<in> zNats"
  shows "\<zcard>(1..m) = m"
proof (cases "m = 0")
  assume
    b1: "m = 0"
  then have "1..m = \<emptyset>"
    by (auto)
  with a1 b1 show ?thesis
    by (simp add: zcard_empty)
next
  assume b1: "m \<noteq> 0"
  with a1 have "1 \<le> m"
    by (auto simp add: zInts_zNats_nonneg zInts_one_le_iff_zero_less)
  with zint_range_zcard [of 1 m] a1 b1 show 
    ?thesis
    by (simp add: zInts_zNats)
qed

lemma zint_range_op_image_add:
  assumes 
    a1: "n \<in> zInts" "m \<in> zInts" "k \<in> zInts"
  shows 
    "(\<olambda> x \<bullet> x + k)\<lparr>n..m\<rparr> = (n + k)..(m + k)"
proof (rule order_antisym)
  from a1 show 
    "(\<olambda> x \<bullet> x + k)\<lparr>n..m\<rparr> \<subseteq> (n + k)..(m + k)"
    by (auto simp add: image_def)
next 
  show "(n + k)..(m + k) \<subseteq> (\<olambda> x \<bullet> x + k)\<lparr>n..m\<rparr>"
  proof (auto)
    fix x assume 
       c1: "x \<in> zInts" and c2: "n + k \<le> x" and c3: "x \<le> m + k"
    with a1 show "x \<in> (\<olambda> x \<bullet> x + k)\<lparr>n..m\<rparr>"
      apply (auto simp add: image_def)
      apply (witness "x - k")
      apply (auto)
      done
  qed
qed

lemma zint_range_rel_image_add:
  assumes 
    a1: "n \<in> zInts" "m \<in> zInts" "k \<in> zInts"
  shows "(\<glambda> x \<bullet> x + k)\<zlImg>n..m\<zrImg> = (n + k)..(m + k)"
proof (rule order_antisym)
  from a1 show 
    "(\<glambda> x \<bullet> x + k)\<zlImg>zint_range n m\<zrImg> \<subseteq> zint_range (n + k) (m + k)"
    by (auto simp add: Image_def glambda_mem)
next 
  show 
    "zint_range (n + k) (m + k) \<subseteq> (\<glambda> x \<bullet> x + k)\<zlImg>zint_range n m\<zrImg>"
  proof (auto)
    fix x assume 
      c1: "x \<in> zInts" "n + k \<le> x" "x \<le> m + k"
    with a1 show "x \<in> (\<glambda> x \<bullet> x + k)\<zlImg>zint_range n m\<zrImg>"
      apply (auto simp add: Image_def glambda_mem)
      apply (witness "x - k")
      apply (auto)
      done
  qed
qed

lemma zint_range_rel_image_zsucc:
  assumes 
    a1: "n \<in> zNats" "m \<in> zNats"
  shows 
    "\<zsucc>\<zlImg>zint_range n m\<zrImg> = zint_range (n + 1) (m + 1)"
proof -
  from a1 have 
    "\<zsucc>\<zlImg>zint_range n m\<zrImg> = (\<glambda> x \<bullet> x + 1)\<zlImg>zint_range n m\<zrImg>"
    by (auto simp add: Z_zsucc_def Image_def glambda_mem zInts_zNats_nonneg)
  with a1 show 
    ?thesis
    by (simp add: zint_range_rel_image_add zInts_zNats_nonneg)
qed

text
{*
Finite Sets
*}


lemma Z_fin_pow_def:  
  "\<fset> X \<defs> 
    { S::'b set | S \<in> \<pset> X \<and> (\<exists> n::'a::znumbers | n \<in> zNats \<bullet> (\<exists> f \<bullet> f \<in> 1..n \<zbij> S)) }"
proof (rule eq_reflection)
  let "?g n" = "(\<glambda> k | k \<in> \<lclose>0\<dots>n\<ropen> \<bullet> (of_nat k) + (1::'a))"
  have b1 [rule_format]: "(\<forall> n \<bullet> ?g n \<in> \<lclose>0\<dots>n\<ropen> \<zbij> 1..(of_nat n))" 
  proof (msafe_no_assms(inference), mauto(fspace), simp_all)
    fix n
    show "\<zdom> (\<glambda> k | k < n \<bullet> (of_nat k) + (1::'a)) = \<lclose>0\<dots>n\<ropen>"
      by (simp add: glambda_dom interval_defs)
    show "\<zran> (\<glambda> k | k < n \<bullet> (of_nat k) + (1::'a)) = 1..(of_nat n)"
    proof (auto simp add: glambda_ran interval_defs nat_of_norm zNats.Rep_inverse)
      fix k::'a
      assume d1: "k \<in> zInts" and d2: "1 \<le> k" and d3: "k \<le> of_nat n"
      from d1 d2 have d4: "k \<in> zNats"
        by (auto simp add: Z_zNats_zInts_conv)
      from d4 d2 have d5: "0 < k"
        by (auto)
      with d2 d3 d4 show "(\<exists> a \<bullet> k = of_nat a + 1 \<and> a < n)"
        apply (witness "nat_of k - 1")
        apply (simp add: nat_of_norm zNats.Rep_inverse)
        done
    qed
  qed
  show 
    "\<fset> X 
    = { S::'b set | S \<in> \<pset> X \<and> (\<exists> n::'a::znumbers | n \<in> zNats \<bullet> (\<exists> f \<bullet> f \<in> 1..n \<zbij> S)) }"
  proof (auto simp add: fin_pow_def finite_card equipotent_def)
    fix S::"'b set" and n::\<nat> and f::"'b \<leftrightarrow> \<nat>"
    assume c1: "S \<subseteq> X" and c2: "f \<in> S \<zbij> \<lclose>0\<dots>n\<ropen>"
    show "(\<exists> n::'a | n \<in> zNats \<bullet> (\<exists> f \<bullet> f \<in> 1..n \<zbij> S))"
      apply (witness "(of_nat n)::'a")
      apply (simp)
      apply (witness "((?g n)\<^sup>\<sim>)\<zfcomp> (f\<^sup>\<sim>)")
      apply (rule fcomp_in_bijI)
      apply (rule bij_inv_bij [OF b1])
      apply (rule bij_inv_bij [OF c2])
      done
  next
    fix S::"'b set" and n::'a and f::"'a \<leftrightarrow> 'b"
    assume c1: "S \<subseteq> X" and c2: "f \<in> zint_range 1 n \<zbij> S" and c3: "n \<in> zNats"
    from bij_inv_bij [OF b1 [of "nat_of n"]]
    show "(\<exists> (n::\<nat>) f \<bullet> f \<in> S \<zbij> \<lclose>0\<dots>n\<ropen>)"
      apply (witness "nat_of n")
      apply (witness "(f\<^sup>\<sim>)\<zfcomp> ((?g (nat_of n))\<^sup>\<sim>)")
      apply (rule fcomp_in_bijI)
      apply (rule bij_inv_bij [OF c2])
      apply (simp add: zNats.Abs_inverse [OF c3])
      done
  qed
qed

lemma Z_zcard_def:  
  assumes a1: "S \<in> \<fset> (X::'b set)"
  shows "\<zcard>S \<defs> (\<mu> (n::'a::znumbers) | n \<in> zNats \<and> (\<exists> f \<bullet> f \<in> 1..n \<zbij> S))"
proof (rule eq_reflection)
  from a1
  obtain n::'a and f where b1: "n \<in> zNats" and b2: "f \<in> zint_range 1 n \<zbij> S"
    by (auto simp add: Z_fin_pow_def [where ?'a = 'a])
  from b2 have b3: "((zcard S)::'a) = \<zcard>((1::'a)..n)"
    by (rule zcard_Image)
  also from b1 have "zcard (zint_range (1::'a) n) = n"
    by (simp add: zint_range_zcard_from_1)
  finally have b5: "zcard S = n"
    by (simp)
  with b2 have b6: "f \<in> zint_range 1 ((zcard S)::'a) \<zbij> S"
    by (simp)
  show "zcard S = (\<mu> (n::'a::znumbers) | n \<in> zNats \<and> (\<exists> f \<bullet> f \<in> zint_range 1 n \<zbij> S))"
    apply (rule the_equality [symmetric])
    apply (simp add: zNats_zcard)
    apply (rule exI)
    apply (rule b6)
    apply (auto)
  proof -
    fix m::'a and f
    assume c1: "m \<in> zNats" and c2: "f \<in> zint_range 1 m \<zbij> S"
    have "((zcard S)::'a) = zcard (zint_range (1::'a) m)"
      by (rule zcard_Image [OF c2])
    then show "m = zcard S"
      by (simp add: zint_range_zcard_from_1 [OF c1])
  qed
qed

lemma Z_fin_pow_def':
  "\<fset> X 
  = {S | S \<in> \<pset> X \<and> 
         (\<exists> n::'a::znumbers \<bullet> n \<in> zNats \<and> (\<exists> f | f \<in> ((1::'a)..n) \<ztfun> S 
           \<bullet> \<zran> f = S))}"
  apply (rule set_eqI)
  apply (simp add: fin_pow_def)
  apply (msafe(wind))
proof -
  fix S
  assume b0: "S \<subseteq> X"
  show "finite S \<Leftrightarrow> (\<exists> n::'a::znumbers \<bullet> n \<in> zNats \<and> (\<exists> f | f \<in> (zint_range (1::'a) n) \<ztfun> S \<bullet> \<zran> f = S))"
    apply (mauto_no_assms(inference))
    apply (induct set: finite)
  proof -
    show "\<exists> n \<bullet> n \<in> zNats \<and>  (\<exists> f | f \<in> (zint_range (1::'a) n) \<ztfun> \<emptyset> \<bullet> \<zran> f = \<emptyset>)"
      apply (simp add: fun_space_defs)
      apply (witness "0::'a")
      apply (simp add: zint_range_empty [THEN sym, OF zInts_1 zInts_0])
      done
  next
    fix x
    fix F
    assume c0: "finite F" and
           c1: "x \<notin> F" and 
           c2: "(\<exists> n \<bullet> n \<in> zNats \<and> (\<exists> f \<bullet> f \<in> zint_range (1::'a) n \<ztfun> F \<and> \<zran> f = F))"
    from c2 obtain n f where 
         c3: "f \<in> zint_range (1::'a) n \<ztfun> F" and 
         c4: "\<zran> f = F" and 
         c5: "n \<in> zNats" by auto

    have c5': "n + (1::'a) \<in> zInts" and c5'': "0 \<le> n"
      apply (insert zInts_zNats_nonneg [of n] zInts_add zInts_1 c5)
      apply (simp_all add: int_of_norm)
      done
      
    from c3 have domf: "\<zdom> f = zint_range (1::'a) n" by (msafe(fspace))
    then have c6: "n + (1::'a) \<notin> \<zdom> f" by auto

    let ?A = "insert (n + 1, x) f"

    have funa: "functional ?A"
      apply (simp only: insert_functional [rule_format])
      apply (insert c3 c6, mauto(fspace))
      done

    have doma: "\<zdom> ?A = zint_range (1::'a) (n + 1)"
    proof -
      have d0: "\<And> x::'a \<bullet> x \<noteq> n + (1::'a) \<and> x \<in> zInts \<and> (1::'a) \<le> x \<and> x \<le> n + (1::'a) \<turnstile> x \<le> n"
      proof auto
        fix r::'a
        assume e0: "r \<noteq> n + (1::'a)" and 
               e1: "r \<in> zInts" and
               e2: "(1::'a) \<le> r" and
               e3: "r \<le> n + (1::'a)"

        with c5 have 
          e0': "(int_of r) \<noteq> int_of (n + 1)" 
          by (simp add: int_of_norm)
        from c5 have 
          "int_of (n + 1) = int_of n + 1"  
          by (simp add: int_of_norm)
        with e0' have 
          e0'': "int_of r \<noteq> (int_of n) + 1" 
          by auto
        from e2 e1 have e2': "1 \<le> int_of r" by (simp add: int_of_norm)
        from e3 e1 c5 have e3': "int_of r \<le> int_of n + 1" by (simp add: int_of_norm)
        from e0'' e2' e3' have e4: "int_of r < int_of n + (1::int)" by arith
        
        from e0'' e4 have "int_of r \<le> int_of n" by arith
        with e1 c5 show 
          "r \<le> n" 
          by (simp add: int_of_norm)
      qed
      show ?thesis
        apply (simp add: Z_rel_insert_dom)
        apply (simp only: domf)
        apply (auto simp add: zint_range_def c5' c5'' d0)
        done
    qed 

    have rana: "\<zran> ?A = insert x F"
      apply (simp add: Z_rel_insert_ran)
      apply (simp add: c4)
      done

    show "(\<exists> m \<bullet> m \<in> zNats \<and> (\<exists> g \<bullet> g \<in> zint_range (1::'a) m \<ztfun> insert x F \<and> \<zran> g = insert x F))"
      apply (witness "n + 1")
      apply (rule conjI)
      apply (rule zNats_add [OF c5 zNats_1])
      apply (witness "f \<union> {(n + (1::'a) \<mapsto> x)}")
      apply (simp only: Z_rel_union_ran)
      apply (auto simp add: c4)
      apply (mauto(fspace) msimp add: funa doma rana)
      done
  next
    fix n f
    assume c0: "n \<in> zNats" and c1: "f \<in> (zint_range (1::'a) n) \<ztfun> S" and c2: "\<zran> f = S"
    from zInts_zNats_nonneg c0 have c0': "n \<in> zInts" by (simp add: int_of_norm)
    have "finite f"
    proof -
      have d0: "finite (\<zdom> f)"
        proof -
          from c1 have "\<zdom> f = zint_range (1::'a) n" by (msafe(fspace))
          with zint_range_finite [OF zInts_1 c0'] show "finite (\<zdom> f)" by auto
        qed
      from c1 have d1: "functional f" by (msafe(fspace))
      from dom_finite_fun [OF d1 d0] show ?thesis by auto
    qed

    with c1 c2 show "finite S"
      by (mauto(fspace) mintro: empty_functional fun_finite_ran)
  qed
qed

lemma Z_fin_powD':
  assumes
    a1: "S \<in> \<fset> X"
  shows 
    "S \<in> \<pset> X \<and> 
    (\<exists> n::'a::znumbers \<bullet> n \<in> \<nat> \<and> (\<exists> f | f \<in> ((1::'a)..n) \<ztfun> S \<bullet> \<zran> f = S))"
proof -
  from a1 have 
    "S \<in> {S | S \<in> \<pset> X \<and> 
              (\<exists> n::'a::znumbers \<bullet> 
                n \<in> zNats \<and> 
                (\<exists> f | f \<in> (zint_range (1::'a) n) \<ztfun> S \<bullet> \<zran> f = S))}"
    by (simp only: Z_fin_pow_def' [THEN sym])
  then show ?thesis by auto
qed

lemma Z_fin_pow1_def:
  "\<fset>\<subone> X \<defs> (\<fset> X) \<setminus> {\<emptyset>}"
  by (simp add: fin_pow1_def)

lemma sub_functional [mintro!(fspace)]:
  "functional f \<turnstile> functional (f \<setminus> A)"
  by (auto simp add: functional_def single_val_def)

lemma sub_converse:
  "(f \<setminus> g)\<^sup>\<sim> = f\<^sup>\<sim> \<setminus> g\<^sup>\<sim>"
  by (auto simp add: converse_def)

lemma functional_sub_dom:
  assumes a1: "functional f" and a2: "A \<subseteq> f"
  shows "\<zdom> (f \<setminus> A) = \<zdom> f \<setminus> \<zdom> A"
proof (auto simp add: Domain_def)
  fix x y y'
  assume b1: "(x \<mapsto> y) \<in> f" and b2: "(x \<mapsto> y) \<notin> A" and b3: "(x \<mapsto> y') \<in> A"
  from a2 b3 have b4: "(x \<mapsto> y') \<in> f"
    by (auto)
  from functionalD [OF a1 b1 b4]
  have "y = y'"
    by (this)
  with b2 b3 show "\<False>"
    by (auto)
qed

lemma Z_finite_iff:
  assumes 
    a1: "S \<in> \<pset> X"
  shows 
    "(S \<in> \<fset> X) \<Leftrightarrow> (\<forall> f | f \<in> S \<zinj> S \<bullet> \<zran> f = S)"
  using a1
  apply (simp add: fin_pow_def)
  apply (rule iffI)
proof -
  assume "finite S"
  then show "(\<forall> f | f \<in> S \<zinj> S \<bullet> \<zran> f = S)"
    apply (induct S set: finite)
    apply (msafe(inference))
  proof -
    fix f
    assume "f \<in> \<emptyset> \<zinj> \<emptyset>"
    then show "\<zran> f = \<emptyset>"
      by (mauto(fspace))
  next
    fix f x S
    assume 
      c1: "finite S" and 
      c2: "x \<notin> S" and 
      c3: "(\<forall> f | f \<in> S \<zinj> S \<bullet> \<zran> f = S)" and
      c4: "f \<in> insert x S \<zinj> insert x S"
    have c5 [rule_format]: "(\<forall> f | f \<in> insert x S \<zinj> insert x S \<and> (x \<mapsto> x) \<in> f \<bullet> \<zran> f = insert x S)"
    proof (msafe(inference))
      fix f
      assume d1: "f \<in> insert x S \<zinj> insert x S" and d2: "(x \<mapsto> x) \<in> f"
      from d1 d2 have d3 [rule_format]: "(\<forall> a \<bullet> (a \<mapsto> x) \<in> f \<Rightarrow> a = x)"
        apply (msafe(inference))
        apply (rule functionalD [of "f\<^sup>\<sim>"])
        apply (mauto(fspace))
        done
      from d1 d2 have d4 [rule_format]: "(\<forall> b \<bullet> (x \<mapsto> b) \<in> f \<Rightarrow> b = x)"
        apply (msafe(inference))
        apply (rule functionalD [of "f"])
        apply (mauto(fspace))
        done
      have d5 [rule_format]: "(\<forall> a b \<bullet> (a \<mapsto> b) \<in> f \<and> a \<notin> S \<Rightarrow> b = x)"
      proof (msafe(inference))
        fix a b 
        assume e1: "(a \<mapsto> b) \<in> f" and e2: "a \<notin> S"
        with d1 have e3: "a = x"     
          by (mauto(fspace))
        from d1 d2 e1 show "b = x"
          apply (simp add: e3)
          apply (rule functionalD [of "f"])
          apply (mauto(fspace))
          done
      qed
      from d1 have d6 [rule_format]: "(\<forall> a b \<bullet> (a \<mapsto> b) \<in> f \<and> b \<notin> S \<Rightarrow> a = x)"
      proof (msafe(inference))
        fix a b 
        assume e1: "(a \<mapsto> b) \<in> f" and e2: "b \<notin> S"
        with d1 have e3: "b = x"     
          apply (mauto(fspace))
          done
        from d1 d2 e1 show "a = x"
          apply (simp add: e3)
          apply (rule functionalD [of "f\<^sup>\<sim>"])
          apply (mauto(fspace))
          done
      qed
      from c2 d1 have d7: "f - {(x \<mapsto> x)} \<in> S \<zinj> S"
        apply (mauto(fspace))
        apply (simp add: sub_converse)
        apply (mauto(fspace))
        apply (auto intro: d5 d6)
        done
      with c3 have d8: "\<zran> (f - {(x \<mapsto> x)}) = S"
        by (auto)
      with d2 show "\<zran> f = insert x S"
        by (auto)
    qed
    show "\<zran> f = insert x S"
      apply (cases "(x \<mapsto> x) \<in> f")
      apply (rule c5)
      apply (simp add: c4) 
    proof -
      assume d1: "(x \<mapsto> x) \<notin> f"
      with c4 obtain b where d2: "(x \<mapsto> b) \<in> f" and d2': "(b \<mapsto> x) \<in> f\<^sup>\<sim>" and d3: "b \<in> S"
        by (mauto(fspace))
      from d2 have d4: "x \<in> \<zran> f" 
      proof (rule contrapos_pp)
        assume e1: "x \<notin> \<zran> f"
        with c4 c2 have e2: "{x} \<zdsub> f \<in> S \<zinj> S"
          apply (mauto(fspace) msimp add: dsub_dom)
          apply (auto simp add: dsub_def eind_def) 
          done
        with c3 have e3: "\<zran> ({x} \<zdsub> f) = S"
          by (auto)
        with e2 d3 obtain a where e4: "a \<in> S" and e5: "(a \<mapsto> b) \<in> f"
          apply (mauto(fspace))
          apply (auto simp add: dsub_def eind_def)
          done
        from c2 e4 have "a \<noteq> x"
          by (auto)
        then have "(b \<mapsto> x) \<notin> f\<^sup>\<sim>"
          apply (rule contrapos_nn)
          apply (rule functionalD [OF dr_tinjD2 [OF c4]])
          apply (auto simp add: converse_def e5)
          done
        then show "(x \<mapsto> b) \<notin> f"
          by (simp add: converse_def)
      qed
      then obtain a where d5: "(a \<mapsto> x) \<in> f" and d5': "(x \<mapsto> a) \<in> f\<^sup>\<sim>"
        by (auto) 
      from c2 d3 have d6: "b \<noteq> x"
        by (auto)
      then have d7: "a \<noteq> x"
        apply (rule contrapos_nn)
        apply (rule functionalD [OF dr_tinjD1 [OF c4] _ d5])
        apply (simp add: d2)
        done
      with c4 d5 have d8: "a \<in> S"
        by (mauto(fspace))
      from d1 d2 d5 have d9: "\<zran> (({x} \<zdsub> f) \<oplus> {(a \<mapsto> b)}) = \<zran> f - {x}"
        apply (simp add: dsub_def rel_oride_def fin_pfun_simp Z_ran_def eind_def set_eq_def)
        apply (mauto(inference) mintro!: disjCI' notI)
      proof -
        fix z
        assume e1: "(z \<mapsto> x) \<in> f" and e2: "z \<noteq> a"
        from e2 show "\<False>"
          apply (rule notE)
          apply (rule functionalD [OF dr_tinjD2 [OF c4] _ d5'])
          using e1 e2 
          apply (simp)
          done
      next
        fix z y
        assume e1: "(z \<mapsto> y) \<in> f" and e2: "y \<noteq> b" and e3: "y \<noteq> x"
        from e2 have e4: "z \<noteq> x"
          apply (rule contrapos_nn)
          apply (rule functionalD [OF dr_tinjD1 [OF c4] e1])
          apply (simp add: d2)
          done
        from e3 have e5: "z \<noteq> a"
          apply (rule contrapos_nn)
          apply (rule functionalD [OF dr_tinjD1 [OF c4] e1])
          apply (simp add: d5)
          done
        from e1 e4 e5 show "(\<exists> z \<bullet> z \<noteq> a \<and> z \<noteq> x \<and> (z \<mapsto> y) \<in> f)"
          by (auto)
      qed
      have d10: "(({x} \<zdsub> f) \<oplus> {(a \<mapsto> b)}) \<in> S \<zinj> S"
      proof ((mauto(fspace)), simp add: fin_pfun_simp)
        from c4 show "functional ({a} \<zdsub> {x} \<zdsub> f)"
          by (mauto(fspace))
        show "functional {(a \<mapsto> b)}"
          by (mauto(fspace) mintro!: fin_pfunI)
        show "functional ((({x} \<zdsub> f) \<oplus> {(a \<mapsto> b)})\<^sup>\<sim>)"
          apply (rule functionalI)
          apply (simp add: converse_def dsub_def rel_oride_def fin_pfun_simp)
          apply (msafe_no_assms(inference))
        proof -
          fix y_d_1 y_d_2
          assume "y_d_1 = a" "y_d_2 = a"
          then show "y_d_1 = y_d_2"
            by (simp)
        next
          fix z y_d_1 y_d_2
          assume f1: "z = b" and f2: "(y_d_2 \<mapsto> z) \<in> f" and f3: "y_d_2 \<noteq> x"   
          from f3 show "y_d_1 = y_d_2"  
            apply (rule contrapos_np)
            apply (rule functionalD [OF dr_tinjD2 [OF c4] _ d2'])
            using f1 f2 f3
            apply (simp)
            done
        next
          fix z y_d_1 y_d_2
          assume f1: "z = b" and f2: "(y_d_1 \<mapsto> z) \<in> f" and f3: "y_d_1 \<noteq> x"   
          from f3 show "y_d_1 = y_d_2"  
            apply (rule contrapos_np)
            apply (rule functionalD [OF dr_tinjD2 [OF c4] _ d2'])
            using f1 f2 f3
            apply (simp)
            done
        next
          fix z y_d_1 y_d_2
          assume 
            f1: "(y_d_1 \<mapsto> z) \<in> f" "(y_d_2 \<mapsto> z) \<in> f"
          show "y_d_1 = y_d_2"
            apply (rule functionalD [OF dr_tinjD2 [OF c4]])
            using f1
            apply (auto)
            done
        qed
      next
        from c2 c4 d8 show 
          "\<zdom> (({x} \<zdsub> f) \<oplus> {(a \<mapsto> b)}) = S"
          apply (msafe(fspace))
          apply (auto simp add: dsub_def rel_oride_def fin_pfun_simp eind_def)+
          done
      next
        from d9 c4 show "\<zran> (({x} \<zdsub> f) \<oplus> {(a \<mapsto> b)}) \<subseteq> S"
          by (mauto(fspace))
      qed
      with c3 have d11: "\<zran> (({x} \<zdsub> f) \<oplus> {(a \<mapsto> b)}) = S"
        by (auto)
      with d9 have d12: "\<zran> f - {x} = S"
        by (auto)
      with d4 show " \<zran> f = insert x S"
        by (auto)
    qed
  qed
next
  assume "(\<forall> f | f \<in> S \<zinj> S \<bullet> \<zran> f = S)"
  then show "finite S"
    apply (rule contrapos_pp)
    apply (simp)
  proof -
    assume c1: "\<not>(finite S)"
    from infinite_countable_subset [OF c1]
    obtain ind::"\<nat> \<rightarrow> 'a" where c2: "inj ind" and c3: "range ind \<subseteq> S"
      by (auto)
    let ?f = "\<zid> (S - range ind) \<union> { n \<bullet> (ind n \<mapsto> ind (Suc n))}"
    show "(\<exists> f | f \<in> S \<zinj> S \<bullet> \<zran> f \<noteq> S)"
      apply (witness "?f")
      apply (msafe(inference))
    proof -
      show "?f \<in> S \<zinj> S"
        apply (msafe(fspace))
        apply (simp_all add: converse_union Z_inverse_id)
        apply (mauto(fspace))
      proof - 
        from inj_onD [OF c2] show "functional { n \<bullet> (ind n \<mapsto> ind (Suc n))}"
          by (auto intro!: functionalI simp add: eind_def)
      next
        from inj_onD [OF c2] show "functional ({ n \<bullet> (ind n \<mapsto> ind (Suc n)) }\<^sup>\<sim>)"
          by (auto intro!: functionalI simp add: eind_def)
      next
        show "\<zdom> ({ n \<bullet> (ind n \<mapsto> ind (Suc n))}) \<zdres> (\<zid> (S - range ind)) = \<zdom> (\<zid> (S - range ind)) \<zdres> ({ n \<bullet> (ind n \<mapsto> ind (Suc n))})"
          by (auto simp add: dres_def rel_id_def)
      next
        show "\<zdom> ({ n \<bullet> (ind n \<mapsto> ind (Suc n))}\<^sup>\<sim>) \<zdres> (\<zid> (S - range ind)) = \<zdom> (\<zid> (S - range ind)) \<zdres> ({ n \<bullet> (ind n \<mapsto> ind (Suc n))}\<^sup>\<sim>)"
          by (auto simp add: dres_def rel_id_def converse_def)
      next
        from c3 show "\<zdom> ?f = S"
          by (auto simp add: rel_id_def Domain_iff eind_def)
      next
        from c3 show "\<zran> ?f \<subseteq> S"
          by (auto simp add: rel_id_def Domain_iff eind_def)
      qed
    next
      from c3 have "ind 0 \<in> S"
        by (auto)
      moreover from inj_onD [OF c2] have "ind 0 \<notin> \<zran> ?f"
        by (auto simp add: rel_id_def eind_def)
      ultimately show "\<zran> ?f \<noteq> S"
        by (auto)
    qed
  qed
qed


lemma Z_empty_fin_pow:
  assumes 
    "SORT_CONSTRAINT('a::znumbers)"
  shows
    "\<emptyset> \<in> \<fset> X"
  apply (subst Z_fin_pow_def' [where ?'a = 'a])
  apply (simp add: fun_space_defs)
  apply (intro exI [where ?x = "0::'a::znumbers"])
  apply (simp add: zNats_0)
  apply (simp add: zint_range_empty [OF zInts_1 zInts_0])
  done


lemma fin_pow_insert:
  assumes 
    "SORT_CONSTRAINT('a::znumbers)"
  assumes 
    a1: "S \<in> \<fset> X" and a2: "x \<in> X"
  shows 
    "S \<union> {x} \<in> \<fset> X"
proof -
  from a1 have "S \<in> {S | S \<in> \<pset> X \<and> (\<exists> n \<bullet> n \<in> zNats \<and> (\<exists> f | f \<in> (zint_range (1::'a) n) \<ztfun> S \<bullet> \<zran> f = S))}"
    by (simp only: Z_fin_pow_def' [where ?'a = 'a, THEN sym])
  then have b0: "S \<in> \<pset> X" and b1: "(\<exists> n::'a::znumbers \<bullet> n \<in> zNats \<and> (\<exists> f | f \<in> (zint_range (1::'a) n) \<ztfun> S \<bullet> \<zran> f = S))" by auto
  from b1 obtain n f where b3: "(n::'a::znumbers) \<in> zNats" and b4: "f \<in> (zint_range 1 n) \<ztfun> S" and b5: "\<zran> f = S" by auto
   
  from b4 have domf: "\<zdom> f = zint_range 1 n" by (mauto(fspace))
  then have b6: "n + 1 \<notin> \<zdom> f" by auto
 
  have b3': "n + (1::'a) \<in> zInts" and b3'': "0 \<le> n"
    apply (insert zInts_zNats_nonneg [of n] zInts_add zInts_1 b3)
    apply (simp_all add: int_of_norm)
    done

  let ?A = "insert (n + 1, x) f"

  have funa: "functional ?A"
    apply (simp only: insert_functional [rule_format])
    apply (insert b4 b6, mauto(fspace))
    done

  have doma: "\<zdom> ?A = zint_range (1::'a) (n + 1)"
  proof -
    have d0: "\<And> x::'a \<bullet> x \<noteq> n + 1 \<and> x \<in> zInts \<and> 1 \<le> x \<and> x \<le> n + 1 \<turnstile> x \<le> n"
    proof auto
      fix r::"'a::znumbers"
      assume e0: "r \<noteq> n + (1::'a)" and 
             e1: "r \<in> zInts" and
             e2: "(1::'a) \<le> r" and
             e3: "r \<le> n + (1::'a)"

      from e0 e1 b3 have e0': "(int_of r) \<noteq> int_of (n + 1)" by (simp add: int_of_norm)
      from b3 have "int_of (n + 1) = int_of n + 1"  by (simp add: int_of_norm)
      with e0' e1 b3 have e0'': "int_of r \<noteq> (int_of n) + 1" by auto
      from e2 e1 have e2': "1 \<le> int_of r" by (simp add: int_of_norm)
      from e3 e1 b3 have e3': "int_of r \<le> int_of n + 1" by (simp add: int_of_norm)
      from e0'' e2' e3' have e4: "int_of r < int_of n + (1::int)" by arith
        
      from e0'' e4 have "int_of r \<le> int_of n" by arith
      with e1 b3 show 
        "r \<le> n" 
        by (simp add: int_of_norm)
    qed
    show ?thesis
      apply (simp add: Z_rel_insert_dom)
      apply (simp only: domf)
      apply (auto simp add: zint_range_def b3' b3'' d0)
      done
  qed 

  have rana: "\<zran> ?A = insert x S"
    apply (simp add: Z_rel_insert_ran)
    apply (simp add: b5)
    done


  show ?thesis
    apply (subst Z_fin_pow_def')
    apply (auto)
    apply (rule a2)
    apply (insert b0, auto)
    apply (witness "(n::'a::znumbers) + 1")
    apply (simp add: zInts_add zInts_1 b3)
    apply (witness "f \<union> {(n + (1::'a) \<mapsto> x)}") 
    apply (simp only: Z_rel_union_ran)
    apply (simp add: b5)
    apply (mauto(fspace) msimp add: rana mintro: funa doma rana)
    done
qed

lemma Z_fin_pow_insert:
  assumes 
    "SORT_CONSTRAINT('a::znumbers)"
  shows
    "\<forall> S x | S \<in> \<fset> X \<and> x \<in> X \<bullet> S \<union> {x} \<in> \<fset> X"
  apply (intro allI)
  apply (msafe(inference))
  apply (rule fin_pow_insert)
  apply simp_all
  done

lemma card_exists:
  assumes a1: "x \<in> A" and a2: "finite A"
  shows "0 < card A"
proof -
  from a1 have "A \<noteq> \<emptyset>" by auto
  with a2 show ?thesis by auto
qed  


lemma Z_fin_pow1_redef:
  "(\<fset>\<subone> X) = {S | (S \<in> \<fset> X) \<and> 0 < \<zcard>S}"
  apply (simp add: Z_fin_pow1_def fin_pow_def)
  apply (rule set_eqI)
  apply (auto simp add: zcard_def int_of_norm)
  apply (simp add: card_exists)
  done

text
{*
Finite functions
*}

lemma Z_finite_part_funs_def:
  "X \<zffun> Y \<defs> {f | f \<in> X \<zpfun> Y \<and> (\<zdom> f \<in> \<fset> X)}"
  apply (rule eq_reflection)
  apply (simp add: finite_part_funs_def fin_pow_def)
  apply (auto simp add: fun_space_defs)
  done

lemma Z_finite_part_fun_fpow:
  "X \<zffun> Y = (X \<zpfun> Y) \<inter> (\<fset> (X \<times> Y))"
  apply (simp add: finite_part_funs_def fin_pow_def)
  apply (auto simp add: fun_space_defs)
  apply (intro dom_finite_fun)
  apply (simp add: functional_def single_val_def)
  apply simp
  apply (intro fun_finite_dom)
  apply simp
  done

section {* Minimum and Maximum *}

definition
  zmin :: "'a::znumbers set \<leftrightarrow> 'a" ("\<zmin>")
where
  zmin_def: 
    "\<zmin> \<defs> 
       {(S::('a::znumbers) set) m::'a::znumbers 
       | S \<in> \<pset>\<subone> zInts \<and> m \<in> zInts \<and> m \<in> S \<and> (\<forall> n | n \<in> S \<bullet> m \<le> n) 
       \<bullet> S \<zmapsto> m}"


definition
  zmax :: "'a::znumbers set \<leftrightarrow> 'a" ("\<zmax>")
where
  zmax_def: 
    "\<zmax> \<defs> 
      {(S::('a::znumbers) set) m::'a::znumbers 
      | S \<in> \<pset>\<subone> zInts \<and> m \<in> zInts \<and> m \<in> S \<and> (\<forall> n | n \<in> S \<bullet> m \<ge> n) 
      \<bullet> S \<zmapsto> m}"

lemma in_zminD1:
  assumes a1: "(S \<mapsto> x) \<in> \<zmin>"
  shows "x \<in> S"
  using a1
  by (auto simp add: zmin_def)

lemma in_zminD2:
  assumes a1: "(S \<mapsto> x) \<in> \<zmin>"
  shows "is_glb \<univ> (op \<le>) S x"
  apply (rule order_class.is_glbI)
  using a1
  apply (auto simp add: zmin_def)
  done

lemma zmin_dom:
  "\<zdom> \<zmin> 
  = {(S::('a::znumbers) set) | S \<in> \<pset>\<subone> zInts \<and> (\<exists> m \<bullet> m \<in> S \<and> (\<forall> n | n \<in> S \<bullet> m \<le> n))}"
  by (auto simp add: Z_Pow1_def zmin_def eind_def)

lemma exists_finite_min:
  assumes a1: "(S::('a::znumbers) set) \<in> \<fset>\<subone> \<int>"
  shows "(\<exists> m | m \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> m \<le> n))"
proof -
  from a1 have 
    b0: "finite S" and 
    b1: "S \<in> \<pset>\<subone> zInts"
    by (simp_all add: fin_pow1_def fin_pow_def Z_Pow1_def)
  from b0 have "S \<in> \<pset>\<subone> zInts \<Rightarrow> (\<exists> m | m \<in> zInts \<bullet> m \<in> S \<and> (\<forall> n | n \<in> S \<bullet> m \<le> n))"
    apply (induct S set: finite)
    apply (auto simp add: Z_Pow1_def)
  proof -
    fix S x m 
    assume 
      c1: "x \<notin> S" and c2: "x \<in> zInts" and 
      c3: "S \<subseteq> zInts" and c4: "m \<in> zInts" and c5: "m \<in> S" and
      c6: "(\<forall> n | n \<in> S \<bullet> m \<le> n)"
    then show "(\<exists> m | m \<in> zInts \<bullet> (m = x \<or> m \<in> S) \<and> m \<le> x \<and> (\<forall> n | n \<in> S \<bullet> m \<le> n))"
      apply (cases "x < m")
      apply (witness "x")
      apply (auto)
      done
  qed
  with b1 show ?thesis
    by (auto)
qed

lemma exists_zmin_zNats:
  assumes 
    a1: "(S::('a::znumbers) set) \<in> \<pset>\<subone> \<nat>"
  shows 
    "(\<exists> m | m \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> m \<le> n))"
  using a1
proof (simp add: Z_Pow1_def)
  from a1 Z_Pow1_def [of zNats] have a1': "S \<subseteq> zNats" and a1'': "S \<noteq> \<emptyset>" by auto
  from a1'' have "\<exists> x \<bullet> x \<in> S" by auto then obtain x where b0: "x \<in> S" by auto

  let ?A = "{n | n \<in> S \<and> x \<le> n}"
  let ?B = "S \<setminus> ?A"
  have b1: "S = ?B \<union> ?A" by auto
  then have b2: "?B = {n | n \<in> S \<and> n < x}" by auto
  have b3: "finite ?B"
  proof (rule bounded_subset_zNats)
    from a1' b1 show "?B \<subseteq> zNats" by auto
    
    from b0 a1' show "\<exists> x | x \<in> zNats \<bullet> (\<forall> n | n \<in> ?B \<bullet> n < x)"
      apply (witness "x")
      apply auto
      done
  qed

  show ?thesis
  proof (cases "?B = \<emptyset>")
    assume c0: "?B = \<emptyset>"
    with b1 have "S = ?A" by auto
    then show "(\<exists> m \<bullet> m \<in> S \<and> (\<forall> n | n \<in> S \<bullet> m \<le> n))"
      apply (witness "x")
      apply (auto simp add: b0)
      done
  next
    assume c0: "?B \<noteq> \<emptyset>"
    then have "?B \<in> \<fset>\<subone> zInts"
      apply (simp add: Z_fin_pow1_def)
      apply (simp add: fin_pow_def)
      apply (simp add: b3)
      apply (insert a1' b1, auto simp add: Z_zNats_zInts_conv)
      done
    with exists_finite_min [of ?B] have "\<exists> m \<bullet> m \<in> ?B \<and> (\<forall> n | n \<in> ?B \<bullet> m \<le> n)" by auto
    then obtain m where c1: "m \<in> ?B" and c2: "\<forall> n | n \<in> ?B \<bullet> m \<le> n" by auto
    from c1 b1 have c1': "m \<in> S" by auto

    have c2: "\<forall> n | n \<in> S \<bullet> m \<le> n"
    proof (subst b1, rule allI, msafe(inference))
      fix n
      assume d0: "n \<in> ?B \<union> ?A"
      have d1: "n \<notin> ?A \<Rightarrow> m \<le> n"
        apply (msafe(inference))
        apply (insert d0 c2, auto)
        done

      from c1 b2 have "m \<le> x" by (auto)
      then have d2: "n \<in> ?A \<Rightarrow> m \<le> n" by auto

      from d1 d2 c2 show "m \<le> n" by auto
    qed

    from c1 c2 show "(\<exists> m \<bullet> m \<in> S \<and> (\<forall> n | n \<in> S \<bullet> m \<le> n))"
      apply (witness "m")
      apply simp
      done
  qed
qed

lemma exists_zmin_bounded_upper:
  assumes a1: "S \<in> \<pset>\<subone> \<nat>" and a2: "\<exists> m | m \<in> \<int> \<bullet> (\<forall> n | n \<in> S \<bullet> n \<le> m)"
  shows "\<exists> m | m \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> m \<le> n)"
proof -
  from a1 Z_Pow1_def [of zNats] have a1': "S \<subseteq> zNats" and a1'': "S \<noteq> \<emptyset>" by auto
  from a2 obtain m where b0: "m \<in> zInts" and b1: "\<forall> n | n \<in> S \<bullet> n \<le> m" by auto


  from a1' a1'' b1 have "S \<subseteq> zint_range 0 m"
    apply (auto simp add: zint_range_def)
    apply (auto simp add: Z_zNats_zInts_conv)
    done
  then have "finite S" 
    apply (rule finite_subset)
    apply (rule zint_range_finite [OF _ b0])
    apply (simp add: int_of_norm)
    done

  with a1' a1'' have b2: "S \<in> \<fset>\<subone> zInts"
    by (auto simp add: Z_zNats_zInts_conv Z_fin_pow1_def fin_pow_def)

  from exists_finite_min [OF b2] show "(\<exists> m | m \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> m \<le> n))" by simp
qed

lemma exists_zmin_bounded_lower:
  assumes a1: "S \<in> \<pset>\<subone> \<int>" and a2: "\<exists> m | m \<in> \<int> \<bullet> (\<forall> n | n \<in> S \<bullet> m \<le> n)"
  shows "\<exists> m | m \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> m \<le> n)"
proof -
  from a1 Z_Pow1_def [of zInts] have a1': "S \<subseteq> zInts" and a1'': "S \<noteq> \<emptyset>" by auto
  from a2 obtain m where b0: "m \<in> zInts" and b1: "\<forall> n | n \<in> S \<bullet> m \<le> n" by auto

  from a1'' have "\<exists> x \<bullet> x \<in> S" by auto then obtain x where b2: "x \<in> S" by auto
  with a1' have b2': "x \<in> zInts" by auto

  let ?A = "{n | n \<in> S \<and> n \<le> x}"
  let ?B = "{n | n \<in> S \<and> x < n}"
  have b3: "S = ?A \<union> ?B" by auto

  from a1' b1 have "?A \<subseteq> zint_range m x"
    by (auto simp add: zint_range_def)
  then have "finite ?A"
    apply (rule finite_subset)
    apply (rule zint_range_finite [OF b0 b2'])
    done
  with a1' have "?A \<in> \<fset>\<subone> zInts" 
    apply (auto simp add: Z_fin_pow1_def fin_pow_def)
    apply (witness "x")
    apply (auto simp add: b2)
    done
  with exists_finite_min [of ?A] have "\<exists> r | r \<in> ?A \<bullet> (\<forall> n | n \<in> ?A \<bullet> r \<le> n)" by auto
  then obtain r where b4: "r \<in> ?A" and b5: "\<forall> n | n \<in> ?A \<bullet> r \<le> n" by auto
  with b3 have b4': "r \<in> S" by auto

  from b4 b5 [rule_format] have "r \<le> x" by auto
  then have "\<forall> n | n \<in> ?B \<bullet> r \<le> n" by (simp add: ge_def)
  with b3 b5 have b5: "\<forall> n | n \<in> S \<bullet> r \<le> n" by auto


  from b4' b5 show "\<exists> m | m \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> m \<le> n)"
    apply (witness "r")
    apply auto
    done
qed
   
  

  
lemma Z_fin_pow1_dom_min:
  "\<fset>\<subone> \<int> \<subseteq> \<zdom> \<zmin>"
  apply (auto intro: exists_finite_min simp add: zmin_dom)
  apply (simp add: Z_Pow1_def fin_pow1_def fin_pow_def)
  done

lemma zmin_functional:
  "functional \<zmin>"
  apply (rule functionalI)
  apply (auto dest!: in_zminD2 simp add: order_class.glb_unique)
  done

lemma zmin_beta:
  assumes 
    a1: "(S::('a::znumbers) set) \<in> \<pset>\<subone> \<int>" "m \<in> S" "(\<forall> n | n \<in> S \<bullet> m \<le> n)"
  shows 
    "\<zmin>\<cdot>S = m"
  apply (intro functional_beta [OF zmin_functional])
  using a1
  apply (auto simp add: zmin_def Z_Pow1_def)
  done

lemma zmin_appl:
  assumes 
    a1: "(S::('a::znumbers) set) \<in> \<pset>\<subone> \<int>" "m \<in> S" "(\<forall> n \<bullet> n \<in> S \<and> m \<le> n)"
  shows 
    "(S \<mapsto> m) \<in> \<zmin>"
  using a1
  by (auto simp add: zmin_def Z_Pow1_def)
 

lemma zmin_betaE:
  assumes 
    a1: "(S::('a::znumbers) set) \<in> \<zdom> \<zmin>" and 
    a2: "\<lbrakk> \<zmin>\<cdot>S \<in> S;  (\<forall> n | n \<in> S \<bullet> \<zmin>\<cdot>S \<le> n) \<rbrakk> \<turnstile> R"
  shows 
    "R"
  apply (rule a2)
  apply (insert functional_appl [OF zmin_functional a1])
  apply (auto simp add: zmin_def)
  done


lemma in_zmaxD1:
  assumes 
    a1: "(S \<mapsto> x) \<in> \<zmax>"
  shows 
    "x \<in> S"
  using a1
  by (auto simp add: zmax_def)

lemma in_zmaxD2:
  assumes 
    a1: "(S \<mapsto> x) \<in> \<zmax>"
  shows 
    "is_lub \<univ> (op \<le>) S x"
  apply (rule order_class.is_lubI)
  using a1
  apply (auto simp add: zmax_def ge_def)
  done

lemma zmax_dom:
  "\<zdom> \<zmax>
  = {(S::('a::znumbers) set) | S \<in> \<pset>\<subone> \<int> \<and> (\<exists> m \<bullet> m \<in> S \<and> (\<forall> n | n \<in> S \<bullet> m \<ge> n))}"
  by (auto simp add: Z_Pow1_def zmax_def eind_def)

lemma exists_finite_max:
  assumes a1: "(S::('a::znumbers) set) \<in> \<fset>\<subone> \<int>"
  shows "(\<exists> m | m \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> m \<ge> n))"
proof -
  from a1 have 
    b0: "finite S" and b1: "S \<in> \<pset>\<subone> zInts"
    by (simp_all add: fin_pow1_def fin_pow_def Z_Pow1_def)
  from b0 have "S \<in> \<pset>\<subone> zInts \<Rightarrow> (\<exists> m | m \<in> zInts \<bullet> m \<in> S \<and> (\<forall> n | n \<in> S \<bullet> m \<ge> n))"
    apply (induct S set: finite)
    apply (auto simp add: Z_Pow1_def)
  proof -
    fix S x m 
    assume 
      c1: "x \<notin> S" and c2: "x \<in> zInts" and 
      c3: "S \<subseteq> zInts" and c4: "m \<in> zInts" and c5: "m \<in> S" and
      c6: "(\<forall> n | n \<in> S \<bullet> m \<ge> n)"
    then show "(\<exists> m | m \<in> zInts \<bullet> (m = x \<or> m \<in> S) \<and> m \<ge> x \<and> (\<forall> n | n \<in> S \<bullet> m \<ge> n))"
      apply (cases "x > m")
      apply (witness "x")
      apply (auto simp add: ge_def gt_def)
      done
  qed
  with b1 show ?thesis
    by (auto)
qed

lemma exists_zmax_bounded_upper:
  assumes a1: "S \<in> \<pset>\<subone> \<int>" and a2: "\<exists> m | m \<in> \<int> \<bullet> (\<forall> n | n \<in> S \<bullet> n \<le> m)"
  shows "\<exists> r | r \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> r \<ge> n)"
proof -
  from a1 Z_Pow1_def [of zInts] have a1': "S \<subseteq> zInts" and a1'': "S \<noteq> \<emptyset>" by auto
  from a2 obtain m where b0: "m \<in> zInts" and b1: "\<forall> n | n \<in> S \<bullet> m \<ge> n" by (auto simp add: ge_def)

  from a1'' have "\<exists> x \<bullet> x \<in> S" by auto then obtain x where b2: "x \<in> S" by auto
  with a1' have b2': "x \<in> zInts" by auto
  
  let ?A = "{n | n \<in> S \<and> x \<le> n}"
  let ?B = "S \<setminus> ?A"
  have b3: "S = ?A \<union> ?B" by auto

  from a1' b1 have "?A \<subseteq> zint_range x m"
    by (auto simp add: zint_range_def ge_def)
  then have "finite ?A"
    apply (rule finite_subset)
    apply (rule zint_range_finite [OF b2' b0])
    done
  with a1' have "?A \<in> \<fset>\<subone> zInts" 
    apply (auto simp add: Z_fin_pow1_def fin_pow_def)
    apply (witness "x")
    apply (auto simp add: b2)
    done
  with exists_finite_max [of ?A] have "\<exists> r | r \<in> ?A \<bullet> (\<forall> n | n \<in> ?A \<bullet> r \<ge> n)" by auto
  then obtain r where b4: "r \<in> ?A" and b5: "\<forall> n | n \<in> ?A \<bullet> r \<ge> n" by auto
  with b3 have b4': "r \<in> S" by auto

  from b4 b5 [rule_format] have "r \<ge> x" by (auto simp add: ge_def)
  then have b6: "\<forall> n | n \<in> ?B \<bullet> r \<ge> n" by (auto simp add: ge_def)
  have b7: "\<forall> n | n \<in> S \<bullet> r \<ge> n"
    apply (subst b3)
    apply (simp only: Un_iff)
    apply (msafe(inference))
    using b5 b6
    apply (auto)
    done


  from b4' b7 show "\<exists> m | m \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> m \<ge> n)"
    apply (witness "r")
    apply (auto simp add: ge_def)
    done
qed

lemma Z_fin_pow1_dom_max:
  "\<fset>\<subone> \<int> \<subseteq> \<zdom> \<zmax>"
  apply (auto intro: exists_finite_max simp add: zmax_dom)
  apply (simp add: Z_Pow1_def fin_pow1_def fin_pow_def)
  done

lemma zmax_functional:
  "functional \<zmax>"
  apply (rule functionalI)
  apply (auto dest!: in_zmaxD2 simp add: order_class.lub_unique)
  done

lemma zmax_beta:
  assumes 
    a1: "(S::('a::znumbers) set) \<in> \<pset>\<subone> \<int>" "m \<in> S" "(\<forall> n | n \<in> S \<bullet> m \<ge> n)"
  shows "\<zmax>\<cdot>S = m"
  apply (intro functional_beta [OF zmax_functional])
  using a1
  apply (auto simp add: zmax_def Z_Pow1_def)
  done

lemma zmax_appl:
  assumes 
    a1: "(S::('a::znumbers) set) \<in> \<pset>\<subone> \<int>" "m \<in> S" "(\<forall> n \<bullet> n \<in> S \<and> m \<ge> n)"
  shows 
    "(S \<mapsto> m) \<in> \<zmax>"
  using a1
  by (auto  simp add: zmax_def Z_Pow1_def)
 

lemma zmax_betaE:
  assumes
    a1: "(S::('a::znumbers) set) \<in> \<zdom> \<zmax>" and 
    a2: "\<lbrakk> \<zmax>\<cdot>S \<in> S;  (\<forall> n | n \<in> S \<bullet> \<zmax>\<cdot>S \<ge> n) \<rbrakk> \<turnstile> R"
  shows "R"
  apply (rule a2)
  apply (insert functional_appl [OF zmax_functional a1])
  apply (auto simp add: zmax_def)
  done

(*
lemma Z_pow_zmax_pow1:
  "(\<pset> \<nat>) \<inter> (\<zdom> \<zmax>) = \<pset>\<subone> \<nat>"
  apply auto
  apply (simp add: Z_Pow1_def zmax_def)
  apply (simp add: Z_Pow1_def)
  apply (erule conjE, auto)
  apply (auto intro: exists_zmin_zNats simp add: zmax_dom)
thm Z_zNats_zInts_conv exists_zmin_zNats
  apply (auto simp add: Z_Pow1_def Z_zNats_zInts_conv)
  done
*)

lemma Z_pow_zmax_fpow1:
  "(\<pset> \<nat>) \<inter> (\<zdom> \<zmax>) = \<fset>\<subone> \<nat>"
proof -
  let ?A = "(\<pset> zNats) \<inter> (\<zdom> zmax)"
  have b0: "?A \<subseteq> \<fset>\<subone> zNats" 
    apply (simp add: Z_fin_pow1_def fin_pow_def)
    apply (auto simp add: Pow_def zmax_dom)
  proof -
    fix x m
    assume c0: "x \<subseteq> zNats" and c1: "x \<in> \<pset>\<subone> zInts" and c2: "m \<in> x" and c3: "\<forall> n | n \<in> x \<bullet> m \<ge> n"

    let ?A = "{n | n \<in> x \<and> n < m}"

    from c2 have c4: "x = ?A \<union> {m}"
    proof auto
      fix r
      assume d0: "r \<in> x" and d1: "r \<noteq> m"
      from c3 [rule_format] d0 have d2: "r \<le> m" by (simp add: ge_def)
      with d1 d2 show "r < m" by arith
    qed

    from c4 c0 have c5: "finite ?A"
      by (auto intro: bounded_subset_zNats)
     
    show "finite x"
      apply (subst c4)
      apply (rule finite_UnI)
      apply (rule c5, auto)
      done
  qed

  have b1: "\<fset>\<subone> zNats \<subseteq> ?A"
  proof -
    have c0: "\<forall> x \<bullet> x \<in> \<fset>\<subone> zNats \<Rightarrow> finite x" 
      by (auto simp add: Z_fin_pow1_def fin_pow_def)
    have c1: "\<forall> x \<bullet> x \<in> \<fset>\<subone> zNats \<Rightarrow> x \<subseteq> zNats" 
      by (auto simp add: Z_fin_pow1_def fin_pow_def)
    have c2: "\<forall> x \<bullet> x \<in> \<fset>\<subone> zNats \<Rightarrow> x \<noteq> \<emptyset>" 
      by (auto simp add: Z_fin_pow1_def fin_pow_def)
    from c1 [rule_format] c2 [rule_format] Z_zNats_zInts_conv have c3: "\<forall> x \<bullet> x \<in> \<fset>\<subone> zNats \<Rightarrow> x \<in> \<pset>\<subone> zInts"
      by (auto simp add: Z_Pow1_def)

    have c4: "\<forall> x \<bullet> x \<in> \<fset>\<subone> zNats \<Rightarrow> (\<exists> m \<bullet> m \<in> x \<and> (\<forall> n | n \<in> x \<bullet> m \<ge> n))"
      apply (msafe(inference))
      apply (intro exists_finite_max)
      apply (simp add: Z_zNats_zInts_conv Z_fin_pow1_def)
      apply (auto simp add: fin_pow_def)
      done

    from c1 c3 c4 show ?thesis
      by (auto simp add: zmax_dom)
  qed



  from b0 b1 show ?thesis by auto
  
qed


lemma Z_min_union:
  assumes 
    a1: "S \<in> \<zdom> \<zmin>" and
    a2: "T \<in> \<zdom> \<zmin>"
  shows 
    "\<zmin>\<cdot>(S \<union> T) = \<zmin>\<cdot>{\<zmin>\<cdot>S, \<zmin>\<cdot>T}"
  apply (rule zmin_beta)
  using a1 a2
  apply (simp add: zmin_dom Z_Pow1_def)
proof -
  from functional_appl [OF zmin_functional a1] functional_appl [OF zmin_functional a2]
  have b1: "{zmin\<cdot>S, zmin\<cdot>T} \<in> \<fset>\<subone> zInts"
    by (simp add: Z_Pow1_def fin_pow1_def fin_pow_def zmin_def)
  with Z_fin_pow1_dom_min have b2: "{zmin\<cdot>S, zmin\<cdot>T} \<in> \<zdom> zmin"
    by (rule subsetD)
  from functional_appl [OF zmin_functional a1] functional_appl [OF zmin_functional a2] functional_appl [OF zmin_functional b2]
  show "zmin\<cdot>{zmin\<cdot>S, zmin\<cdot>T} \<in> S \<union> T" "(\<forall> n | n \<in> S \<union> T \<bullet> zmin\<cdot>{zmin\<cdot>S, zmin\<cdot>T} \<le> n)"
    by (auto simp add: zmin_def)
qed

lemma Z_max_union:
  assumes 
    a1: "S \<in> \<zdom> \<zmax>" and 
    a2: "T \<in> \<zdom> \<zmax>"
  shows 
    "\<zmax>\<cdot>(S \<union> T) = \<zmax>\<cdot>{\<zmax>\<cdot>S, \<zmax>\<cdot>T}"
  apply (rule zmax_beta)
  using a1 a2
  apply (simp add: zmax_dom Z_Pow1_def)
proof -
  from functional_appl [OF zmax_functional a1] functional_appl [OF zmax_functional a2]
  have b1: "{zmax\<cdot>S, zmax\<cdot>T} \<in> \<fset>\<subone> zInts"
    by (simp add: Z_Pow1_def fin_pow1_def fin_pow_def zmax_def)
  with Z_fin_pow1_dom_max have b2: "{zmax\<cdot>S, zmax\<cdot>T} \<in> \<zdom> zmax"
    by (rule subsetD)
  from functional_appl [OF zmax_functional a1] functional_appl [OF zmax_functional a2] functional_appl [OF zmax_functional b2]
  show "zmax\<cdot>{zmax\<cdot>S, zmax\<cdot>T} \<in> S \<union> T" "(\<forall> n | n \<in> S \<union> T \<bullet> zmax\<cdot>{zmax\<cdot>S, zmax\<cdot>T} \<ge> n)"
    by (auto simp add: zmax_def ge_def)
qed

lemma zmin_inter_dom:
  assumes 
    a1: "S \<in> \<zdom> \<zmin>" and 
    a2: "T \<in> \<zdom> \<zmin>" and 
    a3: "S \<inter> T \<noteq> {}"
  shows 
    "S \<inter> T \<in> \<zdom> \<zmin>"
proof (auto simp add: zmin_dom)
  from a1 a2 a3 show b0: "S \<inter> T \<in> \<pset>\<subone> zInts"
    by (auto simp add: zmin_dom Z_Pow1_def)

  from a1 have "\<exists> s | s \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> s \<le> n)" by (auto simp add: zmin_dom)
  then obtain s where b1: "s \<in> S" and b2: "\<forall> n | n \<in> S \<bullet> s \<le> n" by auto
  from a1 b1 have b1': "s \<in> zInts" by (auto simp add: zmin_dom Z_Pow1_def)

  from a2 have "\<exists> t | t \<in> T \<bullet> (\<forall> n | n \<in> T \<bullet> t \<le> n)" by (auto simp add: zmin_dom)
  then obtain t where b3: "t \<in> T" and b4: "\<forall> n | n \<in> T \<bullet> t \<le> n" by auto
  from a2 b3 have b3': "t \<in> zInts" by (auto simp add: zmin_dom Z_Pow1_def)

  show "\<exists> st \<bullet> st \<in> S \<and> st \<in> T \<and> (\<forall> n | n \<in> S \<and> n \<in> T \<bullet> st \<le> n)"
  proof (cases "s \<le> t")
    assume c0: "s \<le> t"
    from c0 b2 b4 have "\<forall> n | n \<in> S \<inter> T \<bullet> s \<le> n" by auto
  
    with b1' have "\<exists> m | m \<in> S \<inter> T \<bullet> (\<forall> n | n \<in> S \<inter> T \<bullet> m \<le> n)"
      apply (intro exists_zmin_bounded_lower [OF b0])
      apply (witness "s")
      apply auto
      done
    then show ?thesis by auto
  next
    assume c1: "\<not> s \<le> t" then have c1': "t \<le> s" by (auto simp add: ge_def)
   
    from c1' b2 b4 have "\<forall> n | n \<in> S \<inter> T \<bullet> t \<le> n" by auto

    with b3' have  "\<exists> m | m \<in> S \<inter> T \<bullet> (\<forall> n | n \<in> S \<inter> T \<bullet> m \<le> n)"
      apply (intro exists_zmin_bounded_lower [OF b0])
      apply (witness "t")
      apply auto
      done
    then show ?thesis by auto
  qed
qed


lemma Z_min_inter:
  assumes 
    a1: "S \<in> \<zdom> \<zmin>" and 
    a2: "T \<in> \<zdom> \<zmin>" and 
    a3: "S \<inter> T \<noteq> {}"
  shows 
    "\<zmin>\<cdot>(S \<inter> T) \<ge> \<zmin>\<cdot>S"
proof -
  from a1 have "\<exists> s \<bullet> s \<in> S \<and> (\<forall> n | n \<in> S \<bullet> s \<le> n)" by (auto simp add: zmin_dom)
  then obtain s where b0: "s \<in> S" and b1: "\<forall> n | n \<in> S \<bullet> s \<le> n" by auto
  from b0 b1 a1 have zmins: "zmin\<cdot>S = s"
    apply (intro zmin_beta)
    apply (auto simp add: zmin_dom)
    done



  have a4: "S \<inter> T \<in> \<zdom> zmin"
    by (rule zmin_inter_dom [OF a1 a2 a3])
  then have "\<exists> st | st \<in> S \<inter> T \<bullet> (\<forall> n | n \<in> S \<inter> T \<bullet> st \<le> n)" by (auto simp add: zmin_dom)
  then obtain st where b2: "st \<in> S \<inter> T" and b3: "\<forall> n | n \<in> S \<inter> T \<bullet> st \<le> n" by auto
  from b2 b3 a4 have zminst: "zmin\<cdot>(S \<inter> T) = st"
    apply (intro zmin_beta)
    by (auto simp add: zmin_dom)

  from b2 have "st \<in> S" by auto
  with b1 show "zmin\<cdot>(S \<inter> T) \<ge> zmin\<cdot>S"
    apply (subst zmins)
    apply (subst zminst)
    apply (simp add: ge_def)
    done
qed

lemma Z_min_inter':
  assumes  
    a1: "S \<in> \<zdom> \<zmin>" and 
    a2: "T \<in> \<zdom> \<zmin>" and 
    a3: "S \<inter> T \<noteq> \<emptyset>"
  shows "\<zmin>\<cdot>(S \<inter> T) \<ge> \<zmin>\<cdot>T"
proof -
  from a2 have "\<exists> t \<bullet> t \<in> T \<and> (\<forall> n | n \<in> T \<bullet> t \<le> n)" by (auto simp add: zmin_dom)
  then obtain t where b0: "t \<in> T" and b1: "\<forall> n | n \<in> T \<bullet> t \<le> n" by auto
  from b0 b1 a2 have zmint: "zmin\<cdot>T = t"
    apply (intro zmin_beta)
    by (auto simp add: zmin_dom)
   

  have a4: "S \<inter> T \<in> \<zdom> zmin"
    by (rule zmin_inter_dom [OF a1 a2 a3])
  then have "\<exists> st | st \<in> S \<inter> T \<bullet> (\<forall> n | n \<in> S \<inter> T \<bullet> st \<le> n)" by (auto simp add: zmin_dom)
  then obtain st where b2: "st \<in> S \<inter> T" and b3: "\<forall> n | n \<in> S \<inter> T \<bullet> st \<le> n" by auto
  from b2 b3 a4 have zminst: "zmin\<cdot>(S \<inter> T) = st"
    apply (intro zmin_beta)
    by (auto simp add: zmin_dom)

  from b2 have "st \<in> T" by auto
  with b1 show "zmin\<cdot>(S \<inter> T) \<ge> zmin\<cdot>T"
    apply (subst zmint)
    apply (subst zminst)
    apply (auto simp add: ge_def)
    done
qed

lemma zmax_inter_dom:
  assumes 
    a1: "S \<in> \<zdom> \<zmax>" and 
    a2: "T \<in> \<zdom> \<zmax>" and 
    a3: "S \<inter> T \<noteq> \<emptyset>"
  shows 
    "S \<inter> T \<in> \<zdom> \<zmax>"

proof (auto simp add: zmax_dom)

  from a1 a2 a3 show b0: "S \<inter> T \<in> \<pset>\<subone> zInts"
    by (auto simp add: zmax_dom Z_Pow1_def)

  from a1 have "\<exists> s | s \<in> S \<bullet> (\<forall> n | n \<in> S \<bullet> s \<ge> n)" by (auto simp add: zmax_dom)
  then obtain s where b1: "s \<in> S" and b2: "\<forall> n | n \<in> S \<bullet> s \<ge> n" by auto
  from a1 b1 have b1': "s \<in> zInts" by (auto simp add: zmax_dom Z_Pow1_def)

  from a2 have "\<exists> t | t \<in> T \<bullet> (\<forall> n | n \<in> T \<bullet> t \<ge> n)" by (auto simp add: zmax_dom)
  then obtain t where b3: "t \<in> T" and b4: "\<forall> n | n \<in> T \<bullet> t \<ge> n" by auto
  from a2 b3 have b3': "t \<in> zInts" by (auto simp add: zmax_dom Z_Pow1_def)

  show "\<exists> st \<bullet> st \<in> S \<and> st \<in> T \<and> (\<forall> n | n \<in> S \<and> n \<in> T \<bullet> st \<ge> n)"
  proof (cases "s \<ge> t")
    assume c0: "s \<ge> t"
    from c0 b2 b4 have "\<forall> n | n \<in> S \<inter> T \<bullet> s \<ge> n" by auto
  
    with b1' have "\<exists> m | m \<in> S \<inter> T \<bullet> (\<forall> n | n \<in> S \<inter> T \<bullet> m \<ge> n)"
      apply (intro exists_zmax_bounded_upper [OF b0])
      apply (witness "s")
      apply (auto simp add: ge_def)
      done
    then show ?thesis by auto
  next
    assume c1: "\<not> s \<ge> t" then have c1': "t \<ge> s" by (auto simp add: ge_def)
   
    from c1' b2 b4 have "\<forall> n | n \<in> S \<inter> T \<bullet> t \<ge> n" by auto

    with b3' have  "\<exists> m | m \<in> S \<inter> T \<bullet> (\<forall> n | n \<in> S \<inter> T \<bullet> m \<ge> n)"
      apply (intro exists_zmax_bounded_upper [OF b0])
      apply (witness "t")
      apply (auto simp add: ge_def)
      done
    then show ?thesis by auto
  qed
qed


lemma Z_max_inter:
  assumes
    a1: "S \<in> \<zdom> \<zmax>" and 
    a2: "T \<in> \<zdom> \<zmax>" and 
    a3: "S \<inter> T \<noteq> \<emptyset>"
  shows 
    "\<zmax>\<cdot>(S \<inter> T) \<le> \<zmax>\<cdot>S"

proof - 
  from a1 have "\<exists> s \<bullet> s \<in> S \<and> (\<forall> n | n \<in> S \<bullet> s \<ge> n)" by (auto simp add: zmax_dom)
  then obtain s where b0: "s \<in> S" and b1: "\<forall> n | n \<in> S \<bullet> s \<ge> n" by auto
  from b0 b1 a1 have zmaxs: "zmax\<cdot>S = s"
    apply (intro zmax_beta)
    apply (auto simp add: zmax_dom)
    done

  have a4: "S \<inter> T \<in> \<zdom> zmax"
    by (rule zmax_inter_dom [OF a1 a2 a3])
  then have "\<exists> st | st \<in> S \<inter> T \<bullet> (\<forall> n | n \<in> S \<inter> T \<bullet> st \<ge> n)" by (auto simp add: zmax_dom)
  then obtain st where b2: "st \<in> S \<inter> T" and b3: "\<forall> n | n \<in> S \<inter> T \<bullet> st \<ge> n" by auto
  from b2 b3 a4 have zmaxst: "zmax\<cdot>(S \<inter> T) = st"
    apply (intro zmax_beta)
    by (auto simp add: zmax_dom)

  from b2 have "st \<in> S" by auto
  with b1 show "zmax\<cdot>(S \<inter> T) \<le> zmax\<cdot>S"
    apply (subst zmaxs)
    apply (subst zmaxst)
    apply (simp add: ge_def)
    done
qed 

lemma Z_max_inter':
  assumes 
    a1: "S \<in> \<zdom> \<zmax>" and 
    a2: "T \<in> \<zdom> \<zmax>" and 
    a3: "S \<inter> T \<noteq> \<emptyset>"
  shows "\<zmax>\<cdot>(S \<inter> T) \<le> \<zmax>\<cdot>T"

proof - 
  from a2 have "\<exists> t \<bullet> t \<in> T \<and> (\<forall> n | n \<in> T \<bullet> t \<ge> n)" by (auto simp add: zmax_dom)
  then obtain t where b0: "t \<in> T" and b1: "\<forall> n | n \<in> T \<bullet> t \<ge> n" by auto
  from b0 b1 a2 have zmaxt: "zmax\<cdot>T = t"
    apply (intro zmax_beta)
    apply (auto simp add: zmax_dom)
    done

  have a4: "S \<inter> T \<in> \<zdom> zmax"
    by (rule zmax_inter_dom [OF a1 a2 a3])
  then have "\<exists> st | st \<in> S \<inter> T \<bullet> (\<forall> n | n \<in> S \<inter> T \<bullet> st \<ge> n)" by (auto simp add: zmax_dom)
  then obtain st where b2: "st \<in> S \<inter> T" and b3: "\<forall> n | n \<in> S \<inter> T \<bullet> st \<ge> n" by auto
  from b2 b3 a4 have zmaxst: "zmax\<cdot>(S \<inter> T) = st"
    apply (intro zmax_beta)
    by (auto simp add: zmax_dom)

  from b2 have "st \<in> T" by auto
  with b1 show "zmax\<cdot>(S \<inter> T) \<le> zmax\<cdot>T"
    apply (subst zmaxt)
    apply (subst zmaxst)
    apply (simp add: ge_def)
    done
qed 

lemma Z_min_max_zint_range:
  assumes 
    a1: "a \<in> \<int>" and 
    a2: "b \<in> \<int>"
  shows 
    "a \<le> b \<Rightarrow> \<zmin>\<cdot>(a..b) = a \<and> \<zmax>\<cdot>(a..b) = b"
  apply (msafe(inference))
  apply (rule zmin_beta)
  using a1 a2
  apply (auto simp add: zint_range_def Z_Pow1_def)
  apply (rule zmax_beta)
  apply (auto simp add: zint_range_def Z_Pow1_def)
  apply (simp add: ge_def)
  done

lemma Z_zint_range_inter_min_max:
  assumes 
    a1: "a \<in> \<int>" and 
    a2: "b \<in> \<int>" and 
    a3: "c \<in> \<int>" and
    a4: "d \<in> \<int>"
  shows 
    "((a..b) \<inter> (c..d)) = (\<zmax>\<cdot>{a, c})..(\<zmin>\<cdot>{b, d})"
proof (auto simp add: zint_range_def)
  fix x
  assume b0: "x \<in> zInts" "a \<le> x" "c \<le> x" "x \<le> b" "x \<le> d"

  then have b1: "zmax\<cdot>{a, c} = a \<or> zmax\<cdot>{a, c} = c"
  proof (cases "a = c")
    apply_end simp
    show "zmax\<cdot>{c} = c"
      apply (rule zmax_beta)
      apply (auto simp add: Z_Pow1_def a3)
      done
  next
    assume 
      b0: "a \<noteq> c"
    show 
      ?thesis
    proof (cases "a < c")
      assume b1: "a < c" then have b1': "c \<ge> a" by (simp add: ge_def)
      show ?thesis
        apply (rule disjI2)
        apply (rule zmax_beta)
        apply (auto simp add: Z_Pow1_def b1' a1 a3)
        done
    next
      assume b1: "\<not> a < c" then have b1': "a \<ge> c" by (simp add: ge_def)
      show ?thesis
        apply (rule disjI1)
        apply (rule zmax_beta)
        apply (auto simp add: Z_Pow1_def b1' a1 a3)
        done
    qed
  qed
  with b0 show "zmax\<cdot>{a, c} \<le> x" 
    by (auto)

  have b1: "zmin\<cdot>{b, d} = b \<or> zmin\<cdot>{b, d} = d"
  proof (cases "b = d")
    apply_end simp
    show "zmin\<cdot>{d} = d"
      apply (rule zmin_beta)
      apply (auto simp add: Z_Pow1_def a4)
      done
  next
    show ?thesis
    proof (cases "b < d")
      assume 
        d1: "b < d"
      show ?thesis
        apply (rule disjI1)
        apply (rule zmin_beta)
        using d1
        apply (auto simp add: Z_Pow1_def a2 a4)
        done
    next
      assume 
        d1: "\<not> b < d"
      show 
        ?thesis
        apply (rule disjI2)
        apply (rule zmin_beta)
        using d1
        apply (auto simp add: Z_Pow1_def a2 a4)
        done
    qed
  qed

  with b0 show "x \<le> zmin\<cdot>{b, d}" by (auto)
next
  fix x
  assume b0: "x \<in> zInts" and b1: "zmax\<cdot>{a, c} \<le> x" and b2: "x \<le> zmin\<cdot>{b, d}"


  have "\<exists> mx | mx \<in> {a, c} \<bullet> (\<forall> n | n \<in> {a, c} \<bullet> mx \<ge> n)"
    apply (intro exists_finite_max)
    apply (simp add: fin_pow1_def fin_pow_def a1 a3)
    done
  then obtain mx where 
    b3: "mx \<in> {a, c}" and b4: "\<forall> n | n \<in> {a, c} \<bullet> mx \<ge> n" 
    by auto
  then have "zmax\<cdot>{a,c} = mx"
    apply (intro zmax_beta)
    apply (auto simp add: Z_Pow1_def a1 a3)
    done
  with b1 have b1': "mx \<le> x" by auto

  from b4 have 
    "mx \<ge> a" 
    by (auto)
  with b1' show  "a \<le> x" by (auto simp add: ge_def)

  from b4 have "mx \<ge> c" by (auto)
  with b1' show "c \<le> x" by (auto simp add: ge_def)


  have "\<exists> mn | mn \<in> {b, d} \<bullet> (\<forall> n | n \<in> {b, d} \<bullet> mn \<le> n)"
    apply (intro exists_finite_min)
    apply (simp add: fin_pow1_def fin_pow_def a2 a4)
    done
  then obtain mn where 
    b5: "mn \<in> {b, d}" and b6: "\<forall> n | n \<in> {b, d} \<bullet> mn \<le> n" 
    by auto
  then have "zmin\<cdot>{b, d} = mn"
    apply (intro zmin_beta)
    apply (auto simp add: Z_Pow1_def a2 a4)
    done
  with b2 have b2' : "x \<le> mn" by auto

  from b6 have "mn \<le> b" by (auto)
  with b2' show "x \<le> b" by auto

  from b6 have "mn \<le> d" by (auto)
  with b2' show "x \<le> d" by auto
qed

section {* Instantiating @{text "\<arithmos>"} to the Reals *}

type_synonym
  arithmos = Real.real

type_notation (xsymbols)
  arithmos ("\<arithmos>")

type_notation (xsymbols output)
  Real.real ("\<arithmos>")

instance real :: znumbers
  by (intro_classes)

no_notation (xsymbols)
  zArith ("\<arithmos>") and
  zNats ("\<nat>") and
  zNats1 ("\<nat>\<subone>") and
  zInts ("\<int>")

abbreviation
  "zArith_arithmos \<defs> zArith-[\<arithmos>]"

abbreviation
  "zNats_arithmos \<defs> zNats-[\<arithmos>]"

abbreviation
  "zNats1_arithmos \<defs> zNats1-[\<arithmos>]"

abbreviation
  "zInts_arithmos \<defs> zInts-[\<arithmos>]"

notation  (xsymbols)
  zArith_arithmos ("\<arithmos>") and
  zNats_arithmos ("\<nat>") and
  zNats1_arithmos ("\<nat>\<subone>") and
  zInts_arithmos ("\<int>")

no_notation
  zsucc ("\<zsucc>")

abbreviation
  "zsucc_arithmos \<defs> zsucc-[\<arithmos>]"

notation
  zsucc_arithmos ("\<zsucc>")

no_notation (xsymbols)
  zint_range (infixl ".." 110)

abbreviation
  "zint_range_arithmos \<defs> zint_range-[\<arithmos>]"

notation (xsymbols)
  zint_range_arithmos (infixl ".." 110)

no_notation
  zcard ("\<zcard>")

abbreviation
  "zcard_arithmos \<defs> zcard-['a,\<arithmos>]"

notation
  zcard_arithmos ("\<zcard>")

no_notation
  zmod ("\<zmod>")

abbreviation
  "zmod_arithmos \<defs> zmod-[\<arithmos>]"

notation
  zmod_arithmos ("\<zmod>")

no_notation
  zdiv ("\<zdiv>")

abbreviation
  "zdiv_arithmos \<defs> zdiv-[\<arithmos>]"

notation
  zdiv_arithmos ("\<zdiv>")

no_syntax (xsymbols)
  "_Z_Numbers\<ZZ>ziter" :: "[logic, logic, logic] \<rightarrow> logic" ("_\<^bzup>_\<^ezup>[_]" [1000] 999)

no_translations
  "_Z_Numbers\<ZZ>ziter R n X" \<rightleftharpoons> "CONST Z_Numbers.ziter X n R"

abbreviation
  "ziter_arithmos \<defs> ziter-['a, \<arithmos>]"

syntax (xsymbols)
  "_Z_Numbers\<ZZ>ziter" :: "[logic, logic, logic] \<rightarrow> logic" ("_\<^bzup>_\<^ezup>[_]" [1000] 999)
  "_Z_Numbers\<ZZ>zitera" :: "[logic, logic, logic] \<rightarrow> logic" ("_\<^zitera>{:_:}{:_:}" [1000] 999)

translations
  "_Z_Numbers\<ZZ>ziter R n X" \<rightleftharpoons> "CONST Z_Numbers.ziter_arithmos X n R"
  "_Z_Numbers\<ZZ>zitera R n X" \<rightharpoonup> "_Z_Numbers\<ZZ>ziter R n X"

no_notation
  zmin ("\<zmin>")

abbreviation
  "zmin_arithmos \<defs> zmin-[\<arithmos>]"

notation
  zmin_arithmos ("\<zmin>")

no_notation
  zmax ("\<zmax>")

abbreviation
  "zmax_arithmos \<defs> zmax-[\<arithmos>]"

notation
  zmax_arithmos ("\<zmax>")

end
