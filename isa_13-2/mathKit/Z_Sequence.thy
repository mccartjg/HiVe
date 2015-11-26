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
  Z_Sequence

imports 
  Z_Fun 
  Z_Numbers
  Z_Sequence_Chap

begin

section {* The sequence model *}

text {*

Finite sequences are taken from the set of finite functions from @{text "\<nat>"} to 
@{text "X"} whose @{text "\<zdom>"} is the segment @{text "(1..n)"} 
for some natural number, @{text "n"}.  
We develop a syntax and type constructors for the @{text "\<zseq>"} type and 
introduce basic lemmas.
*}

type_synonym
  'a seqT = "(\<arithmos> \<leftrightarrow> 'a)"

definition
  seq :: "'a set \<rightarrow> 'a seqT set"
where
  seq_def : "seq X \<defs> (\<Union> n | n \<in> \<nat> \<bullet> (1..n) \<ztfun> X)"

notation (zed)
  seq ("\<zseq>")

lemma seqIa:
  assumes 
    a1: "n \<in> \<nat>" "s \<in> (1..n) \<ztfun> X"
  shows 
    "s \<in> \<zseq> X"
  using a1
  by (auto simp add: seq_def)

lemma seqEa:
  assumes a1: "s \<in> \<zseq> X" "\<And> n \<bullet> \<lbrakk> n \<in> \<nat>; s \<in> (1..n) \<ztfun> X \<rbrakk> \<turnstile> R"
  shows "R"
  using a1
  by (auto simp add: seq_def)

lemma seq_functional:
  assumes a1: "s \<in> \<zseq> X"
  shows "functional s"
  apply (rule seqEa [OF a1])
  apply ((mauto(fspace)))
  done

lemma seq_finite:
  assumes a1: "s \<in> \<zseq> X"
  shows "finite s"
  apply (rule seqEa [OF a1])
  apply (rule dom_finite_fun)
  apply (mauto(fspace))
  apply (simp add: zint_range_finite zInts_zNats)
  done

lemma seq_finite_dom:
  assumes a1: "s \<in> \<zseq> X"
  shows "finite (\<zdom> s)"
  apply (rule seqEa [OF a1])
  apply ((mauto(fspace)))
  apply (simp add: zint_range_finite zInts_zNats)
  done

lemma seq_zcard_dom:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zcard>s = \<zcard>(\<zdom> s)"
  apply (rule fun_zcard_dom)
  apply (rule seq_functional [OF a1])
  done

lemma seq_dom:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zdom> s = 1..(\<zcard>s)"
proof -
  from a1 obtain n where a2: "\<zdom> s = (1..n)" and a3: "n \<in> \<nat>"
    apply (elim seqEa) 
    apply (mauto(fspace))
    done
  from seq_zcard_dom [OF a1] 
  have "\<zcard>s = \<zcard>(\<zdom> s)"
    by (this)
  also have "\<dots> = \<zcard>(1..n)"
    by (simp add: a2)
  also have "\<dots> = n"
    by (simp add: zint_range_zcard_from_1 [OF a3]) 
  finally show ?thesis 
    by (simp add: a2)
qed

lemma seq_ran:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> s \<subseteq> X"
  apply (rule seqEa [OF a1])
  apply ((mauto(fspace)))
  done

lemma seq_finite_ran:
  "s \<in> \<zseq> X \<turnstile> finite (\<zran> s)"
  by (auto intro: fun_finite_ran seq_finite)

lemma seq_in_ran1:
  assumes a1: "s \<in> \<zseq> X" and a2: "n \<in> \<zdom> s"
  shows "s\<cdot>n \<in> \<zran> s"
  apply (rule functional_ran)
  apply (rule seq_functional [OF a1])
  apply (rule a2)
  done

lemma seq_in_ran:
  assumes a1: "s \<in> \<zseq> X" and a2: "n \<in> \<zdom> s"
  shows "s\<cdot>n \<in> X"
  using seq_in_ran1 [OF a1 a2] seq_ran [OF a1]
  by (auto)


lemma seqI [mintro!(fspace)]:
  assumes a1: "s \<in> (1..\<zcard>s) \<ztfun> X"
  shows "s \<in> \<zseq> X"
  apply (rule seqIa [of "\<zcard>s"])
  using a1
  apply (auto simp add: zNats_zcard)
  done

lemma seqD:
  assumes a1: "s \<in> \<zseq> X"
  shows "s \<in> (1..\<zcard>s) \<ztfun> X"
  apply (mauto(fspace))
  apply (rule seq_functional [OF a1])
  apply (insert seq_dom [OF a1], simp)
  apply (rule seq_ran [OF a1])
  done

lemma seqE [melim!(fspace)]:
  assumes a1: "s \<in> \<zseq> X" and a2: "s \<in> (1..\<zcard>s) \<ztfun> X \<turnstile> R"
  shows "R"  
  apply (rule a2)
  apply (rule seqD [OF a1])
  done

lemma seq_mem:
  "s \<in> \<zseq> X \<Leftrightarrow> s \<in> (1..\<zcard>s) \<ztfun> X"
  by (auto intro: seqD seqI)

lemma seq_index_bound:  
  assumes a1: "s \<in> \<zseq> X" and a2: "(n \<mapsto> x) \<in> s"  
  shows  "n \<in> \<int> \<and> 1 \<le> n \<and> n \<le> \<zcard>s" 
proof (msafe(inference)) 
  from a2 have  b0: "n \<in> \<zdom> s"  by (auto simp add: Domain_def)  
  from b0 seq_dom [OF a1] show "n \<in> \<int>" by auto
  from b0 seq_dom [OF a1] show "n \<le> \<zcard>s" by auto
  from b0 seq_dom [OF a1] show "1 \<le> n" by auto
qed

lemma seq_appl:
  assumes a1: "s \<in> \<zseq> X" and a2: "n \<in> \<int>" and a3: "1 \<le> n" and a4: "n \<le> \<zcard>s"
  shows "(n \<mapsto> s\<cdot>n) \<in> s"
proof (rule functional_appl)
  from seq_functional [OF a1] show "functional s" by this
  from a2 a3 a4 seq_dom [OF a1] show "n \<in> \<zdom> s"  
    by (simp add: zInts_one_le_iff_zero_less Z_zNats_zInts_conv)
qed

lemma seq_beta:
  assumes a1: "s \<in> \<zseq> X" and a2: "(n \<mapsto> x) \<in> s"
  shows "s\<cdot>n = x"
proof -
  from seq_functional [OF a1] have b1: "functional s" by this
  from b1 a2 show ?thesis by (simp add: functional_beta)
qed

lemma Z_ran_redef:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> s = { i | i \<in> (1..\<zcard>s) \<bullet> s\<cdot>i}"
  apply (simp add: dsub_def)
  apply (rule set_eqI, mauto(inference) msimp add: Range_iff Domain_iff)
proof - 
  fix y x
  assume b0: "(x, y) \<in> s"

  from b0 have "x \<in> \<zdom> s" by auto
  then have b1: "x \<in> (1..\<zcard>s)" by (simp add: seq_dom [OF a1])
  
  show "y \<in> {i | i \<in> \<int> \<and> 1 \<le> i \<and> i \<le> \<zcard>s \<bullet> s\<cdot>i}" 
    apply auto
    apply (witness "x")
    apply (intro conjI)
    apply (rule seq_beta [OF a1 b0, THEN sym])
    apply (insert b1)
    apply (simp_all add: zcard_def)
    done
next
  fix y
  assume b0: "y \<in> {i | i \<in> \<int> \<and> 1 \<le> i \<and> i \<le> \<zcard>s \<bullet> s\<cdot>i}"
  from b0 obtain i where b1: "i \<in> \<int>" and b2: "1 \<le> i" and b3: "i \<le> \<zcard>s" and b4: "y = s\<cdot>i" by auto

  show "\<exists> x \<bullet> (x, y) \<in> s"
    apply (witness "i")
    apply (simp add: b4)
    apply (rule seq_appl [OF a1])
    apply (rule b1, rule b2, rule b3)
    done
qed

  

lemma seq_transitive:
  assumes a1: "A \<subseteq> X" and a2: "t \<in> \<zseq> A"
  shows "t \<in> \<zseq> X"
  using a1 seq_dom [OF a2] seq_ran [OF a2] seq_functional [OF a2]
  by (mauto(fspace))


lemma seq_seq_ran:
  assumes a1: "s \<in> \<zseq> X"
  shows "s \<in> \<zseq> (\<zran> s)"
  by (mauto(fspace) mintro: seq_functional [OF a1] seq_dom [OF a1])

lemma seq_X_ran:
  assumes a1: "v \<in> \<zseq> X" and a2: "\<zran> v \<subseteq> \<zran> t"
  shows "v \<in> \<zseq> (\<zran> t)"
  by (mauto(fspace) mintro: seq_functional [OF a1] seq_dom [OF a1] a2)


section {* Non-empty Sequences *}

text
{*

The empty sequence @{text "\<sempty>"} is an alternate notation for the @{text "\<emptyset>"} 
function from @{text "\<arithmos>"} to @{text "X"}.

*}

definition
  sempty :: "'a seqT"
where
  sempty_def : "sempty \<defs> \<emptyset>"

notation (zed)
  sempty ("\<sempty>") 

notation (xsymbols)
  sempty ("\<lang> \<rang>")

lemma sempty_seq: "\<lang> \<rang> \<in> \<zseq> X"
  apply (simp add: sempty_def)
  apply (rule seqIa [where ?n = "0"])
  apply (mauto(fspace) mintro!: fin_pfunI)
  apply (auto)
  done

lemma Z_sempty_ran:
  "\<zran> \<lang> \<rang> = \<emptyset>"
  by (simp add: sempty_def)

lemma zcard_sempty [simp]:
  "\<zcard>\<lang> \<rang> = 0"
  by (simp add: sempty_def)

lemma zcard_zero:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zcard>s = 0 \<Leftrightarrow> s = \<lang> \<rang>"
  using a1 [THEN seq_finite]
  by (simp add: sempty_def zcard_def)

text
{*

@{text "\<zseq>\<subone>"} is the set of all finite sequences over @{text "X"} 
except for the empty sequence @{text "\<sempty>"}.

*}

definition
  seq1 :: "'a set \<rightarrow> 'a seqT set"
where
  seq1_def: "seq1 X \<defs> { s | s \<in> \<zseq> X \<and> 0 < \<zcard>s }"

notation (xsymbols)
  seq1 ("\<zseq>\<subone>")

lemma
  seq1_nonempty: "\<zseq>\<subone> X = (\<zseq> X - {\<sempty>})"
  apply (rule set_eqI)
  apply (simp add: seq1_def)
  apply (mauto(wind) msimp add: seq_finite zcard_nempty_conv sempty_def)
  done

lemma seq1I [mintro!(fspace)]:
  assumes 
    a1: "s \<in> \<zseq> X" "s \<noteq> \<sempty>"
  shows 
    "s \<in> \<zseq>\<subone> X"
  using a1
  by (auto simp add: seq1_nonempty)
  
lemma seq1E [melim!(fspace)]:
  assumes 
    a1: "s \<in> \<zseq>\<subone> X" "\<lbrakk> s \<in> \<zseq> X; s \<noteq> \<sempty> \<rbrakk> \<turnstile> R"
  shows 
    "R"
  using a1
  by (auto simp add: seq1_nonempty)

lemma seq1D:
  assumes
    a1: "s \<in> \<zseq>\<subone> X"
  shows 
    seq1_seq: "s \<in> \<zseq> X" and 
    seq1_nempty: "s \<noteq> \<sempty>"
  using a1
  by (simp_all add: seq1_nonempty sempty_def)

lemma seq1_functional:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "functional s"
proof -
  from a1 have a1': "s \<in> \<zseq> X" by (intro seq1D)
  then show "functional s" by (rule seq_functional)
qed

lemma seq1_card_gr_0:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "0 < \<zcard>s"
proof -
  from a1 have b1: "s \<in> \<zseq> X" by (simp add: seq1_nonempty)
  from a1 have b2: "s \<noteq> \<sempty>" by (simp add: seq1_nonempty sempty_def)
  then have "\<zcard>s \<noteq> 0" 
    by (simp add: zcard_zero [OF b1])
  moreover have "0 \<le> \<zcard>s"
    by (simp add: zNats_le0)
  ultimately show ?thesis
    by (auto)
qed

lemma seq1_card_ge_1:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "1 \<le> \<zcard>s"
  using seq1_card_gr_0 [OF a1]
  by (simp add: zInts_one_le_iff_zero_less zInts_zcard)


section {* Injective Sequences *}

text
{*
@{text "\<ziseq> X"} is the set of injective finite 
sequences over X: these are precisely the finite sequences over X which contain no repetitions.
*}


definition
  iseq :: "'a set \<rightarrow> 'a seqT set"
where
  iseq_def: "iseq X \<defs> \<zseq> X \<inter> (\<nat> \<zpinj> X)"

notation (xsymbols)
  iseq ("\<ziseq>")

lemma iseqI [mintro!(fspace)]:
  assumes
    a1: "s \<in> (1..\<zcard>s) \<zinj> X"
  shows 
   "s \<in> \<ziseq> X"
  using a1
  apply (auto simp add: iseq_def)
  apply ((mauto(fspace)))
  apply (auto simp add: Z_zNats_zInts_conv)
  done

lemma iseqE [melim!(fspace)]:
  assumes 
    a1: "s \<in> \<ziseq> X" and 
    a2: "\<And> n \<bullet> s \<in> (1..\<zcard>s) \<zinj> X \<turnstile> R"
  shows 
    "R"
  using a1
  apply (auto simp add: iseq_def)
  apply ((mauto(fspace)))
  apply (rule a2)
  apply (mauto(fspace))
  done

section {* Infinite Sequences *}

text
{*

Infinite sequences are those sequences that have the whole of @{text "\<nat>"} as their Domain.

*}

definition
  inf_seq :: "'a set \<rightarrow> 'a seqT set"
where
  inf_seq_def: "inf_seq X \<defs> \<zseq> X \<union> \<nat> \<ztfun> X"

notation (xsymbols)
  inf_seq ("\<zseq>\<^sub>\<infinity>")

lemma inf_seqI [mintro!(fspace)]:
  assumes 
    a1: "n \<in> \<nat> \<and> s \<in> (1..n) \<ztfun> X \<or> s \<in> \<nat> \<ztfun> X"
  shows 
    "s \<in> \<zseq>\<^sub>\<infinity> X"
  using a1
  by (auto simp add: inf_seq_def seq_def)

lemma inf_seqE [melim!(fspace)]:
  assumes 
    a1: "s \<in> \<zseq>\<^sub>\<infinity> X" and 
    a2: "\<And> n \<bullet> n \<in> \<nat> \<and> s \<in> (1..n) \<ztfun> X \<or> s \<in> \<nat> \<ztfun> X \<turnstile> R"
  shows "R"
  using a1 a2
  by (auto simp add: inf_seq_def seq_def)


section {* Sequence Construction *}


text {*

We develop a step-by-step construction of sequences.  
This section also presents the case and induction theorems for sequences.

*}

text {*

As a first step, we introduce the stranslate function which translates the Domain of the 
sequence by a natural number n. 

*}

definition
  stranslate :: "['a seqT, \<arithmos>] \<rightarrow> 'a seqT"
where
  stranslate_def : "stranslate s n_d_0 \<defs> {n x | (n \<mapsto> x) \<in> s \<bullet> (n + n_d_0 \<mapsto> x)}"

lemma stranslate_conv: "stranslate s n_d_0 = {x \<bullet> x + n_d_0 \<mapsto> x} \<zfcomp> s"
  by (simp add: stranslate_def rel_fcomp_def set_eq_def rel_bcomp_def)
  
lemma stranslate_image:
  "stranslate s n_d_0 = (\<olambda>(n, x) \<bullet> (n + n_d_0 \<mapsto> x)) \<lparr> s \<rparr>"
  by (auto simp add: stranslate_def)

lemma stranslate_sempty: "stranslate \<sempty> n = \<sempty>"
  by (simp add: stranslate_def sempty_def)

lemma stranslate_functional:
  assumes a1: "functional s"
  shows "functional (stranslate s n0)"
  apply (simp add: stranslate_conv)
  apply (rule fcomp_functional [OF _ a1])
  apply (rule functionalI)
  apply (auto)
  done

lemma stranslate_finite: 
 assumes a1: "finite s"
 shows "finite (stranslate s n)"
 apply (simp only: stranslate_def)
 apply (insert a1)
 apply (induct rule: finite_induct)
 apply (simp)
proof -
  fix x:: "\<arithmos> \<times> 'a" and  F :: "(\<arithmos> \<times> 'a) set"
  assume Aa3: "finite {na x | (na, x) \<in> F \<bullet> (na + n, x)}"
  have 
    "{na xa | (na, xa) \<in> (insert x F) \<bullet> (na + n, xa)} 
    = (insert (fst x + n, snd x) {na x | (na, x) \<in> F \<bullet> (na + n, x)})"
    by auto
  with Aa3
  show "finite {na xa | (na, xa) \<in> (insert x F) \<bullet> (na + n, xa)}" 
    by simp
qed

lemma stranslate_dom:
  "\<zdom> (stranslate s k) = { n | n \<in> \<zdom> s \<bullet> n + k }"
  by (auto simp add: stranslate_def eind_def)

lemma stranslate_seq_dom:
  assumes 
    a1: "s \<in> \<zseq> X" and 
    a2: "k \<in> \<int>"
  shows 
    "\<zdom> (stranslate s k) = (k + 1)..(k + \<zcard>s)"
proof (rule set_eqI)
  fix n 
  from a1 a2 show 
    "n \<in> \<zdom> (stranslate s k) \<Leftrightarrow> n \<in> (k + 1)..(k + \<zcard>s)"
    apply (auto simp add: stranslate_dom seq_dom [OF a1])
    apply (witness "n - k")
    apply (auto)
    done
qed

lemma stranslate_ran_eq:
  "\<zran> (stranslate s n_d_0) = \<zran> s"
  by (auto simp add: stranslate_def dsub_def eind_def)

lemma stranslate_seq_ran:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> (stranslate s n0) \<subseteq> X"
  apply (simp add: stranslate_ran_eq)
  apply (rule seq_ran [OF a1])
  done

lemma stranslate_zcard:
  "\<zcard>(stranslate s n_d_0) = \<zcard>s"
  apply (simp add: stranslate_image)
  apply (rule zcard_image)
  apply (rule inj_onI)
  apply auto
  done

lemma stranslate_index_bound:
  assumes a1: "t \<in> \<zseq> X" and a2: "(a \<mapsto> b) \<in> stranslate t n"
  shows "n + 1 \<le> a" "a \<le> \<zcard>t + n"
proof -
  from a2 have b0: "a \<in> \<zdom> (stranslate t n)" by auto
  from b0 show "n + 1 \<le> a"
    apply (simp add: stranslate_dom [of t n] seq_dom [OF a1]) 
    apply (auto)
    done
  from b0 show "a \<le> \<zcard>t + n"
    apply (simp add: stranslate_dom [of t n] seq_dom [OF a1]) 
    apply (auto)
    done
qed

lemma stranslate_appl:
  assumes 
    a1: "s \<in> \<zseq> X" and 
    a2: "n_d_0 + 1 \<le> n" and 
    a3: "n \<le> n_d_0 + \<zcard>s" and 
    a4: "n - n_d_0 \<in> \<int>"
  shows 
    "(n \<mapsto> (stranslate s n_d_0)\<cdot>n) \<in> (stranslate s n_d_0)"

proof -
  from a2 a3 a4 have b1: "n \<in> \<zdom> (stranslate s n_d_0)" 
    apply (simp add: stranslate_dom stranslate_zcard seq_dom [OF a1])
    apply (witness "n - n_d_0")
    apply (simp)
    done
  have b2: "functional (stranslate s n_d_0)" by (simp add: stranslate_functional [OF seq_functional [OF a1]])
  from b1 b2 show ?thesis by (auto simp add: functional_appl)
qed

lemma stranslate_appl2:
  assumes a1: "s \<in> \<zseq> X" and a2: "n \<in> \<int>" and a3: "1 \<le> n" and a4: "n \<le> \<zcard>s"
  shows "(n + n_d_0 \<mapsto> s\<cdot>n) \<in> (stranslate s n_d_0)"
  apply (simp add: stranslate_def)
  apply (rule seq_appl [OF a1 a2 a3 a4])
  done

lemma stranslate_beta1:
  assumes a1: "s \<in> \<zseq> X"
  shows "(stranslate s n)\<cdot>(i + n) = s\<cdot>i"
proof (cases "i \<in> \<zdom> s")
  assume b1: "i \<in> \<zdom> s"
  then show ?thesis
    apply (intro functional_beta)
    apply (rule stranslate_functional)
    apply (rule seq_functional [OF a1])
    apply (rule stranslate_appl2 [OF a1])
    apply (simp_all add: seq_dom [OF a1] Z_zNats_zInts_conv)
    done
next
  assume b1: "i \<notin> \<zdom> s"
  then have b2: "i + n \<notin> \<zdom> (stranslate s n)"
    by (simp add: Domain_iff stranslate_def)
  from b1 b2 show "(stranslate s n)\<cdot>(i + n) = s\<cdot>i"
    by (simp add: undef_beta)
qed

lemma stranslate_beta2:
  assumes a1: "s \<in> \<zseq> X"
  shows "(stranslate s n)\<cdot>i = s\<cdot>(i - n)"
  using stranslate_beta1 [OF a1, of "n" "i - n"]
  by (auto)

lemma stranslate_mem:
  assumes a1: "s \<in> \<zseq> X"
  shows "(x \<mapsto> y) \<in> stranslate s n_d_0 \<Leftrightarrow> (\<exists> r \<bullet> x = r + n_d_0 \<and> (r, y) \<in> s)"
  by (auto simp add: stranslate_def)

lemma stranslate_union:
  "stranslate (s \<union> t) n = ((stranslate s n) \<union> (stranslate t n))"
  by (auto simp add: stranslate_def)

lemma stranslate_stranslate:
  "stranslate (stranslate s m) n = stranslate s (m + n)"
  by (auto simp add: stranslate_def)

lemma stranslate_zero:
  "stranslate s 0 = s"
  by (auto simp add: stranslate_def)


lemma stranslate_inj:
  "stranslate s n = stranslate s' n \<Leftrightarrow> s = s'"  
  apply (simp add: stranslate_def)
  apply (simp add: set_eq_def)
  apply auto
proof-
  fix a b
  assume Aa1: "\<forall> a b \<bullet>
           (\<exists> na \<bullet> a = na + n \<and> (na \<mapsto> b) \<in> s) \<Leftrightarrow>
           (\<exists> na \<bullet> a = na + n \<and> (na \<mapsto> b) \<in> s')"
  assume Aa2: "(a \<mapsto> b) \<in> s"
  with Aa1 [rule_format, where ?a = "a + n" and ?b = "b"]
  show "(a \<mapsto> b) \<in> s'"
  by auto
next
  fix a b
  assume Aa1: "\<forall> a b \<bullet>
           (\<exists> na \<bullet> a = na + n \<and> (na \<mapsto> b) \<in> s) \<Leftrightarrow>
           (\<exists> na \<bullet> a = na + n \<and> (na \<mapsto> b) \<in> s')"
  assume Aa2: "(a \<mapsto> b) \<in> s'"
  with Aa1 [rule_format, where ?a = "a + n" and ?b = "b"] 
  show "(a \<mapsto> b) \<in> s"
  by auto
qed


section {* Single element insertion *}

text
{*

We can construct sequences by iteratively inserting a single element into a 
previously formed sequence.  
We begin by creating a sequence containing a single element by inserting that 
element into the empty sequence.

*}

definition
  sinsert :: "['a, 'a seqT] \<rightarrow> 'a seqT"
where
  sinsert_def : "sinsert x s \<defs> {(1 \<mapsto> x)} \<oplus> (stranslate s 1)"

syntax (xsymbols)
  "_Z_Sequence\<ZZ>extseq" :: "args \<rightarrow> logic" ("\<lang>_\<rang>")

translations
  "\<lang>x, xs\<rang>"\<rightleftharpoons> "CONST Z_Sequence.sinsert x \<lang>xs\<rang>"
  "\<lang>x\<rang>"\<rightleftharpoons> "CONST Z_Sequence.sinsert x \<sempty>"


lemma sunit_conv:
  "\<lang>x\<rang> = {(1 \<mapsto> x)}"
  apply (simp add: sinsert_def stranslate_sempty)
  apply (simp add: sempty_def rel_oride_def dsub_def Domain_iff eind_def)
  done

lemma stranslate_sunit: 
  "stranslate \<lang>x\<rang> n = {(n + 1 \<mapsto> x)}"
proof - 
  show "stranslate \<lang>x\<rang> n = {(n + 1 \<mapsto> x)}"
    by (simp add: sunit_conv stranslate_def eind_def)
qed

lemma sinsert_redef:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "sinsert x s = insert (1 \<mapsto> x) (stranslate s 1)"
proof 
  from a1 a2 show "sinsert x s \<subseteq> insert (1 \<mapsto> x) (stranslate s 1)"
    by (auto simp add: sinsert_def rel_oride_def dsub_def Domain_iff stranslate_def)
  from a1 a2 seq_dom [OF a1] stranslate_seq_dom [OF a1, of 1] show 
    "insert (1 \<mapsto> x) (stranslate s 1) \<subseteq> sinsert x s"
    by (simp add: sinsert_def rel_oride_def dsub_def Domain_iff)
qed


lemma sinsert_functional:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "functional (sinsert x s)"
  apply (insert a1 a2 stranslate_functional [OF seq_functional [OF a1], of "1"])
  apply (simp add: sinsert_def)
  apply (mauto(fspace))
  apply (simp add: stranslate_seq_dom [OF a1] dsub_def eind_def)
  apply (mauto(fspace) mintro!: fin_pfunI)
  done

lemma sinsert_redef2:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "sinsert x s = {(1 \<mapsto> x)} \<union> (stranslate s 1)"
  by (simp add: sinsert_redef [OF a1 a2])
  
lemma sinsert_dom:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "\<zdom> (sinsert x s) = (1..(\<zcard>s + 1))"
proof -
  have b1: "\<zdom> s = (1..\<zcard>s)" by (simp add: seq_dom [OF a1])
  also have b2: "\<zdom> (stranslate s 1) = 2..(1 + \<zcard>s)"
    by (auto simp add: stranslate_seq_dom [OF a1])
  from b1 b2 zcard_range [of s] show ?thesis
    apply (auto simp add: sinsert_def Z_rel_oride_dom_dist Z_zNats_zInts_conv fin_pfun_simp linorder_not_le)
    apply (simp add: int_of_norm)
    done
qed

lemma sinsert_ran:
  assumes 
    a1: "s \<in> \<zseq> X" and 
    a2: "x \<in> X"
  shows 
    "\<zran> (sinsert x s) \<subseteq> X"
proof -
  from seq_ran [OF a1] a2 show 
    ?thesis
    by (auto simp add: sinsert_def rel_oride_def stranslate_def dsub_def dres_def eind_def)
qed

lemma sinsert_closed:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "sinsert x s \<in> \<zseq> X"
proof (rule seqIa [where ?n = "\<zcard>s + 1"], simp)
  from sinsert_functional [OF a1 a2] have functional: "functional (sinsert x s)" by this
  from sinsert_dom [OF a1 a2] have dom: "\<zdom> (sinsert x s) = (1..(\<zcard>s + 1))"
    by (auto)
  have range: "\<zran> (sinsert x s) \<subseteq> X" by (intro sinsert_ran [OF a1 a2])
  from functional dom range show "sinsert x s \<in> 1..(\<zcard>s + 1) \<ztfun> X" by (mauto(fspace))
qed

lemma sinsert_zcard:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "\<zcard>(sinsert x s) = \<zcard>s + 1"
proof -
  from sinsert_closed [OF a1 a2] have b1: "sinsert x s \<in> \<zseq> X" by this
  have 
    b2: "\<zcard>(sinsert x s) 
        = \<zcard>(\<zdom> (sinsert x s))" by (auto simp add: seq_zcard_dom [OF b1])
  from sinsert_dom [OF a1 a2] have 
    b3: "\<zdom> (sinsert x s) = 1..(\<zcard>s + 1)" by (auto)
  from b2 b3 show ?thesis by (auto simp add: zint_range_zcard_from_1)
qed

lemma sinsert_seq1:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "sinsert x s \<in> \<zseq>\<subone> X"
  apply (rule seq1I)
  apply (rule sinsert_closed [OF a1 a2])
  apply (simp add: 
            zcard_zero [symmetric, OF sinsert_closed [OF a1 a2]] 
            sinsert_zcard [OF a1 a2] zNats_zcard nat_of_norm)
  done

lemma sunit_seq:
  assumes a1: "x \<in> X"
  shows "\<lang>x\<rang> \<in> \<zseq> X"
  by (simp add: sinsert_closed [OF sempty_seq a1])

lemma Z_sunit_ran:
  assumes a1: "x \<in> X"
  shows "\<zran> \<lang>x\<rang> = {x}"
  apply (simp add: sinsert_def stranslate_sempty)
  apply (simp add: rel_oride_rid sempty_def)
  done

lemma sunit_zcard:
  assumes a1: "x \<in> X"
  shows "\<zcard>\<lang>x\<rang> = 1"
  apply (simp add: sinsert_def stranslate_sempty)
  apply (simp add: sempty_def rel_oride_rid)
  done

lemma sunit_seq1:
  assumes a1: "x \<in> X"
  shows "\<lang>x\<rang> \<in> \<zseq>\<subone> X"
  apply (rule seq1I [OF sunit_seq [OF a1]])
  apply (simp add: sinsert_def stranslate_sempty)
  apply (simp add: sempty_def rel_oride_rid)
  done

lemma sinsert_mem:
  assumes a1: "xs \<in> \<zseq> X" and a2: "x \<in> X"
  shows "(a \<mapsto> b) \<in> (sinsert x xs) \<Leftrightarrow> (a = 1 \<and> b = x) \<or> (a \<mapsto> b) \<in> stranslate xs 1"
  by (auto simp add: sinsert_redef [OF a1 a2])

lemma sinsert_appl:
  assumes 
    a1: "s \<in> \<zseq> X" and
    a2: "x \<in> X" and 
    a3: "n \<in> \<int>" and 
    a4: "1 \<le> n" and a5: "n \<le> \<zcard>s"
  shows "(n + 1 \<mapsto> s\<cdot>n) \<in> sinsert x s"
  using a4 a5
  apply (simp add: sinsert_redef [OF a1 a2] stranslate_def)
  apply (rule seq_appl [OF a1 a3 a4 a5])
  done

lemma sinsert_appl_first:
  assumes 
    a1: "s \<in> \<zseq> X" and 
    a2: "x \<in> X"
  shows 
    "(1 \<mapsto> x) \<in> sinsert x s"
  by (simp add: sinsert_redef [OF a1 a2] stranslate_def)

lemma sinsert_appl_back:
  assumes 
    a1: "s \<in> \<zseq> X" and
    a2: "x \<in> X" and 
    a3: "n \<in> \<int>" and 
    a4: "2 \<le> n" and 
    a5: "n \<le> \<zcard>s + 1"
  shows 
    "(n \<mapsto> s\<cdot>(n - 1)) \<in> sinsert x s"
  using a3 a4 a5
  apply (simp add: sinsert_redef [OF a1 a2] stranslate_def)
  apply (witness "n - 1")
  apply simp
  apply (intro seq_appl [OF a1])
  apply simp_all
  done

lemma sinsert_beta_first:
  assumes 
    a1: "s \<in> \<zseq> X" and 
    a2: "x \<in> X"
  shows 
    "(sinsert x s)\<cdot>1 = x"
  using sinsert_functional [OF a1 a2]
  by (auto simp add: sinsert_redef [OF a1 a2] insert_beta)

lemma sinsert_beta_back:  
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X" and a3: "n \<noteq> 0"
  shows "(sinsert x s)\<cdot>(n + 1) = s\<cdot>n"
  using a3 sinsert_functional [OF a1 a2]
  by (auto simp add: sinsert_redef [OF a1 a2] insert_beta stranslate_beta1 [OF a1])
  
lemma sinsert_beta:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "(sinsert x s)\<cdot>n = \<if> n = 1 \<then> x \<else> s\<cdot>(n - 1) \<fi>"
  using sinsert_functional [OF a1 a2]
  by (simp add: sinsert_redef [OF a1 a2] insert_beta stranslate_beta2 [OF a1])

lemma sempty_noteq_sinsert:
  assumes 
    a1: "s \<in> \<zseq> X" and
    a2: "x \<in> X" 
  shows "\<sempty> \<noteq> sinsert x s" and "sinsert x s \<noteq> \<sempty>"
proof -
  have "0 \<le> \<zcard>s" by (auto simp add: zcard_def)
  then have 
    "\<zcard>\<sempty> \<noteq> \<zcard>(sinsert x s)"
    by (simp add: sempty_def sinsert_zcard [OF a1 a2])
  then show 
    "\<sempty> \<noteq> sinsert x s" "sinsert x s \<noteq> \<sempty>"
    by auto
qed

lemma sinsert_noteq:
  assumes a1: "s \<in> \<zseq> X" and a2: "a \<in> X"
  shows "sinsert a s \<noteq> s"
proof -
  have "\<zcard>(sinsert a s) \<noteq> \<zcard>s"  
    by (simp add: sinsert_zcard [OF a1 a2]) 
  then show ?thesis by auto
qed


lemma insert_inj:
  assumes a1: "a \<notin> B" and a2: "a \<notin> C"
  shows "insert a B = insert a C \<turnstile> B = C"
proof -
  assume b0: "insert a B = insert a C"
  from a1 have "\<forall> b \<bullet> b \<in> B \<Rightarrow> b \<noteq> a \<and> b \<in> insert a B" by auto
  with b0 have "\<forall> b \<bullet> b \<in> B \<Rightarrow> b \<noteq> a \<and> b \<in> insert a C" by auto
  then have b1: "\<forall> b \<bullet> b \<in> B \<Rightarrow> b \<in> C" by auto
  from a2 have "\<forall> c \<bullet> c \<in> C \<Rightarrow> c \<noteq> a \<and> c \<in> insert a C" by auto
  with b0 have "\<forall> c \<bullet> c \<in> C \<Rightarrow> c \<noteq> a \<and> c \<in> insert a B" by auto
  then have b2: "\<forall> c \<bullet> c \<in> C \<Rightarrow> c \<in> B" by auto
  from b1 b2 show "B = C" by auto
qed

lemma sinsert_inj:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X" 
  and a3: "t \<in> \<zseq> X" and a4: "y \<in> X"
  shows "sinsert x s = sinsert y t \<Leftrightarrow> x = y \<and> s = t"
  apply (msafe(inference))
  apply (simp_all)
proof -
  assume b1: "sinsert x s = sinsert y t"
  from b1 have "(sinsert x s)\<cdot>1 = (sinsert y t)\<cdot>1"
    by (simp)
  with a1 a2 a3 a4 show b2: "x = y"
    by (simp add: sinsert_beta_first)
  show "s = t"
  proof (rule functional_eqI [OF seq_functional [OF a1] seq_functional [OF a3]])
    from b1 have "\<zcard>(sinsert x s) = \<zcard>(sinsert y t)"
      by (simp)
    with b2 sinsert_zcard [OF a1 a2] sinsert_zcard [OF a3 a4]
    have "\<zcard>s = \<zcard>t"
      by (auto)
    with seq_dom [OF a1] seq_dom [OF a3] show "\<zdom> s = \<zdom> t"
      by (simp)
    fix n assume c1: "n \<in> \<zdom> s"
    with seq_dom [OF a1] have "n \<noteq> 0"
      by (auto)
    with b1 sinsert_beta [OF a1 a2, of "n + 1"] sinsert_beta [OF a3 a4, of "n + 1"]
    show "s\<cdot>n = t\<cdot>n"
      by (simp)
  qed
qed

text {*

Sequence concatination is defined using the @{text "\<oplus>"} operator to avoid the 
requirement that the inputs be Sequences.  The Spivey definition is included in the 
@{text "sconcat_redef"} lemma.

*}

definition
  sconcat :: "['a seqT, 'a seqT] \<rightarrow> 'a seqT"
where
  sconcat_def : "sconcat s t \<defs> s \<oplus> stranslate t (\<zcard>s)"

notation (xsymbols)
  sconcat (infixl "\<zcat>" 100)

lemma sconcat_redef:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "s\<zcat>t = s \<union> stranslate t (\<zcard>s)"
proof -
  have b1: "disjoint (\<zdom> s) (\<zdom> (stranslate t (\<zcard>s)))"
    by (auto simp add: seq_dom [OF a1] stranslate_seq_dom [OF a2 zInts_zcard] disjoint_def)
  have b2: "s \<oplus> stranslate t (\<zcard>s) = s \<union> stranslate t (\<zcard>s)"
    by (simp add: Z_rel_oride_disj [OF b1])
  from b2 show ?thesis
    by (simp add: sconcat_def)
qed


lemma Z_sconcat_redef [rule_format]:
  "\<lbrakk> s \<in> \<zseq> X; t \<in> \<zseq> X \<rbrakk> \<turnstile> s\<zcat>t \<defs> s \<union> {n | n \<in> \<zdom> t \<bullet> n + \<zcard>s \<zmapsto> t\<cdot>n}"
  apply (rule eq_reflection)
  apply (auto simp add: sconcat_redef stranslate_def seq_dom)
  apply (simp add: seq_beta [THEN sym])
  apply (simp_all add: seq_index_bound)
  apply (simp add: seq_appl)
  done

lemma Z_sconcat_sempty:
  assumes a1: "s \<in> \<zseq> X"
  shows 
    Z_sconcat_semptyl: "\<sempty>\<zcat>s = s" and 
    Z_sconcat_semptyr: "s\<zcat>\<sempty> = s"
  apply (simp_all add: sempty_def sconcat_def stranslate_def del: split_eta_SetCompr2)
  apply (simp_all add: rel_oride_lid rel_oride_rid eind_def)
  done

lemma sconcat_functional:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "functional (s\<zcat>t)"
proof -
  from seq_functional [OF a1] stranslate_functional [OF seq_functional [OF a2]] show ?thesis
    apply (simp add: sconcat_def stranslate_def)
    apply (mauto(fspace))
    done
qed
  

lemma sconcat_dom:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "\<zdom> (s\<zcat>t) = 1..(\<zcard>s + \<zcard>t)"
proof -
  have b1: "\<zdom> s = (1..\<zcard>s)"
    by (simp add: seq_dom [OF a1])
  have b2: "\<zdom> (stranslate t (\<zcard>s)) = (\<zcard>s + 1)..(\<zcard>s + \<zcard>t)"
    by (simp add: stranslate_seq_dom [OF a2 zInts_zcard])
  from b1 b2 show ?thesis
    by (auto simp add: 
          sconcat_def Z_rel_oride_dom_dist set_eq_def int_of_norm zInts_zcard int_of_zcard)
qed

lemma sconcat_ran:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "\<zran> (s\<zcat>t) \<subseteq> X"
  apply (insert seq_ran [OF a1] seq_ran [OF a2])
  apply (simp add: sconcat_def stranslate_def)
  apply (mstep(fspace))
  apply (rule rel_oride_ran_dist)
  apply (auto simp add: dsub_def eind_def)
  done


lemma Z_sconcat_ran_union:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "\<zran> (s\<zcat>t) = (\<zran> s) \<union> (\<zran> t)"
proof -
  have "(\<zran> s) \<union> (\<zran> t) = (\<zran> s) \<union> (\<zran> (stranslate t (\<zcard>s)))"
    by (simp add: stranslate_ran_eq)
  also have "\<dots> = \<zran> (s \<union> (stranslate t (\<zcard>s)))"
    by (simp add: Z_rel_union_ran [THEN sym])
  also have "\<dots> = \<zran> (s\<zcat>t)"
    by (simp add: sconcat_redef [OF a1 a2])
  finally have "(\<zran> s) \<union> (\<zran> t) = \<zran> (s\<zcat>t)" by this
  then show ?thesis by simp
qed

lemma sconcat_closed:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "(s\<zcat>t) \<in> \<zseq> X"
proof (rule seqIa [where ?n = "\<zcard>s + \<zcard>t"], simp)
  from sconcat_functional [OF a1 a2] have functional: "functional (s\<zcat>t)" by this
  from sconcat_dom [OF a1 a2] have dom: "\<zdom> (s\<zcat>t) = 1..(\<zcard>s + \<zcard>t)"
    by (auto)
  have 
    range: "\<zran> (s\<zcat>t) \<subseteq> X" 
    by (rule sconcat_ran [OF a1 a2])
  from functional dom range show 
    "s\<zcat>t \<in> 1..(\<zcard>s + \<zcard>t) \<ztfun> X"
    by ((mauto(fspace)))
qed

lemma Z_sconcat_zcard:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "\<zcard>(s\<zcat>t) = \<zcard>s + \<zcard>t"
proof -
  from sconcat_closed [OF a1 a2] have b1: "s\<zcat>t \<in> \<zseq> X"
    by (auto)
  have b2: "\<zcard>(s\<zcat>t) = \<zcard>(\<zdom> (s\<zcat>t)) "
    by (auto simp add: seq_zcard_dom [OF b1])
  from sconcat_dom [OF a1 a2] have 
    b3: "\<zdom> (s\<zcat>t) = 1..(\<zcard>s + \<zcard>t)"
    by (auto)
  from b2 b3 show ?thesis
    by (auto simp add: zint_range_zcard_from_1)
qed

lemma sconcat_index_bound:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X" and a3: "(n \<mapsto> x) \<in> s\<zcat>t"
  shows "1 \<le> n" and "n \<le> \<zcard>s + \<zcard>t"
proof -
  from a3 have b0: "n \<in> \<zdom> (s\<zcat>t)" by (auto simp add: Domain_def)
  from b0 sconcat_dom [OF a1 a2] show "1 \<le> n" "n \<le> \<zcard>s + \<zcard>t" by auto
qed

lemma sconcat_sunit_insert_end:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "s\<zcat>\<lang>x\<rang> = insert (\<zcard>s + 1 \<mapsto> x) s"
  by (simp add: sconcat_redef [OF a1 sunit_seq [OF a2]] stranslate_sunit)
 
lemma sinsert_sconcat:
  assumes a1: "xs \<in> \<zseq> X" and a2: "x \<in> X"
  shows "(sinsert x xs) = \<lang>x\<rang>\<zcat>xs"
  apply (simp add: sconcat_def sinsert_def stranslate_sempty)
  apply (simp add: sempty_def rel_oride_rid)
  done

lemma sconcat_sunit_insert_front:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "\<lang>x\<rang>\<zcat>s = insert (1 \<mapsto> x) (stranslate s 1)"
proof -
  have "\<lang>x\<rang>\<zcat>s = sinsert x s"
    apply (rule sinsert_sconcat [THEN sym]) 
    apply (rule a1, rule a2)
    done
  also have "\<dots> = insert (1 \<mapsto> x) (stranslate s 1)"
    by (simp add: sinsert_redef [OF a1 a2])
  finally show ?thesis by this
qed


lemma Z_sconcat_assoc:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X" and a3: "u \<in> \<zseq> X"
  shows "(s\<zcat>t)\<zcat>u = s\<zcat>(t\<zcat>u)"
proof -
  have b1: "s\<zcat>t \<in> \<zseq> X" by (simp add: sconcat_closed [OF a1 a2])
  have b2: "s\<zcat>t = s \<union> stranslate t (\<zcard>s)"
    by (simp add: sconcat_redef [OF a1 a2])
  from b1 have b3: "(s\<zcat>t)\<zcat>u = (s\<zcat>t) \<union> stranslate u (\<zcard>s + \<zcard>t)"
    by (simp add: sconcat_redef [OF b1 a3] Z_sconcat_zcard [OF a1 a2])
  from b2 b3 have b4: "(s\<zcat>t)\<zcat>u = 
                       s \<union> stranslate t (\<zcard>s) \<union> stranslate u (\<zcard>s + \<zcard>t)"
    by (auto)
  have c2: "t\<zcat>u = t \<union> stranslate u (\<zcard>t)"
    by (simp add: sconcat_redef [OF a2 a3])
  have c3: "s\<zcat>(t\<zcat>u) = s \<union> stranslate (t\<zcat>u) (\<zcard>s)"
    by (simp add: sconcat_redef [OF a1 sconcat_closed [OF a2 a3]])
  from c2 c3 have c4: "s\<zcat>(t\<zcat>u) =
                       s \<union> stranslate (t \<union> stranslate u (\<zcard>t)) (\<zcard>s)"
    by (auto)
  show ?thesis
    apply (simp add: b4 c4)
    apply (auto simp add: stranslate_def)
    done
qed

lemma sinsert_sconcat_assoc:
  assumes a1: "x \<in> X" and a2: "s \<in> \<zseq> X" and a3: "t \<in> \<zseq> X"
  shows "(sinsert x s)\<zcat>t = sinsert x (s\<zcat>t)"
proof -
  have 
    "(sinsert x s)\<zcat>t
    = (\<lang>x\<rang>\<zcat>s)\<zcat>t"
    by (simp add: sinsert_sconcat [OF a2 a1])
  also have "\<dots> 
    = \<lang>x\<rang>\<zcat>(s\<zcat>t)"
    by (rule Z_sconcat_assoc [OF sinsert_closed [OF sempty_seq a1] a2 a3])
  also have "\<dots>
    = sinsert x (s\<zcat>t)"
    apply (rule sinsert_sconcat [THEN sym])
    apply (rule sconcat_closed [OF a2 a3])
    apply (rule a1)
    done
  finally show 
    "(sinsert x s)\<zcat>t = sinsert x (s\<zcat>t)" 
    by this
qed

lemma sconcat_mem:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "(a \<mapsto> b) \<in> s\<zcat>t \<Leftrightarrow> (a, b) \<in> s \<or> (a, b) \<in> stranslate t (\<zcard>s)"
  by (auto simp add: sconcat_redef [OF a1 a2])

lemma sconcat_applL:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X" and a3: "n \<in> \<int>" and a4: "1 \<le> n" and a5: "n \<le> \<zcard>s"
  shows "(n \<mapsto> s\<cdot>n) \<in> s\<zcat>t"
proof -
  have b0: "functional s" by (rule seq_functional [OF a1])
  from a3 a4 a5 seq_dom [OF a1] have b1: "n \<in> \<zdom> s" by auto
  from b0 b1 show ?thesis 
    apply (simp add: sconcat_redef [OF a1 a2])
    apply (auto dest: functional_appl)
    done
qed  

lemma sconcat_applR:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X" and a3: "n \<in> \<int>" and a4: "1 \<le> n" and a5: "n \<le> \<zcard>t"
  shows "(n + \<zcard>s \<mapsto> t\<cdot>n) \<in> s\<zcat>t"
proof -
  have "(n + \<zcard>s, t\<cdot>n) \<in> stranslate t (\<zcard>s)"
    by (rule stranslate_appl2 [OF a2 a3 a4 a5])
  then show ?thesis
    by (auto simp add: sconcat_redef [OF a1 a2])
qed

lemma sconcat_betaL:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X" and a3: "n \<in> \<int>" and a4: "1 \<le> n" and a5: "n \<le> \<zcard>s"
  shows "(s\<zcat>t)\<cdot>n = s\<cdot>n"
proof -
  have b0: "(n \<mapsto> s\<cdot>n) \<in> s\<zcat>t" by (rule sconcat_applL [OF a1 a2 a3 a4 a5])
  have b1: "functional (s\<zcat>t)" by (intro sconcat_functional [of _ X] a1 a2)
  from b0 b1 show "(s\<zcat>t)\<cdot>n = s\<cdot>n"
    by (auto dest: functional_beta)
qed

lemma sconcat_betaR:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X" and a3: "n \<in> \<int>" and a4: "1 \<le> n" and a5: "n \<le> \<zcard>t"
  shows "(s\<zcat>t)\<cdot>(n + \<zcard>s) = t\<cdot>n"
proof -
  have b0: "(n + \<zcard>s \<mapsto> t\<cdot>n) \<in> s\<zcat>t" 
    by (rule sconcat_applR [OF a1 a2 a3 a4 a5])
  from sconcat_functional [OF a1 a2] 
  have b1: "functional (s\<zcat>t)" 
    by this
  from b0 b1 show "(s\<zcat>t)\<cdot>(n + \<zcard>s) = t\<cdot>n"
    by (auto dest: functional_beta)
qed

lemma sconcat_betaR2:
  assumes 
    a1: "s \<in> \<zseq> X" and 
    a2: "t \<in> \<zseq> X" and 
    a3: "n \<in> \<int>" and 
    a4: "\<zcard>s + 1 \<le> n" and 
    a5: "n \<le> \<zcard>s + \<zcard>t"
  shows 
    "(s\<zcat>t)\<cdot>n = t\<cdot>(n - \<zcard>s)"
  using sconcat_betaR [OF a1 a2, of "n - \<zcard>s"] a3 a4 a5
  by (simp add: zInts_zcard)


section {* Case and Induction rules *}

text 
{*

We set up case and induction theorems for sequences.  The 
@{text "seq_exhaust"} theorem is much easier to prove after the definition of 
@{text "\<zhead>"} and @{text "\<ztail>"} however, 
it is proved here as a more natural place in the development of the theory.

*}

lemma seq_exhaust:
  assumes a1: "s \<in> \<zseq> X"
  shows "(\<exists> x xs | xs \<in> \<zseq> X \<and> x \<in> X \<bullet> s = (sinsert x xs)) \<or> (s = \<sempty>)"
proof (rule disjCI)
  assume a2: "s \<noteq> \<sempty>"
  show "(\<exists> x xs | xs \<in> \<zseq> X \<and> x \<in> X \<bullet> s = (sinsert x xs))"
    apply (witness "s\<cdot>1")
    apply (witness "stranslate ({1} \<zdsub> s) -1")
    apply (msafe(inference))
  proof -
    from a2 have c1: "1 \<in> \<zdom> s"
      by (auto simp add: 
            seq_dom [OF a1] zcard_zero [OF a1, symmetric] int_of_norm zInts_zcard int_of_zcard)
    from card_Suc_Diff1 [OF seq_finite_dom [OF a1] c1, symmetric]
    have c2: "\<zcard>(\<zdom> ({1} \<zdsub> s)) = \<zcard>(\<zdom> s) - 1"
      by (auto simp add: dsub_dom nat_of_norm zNats_zcard nat_of_zcard)
    then have c3: "\<zcard>({1} \<zdsub> s) = \<zcard>s - 1"
      by (simp add: 
            seq_zcard_dom [OF a1] fun_zcard_dom [OF dsub_functional, OF seq_functional [OF a1]])
{ from a1 c1 show "s\<cdot>1 \<in> X"
      by (rule seq_in_ran)
  next
    show "stranslate ({1} \<zdsub> s) -1 \<in> \<zseq> X"
    proof ((mauto(fspace)))
      show "functional (stranslate ({1} \<zdsub> s) -1)"
        apply (rule stranslate_functional)
        apply (rule dsub_functional)
        apply (rule seq_functional [OF a1])
        done
      show "\<zdom> (stranslate ({1} \<zdsub> s) -1) = (1..\<zcard>(stranslate ({1} \<zdsub> s) -1))"
      proof (rule set_eqI)
        fix x
        show "x \<in> \<zdom> (stranslate ({1} \<zdsub> s) -1) \<Leftrightarrow> x \<in> (1..\<zcard>(stranslate ({1} \<zdsub> s) -1))"
          apply (simp add: dsub_dom stranslate_dom seq_dom [OF a1] stranslate_zcard c3)
          apply (auto)
          apply (simp add: int_of_norm)
          apply (witness "x + 1")
          apply (auto simp add: int_of_norm zInts_zcard int_of_zcard)
          done
      qed
      show "\<zran> (stranslate ({1} \<zdsub> s) -1) \<subseteq> X"
        apply (simp add: stranslate_ran_eq)
        apply (rule order_trans [OF _ seq_ran [OF a1]])
        apply (auto simp add: dsub_def)
        done
    qed
  next
    show "s = sinsert (s\<cdot>1) (stranslate ({1} \<zdsub> s) -1)"
    proof (auto simp add: sinsert_def stranslate_def dsub_def rel_oride_def eind_def)
      fix k x
      assume 
        d1: "(k \<mapsto> x) \<in> s" and 
        d2: "\<forall> n \<bullet> k = n + 1 \<Rightarrow> (\<forall> m \<bullet> n = m + -1 \<Rightarrow> m = 1 \<or> (m \<mapsto> x) \<notin> s)"
      from d2 [rule_format, of "k - 1" "k"] d1
      show d3: "k = 1"
        by (auto)
      with d1 show "x = s\<cdot>1"
        by (simp add: functional_beta [OF seq_functional [OF a1]])
    next
      from c1 show "(1 \<mapsto> s\<cdot>1) \<in> s"
        by (rule functional_appl [OF seq_functional [OF a1]])
    qed }
  qed
qed

theorem seq_cases:
  assumes 
    a1: "s \<in> \<zseq> X" and 
    a2: "s = \<sempty> \<turnstile> R" and 
    a3: "\<And> xs x \<bullet> \<lbrakk> xs \<in> \<zseq> X; x \<in> X; s = sinsert x xs \<rbrakk> \<turnstile> R"
  shows 
    "R"
  using seq_exhaust [OF a1] a2 a3
  by (auto)

theorem seq_induct_insert:
  assumes a1: "s \<in> \<zseq> X" and a2: "P \<sempty>" and a3: "(\<And>xs x \<bullet> \<lbrakk>xs \<in> \<zseq> X; x \<in> X; P xs\<rbrakk> \<turnstile> P (sinsert x xs))"
  shows "P s"
proof -
  have b1: "\<forall> c | c \<in> \<nat> \<bullet> (\<forall> s \<bullet> s \<in> \<zseq> X \<Rightarrow> \<zcard>s = c \<Rightarrow> P s)"
  proof (rule allI, rule impI)
    fix c
    assume c1: "c \<in> \<nat>"
    then show "(\<forall> s \<bullet> s \<in> \<zseq> X \<Rightarrow> \<zcard>s = c \<Rightarrow> P s)"
      apply (induct c set: zNats)
      apply (auto)
    proof -
      fix s'
      assume Ab1: "s' \<in> \<zseq> X" and Ab2: "\<zcard>s' = 0"
      with a2 show "P s'"
        by (simp add: zcard_zero)
    next
      fix n s'
      assume Ab1: "n \<in> \<nat>" and
        Ab2: "\<forall> s \<bullet> s \<in> \<zseq> X \<Rightarrow> \<zcard>s = n \<Rightarrow> P s" and 
        Ab3: "s' \<in> \<zseq> X" and
        Ab4: "\<zcard>s' = n + 1"
      show "P s'"
      proof (rule seq_cases [OF Ab3])
        assume "s' = \<sempty>"
        with Ab1 Ab4 show "P s'"
          by (auto simp add: zcard_zero Z_zNats_zInts_conv)
      next
        fix y t
        assume e1: "t \<in> \<zseq> X" and e2: "y \<in> X" and e3: "s' = sinsert y t"
        from Ab4 have e4: "\<zcard>t = n"
          by (simp add: e3 sinsert_zcard [OF e1 e2])
        show "P s'"
          apply (simp add: e3)
          apply (rule a3 [OF e1 e2])
          apply (rule Ab2 [rule_format])
          apply (simp_all add: e1 e4)
          done
      qed
    qed
  qed
  show "P s"
    apply (rule b1 [rule_format, of "\<zcard>s"])
    apply (auto simp add: a1)
    done
 qed

theorem seq_induct:
  assumes 
    a1: "s \<in> \<zseq> X" and a2: "P \<sempty>" and 
    a3: "(\<And>xs x \<bullet> \<lbrakk>xs \<in> \<zseq> X; x \<in> X; P xs\<rbrakk> \<turnstile> P (\<lang>x\<rang>\<zcat>xs))"
  shows "P s"
  apply (rule seq_induct_insert [of "s" "X" "P"])
  apply (rule a1)
  apply (rule a2)
  using a3 
  apply (auto simp add: sinsert_sconcat)
  done

theorem seq_sconcat_induct:
  assumes a1: "s \<in> \<zseq> X" and a2: "P \<sempty>" and a3: "\<And> x \<bullet> x \<in> X \<turnstile> P \<lang>x\<rang>"
  and a4: "\<And>s t \<bullet> \<lbrakk>s \<in> \<zseq> X; t \<in> \<zseq> X; P s; P t\<rbrakk> \<turnstile> P (s\<zcat>t)"
  shows "P s"
proof (induct "s" rule: seq_induct)
  show "s \<in> \<zseq> X" by (rule a1)
  show "P \<sempty>" by (rule a2)
next
  fix xs x
  assume b0: "xs \<in> \<zseq> X" and b1: "x \<in> X" and b2: "P xs"
  from b1 have b3: "P \<lang>x\<rang>" by (rule a3)
  from sunit_seq [OF b1] b0 b3 b2 show "P (\<lang>x\<rang>\<zcat>xs)" by (rule a4)
qed

section {* Sequence Recursion *}


definition
  seq_case :: "'a set \<rightarrow> ['b, ['a, 'a seqT] \<rightarrow> 'b] \<rightarrow> ('a seqT \<rightarrow> 'b)"
where
  seq_case_def : 
    "seq_case A b f s 
    \<defs> (\<mu> z | 
        (s = \<sempty> \<Rightarrow> z = b) \<and> 
        (\<forall> x t | x \<in> A \<and> t \<in> \<zseq> A \<bullet> s = sinsert x t \<Rightarrow> z = f x t))"

definition
  insertseq_rel :: "'a set \<rightarrow> ('a seqT \<leftrightarrow> 'a seqT)"
where
  insertseq_rel_def : "insertseq_rel A \<defs> ({s a | s \<in> \<zseq> A \<and> a \<in> A \<bullet> s \<mapsto> sinsert a s})"

lemma insertseq_relI [mintro!(fspace)] :
  "\<And> s \<bullet> \<lbrakk> s \<in> \<zseq> X; s' = sinsert a s; a \<in> X \<rbrakk> \<turnstile> (s, s') \<in> insertseq_rel X"
  by (auto simp add: insertseq_rel_def)

lemma insertseq_relE [melim!(fspace)]:
  assumes 
    a1: "(s \<mapsto> s') \<in> insertseq_rel A" "\<And> a \<bullet>  \<lbrakk> s \<in> \<zseq> A; a \<in> A; s' = sinsert a s\<rbrakk> \<turnstile> R"
  shows 
    "R"
  using a1
  by (auto simp add: insertseq_rel_def)
 

lemma insertseq_subset_measure:
  "insertseq_rel A \<subseteq> measure (\<olambda> x \<bullet> \<card>(\<zdom> x))"
  apply (auto simp add: measure_def inv_image_def)
  apply (elim insertseq_relE)
  apply (simp add: seq_dom sinsert_dom)
proof -
  fix s
  have "\<zcard>(1..\<zcard>s) < \<zcard>(1..(\<zcard>s + 1))"
    by (simp add: zint_range_zcard_from_1 zInts_zcard)
  then show "card (1..\<zcard>s) < card (1..(\<zcard>s + 1))"
    by (simp add: zcard_def of_nat_less_iff)
qed

theorem insertseq_rel_wellfounded:
  shows "wf (insertseq_rel A)"
  by (rule wf_subset [OF wf_measure insertseq_subset_measure])

definition
  seq_rec :: "'a set \<rightarrow> ['b, ['a, 'a seqT, 'b] \<rightarrow> 'b, 'a seqT] \<rightarrow> 'b"
where
  seq_rec_def: "seq_rec A b d \<defs> 
                  wfrec (insertseq_rel A) (\<olambda> f \<bullet> seq_case A b (\<olambda> a t \<bullet> d a t (f t)) )"

lemma seq_case_sempty:
  "seq_case A b f \<sempty> = b"
  apply (simp add: seq_case_def)
  apply (rule the_equality)
  apply auto
  apply (simp add: sempty_noteq_sinsert)
  done

lemma seq_case_sinsert:
  assumes 
    a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows 
    "seq_case X a f (sinsert x s) = f x s"
  apply (simp add: seq_case_def)
  apply (rule the_equality)
  using a1 a2
  apply (auto simp add: sempty_noteq_sinsert sinsert_inj)
  done
  

lemma seq_rec_unfold:
  "seq_rec A c d a = seq_case A c (\<olambda> aa t \<bullet> d aa t (cut (seq_rec A c d) (insertseq_rel A) a t)) a"
  by (simp add: seq_rec_def wfrec [OF insertseq_rel_wellfounded])

lemma seq_rec_sempty:
  "seq_rec A c h \<sempty> = c"
  apply (simp add: seq_rec_unfold)
  apply (simp add: seq_case_sempty)
  done

lemma seq_rec_cut:
  assumes 
    a1: "x \<in> A" and 
    a2: "s \<in> \<zseq> A"
  shows "cut (seq_rec A c h) (insertseq_rel A) (sinsert x s) s = seq_rec A c h s"
  apply (rule cut_apply)
  using insertseq_rel_def a1 a2
  apply (auto simp add: insertseq_rel_def)
  done


lemma seq_rec_sinsert:
  assumes 
    a1: "s \<in> \<zseq> A" and 
    a2: "x \<in> A"
  shows 
    "seq_rec A c h (sinsert x s) = h x s (seq_rec A c h s)"
proof -
  have "\<forall> x \<bullet> x \<in> A \<Rightarrow> seq_rec A c h (sinsert x s) = h x s (seq_rec A c h s)"
  proof (induct "s" rule: seq_induct_insert, rule a1, msafe(inference))
    fix x 
    assume 
      b0': "x \<in> A"
    have 
      b0: "\<sempty> \<in> \<zseq> A" 
      by (rule sempty_seq)
    show 
      "seq_rec A c h \<lang>x\<rang> = h x \<sempty> (seq_rec A c h \<sempty>)"
      apply (simp add: seq_rec_unfold)
      using b0 b0' a1 a2
      apply (simp add: seq_case_sempty seq_case_sinsert)
      apply (rule arg_cong [where ?f = "h x \<sempty>"])
      apply (simp add: seq_rec_cut seq_rec_sempty)
      done
  next
    fix x xs xa
    assume 
      b0: "xs \<in> \<zseq> A" and 
      b1: "xa \<in> A" and 
      b2: "\<forall> x \<bullet> x \<in> A \<Rightarrow> seq_rec A c h (sinsert x xs) = h x xs (seq_rec A c h xs)" and 
      b3: "x \<in> A"
    from b2 b3 have 
      b2': "seq_rec A c h (sinsert x xs) = h x xs (seq_rec A c h xs)" 
      by auto
    have 
      b3': "sinsert xa xs \<in> \<zseq> A" 
      by (rule sinsert_closed [OF b0 b1])
    show "seq_rec A c h (sinsert x (sinsert xa xs)) = h x (sinsert xa xs) (seq_rec A c h (sinsert xa xs))"
      apply (simp add: seq_rec_unfold)
      using a1 a2 b0 b1 b2 b3 b2' b3'
      apply (simp add: seq_case_sinsert)
      apply (rule arg_cong [where ?f = "h x (sinsert xa xs)"])
      apply (simp add: seq_rec_cut)
      done
  qed
  with a2 show 
    ?thesis 
    by auto
qed

section {* Head and Tail *}

text {*

For a non-empty sequence @{text "s"}:
@{text "\<zhead> s"} is the first element of @{text "s"}, and @{text "\<ztail> s"}
 contains every element except for the head.

*}

definition
  shead :: "'a seqT \<rightarrow> 'a"
where
  shead_def : "shead \<defs> (\<olambda> s \<bullet> s\<cdot>1)"

notation (xsymbols)
  shead ("\<zhead>")

definition
  stail :: "'a seqT \<rightarrow> 'a seqT"
where
  stail_def : "stail \<defs> (\<olambda> s \<bullet> {n | n \<in> 1..(\<zcard>s - 1) \<bullet> (n \<mapsto> s\<cdot>(n + 1))})"

notation (xsymbols)
  stail ("\<ztail>")

lemma stail_functional:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "functional (\<ztail> s)"
  apply (insert seq1_functional [OF a1])
  apply (auto intro!: functionalI elim!: functionalE)
  apply (simp add: stail_def)
  done

lemma stail_dom:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zdom> (\<ztail> s) = 1..(\<zcard>s - 1)"
  by (auto simp add: stail_def)

lemma stail_ran:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zran> (\<ztail> s) \<subseteq> X"
proof -
  have a1': "s \<in> \<zseq> X" by (intro seq1D [OF a1])
  have "\<zran> (\<ztail> s) \<subseteq> \<zran> s"
  proof (auto simp add: stail_def)
    fix n
    assume b0: "n \<in> \<int>" and b1: "1 \<le> n" and b2: "n \<le> \<zcard>s - 1"
    show "s\<cdot>(n + 1) \<in> \<zran> s"
      apply (simp add: Range_iff Domain_iff dsub_def)
      apply (witness "n + 1")
      apply (intro seq_appl [OF a1'])
      apply (insert b0 b1 b2)
      apply simp_all
      done
  qed
  also have "\<dots> \<subseteq> X" by (rule seq_ran [OF a1'])
  finally show ?thesis by this
qed

lemma shead_in_ran:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zhead> s \<in> X"
  apply (rule seq1E [OF a1])
  apply (simp add: shead_def)
  apply (rule seq_in_ran)
  apply (simp)
  apply (auto simp add: 
           seq_dom zcard_zero [symmetric] zNats_neq0_conv zNats_zcard 
           zInts_one_le_iff_zero_less zInts_zcard)
  done

lemma stail_closed:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<ztail> s \<in> \<zseq> X"
proof (rule seqIa [where ?n = "\<zcard>s - 1"])
  from a1 show "\<zcard>s - 1 \<in> \<nat>"
    apply (elim seq1E)
    apply (simp add:
             zcard_zero [symmetric] zInts_zcard zNats_neq0_conv 
             zNats_zcard zInts_one_le_iff_zero_less)
    done
  have functional: "functional (\<ztail> s)" by (rule stail_functional [OF a1])
  have dom: "\<zdom> (\<ztail> s) = 1..(\<zcard>s - 1)" by (rule stail_dom [OF a1])
  have ran: "\<zran> (\<ztail> s) \<subseteq> X" by (rule stail_ran [OF a1])
  from functional dom ran show "\<ztail> s \<in> 1..(\<zcard>s - 1) \<ztfun> X" by (mauto(fspace))
qed

lemma stail_zcard:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zcard>(\<ztail> s ) = \<zcard>s - 1"
  apply (simp add: seq_zcard_dom [OF stail_closed [OF a1]])
  apply (simp add: stail_dom [OF a1] zint_range_zcard_from_1 seq1_card_ge_1 [OF a1] zNats_zcard)
  done

lemma shead_sunit:
  assumes a1: "x \<in> X"
  shows "\<zhead> \<lang>x\<rang> = x"
  apply (simp add: shead_def sinsert_def stranslate_sempty)
  apply (simp add: sempty_def rel_oride_rid)
  apply (rule functional_beta)
  apply (auto intro!: functionalI)
  done

lemma stail_sunit:
  assumes a1: "x \<in> X"
  shows "\<ztail> \<lang>x\<rang> = \<sempty>"
  apply (auto simp add: stail_def sunit_zcard [OF a1])
  apply (simp_all add: sempty_def)
  done

lemma shead_sinsert:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "\<zhead> (sinsert x s) = x"
  apply (simp add: shead_def)
  apply (insert sinsert_beta_first [OF a1 a2])
  apply simp
  done

lemma stail_sinsert:  
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"  
  shows "\<ztail> (sinsert x s) = s"
  apply (simp add: stail_def)
  apply (simp add: sinsert_zcard [OF a1 a2])
proof (simp add: set_eq_def, msafe_no_assms(inference))
  fix a b
  assume b0: "b = (sinsert x s)\<cdot>(a + 1)" and b1: "a \<in> \<int>" and b2: "1 \<le> a" and b3: "a \<le> \<zcard>s"
  from b0 sinsert_beta [OF a1 a2] b2 have b4: "b = s\<cdot>a" by auto
  show "(a \<mapsto> b) \<in> s"
    apply (subst b4)
    apply (rule seq_appl [OF a1 b1 b2 b3])
    done
next
  fix a b
  assume b0: "(a, b) \<in> s"
  then have b1: "a \<in> \<zdom> s" by (auto)
  from seq_beta [OF a1 b0] have b2: "b = s\<cdot>a" by auto
  from b1 b2 show "b = (sinsert x s)\<cdot>(a + 1)" 
    by (simp add: sinsert_beta [OF a1 a2] seq_dom [OF a1])
  from b1 show "a \<in> \<int>" "1 \<le> a" "a \<le> \<zcard>s"
    by (simp_all add: seq_dom [OF a1])
qed

lemma shead_sconcat:
  assumes a1: "s \<in> \<zseq>\<subone> X" and a2: "t \<in> \<zseq> X"
  shows "\<zhead> (s\<zcat>t) = \<zhead> s"
proof -
  from seq1D [OF a1] have b1: "s \<in> \<zseq> X" and b2: "s \<noteq> \<sempty>" by auto
  from b1 b2 have b2': "0 < \<zcard>s" 
    by (auto simp add: zcard_zero [symmetric] zNats_neq0_conv [OF zNats_zcard])
  from seq_dom [OF b1] have b3: "\<zdom> s = (1..\<zcard>s)" by (auto)
  from b2' b3 show ?thesis
    apply (simp add: shead_def)
    apply (rule sconcat_betaL)
    apply (rule b1, rule a2)
    apply (auto simp add: zInts_one_le_iff_zero_less [OF zInts_zcard])
    done
qed

lemma shead_stail_reconstr:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<lang>\<zhead> s\<rang>\<zcat>(\<ztail> s) = s"
proof -
  from seq1D [OF a1] have a1': "s \<in> \<zseq> X" by auto
  have "s \<in> \<zseq>\<subone> X \<Rightarrow> \<lang>\<zhead> s\<rang>\<zcat>(\<ztail> s) = s"
  proof (cases "s" rule: seq_cases, rule a1')
    show "s = \<sempty> \<turnstile> s \<in> \<zseq>\<subone> X \<Rightarrow> \<lang>\<zhead> s\<rang>\<zcat>(\<ztail> s) = s"
      by (simp add: sempty_def seq1_nonempty)
    apply_end simp
  next
    apply_end simp
    apply_end (msafe(inference))
    fix xs x
    assume b0: "xs \<in> \<zseq> X" and b1: "x \<in> X" and b2: "sinsert x xs \<in> \<zseq>\<subone> X"
    have "\<lang>\<zhead> (sinsert x xs)\<rang>\<zcat>(\<ztail> (sinsert x xs)) = \<lang>x\<rang>\<zcat>\<ztail> ((sinsert x xs))"
      by (simp add: shead_sinsert [OF b0 b1])
    also have "\<dots> = \<lang>x\<rang>\<zcat>xs" by (simp add: stail_sinsert [OF b0 b1])
    also have "\<dots> = sinsert x xs" by (simp add: sinsert_sconcat [OF b0 b1])
    finally show "\<lang>\<zhead> (sinsert x xs)\<rang>\<zcat>(\<ztail> (sinsert x xs)) = sinsert x xs" 
      by auto
  qed
  with a1 show ?thesis by auto
qed

lemma Z_shead_stail_reconstr:
  assumes a1: "s \<in> \<zseq> X"
  shows "s \<noteq> \<sempty> \<Rightarrow> \<lang>\<zhead> s\<rang>\<zcat>(\<ztail> s) = s"
  apply (msafe(inference))
  apply (intro shead_stail_reconstr)
  using a1 
  apply (auto intro: seq1I)
  done

lemma stail_sconcat_unit:
  assumes a1: "s \<in> \<zseq>\<subone> X" and a2: "x \<in> X"
  shows "\<ztail> (s\<zcat>\<lang>x\<rang>) = (\<ztail> s)\<zcat>\<lang>x\<rang>"
proof -
  have "s \<in> \<zseq>\<subone> X \<Rightarrow> \<ztail> (s\<zcat>\<lang>x\<rang>) = (\<ztail> s)\<zcat>\<lang>x\<rang>"
  proof (cases "s" rule: seq_cases)
    from seq1D [OF a1] show "s \<in> \<zseq> X" by auto
    show "s = \<sempty> \<turnstile> s \<in> \<zseq>\<subone> X \<Rightarrow> \<ztail> (s\<zcat>\<lang>x\<rang>) = (\<ztail> s)\<zcat>\<lang>x\<rang>"
      by (simp add: sempty_def seq1_nonempty)
    apply_end simp
  next
    apply_end simp
    apply_end (msafe(inference))
    fix xs xa
    assume b0: "xs \<in> \<zseq> X" and b1: "xa \<in> X"
    from sunit_seq [OF a2] have a2': "\<lang>x\<rang> \<in> \<zseq> X" by auto
    from sunit_seq [OF b1] have b1': "\<lang>xa\<rang> \<in> \<zseq> X" by auto   
    have "\<ztail> (sinsert xa xs\<zcat>\<lang>x\<rang>) = \<ztail> ((\<lang>xa\<rang>\<zcat>xs)\<zcat>\<lang>x\<rang>)" 
      by (simp add: sinsert_sconcat [OF b0 b1])
    also have "\<dots> = \<ztail> (\<lang>xa\<rang>\<zcat>(xs\<zcat>\<lang>x\<rang>))" 
      by (simp add: Z_sconcat_assoc [OF b1' b0 a2'])
    also have "\<dots> = \<ztail> (sinsert xa (xs\<zcat>\<lang>x\<rang>))" 
      by (simp add: sinsert_sconcat [OF sconcat_closed [OF b0 a2'] b1])
    also have "\<dots> = xs\<zcat>\<lang>x\<rang>" 
      by (simp add: stail_sinsert [OF sconcat_closed [OF b0 a2'] b1])
    finally have b2: "\<ztail> ((sinsert xa xs)\<zcat>\<lang>x\<rang>) = xs\<zcat>\<lang>x\<rang>" 
      by auto
    have b3: "(\<ztail> (sinsert xa xs))\<zcat>\<lang>x\<rang> = xs\<zcat>\<lang>x\<rang>" 
      by (simp add: stail_sinsert [OF b0 b1])
    from b2 b3 show "\<ztail> ((sinsert xa xs)\<zcat>\<lang>x\<rang>) = (\<ztail> (sinsert xa xs))\<zcat>\<lang>x\<rang>" 
      by auto
  qed
  with a1 show ?thesis by auto
qed


lemma sunit_sconcat_stail:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "\<ztail> (\<lang>x\<rang>\<zcat>s) = s"
proof -
  have "\<ztail> (\<lang>x\<rang>\<zcat>s) = \<ztail> (sinsert x s)"
    by (simp add: sinsert_sconcat [OF a1 a2])
  then show "\<ztail> (\<lang>x\<rang>\<zcat>s) = s"
    by (simp add: stail_sinsert [OF a1 a2])
qed

lemma stail_sconcat:
  assumes a1: "s \<in> \<zseq>\<subone> X" and a2: "t \<in> \<zseq> X"
  shows "\<ztail> (s\<zcat>t) = (\<ztail> s)\<zcat>t"
proof (cases "s" rule: seq_cases)
  from a1 show "s \<in> \<zseq> X" 
    by (auto simp add: seq1_nonempty)
  assume c1 : "s = \<sempty>"
  from c1 have c2: "s \<notin> \<zseq>\<subone> X" 
    by (auto simp add: seq1_nonempty sempty_def)
  from a1 c2 show "\<ztail> (s\<zcat>t) = (\<ztail> s)\<zcat>t" 
    by (auto)
next
  apply_end simp
  fix xs x
  assume a3: "xs \<in> \<zseq> X" and a4: "x \<in> X"
  have "\<ztail> ((sinsert x xs)\<zcat>t) = \<ztail> (\<lang>x\<rang>\<zcat>xs\<zcat>t)"
    by (simp add: sinsert_sconcat [OF a3 a4])
  also have "\<dots> = \<ztail> (\<lang>x\<rang>\<zcat>(xs\<zcat>t))"
    by (simp add: Z_sconcat_assoc [OF sinsert_closed [OF sempty_seq a4] a3 a2])
  also have "\<dots> = xs\<zcat>t"
    by (simp add: sunit_sconcat_stail [OF sconcat_closed [OF a3 a2] a4])
  finally show "\<ztail> ((sinsert x xs)\<zcat>t) = (\<ztail> (sinsert x xs))\<zcat>t"
    by (simp add: stail_sinsert [OF a3 a4])
qed

      

section {* Front and Last *}

text
{*

@{text "\<zlast> s"} is the last element in the sequence and
@{text "\<zfront> s"} contains every element except for the last.

*}



definition
  slast :: "'a seqT \<rightarrow> 'a"
where
  slast_def: "slast \<defs> (\<olambda> s \<bullet> s\<cdot>(\<zcard>s))"

notation (xsymbols)
  slast ("\<zlast>")

definition
  sfront :: "'a seqT \<rightarrow> 'a seqT"
where
  sfront_def: "sfront \<defs> (\<olambda> s \<bullet> 1..(\<zcard>s - 1)\<zdres>s)"

notation (xsymbols)
  sfront ("\<zfront>")

lemma sfront_redef:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zfront> s = {\<zcard>s}\<zdsub>s"
  apply (simp add: sfront_def dres_def dsub_def zInts_zcard order_less_le)
  apply (mauto(wind) msplit: prod.splits)
  apply (mauto(inference))
  apply (auto 
           dest!: seq_index_bound [OF a1] 
           simp add: sfront_def dres_def dsub_def zInts_zcard order_less_le)
  done

lemma sfront_functional:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "functional (\<zfront> s)"
proof -
  from seq1D [OF a1] have a1': "s \<in> \<zseq> X" by simp
  with seq_functional [OF a1'] show ?thesis
    apply (simp add: sfront_def)
    apply (auto intro!: functionalI elim!: functionalE )
    apply (auto simp add: dres_def)
    done
qed

lemma sfront_dom:
  assumes 
    a1: "s \<in> \<zseq>\<subone> X"
  shows 
    "\<zdom> (\<zfront> s) = 1..(\<zcard>s - 1)"
proof -
  from a1 have b1: "s \<in> \<zseq> X"
    by (simp add: seq1_nonempty)
  have b2: "0 < \<zcard>s" 
    by (simp add: seq1_card_gr_0 [OF a1])
  then have b3: "\<zcard>s - 1 < \<zcard>s" 
    by (simp add: zInts_zcard int_of_norm)
  from b3 show ?thesis
    by (auto simp add: sfront_def seq_dom [OF b1] Z_dres_dom)
qed

lemma sfront_ran:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zran> (\<zfront> s) \<subseteq> X"
proof -
  have a1': "s \<in> \<zseq> X"
    by (intro seq1D [OF a1])
  have "\<zran> (\<zfront> s) \<subseteq> \<zran> s"
    by (auto simp add: sfront_def dres_def)
  also have "\<dots> \<subseteq> X" 
    by (rule seq_ran [OF a1'])
  finally show ?thesis by this
qed

lemma slast_in_ran:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zlast> s \<in> X"
  apply (unfold slast_def)
  apply (rule seq_in_ran [OF seq1_seq [OF a1]])
  apply (simp add: seq_dom [OF seq1_seq [OF a1]] seq1_card_ge_1 [OF a1] zInts_zcard)
  done

lemma sfront_closed:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zfront> s \<in> \<zseq> X"
proof (rule seqIa [where ?n = "\<zcard>s - 1"])
  from seq1_card_gr_0 [OF a1] show "\<zcard>s - 1 \<in> \<nat>"
    by (simp add: zNats_zcard nat_of_norm)
  from sfront_functional [OF a1] sfront_dom [OF a1] sfront_ran [OF a1]
  show "\<zfront> s \<in> 1..(\<zcard>s - 1) \<ztfun> X" 
    by (mauto(fspace))
qed

lemma sfront_zcard:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zcard>(\<zfront> s) = \<zcard>s - 1"
  apply (simp add: seq_zcard_dom [OF sfront_closed [OF a1]])
  apply (simp add: sfront_dom [OF a1] zint_range_zcard_from_1 zNats_zcard seq1_card_ge_1 [OF a1])
  done

lemma sfront_beta:
  assumes 
    a1: "s \<in> \<zseq>\<subone> X" and
    a2: "n \<in> \<int>" "1 \<le> n" "n \<le> \<zcard>s - 1"
  shows "(\<zfront> s)\<cdot>n = s\<cdot>n"
  apply (simp add: sfront_redef [OF seq1_seq [OF a1]])
  apply (rule dsub_beta)
  using a1 a2
  apply (auto)
  done

lemma sfront_sunit:
  assumes 
    a1: "x \<in> X"
  shows 
    "\<zfront> \<lang>x\<rang> = \<sempty>"
  apply (auto simp add: sfront_def dres_def sunit_zcard [OF a1])
  apply (simp_all add: sempty_def)
  done

lemma slast_sunit:
  assumes a1: "x \<in> X"
  shows "\<zlast> \<lang>x\<rang> = x"
  by (auto simp add: slast_def dres_def sunit_zcard [OF a1] sinsert_beta [OF sempty_seq a1])

lemma sfront_subset:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zfront> s \<subset> s"
proof (intro psubsetI)
  from a1 have b1: "s \<in> \<zseq> X" 
    by (simp add: seq1_nonempty)
  show "\<zfront> s \<subseteq> s"
    apply (simp add: sfront_def dres_def)
    apply (insert seq_dom [OF b1])
    apply (auto)
    done
next
  from sfront_zcard [OF a1] have "\<zcard>(\<zfront> s) \<noteq> \<zcard>s"
    by (simp)
  then show "\<zfront> s \<noteq> s"
    by (auto)
qed

lemma sfront_missing_element:
  assumes a1: "s \<in> \<zseq>\<subone> X" and a2: "(a \<mapsto> b) \<in> s" and a3: "(a \<mapsto> b) \<notin> \<zfront> s"
  shows "a = \<zcard>s" and "b = s\<cdot>(\<zcard>s)"
proof -
  from seq_index_bound [OF seq1_seq [OF a1] a2] a3 
  show b5: "a = \<zcard>s" 
    by (auto simp add: sfront_def dres_def zInts_zcard int_of_norm a2)
  from a2 b5 seq_functional [OF seq1_seq [OF a1]] show "b = s\<cdot>(\<zcard>s)"
    by (auto dest: functional_beta)
qed

lemma sfront_eq_elements:
  assumes 
    a1: "s \<in> \<zseq>\<subone> X" and 
    a2: "n \<in> \<int>" "1 \<le> n" "n \<le> \<zcard>s - 1"
  shows 
    "(\<zfront> s)\<cdot>n = s\<cdot>n"
  apply (rule functional_beta)
  apply (rule sfront_functional [OF a1])
  using a2
  apply (simp add: sfront_def dres_def)
  apply (rule functional_appl)
  apply (rule seq_functional [OF seq1_seq [OF a1]])
  apply (simp add: seq_dom [OF seq1_seq [OF a1]])
  done

lemma seq1_last_x_in_dom:
  assumes 
    a1: "s \<in> \<zseq>\<subone> X"
  shows 
    "\<zcard>s \<in> \<zdom> s"
  by (simp add: seq_dom [OF seq1_seq [OF a1]] zInts_zcard seq1_card_ge_1 [OF a1])

lemma sfront_sinsert:
  assumes a1: "s \<in> \<zseq>\<subone> X" and a2: "x \<in> X"
  shows "\<zfront> (sinsert x s) = sinsert x (\<zfront> s)"
  using a2 sinsert_closed [OF seq1_seq [OF a1] a2] seq1_seq [OF a1] sfront_closed [OF a1] seq1_card_gr_0 [OF a1]
  apply (simp add: sfront_redef dsub_def sinsert_zcard)
  apply (step)
  apply (auto simp add: sinsert_redef2 stranslate_def)
  done

lemma slast_sinsert:
  assumes a1: "s \<in> \<zseq>\<subone> X" and a2: "x \<in> X"
  shows "\<zlast> (sinsert x s) = \<zlast> s"
  using a2 seq1_seq [OF a1] sinsert_seq1 [OF seq1_seq [OF a1] a2] seq1_nempty [OF a1]
  by (simp add: slast_def sinsert_beta_back sinsert_zcard zcard_zero)

lemma sfront_sconcat_sunit:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "\<zfront> (s\<zcat>\<lang>x\<rang>) = s"
  using a1 a2 sunit_seq [OF a2] sconcat_closed [OF a1 sunit_seq [OF a2]]
  apply (simp add: sfront_redef dsub_def Z_sconcat_zcard sunit_zcard)
  apply (simp add: sconcat_redef stranslate_def sinsert_redef2 [OF sempty_seq] eind_def)
  apply (auto simp only: sempty_def)
proof -
  fix x
  assume b1: "(\<zcard>s + 1 \<mapsto> x) \<in> s"
  then have "\<zcard>s + 1 \<in> \<zdom> s"
    by (auto)
  then show "\<False>"
    by (auto simp add: seq_dom [OF a1])
qed

lemma slast_sconcat_sunit:
  assumes a1: "s \<in> \<zseq> X" and a2: "x \<in> X"
  shows "\<zlast> (s\<zcat>\<lang>x\<rang>) = x"
  apply (simp add: slast_def)
  apply (simp add: Z_sconcat_zcard [OF a1 sunit_seq [OF a2]] sunit_zcard [OF a2])
  apply (rule functional_beta)
  apply (rule seq_functional [OF sconcat_closed [OF a1 sunit_seq [OF a2]]])
  apply (simp add: sconcat_redef [OF a1 sunit_seq [OF a2]])
  apply (simp add: stranslate_sunit)
  done



lemma sfront_slast_cong:
  assumes a1: "s \<in> \<zseq>\<subone> X" and a2: "t \<in> \<zseq>\<subone> X" and
    a3: "\<zcard>s = \<zcard>t" and a4: "\<zfront> s = \<zfront> t" and a5: "\<zlast> s = \<zlast> t"
  shows "s = t"
proof (rule rel_eqI)
  from a3 seq_dom [OF seq1_seq [OF a1]]  seq_dom [OF seq1_seq [OF a2]] have 
    b1: "\<zdom> s = \<zdom> t"
    by (simp)
  fix n x
  show "(n \<mapsto> x) \<in> s \<Leftrightarrow> (n \<mapsto> x) \<in> t"
  proof (cases "n \<in> \<zdom> s")
    assume c1: "n \<notin> \<zdom> s"
    then have c2: "n \<notin> \<zdom> t" 
      by (simp add: b1) 
    with c1 show ?thesis
      by (simp add: Domain_iff)  
  next
    assume 
      c1: "n \<in> \<zdom> s"
    then have 
      c2: "n \<in> \<zdom> t"
      by (simp add: b1)
    show ?thesis
    proof (cases "n = \<zcard>s")
      assume d1: "n = \<zcard>s"
      from c1 have "(n \<mapsto> x) \<in> s \<Leftrightarrow> s\<cdot>n = x"
        by (auto intro: functional_appl functional_beta seq_functional [OF seq1_seq [OF a1]])
      also from d1 have "\<dots> \<Leftrightarrow> \<zlast> s = x"
        by (simp add: slast_def)
      also have "\<dots> \<Leftrightarrow> \<zlast> t = x"
        by (simp add: a5)
      also from d1 have "\<dots> \<Leftrightarrow> t\<cdot>n = x"
        by (simp add: slast_def a3)
      also from c2 have "\<dots> \<Leftrightarrow> (n \<mapsto> x) \<in> t" 
        by (auto intro: functional_appl functional_beta seq_functional [OF seq1_seq [OF a2]])
      finally show ?thesis by (this)
    next
      assume d1: "n \<noteq> \<zcard>s"
      from c1 have "(n \<mapsto> x) \<in> s \<Leftrightarrow> s\<cdot>n = x"
        by (auto intro: functional_appl functional_beta seq_functional [OF seq1_seq [OF a1]])
      also from c1 d1 sfront_beta [OF a1] have "\<dots> \<Leftrightarrow> (\<zfront> s)\<cdot>n = x"
        by (auto simp add: seq_dom [OF seq1_seq [OF a1]] zInts_zcard int_of_norm)
      also have "\<dots> \<Leftrightarrow> (\<zfront> t)\<cdot>n = x"
        by (simp add: a4)
      also from c2 d1 sfront_beta [OF a2] have "\<dots> \<Leftrightarrow> t\<cdot>n = x"
        by (auto simp add: a3 seq_dom [OF seq1_seq [OF a2]] zInts_zcard int_of_norm)
      also from c2 have "\<dots> \<Leftrightarrow> (n \<mapsto> x) \<in> t" 
        by (auto intro: functional_appl functional_beta seq_functional [OF seq1_seq [OF a2]])
      finally show ?thesis by (this)   
    qed
  qed
qed

lemma sfront_slast_reconstr:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "(\<zfront> s)\<zcat>\<lang>\<zlast> s\<rang> = s"
  apply (insert
    sconcat_closed [OF sfront_closed [OF a1] sunit_seq [OF slast_in_ran [OF a1]]]
    sfront_closed [OF a1]
    sunit_seq [OF slast_in_ran [OF a1]]
    slast_in_ran [OF a1])
  apply (rule sfront_slast_cong)
  apply (rule seq1I)
  apply (assumption)
  apply (simp add: zcard_zero [symmetric] Z_sconcat_zcard sinsert_zcard sempty_seq zNats_zcard nat_of_norm)
  apply (rule a1)
  apply (simp add: Z_sconcat_zcard sinsert_zcard sempty_seq sfront_zcard [OF a1] zNats_zcard nat_of_norm)
  apply (simp_all add: sfront_sconcat_sunit slast_sconcat_sunit)
  done

lemma Z_sfront_slast_reconstr:
  assumes 
    a1: "s \<in> \<zseq> X"
  shows 
    "s \<noteq> \<sempty> \<Rightarrow> (\<zfront> s)\<zcat>\<lang>\<zlast> s\<rang> = s"
  apply (msafe(inference))
  apply (intro sfront_slast_reconstr)
  using a1
  apply (auto intro: seq1I)
  done


theorem seq_induct_rev:
  assumes a1: "s \<in> \<zseq> X" and a2: "P \<sempty>" and a3: "(\<And>xs x \<bullet> \<lbrakk>xs \<in> \<zseq> X; x \<in> X; P xs\<rbrakk> \<turnstile> P (xs\<zcat>\<lang>x\<rang>))"
  shows "P s"
proof -
  have b1: "\<forall> c | c \<in> \<nat> \<bullet> (\<forall> s \<bullet> s \<in> \<zseq> X \<Rightarrow> \<zcard>s = c \<Rightarrow> P s)"
  proof (rule allI, rule impI)
    fix c
    assume c1: "c \<in> \<nat>"
    then show "(\<forall> s \<bullet> s \<in> \<zseq> X \<Rightarrow> \<zcard>s = c \<Rightarrow> P s)"
      apply (induct c set: zNats)
      apply (auto)
    proof -
      fix s'
      assume Ab1: "s' \<in> \<zseq> X" and Ab2: "\<zcard>s' = 0"
      with a2 show "P s'"
        by (simp add: zcard_zero)
    next
      fix n s'
      assume Ab1: "n \<in> \<nat>" and
        Ab2: "\<forall> s \<bullet> s \<in> \<zseq> X \<Rightarrow> \<zcard>s = n \<Rightarrow> P s" and 
        Ab3: "s' \<in> \<zseq> X" and
        Ab4: "\<zcard>s' = n + 1"
      have Ab5: "s' \<in> \<zseq>\<subone> X"
        apply (rule seq1I [OF Ab3])
        apply (simp add: zcard_zero [symmetric, OF Ab3] Ab4 Ab1 nat_of_norm)
        done
      have "(\<zfront> s')\<zcat>\<lang>\<zlast> s'\<rang> = s'"
        by (rule sfront_slast_reconstr [OF Ab5])
      moreover have "P ((\<zfront> s')\<zcat>\<lang>\<zlast> s'\<rang>)"
        apply (rule a3)
        apply (rule sfront_closed [OF Ab5])
        apply (rule slast_in_ran [OF Ab5])
        apply (rule Ab2 [rule_format])
        apply (simp_all add: sfront_closed [OF Ab5] sfront_zcard [OF Ab5] Ab4)
        done
      ultimately show "P s'" by (simp)
    qed
  qed
  show "P s"
    apply (rule b1 [rule_format, of "\<zcard>s"])
    apply (auto simp add: a1)
    done
qed

lemma sfront_sconcat:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq>\<subone> X"
  shows "\<zfront> (s\<zcat>t) = s\<zcat>(\<zfront> t)"
proof -
  have 
    "\<zfront> (s\<zcat>t) 
    = \<zfront> (s\<zcat>((\<zfront> t)\<zcat>\<lang>\<zlast> t\<rang>))"
    by (simp add: sfront_slast_reconstr [OF a2])
  also from sfront_sconcat_sunit [OF sconcat_closed [OF a1 sfront_closed [OF a2]] slast_in_ran [OF a2]] have "\<dots> 
    = s\<zcat>(\<zfront> t)"
    using a1 a2
    by (simp add: Z_sconcat_assoc sfront_closed sunit_seq slast_in_ran)
  finally show "?thesis" by (this)
qed

lemma sfront_reconstr:
  assumes 
    a1: "s \<in> \<zseq>\<subone> X"
  shows 
    "insert (\<zcard>s \<mapsto> s\<cdot>(\<zcard>s)) (\<zfront> s) = s"
  apply (insert sfront_slast_reconstr [OF a1])
  using a1
  apply (simp add: sconcat_redef [OF sfront_closed sunit_seq] slast_in_ran)
  apply (simp add: slast_def stranslate_sunit stranslate_sunit sfront_zcard)
  done

lemma Z_shead_slast_sunit:
  assumes 
    a1: "x \<in> X"
  shows 
    "\<lch> \<zhead> \<lang>x\<rang> \<chEq> \<zlast> \<lang>x\<rang> \<chEq> x \<rch>"
  using a1
  by (simp add: shead_sunit slast_sunit)

lemma Z_stail_sfront_sunit:
  assumes 
    a1: "x \<in> X"
  shows 
    "\<lch> \<ztail> \<lang>x\<rang> \<chEq> \<zfront> \<lang>x\<rang> \<chEq> \<sempty> \<rch>"
  using a1
  by (simp add: sfront_sunit stail_sunit)

lemma Z_shead_stail_sconcat:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "s \<noteq> \<sempty> \<Rightarrow> \<zhead> (s \<zcat> t) = \<zhead> s \<and> \<ztail> (s \<zcat> t) = (\<ztail> s) \<zcat> t"
proof (msafe(inference))
  assume b0: "s \<noteq> \<sempty>"
  from seq1I [OF a1 b0] have a1': "s \<in> \<zseq>\<subone> X" by this
  show "\<zhead> (s \<zcat> t) = \<zhead> s" by (rule shead_sconcat [OF a1' a2])
  show "\<ztail> (s \<zcat> t) = (\<ztail> s) \<zcat> t" by (rule stail_sconcat [OF a1' a2])
qed


lemma Z_decomposition_defs:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows
    Z_shead_def: "\<zhead> s \<defs> s\<cdot>1" and
    Z_slast_def: "\<zlast> s \<defs> s\<cdot>(\<zcard>s)" and
    Z_stail_def: "\<ztail> s \<defs> (\<glambda> n |  n \<in> 1..(\<zcard>s - 1) \<bullet> s\<cdot>(n + 1))" and
    Z_sfront_def: "\<zfront> s \<defs> 1..(\<zcard>s - 1)\<zdres>s"
  using a1
  by (auto simp add: shead_def slast_def stail_def sfront_def glambda_def)
  
section {* Reverse *}

text {*

Sequences can be reversed.  A helper function sreflect is defined to 
reverse the Domain of the Sequence.

*}

definition
  srev :: "'a seqT \<rightarrow> 'a seqT"
where
  srev_def: "srev \<defs> (\<olambda> s \<bullet> (\<glambda> n | n \<in> \<zdom> s \<bullet> s\<cdot>(\<zcard>s - n + 1)))"

notation (xsymbols)
  srev ("\<zrev>")

lemma Z_srev_def:
  "s \<in> \<zseq> X \<turnstile> \<zrev> s \<defs> (\<glambda> n | n \<in> \<zdom> s \<bullet> s\<cdot>(\<zcard>s - n + 1))"
  by (auto simp add: srev_def)

lemma srev_mem:
  assumes a1: "s \<in> \<zseq> X"
  shows "(n \<mapsto> x) \<in> \<zrev> s \<Leftrightarrow> (\<zcard>s - n + 1 \<mapsto> x) \<in> s"
proof (auto simp add: srev_def glambda_mem seq_dom [OF a1])
  assume 
    b1: "n \<in> \<int>" "1 \<le> n" "n \<le> \<zcard>s"
  show "(\<zcard>s - n + 1 \<mapsto> s\<cdot>(\<zcard>s - n + 1)) \<in> s"
    apply (rule seq_appl [OF a1])
    using a1 b1
    apply (auto simp add: zInts_zcard) 
    done
next
  assume b1: "(\<zcard>s - n + 1 \<mapsto> x) \<in> s"
  from seq_index_bound [OF a1 b1] have "\<zcard>s - n + 1 \<in> \<int>"
    by (auto)
  then have "\<zcard>s - (\<zcard>s - n + 1) + 1 \<in> \<int>"
    by (simp only: zInts_zcard zInts_norm)
  then show "n \<in> \<int>"
    by (simp)
  from seq_index_bound [OF a1 b1] show "1 \<le> n"
    by (simp)
  from seq_index_bound [OF a1 b1] show "n \<le> \<zcard>s"
    by (simp)
  from a1 b1 show "x = s\<cdot>(\<zcard>s - n + 1)"
    by (simp add: seq_beta)
qed

lemma srev_as_image:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zrev> s = (\<olambda> (n, x) \<bullet> (\<zcard>s - n + 1 \<mapsto> x))\<lparr>s\<rparr>"
  by (auto intro!: exI simp add: srev_mem [OF a1] image_def)

lemma Z_srev_sempty: "\<zrev> \<sempty> = \<sempty>"
  by (simp add: sempty_def srev_def glambda_def)

lemma srev_functional:
  assumes a1: "s \<in> \<zseq> X"
  shows "functional (\<zrev> s)"
  by (simp add: srev_def glambda_functional)

lemma srev_dom:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zdom> (\<zrev> s) = \<zdom> s"
  by (auto simp add: srev_def glambda_dom)

lemma srev_ran:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> (\<zrev> s) \<subseteq> X"
  by (auto intro!: seq_in_ran [OF a1] simp add: srev_def glambda_ran seq_dom [OF a1] zInts_zcard)

lemma srev_ran_eq:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> (\<zrev> s) = \<zran> s"
proof (auto 
         intro!: seq_in_ran [OF seq_seq_ran [OF a1]] 
         simp add: srev_def glambda_ran seq_dom [OF a1] zInts_zcard)
  fix n x
  assume b0: "(n \<mapsto> x) \<in> s"
  from seq_beta [OF a1 b0] seq_index_bound [OF a1 b0]
  show "(\<exists> k \<bullet> x = s\<cdot>(\<zcard>s - k + 1) \<and> k \<in> \<int> \<and> 1 \<le> k \<and> k \<le> \<zcard>s)"
    apply (witness "\<zcard>s - n + 1")
    apply (auto simp add: zInts_zcard)
    done
qed

lemma srev_closed:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zrev> s \<in> \<zseq> X"
  apply (unfold srev_def)
  apply (rule seqIa [where ?n = "\<zcard>s"])
  apply (simp add: zNats_zcard)
  apply ((mauto(fspace)))
  apply (auto 
           intro!: seq_in_ran [OF a1] 
           simp add: glambda_mem seq_dom [OF a1] srev_dom [OF a1] srev_ran [OF a1] zInts_zcard)
  done

lemma srev_zcard:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zcard>(\<zrev> s) = (\<zcard>s)"
  by (simp add: seq_zcard_dom [OF srev_closed [OF a1]] srev_dom [OF a1] seq_zcard_dom [OF a1])

lemma srev_not_empty:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zrev> s \<in> \<zseq>\<subone> X"
  using a1 
  apply ((msafe(fspace)))
  apply (insert seq1_seq [OF a1] srev_closed [OF seq1_seq [OF a1]])
  apply (simp_all add: srev_functional srev_dom srev_ran srev_zcard zcard_zero [symmetric] seq_dom)
  done

lemma Z_srev_sunit: "\<zrev> \<lang>x\<rang> = \<lang>x\<rang>"
  apply (simp add: sunit_conv srev_def fin_pfun_simp glambda_def)
  apply (simp add: fin_funappl eind_def) 
  done

lemma srev_beta:
  assumes a1: "s \<in> \<zseq> X" and a2: "i \<in> \<int>" and a3: "1 \<le> i" and a4: "i \<le> \<zcard>s"
  shows "(\<zrev> s)\<cdot>(\<zcard>s - i + 1) = s\<cdot>i"
  apply (rule functional_beta [OF srev_functional [OF a1]])
  using seq_appl [OF a1 a2 a3 a4] a1 a2 a3 a4
  apply (simp add: srev_def glambda_mem seq_dom [OF a1] zInts_zcard)
  done    

lemma srev_beta2:
  assumes a1: "s \<in> \<zseq> X" and a2: "i \<in> \<int>" and a3: "1 \<le> i" and a4: "i \<le> \<zcard>s" 
  shows "(\<zrev> s)\<cdot>i = s\<cdot>(\<zcard>s - i + 1)"
  apply (rule functional_beta [OF srev_functional [OF a1]])
  using seq_appl [OF a1, of "\<zcard>s - i + 1"] a1 a2 a3 a4
  apply (simp add: srev_def glambda_mem seq_dom [OF a1] zInts_zcard)
  done    

lemma Z_srev_sconcat:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "\<zrev> (s\<zcat>t) = (\<zrev> t)\<zcat>(\<zrev> s)"
proof -
  from a1 a2 have b1: "\<zcard>(s\<zcat>t) = \<zcard>s + \<zcard>t"
    by (simp add: Z_sconcat_zcard)
  let ?f = "(\<olambda> (n, x) \<bullet> (\<zcard>s + \<zcard>t - n + 1 \<mapsto> x))"
  have "\<zrev> (s\<zcat>t) = ?f\<lparr>s\<zcat>t\<rparr>"
    by (auto simp add: srev_as_image [OF sconcat_closed [OF a1 a2]] b1 image_def zInts_zcard)
  also have "\<dots> = ?f\<lparr>s\<rparr> \<union> ?f\<lparr>stranslate t (\<zcard>s)\<rparr>"
    by (simp add: image_Un sconcat_redef [OF a1 a2]) 
  also have "?f\<lparr>stranslate t (\<zcard>s)\<rparr> = \<zrev> t"
    by (auto simp add: srev_as_image [OF a2] image_def stranslate_def)
  also have "?f\<lparr>s\<rparr> = stranslate (\<zrev> s) (\<zcard>t)"
    by (auto simp add: srev_as_image [OF a1] image_def stranslate_def)
  also have "stranslate (\<zrev> s) (\<zcard>t) \<union> \<zrev> t = (\<zrev> t)\<zcat>(\<zrev> s)"
    apply (simp add: sconcat_redef [OF srev_closed [OF a2] srev_closed [OF a1]])
    apply (auto simp add: srev_zcard[OF a2])
    done
  finally show "?thesis" by (this)
qed

lemma srev_sinsert:
  assumes a1: "xs \<in> \<zseq> X" and a2: "x \<in> X"
  shows "\<zrev> (sinsert x xs) = (\<zrev> xs)\<zcat>\<lang>x\<rang>"
  by (simp add: sinsert_sconcat [OF a1 a2] Z_srev_sconcat [OF sunit_seq [OF a2] a1] Z_srev_sunit)

lemma Z_srev_srev:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zrev> (\<zrev> s) = s"
  apply (subst srev_as_image [OF srev_closed [OF a1]])
  apply (subst srev_zcard [OF a1])
  apply (subst srev_as_image [OF a1])
  apply (auto intro!: exI simp add: image_def)
  done

lemma shead_srev_sfront:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zhead> (\<zrev> s) = \<zlast> s"
  apply (simp add: shead_def slast_def)
  apply (subst srev_beta2 [OF seq1_seq [OF a1]])
  apply (auto simp add: seq1_card_ge_1 [OF a1])
  done

text
{*

The Spivey book has the statement: @{text "s \<noteq> \<sempty> \<Rightarrow> \<ztail> (\<zrev> s) = \<zfront> s"}.  
This statement is false.

Consider the set:
@{text "S = {1 \<mapsto> A, 2 \<mapsto> B, 3 \<mapsto> C"} then:
@{text "\<ztail> (\<zrev> S) = \<ztail> {1 \<mapsto> C, 2 \<mapsto> B, 3 \<mapsto> A} = {1 \<mapsto> C, 2 \<mapsto> B} 
\<noteq> \<zfront> S = {1 \<mapsto> A, 2 \<mapsto> B}"}
*}


lemma stail_srev_srev_sfront:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<ztail> (\<zrev> s) = \<zrev> (\<zfront> s)"
proof -
  have "s \<noteq> \<sempty> \<Rightarrow> \<ztail> (\<zrev> s) = \<zrev> (\<zfront> s)"
  proof (rule seq_induct [OF seq1_seq [OF a1]])
    apply_end simp_all
    apply_end (msafe(inference))
    fix xs x
    assume 
      b0: "xs \<in> \<zseq> X" and 
      b1: "x \<in> X" and 
      b2: "xs \<noteq> \<sempty> \<Rightarrow> \<ztail> (\<zrev> xs) = \<zrev> (\<zfront> xs)"
    show 
      "\<ztail> (\<zrev> (\<lang>x\<rang> \<zcat> xs)) = \<zrev> (\<zfront> (\<lang>x\<rang> \<zcat> xs))"
    proof (cases "xs = \<sempty>")
      apply_end simp
      show "\<ztail> (\<zrev> (\<lang>x\<rang> \<zcat> \<sempty>)) = \<zrev> (\<zfront> (\<lang>x\<rang> \<zcat> \<sempty>))"
        by (simp add: 
              Z_srev_sunit sfront_sunit [OF b1] stail_sunit [OF b1] 
              Z_srev_sempty Z_sconcat_sempty [OF sunit_seq [OF b1]])
    next
      assume b3: "xs \<noteq> \<sempty>"
      from seq1I [OF b0 b3] have b0': "xs \<in> \<zseq>\<subone> X" by this
      from sunit_seq [OF b1] have b1': "\<lang>x\<rang> \<in> \<zseq> X" by this
      from b2 [rule_format] b3 have b4: "\<ztail> (\<zrev> xs) = \<zrev> (\<zfront> xs)" by auto
      have "\<ztail> (\<zrev> (\<lang>x\<rang> \<zcat> xs)) = \<ztail> ( (\<zrev> xs) \<zcat> \<lang>x\<rang> )"
        by (simp add: Z_srev_sconcat [OF b1' b0] Z_srev_sunit)
      also have "\<dots> = (\<ztail> (\<zrev> xs)) \<zcat> \<lang>x\<rang>"
        by (simp add: stail_sconcat [OF srev_not_empty [OF b0'] b1'])
      also have "\<dots> = \<zrev> (\<zfront> xs) \<zcat>  \<lang>x\<rang>" by (simp add: b4)
      finally have b5: "\<ztail> (\<zrev> (\<lang>x\<rang> \<zcat> xs)) = \<zrev> (\<zfront> xs) \<zcat>  \<lang>x\<rang>" by this
 
      have "\<zrev> (\<zfront> (\<lang>x\<rang> \<zcat> xs)) = \<zrev> (\<lang>x\<rang> \<zcat> (\<zfront> xs))"
        by (simp add: sfront_sconcat [OF b1' b0'])
      also have "\<dots> = \<zrev> (\<zfront> xs) \<zcat> \<lang>x\<rang>"
        by (simp add: Z_srev_sconcat [OF b1' sfront_closed [OF b0']] Z_srev_sunit)
      finally have b6: "\<zrev> (\<zfront> (\<lang>x\<rang> \<zcat> xs)) = \<zrev> (\<zfront> xs) \<zcat> \<lang>x\<rang>" by this

      from b5 b6 show "\<ztail> (\<zrev> (\<lang>x\<rang> \<zcat> xs)) = \<zrev> (\<zfront> (\<lang>x\<rang> \<zcat> xs))"
        by auto
    qed
  qed
  with seq1D [OF a1] show ?thesis by auto
qed

lemma Z_shead_stail_srev_sfront:
  assumes a1: "s \<in> \<zseq> X"
  shows "s \<noteq> \<sempty> \<Rightarrow> (\<zhead> (\<zrev> s) = \<zlast> s) \<and> (\<ztail> (\<zrev> s) = \<zrev> (\<zfront> s)) "
  apply (msafe(inference))
  apply (simp add: shead_srev_sfront [OF seq1I [OF a1 _]])
  apply (simp add: stail_srev_srev_sfront [OF seq1I [OF a1 _]])
  done

lemma slast_srev_shead:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zlast> (\<zrev> s) = \<zhead> s"
  apply (simp add: shead_def slast_def)
  apply (subst srev_beta2 [OF seq1_seq [OF a1]])
  apply (auto simp add: seq1_card_ge_1 [OF a1] zInts_zcard srev_zcard [OF seq1_seq [OF a1]])
  done

lemma sfront_srev_srev_stail:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<zfront> (\<zrev> s) = \<zrev> (\<ztail> s)"
proof -
  have "s \<noteq> \<sempty> \<Rightarrow> \<zfront> (\<zrev> s) = \<zrev> (\<ztail> s)"
  proof (rule seq_cases [OF seq1_seq [OF a1]])
    apply_end simp
    apply_end (msafe(inference))
    fix xs x
    assume b0: "xs \<in> \<zseq> X" and b1: "x \<in> X"
    apply_end (simp add: sinsert_sconcat [OF _ _])
    from sunit_seq [OF b1] have b1': "\<lang>x\<rang> \<in> \<zseq> X" by this
    show "\<zfront> (\<zrev> (\<lang>x\<rang> \<zcat> xs)) = \<zrev> (\<ztail> (\<lang>x\<rang> \<zcat> xs))"
    proof -
      have "\<zfront> (\<zrev> (\<lang>x\<rang> \<zcat> xs)) = \<zfront> (\<zrev> xs \<zcat> \<zrev> \<lang>x\<rang>)"
        by (simp add: Z_srev_sconcat [OF b1' b0])
      also have "\<dots> = \<zfront> (\<zrev> xs \<zcat> \<lang>x\<rang>)"
        by (simp add: Z_srev_sunit)
      also have "\<dots> = \<zrev> xs \<zcat> \<zfront> \<lang>x\<rang>"
        by (simp add: sfront_sconcat [OF srev_closed [OF b0] sunit_seq1 [OF b1]])
      also have "\<dots> = \<zrev> xs"
        by (simp add: sfront_sunit [OF b1] Z_sconcat_sempty [OF srev_closed [OF b0]])
      finally have b4: "\<zfront> (\<zrev> (\<lang>x\<rang> \<zcat> xs)) = \<zrev> xs" by this

      have "\<zrev> (\<ztail> (\<lang>x\<rang> \<zcat> xs)) = \<zrev> (\<ztail> \<lang>x\<rang> \<zcat> xs)"
        by (simp add: stail_sconcat [OF sunit_seq1 [OF b1] b0])
      also have "\<dots> = \<zrev> xs"
        by (simp add: stail_sunit [OF b1] Z_sconcat_sempty [OF b0])
      finally have "\<zrev> (\<ztail> (\<lang>x\<rang> \<zcat> xs)) = \<zrev> xs" by this

      with b4 show ?thesis by auto
    qed
  qed
  with seq1D [OF a1] show ?thesis by auto
qed


lemma Z_slast_sfront_srev:
  assumes a1: "s \<in> \<zseq> X"
  shows 
    "s \<noteq> \<sempty> \<Rightarrow> 
      \<zlast> (\<zrev> s) = \<zhead> s \<and> \<zfront> (\<zrev> s) = \<zrev> (\<ztail> s)"
  apply (msafe(inference))
  apply (simp add: slast_srev_shead [OF seq1I [OF a1]])
  apply (simp add: sfront_srev_srev_stail [OF seq1I [OF a1]])
  done


section {* Prefix, Suffix and Infix *}

text {*

A sequence can be a prefix of, a suffix of, or within another sequence. (pg. 119)


*}

definition
  sprefix :: "['a seqT, 'a seqT] \<rightarrow> \<bool>"
where
  sprefix_def: "sprefix s t \<defs> \<exists> v | v \<in> \<zseq> (\<zran> t) \<bullet> s\<zcat>v = t"

notation (xsymbols)
  sprefix (infix "\<prefix>" 100)

definition
  ssuffix :: "['a seqT, 'a seqT] \<rightarrow> \<bool>"
where
  ssuffix_def: "ssuffix s t \<defs> \<exists> u | u \<in> \<zseq> (\<zran> t) \<bullet> u\<zcat>s = t"

notation (xsymbols)
  ssuffix (infix "\<suffix>" 100)

definition
  sinfix :: "['a seqT, 'a seqT] \<rightarrow> \<bool>"
where
  sinfix_def: "sinfix s t \<defs> (\<exists> u v | u \<in> \<zseq> (\<zran> t) \<and> v \<in> \<zseq> (\<zran> t) \<bullet> u\<zcat>s\<zcat>v = t)"

notation (xsymbols)
  sinfix (infix "\<infix>" 100)

lemma sprefix_closed:
  assumes a1: "t \<in> \<zseq> X" and a2: "s \<prefix> t"
  shows "\<exists> v | v \<in> \<zseq> X \<bullet> s\<zcat>v = t"
proof -
  from a2 obtain v where b0: "v \<in> \<zseq> (\<zran> t)" and b1: "(s\<zcat>v = t)" 
    by (auto simp add: sprefix_def)
  have b0': "v \<in> \<zseq> X" 
    by (rule seq_transitive [OF a1 [THEN seq_ran] b0])
  from b0' b1 show ?thesis
    by (witness "v", simp)
qed

lemma ssuffix_closed:
  assumes a1: "t \<in> \<zseq> X" and a2: "s \<suffix> t"
  shows "\<exists> u | u \<in> \<zseq> X \<bullet> u\<zcat>s = t"
proof -
  from a2 obtain u where  b0: "u \<in> \<zseq> (\<zran> t)" and b1: "u\<zcat>s = t"
    by (auto simp add: ssuffix_def)
  from seq_transitive [OF a1 [THEN seq_ran] b0]
  have b0': "u \<in> \<zseq> X" 
    by auto
  from b0' b1 show ?thesis
    by (witness "u", simp)
qed

lemma sinfix_closed:
  assumes a1: "t \<in> \<zseq> X" and a2: "s \<infix> t"
  shows "\<exists> u v | u \<in> \<zseq> X \<and> v \<in> \<zseq> X \<bullet> u\<zcat>s\<zcat>v = t"
proof -
  from a2 obtain u v where b0: "u \<in> \<zseq> (\<zran> t)" and b1: "v \<in> \<zseq> (\<zran> t)" and
    b2: "u\<zcat>s\<zcat>v = t"
    by (auto simp add: sinfix_def)
  from seq_transitive [OF a1 [THEN seq_ran] b0] have b0': "u \<in> \<zseq> X" by auto
  from seq_transitive [OF a1 [THEN seq_ran] b1] have b1': "v \<in> \<zseq> X" by auto
  from b0' b1' b2 show ?thesis
    by (witness "u", witness "v", simp)
qed

lemma sprefix_redef:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "s \<prefix> t \<Leftrightarrow> (\<exists> v | v \<in> \<zseq> X \<bullet> s\<zcat>v = t)"
  apply (msafe_no_assms(inference))
  using a1 a2
  apply (simp add: sprefix_closed)
proof -
  fix v
  assume b0: "v \<in> \<zseq> X" and b1: "s\<zcat>v = t"
  have "\<zran> v \<subseteq> \<zran> (s\<zcat>v)" 
    by (auto simp add: Z_sconcat_ran_union [OF a1 b0])
  also have "\<dots> \<subseteq> \<zran> t"
    by (simp add: b1)
  finally have "\<zran> v \<subseteq> \<zran> t" by this
thm seq_X_ran
  with seq_X_ran [OF b0] have b2: "v \<in> \<zseq> (\<zran> t)" by auto
  then show "s \<prefix> t"
    apply (simp add: sprefix_def)
    apply (witness "v")
    apply (simp add: b1)
    done
qed

lemma ssuffix_redef:
  assumes 
    a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows 
    "s \<suffix> t \<Leftrightarrow> (\<exists> u | u \<in> \<zseq> X \<bullet> u\<zcat>s = t)"
  apply (msafe_no_assms(inference))
  apply (simp add: ssuffix_closed a2)
proof -
  fix u
  assume 
    b0: "u \<in> \<zseq> X" and 
    b1: "u\<zcat>s = t"
  have 
    "\<zran> u
    \<subseteq> \<zran> (u\<zcat>s)"
    by (auto simp add: Z_sconcat_ran_union [OF b0 a1])
  also have "\<dots> 
    \<subseteq> \<zran> t"
    by (simp add: b1)
  finally have 
    "\<zran> u \<subseteq> \<zran> t"
    by this
  with seq_X_ran [OF b0] have 
    "u \<in> \<zseq> (\<zran> t)"
    by auto
  then show 
    "s \<suffix> t"
    apply (simp add: ssuffix_def)
    apply (witness "u")
    apply (simp add: b1)
    done
qed

lemma sinfix_redef:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "s \<infix> t \<Leftrightarrow> (\<exists> u v | u \<in> \<zseq> X \<and> v \<in> \<zseq> X \<bullet> u\<zcat>s\<zcat>v = t)"
proof (msafe_no_assms(inference))
  assume b0: "s \<infix> t"
  from sinfix_closed [OF a2 b0] show "\<exists> u v | u \<in> \<zseq> X \<and> v \<in> \<zseq> X \<bullet> u\<zcat>s\<zcat>v = t" by this
next
  fix u v
  assume b0: "u \<in> \<zseq> X" and b1: "v \<in> \<zseq> X" and b2: "u\<zcat>s\<zcat>v = t"
  have b3: "u\<zcat>s \<in> \<zseq> X" by (rule sconcat_closed [OF b0 a1])

  have "\<zran> u \<subseteq> \<zran> (u\<zcat>s\<zcat>v)"
    apply (simp add: Z_sconcat_ran_union [OF b3 b1])
    apply (auto simp add: Z_sconcat_ran_union [OF b0 a1])
    done
  also have "\<dots> \<subseteq> \<zran> t"
    by (simp add: b2)
  finally have "\<zran> u \<subseteq> \<zran> t" by this
  with seq_X_ran [OF b0] have b4: "u \<in> \<zseq> (\<zran> t)" by auto

  have "\<zran> v \<subseteq> \<zran> (u\<zcat>s\<zcat>v)" 
    by (auto simp add: Z_sconcat_ran_union [OF b3 b1])
  also have "\<dots> \<subseteq> \<zran> t"
    by (simp add: b2)
  finally have "\<zran> v \<subseteq> \<zran> t" by this
  with seq_X_ran [OF b1] have b5: "v \<in> \<zseq> (\<zran> t)" by auto

  from b4 b5 b2 show "s \<infix> t"
    apply (simp add: sinfix_def)
    apply (witness "u")
    apply simp
    apply (witness "v")
    apply simp
    done
qed


lemma Z_component_defs:
   assumes 
     a1: "s \<in> \<zseq> X" "t \<in> \<zseq> X"
   shows 
     Z_sprefix_def: "s \<prefix> t \<defs> (\<exists> v | v \<in> \<zseq> X \<bullet> s\<zcat>v = t)" and
     Z_ssuffix_def: "s \<suffix> t \<defs> (\<exists> u | u \<in> \<zseq> X \<bullet> u\<zcat>s = t)" and
     Z_sinfix_def: "s \<infix> t \<defs> (\<exists> u v | u \<in> \<zseq> X \<and> v \<in> \<zseq> X \<bullet> u\<zcat>s\<zcat>v = t)"
  using a1
  by (simp_all only: ssuffix_redef sprefix_redef sinfix_redef)

lemma sprefix_subset:
  assumes 
    a1: "s \<in> \<zseq> X" and
    a2: "t \<in> \<zseq> X" and
    a3: "s \<prefix> t"
  shows 
    "s \<subseteq> t"
proof -
  from a3 obtain v where 
    b0: "s\<zcat>v = t" and 
    b1: "v \<in> \<zseq> (\<zran> t)"
    by (auto simp add: sprefix_def)
  from seq_transitive [OF a2 [THEN seq_ran] b1] 
  have 
    b2: "v \<in> \<zseq> X" 
    by auto
  from b0 have
    b3: "s\<zcat>v = s \<union> stranslate v (\<zcard>s)" by (intro sconcat_redef [OF a1 b2])
  then show 
    ?thesis
    apply (subst b0 [THEN sym])
    apply auto
    done
qed

lemma sprefix_sconcat:
  assumes a1: "(a\<zcat>b) \<prefix> t" and a2: "a \<in> \<zseq> X" and a3: "b \<in> \<zseq> X" and a4: "t \<in> \<zseq> X"
  shows "a \<prefix> t"
proof (simp add: sprefix_def)
  from a1 obtain v where b1: "v \<in> \<zseq> (\<zran> t)" and b2: "(a\<zcat>b)\<zcat>v = t" 
    by (auto simp add: sprefix_def)
  with seq_transitive [OF a4 [THEN seq_ran] b1] have b0: "v \<in> \<zseq> X" by auto
  have concat: "a\<zcat>(b\<zcat>v) = t"
  proof -
    have "(a\<zcat>b)\<zcat>v = t" by (simp only: b1 b2)
    then show "a\<zcat>(b\<zcat>v) = t"
      by (simp add: Z_sconcat_assoc [OF a2 a3 b0])
  qed
  have seq: "b\<zcat>v \<in> \<zseq> (\<zran> t)"
  proof (rule seqIa [where ?n = "\<zcard>b + \<zcard>v"], simp add: zNats_zcard)
    from seq_functional [OF sconcat_closed [OF a3 b0]] 
    have ftn: "functional (b\<zcat>v)"
      by auto
    from sconcat_dom [OF a3 b0] 
    have dom: "\<zdom> (b\<zcat>v) = 1..(\<zcard>b + \<zcard>v)"
      by auto
    have ran: "\<zran> (b\<zcat>v) \<subseteq> \<zran> t"
    proof -
      from concat have "(stranslate (b\<zcat>v) (\<zcard>a)) \<subseteq> t"
        by (auto simp add: sconcat_redef [OF a2 sconcat_closed [OF a3 b0]])
      then have "\<zran> (stranslate (b\<zcat>v) (\<zcard>a)) \<subseteq> \<zran> t" 
        by auto
      then show "\<zran> (b\<zcat>v) \<subseteq> \<zran> t" 
        by (simp add: stranslate_ran_eq)
    qed
    from ftn dom ran show "b\<zcat>v \<in> 1..(\<zcard>b + \<zcard>v) \<ztfun> (\<zran> t)" 
      by (mauto(fspace))
  qed
  from seq concat show "\<exists> r \<bullet> (r \<in> \<zseq> (\<zran> t)) \<and> a\<zcat>r = t"
    by (witness "b\<zcat>v", simp)
qed

lemma ssuffix_sub:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X" and a3: "s \<suffix> t"
  shows "stranslate s (\<zcard>t - \<zcard>s) \<subseteq> t"
proof -
  from ssuffix_closed [OF a2 a3] obtain u where "u \<in> \<zseq> X \<and> u\<zcat>s = t" by auto
  then have b0: "u \<in> \<zseq> X" and b1: "u\<zcat>s = t" by auto
  have card: "\<zcard>u = \<zcard>t - \<zcard>s"
  proof -
    from Z_sconcat_zcard [OF b0 a1] b1 have "\<zcard>t = \<zcard>u + \<zcard>s" by auto
    then show ?thesis by arith
  qed
  from b1 show ?thesis
    by (auto simp add: sconcat_redef [OF b0 a1] card)
qed

lemma Z_sinfix_sp:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "s \<infix> t \<Leftrightarrow> (\<exists> u | u \<in> \<zseq> X \<bullet> (s \<suffix> u) \<and> (u \<prefix> t) )"
proof (rule iffI)
  assume b0: "s \<infix> t"
  from b0 obtain u v
  where useq: "u \<in> \<zseq> (\<zran> t)"
       and vseq: "v \<in> \<zseq> (\<zran> t)"
       and concat: "u\<zcat>s\<zcat>v = t"
    by (auto simp add: sinfix_def)
  have useq': "u \<in> \<zseq> X" by (rule seq_transitive [OF a2 [THEN seq_ran] useq])
  have vseq': "v \<in> \<zseq> X" by (rule seq_transitive [OF a2 [THEN seq_ran] vseq])
  have ssubt: "stranslate s (\<zcard>u) \<subseteq> t"
    apply (insert concat)
    apply (simp only: sconcat_redef [OF sconcat_closed [OF useq' a1] vseq'])
    apply (simp only: Z_sconcat_zcard [OF useq' a1])
    apply (simp add: sconcat_redef [OF useq' a1])
    apply auto
    done
  have a1': "s \<in> \<zseq> (\<zran> t)"
  proof (rule seqIa [where ?n = "\<zcard>s"], simp add: zNats_zcard)
    have ftn: "functional s" by (rule seq_functional [OF a1])
    have dom: "\<zdom> s = (1..\<zcard>s)" by (rule seq_dom [OF a1])
    have ran: "\<zran> s \<subseteq> \<zran> t"
    proof -
      have "\<zran> s = \<zran> (stranslate s (\<zcard>u))" 
        by (rule stranslate_ran_eq [THEN sym])
      also with ssubt have "\<dots> \<subseteq> \<zran> t" by auto
      finally show ?thesis by auto
    qed
    from ftn dom ran show "s \<in> (1..\<zcard>s) \<ztfun> (\<zran> t)" by (mauto(fspace))
  qed
  have b2: "u \<in> \<zseq> (\<zran> (u\<zcat>s))" 
    apply (intro seqIa [where ?n = "\<zcard>u"])
    apply simp
    using seq_dom [OF useq] seq_functional [OF useq]
    apply (mauto(fspace) mintro: seq_functional seq_dom msimp add: sconcat_redef [OF useq a1'])
    done
  have b3: "s \<suffix> (u\<zcat>s)"
    apply (simp add: ssuffix_def)
    apply (witness "u")
    apply (simp_all add: b2)
    done
  have b4: "(u\<zcat>s) \<prefix> t"
    apply (simp add: sprefix_def)
    apply (witness "v")
    apply (simp add: concat vseq)
    done
  have b5: "u\<zcat>s \<in> \<zseq> (\<zran> (u\<zcat>s))"
    apply (rule seq_seq_ran)
    apply (rule sconcat_closed [OF useq a1'])
    done
  show "\<exists> u \<bullet> u \<in> \<zseq> X \<and> s \<suffix> u \<and> u \<prefix> t"
    apply (witness "u\<zcat>s")
    apply (simp add: b2 b3 b4)
    apply (rule seq_transitive [OF sconcat_closed [OF useq' a1, THEN seq_ran]])
    apply (rule b5)
    done
next
  assume b0: "\<exists> u \<bullet> u \<in> \<zseq> X \<and> s \<suffix> u \<and> u \<prefix> t"
  from b0 obtain u where "u \<in> \<zseq> X \<and> s \<suffix> u \<and> u \<prefix> t" by auto
  then have useqX: "u \<in> \<zseq> X" and suff: "s \<suffix> u" and pref: "u \<prefix> t" 
    by auto
  from ssuffix_closed [OF useqX suff] obtain r where "r \<in> \<zseq> X \<and> r\<zcat>s = u" by auto
  then have rseqX: "r \<in> \<zseq> X" and rcats: "r\<zcat>s = u" by auto
  from sprefix_closed [OF a2 pref] obtain v where "v \<in> \<zseq> X \<and> u\<zcat>v = t" by auto
  then have vseqX: "v \<in> \<zseq> X" and ucatv: "u\<zcat>v = t" by auto
  have rseqt: "r \<in> \<zseq> (\<zran> t)"
    apply (intro seqIa [where ?n = "\<zcard>r"])
    using seq_functional [OF rseqX] seq_dom [OF rseqX]
    apply (mauto(fspace) msimp add: ucatv [symmetric] sconcat_redef [OF useqX vseqX] zNats_zcard)
    apply (simp add: rcats [symmetric] sconcat_redef [OF rseqX a1])
    apply (auto)
    done
  have vseqt: "v \<in> \<zseq> (\<zran> t)"
    apply (intro seqIa [where ?n = "\<zcard>v"])
    using seq_functional [OF vseqX] seq_dom [OF vseqX]
    apply (mauto(fspace) msimp add: zNats_zcard)
  proof -
    have c0: "\<zran> (stranslate v (\<zcard>u)) \<subseteq> \<zran> t"
      apply (insert rcats ucatv)
      apply (simp add: sconcat_redef [OF rseqX a1])
      apply (simp add: sconcat_redef [OF useqX vseqX])
      apply (auto)
      done
    have c1: "\<zran> v = \<zran> (stranslate v (\<zcard>u))" 
      by (simp add: stranslate_ran_eq)
    from c0 c1 show "\<zran> v \<subseteq> \<zran> t" by auto
  qed
  have concat: "r\<zcat>s\<zcat>v = t" 
    apply (subst rcats)
    apply (rule ucatv)
    done 
  show "s \<infix> t"
    apply (simp add: sinfix_def)
    apply (witness "r")
    apply (rule conjI)
    apply (rule rseqt)
    apply (witness "v")
    apply (intro conjI)
    apply (rule vseqt)
    apply (rule concat)
    done
qed

lemma Z_sinfix_ps:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "s \<infix> t \<Leftrightarrow> (\<exists> v | v \<in> \<zseq> X \<bullet> (s \<prefix> v) \<and> (v \<suffix> t) )"
proof (rule iffI)
  assume b0: "s \<infix> t"  
  from sinfix_closed [OF a2 b0] obtain u v where "(u \<in> \<zseq> X \<and> v \<in> \<zseq> X) \<and> u\<zcat>s\<zcat>v = t" by auto
  then have
    uinseqX: "u \<in> \<zseq> X" and 
    vinseqX: "v \<in> \<zseq> X" and 
    concat: "u\<zcat>s\<zcat>v = t" 
    by auto
  have vseqconcat: "v \<in> \<zseq> (\<zran> (s\<zcat>v))"
  proof (rule seqIa [where ?n = "\<zcard>v"], simp add: zNats_zcard)
    have ftn: "functional v" by (rule seq_functional [OF vinseqX])
    have dom: "\<zdom> v = (1..\<zcard>v)" by (rule seq_dom [OF vinseqX])
    have ran: "\<zran> v \<subseteq> \<zran> (s\<zcat>v)"
    proof -
      have "\<zran> v = \<zran> (stranslate v (\<zcard>s))" by (simp add: stranslate_ran_eq)
      also have "\<dots> \<subseteq> (\<zran> (s\<zcat>v))" by (auto simp add: sconcat_redef [OF a1 vinseqX])
      finally show ?thesis by auto
    qed
    from ftn dom ran show "v \<in> (1..\<zcard>v) \<ztfun> (\<zran> (s\<zcat>v))" by (mauto(fspace))
  qed
  have b2: "s\<zcat>v \<in> \<zseq> X" 
    by (rule sconcat_closed [OF a1 vinseqX])
  have b3: "s \<prefix> (s\<zcat>v)"
    apply (simp add: sprefix_def)
    apply (witness "v")
    apply (simp_all add: vseqconcat)
    done       
  have useqt: "u \<in> \<zseq> (\<zran> t)"
    apply (rule seqIa [where ?n = "\<zcard>u"])
    using seq_functional [OF uinseqX] seq_dom [OF uinseqX]
    apply (mauto(fspace) msimp add: zNats_zcard)
    apply (simp add: concat [symmetric] sconcat_redef [OF sconcat_closed [OF uinseqX a1] vinseqX])
    apply (simp add: sconcat_redef [OF uinseqX a1])
    apply (auto)
    done
  have b4: "(s\<zcat>v) \<suffix> t"
    apply (simp add: ssuffix_def) 
    apply (witness "u")
    apply (intro conjI)
    apply (rule useqt)
    apply (insert concat)
    apply (simp add: Z_sconcat_assoc [OF uinseqX a1 vinseqX])
    done
  show "\<exists> v \<bullet> v \<in> \<zseq> X \<and> s \<prefix> v \<and> v \<suffix> t"
    apply (witness "s\<zcat>v")
    apply (simp add: b2 b3 b4)
    done
next
  assume b0: "\<exists> v \<bullet> v \<in> \<zseq> X \<and> s \<prefix> v \<and> v \<suffix> t"
  from b0 obtain v where "v \<in> \<zseq> X \<and> s \<prefix> v \<and> v \<suffix> t" by auto
  then have vseqX: "v \<in> \<zseq> X" and sprefixv: "s \<prefix> v" and vsuffixt: "v \<suffix> t" by auto
  from sprefix_closed [OF vseqX sprefixv] obtain r where "r \<in> \<zseq> X \<and> s\<zcat>r = v" by auto
  then have rseqX: "r \<in> \<zseq> X" and sconcatr: "s\<zcat>r = v" by auto  
  from ssuffix_closed [OF a2 vsuffixt] obtain p where "p \<in> \<zseq> X \<and> p\<zcat>v = t" by auto
  then have pseqX: "p \<in> \<zseq> X" and pconcatv: "p\<zcat>v = t" by auto
  have pseqt: "p \<in> \<zseq> (\<zran> t)"
    apply (rule seqI)
    apply (mauto(fspace))
    apply (intro seq_functional [OF pseqX])
    apply (intro seq_dom [OF pseqX])
    apply (insert pconcatv)
    apply (simp add: sconcat_redef [OF pseqX vseqX])
    apply (auto simp add: Range_def Domain_def)
    done
  have rseqt: "r \<in> \<zseq> (\<zran> t)"
  proof (rule seqI)
    have ftn: "functional r" by (rule seq_functional [OF rseqX])
    have dom: "\<zdom> r = (1..\<zcard>r)" by (rule seq_dom [OF rseqX])
    have ran: "\<zran> r \<subseteq> \<zran> t"
    proof -
      have "\<zran> r = \<zran> (stranslate r (\<zcard>s))" by (simp add: stranslate_ran_eq)
      also from sconcatr have "\<dots> \<subseteq> \<zran> v" 
        by (auto simp add: sconcat_redef [OF a1 rseqX])
      also have "\<dots> \<subseteq> \<zran> t"
      proof -
        have "\<zran> v = \<zran> (stranslate v (\<zcard>p))" by (simp add: stranslate_ran_eq)
        also from pconcatv have "\<dots> \<subseteq> \<zran> t" by (auto simp add: sconcat_redef [OF pseqX vseqX])
        finally show "\<zran> v \<subseteq> \<zran> t" by auto
      qed
      finally show "\<zran> r \<subseteq> \<zran> t" by auto
    qed
    from ftn dom ran show "r \<in> (1..\<zcard>r) \<ztfun> (\<zran> t)" by (mauto(fspace))
  qed
  have concat: "p\<zcat>s\<zcat>r = t"
    apply (simp add: Z_sconcat_assoc [OF pseqX a1 rseqX])
    apply (simp add: sconcatr)
    apply (simp add: pconcatv)
    done
  show "s \<infix> t"
    apply (simp add: sinfix_def)
    apply (witness "p")
    apply (rule conjI)
    apply (rule pseqt)
    apply (witness "r")
    apply (rule conjI)
    apply (rule rseqt)
    apply (rule concat)
    done
qed

lemma sprefix_self:
  assumes a1: "s \<in> \<zseq> X"
  shows "s \<prefix> s"
  apply (simp add: sprefix_def)
  apply (witness "\<sempty>::'a seqT")
  apply (simp add: sempty_seq Z_sconcat_sempty [OF a1])
  done

lemma ssuffix_self:
  assumes a1: "s \<in> \<zseq> X"
  shows "s \<suffix> s"
  apply (simp add: ssuffix_def)
  apply (witness "\<sempty>::'a seqT")
  apply (simp add: sempty_seq Z_sconcat_sempty [OF a1])
  done

lemma sinfix_self:
  assumes a1: "s \<in> \<zseq> X"
  shows "s \<infix> s"
  apply (simp add: sinfix_def)
  apply (witness "\<sempty>::'a seqT")
  apply (simp add: sempty_seq)
  apply (witness "\<sempty>::'a seqT")
  apply (simp add: sempty_seq Z_sconcat_sempty [OF a1])
  done

section {* Indexed Disjoint Partitions *}

(*
lemma Z_iDisjoint_iPartition_redef:
  "\<forall> S T | S \<in> Y \<zpfun> (\<pset> X) \<and> T \<in> \<pset> X \<bullet> 
   (\<iDisjoint> S \<Leftrightarrow> (\<forall> i j | i \<in> \<zdom> S \<and> j \<in> \<zdom> S \<bullet> S\<cdot>i \<inter> S\<cdot>j = \<emptyset>)) \<and>
   (S \<iPartition> T \<Leftrightarrow> (\<iDisjoint> S) \<and> (\<Union>{i | i \<in> \<zdom> S \<bullet> S\<cdot>i} = T))"
*)

lemma Z_iDisjoint_empty:
  "\<iDisjoint> \<emptyset>"
  by (simp add: iDisjoint_def)

lemma iDisjoint_sempty:
  "\<iDisjoint> \<sempty>"
  by (simp add: iDisjoint_def sempty_def)

lemma Z_iDisjoint_sunit:
  "\<iDisjoint> \<lang>x\<rang>"
  apply (simp add: sinsert_def stranslate_sempty)
  apply (simp add: rel_oride_rid sempty_def iDisjoint_def)
  done

lemma disjoint_inter:
  "disjoint A B \<Leftrightarrow> A \<inter> B = \<emptyset>"
  by (auto simp add: disjoint_def)


lemma Z_iDisjoint_sinsert: 
  "\<iDisjoint> \<lang>A, B\<rang> \<Leftrightarrow> A \<inter> B = \<emptyset>"
proof (rule iffI)
  assume b0: "\<iDisjoint> \<lang>A, B\<rang>"
  show "A \<inter> B = {}"
  proof (rule contrapos_pp [OF b0])
    assume c0: "A \<inter> B \<noteq> \<emptyset>"
    show "\<not> \<iDisjoint> \<lang>A, B\<rang>"
      apply (auto simp add: iDisjoint_def disjoint_def)
      apply (witness "1::\<arithmos>")
      apply (witness "A")
      apply (rule conjI)
      apply (simp add: sinsert_def stranslate_sempty)
      apply (simp add: stranslate_def rel_oride_def sempty_def Domain_iff dsub_def)
      apply (witness "2::\<arithmos>")
      apply (witness "B")
      apply (simp add: c0 sinsert_def stranslate_sempty)
      apply (simp add: stranslate_def rel_oride_def sempty_def Domain_iff dsub_def)
      done
  qed
next
  assume b0: "A \<inter> B = \<emptyset>"
  then show "\<iDisjoint> \<lang>A, B\<rang>"
    apply (simp add: sinsert_def stranslate_sempty)
    apply (simp add: stranslate_def rel_oride_def sempty_def Domain_def dsub_def)
    apply (simp add: iDisjoint_def disjoint_def)
    apply (intro allI)
    apply auto
    done
qed

lemma Range_inter:
  "\<Union> \<zran> \<lang>A, B\<rang> = C \<Leftrightarrow> A \<union> B = C"
  apply (simp add: sinsert_def stranslate_sempty)
  apply (simp add: 
            rel_oride_def sempty_def stranslate_def rel_oride_def Domain_iff dsub_def eind_def)
  done

lemma Z_iPartition_sinsert:
  "\<lang>A, B\<rang> \<iPartition> C \<Leftrightarrow> A \<inter> B = \<emptyset> \<and> A \<union> B = C"
  apply (simp add: iPartition_def)
  apply (msafe_no_assms(inference))
proof -
  assume b0: "\<iDisjoint> \<lang>A, B\<rang>" and b1: "\<Union> \<zran> \<lang>A, B\<rang> = C"
  from b0 Z_iDisjoint_sinsert [of A B] show "A \<inter> B = \<emptyset>" by auto
  from b1 Range_inter [of A B] show "A \<union> B = C" by auto
next
  assume b0: "A \<inter> B = \<emptyset>" and b1: "A \<union> B = C"
  from b0 Z_iDisjoint_sinsert [of A B] show "\<iDisjoint> \<lang>A, B\<rang>" by auto
  from b1 Range_inter [of A B] show "\<Union> \<zran> \<lang>A, B\<rang> = C" by auto
qed

section {* Reverse induction *}

text
{*

It is sometimes useful to induct from the end of a sequence rather than the front.  
Case and Induction theorems are presented in order to acheive this; two examples of 
its use are also presented.

*}

lemma seq_rev_exhaust:
  assumes a1: "s \<in> \<zseq> X"
  shows "(\<exists> x xs | xs \<in> \<zseq> X \<and> x \<in> X \<bullet> s = (xs\<zcat>\<lang>x\<rang>)) \<or> (s = \<sempty>)"
proof (rule disjCI)
  assume a2: "s \<noteq> \<sempty>"
  from seq1I [OF a1 a2] have seq1s: "s \<in> \<zseq>\<subone> X" by auto
  show "\<exists> x xs | xs \<in> \<zseq> X \<and> x \<in> X \<bullet> s = (xs\<zcat>\<lang>x\<rang>)"
    apply (witness "\<zlast> s")
    apply (witness "\<zfront> s")
    apply (msafe(inference))
    apply (rule sfront_closed)
    apply (rule seq1I [OF a1 a2])
    apply (rule slast_in_ran)
    apply (rule seq1I [OF a1 a2])
    apply (rule seq1s [THEN sfront_slast_reconstr [THEN sym]])
    done
qed

theorem seq_rev_cases:
  assumes a1: "s \<in> \<zseq> X" and a2: "s = \<sempty> \<turnstile> R"
  and a3: "\<And> xs x \<bullet> \<lbrakk> xs \<in> \<zseq> X; x \<in> X; s = xs\<zcat>\<lang>x\<rang> \<rbrakk> \<turnstile> R"
  shows "R"
  using seq_rev_exhaust [OF a1] a2 a3
  by (auto)

theorem seq_rev_induct:
  assumes 
    A1: "s \<in> \<zseq> X"
  shows
  "P \<sempty> \<turnstile> (\<And>xs x \<bullet> \<lbrakk>xs \<in> \<zseq> X; x \<in> X; P xs\<rbrakk> \<turnstile> P (xs\<zcat>\<lang>x\<rang>)) \<turnstile> P s"
  apply (subst Z_srev_srev [symmetric, OF A1])
thm seq_induct [where ?P = "(\<olambda> x \<bullet> P (srev x))"] 
  apply (rule seq_induct [where ?P = "(\<olambda> x \<bullet> P (srev x))"])
  apply (rule srev_closed [OF A1])
  apply (simp add: Z_srev_sempty)
proof -
  fix xs x
  assume 
    b1: "xs \<in> \<zseq> X" and b2: "x \<in> X" and
    b3: "P (srev xs)" and
    b4: "P \<sempty>" and
    b5: "\<And> xs x \<bullet> \<lbrakk>xs \<in> \<zseq> X; x \<in> X; P xs\<rbrakk> \<turnstile> P (xs\<zcat>\<lang>x\<rang>)"
  have 
    b6: "P ((\<zrev> xs)\<zcat>\<lang>x\<rang>)"
    apply (rule b5, rule srev_closed [OF b1], rule b2)
    apply (rule b3)
    done
  show 
    "P (\<zrev> (\<lang>x\<rang>\<zcat>xs))"
    apply (simp add: Z_srev_sconcat [OF sunit_seq [OF b2] b1])
    apply (simp add: Z_srev_sunit) 
    apply (rule b6)
  done
qed


lemma slast_srev_srev_sfront:
  assumes a1: "s \<in> \<zseq>\<subone> X"
  shows "\<ztail> (\<zrev> s) = \<zrev>(\<zfront> s)"
proof -
  from seq1D [OF a1] have a1': "s \<in> \<zseq> X" by auto
  have "s \<in> \<zseq>\<subone> X \<Rightarrow> \<ztail> (\<zrev> s) = \<zrev>(\<zfront>s)"
  proof (cases "s" rule: seq_rev_cases, rule a1')
    show "s = \<sempty> \<turnstile> s \<in> \<zseq>\<subone> X \<Rightarrow> \<ztail>(\<zrev> s ) = \<zrev>(\<zfront> s)"
      by (simp add: seq1_nonempty sempty_def) apply_end simp
  next apply_end simp apply_end (msafe(inference))
    fix xs x
    assume b0: "xs \<in> \<zseq> X" and b1: "x \<in> X"
    from sunit_seq [OF b1] have b1': "\<lang>x\<rang> \<in> \<zseq> X" 
      by auto
    have "\<ztail> (\<zrev>(xs\<zcat>\<lang>x\<rang>)) = \<ztail>((\<zrev> \<lang>x\<rang>)\<zcat>(\<zrev> xs))" 
      by (simp add: Z_srev_sconcat [OF b0 b1'])
    also have "\<dots> = \<ztail> (\<lang>x\<rang>\<zcat>\<zrev> xs)" 
      by (simp add: Z_srev_sunit)
    also have "\<dots> = \<zrev> xs" 
      by (simp add: sunit_sconcat_stail [OF srev_closed [OF b0] b1])
    finally have b2: "\<ztail> (\<zrev>(xs\<zcat>\<lang>x\<rang>)) = \<zrev> xs" 
      by auto 
    show "\<ztail>(\<zrev> (xs\<zcat>\<lang>x\<rang>)) = \<zrev> (\<zfront> (xs\<zcat>\<lang>x\<rang>))"
      apply (cases "xs = \<sempty>")
      apply (subst b2)
      apply (simp add: Z_srev_sempty Z_sconcat_sempty [OF b1'])
      apply (simp add: sfront_sunit [OF b1] Z_srev_sempty)
    proof -
      assume c0: "xs \<noteq> \<sempty>"
      from seq1I [OF b0 c0] have c1: "xs \<in> \<zseq>\<subone> X" 
        by auto
      have c2: " \<zrev> (\<zfront>(xs\<zcat>\<lang>x\<rang>)) = \<zrev> xs" 
        by (simp add: sfront_sconcat_sunit [OF b0 b1])
      from b2 c2 show "\<ztail>(\<zrev>(xs\<zcat>\<lang>x\<rang>)) = \<zrev>(\<zfront>(xs\<zcat>\<lang>x\<rang>))" 
        by auto
    qed
  qed
  with a1 show ?thesis by auto
qed


lemma slast_sconcat:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq>\<subone> X"
  shows "\<zlast> (s\<zcat>t) = \<zlast> t"
proof -
  from seq1D [OF a2] have a2': "t \<in> \<zseq> X" by auto
  have "t \<in> \<zseq>\<subone> X \<Rightarrow> \<zlast> (s\<zcat>t) = \<zlast> t"
  proof (cases "t" rule: seq_rev_cases)
    show "t \<in> \<zseq> X" by (rule a2')
    show "t = \<sempty> \<turnstile> t \<in> \<zseq>\<subone> X \<Rightarrow> \<zlast> (s\<zcat>t) = \<zlast> t" by (simp add: seq1_nonempty sempty_def)
    apply_end simp
  next
    apply_end simp
    apply_end (msafe(inference))
    fix xs x
    assume b0: "xs \<in> \<zseq> X" and b1: "x \<in> X"
    from sunit_seq [OF b1] have b1': "\<lang>x\<rang> \<in> \<zseq> X" 
      by auto
    have "\<zlast> (s\<zcat>(xs\<zcat>\<lang>x\<rang>)) = \<zlast> ((s\<zcat>xs)\<zcat>\<lang>x\<rang>)" 
      by (simp add: Z_sconcat_assoc [OF a1 b0 b1'])
    also have "\<dots> = x" 
      by (simp add: slast_sconcat_sunit [OF sconcat_closed [OF a1 b0] b1])
    finally have b2: "\<zlast> (s\<zcat>(xs\<zcat>\<lang>x\<rang>)) = x" 
      by auto
    have b3: "\<zlast> (xs\<zcat>\<lang>x\<rang>) = x" 
      by (simp add: slast_sconcat_sunit [OF b0 b1])
    from b2 b3 show "\<zlast> (s\<zcat>(xs\<zcat>\<lang>x\<rang>)) = \<zlast> (xs\<zcat>\<lang>x\<rang>)" 
      by auto
  qed
  with a2 show ?thesis by auto
qed


lemma Z_slast_sfront_sconcat:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "t \<noteq> \<sempty> \<Rightarrow> \<zlast> (s \<zcat> t) = \<zlast> t \<and> \<zfront> (s \<zcat> t) = s \<zcat> (\<zfront> t)"
proof (msafe(inference))
  assume b0: "t \<noteq> \<sempty>"
  from seq1I [OF a2 b0] have a2': "t \<in> \<zseq>\<subone> X" by this
  show "\<zlast> (s \<zcat> t) = \<zlast> t" by (rule slast_sconcat [OF a1 a2'])
  show "\<zfront> (s \<zcat> t) = s \<zcat> (\<zfront> t)" by (rule sfront_sconcat [OF a1 a2'])
qed


section {* Converting a function to a sequence *}

text {*

(pg. 118)
We can create a sequence @{text "\<squash> f"} from a function 
@{text "f \<in> \<nat> \<zpfun> X"}, by translating its domain using the @{text "bounded_card"} function.  The inverse of this function is used to show monotonicity of the Squash function.

*}

definition
  bounded_card :: "[\<arithmos> set, \<arithmos>] \<rightarrow> \<arithmos>"
where
  bounded_card_def: "bounded_card A n \<defs> (zcard {i::\<arithmos> | (i \<in> A) \<and> (i < n)})"

fun
  inv_bounded_card :: "[\<arithmos> set, \<nat>] \<rightarrow> \<arithmos>"
where
  inv_bounded_card_0: "inv_bounded_card A 0 = Min A"
| inv_bounded_card_Suc: "inv_bounded_card A (Suc n) = inv_bounded_card (A \<setminus> {Min A}) n"

definition
  ssquash :: "(\<arithmos> \<leftrightarrow> 'a) \<rightarrow> (\<arithmos> \<leftrightarrow> 'a)"
where
  ssquash_def : "ssquash f \<defs> {x | x \<in> \<zdom> f \<bullet> ( (bounded_card (\<zdom> f) x + 1) \<zmapsto> f\<cdot>x)}" 

notation (zed)
  ssquash ("\<squash>")

lemma conj_inter:
  "{i::\<arithmos> | (P i) \<and> (Q i)} = {i::\<arithmos> | P i} \<inter> {i::\<arithmos> | Q i}"
by auto

lemma zNats_decD:
  assumes a1: "x - 1 \<in> \<nat>"
  shows "x \<in> \<nat>"
proof -
  from zInts_add [OF zInts_zNats [OF a1] zInts_1]
  have b1: "x \<in> \<int>"
    by (auto)
  from a1 have "0 \<le> x - 1"
    by (auto simp add: zNats_def)
  then have "0 \<le> x"
    by (auto)
  with b1 show ?thesis
    by (rule zNats_0_le_zInts)
qed

lemma zInts_decD:
  assumes a1: "x - 1 \<in> \<int>"
  shows "x \<in> \<int>"
  using zInts_add [OF a1 zInts_1]
  by (auto)

lemma bounded_card_inj_on:
  assumes a1: "finite A"
  shows "inj_on (bounded_card A) A"
  proof (simp add: inj_on_def,msafe(inference))
  fix x1 x2
  assume b1: "x1 \<in> A" and b2: "x2 \<in> A"
  and b3: "bounded_card A x1 = bounded_card A x2"
  let ?s1 = "{i::\<arithmos> | (i \<in> A) \<and> (i < x1)}"
  let ?s2 = "{i::\<arithmos> | (i \<in> A) \<and> (i < x2)}"
  show "x1 = x2"
  proof (insert linorder_less_linear [where ?x = "x1" and ?y = "x2"], msafe(inference))
    assume Ac1: "x1 < x2"
    with b1 have "x1 \<in> ?s2 \<and> x1 \<notin> ?s1" by (auto)
    then have
    "?s1 \<subset> ?s2"  
    by (auto)
    then have
    "\<zcard>?s1 < \<zcard>?s2"
      apply (simp add: zcard_def)
      apply (intro psubset_card_mono)
      apply (simp_all add: conj_inter)
      apply (intro finite_Int, intro disjI1)
      apply (rule a1)
    done 
    then show ?thesis
    by (insert b3, auto simp add: bounded_card_def)
  next
    assume Ac1: "x2 < x1"
    with b2 have "x2 \<in> ?s1 \<and> x2 \<notin> ?s2" by (auto)
    then have
    "?s2 \<subset> ?s1"
    by (auto)
    then have
    "\<zcard>?s2 < \<zcard>?s1"
      apply (simp add: zcard_def)
      apply (intro psubset_card_mono)
      apply (simp_all add: conj_inter)
      apply (intro finite_Int, intro disjI1)
      apply (rule a1)
    done
    then show ?thesis
    by (insert b3, auto simp add: bounded_card_def)
  qed
qed

lemma inv_bounded_card_in:
  "\<forall> A \<bullet> finite A \<Rightarrow> x < \<card>A \<Rightarrow> inv_bounded_card A x \<in> A"
proof (rule nat_induct, simp_all)
apply_end (msafe(inference))
  fix x :: \<nat>
  and A :: "\<arithmos> set"
  assume Aa1: "finite A"
  and Aa2: "0 < \<card>A"
  then have
    "A \<noteq> \<emptyset>"
  by auto
  with Aa1 show
  "Min A \<in> A"
  by auto
next
  fix x :: \<nat>
  and A :: "\<arithmos> set"
  assume Aa1: "\<forall> A \<bullet> finite A \<Rightarrow> x < \<card>A \<Rightarrow> inv_bounded_card A x \<in> A"
  assume Aa2: "finite A"
  assume Aa3: "Suc x < \<card>A"
  let ?A' = "A \<setminus> {Min A}"

  from Aa2 have b0: "finite ?A'" by auto
  from Aa2 Aa3 have b1: "A \<noteq> \<emptyset>" by auto
  with Aa2 Aa3 have b2: "x < \<card>?A'"
    by (auto simp add: Aa2 [THEN card_Diff_singleton])

  from b0 b2 have b3: "inv_bounded_card ?A' x \<in> ?A'"
    apply (intro Aa1 [rule_format])
    apply simp_all
    done
  then show
  "inv_bounded_card ?A' x \<in> A"
  by auto
qed                

lemma inv_bounded_card_in_better:
  assumes A1: "finite A" and A2: "x \<in> (1..(\<zcard>A))" 
  shows "inv_bounded_card A (nat_of (x - 1)) \<in> A"
proof -
  from A2 have Ra1:
  "x \<in> zNats \<and> 1 \<le> x \<and> x \<le> zcard A"
  by (simp add: Z_zNats_zInts_conv)
  with A2 show ?thesis
    apply (intro inv_bounded_card_in [rule_format, OF A1])
    apply (simp add:  zNats_zcard [THEN zNats_1 [THEN zint_range_of_nat]])
    apply (auto simp add: nat_of_norm zNats.Abs_inverse nat_of_zcard)
  done
qed



lemma bounded_card_inverse:
  "\<forall> A \<bullet> finite A \<Rightarrow> x < \<card>A \<Rightarrow> bounded_card (A) (inv_bounded_card A x) = (of_nat x)"
   apply (rule nat_induct)
   apply (simp_all add: bounded_card_def zcard_def real_of_nat_def [symmetric] real_of_nat_Suc [symmetric] not_less)
   apply (msafe(inference))
proof -
  fix n :: "\<nat>" and A :: "\<arithmos> set"
  assume 
    b1: "\<forall> A \<bullet> finite A \<Rightarrow> n < \<card>A \<Rightarrow> \<card>{ i | i \<in> A \<and> i < inv_bounded_card A n } = n" and
    b2: "finite A" and b3: "Suc n < \<card>A"
  from b2 have b4: "finite (A \<setminus> {Min A})"
    by (auto)
  have b5a: "(\<forall> n A | n < \<card> A \<bullet> A \<noteq> \<emptyset>)"
    by (auto)
  from b5a [rule_format, OF b3] have b5: "A \<noteq> \<emptyset>"
    by (this)
  with b2 have b6: "Min A \<in> A"
    by (rule Min_in)
  with b3 b2 have b7: "n < \<card>(A \<setminus> {Min A})"
    by (auto simp add: card_Diff_singleton)
  from b5a [rule_format, OF b7]  have b8: "(A \<setminus> {Min A}) \<noteq> \<emptyset>"
    by (this)
  from b6 have "{ i | i \<in> A \<and> i < inv_bounded_card (A \<setminus> {Min A}) n }
  = { i | i \<in> (A \<setminus> {Min A}) \<and> i < inv_bounded_card (A \<setminus> {Min A}) n } \<union> { i | i \<in> ({Min A}) \<and> i < inv_bounded_card (A \<setminus> {Min A}) n }"
    by (auto)
  also have "{ i | i \<in> ({Min A}) \<and> i < inv_bounded_card (A \<setminus> {Min A}) n }
  = {Min A}"
  proof (auto)
    from inv_bounded_card_in [rule_format, OF b4 b7]
    have c1: "inv_bounded_card (A \<setminus> {Min A}) n \<in> A" and
      c2: "inv_bounded_card (A \<setminus> {Min A}) n \<noteq> Min A"
      by (auto)
    from  Min_le [OF b2 c1] c2
    show "Min A < inv_bounded_card (A \<setminus> {Min A}) n"
      by (auto)
  qed
  finally have b9: 
    "{ i | i \<in> A \<and> i < inv_bounded_card (A \<setminus> {Min A}) n }
    = insert (Min A) { i | i \<in> (A \<setminus> {Min A}) \<and> i < inv_bounded_card (A \<setminus> {Min A}) n }"
    by (auto)
  have 
    "\<card>{ i | i \<in> A \<and> i < inv_bounded_card (A \<setminus> {Min A}) n }
    = Suc (\<card>{ i | i \<in> (A \<setminus> {Min A}) \<and> i < inv_bounded_card (A \<setminus> {Min A}) n })"
    apply (subst b9)
    apply (auto)
    apply (rule card_insert_disjoint)
    apply (auto)
    apply (rule finite_subset [OF _ b2])
    apply (auto)
    done
  with b1 [rule_format, OF b4 b7] show "\<card>{ i | i \<in> A \<and> i < inv_bounded_card (A \<setminus> {Min A}) n } = Suc n"
    by (simp)
qed

lemma bounded_card_inverse_better:
  assumes 
    A1: "finite A" and 
    A2: "x \<in> (0..(\<zcard>A - 1))" 
  shows
    "bounded_card (A) (inv_bounded_card A (nat_of x)) = x"
proof -
  from A2 have 
    Ra1:  "x \<in> zNats \<and> x < zcard A"
    by (simp add: Z_zNats_zInts_conv zNats_decD)
  then have
    "x = of_nat (nat_of x)"
    by (simp add: zNats.Abs_inverse)
  also from Ra1 have
  "... = bounded_card A (inv_bounded_card A (nat_of x))"
    apply (intro bounded_card_inverse [rule_format, OF A1, THEN sym])
    apply (simp add: nat_of_zcard [symmetric,  where ?'a = "\<arithmos>"] nat_of_less_iff)
    done
  finally show ?thesis 
    by auto
qed

lemma ssquash_bounded_card_finite:
  assumes a1: "finite f" and a2: "(n::\<arithmos>) \<in> \<zdom> f"
  shows "finite {i::\<arithmos> | (i \<in> \<zdom> f) \<and> (i < n)}"
proof -
  have b1: "{i::\<arithmos> | (i \<in> \<zdom> f) \<and> (i < n)} \<subseteq> {i | i \<in> \<zdom> f}" by (auto)
  from fun_finite_dom [OF a1] have b2: "finite {i | i \<in> \<zdom> f}" by (auto)
  from b1  b2 show ?thesis by (simp add: finite_subset [OF b1 b2])
qed


lemma ssquash_bounded_card_monotonic:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  and a3: "n1 \<in> \<zdom> f" and a4: "n2 \<in> \<zdom> f" and a5: "n1 < n2"
  shows "bounded_card (\<zdom> f) n1 < bounded_card (\<zdom> f) n2"
proof -
  from a5 have b1: "{i | (i \<in> \<zdom> f) \<and> (i < n1)} \<subseteq> {i | (i \<in> \<zdom> f) \<and> (i < n2)}"
    by (auto)
  have b2: "n1 \<notin> {i | (i \<in> \<zdom> f) \<and> (i < n1)}" by (auto)
  from a3 a5 have b3: "n1 \<in> {i | (i \<in> \<zdom> f) \<and> (i < n2)}" by (auto)
  from b2 b3 have b4: "{i | (i \<in> \<zdom> f) \<and> (i < n1)} \<subset> {i | (i \<in> \<zdom> f) \<and> (i < n2)}"
    by (auto)
  have b5: "finite {i | (i \<in> \<zdom> f) \<and> (i < n2)}"
    by (simp add: ssquash_bounded_card_finite [OF a1 a4]) 
  have b6: "\<card>{i | (i \<in> \<zdom> f) \<and> (i < n1)} < \<card>{i | (i \<in> \<zdom> f) \<and> (i < n2)}"
    by (simp add: psubset_card_mono [OF b5 b4])
  show ?thesis
    apply (simp add: bounded_card_def zcard_def)
    apply (simp add: b6)
  done
qed

lemma ssquash_existsone:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  and a3: "n \<in> \<zdom> f" and a4: "x = bounded_card (\<zdom> f) n + 1"
  shows "\<lbrakk> k \<in> \<zdom> f; x = bounded_card (\<zdom> f) k + 1; y = f\<cdot>k \<rbrakk> \<turnstile> y = f\<cdot>n"
proof -
  fix k
  assume a5: "x = bounded_card (\<zdom> f) k + 1" "y = f\<cdot>k" "k \<in> \<zdom> f"
  from a4 a5 have b1: "bounded_card (\<zdom> f) n = bounded_card (\<zdom> f) k" and b2: "y = f\<cdot>k" and b3: "k \<in> \<zdom> f"
    by (auto)
  from a1 have b4: "finite (\<zdom> f)" by (simp add: fun_finite_dom)
  have b5: "k = n"
    apply (insert a3 a4 b1 b2 b3)
    apply (insert bounded_card_inj_on [OF b4])
    apply (simp add: inj_on_def)
    done
  from b2 b5 show "y = f\<cdot>n"
    by (auto)
qed

lemma ssquash_sempty:
  "\<squash> \<sempty> = \<sempty>"
  by (auto simp add: ssquash_def bounded_card_def sempty_def)

lemma ssquash_fun:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  shows "functional (\<squash> f)"
proof -
  from a2 have b1: "functional f" by ((mauto(fspace)))
  show ?thesis
    apply (simp add: functional_def single_val_def)
    apply (auto)
  proof -
    fix x y1 y2
    assume c1: "(x \<mapsto> y1) \<in> \<squash> f" and c2: "(x \<mapsto> y2) \<in> \<squash> f"
    from c1 obtain n where c3: "x = (bounded_card (\<zdom> f) n) + 1" and c4: "n \<in> \<zdom> f"
      apply (simp add: ssquash_def)
      apply (auto)
      done
    have c5: "y1 = f\<cdot>n"
      apply (insert c1)
      apply (simp add: ssquash_def)
      apply (mauto_no_assms(inference) msimp add: ssquash_existsone [OF a1 a2 c4 c3])
      done
    have c6: "y2 = f\<cdot>n"
      apply (insert c2)
      apply (simp add: ssquash_def)
      apply (mauto_no_assms(inference) msimp add: ssquash_existsone [OF a1 a2 c4 c3])
      done
    from c5 c6 show "y1 = y2"
      by (auto)
  qed
qed

lemma ssquash_image:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  shows "\<squash> f = (\<olambda> n \<bullet> (bounded_card (\<zdom> f) n + 1 \<mapsto> f\<cdot>n)) \<lparr> (\<zdom> f) \<rparr>"
  apply (auto simp add: image_def)
proof -
  fix a b
  assume a3: "(a \<mapsto> b) \<in> \<squash> f"
  show "\<exists> x \<bullet> (x \<in> \<zdom> f) \<and> (a = bounded_card (\<zdom> f) x + 1) \<and> (b = f\<cdot>x)"
    apply (insert a3)
    apply (simp add: ssquash_def)
    apply (auto)
    done
next
  fix x y
  assume a3: "(x \<mapsto> y) \<in> f"
  from a3 have b1: "x \<in> \<zdom> f" 
    by (auto)
  show "(bounded_card (\<zdom> f) x + 1 \<mapsto> f\<cdot>x) \<in> \<squash> f"
    apply (insert b1)
    apply (simp only: ssquash_def)
    apply (auto)
    done
qed

lemma ssquash_finite:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  shows "finite (\<squash> f)"
  apply (simp add: ssquash_image [OF a1 a2])
  apply (insert fun_finite_dom [OF a1])
  apply (auto)
  done

lemma ssquash_bounded_card_ran:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X" and a3: "n \<in> \<zdom> f"
  shows "bounded_card (\<zdom> f) n + 1 \<in> (1..(\<zcard>f))"
proof -
  from a2 have b1: "functional f" by ((mauto(fspace)))
  from a3 have b2: "{i | (i \<in> \<zdom> f) \<and> (i < n)} \<subseteq> \<zdom> f"
    by (auto)
  have b3: "n \<notin> {i | (i \<in> \<zdom> f) \<and> (i < n)}" by (auto)
  from a3 b3 b2 have b4: "{i | (i \<in> \<zdom> f) \<and> (i < n)} \<subset> \<zdom> f" by (auto)
  have b5: "\<zcard>{i | (i \<in> \<zdom> f) \<and> (i < n)} < \<zcard>f"
    apply (simp only: zcard_def fun_card_dom [OF b1])
    apply (simp add: psubset_card_mono [OF fun_finite_dom [OF a1] b4])
    done
  then show ?thesis
    apply (simp add: bounded_card_def)
    apply (msafe(inference))
    apply (simp add: zcard_def)
    apply (simp add: zcard_def)
    apply (subst zInts_le_add1_eq_le [THEN sym])
    apply (auto simp add: zcard_def)
  done
qed

lemma ssquash_dom:
   assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>]  \<zpfun> X"
   shows "\<zdom> (\<squash> f) = (1..(\<zcard>f))"
proof -
  have 
    "\<zdom> (\<squash> f) 
    = {x | x \<in> \<zdom> f \<bullet> bounded_card (\<zdom> f) x + 1}"
    by (simp add: ssquash_def set_eqI Domain_iff)
  also have "... 
    = (1..(\<zcard>f))"
    apply (rule set_eqI)
    apply (msafe(inference))
  proof -
    fix x :: \<arithmos>
    assume Ab1: "x \<in> {x | x \<in> \<zdom> f \<bullet> bounded_card (\<zdom> f) x + 1}"
    then show 
      "x \<in> (1..(\<zcard>f))"
      apply (simp)
      apply (mauto(inference) mdest!: ssquash_bounded_card_ran [OF a1 a2])
      apply (auto)
      done
  next
    fix x :: \<arithmos>
    assume "x \<in> (1..(\<zcard>f))"
    then have Ab1: "x - 1 \<in> 0..((\<zcard>f) - 1)"
      by (auto)
    let ?x = "inv_bounded_card (\<zdom> f) (nat_of (x - 1))"
    from a2 have 
      Rb1: "\<zcard>f = \<zcard>(\<zdom>f)"
      apply (intro fun_zcard_dom)
      apply (mauto(fspace))
      done
    with Ab1 have Ab2: "x - 1 \<in> 0..((\<zcard>(\<zdom> f)) - 1)"
      by (simp)
    from bounded_card_inverse_better [OF a1 [THEN fun_finite_dom] Ab2] have 
      Rb2: "x = bounded_card (\<zdom> f) ?x + 1"
      by (auto)
    from Ab1 Rb1 have 
      Rb3: "?x \<in> \<zdom> f"
      apply (intro inv_bounded_card_in_better)
      apply (rule a1 [THEN fun_finite_dom])
      apply (auto dest: zInts_decD)
      done
    with Rb2 Rb3 show
      "x \<in> {x | x \<in> \<zdom> f \<bullet> bounded_card (\<zdom> f) x + 1}"
      by auto
  qed
  finally show ?thesis 
    by (this)
qed


lemma ssquash_ran:
  assumes a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  shows "\<zran> (\<squash> f) \<subseteq> X"
proof -
  from a2 have b1: "\<zran> f \<subseteq> X" by ((mauto(fspace)))
  show ?thesis
    apply (simp add: ssquash_def)
    apply (insert b1)
    apply (auto)   
    apply (insert a2)
    apply auto
  done
qed

lemma ssquash_ran_function:
  assumes a1: "functional f"
  shows "\<zran> f = \<zran> (\<squash> f)"
  apply (simp add: ssquash_def)
  apply (auto simp add: set_eq_def Range_iff Domain_iff)
proof -
  fix x y
  assume b0: "(y, x) \<in> f"
  have b1: "f\<cdot>y = x" by (intro functional_beta [OF a1 b0])
  show "\<exists> xa \<bullet> x = f\<cdot>xa \<and> (\<exists> y \<bullet> (xa, y) \<in> f)"
    apply (witness "y")
    apply (intro conjI)
    apply (rule b1 [THEN sym])
    apply (witness "x")
    apply (rule b0)
    done
next
  fix xa y
  assume b0: "(xa, y) \<in> f"
  have b1: "f\<cdot>xa = y" by (intro functional_beta [OF a1 b0])
  show "\<exists> x \<bullet> (x, f\<cdot>xa) \<in> f"
    apply (witness "xa")
    apply (subst b1)
    apply (rule b0)
    done
qed

lemma ssquash_closed:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  shows "\<squash> f \<in> \<zseq> X"
proof (rule seqIa [where ?n = "\<zcard>f", OF zNats_zcard])
 show "\<squash> f \<in> (1..(\<zcard>f)) \<ztfun> X"
   apply ((mauto(fspace)))
   apply (rule ssquash_fun [OF a1 a2])
   apply (rule ssquash_dom [OF a1 a2])
   apply (rule ssquash_ran [OF a2])
   done
qed

lemma ssquash_zcard:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  shows "\<zcard>(\<squash> f) = \<zcard>f"
  apply (simp add: ssquash_image [OF a1 a2])
  using a2
  apply (mauto(fspace))
  apply (simp add: fun_zcard_dom)
  apply (rule zcard_image) 
  apply (rule inj_onI)
  apply (rule inj_onD [OF bounded_card_inj_on [OF fun_finite_dom [OF a1]]])
  apply (auto)
  done

lemma ssquash_unit_set:
  assumes a1: "A = {(k, x)}"
  shows "\<squash> A = {(1, x)}"
  apply (insert a1)
  apply (auto simp add: ssquash_def bounded_card_def Domain_iff eind_def)
  defer
  apply (intro functional_beta)
  apply (auto intro!: functionalI)
proof -
  have b0: "{i | i = k \<and> i < k} = {}" by auto
  from a1 show 
    "\<zcard>{i | i = k \<and> i < k} = 0"
    by (simp add: b0)
qed


lemma ssquash_appl:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X" and a3: "n \<in> (1..(\<zcard>f))"
  shows "(n, (\<squash> f)\<cdot>n) \<in> \<squash> f" 
  apply (rule seq_appl)
  apply (rule ssquash_closed [OF a1 a2])
  apply (insert a3, simp_all add: ssquash_zcard [OF a1 a2])
done

lemma ssquash_beta_function2:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X" and a3: "(a, b) \<in> f"
  shows "(\<squash> f)\<cdot>(bounded_card (\<zdom> f) a + 1) = f\<cdot>a"
  apply (intro functional_beta)
  apply (intro seq_functional [OF ssquash_closed [OF a1 a2]])
  apply (simp add: ssquash_def)
  apply (witness "a")
  apply simp
  apply (insert a3)
  apply auto
  done

lemma ssquash_beta:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X" and a3: "(a \<mapsto> b) \<in> \<squash> f"
  shows "(\<squash> f)\<cdot>a = b"
proof -
  have b1: "\<squash> f \<in> \<zseq> X" 
    by (simp add: ssquash_closed [OF a1 a2])
  show ?thesis by (simp add: seq_beta [OF b1 a3])
qed

lemma ssquash_dom_image:
  shows "\<zdom> (\<squash> f) = (\<olambda> r \<bullet> (bounded_card (\<zdom> f) r + 1))\<lparr>\<zdom> f\<rparr>" 
  by (auto simp add: image_def ssquash_def Domain_iff eind_def)

lemma ssquash_beta_function:
  assumes a1: "finite f" and a2: "f \<in> \<univ>-[\<arithmos>] \<zpfun> X" and a3: "(a, b) \<in> \<squash> f"
  shows "(\<squash> f)\<cdot>a = f\<cdot>(inv_bounded_card (\<zdom> f) (nat_of (a - 1)))"
  apply (rule functional_beta)
  apply (rule ssquash_fun [OF a1 a2])
proof-
  let ?x = "inv_bounded_card (\<zdom> f) (nat_of (a - 1))"
  from a2 have Rb1:
  "\<zcard>f = \<zcard>(\<zdom>f)"
    apply (intro fun_zcard_dom)
    apply (mauto(fspace))
  done
  from a3 ssquash_dom [OF a1 a2] have Rb2: 
  "a \<in> (1..(\<zcard>f))"
  by auto
  from Rb1 Rb2 have Rb3:
  "?x \<in> \<zdom> f"
    apply (intro inv_bounded_card_in_better)
    apply (rule a1 [THEN fun_finite_dom])
    apply simp
  done
  from Rb1 Rb2 Rb3 show 
  "(a, f\<cdot>?x) \<in> \<squash> f"
    apply (simp add: ssquash_def)
    apply (witness "?x")
    apply simp_all
    apply (subst bounded_card_inverse_better [rule_format])
    apply (rule a1 [THEN fun_finite_dom])
    apply (auto)
  done
qed


lemma ssquash_union:
  assumes a1: "finite A" and a2: "A \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  and a3: "finite B" and a4: "B \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  shows "\<forall> a b | a \<in> \<zdom> A \<and> b \<in> \<zdom> B \<bullet> a < b \<turnstile> \<squash> (A \<union> B) = (\<squash> A) \<union> stranslate (\<squash> B) (\<zcard>(\<squash> A))"
proof -
  assume disjdom: "\<forall> a b | a \<in> \<zdom> A \<and> b \<in> \<zdom> B \<bullet> a < b"
  from a2 have funA: "functional A" 
    by (mauto(fspace))
  from disjdom have disjdom2: "\<forall> a b | a \<in> \<zdom> A \<and> b \<in> \<zdom> B \<bullet> a < b" 
    by auto
  from a1 a3 have finAuB: "finite (A \<union> B)" 
    by (auto)
  from a2 a4 disjdom have funAuB: "(A \<union> B) \<in> \<univ>-[\<arithmos>] \<zpfun> X" 
    apply (mauto(fspace))
    apply (auto simp add: dres_def Domain_iff eind_def)
    done
  have 
    Ra1: "stranslate (\<squash> B) (\<zcard>A) = (\<olambda> n \<bullet> (bounded_card (\<zdom> B) n + \<zcard>A + 1, B\<cdot>n))\<lparr> \<zdom> B \<rparr>"
    apply (auto)
    apply (auto simp add: ssquash_image [OF a3 a4] stranslate_conv Z_rel_fcomp_mem image_def)
    done
  show ?thesis
    apply (simp add: ssquash_zcard [OF a1 a2])
    apply (simp add: ssquash_image [OF a1 a2])
    apply (simp add: Ra1)
    apply (simp add: ssquash_image [OF finAuB funAuB])
  proof -
  have c0: "(\<olambda> n \<bullet> (bounded_card (\<zdom> (A \<union> B)) n + 1, (A \<union> B)\<cdot>n))\<lparr> \<zdom> A \<rparr> 
  = (\<olambda> n \<bullet> (bounded_card (\<zdom> A) n + 1, A\<cdot>n))\<lparr> \<zdom> A \<rparr>"
    apply (rule image_cong)
    apply simp_all
    apply (msafe(inference))
  proof -
    fix x
    assume d1: "x \<in> \<zdom> A"
    have e1: "\<forall> i | i < x  \<and>  i \<in> \<zdom> (A\<union>B)\<bullet> i \<notin> \<zdom>B"
      apply (msafe(inference))
      apply (rule contrapos_pn, assumption)
      proof -
        fix i
        assume f2: "i \<in> \<zdom> (A \<union> B)" and f3: "i \<in> \<zdom> B"
        from disjdom f3 d1 have "x < i" by auto
        then show "\<not> (i < x)" by auto
      qed
    have e2: "{i | i \<in> Domain (A \<union> B) \<and> i < x} = {i | i  \<in> \<zdom> A \<and> i < x}"
      apply (insert e1)
      apply auto
      done
    then show "bounded_card (Domain (A \<union> B)) x = bounded_card (Domain A) x" 
      by (simp add: bounded_card_def)
  next
    fix x
    assume f1: "x \<in> \<zdom> A"
    from f1 disjdom have e2: "\<forall> b | b \<in> \<zdom> B \<bullet> x < b" by (auto)
    from e2 have e3: "x \<notin> \<zdom> B" by auto
    from f1 have e4: "(x, A\<cdot>x) \<in> A"
      apply (intro functional_appl) 
      apply (insert a2) 
      apply ((mauto(fspace))) 
      done
    from e3 e4 show "(A \<union> B)\<cdot>x = A\<cdot>x" 
      apply (intro functional_beta) 
      apply (insert funAuB) 
      apply ((mauto(fspace))) 
      done
  qed
  have c1: "(\<olambda> n \<bullet> (bounded_card (\<zdom> (A \<union> B)) n + 1, (A \<union> B)\<cdot>n))\<lparr> \<zdom> B \<rparr> 
  = (\<olambda> n \<bullet> (bounded_card (\<zdom> B) n + \<zcard>A + 1, B\<cdot>n))\<lparr> \<zdom> B \<rparr>"
    apply (rule image_cong)
    apply simp_all
    apply (msafe(inference))
  proof -
    fix x
    assume d1: "x \<in> \<zdom> B"
    have r1: "{i | i \<in> \<zdom> (A \<union> B) \<and> i < x } = {k | k \<in> \<zdom> A} \<union> {s | s \<in> \<zdom> B \<and> s < x}"
      apply (insert disjdom d1)
      apply auto
      done
    have r2: "\<zdom> A Int {s | s \<in> \<zdom> B \<and> s < x} = \<emptyset>"
      apply (insert disjdom d1)
      apply auto
      done
    from d1 have r3: "{s | s \<in> \<zdom> B \<and> s < x} \<subseteq> \<zdom> B" by auto
    from a3 have r4: "finite (\<zdom> B)" by (simp add: fun_finite_dom)
    from r3 r4 have r5: "finite {s | s \<in> \<zdom> B \<and> s < x}" by (simp add: finite_subset)
    from a1 have r6: "finite (\<zdom> A)" by (simp add: fun_finite_dom)
    from r2 r3 r4 r5 r6 have 
      r7: "\<zcard>(Domain A \<union> {s | s \<in> \<zdom> B \<and> s < x}) = \<zcard>(\<zdom> A) + \<zcard>{s | s \<in> \<zdom> B \<and> s < x}"
      apply (intro zcard_union_disjoint)
      apply (msafe(inference))
    done
    show "bounded_card (\<zdom> (A \<union> B)) x = bounded_card (\<zdom> B) x + \<zcard>A"
      apply (simp add: bounded_card_def)
      apply (simp add: r1)
      apply (insert r2 a1 a3)
      apply (simp add: r7)
      apply (rule fun_zcard_dom [OF funA, THEN sym])
    done
  next
    fix x
    assume y1: "x \<in> \<zdom> B"
    from y1 disjdom2 have y2: "\<forall> a | a \<in> \<zdom> A \<bullet> a < x" by auto
    from y2 have y3: "x \<notin> \<zdom> A" by auto
    from y1 have y4: "(x, B\<cdot>x) \<in> B" 
      apply (intro functional_appl) 
      apply (insert a4) 
      apply ((mauto(fspace))) 
      done
    from y3 y4 show "(A \<union> B)\<cdot>x = B\<cdot>x" 
      apply (intro functional_beta) 
      apply (insert funAuB) 
      apply ((mauto(fspace))) 
      done
  qed
  have "(\<olambda> n \<bullet> (bounded_card (\<zdom> (A \<union> B)) n + 1, (A \<union> B)\<cdot>n)) \<lparr> (\<zdom> (A \<union> B))\<rparr> 
  = (\<olambda> n \<bullet> (bounded_card (\<zdom> (A \<union> B)) n + 1, (A \<union> B)\<cdot>n))\<lparr> \<zdom> A \<union> \<zdom> B\<rparr>" 
    by auto 
  also have "\<dots> 
  =  (\<olambda> n \<bullet> (bounded_card (\<zdom> (A \<union> B)) n + 1, (A \<union> B)\<cdot>n))\<lparr>(\<zdom> A)\<rparr> \<union> 
     (\<olambda> n \<bullet> (bounded_card (\<zdom> (A \<union> B)) n + 1, (A \<union> B)\<cdot>n))\<lparr> (\<zdom> B) \<rparr>"
    by (simp add: image_Un)
  also from c0 c1 have "\<dots> 
  = (\<olambda> n \<bullet> (bounded_card (\<zdom> A) n + 1, A\<cdot>n))\<lparr>\<zdom> A\<rparr> \<union> 
    (\<olambda> n \<bullet> (bounded_card (\<zdom> B) n + \<zcard>A + 1, B\<cdot>n))\<lparr> \<zdom> B \<rparr> "   
    by (auto)
  finally show 
    "(\<olambda> n \<bullet> (bounded_card (Domain (A \<union> B)) n + 1, (A \<union> B)\<cdot>n))\<lparr>Domain (A \<union> B)\<rparr> 
    = (\<olambda> n \<bullet> (bounded_card (Domain A) n + 1, A\<cdot>n))\<lparr>Domain A\<rparr> \<union> 
      (\<olambda> n \<bullet> (bounded_card (Domain B) n + \<zcard>A + 1, B\<cdot>n))\<lparr>Domain B\<rparr>" 
    by auto
  qed
qed


lemma ssquash_stranslate_function:
  assumes a1: "finite s" and a2: "s \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  shows "\<squash> (stranslate s k) = \<squash> s"
proof -
  have b0: "\<zdom> (stranslate s k) = (\<olambda> n \<bullet> n + k)\<lparr>\<zdom> s \<rparr>"
    by (auto simp add: stranslate_def eind_def)
  have "\<squash> (stranslate s k) 
  = (\<olambda> n \<bullet> (bounded_card (\<zdom> (stranslate s k)) n + 1, (stranslate s k)\<cdot>n))\<lparr>\<zdom> (stranslate s k)\<rparr>"
    apply (rule ssquash_image)
    apply (rule stranslate_finite [OF a1])
    apply (insert a2, (mauto(fspace)))
    apply (rule stranslate_functional)
    apply simp_all
    done
  also have "\<dots> = (\<olambda> n \<bullet> (bounded_card (\<zdom> (stranslate s k)) n + 1, (stranslate s k)\<cdot>n))\<lparr>(\<olambda> n \<bullet> n + k)\<lparr>\<zdom> s \<rparr>\<rparr>"
    by (simp add: b0)
  also have "\<dots> 
  = (\<olambda> x \<bullet> (bounded_card (\<zdom> (stranslate s k)) (x + k) + 1, (stranslate s k)\<cdot>(x + k)))\<lparr>\<zdom> s\<rparr>"
    by (simp add: image_image)
  finally have b1: "\<squash> (stranslate s k) 
  = (\<olambda> x \<bullet> (bounded_card (\<zdom> (stranslate s k)) (x + k) + 1, (stranslate s k)\<cdot>(x + k)))\<lparr>\<zdom> s\<rparr>" 
    by auto
  have b2: "\<squash> s = (\<olambda> n \<bullet> (bounded_card (\<zdom> s) n + 1, s\<cdot>n))\<lparr>\<zdom> s\<rparr>"
    by (rule ssquash_image [OF a1 a2])
  have b3: "\<And> x \<bullet> x \<in> \<zdom> s \<turnstile> \<zcard>{i | i \<in> \<zdom> (stranslate s k) \<and> i < x + k} = \<zcard>{i | i \<in> \<zdom> s \<and> i < x}"
  proof -
    fix x 
    assume c0: "x \<in> \<zdom> s"
    let ?A = "{i | i \<in> \<zdom> (stranslate s k) \<and> i < x + k}"
    let ?B = "{i | i \<in> \<zdom> s \<and> i < x}"
    have c1: "inj_on (\<olambda> q :: \<arithmos> \<bullet> q - k) ?A"
      apply (rule inj_onI)
      apply auto
    done
    have c2: "(\<olambda> q \<bullet> q - k)\<lparr> ?A \<rparr> \<subseteq> ?B"
      by (auto simp add: stranslate_def eind_def)
    have c3: "inj_on (\<olambda> r \<bullet> r + k) ?B"
      apply (rule inj_onI)
      apply auto
      done
    have c4: "(\<olambda> r \<bullet> r + k)\<lparr> ?B \<rparr> \<subseteq> ?A"
      by (auto simp add: stranslate_def)
    have c5: "finite ?A"
    proof -
      have d0: "?A = (\<zdom> (stranslate s k)) \<inter> {i | i < x + k}"
        by auto
      show ?thesis
        apply (simp add: d0)
        apply (rule finite_Int)
        apply (rule disjI1)
        apply (intro fun_finite_dom)
        apply (intro stranslate_finite)
        apply (rule a1)
        done
    qed
    have c6: "finite ?B"
    proof -
      have d0: "?B = (\<zdom> s) \<inter> {i | i < x}" by auto
      show ?thesis
        apply (simp add: d0)
        apply (rule finite_Int)
        apply (rule disjI1)
        apply (rule fun_finite_dom)
        apply (rule a1)
        done
    qed
    from c1 c2 c3 c4 c5 c6 show "\<zcard>?A = \<zcard>?B" 
      apply (simp add: zcard_def)
      apply (intro card_bij_eq [where ?f = "\<olambda> q \<bullet> q - k" and ?g = "(\<olambda> r \<bullet> r + k)"])
      apply simp_all
      done
  qed
  have b4: "\<And> x \<bullet> x \<in> \<zdom> s \<turnstile> (stranslate s k)\<cdot>(x + k) = s\<cdot>x"
  proof -
    fix x
    assume c0: "x \<in> \<zdom> s"
    from c0 have c0': "x + k \<in> \<zdom> (stranslate s k)"
      by (simp add: stranslate_def Domain_iff)
    have c1: "functional (stranslate s k)"
      apply (rule stranslate_functional)
      apply (insert a2, (mauto(fspace)))
      done
    have c2: "(x + k, s\<cdot>x) \<in> stranslate s k"
    proof -
      have d0: "s\<cdot>x = (stranslate s k)\<cdot>(x + k)"
        apply (intro functional_beta [THEN sym])
        apply (rule stranslate_functional)
        apply (insert a2, (mauto(fspace)))
        apply (simp add: stranslate_def)
        apply (intro functional_appl)
        apply (insert c0, simp_all)
        done
      then show ?thesis
        apply (simp add: d0)
        apply (rule functional_appl [OF c1 c0'])
        done
    qed
    show  "(stranslate s k)\<cdot>(x + k) = s\<cdot>x"
      by (rule functional_beta [OF c1 c2])
  qed
  show ?thesis
    apply (simp add: b1 b2)
    apply (rule image_cong)
    apply simp_all
    apply (intro conjI)
    apply (simp add: bounded_card_def)
    apply (simp_all add: b3 b4)
  done   
qed

lemma ssquash_stranslate:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<squash> (stranslate s n) = s"
proof (induct "s" rule: seq_rev_induct, rule a1)
  show "\<squash> (stranslate \<sempty> n) = \<sempty>" 
    by (simp add: stranslate_sempty ssquash_sempty)
next
  fix xs x
  assume b1: "xs \<in> \<zseq> X" and b2: "x \<in> X" and b3: "\<squash> (stranslate xs n) = xs"
  have b4: "finite (stranslate xs n)" 
    by (rule stranslate_finite [OF seq_finite [OF b1]])
  have b5: "(stranslate xs n) \<in> \<univ>-[\<arithmos>] \<zpfun> X"
    apply (mauto(fspace))
    apply (simp_all add: 
              stranslate_functional [OF seq_functional [OF b1]] stranslate_seq_ran [OF b1])
  done
  have b6: "finite (stranslate \<lang>x\<rang> (\<zcard>xs + n))" 
    by (rule stranslate_finite [OF seq_finite [OF sunit_seq [OF b2]]])
  have b7: "stranslate \<lang>x\<rang> (\<zcard>xs + n) \<in> \<univ>-[\<arithmos>] \<zpfun> X"
    apply (mauto(fspace))
    apply (simp_all add: 
              stranslate_functional [OF seq_functional [OF sunit_seq [OF b2]]]
              stranslate_seq_ran [OF sunit_seq [OF b2]])
  done
  have b8: "\<forall> a b | a \<in> \<zdom> (stranslate xs n) \<and> b \<in> \<zdom> (stranslate \<lang>x\<rang> (\<zcard>xs + n)) \<bullet> a < b"
    apply (msafe(inference))
    proof -
      fix a b
      assume c1: "a \<in> \<zdom> (stranslate xs n)" and 
        c2: "b \<in> \<zdom> (stranslate \<lang>x\<rang> (\<zcard>xs + n))"
      from c1 have d1: 
      "a \<le> \<zcard>xs + n" 
      by (auto simp add: stranslate_dom seq_dom [OF b1])
      from c2 have d2: 
      "(\<zcard>xs + n) + 1 \<le> b" 
      by (auto simp add: stranslate_dom seq_dom [OF sunit_seq [OF b2]])
      from d1 d2 show "a < b" by auto
    qed
  have b9: "\<squash> {(\<zcard>xs + n+1, x)} = {(1, x)}" 
    apply (simp add: ssquash_def)
    apply (simp add: bounded_card_def)
    apply (auto simp add: Domain_iff dsub_def eind_def)
    proof -
      have e1: "{i | i = (\<zcard>xs + n + 1) \<and> i <(\<zcard>xs + n + 1)} = \<emptyset>" by auto
      show "\<zcard>{i | i = (\<zcard>xs + n + 1)\<and> i < (\<zcard>xs + n + 1)} = 0" by (simp add: e1)
      show "{(\<zcard>xs + n + 1, x)}\<cdot>(\<zcard>xs + n + 1) = x"
        apply (rule functional_beta)
        apply (auto simp add: functional_def single_val_def)
      done
    qed 
  have b10: "stranslate (\<squash> (stranslate \<lang>x\<rang> (\<zcard>xs + n))) (\<zcard>xs) = stranslate \<lang>x\<rang> (\<zcard>xs)"
    apply (simp add: stranslate_sunit)
    apply (simp add: b9)
    apply (simp add: stranslate_def eind_def)
  done
  show "\<squash> (stranslate (xs\<zcat>\<lang>x\<rang>) n) = xs\<zcat>\<lang>x\<rang>"
    apply (subst sconcat_redef)
    apply (rule b1)
    apply (rule sunit_seq [OF b2])
    apply (simp add: sconcat_redef [OF b1 sunit_seq [OF b2]])
    apply (simp add: stranslate_union)
    apply (simp add: stranslate_stranslate)
    apply (rule trans)
    apply (rule ssquash_union [OF b4 b5 b6 b7])
    apply (rule b8)
    apply (simp add: ssquash_zcard [OF b4 b5] ssquash_zcard [OF b6 b7])
    apply (simp add: stranslate_zcard)
    apply (simp add: b3 b10)
  done
qed

lemma ssquash_seq:
  assumes a1: "s \<in> \<zseq> X"
  shows "s = \<squash> s"
proof -
  have b0: "s = stranslate s 0" 
    by (auto simp add: stranslate_def)
  then have b1: "\<squash> (stranslate s 0) = \<squash> s" 
    by auto
  have b2: "\<squash> (stranslate s 0) = s" 
    by (simp add: ssquash_stranslate [OF a1])
  from b1 b2 show ?thesis by auto
qed


section {* Filtering on Domain and Range *}

text
{*

@{text "V\<upharpoonleft>s"} is a sequence that contains just those elements of
 @{text "\<zdom> s"} which are also members of V.  Similarly, 
@{text "s\<restriction>V"} is a sequence that contains just those elements of
 @{text "\<zran> s"} which are also members of V.
*}


definition
  sxtract :: "[\<arithmos> set, \<arithmos> \<leftrightarrow> 'a] \<rightarrow> (\<arithmos> \<leftrightarrow> 'a)"
where
  sxtract_def : "sxtract U s \<defs> \<squash> (U \<zdres> s)"

notation (xsymbols)
  sxtract (infixr "\<upharpoonleft>" 90)

definition
  sfilter :: "[\<arithmos> \<leftrightarrow> 'a, 'a set] \<rightarrow> (\<arithmos> \<leftrightarrow> 'a)"
where
  sfilter_def : "sfilter s V \<defs> \<squash> (s \<zrres> V)"

notation (xsymbols)
  sfilter (infixl "\<restriction>" 90)


lemma Z_sxtract_def:
  "\<lbrakk> U \<in> \<pset> \<univ>-[\<arithmos>];  s \<in> \<zseq> X \<rbrakk> \<turnstile> U \<upharpoonleft> s \<defs> \<squash>(U \<zdres> s)"
  by (auto simp add: sxtract_def)

lemma Z_sfilter_def:
  "\<lbrakk> s \<in> \<zseq> X;  V \<in> \<pset> X \<rbrakk> \<turnstile> s \<restriction> V \<defs> \<squash> (s \<zrres> V)"
  by (auto simp add: sfilter_def)


lemma dres_seq_finite:
  assumes a1: "s \<in> \<zseq> X"
  shows "finite (U \<zdres> s)"
proof -
  have b1: "(U \<zdres> s) \<subseteq> s"
    apply (simp add: dres_def)
    apply (auto)
    done
  show ?thesis
    by (simp add: finite_subset [OF b1 seq_finite [OF a1]])
qed

lemma dres_seq_pfun:
  assumes a1: "s \<in> \<zseq> X"
  shows "U \<zdres> s \<in> (\<univ>-[\<arithmos>] \<zpfun> X)"
  apply ((mauto(fspace)))
proof -
  from seq_functional [OF a1] 
  show "functional (U \<zdres> s)" by ((mauto(fspace)))
  have b3: "\<zran> s \<subseteq> X" by (simp add: seq_ran [OF a1])
  from b3 show "\<zran> (U \<zdres> s) \<subseteq> X"
    apply (simp add: dres_def)
    apply (auto simp add: eind_def)
    done
qed

lemma rres_finite:
  assumes a1: "finite s"
  shows "finite (s \<zrres> V)"
proof -
  have b1: "(s \<zrres> V) \<subseteq> s"
    apply (simp add: rres_def)
    apply (auto)
    done
  show ?thesis
    by (simp add: finite_subset [OF b1 a1])
qed

lemma rres_dom: 
  "\<zdom> (R \<zrres> V) = {x | \<exists> y \<bullet> x \<in> \<zdom> R \<and> (x,y) \<in> R \<and> y \<in> V}"
  by (auto simp add: rres_def)

lemma rres_card:
  assumes a1: "finite s" and a2: "functional s"
  shows "\<card>(s \<zrres> V) = \<card>(\<zdom> (s \<zrres> V))"
proof (rule fun_card_dom)
  from a2 show "functional (s \<zrres> V)" by (simp add: rres_functional)
qed

lemma rres_le_card:
  assumes a1: "finite s"
  shows "\<card>(s \<zrres> V) \<le> \<card>s"
proof -
  have b1: "(s \<zrres> V) \<subseteq> s" by (auto simp add: rres_def)
  show ?thesis
    apply (insert b1 a1)
    apply (simp add: card_mono)
    done
qed

lemma rres_seq_finite:
  assumes a1: "s \<in> \<zseq> X"
  shows "finite (s \<zrres> V)"
proof -
  have b1: "(s \<zrres> V) \<subseteq> s"
    apply (simp add: rres_def)
    apply (auto)
    done
  show ?thesis
    by (simp add: finite_subset [OF b1 seq_finite [OF a1]])
qed

lemma rres_seq_pfun:
  assumes a1: "s \<in> \<zseq> X"
  shows "s \<zrres> V \<in> \<univ>-[\<arithmos>] \<zpfun> X"
  apply ((mauto(fspace)))
proof -
  from seq_functional [OF a1] 
  show "functional (s \<zrres> V)" 
    by ((mauto(fspace)))
  have b3: "\<zran> s \<subseteq> X" 
    by (simp add: seq_ran [OF a1])
  from b3 show "\<zran> (s \<zrres> V) \<subseteq> X"
    apply (simp add: rres_def)
    apply (auto simp add: eind_def)
    done
qed

lemma rres_ran_R:
  "\<zran> (R \<zrres> V) \<subseteq> \<zran> R" by (auto simp add: rres_def)

lemma rres_ran_V:
  "\<zran> (R \<zrres> V) \<subseteq> V" by (auto simp add: rres_def)

lemma rres_seq_ran:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> (s \<zrres> V) \<subseteq> X"
proof -
  have "\<zran> (s \<zrres> V) \<subseteq> \<zran> s" by (simp add: rres_ran_R)
  also have "\<dots> \<subseteq> X" by (simp add: seq_ran [OF a1])
  finally show ?thesis by auto
qed
  
lemma rres_beta:
  assumes a1: "functional R" and a2: "R\<cdot>a \<in> V" and a3: "a \<in> \<zdom> R"
  shows "(R \<zrres> V)\<cdot>a = R\<cdot>a"
  apply (intro functional_beta)
  apply (intro rres_functional)
  apply (rule a1)
  apply (simp add: rres_def)
  apply (intro conjI)
  apply (rule a2)
  apply (rule functional_appl)
  apply (rule a1)
  apply (rule a3)
  done

lemma sxtract_sempty:
  "U\<upharpoonleft>\<sempty> = \<sempty>"
  by (auto simp add: ssquash_def sxtract_def dres_def sempty_def)
 
lemma sfilter_sempty:
  "\<sempty>\<restriction>V = \<sempty>"
  by (auto simp add: ssquash_def sfilter_def rres_def sempty_def)

lemma Z_sfilter_sxtract_sempty:
  "\<lch> \<sempty>\<restriction>V \<chEq> U\<upharpoonleft>\<sempty> \<chEq> \<sempty> \<rch>"
  by (simp add: sempty_def sfilter_def sxtract_def dres_def rres_def ssquash_def eind_def)

lemma Z_sfilter_empty_sxtract_sempty:
  "\<lch> s\<restriction>\<emptyset> \<chEq> \<emptyset>\<upharpoonleft>s \<chEq> \<sempty> \<rch>"
  by (simp add: sempty_def rres_def dres_def ssquash_def sfilter_def sxtract_def eind_def)

lemma sxtract_functional:
  assumes a1: "s \<in> \<zseq> X"
  shows "functional (U\<upharpoonleft>s)"
  apply (simp add: sxtract_def)
  apply (simp add: ssquash_fun [OF dres_seq_finite [OF a1] dres_seq_pfun [OF a1]])
  done

lemma sxtract_dom:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zdom> (U\<upharpoonleft>s) = (1..(\<zcard>(U \<zdres> s)))"
  apply (simp add: sxtract_def)
  apply (simp add: ssquash_dom [OF dres_seq_finite [OF a1] dres_seq_pfun [OF a1]])
done

lemma sxtract_ran:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> (U\<upharpoonleft>s) \<subseteq> X"   
  apply (simp add: sxtract_def)
  apply (simp add: ssquash_ran [OF dres_seq_pfun [OF a1]])
  done  

lemma sxtract_closed:
  assumes a1: "s \<in> \<zseq> X"
  shows "U\<upharpoonleft>s \<in> \<zseq> X"
proof (rule seqIa [where ?n = "\<zcard>(U \<zdres> s)", OF zNats_zcard])
  have ftn: "functional (U\<upharpoonleft>s)" 
    by (rule sxtract_functional [OF a1])
  have dom: "\<zdom> (U\<upharpoonleft>s) = (1..(\<zcard>(U \<zdres> s)))" 
    by (rule sxtract_dom [OF a1])
  have ran: "\<zran> (U\<upharpoonleft>s) \<subseteq> X" 
    by (rule sxtract_ran [OF a1])
  from ftn dom ran show 
    "(U\<upharpoonleft>s) \<in> (1..(\<zcard>(U \<zdres> s))) \<ztfun> X" 
    by (mauto(fspace))
qed

lemma sfilter_functional:
  assumes a1: "s \<in> \<zseq> X"
  shows "functional (s\<restriction>V)"
  apply (simp add: sfilter_def)
  apply (simp add: ssquash_fun [OF rres_seq_finite [OF a1] rres_seq_pfun [OF a1]])
  done

lemma sfilter_dom:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zdom> (s\<restriction>V) = (1..(\<zcard>(s \<zrres> V)))"
  apply (simp add: sfilter_def)
  apply (simp add: ssquash_dom [OF rres_seq_finite [OF a1] rres_seq_pfun [OF a1]])
done
  

lemma sfilter_ran:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> (s\<restriction>V) \<subseteq> X"
  apply (simp add: sfilter_def)
  apply (simp add: ssquash_ran [OF rres_seq_pfun [OF a1]])
  done

lemma sfilter_ran2:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> (s\<restriction>V) \<subseteq> V"
  apply (simp add: sfilter_def)
  apply (rule ssquash_ran)
  apply (mauto(fspace))
  apply (simp add: rres_functional [OF seq_functional [OF a1]])
  apply (auto simp add: rres_def)
  done

(*
declare [[simproc del: defined_Collect]]
declare [[simp_trace]]
*)

lemma sfilter_ranV:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> (s\<restriction>V) \<subseteq> V"
(* J: note that putting these together doesn't do the right thing! *)
  apply (simp add: sfilter_def rres_def ssquash_def bounded_card_def del: split_eta_SetCompr2)
  apply (auto simp del: split_eta_SetCompr2)
proof -
  fix xb y
  assume b0: "y \<in> V" and b1: "(xb, y) \<in> s"
  have "{ x y | y \<in> V \<and> (x, y) \<in> s \<bullet> (x \<mapsto> y) }\<cdot>xb = y"
    apply (rule functional_beta)
    apply (insert seq_functional [OF a1])
    apply (auto intro!: functionalI elim!: functionalE)
    apply (rule b0, rule b1)
    done
  with b0 show "{ x y | y \<in> V \<and> (x, y) \<in> s \<bullet> (x \<mapsto> y) }\<cdot>xb \<in> V"
    by simp
qed
(* J: FIX syntax of last show! ! ! *)


lemma Z_sfilter_ran_redef:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> s \<subseteq> V \<Leftrightarrow> s\<restriction>V = s"
proof (rule iffI)
  assume b1: "\<zran> s \<subseteq> V"
  from b1 have b2: "{ x y | y \<in> V \<and> (x, y) \<in> s \<bullet> (x, y)} = s" by auto
  have b3: "\<squash> s = \<squash> (stranslate s 0)" 
    by (simp add: stranslate_def del: split_eta_SetCompr2)
  show "s\<restriction>V = s"
    apply (simp add: sfilter_def rres_def del: split_eta_SetCompr2)
    apply (simp add: b2 b3 del: split_eta_SetCompr2)
    apply (simp add: ssquash_stranslate [OF a1])
    done
next
  assume c1: "s\<restriction>V = s"
  from c1 have "\<zran> s = \<zran> (s\<restriction>V)" by auto
  also have "\<dots> \<subseteq> V" by (simp add: sfilter_ran2 [OF a1])
  finally show "\<zran> s \<subseteq> V" by auto
qed



lemma rres_ran_seq:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> (s \<zrres> V) = {y | \<exists> x \<bullet> (x, y) \<in> s \<and> y \<in> V}"
  by (auto simp add: rres_def Range_iff Domain_iff dsub_def)

lemma Z_ran_sfilter_inter:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zran> (s\<restriction>V) = (\<zran> s) \<inter> V"
proof -
  have b0: "(\<zran> s) \<inter> V = { y | \<exists> x \<bullet> (x, y) \<in> s \<and> y \<in> V}" 
    by (auto simp add: Range_iff dsub_def Domain_iff)
  have "\<zran> (s\<restriction>V) = \<zran> (\<squash> (s \<zrres> V))" 
    by (simp add: sfilter_def)
  also have "\<dots> = \<zran> (s \<zrres> V)" 
    apply (intro ssquash_ran_function [THEN sym])
    apply (rule rres_functional [OF seq_functional [OF a1]])
    done
  also have "\<dots> = {y | \<exists> x \<bullet> (x, y) \<in> s \<and> y \<in> V}" 
    by (intro rres_ran_seq [OF a1])
  finally have b1: "\<zran> (s\<restriction>V) = {y | \<exists> x \<bullet> (x, y) \<in> s \<and> y \<in> V}" 
    by auto
  show ?thesis by (simp add: b0 b1)
qed

lemma sfilter_closed:
  assumes a1: "s \<in> \<zseq> X"
  shows "s\<restriction>V \<in> \<zseq> X"
proof (rule seqIa [where ?n = "\<zcard>(s \<zrres> V)", OF zNats_zcard])
  have ftn: "functional (s\<restriction>V)" 
    by (rule sfilter_functional [OF a1])
  have dom: "\<zdom> (s\<restriction>V) = (1..(\<zcard>(s \<zrres> V)))"
    by (rule sfilter_dom [OF a1])
  have ran: "\<zran> (s\<restriction>V) \<subseteq> X"
    by (rule sfilter_ran [OF a1])
  from ftn dom ran show "s\<restriction>V \<in> (1..(\<zcard>(s \<zrres> V))) \<ztfun> X" by (mauto(fspace))
qed

lemma sfilter_closedV:
  assumes a1: "s \<in> \<zseq> X"
  shows "s\<restriction>V \<in> \<zseq> V"
  apply (rule seqIa [where ?n = "\<zcard>(s \<zrres> V)", OF zNats_zcard])
  apply (mauto(fspace))
  apply (rule seq_functional [OF sfilter_closed [OF a1]])
  apply (simp add: sfilter_dom [OF a1])
  apply (rule sfilter_ranV [OF a1])
  done

lemma sfilter_zcard:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zcard>(s\<restriction>V) = \<zcard>(s \<zrres> V)"
proof -
  from sfilter_closed [OF a1] have "s\<restriction>V \<in> \<zseq> X" 
    by auto
  then have b0: "\<zcard>(s\<restriction>V) = \<zcard>(\<zdom> (s\<restriction>V))" 
    by (rule seq_zcard_dom)
  from sfilter_dom [OF a1] have "\<zdom> (s\<restriction>V) = (1..\<zcard>(s \<zrres> V))"
    by auto
  with b0 show ?thesis 
  by (auto simp add: zint_range_zcard_from_1)
qed

lemma zcard_mono:
  assumes A1: "finite B" and A2: "A <= B"
  shows 
  "zcard A \<le> zcard B"
    apply (simp add: zcard_def)
    apply (rule card_mono [OF A1 A2])
  done

lemma Z_zcard_sfilter:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zcard>(s\<restriction>V) \<le> \<zcard>s"
proof -
  have b1: "{ x y | y \<in> V \<and> (x, y) \<in> s \<bullet> (x, y)} \<subseteq> s" by (auto)
  show "\<zcard>(s\<restriction>V) \<le> \<zcard>s"
    apply (simp add: sfilter_def)
    apply (simp add: ssquash_zcard [OF rres_seq_finite [OF a1] rres_seq_pfun [OF a1]])
    apply (simp add: rres_def del: split_eta_SetCompr2)
    apply (simp add: zcard_def del: split_eta_SetCompr2)
    apply (simp add: card_mono [OF seq_finite [OF a1] b1] del: split_eta_SetCompr2)
  done
qed
 
      
lemma Z_sconcat_sfilter:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "(s\<zcat>t)\<restriction>V = (s\<restriction>V)\<zcat>(t\<restriction>V)"
proof -
  have b0: "\<squash> (s \<zrres> V) \<in> \<zseq> X" 
    by (rule ssquash_closed [OF rres_finite [OF seq_finite [OF a1]] rres_seq_pfun [OF a1]])
  have b1: "\<squash> (t \<zrres> V) \<in> \<zseq> X"
    by (rule ssquash_closed [OF rres_finite [OF seq_finite [OF a2]] rres_seq_pfun [OF a2]])
  have finiteSresV: "finite (s \<zrres> V)"
    by (intro rres_finite [OF seq_finite [OF a1]])      
  have SresVpfun: "(s \<zrres> V) \<in> \<univ>-[\<arithmos>] \<zpfun> X"
    apply (mauto(fspace))
    apply (intro rres_functional [OF seq_functional [OF a1]])
    apply (simp add: Domain_iff rres_def)
    apply (insert seq_ran [OF a1])
    apply (auto simp add: Range_iff Domain_iff rres_def eind_def)
    done
  have finiteTresV: "finite (stranslate t (\<zcard>s) \<zrres> V)"
    by (intro rres_finite [OF stranslate_finite [OF seq_finite [OF a2]]])
  have TresVpfun: "(stranslate t (\<zcard>s) \<zrres> V) \<in> \<univ>-[\<arithmos>] \<zpfun> X"
    apply (mauto(fspace))
    apply (intro rres_functional [OF stranslate_functional [OF seq_functional [OF a2]]])
    apply (simp add: Domain_iff rres_def)
    apply (insert stranslate_seq_ran [OF a2])
    apply (auto simp add: Range_iff Domain_iff rres_def eind_def)
    done
  have disjointDomain: "\<forall> a b \<bullet> a \<in> \<zdom> (s \<zrres> V) \<and> b \<in> \<zdom> (stranslate t (\<zcard>s) \<zrres> V) \<Rightarrow> a < b"
    apply (intro allI)
    apply (simp add: rres_dom)
    apply (insert seq_index_bound [OF a2])
    apply (auto simp add: seq_dom [OF a1] seq_dom [OF a2] stranslate_dom)
  done    
  have translate: 
    "stranslate (\<squash> (stranslate t (\<zcard>s) \<zrres> V)) (\<zcard>(s \<zrres> V)) 
    = stranslate (\<squash> (t \<zrres> V)) (\<zcard>(s \<zrres> V))"
  proof -
    have "\<squash> (stranslate t (\<zcard>s) \<zrres> V) = \<squash> (t \<zrres> V)"
    proof -
      have c0: "stranslate t (\<zcard>s) \<zrres> V = stranslate (t \<zrres> V) (\<zcard>s)"
        by (auto simp add: rres_def stranslate_def)
      show ?thesis
        apply (simp add: c0)
        apply (intro ssquash_stranslate_function)
        apply (rule rres_seq_finite [OF a2])
        apply (rule rres_seq_pfun [OF a2])
        done
    qed
    then show ?thesis by simp
  qed
  show ?thesis
    apply (simp add: sfilter_def) 
    apply (simp add: sconcat_redef [OF b0 b1])
    apply (simp add: sconcat_redef [OF a1 a2])
    apply (simp add: rres_union_dist1 [THEN sym])
    apply (rule ssquash_union [THEN trans, where ?X1 = "X"])
    apply (rule finiteSresV)
    apply (rule SresVpfun)
    apply (rule finiteTresV)
    apply (rule TresVpfun)
    apply (rule disjointDomain)
    apply (simp add: ssquash_zcard [OF finiteSresV SresVpfun])
    apply (simp add: translate)
  done
qed

lemma sfilter_repeat_singleton:
  assumes 
    a1: "x \<in> X"
  shows 
    "(\<lang>x\<rang>\<restriction>V) \<restriction> W = \<lang>x\<rang>\<restriction>(V \<inter> W)"
  using ssquash_sempty
  apply (cases "x \<notin> V")
  apply (cases "x \<notin> W")
  apply (simp add: 
            sinsert_def rel_oride_def Domain_iff dsub_def stranslate_sempty 
            eind_def)
  using a1
  apply (simp add: sfilter_def rres_def ssquash_sempty sempty_def eind_def) 
  apply (simp add: ssquash_def bounded_card_def eind_def)
  apply (simp add: sinsert_def rel_oride_def Domain_iff dsub_def stranslate_sempty)
  using a1
  apply (simp add: sfilter_def rres_def ssquash_def bounded_card_def sempty_def eind_def)
  apply (cases "x \<notin> W")
  apply (simp add: sinsert_def rel_oride_def Domain_iff dsub_def stranslate_sempty eind_def)
  apply (simp add: 
            sfilter_def rres_def ssquash_def bounded_card_def sempty_def Domain_iff eind_def)
  apply (subst functional_beta)
  apply (auto intro!: functionalI simp add: eind_def)
proof -
  fix a b
  assume 
    b0: "x \<in> V" and b1: "x \<in> W" and b2: "(a, b) \<in> \<lang>x\<rang>\<restriction>V\<restriction>W"
  have a2: "{ xa y | y \<in> V \<and> (xa, y) \<in> \<lang>x\<rang> \<bullet> (xa, y)} = {(1, x)}"
    apply (insert b0)
    apply (simp add: sinsert_def rel_oride_def Domain_iff dsub_def stranslate_sempty)
    apply (auto simp add: sempty_def del: split_eta_SetCompr2)
    done
  from b1 have a3: "{xa y | y \<in> W \<and> xa = 1 \<and> y = x \<bullet> (xa, y)} = {(1, x)}" 
    by auto
  from b2 ssquash_unit_set [OF a2] ssquash_unit_set [OF a3]
  have b3: "a = 1"
    by (simp add: sfilter_def rres_def del: split_eta_SetCompr2)
  have b4: "\<lang>x\<rang>\<restriction>V\<restriction>W \<in> \<zseq> X"
    apply (intro sfilter_closed)
    apply (rule sunit_seq [OF a1])
    done
  from b2 have b5: "b = x"
  proof -
    have "b = (\<lang>x\<rang>\<restriction>V\<restriction>W)\<cdot>a"
      apply (intro functional_beta [THEN sym])
      apply (insert seq_functional [OF b4])
      apply (auto intro!: functionalI elim!: functionalE)
      apply (rule b2)
      done
    also from ssquash_unit_set [OF a2] ssquash_unit_set [OF a3]
    have "\<dots> = x"
      apply (simp add: sfilter_def rres_def del: split_eta_SetCompr2)
      apply (intro functional_beta)
      apply (auto intro!: functionalI)
      apply (simp add: b3)
      done
    finally show "b = x" by this
  qed
  have a4: "{ xa y | y \<in> V \<and> y \<in> W \<and> (xa, y) \<in> \<lang>x\<rang> \<bullet> (xa, y) } = {(1, x)}"
    apply (simp add: sinsert_def rel_oride_def Domain_iff dsub_def stranslate_sempty)
    apply (simp add: sempty_def)
    apply (insert b0 b1)
    apply auto
    done
  from ssquash_unit_set [OF a4]
  show "(a, b) \<in> (\<lang>x\<rang>\<restriction>(V \<inter> W))"
    by (simp add: b3 b5 sfilter_def rres_def)
next
  fix a b
  assume b0: "x \<in> V" and b1: "x \<in> W" and b2: "(a, b) \<in> \<lang>x\<rang>\<restriction>(V \<inter> W)"
  from b0
  have a2: "{ xa y | y \<in> V \<and> (xa, y) \<in> \<lang>x\<rang> \<bullet> (xa \<mapsto> y)} = {(1, x)}"
    apply (simp add: sinsert_def rel_oride_def Domain_iff dsub_def stranslate_sempty)
    apply (auto simp add: sempty_def)
    done
  from b1 have a3: "{ xa y | y \<in> W \<and> xa = 1 \<and> y = x \<bullet> (xa, y) } = {(1, x)}"
    by auto
  have a4: "{ xa y | y \<in> V \<and> y \<in> W \<and> (xa, y) \<in> \<lang>x\<rang> \<bullet> (xa, y)} = {(1, x)}"
    apply (simp add: sinsert_def rel_oride_def Domain_iff dsub_def stranslate_sempty)
    apply (simp add: sempty_def)
    apply (insert b0 b1)
    apply auto
    done
  from b2 ssquash_unit_set [OF a4] have b3: "a = 1"
    by (simp add: sfilter_def rres_def)
  from b2 have b4: "b = x"
  proof - 
    have "b = (\<lang>x\<rang>\<restriction>(V \<inter> W))\<cdot>a"
      apply (intro functional_beta [THEN sym])
      apply (rule seq_functional)
      apply (intro sfilter_closed)
      apply (rule sunit_seq [OF a1])
      apply (rule b2)
      done
    also from ssquash_unit_set [OF a4]
    have "\<dots> = x"
      apply (simp add: sfilter_def rres_def)
      apply (intro functional_beta)
      apply (mauto(fspace) mintro!: fin_pfunI)
      apply (simp add: b3)
      done
    finally show "b = x" 
      by this
  qed
  from ssquash_unit_set [OF a2] ssquash_unit_set [OF a3]
  show "(a, b) \<in> \<lang>x\<rang>\<restriction>V\<restriction>W"
    by (simp add: sfilter_def rres_def b3 b4)
qed

lemma Z_sfilter_repeat:
  assumes a1: "s \<in> \<zseq> X"
  shows "(s\<restriction>V)\<restriction>W = s\<restriction>(V \<inter> W)"
proof (rule seq_rev_induct [OF a1])
  show "(\<sempty>\<restriction>V)\<restriction>W = \<sempty>\<restriction>(V \<inter> W)"
    by (simp add: sfilter_sempty)
next
  fix xs x
  assume b0: "xs \<in> \<zseq> X" and b1: "x \<in> X" and b2: "xs\<restriction>V\<restriction>W = xs\<restriction>(V \<inter> W)"
  have b1': "\<lang>x\<rang> \<in> \<zseq> X" 
    by (rule sunit_seq [OF b1])
  show "(xs\<zcat>\<lang>x\<rang>)\<restriction>V\<restriction>W = (xs\<zcat>\<lang>x\<rang>)\<restriction>(V \<inter> W)"
    apply (simp add: Z_sconcat_sfilter [OF b0 b1'])
    apply (simp add: Z_sconcat_sfilter [OF sfilter_closed [OF b0] sfilter_closed [OF b1']])
    apply (simp add: sfilter_repeat_singleton [OF b1] b2)
    done
qed
   
text {*

The following three lemmas are not expressed exactly as in "The Z notation".  
All three require the extra assumption that @{text "\<card>s \<le> \<card>t"}
for solving various arithmatic expressions.  
This must be an unstated assumption in the definition of suffix, prefix and infix since if 
@{text "s"} is larger than @{text "t"} it obviously can not be a suffix, prefix or infix of 
@{text "t"} anyway.

The infix expression requires a complete restatement.  The original expression in the book is:
@{text "s \<infix> t \<Leftrightarrow> (\<exists> n | n \<in> {1..\<card>t} \<bullet> s = {n..n + \<card>s}\<upharpoonleft>t"} 
which is clearly wrong since @{text "\<card>{n..n + \<card>s} > \<card>s"}.
*}
(* J: TODO move this, and also check whether is the best replacement for Domain_def!
  Along the same lines, note that should probably del better the split_eta_SetCompr2
*)

lemma Domain_Collect_Zsplit: 
  "\<zdom> { x | P x \<bullet> (Q x \<mapsto> R x) } = { x | P x \<bullet> Q x }"
  by (auto simp add: eind_def)

lemma Z_sprefix_sxtract:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X" and a3: "\<zcard>s \<le> \<zcard>t"
  shows "s \<prefix> t \<Leftrightarrow> s = (1..(\<zcard>s))\<upharpoonleft>t"
proof (rule iffI)
  assume b0: "s \<prefix> t"
  from sprefix_closed [OF a2 b0] obtain v where b1: "v \<in> \<zseq> X \<and> s\<zcat>v = t" by auto
  from b1 have seqv: "v \<in> \<zseq> X" by auto
  from b1 have scatv: "s\<zcat>v = t" by auto
  have b2: "s = \<squash> { x y | 1 \<le> x \<and> x \<le> \<zcard>s \<and> (x, y) \<in> t \<bullet> (x, y) }"
  proof -
    have c0: "{ x y | 1 \<le> x \<and> x \<le> \<zcard>s \<and> (x, y) \<in> t \<bullet> (x, y) } = s"
    proof (auto simp add: set_eq_def)
      fix a b
      assume d0: "1 \<le> a" and d1: "a \<le> \<zcard>s" and d2: "(a, b) \<in> t"
      have d3: "b = s\<cdot>a"
      proof -
        from seq_beta [OF a2 d2] have "b = t\<cdot>a" by auto
        also have "\<dots> = s\<cdot>a"
          apply (intro subset_beta [THEN sym])
          apply (rule seq_functional [OF a1])
          apply (rule seq_functional [OF a2])
          apply (rule sprefix_subset [OF a1 a2 b0])
          apply (simp add: seq_dom [OF a1])
          apply (insert d0 d1, simp)
          apply (insert seq_index_bound [OF a2 d2], simp)
        done
        finally show "b = s\<cdot>a" by auto
      qed 
      show "(a, b) \<in> s"
        apply (subst d3)
        apply (rule seq_appl, rule a1)
        apply (insert seq_index_bound [OF a2 d2] d0 d1) 
        apply arith+ 
      done
    next
      fix a b
      assume d0: "(a, b) \<in> s"
      from seq_index_bound [OF a1 d0] show "1 \<le> a" by auto
      from seq_index_bound [OF a1 d0] show "a \<le> \<zcard>s" by auto
      from sprefix_subset [OF a1 a2 b0] d0 show "(a, b) \<in> t" by auto
    qed
    show "s = \<squash> { x y | 1 \<le> x \<and> x \<le> \<zcard>s \<and> (x, y) \<in> t \<bullet> (x, y) }"
      apply (subst c0)
      apply (insert ssquash_seq [OF a1], simp)
      done
  qed
  show "s = (1..(\<zcard>s))\<upharpoonleft>t"
    apply (simp add: sxtract_def)
    apply (simp add: dres_def)
    apply (subst b2)
    apply (insert seq_index_bound [OF a2])
    apply (rule arg_cong [where ?f = ssquash])
    apply auto
  done
next
  assume b0: "s = (1..(\<zcard>s))\<upharpoonleft>t"
  let ?v = "{x y | \<zcard>s < x \<and> ((x, y) \<in> t) \<bullet> (x - \<zcard>s, y)}"

  have Rb0:
  "?v = {x | x \<in> \<int> \<and> \<zcard>s < x  \<and> x \<le> \<zcard>t \<bullet> (x - \<zcard>s, t\<cdot>x)}"
    apply (auto simp add: set_eq_def)
    apply (simp add: a2 [THEN seq_beta])
    apply (rule a2 [THEN seq_index_bound, THEN conjunct1], simp)
    apply (rule a2 [THEN seq_index_bound, THEN conjunct2, THEN conjunct2], simp)
    apply (rule a2 [THEN seq_appl], simp_all)
    apply (simp add: zInts_one_le_iff_zero_less zInts_norm)
    apply (rule order_le_less_trans)
    apply (rule zcard_range [THEN zNats_le0])
    apply assumption
  done
  have ftn: 
  "functional ?v"
    apply (intro functionalI, auto)
    apply (rule a2 [THEN seq_functional [THEN functionalD]])
    apply auto
  done
  have dom: 
  "\<zdom> ?v = (1..(\<zcard>t - \<zcard>s))"
    apply (simp add: Domain_Collect_Zsplit Rb0)
    apply (rule set_eqI)
    apply (mauto_full(inference))
    apply (rule zInts_diff)
    apply (simp_all add: zInts_zcard)
    apply (subst zInts_one_le_iff_zero_less)
    apply (rule zInts_diff)
    apply (simp_all add: zInts_zcard)
(*
    apply (msafe(wind))
    apply simp_all
    apply (mauto(inference))
    apply simp_all
    apply (rule zInts_diff)
    apply (simp_all add: zInts_zcard)
    apply (subst zInts_one_le_iff_zero_less)
    apply (rule zInts_diff)
    apply (simp_all add: zInts_zcard)
*)
  proof -
    fix 
      x::\<arithmos>
    assume 
      "x \<in> zInts" "1 \<le> x" "x \<le> zcard t - zcard s"
    then show
      "(\<exists> x' \<bullet> x = x' - zcard s \<and> x' \<in> zInts \<and> zcard s < x' \<and> x' \<le> zcard t)"
      apply (witness "x + zcard s")
      apply auto
      apply (rule zInts_add)
      apply (simp_all add: zInts_zcard)
    done
  qed    
  have ran: 
  "\<zran> ?v \<subseteq> \<zran> t" 
  by auto

  from ftn dom ran have b1: "?v \<in> \<zseq> (\<zran> t)"
    apply (intro seqIa [where ?n = "\<zcard>t - \<zcard>s"])
    apply (rule zNats_zcard [THEN zNats_zcard [THEN zNats_diff], OF a3])
    apply (mauto(fspace))
  done
  from seq_transitive [OF a2 [THEN seq_ran] b1]
  have b1': "?v \<in> \<zseq> X" 
  by auto
  have b2: "s\<zcat>?v = t"
  proof -
    from a3 have c0: 
    "s = { x y | x \<in> (1..\<zcard>s) \<and> (x, y) \<in> t \<bullet> (x, y) }"
      apply (subst b0)
      apply (simp add: sxtract_def dres_def)
      apply (intro ssquash_seq [THEN sym])
      apply (intro seqIa [where ?n = "\<zcard>s"])
      apply (rule zNats_zcard)
      apply (mauto(fspace))
      apply (intro functionalI, auto)
      apply (rule a2 [THEN seq_functional [THEN functionalD]])
      apply (auto simp add: Z_dom_def)
      apply (rule exI)
      apply (rule seq_appl [OF a2])
      apply simp_all
    done
    have c1: 
    "stranslate ?v (\<zcard>s) = {x y | \<zcard>s < x \<and> (x, y) \<in> t \<bullet> (x, y) }"
      apply (simp add: stranslate_def)
      apply (auto simp add: set_eq_def)
    proof -
      fix a b
      assume d0: "\<zcard>s < a" and d1: "(a, b) \<in> t"
      show "\<exists> n \<bullet> a = n + \<zcard>s \<and> (\<exists> x \<bullet> n = x - \<zcard>s \<and> \<zcard>s < x \<and> (x, b) \<in> t)"
        apply (witness "a - \<zcard>s")
        apply (intro conjI)
        apply (insert d0, arith)
        apply (witness "a")
        apply (intro conjI)
        apply auto
        apply (rule d1)
      done
    qed
    show "s\<zcat>?v = t"
      apply (simp add: sconcat_redef [OF a1 b1'])
      apply (subst c0)
      apply (subst c1)
      apply (insert seq_dom [OF a2])
      apply (auto simp add: set_eq_def)
    done
  qed

  show "s \<prefix> t"
    apply (simp add: sprefix_def)
    apply (witness "?v")
    apply (intro conjI)
    apply (rule b1)
    apply (rule b2)
    done
qed

lemma zNats_0_le:
  assumes a1: "x \<in> \<nat>"
  shows "0 \<le> x"
  using a1
  by (rule zNats_induct, simp_all)

lemma Z_ssuffix_sxtract:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X" and a3: "\<zcard>s \<le> \<zcard>t"
  shows "s \<suffix> t \<Leftrightarrow> s = ((\<zcard>t - \<zcard>s + 1)..(\<zcard>t))\<upharpoonleft>t"
proof (rule iffI)
  assume b0: "s \<suffix> t"
  from ssuffix_closed [OF a2 b0] obtain u where "u \<in> \<zseq> X \<and> u\<zcat>s = t" 
    by auto
  then have b1: "u \<in> \<zseq> X" and b2: "u\<zcat>s = t" 
    by auto
  from b2 Z_sconcat_zcard [OF b1 a1] have b3: "\<zcard>u = \<zcard>t - \<zcard>s" 
    by auto
  from ssuffix_sub [OF a1 a2 b0] have b4: "stranslate s (\<zcard>t - \<zcard>s) \<subseteq> t" 
    by auto
  have b5: "s = \<squash> {x y | (\<zcard>t - \<zcard>s + 1) \<le> x \<and> x \<le> \<zcard>t \<and> (x, y) \<in> t \<bullet> (x, y) }"
  proof -
    have c0: "{x y | (\<zcard>t - \<zcard>s + 1) \<le> x \<and> x \<le> \<zcard>t \<and> (x, y) \<in> t \<bullet> (x, y) } = stranslate s (\<zcard>t - \<zcard>s)"
    proof (auto simp add: set_eq_def)
      fix a b
      assume d0: "(\<zcard>t - \<zcard>s + 1) \<le> a" and d1: "a \<le> \<zcard>t" and d2: "(a, b) \<in> t"
      have d3: "t\<cdot>a = b" by (rule seq_beta [OF a2 d2])
      have "(stranslate s (\<zcard>t - \<zcard>s))\<cdot>a = t\<cdot>a"
        apply (rule subset_beta)
        apply (rule stranslate_functional [OF seq_functional [OF a1]])
        apply (rule seq_functional [OF a2])
        apply (rule b4)
        apply (subst stranslate_seq_dom [OF a1])
        apply (rule zInts_diff [OF zInts_zcard zInts_zcard])
        apply (simp add: zint_range_mem)
        apply (insert d0 d1 d2)
        apply (simp add: seq_index_bound [OF a2])
      done
      with d3 have d4: "b = (stranslate s (\<zcard>t - \<zcard>s))\<cdot>a" by auto
      show "(a, b) \<in> stranslate s (\<zcard>t - \<zcard>s)"
        apply (simp add: d4)
        apply (rule stranslate_appl [OF a1])
        apply (insert d0 d1 d2 a3)
        apply simp_all
        apply (rule zInts_diff)
        apply (simp add: seq_index_bound [OF a2])
        apply (rule zInts_diff [OF zInts_zcard zInts_zcard])
      done
    next
      fix a b
      assume d0: "(a, b) \<in> stranslate s (\<zcard>t - \<zcard>s)"
      from stranslate_index_bound [OF a1 d0] show "(\<zcard>t - \<zcard>s + 1) \<le> a" by auto
      from stranslate_index_bound [OF a1 d0] have "a \<le> \<zcard>s + (\<zcard>t - \<zcard>s)" by auto
      with a3 show "a \<le> \<zcard>t" by arith
      from b4 d0 show "(a, b) \<in> t" by auto
    qed
    show ?thesis
      apply (simp only: c0)
      apply (simp add: ssquash_stranslate [OF a1])
      done    
  qed
  show "s = ((\<zcard>t - \<zcard>s + 1)..(\<zcard>t))\<upharpoonleft>t"
    apply (simp add: sxtract_def dres_def)
    apply (subst b5)
    apply (rule arg_cong [where ?f = ssquash])
    apply (auto simp add: set_eq_def)
    apply (simp add: seq_index_bound [OF a2])
  done
next
  assume b0: "s = ((\<zcard>t - \<zcard>s + 1)..\<zcard>t)\<upharpoonleft>t"
  let ?u = "{ x y | 1 \<le> x \<and> x \<le> \<zcard>t - \<zcard>s \<and> (x, y) \<in> t \<bullet> (x, y) }"

  have Rb0:
  "?u = {x | x \<in> \<int> \<and> 1 \<le> x  \<and> x \<le> (\<zcard>t - \<zcard>s) \<bullet> (x, t\<cdot>x)}"
    apply (auto simp add: set_eq_def)
    apply (simp add: a2 [THEN seq_beta])
    apply (rule a2 [THEN seq_index_bound, THEN conjunct1], simp)
    apply (rule a2 [THEN seq_appl], simp_all)
    apply (rule order_trans)
    apply (simp_all add: algebra_simps)
    apply (rule zcard_range [THEN zNats_le0])
  done
(* J:  uncomfortable! *)
  have "\<forall> x::\<arithmos> | x \<le> \<zcard>t - \<zcard>s \<bullet> x \<le> \<zcard>t"
    apply (msafe(inference))
    apply (rule order_trans, assumption)
    apply (simp add: algebra_simps)
    apply (intro zNats_0_le zNats_zcard [of s])
    done
  with seq_dom [OF a2] have dom: "\<zdom> ?u = 1..(\<zcard>t - \<zcard>s)"
    by (auto simp add: set_eq_def Domain_iff Rb0)
  have ftn: "functional ?u"
    apply (insert seq_functional [OF a2])
    apply (auto intro!: functionalI elim!: functionalE)
  done 
  have ran: "\<zran> ?u \<subseteq> \<zran> t" by auto

  from ftn dom ran 
  have b1: "?u \<in> \<zseq> (\<zran> t)"
    apply (intro seqIa [where ?n = "\<zcard>t - \<zcard>s"])
    apply (simp add: zNats_diff [OF zNats_zcard zNats_zcard a3])
    apply (mauto(fspace))
  done
  from seq_transitive [OF a2 [THEN seq_ran] b1]
  have b1': "?u \<in> \<zseq> X" by auto
  have cardu: "\<zcard>?u = \<zcard>t - \<zcard>s"
  proof -
    have "\<zcard>?u = \<zcard>(\<zdom> ?u)" by (intro seq_zcard_dom [OF b1])
    also have "\<dots> = \<zcard>(1..(\<zcard>t - \<zcard>s))" by (simp only: dom)
    also have "\<dots> = \<zcard>t - \<zcard>s" by (simp add: zint_range_zcard_from_1 [OF zNats_diff [OF zNats_zcard zNats_zcard a3]])
    finally show "\<zcard>?u = \<zcard>t - \<zcard>s" by auto
  qed
  have b2: "?u\<zcat>s = t"
  proof -
    have c0: "stranslate s (\<zcard>?u) = {x y | (\<zcard>t - \<zcard>s + 1) \<le> x \<and> x \<le> \<zcard>t \<and> (x, y) \<in> t \<bullet> (x \<mapsto> y)}"
    proof -
      let ?b = "{x y | (\<zcard>t - \<zcard>s + 1) \<le> x \<and> x \<le> \<zcard>t \<and> (x, y) \<in> t \<bullet> (x \<mapsto> y)}"
      let ?a = "{x y | x \<in> zInts \<and> 1 \<le> x \<and> x \<le> \<zcard>s \<and> (x + (\<zcard>t - \<zcard>s), y) \<in> t \<bullet> (x \<mapsto> y)}"
   
  have Rc0:
  "?a = {x | x \<in> \<int> \<and> 1 \<le> x  \<and> x \<le> \<zcard>s \<bullet> (x, t\<cdot>(x + (\<zcard>t - \<zcard>s)))}"
    apply (auto simp add: set_eq_def)
    apply (simp add: a2 [THEN seq_beta])
    apply (rule a2 [THEN seq_appl], simp_all)
    apply (rule zInts_add, simp_all)
    apply (rule zInts_diff [OF zInts_zcard zInts_zcard])
    apply (rule add_increasing2)
    using a3
    apply (simp_all)
  done
  have Rc1:
  "?b = {x | x \<in> \<int> \<and> (\<zcard>t - \<zcard>s + 1) \<le> x \<and> x \<le> \<zcard>t \<bullet> (x, t\<cdot>x)}"
    apply (auto simp add: set_eq_def)
    apply (simp add: a2 [THEN seq_beta])
    apply (rule a2 [THEN seq_index_bound, THEN conjunct1], simp)
    apply (rule a2 [THEN seq_appl], simp_all)
    apply (rule order_trans [where ?y = "zcard t - zcard s + 1"])
    using a3
    apply (simp_all)
  done

      have seqa: "?a \<in> \<zseq> X"
      proof (intro seqIa [where ?n = "\<zcard>s", OF zNats_zcard])
        have ftn: "functional ?a"
          apply (insert seq_functional [OF a2])
          apply (auto intro!: functionalI elim!: functionalE)
        done
        from zNats_zcard [of s] zNats_zcard [of t] seq_dom [OF a2] a3 have dom: 
        "\<zdom> ?a = (1..\<zcard>s)"
          by (auto simp add: set_eq_def Domain_iff Rc0 zInts_zNats_nonneg intro: zInts_add zInts_diff)
        have ran: "\<zran> ?a \<subseteq> X"
        proof -
          have "\<zran> ?a \<subseteq> \<zran> t" by auto
          also have "\<dots> \<subseteq> X" by (intro seq_ran [OF a2])
          finally show "\<zran> ?a \<subseteq> X" by auto
        qed
        from ftn dom ran show "?a \<in> (1..\<zcard>s) \<ztfun> X" by (mauto(fspace))
      qed
      have trans: "stranslate ?a (\<zcard>t - \<zcard>s) = ?b"
      proof (auto simp add: stranslate_def set_eq_def)
(*
      apply_end (rule zInts_add, simp_all)
      apply_end (rule zInts_diff [OF zInts_zcard zInts_zcard])
*)
        fix a b
        assume d0: "(\<zcard>t - \<zcard>s + 1) \<le> a" and d1: "a \<le> \<zcard>t" and d2: "(a, b) \<in> t"
        from d2 have Rd0:
        "a \<in> zInts"
        by (rule a2 [THEN seq_index_bound, THEN conjunct1])

        let ?n = "a - (\<zcard>t - \<zcard>s)"
        from d0 d1 a3 have d3: "a = ?n + (\<zcard>t - \<zcard>s)" by arith
        from d0 have d4: "1 \<le> ?n" by arith
        from d1 a3 have d5: "?n \<le> \<zcard>s" by arith
        have d6: "(?n + (\<zcard>t - \<zcard>s), b) \<in> t"
          apply (subst d3 [THEN sym])
          by (rule d2)
        from Rd0 have Rd7:
        "?n \<in> zInts"
        by (intro zInts_diff, simp_all add: zInts_zcard)
        from d3 d4 d5 d6 Rd7 show 
        "\<exists> n \<bullet> a = n + (\<zcard>t - \<zcard>s) \<and> n \<in> zInts \<and> 1 \<le> n \<and> n \<le> \<zcard>s \<and> (n + (\<zcard>t - \<zcard>s), b) \<in> t"
          apply (witness "?n")
          apply (intro conjI)
          apply simp_all
        done
      qed
      from b0 have "s = ((\<zcard>t - \<zcard>s + 1)..\<zcard>t)\<upharpoonleft>t" 
        by auto
      also from seq_dom [OF a2] have "\<dots> = \<squash> ?b" 
        apply (simp add: Rc1 sxtract_def dres_def eind_def)
        apply (rule arg_cong [where ?f = "ssquash"])
        apply (auto simp add: set_eq_def)
        done
      also have "\<dots> = \<squash> (stranslate ?a (\<zcard>t - \<zcard>s))"
        by (simp only: trans [THEN sym])
      also have "\<dots> = ?a" by (rule ssquash_stranslate [OF seqa])
      finally have d0: "s = ?a" by auto
      have "stranslate s (\<zcard>?u) = stranslate s (\<zcard>t - \<zcard>s)" by (simp only: cardu)
      also with d0 have "\<dots> = stranslate ?a (\<zcard>t - \<zcard>s)" by simp
      also have "\<dots> = ?b" by (simp only: trans)
      finally show "stranslate s (\<zcard>?u) = ?b" by simp
    qed
    show ?thesis
      apply (simp only: sconcat_redef [OF b1' a1])
      apply (simp only: c0)
      apply (insert seq_dom [OF a2] a3)
      apply (auto simp add: set_eq_def linorder_not_le)
      apply (subst zInts_le_add1_eq_le [THEN sym])
      apply (rule a2 [THEN seq_index_bound, THEN conjunct1], simp)
      apply (intro zInts_diff, simp_all add: zInts_zcard)
    done
  qed
  from b1 b2 show "s \<suffix> t"
    apply (simp add: ssuffix_def)
    apply (witness "?u", simp)
  done
qed

lemma Z_sinfix_sxtract:
  assumes 
    a1: "s \<in> \<zseq> X" and
    a2: "t \<in> \<zseq> X" and 
    a3: "\<zcard>s \<le> \<zcard>t"
  shows 
    "s \<infix> t \<Leftrightarrow> (\<exists> n | n \<in> 0..(\<zcard>t - \<zcard>s) \<bullet> s = ((n+1)..(n + \<zcard>s)\<upharpoonleft>t))"
proof (rule iffI)
  assume b0: "s \<infix> t"
  from sinfix_closed [OF a2 b0] obtain u v where b1: "(u \<in> \<zseq> X \<and> v \<in> \<zseq> X) \<and> u\<zcat>s\<zcat>v = t" by auto
  from b1 have uinseqX: "u \<in> \<zseq> X" and vinseqX: "v \<in> \<zseq> X" and concat: "u\<zcat>s\<zcat>v = t" by auto
  have b2: "\<zcard>u \<le> \<zcard>t - \<zcard>s"
  proof -
    have "\<zcard>(u\<zcat>s\<zcat>v) = \<zcard>u + \<zcard>s + \<zcard>v"
      by (simp add: Z_sconcat_zcard [OF sconcat_closed [OF uinseqX a1] vinseqX] Z_sconcat_zcard [OF uinseqX a1])
    with concat have c1: "\<zcard>u + \<zcard>s + \<zcard>v = \<zcard>t" by auto
    with a3 have c1: "\<zcard>u + \<zcard>v = \<zcard>t - \<zcard>s" by auto
    also have
    "... \<le> \<zcard>t - \<zcard>s + \<zcard>v" 
      apply (rule add_increasing2)
      apply (rule zcard_range [THEN zNats_le0])
      apply simp
    done
    finally have c1: 
    "\<zcard>u + \<zcard>v \<le> \<zcard>t - \<zcard>s + \<zcard>v" .
    show ?thesis 
      apply (rule add_le_imp_le_right)
      apply (rule c1)
    done
  qed

  have ssubt: "stranslate s (\<zcard>u) \<subseteq> t"
    apply (insert concat)
    apply (simp only: sconcat_redef [OF sconcat_closed [OF uinseqX a1] vinseqX])
    apply (simp only: Z_sconcat_zcard [OF uinseqX a1])
    apply (simp add: sconcat_redef [OF uinseqX a1])
    apply auto
    done


  have b3: "{ x y | x \<in> zInts \<and> (\<zcard>u + 1) \<le> x \<and> x \<le> \<zcard>u + \<zcard>s \<and> (x, y) \<in> t \<bullet> (x \<mapsto> y)} = stranslate s (\<zcard>u)"
  proof (auto simp add: set_eq_def)
    fix a b
    assume c0: "(\<zcard>u + 1) \<le> a" and c1: "a \<le> \<zcard>u + \<zcard>s" and c2: "(a, b) \<in> t"
    let ?n = "a - \<zcard>u"
    have c3: "t\<cdot>a = b" by (intro seq_beta [OF a2 c2])
    have "(stranslate s (\<zcard>u))\<cdot>a = t\<cdot>a"
      apply (intro subset_beta)    
      apply (intro stranslate_functional [OF seq_functional [OF a1]])
      apply (intro seq_functional [OF a2])
      apply (intro ssubt)
      apply (subst stranslate_seq_dom [OF a1])
      apply (simp_all add: zint_range_mem zInts_zcard)
      apply (insert c0 c1 c2)
      apply (simp add: seq_index_bound [OF a2])
    done
    with c3 have c4: "b = (stranslate s (\<zcard>u))\<cdot>a" by auto
    show "(a, b) \<in> stranslate s (\<zcard>u)"
      apply (subst c4)
      apply (intro stranslate_appl [OF a1])
      apply (rule c0)
      apply (rule c1)
      apply (intro zInts_diff zInts_zcard) 
      apply (insert c2)
      apply (simp add: seq_index_bound [OF a2])
    done
  next
    fix a b
    assume c0: "(a, b) \<in> stranslate s (\<zcard>u)"
    from stranslate_index_bound [OF a1 c0] show "(\<zcard>u + 1) \<le> a" by auto
    from stranslate_index_bound [OF a1 c0] show "a \<le> \<zcard>u + \<zcard>s" by auto
    from ssubt c0 show "(a, b) \<in> t" by auto
  next
    fix a b
    assume c0: "(a, b) \<in> stranslate s (\<zcard>u)"
    then have
    "a \<in> \<zdom> (stranslate s (\<zcard>u))" by auto
    then show
    "a \<in> zInts"
    by (simp add: stranslate_seq_dom [OF a1 zInts_zcard])
  qed

  show "\<exists> n \<bullet> n \<in> 0..(\<zcard>t - \<zcard>s) \<and> s = (n+1)..(n + \<zcard>s)\<upharpoonleft>t"
    apply (witness "\<zcard>u")
    apply (simp add: seq_dom [OF a2] zInts_zcard)
    apply (intro conjI)
    apply (simp add: zcard_def)
    apply (rule b2)
    apply (simp add: sxtract_def dres_def zint_range_mem del: split_eta_SetCompr2)
    apply (subst b3)
    apply (simp add: ssquash_stranslate [OF a1])
    done
next
  assume "\<exists> n \<bullet> n \<in> 0..(\<zcard>t - \<zcard>s) \<and> s = (n+1)..(n + \<zcard>s)\<upharpoonleft>t"
  then obtain n where "n \<in> 0..(\<zcard>t - \<zcard>s) \<and> s = (n+1)..(n + \<zcard>s)\<upharpoonleft>t" by auto
  then have 
    b00: "n\<in>zInts" and 
    b0: "0 \<le> n" and 
    b1: "n \<le> \<zcard>t - \<zcard>s" and 
    b2: "s = (n+1)..(n + \<zcard>s)\<upharpoonleft>t" by auto

  let ?u = 
    "{x y | 1 \<le> x \<and> x \<le> n \<and> (x, y) \<in> t \<bullet> (x\<mapsto>y)}"
  let ?v = 
    "{ x y | (\<zcard>s + n + 1) \<le> x \<and> x \<le> \<zcard>t \<and> (x, y) \<in> t \<bullet> (x - (\<zcard>s + n), y)}"
  have domu: "\<zdom> ?u = (1..n)"
  proof (auto simp add: Domain_iff)
  apply_end (simp add: seq_index_bound [OF a2])
    fix x
    assume d0: "1 \<le> x" and d1: "x \<le> n" and d2: "x \<in> zInts"
    have "(0::\<arithmos>) \<le> zcard s" by (rule zNats_le0 [OF zNats_zcard])
    with b1 d1 a3 have d1': "x \<le> \<zcard>t" by arith
    
    show "\<exists> y \<bullet> (x, y) \<in> t"
      apply (witness "t\<cdot>x")
      apply (rule seq_appl [OF a2 d2 d0 d1'])
    done
  qed 

  have domv: "\<zdom> ?v = 1..(\<zcard>t - (\<zcard>s + n))"
  proof (auto simp add: Domain_iff)
  apply_end (intro zInts_diff zInts_add)
  apply_end (simp_all add: seq_index_bound [OF a2] b00 zInts_zcard)
    fix y xa
  next
    fix x
    assume d0: "1 \<le> x" and d1: "x \<le> \<zcard>t - (\<zcard>s + n)" and d1a: "x\<in>zInts"
    let ?xa = "x + (\<zcard>s + n)"
    let ?y = "t\<cdot>?xa"
    have d2: "x = ?xa - (\<zcard>s + n)" by arith
    from d1 d0 have d3: "(\<zcard>s + n + 1) \<le> ?xa" by arith
    from a3 d1 d0 have d4: "?xa \<le> \<zcard>t" by arith
    have d5: "(?xa, ?y) \<in> t"
     apply (rule seq_appl [OF a2])
     apply (intro zInts_add b00 zInts_zcard d1a)
     apply (rule add_increasing2)
     apply (rule add_increasing2 [OF b0])
     apply (rule zNats_le0 [OF zNats_zcard])
     apply (rule d0)
     apply (rule d4)
     done
   from d2 d3 d4 d5 show 
     "\<exists> y xa \<bullet> 
       x = xa - (\<zcard>s + n) \<and> 
       (\<zcard>s + n + 1) \<le> xa \<and> xa \<le> \<zcard>t \<and> 
       (xa, y) \<in> t"
     apply (witness "?y")
     apply (witness "?xa")
     apply simp
   done
  qed


  have useq: "?u \<in> \<zseq> (\<zran> t)"
  proof (intro seqIa [where ?n = "n"])
  apply_end (simp add: Z_zNats_zInts_conv b00 b0)
    have ftn: "functional ?u"
      apply (insert seq_functional [OF a2])
      apply (auto intro!: functionalI elim!: functionalE)
      done
   
    have ran: "\<zran> ?u \<subseteq> \<zran> t" by auto
    from ftn domu ran show "?u \<in> (1..n) \<ztfun> (\<zran> t)" by (mauto(fspace))
  qed
  from seq_transitive [OF a2 [THEN seq_ran] useq]
  have useq': "?u \<in> \<zseq> X" by auto
  have cardu: "\<zcard>?u = n"
  proof -
    have "\<zcard>?u = \<zcard>(\<zdom> ?u)" by (rule seq_zcard_dom [OF useq])
    also have "\<dots> = \<zcard>(1..n)" by (simp only: domu)
    also have "\<dots> = n" 
      apply (rule zint_range_zcard_from_1)
      apply (simp add: Z_zNats_zInts_conv b00 b0)
    done
    finally show "\<zcard>?u = n" by auto
  qed

  have vseq: "?v \<in> \<zseq> (\<zran> t)"
  proof (rule seqIa [where ?n = "\<zcard>t - (\<zcard>s + n)"])
  apply_end (intro zNats_diff zNats_zcard zNats_add)
  apply_end (simp add: Z_zNats_zInts_conv b00 b0)
  apply_end (insert b1, simp)
    have ftn: "functional ?v"
    proof (auto intro!: functionalI)
      fix xb y ya
      assume d1: "xb \<le> \<zcard>t" and d2: "(\<zcard>s + n + 1) \<le> xb"
      and d3: "(xb, y) \<in> t" and d4: "(xb, ya) \<in> t"
      with d3 seq_functional [OF a2] d4 show "y = ya" by (auto elim!: functionalE)
    qed
   
    have ran: "\<zran> ?v \<subseteq> \<zran> t" by auto
    from ftn domv ran show 
      "?v \<in> 1..(\<zcard>t - (\<zcard>s + n)) \<ztfun> (\<zran> t)" 
      by (mauto(fspace))
  qed
  from seq_transitive [OF a2 [THEN seq_ran] vseq]
  have vseq': "?v \<in> \<zseq> X" by auto
  have cardv: "\<zcard>?v = \<zcard>t - (\<zcard>s + n)"
  proof -
    have 
      "\<zcard>?v 
      = \<zcard>(\<zdom> ?v)" 
      by (rule seq_zcard_dom [OF vseq])
    also have "\<dots> 
      = \<zcard>(1..(\<zcard>t - (\<zcard>s + n)))" 
      by (simp only: domv)
    also have "\<dots> 
      = \<zcard>t - (\<zcard>s + n)" 
      apply (rule zint_range_zcard_from_1)
      apply (intro zNats_diff zNats_zcard zNats_add)
      apply (simp add: Z_zNats_zInts_conv b00 b0)
      apply (insert b1, simp)
    done
    finally show "\<zcard>?v = \<zcard>t - (\<zcard>s + n)" by auto
  qed

  have concat: "?u\<zcat>s\<zcat>?v = t"
  proof -
    have d0: "stranslate s n = {x y | n + 1 \<le> x \<and> x \<le> n + \<zcard>s \<and> (x, y) \<in> t \<bullet> x \<mapsto> y}"
    proof -
      let ?b = "{x y | x \<in> zInts \<and> n + 1 \<le> x \<and> x \<le> n + \<zcard>s \<and> (x, y) \<in> t \<bullet> x \<mapsto> y}"
      let ?a = "{ x y | x \<in> zInts \<and> 1 \<le> x \<and> x \<le> \<zcard>s \<and> (x + n, y) \<in> t \<bullet> x \<mapsto> y}"
      have e0: "?a \<in> \<zseq> X"
        apply (rule seqIa [where ?n = "\<zcard>s", OF zNats_zcard])
        apply (mauto(fspace))
        apply (insert seq_functional [OF a2] a3 seq_ran [OF a2])
        apply (auto intro!: functionalI elim!: functionalE simp add: Z_dom_def Z_ran_def eind_def)
      proof -
        fix x 
        assume f0: "1 \<le> x" and f1: "x \<le> \<zcard>s" and f2: "x \<in> zInts"
        from a3 f1 have f1': "x \<le> \<zcard>t" by arith
        show "\<exists> y \<bullet> (x + n, y) \<in> t"
          apply (witness "t\<cdot>(x + n)")
          apply (rule seq_appl [OF a2])
          apply (insert f0 b00 b0 b1 f2)
          apply (intro zInts_add, simp_all)
          apply (insert f1 f1')
          apply arith
        done
      qed
      have e1: "stranslate ?a n = ?b"
      proof (auto simp add: stranslate_def)
      apply_end (simp_all add: seq_index_bound [OF a2])
        fix a b
        assume f0: "n + 1 \<le> a" and f1: "a \<le> n + \<zcard>s" and f2: "(a, b) \<in> t"
        show " \<exists> r \<bullet> a = r + n \<and> r \<in> zInts \<and> 1 \<le> r \<and> r \<le> \<zcard>s \<and> (r + n, b) \<in> t"
          apply (witness "a - n")
          apply (intro conjI)
          apply (insert f0 f1 f2 b0 b1)
          apply arith
          apply simp_all
          apply (intro zInts_diff b00)
          apply (simp_all add: seq_index_bound [OF a2])
        done
      qed
      show ?thesis
        apply (subst b2)
        apply (simp add: sxtract_def dres_def del: split_eta_SetCompr2)
        apply (subst e1 [THEN sym])
        apply (simp add: ssquash_stranslate [OF e0] del: split_eta_SetCompr2)
        apply (simp add: e1 del: split_eta_SetCompr2)
        apply (auto simp add: set_eq_def del: split_eta_SetCompr2)
        apply (simp add: seq_index_bound [OF a2])
      done
    qed

    have d1: "stranslate ?v (n + \<zcard>s) = { x y | (\<zcard>s + n + 1) \<le> x \<and> x \<le> \<zcard>t \<and> (x, y) \<in> t \<bullet> x \<mapsto> y}"
    proof (auto simp add: stranslate_def)    
      fix a b
      assume e0: "(\<zcard>s + n + 1) \<le> a" and e1: "a \<le> \<zcard>t" and e2: "(a, b) \<in> t"
      have e3: "n + \<zcard>s = \<zcard>s + n" by arith
      let ?r = "a - (n + \<zcard>s)"
      show "\<exists> r \<bullet> a = r + (n + \<zcard>s) \<and> (\<exists> x \<bullet> r = x - (\<zcard>s + n) \<and> (\<zcard>s + n + 1) \<le> x \<and> x \<le> \<zcard>t \<and> (x, b) \<in> t)"
        apply (witness "?r")
        apply (intro conjI)
        apply (insert e3 e0)
        apply arith
        apply (witness "a")
        apply (intro conjI)
        apply arith
        apply simp_all
        apply (rule e1)
        apply (rule e2)
        done
    qed
    show ?thesis
      apply (simp add: sconcat_redef [OF sconcat_closed [OF useq' a1] vseq']  del: split_eta_SetCompr2)
      apply (simp add: Z_sconcat_zcard [OF useq' a1] del: split_eta_SetCompr2)
      apply (simp only: cardu del: split_eta_SetCompr2)
      apply (simp add: sconcat_redef [OF useq' a1] del: split_eta_SetCompr2)
      apply (simp only: cardu del: split_eta_SetCompr2)
      apply (simp add: d0 d1)
      apply (insert seq_dom [OF a2])
      apply (auto simp add: set_eq_def linorder_not_le)
      apply (subst zInts_le_add1_eq_le [THEN sym])
      apply (rule a2 [THEN seq_index_bound, THEN conjunct1], simp_all add: b00)
      apply (subst zInts_le_add1_eq_le [THEN sym])
      apply (rule a2 [THEN seq_index_bound, THEN conjunct1], simp_all add: b00)
      apply (intro zInts_add b00 zInts_zcard)
    done
  qed
   

  show "s \<infix> t"
    apply (simp add: sinfix_def)
    apply (witness "?u")
    apply (intro conjI)
    apply (rule useq)
    apply (witness "?v")
    apply (intro conjI)
    apply (rule vseq)
    apply (rule concat)
  done
qed


section {* Relational Operations *}


text {*

Relational operations on sequences. (pg. 120)

*}

lemma Z_sempty_rel_bcomp:
  "f \<zbcomp> \<sempty> = \<sempty>"
  by (simp add: sempty_def rel_bcomp_def glambda_def)

lemma seq_rel_bcomp_functional:
  assumes a1: "s \<in> \<zseq> X" and a2: "f \<in> X \<ztfun> Y"
  shows "functional (f \<zbcomp> s)"
  using a1 a2 seq_functional [OF a1]
    by (mauto(fspace))

lemma seq_rel_bcomp_dom:
  assumes a1: "s \<in> \<zseq> X" and a2: "f \<in> X \<ztfun> Y"
  shows "\<zdom> (f \<zbcomp> s) = (1..\<zcard>s)"
  apply (insert seq_dom [OF a1])
  apply (auto simp add: Domain_iff rel_bcomp_def glambda_def)
proof -
  fix x
  assume b0: "1 \<le> x" and b1: "x \<le> \<zcard>s" and b00: "x\<in>zInts"
  let ?ya = "s\<cdot>x"
  let ?y = "f\<cdot>?ya"

  have b2: "s\<cdot>x \<in> X"
  proof -
    have "s\<cdot>x \<in> \<zran> s"
      apply (simp add: Range_iff Domain_iff)
      apply (witness "x")
      apply (rule seq_appl [OF a1])
      apply (insert b00 b0 b1)
      apply simp_all
      done
    with seq_ran [OF a1] show ?thesis by auto
  qed

  show "\<exists> y ya \<bullet> (x, ya) \<in> s \<and> (ya, y) \<in> f"
    apply (witness "?y")
    apply (witness "?ya")
    apply (intro conjI)
    apply (rule seq_appl [OF a1])
    apply (insert b0 b00, simp_all)
    apply (rule b1)
    apply (intro functional_appl)
    apply (insert a2)
    apply (mauto(fspace))
    apply (insert a2)
    apply (insert b2)
    apply (mauto(fspace))
    done   
qed

lemma seq_rel_bcomp_ran:
  assumes a1: "s \<in> \<zseq> X" and a2: "f \<in> X \<ztfun> Y"
  shows "\<zran> (f \<zbcomp> s) \<subseteq> Y"
proof -
  have "\<zran> (f \<zbcomp> s) \<subseteq> \<zran> f" by (simp add: bcomp_ran)
  also have "\<dots> \<subseteq> Y" by (insert a2, (mauto(fspace)))
  finally show ?thesis by this
qed


lemma seq_rel_comp_seq:
  assumes a1: "s \<in> \<zseq> X" and a2: "f \<in> X \<ztfun> Y"
  shows "f \<zbcomp> s \<in> \<zseq> Y"
proof (rule seqIa [where ?n = "\<zcard>s", OF zNats_zcard])
  from seq_rel_bcomp_functional [OF a1 a2] seq_rel_bcomp_dom [OF a1 a2] seq_rel_bcomp_ran [OF a1 a2]
  show "f \<zbcomp> s \<in> (1..\<zcard>s) \<ztfun> Y" by (mauto(fspace))
qed

lemma Z_seq_rel_bcomp_zcard:
  assumes a1: "s \<in> \<zseq> X" and a2: "f \<in> X \<ztfun> Y"
  shows "\<zcard>(f \<zbcomp> s) = \<zcard>s"
  apply (simp add: seq_zcard_dom [OF seq_rel_comp_seq [OF a1 a2]])
  apply (simp add: seq_rel_bcomp_dom [OF a1 a2] zint_range_zcard_from_1 [OF zNats_zcard])
done

lemma seq_rel_bcomp_beta:
  assumes a1: "s \<in> \<zseq> X" and a2: "f \<in> X \<ztfun> Y"
  and a3: "i \<in> 1..(\<zcard>s)"
  shows "(f \<zbcomp> s)\<cdot>i = f\<cdot>(s\<cdot>i)"
proof (intro functional_beta)
  show "functional (f \<zbcomp> s)" by (rule seq_rel_bcomp_functional [OF a1 a2])
  
  from a2 have a2': "functional f" by (mauto(fspace))
  have b0: "s\<cdot>i \<in> X"
  proof -
    have "s\<cdot>i \<in> \<zran> s"
      apply (simp add: Range_iff Domain_iff)
      apply (witness "i")
      apply (rule seq_appl [OF a1])
      apply (insert a3)
      apply auto
    done
    also have "\<dots> \<subseteq> X" by (rule seq_ran [OF a1])
    finally show ?thesis by this
  qed

  show "(i, f\<cdot>(s\<cdot>i)) \<in> f \<zbcomp> s"
    apply (simp add: rel_bcomp_def glambda_def)
    apply (witness "s\<cdot>i")
    apply (rule conjI)
    apply (rule seq_appl [OF a1])
    apply (insert a3)
    apply simp_all
    apply (intro functional_appl)
    apply (rule a2')
    apply (insert b0 a2)
    apply (mauto(fspace))
    done
qed

lemma Z_seq_rel_bcomp_beta:
  assumes a1: "s \<in> \<zseq> X" and a2: "f \<in> X \<ztfun> Y"
  shows "\<forall> i | i \<in> (1..\<zcard>s) \<bullet> (f \<zbcomp> s)\<cdot>i = f\<cdot>(s\<cdot>i)"
  apply (msafe(inference))
  apply (rule seq_rel_bcomp_beta [OF a1 a2])
  apply simp
  done

lemma Z_sunit_rel_bcomp:
  assumes a1: "x \<in> X" and a2: "f \<in> X \<ztfun> Y"
  shows "f \<zbcomp> \<lang>x\<rang> = \<lang>f\<cdot>x\<rang>"
  apply (simp add: sinsert_def)
  apply (simp add: stranslate_sempty)
  apply (simp add: sempty_def rel_oride_def Domain_iff dsub_def)
  apply (auto simp add: rel_bcomp_def glambda_def)
  apply (rule functional_beta [THEN sym])
  apply (insert a2)
  apply (mauto(fspace))
  apply (rule functional_appl)
  apply (mauto(fspace))
  apply (insert a2 a1)
  apply (mauto(fspace))
  done

lemma Z_sconcat_rel_bcomp:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X" and a3: "f \<in> X \<ztfun> Y"
  shows "f \<zbcomp> (s\<zcat>t) = (f \<zbcomp> s)\<zcat>(f\<zbcomp> t)"
  apply (simp add: sconcat_redef [OF a1 a2])
  apply (simp add: sconcat_redef [OF seq_rel_comp_seq [OF a1 a3] seq_rel_comp_seq [OF a2 a3]])
  apply (simp add: Z_seq_rel_bcomp_zcard [OF a1 a3])
  apply (simp add: rel_bcomp_def glambda_def)
  apply (auto simp add: stranslate_def)
  done

lemma Z_srev_rel_bcomp:
  assumes a1: "s \<in> \<zseq> X" and a2: "f \<in> X \<ztfun> Y"
  shows "\<zrev> (f \<zbcomp> s) = f \<zbcomp> \<zrev>s"
proof (rule seq_induct [OF a1])
  show "\<zrev> (f \<zbcomp> \<sempty>) = f \<zbcomp> \<zrev>\<sempty>"
    by (simp add: Z_sempty_rel_bcomp Z_srev_sempty)
next
  fix xs x
  assume b0: "xs \<in> \<zseq> X" and b1: "x \<in> X" and b2: "\<zrev>(f \<zbcomp> xs) = f \<zbcomp> \<zrev>xs"
  from sunit_seq [OF b1] have b1': "\<lang>x\<rang> \<in> \<zseq> X" by this
  

  show "\<zrev> (f \<zbcomp> (\<lang>x\<rang> \<zcat> xs)) = f \<zbcomp> (\<zrev> (\<lang>x\<rang> \<zcat> xs))"
    apply (simp add: Z_sconcat_rel_bcomp [OF b1' b0 a2])
    apply (simp add: Z_srev_sconcat [OF seq_rel_comp_seq [OF b1' a2] seq_rel_comp_seq [OF b0 a2]])
    apply (simp add: Z_srev_sconcat [OF b1' b0] b2 Z_srev_sunit)
    apply (simp add: Z_sconcat_rel_bcomp [OF srev_closed [OF b0] b1' a2])
    apply (simp add: Z_sunit_rel_bcomp [OF b1 a2] Z_srev_sunit)
    done
qed

lemma sfilter_rel_bcomp_sunit:
  assumes a1: "x \<in> X" and a2: "f \<in> X \<ztfun> Y"
  shows "(f \<zbcomp> \<lang>x\<rang>) \<restriction> V = f \<zbcomp> (\<lang>x\<rang> \<restriction> (f\<^sup>\<sim>)\<zlImg>V\<zrImg>)"
proof -
  from sunit_seq [OF a1] have a1': "\<lang>x\<rang> \<in> \<zseq> X" by this

  have a3: "(x, f\<cdot>x) \<in> f"
    apply (rule functional_appl)
    apply (insert a2 a1, (mauto(fspace)))
    done
 
  have c0: "{i::real | i = 1 \<and> i < 1} = \<emptyset>" by auto
  have b0: "f\<cdot>x \<in> V \<Rightarrow> ((f \<zbcomp> \<lang>x\<rang>) \<restriction> V = f \<zbcomp> \<lang>x\<rang>)"
    apply (simp add: Z_sunit_rel_bcomp [OF a1 a2])
    apply (simp add: sfilter_def rres_def)
    apply (simp add: sinsert_def sempty_def stranslate_def rel_oride_rid eind_def)
    apply (auto simp add: ssquash_def)
    apply (auto simp add: bounded_card_def c0 fin_funappl)
    done

  have c1: "{ i::real | i = 1 \<and> (\<exists> xa \<bullet> xa \<in> V \<and> (x, xa) \<in> f) \<and> i < 1 } = \<emptyset>" by auto
  have b1: "f\<cdot>x \<in> V \<Rightarrow> \<lang>x\<rang> \<restriction> (f\<^sup>\<sim>)\<zlImg>V\<zrImg> = {(1, x)}"
    apply (simp add: sfilter_def rres_def)
    apply (simp add: sinsert_def sempty_def stranslate_def rel_oride_rid converse_def eind_def)
    apply (simp add: eind_norm [of "Collect"] ex_simps' del: ex_simps)
    apply (auto simp add: ssquash_def bounded_card_def c1 Z_dom_def less_le zcard_def)
    apply (rule functional_beta)
    apply (insert a2, mauto(fspace))
    apply (auto elim!: functionalE intro!: functionalI)
    apply (rule functional_beta [THEN sym])
    apply (insert a2, (mauto(fspace)))
    apply (auto elim!: functionalE intro!: functionalI)
    apply (witness "f\<cdot>x")
    apply (simp add: a3)
    apply (witness "f\<cdot>x")
    apply (simp add: a3)
    done

  have b2: "f\<cdot>x \<notin> V \<Rightarrow> (f \<zbcomp> \<lang>x\<rang>) \<restriction> V = \<sempty>"
  proof (msafe(inference))
    assume d0: "f\<cdot>x \<notin> V"
    from d0 have d1: "{ (xa::real) y | y \<in> V \<and> xa = 1 \<and> y = f\<cdot>x \<bullet> xa\<mapsto>y} = \<emptyset>" by auto
    from d0 show "(f \<zbcomp> \<lang>x\<rang>) \<restriction> V = \<sempty>"
      apply (simp add: sfilter_def rres_def Z_sunit_rel_bcomp [OF a1 a2] del: split_eta_SetCompr2)
      apply (simp add: sinsert_def sempty_def stranslate_def rel_oride_rid d1)
      apply (simp add: ssquash_def bounded_card_def rel_oride_mem Z_dom_def)
      done
  qed

  have b3: "f\<cdot>x \<notin> V \<Rightarrow>  \<lang>x\<rang> \<restriction> (f\<^sup>\<sim>)\<zlImg>V\<zrImg> = \<sempty>"
  proof (msafe(inference))
    assume d0: "f\<cdot>x \<notin> V"
    have "\<forall> b \<bullet> (x, b) \<in> f \<Rightarrow> b = f\<cdot>x"
      apply auto
      apply (rule functional_beta [THEN sym])
      apply (insert a2, (mauto(fspace)))
      done
    with d0 have d1: "{ (xa::real) y | (\<exists> x \<bullet> x \<in> V \<and> (y, x) \<in> f) \<and> xa = 1 \<and> y = x \<bullet> xa\<mapsto>y} = \<emptyset>" by auto
    from d0 show "\<lang>x\<rang> \<restriction> (f\<^sup>\<sim>)\<zlImg>V\<zrImg> = \<sempty>"
      apply (simp add: sfilter_def rres_def del: split_eta_SetCompr2)
      apply (simp add: sinsert_def sempty_def stranslate_def rel_oride_rid converse_def d1)
      apply (simp add: ssquash_def bounded_card_def rel_oride_mem Domain_iff)
      apply (msafe_no_assms(inference))
      apply (rule contrapos_nn, assumption)
      apply (subst a2 [THEN tfun_beta], assumption+)
      done
  qed
    


  show ?thesis
    apply (cases "f\<cdot>x \<in> V")
    apply (simp add: b0 [rule_format])
    apply (simp add: b1 [rule_format])
    apply (simp add: sinsert_def stranslate_sempty)
    apply (simp add: sempty_def rel_oride_rid)
    apply (simp add: b2 [rule_format])
    apply (simp add: b3 [rule_format])
    apply (simp add: Z_sempty_rel_bcomp)
    done
qed

lemma Z_sfilter_rel_bcomp:
  assumes a1: "s \<in> \<zseq> X" and a2: "f \<in> X \<ztfun> Y"
  shows "(f \<zbcomp> s) \<restriction> V = f \<zbcomp> (s \<restriction> (f\<^sup>\<sim>)\<zlImg>V\<zrImg>)"
proof (rule seq_induct [OF a1])
  show "(f \<zbcomp> \<sempty>) \<restriction> V = f \<zbcomp> (\<sempty> \<restriction> (f\<^sup>\<sim>)\<zlImg>V\<zrImg>)"
    by (simp add: Z_sempty_rel_bcomp sfilter_sempty)
next
  fix xs x
  assume b0: "xs \<in> \<zseq> X" and b1: "x \<in> X" and 
  b2: "(f \<zbcomp> xs) \<restriction> V = f \<zbcomp> (xs \<restriction> (f\<^sup>\<sim>)\<zlImg>V\<zrImg>)"
  from sunit_seq [OF b1] have b1': "\<lang>x\<rang> \<in> \<zseq> X" by this

  show "(f \<zbcomp> (\<lang>x\<rang> \<zcat> xs)) \<restriction> V = f \<zbcomp> ((\<lang>x\<rang> \<zcat> xs) \<restriction> (f\<^sup>\<sim>)\<zlImg>V\<zrImg>)"
    apply (simp add: Z_sconcat_rel_bcomp [OF b1' b0 a2])
    apply (simp add: Z_sconcat_sfilter [OF seq_rel_comp_seq [OF b1' a2] seq_rel_comp_seq [OF b0 a2]])
    apply (simp add: b2)
    apply (simp add: Z_sconcat_sfilter [OF b1' b0])
    apply (simp add: Z_sconcat_rel_bcomp [OF sfilter_closed [OF b1'] sfilter_closed [OF b0] a2])
    apply (simp add: sfilter_rel_bcomp_sunit [OF b1 a2])
    done
qed


    
section {* Distributed Concatination *}


definition
  sdistrib_concat :: "'a set \<rightarrow> 'a seqT seqT \<rightarrow> 'a seqT"
where
  sdistrib_concat_def : "sdistrib_concat X \<defs> seq_rec (\<zseq> X) \<sempty> (\<olambda> x s b \<bullet> x\<zcat>b)"

notation (xsymbols)
  sdistrib_concat ("\<zcat>'/[_] _" [1000, 101] 99)

syntax (zed)
  "_Z_Sequence\<ZZ>sdistrib_concata" :: "[logic, logic] \<rightarrow> logic" ("\<^sdistriba>{:_:} _" [1000, 101] 99)

translations
  "_Z_Sequence\<ZZ>sdistrib_concata X" \<rightharpoonup> "CONST Z_Sequence.sdistrib_concat X"



lemma sdistrib_sempty:
  shows "\<zcat>/[X] \<sempty> \<defs> \<sempty>"
  by (simp add: sdistrib_concat_def seq_rec_sempty)
 

lemma sdistrib_closed:
  assumes a1: "s \<in> \<zseq> (\<zseq> X)"
  shows "\<zcat>/[X] s \<in> \<zseq> X"
proof (induct "s" rule: seq_induct, rule a1)
  show "\<zcat>/[X] \<sempty> \<in> \<zseq> X"
    apply (simp add: sdistrib_sempty)
    apply (rule sempty_seq)
    done
next
  fix xs x
  assume b0: "xs \<in> \<zseq> (\<zseq> X)" and b1: "x \<in> \<zseq> X" and b2: "\<zcat>/[X] xs \<in> \<zseq> X"
  then show "\<zcat>/[X] (sconcat \<lang>x\<rang> xs) \<in> \<zseq> X"
    apply (subst sinsert_sconcat [THEN sym, OF b0 b1])
    apply (simp add: sdistrib_concat_def)
    using a1 
    apply (simp add: seq_rec_sinsert)
    apply (rule sconcat_closed)
    apply assumption
    apply (simp add: sdistrib_concat_def)
    done
qed
    
lemma sdistrib_sunit:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zcat>/[X] \<lang>s\<rang> = s"
  apply (simp add: sdistrib_concat_def)
  apply (insert a1 sempty_seq [of "\<zseq> X"])
  apply (simp add: seq_rec_sinsert)
  apply (simp add: seq_rec_sempty)
  apply (simp add: Z_sconcat_sempty [OF a1])
  done

lemma Z_sdistrib_sunit:
  assumes a1: "s \<in> \<zseq> X"
  shows "\<zcat>/[X] \<lang>s\<rang> \<defs> s"
  using a1
  by (auto simp add: sdistrib_sunit)


lemma Z_sdistrib_sinsert_seq:
  assumes a1: "s \<in> \<zseq> X" and a2: "t \<in> \<zseq> X"
  shows "\<zcat>/[X] \<lang>s, t\<rang> = s\<zcat>t"
proof (simp add: sdistrib_concat_def)
  have b0: "\<lang>t\<rang> \<in> \<zseq> (\<zseq> X)"
    by (rule sunit_seq [OF a2])
  have b1: "\<sempty> \<in> \<zseq> (\<zseq> X)" by (rule sempty_seq)
  show "seq_rec (\<zseq> X) \<sempty> (\<olambda> x s \<bullet> op\<zcat>x) \<lang>s, t\<rang> = s\<zcat>t"
    apply (simp add: seq_rec_sinsert [OF b0 a1])
    apply (simp add: seq_rec_sinsert [OF b1 a2])
    apply (simp add: seq_rec_sempty)
    apply (simp add: Z_sconcat_sempty [OF a2])
    done
qed



lemma sdistrib_sconcat:
  assumes a1: "s \<in> \<zseq> (\<zseq> X)" and a2: "t \<in> \<zseq> (\<zseq> X)"
  shows "\<zcat>/[X] (s\<zcat>t) = (\<zcat>/[X] s)\<zcat>(\<zcat>/[X] t)"
proof (induct "s" rule: seq_induct, rule a1)
  have b0: "\<sempty> \<in> \<zseq> (\<zseq> X)" by (rule sempty_seq)
  show "\<zcat>/[X] (\<sempty>\<zcat>t) = (\<zcat>/[X] \<sempty>)\<zcat>(\<zcat>/[X] t)"
    by (simp add: Z_sconcat_sempty [OF a2] sdistrib_sempty Z_sconcat_sempty [OF sdistrib_closed [OF a2]])
next
  apply_end (subst sinsert_sconcat [THEN sym], simp_all)
  apply_end (subst sinsert_sconcat [THEN sym], simp_all)
  fix xs x
  assume 
    b0: "xs \<in> \<zseq> (\<zseq> X)" and 
    b1: "x \<in> \<zseq> X" and 
    b2: "\<zcat>/[X] (xs\<zcat>t) = (\<zcat>/[X] xs)\<zcat>(\<zcat>/[X] t)"
  with a2 have "\<zcat>/[X] ((sinsert x xs)\<zcat>t) = \<zcat>/[X] (sinsert x (xs\<zcat>t))"
    by (simp add: sinsert_sconcat_assoc)
  also have "\<dots> = x\<zcat>(\<zcat>/[X] (xs\<zcat>t))"
    apply (simp add: sdistrib_concat_def)
    apply (insert a2 b1 b2 sconcat_closed [OF b0 a2])
    apply (simp add: seq_rec_sinsert sdistrib_closed)
    done
  also have "\<dots> = x\<zcat>((\<zcat>/[X] xs)\<zcat>(\<zcat>/[X] t))" by (simp add: b2)
  also have "\<dots> = (x\<zcat>(\<zcat>/[X] xs))\<zcat>(\<zcat>/[X] t)"
    apply (rule Z_sconcat_assoc [THEN sym])
    apply (rule b1)
    apply (rule sdistrib_closed [OF b0])
    apply (rule sdistrib_closed [OF a2])
    done
  also have "\<dots> = (\<zcat>/[X] (sinsert x xs))\<zcat>(\<zcat>/[X] t)"
    apply (simp add: sdistrib_concat_def)
    apply (insert a2 b0 b1 b2 sconcat_closed [OF b0 a2])
    apply (simp add: seq_rec_sinsert sdistrib_closed)
    done
  finally show 
    "\<zcat>/[X] ((sinsert x xs)\<zcat>t) = (\<zcat>/[X] (sinsert x xs))\<zcat>(\<zcat>/[X] t)" 
    by this
qed

lemma Z_sdistrib_sconcat:
  assumes a1: "s \<in> \<zseq> (\<zseq> X)" "t \<in> \<zseq> (\<zseq> X)"
  shows "\<zcat>/[X] (s\<zcat>t) \<defs> (\<zcat>/[X] s)\<zcat>(\<zcat>/[X] t)"
  using a1
  by (auto simp add: sdistrib_sconcat)


lemma sdistrib_sinsert:
  assumes a1: "xs \<in> \<zseq> (\<zseq> X)" and a2: "x \<in> \<zseq> X"
  shows "\<zcat>/[X] (sinsert x xs) = x\<zcat>(\<zcat>/[X] xs)"
  apply (simp add: sinsert_sconcat [OF a1 a2])
  apply (subst sdistrib_sconcat)
  apply (rule sunit_seq [OF a2])
  apply (rule a1)
  apply (simp add: sdistrib_sunit [OF a2])
  done

lemma srev_sdistrib:
  assumes a1: "s \<in> \<zseq> (\<zseq> X)"
  shows 
    "\<graphof> srev \<zbcomp> s = { a b | (a, b) \<in> s \<bullet> (a, \<zrev>b)}" 
    "\<graphof> srev \<zbcomp> s \<in> \<zseq> (\<zseq> X)"
proof -
  show b0: "\<graphof> srev \<zbcomp> s = { a b | (a, b) \<in> s \<bullet> (a, \<zrev> b)}"
    by (auto simp add: graph_of_def rel_bcomp_def glambda_def) 
  show "\<graphof> srev \<zbcomp> s \<in> \<zseq> (\<zseq> X)"
    apply (simp add: b0)
   proof (rule seqIa [where ?n = "\<zcard>s", OF zNats_zcard])
     have ftn: "functional { a b | (a, b) \<in> s \<bullet> (a, \<zrev> b)}"
       by (auto 
             intro!: functionalI elim!: functionalE 
             dest: seq_functional [OF a1, THEN functionalD]) 
     have dom: "\<zdom> { a b | (a, b) \<in> s \<bullet> (a, \<zrev>b)} = (1..\<zcard>s)"
     proof -
       have "\<zdom> { a b | (a, b) \<in> s \<bullet> (a, \<zrev>b)} = \<zdom> s" by (auto simp add: Z_dom_def)
       also have "\<dots> = (1..\<zcard>s)" by (simp add: seq_dom [OF a1])
       finally show ?thesis by this
     qed
     have ran: "\<zran> { a b | (a, b) \<in> s \<bullet> (a, \<zrev>b)} \<subseteq> \<zseq> X"
     proof auto
       fix a b
       assume "(a, b) \<in> s" 
       with seq_ran [OF a1] have "b \<in> \<zseq> X" by auto
       then show "\<zrev>b \<in> \<zseq> X" by (rule srev_closed)
     qed
     from ftn dom ran show "{ a b | (a, b) \<in> s \<bullet> (a, \<zrev>b)} \<in> (1..\<zcard>s) \<ztfun> \<zseq> X" by (mauto(fspace)) 
   qed
qed

lemma Z_srev_sdistrib:
  assumes 
    a1: "q \<in> \<zseq> (\<zseq> X)"
  shows 
    "\<zrev>(\<zcat>/[X] q) = \<zcat>/[X] (\<zrev> ((\<graphof> srev) \<zbcomp> q))"
proof (induct "q" rule: seq_induct, rule a1)
  have b0: "\<zrev>(\<zcat>/[X] \<sempty>) = \<sempty>"
    by (simp add: sdistrib_sempty Z_srev_sempty)

  have b00: "((\<graphof> srev) \<zbcomp> \<sempty>) = \<sempty>" 
  by (simp add: sempty_def graph_of_def rel_bcomp_def)

  then have b1: "\<zcat>/[X] (\<zrev>((\<graphof> srev) \<zbcomp> \<sempty>)) = \<sempty>"
    apply (subst b00)
    apply (simp add: Z_srev_sempty)
    apply (insert sdistrib_sempty [of "X"])
    apply (simp add: sempty_def)
  done

  from b0 b1 show 
    "\<zrev>(\<zcat>/[X] \<sempty>) = \<zcat>/[X] (\<zrev>((\<graphof> srev) \<zbcomp> \<sempty>))" 
    by simp
next
  apply_end (subst sinsert_sconcat [THEN sym], simp_all)
  apply_end (subst sinsert_sconcat [THEN sym], simp_all)
  fix xs x
  assume b0: "xs \<in> \<zseq> (\<zseq> X)" and b1: "x \<in> \<zseq> X" 
  and b2: "\<zrev>(\<zcat>/[X] xs) = \<zcat>/[X] (\<zrev> ((\<graphof> srev) \<zbcomp> xs))"

  have b3: "\<zcat>/[X] xs \<in> \<zseq> X"
    by (rule sdistrib_closed [OF b0])

  from b3 have b3': "seq_rec (\<zseq> X) \<sempty> (\<olambda> x s \<bullet> op\<zcat>x) xs \<in> \<zseq> X"
    by (simp add: sdistrib_concat_def)

  have b4: 
    "\<zrev>((seq_rec (\<zseq> X) \<sempty> (\<olambda> x s \<bullet> op\<zcat>x) xs)) 
    = \<zcat>/[X] (\<zrev>( (\<graphof> srev) \<zbcomp> xs))"
  proof -
    have 
      "\<zcat>/[X] xs 
      = (seq_rec (\<zseq> X) \<sempty> (\<olambda> x s \<bullet> op\<zcat>x) xs)" 
      by (simp add: sdistrib_concat_def)
    with b2 show ?thesis by auto
  qed

  have b5: 
    "\<zrev>(\<zcat>/[X] (sinsert x xs)) 
    = (\<zcat>/[X] (\<zrev> ((\<graphof> srev) \<zbcomp> xs)))\<zcat>(\<zrev> x)"
    apply (subst sdistrib_concat_def)
    apply (simp add: seq_rec_sinsert [OF b0 b1])
    apply (simp add: Z_srev_sconcat [OF b1 b3'])
    apply (simp add: b4)
    done

  have b7: "\<graphof> srev \<zbcomp> xs \<in> \<zseq> (\<zseq> X)"
    by (rule srev_sdistrib [OF b0])

  have b6: "\<graphof> srev \<zbcomp> sinsert x xs = sinsert (\<zrev> x) (\<graphof> srev \<zbcomp> xs)"
    apply (auto)
    apply (simp add: Z_rel_bcomp_mem)
    apply ((msafe(inference)))
  proof -
    fix a y z
    assume c0: "(a, y) \<in> sinsert x xs" and c1: "(y, z) \<in> \<graphof> srev"
    from c0 have c2: "(a = 1 \<and> y = x) \<or> (a, y) \<in> stranslate xs (1)" 
    by (auto simp add: sinsert_def rel_oride_def Domain_iff dsub_def)
    from c1 have c3: "z = \<zrev> y" by (simp add: graph_of_def glambda_def)
    
    have c4: "a = 1 \<and> y = x \<Rightarrow> (a, z) \<in>  sinsert (\<zrev> x) (\<graphof> srev \<zbcomp> xs)"
    proof (msafe_no_assms(inference))
      assume d0: "a = 1" and d1: "y = x"
      have "(a, z) = (1, \<zrev> x)" by (simp add: d0 d1 c3)
      also have "\<dots> \<in> sinsert (\<zrev> x) (\<graphof> srev \<zbcomp> xs)"
        apply (subst sinsert_redef)
        apply (rule b7)
        apply (rule srev_closed [OF b1])
        apply simp
        done
      finally show "(a, z) \<in> sinsert (\<zrev> x) (\<graphof> srev \<zbcomp> xs)" by this
    qed

    from c2 have 
      c5: "\<not> (a = 1 \<and> y = x) \<Rightarrow> 
            (a, y) \<in> stranslate xs (1) \<Rightarrow> (a, z) \<in>  sinsert (\<zrev> x) (\<graphof> srev \<zbcomp> xs)"
      apply (intro impI conjI)
      apply (elim disjE)
      apply (intro c4 [rule_format])
      apply simp_all
      apply (subst sinsert_redef)
      apply (rule b7)
      apply (rule srev_closed [OF b1])
      apply simp_all
      apply (intro disjI2)
      apply (simp add: stranslate_def)
      apply (simp_all add: graph_of_def rel_bcomp_def glambda_def)
    proof -
      assume d0: "\<exists> n \<bullet> a = n + 1 \<and> (n, y) \<in> xs"
      from d0 obtain n where d1: "a = n + 1" and d2: "(n, y) \<in> xs" by auto
      show "\<exists> n \<bullet> a = n + 1 \<and> (\<exists> y \<bullet> (n, y) \<in> xs \<and> z = \<zrev> y)"
        apply (witness "n")
        apply (simp add: d1)
        apply (witness "y")
        apply (simp add: d2 c3)
        done
    qed


    show "(a, z) \<in> sinsert (\<zrev> x) (\<graphof> srev \<zbcomp> xs)"
      apply (cases "a = 1 \<and> y = x")
      apply (intro c4 [rule_format])
      apply simp_all
      apply (intro c5 [rule_format])
      apply (insert c2)
      apply auto
      done
  next
    fix a b
    assume c0: "(a, b) \<in> sinsert (\<zrev> x) (\<graphof> srev \<zbcomp> xs)"
    from c0 have 
      c1: "(a = 1 \<and> b = (\<zrev> x)) \<or> (a, b) \<in> stranslate (\<graphof> srev \<zbcomp> xs) (1)" 
      by (auto simp add: sinsert_def rel_oride_def Domain_iff dsub_def)

    have c2: "a = 1 \<and> b = (\<zrev> x) \<Rightarrow> (a, b) \<in> \<graphof> srev \<zbcomp> sinsert x xs"
      apply (auto simp add: graph_of_def rel_bcomp_def glambda_def)
      apply (witness "x")
      apply (simp add: sinsert_redef [OF b0 b1])
      done
  
    have 
      c3: "\<not> (a = 1 \<and> b = (\<zrev> x)) \<Rightarrow> 
            (a, b) \<in> stranslate (\<graphof> srev \<zbcomp> xs) (1)  \<Rightarrow> 
              (a, b) \<in> \<graphof> srev \<zbcomp> sinsert x xs"
      apply (msafe_no_assms_step(inference))
      apply (msafe_no_assms_step(inference))
(* J: XXX TODO come back here: msafe going too far! *)
      apply (simp add: stranslate_def)
      apply (simp add: sinsert_redef [OF b0 b1])
      apply (simp add: graph_of_def rel_bcomp_def glambda_def)
    proof -
      assume "\<exists> n \<bullet> a = n + 1 \<and> (\<exists> y \<bullet> (n, y) \<in> xs \<and> b = \<zrev>y)"
      then obtain n y where d0: "a = n + 1" and d1: "(n, y) \<in> xs" and d2: "b = \<zrev> y" by auto
      show "\<exists> y \<bullet> (a = 1 \<and> y = x \<or> (a, y) \<in> stranslate xs (1)) \<and> b = \<zrev>y"
        apply (witness "y")
        apply (rule conjI)
        apply (rule disjI2)
        using d0 d1
        apply (simp add: stranslate_def)
        apply (rule d2)
        done
    qed
      


    show "(a, b) \<in> \<graphof> srev \<zbcomp> sinsert x xs"
      apply (cases "a = 1 \<and> b = (\<zrev> x)")
      apply (intro c2 [rule_format])
      apply simp_all
      apply (intro c3 [rule_format])
      apply simp_all
      apply (insert c1)
      apply auto
      done
  qed
  

  have 
    b8: "\<zcat>/[X] (\<zrev>( (\<graphof> srev) \<zbcomp> (sinsert x xs))) 
        = (\<zcat>/[X] \<zrev> ((\<graphof> srev) \<zbcomp> xs))\<zcat>(\<zrev> x)"
    apply (simp add: b6)
    apply (subst srev_sinsert [OF b7 srev_closed [OF b1]])
    apply (subst sdistrib_sconcat)
    apply (rule srev_closed [OF b7])
    apply (rule sunit_seq)
    apply (rule srev_closed [OF b1])
    apply (subst sdistrib_sunit)
    apply (rule srev_closed [OF b1])
    apply simp
    done
    

  from b5 b8 show 
    "\<zrev> (\<zcat>/[X] (sinsert x xs)) 
    = \<zcat>/[X] (\<zrev>( (\<graphof> srev) \<zbcomp> (sinsert x xs)))" 
    by simp
qed


lemma Z_sdistrib_sfilter:
  assumes a1: "q \<in> \<zseq> (\<zseq> X)"
  shows "(\<zcat>/[X] q)\<restriction>V = \<zcat>/[V] ((\<glambda> s | s \<in> \<zseq> X \<bullet> s\<restriction>V) \<zbcomp> q)"
proof (rule seq_induct [OF a1])
  show "(\<zcat>/[X] \<sempty>)\<restriction>V = \<zcat>/[V] ((\<glambda> s | s \<in> \<zseq> X \<bullet> s\<restriction>V) \<zbcomp> \<sempty>)"
    apply (subst Z_sempty_rel_bcomp)
    apply (simp add: sdistrib_sempty sfilter_sempty)
    done
next
  apply_end (subst sinsert_sconcat [THEN sym], simp_all)
  apply_end (subst sinsert_sconcat [THEN sym], simp_all)
  fix xs x
  assume
    b0: "xs \<in> \<zseq> (\<zseq> X)" and 
    b1: "x \<in> \<zseq> X" and 
    b2: "(\<zcat>/[X] xs)\<restriction>V = \<zcat>/[V] ((\<glambda> s | s \<in> \<zseq> X \<bullet> s\<restriction>V) \<zbcomp> xs)"
  have 
    b3: "x\<restriction>V = \<zcat>/[V] ((\<glambda> s | s \<in> \<zseq> X \<bullet> s\<restriction>V) \<zbcomp> \<lang>x\<rang>)"
  proof -
    have 
      c0: "(\<glambda> s | s \<in> \<zseq> X \<bullet> s\<restriction>V) \<zbcomp> \<lang>x\<rang> = \<lang>x\<restriction>V\<rang>"
      apply (subst Z_sunit_rel_bcomp)
      apply (rule b1)
      apply (mauto(fspace))
      apply (simp add: glambda_def Domain_Collect_Zsplit eind_def Z_dom_def)
      apply (subst functional_beta)
      apply (simp_all add: glambda_def)
      apply (insert seq_functional [OF sfilter_closed [OF _]])
      apply (auto intro!: functionalI elim!: functionalE)
      apply (rule b1)
      done
    show ?thesis
      apply (simp add: c0)
      apply (subst sdistrib_sunit)
      apply (simp_all add: sfilter_closedV [OF b1])
      done
  qed
  have b4: "(\<glambda> s | s \<in> \<zseq> X \<bullet> s\<restriction>V) \<zbcomp> \<lang>x\<rang> \<in> \<zseq> (\<zseq> V)"
    apply (rule seq_rel_comp_seq [OF sunit_seq [OF b1]])
    apply (simp add: glambda_def)
    apply (mauto(fspace))
    apply (auto intro!: functionalI)
    apply (simp add: sfilter_closedV)
    done
  have b5: "(\<glambda> s | s \<in> \<zseq> X \<bullet> s\<restriction>V) \<zbcomp> xs \<in> \<zseq> (\<zseq> V)"
    apply (rule seq_rel_comp_seq [OF b0])
    apply (simp add: glambda_def)
    apply (mauto(fspace))
    apply (auto intro!: functionalI)
    apply (simp add: sfilter_closedV)
    done

  show 
    "(\<zcat>/[X] (sinsert x xs))\<restriction>V 
    = \<zcat>/[V] ((\<glambda> s | s \<in> \<zseq> X \<bullet> s\<restriction>V) \<zbcomp> (sinsert x xs))"
    apply (simp add: sdistrib_sinsert [OF b0 b1])
    apply (subst Z_sconcat_sfilter)
    apply (rule b1)
    apply (rule sdistrib_closed [OF b0])
    apply (simp add: sinsert_sconcat [OF b0 b1])
    apply (subst Z_sconcat_rel_bcomp)
    apply (rule sunit_seq [OF b1])
    apply (rule b0)
    apply (mauto(fspace))
    apply (simp add: Domain_Collect_Zsplit rel_bcomp_def glambda_def eind_def Z_dom_def)
    apply (subst sdistrib_sconcat [OF b4 b5])
    apply (simp add: b3 b2)
    done
qed
  
lemma Z_sdistrib_rel_bcomp:
  assumes 
    a1: "q \<in> \<zseq> (\<zseq> X)" and 
    a2: "f \<in> X \<ztfun> Y"
  shows 
    "f \<zbcomp> (\<zcat>/[X] q) = \<zcat>/[Y] ((\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<zbcomp> q)"
proof (rule seq_induct [OF a1])
  show "f \<zbcomp>  (\<zcat>/[X] \<sempty>) = \<zcat>/[Y] ((\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<zbcomp> \<sempty>)"
    by (simp add: sdistrib_sempty Z_sempty_rel_bcomp)
next
  apply_end (subst sinsert_sconcat [THEN sym], simp_all)
  apply_end (subst sinsert_sconcat [THEN sym], simp_all)
  fix xs x
  assume 
    b0: "xs \<in> \<zseq> (\<zseq> X)" and 
    b1: "x \<in> \<zseq> X" and 
    b2: "f \<zbcomp> \<zcat>/[X] xs = \<zcat>/[Y] ((\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<zbcomp> xs)"

  have b3: "f \<zbcomp> x = \<zcat>/[Y] ((\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<zbcomp> \<lang>x\<rang>)"  
  proof -
    have c0: "((\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<zbcomp> \<lang>x\<rang>) = \<lang>f \<zbcomp> x\<rang>"
      apply (subst Z_sunit_rel_bcomp)
      apply (rule b1)
      apply (mauto(fspace))
      apply (simp add: Domain_Collect_Zsplit rel_bcomp_def glambda_def eind_def Z_dom_def)
      apply (simp add: glambda_def)
      apply (subst functional_beta [of _ _ "f \<zbcomp> x"])
      apply (simp_all add: b1)
      apply (insert a2)
      apply (mauto(fspace))
      apply (auto intro!: functionalI elim!: functionalE)
      done
    show ?thesis
      apply (simp add: c0)  
      apply (subst sdistrib_sunit [THEN sym])
      apply (rule seq_rel_comp_seq)
      apply (rule b1)
      apply (rule a2)
      apply (simp add: sdistrib_concat_def)     
      done  
  qed

  have b4: "(\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<in> \<zseq> X \<ztfun> \<zseq> Y"
  proof -
    have 
      c0: "\<zdom> (\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) = \<zseq> X" 
      by (simp add: glambda_dom)
    have
      c1: "\<zran> (\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<subseteq> \<zseq> Y"
      apply (auto simp add: glambda_ran)
      apply (rule seq_rel_comp_seq [OF _ a2])
      apply assumption
      done

    from c0 c1 show 
      "(\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<in> \<zseq> X \<ztfun> \<zseq> Y"
      by (mauto(fspace))
  qed


  have b5: "(\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<zbcomp> \<lang>x\<rang> \<in> \<zseq> (\<zseq> Y)"
    by (rule seq_rel_comp_seq [OF sunit_seq [OF b1] b4])

  have b6: "(\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<zbcomp> xs \<in> \<zseq> (\<zseq> Y)"
    by (rule seq_rel_comp_seq [OF b0 b4])

  show 
    "f \<zbcomp> \<zcat>/[X] (sinsert x xs)  
    = \<zcat>/[Y] ((\<glambda> s | s \<in> \<zseq> X \<bullet> f \<zbcomp> s) \<zbcomp> sinsert x xs)"
    apply (simp add: sdistrib_sinsert [OF b0 b1])
    apply (simp add: Z_sconcat_rel_bcomp [OF b1 sdistrib_closed [OF b0] a2])
    apply (simp add: b2)
    apply (simp add: sinsert_sconcat [OF b0 b1])
    apply (subst Z_sconcat_rel_bcomp [where ?X = "\<zseq> X"])
    apply (rule sunit_seq [OF b1])
    apply (rule b0)
    apply (mauto(fspace))
    apply (simp add: glambda_dom)
    apply (simp add: b3)
    apply (subst sdistrib_sconcat [THEN sym])
    apply (simp_all add: b5 b6)
    done
qed

lemma sinsert_seq_seq:
  assumes 
    a1: "xs \<in> \<zseq> (\<zseq> X)" and 
    a2: "x \<in> \<zseq> X" and 
    a3: "i \<in> (1..(\<zcard>xs + 1))"
  shows 
    "(sinsert x xs)\<cdot>i \<in> \<zseq> X"
  apply (rule seq_in_ran)
  apply (rule sinsert_closed [OF a1 a2])
  apply (insert a3)
  apply (simp add: sinsert_dom [OF a1 a2])
done


lemma sdistrib_ran1:
  assumes a1: "q \<in> \<zseq> (\<zseq> X)"
  shows "\<zran> (\<zcat>/[X] q) = \<Union> { i | i \<in> (1..\<zcard>q) \<bullet> \<zran> (q\<cdot>i)}"
proof (rule seq_induct [OF a1])
  show "\<zran> (\<zcat>/[X] \<sempty>) = \<Union> { i | i \<in> (1..\<zcard>\<sempty>) \<bullet> \<zran>(\<sempty>\<cdot>i)}"
    apply (simp add: sdistrib_sempty Z_sempty_ran)
    apply auto
  done
next
  apply_end (subst sinsert_sconcat [THEN sym], simp, simp)
  apply_end (subst sinsert_sconcat [THEN sym], simp, simp)
  apply_end (subst sinsert_sconcat [THEN sym], simp, simp)
  fix xs x
  assume b0: "xs \<in> \<zseq> (\<zseq> X)" and b1: "x \<in> \<zseq> X"
  and b2: "\<zran> (\<zcat>/[X] xs) = \<Union> { i | i \<in> (1..\<zcard>xs) \<bullet> \<zran> (xs\<cdot>i)}"

  have 
    b3: "\<zran> x \<union> {y | \<exists> i | 1 \<le> i \<bullet> i \<in> zInts \<and> i \<le> \<zcard>xs \<and> y \<in> \<zran> (xs\<cdot>i)} 
        = {y | \<exists> i | 1 \<le> i \<bullet>  i \<in> zInts \<and> i \<le> (\<zcard>xs + 1) \<and> y \<in> \<zran> ((sinsert x xs)\<cdot>i)}"
  proof -
    let ?A = "\<zran> x"
    let ?B = "{y | \<exists> i | 1 \<le> i \<bullet> i \<in> zInts \<and> i \<le> \<zcard>xs \<and> y \<in> \<zran> (xs\<cdot>i)}"
    let ?C = "{y | \<exists> i | 1 \<le> i \<bullet> i \<in> zInts \<and> i \<le> (\<zcard>xs + 1) \<and> y \<in> \<zran> ((sinsert x xs)\<cdot>i)}"
    show ?thesis
    proof (rule set_eqI, (msafe(inference)))
      fix xa
      assume c0: "xa \<in> ?A \<union> ?B"
      have c1: "xa \<in> ?A \<Rightarrow> xa \<in> ?C"
      proof auto
        fix r
        assume d0: "(r, xa) \<in> x"
        show "\<exists> i | 1 \<le> i \<bullet> i \<in> zInts \<and> i \<le> (\<zcard>xs + 1) \<and> xa \<in> \<zran> ((sinsert x xs)\<cdot>i)"
          apply (witness "1::\<arithmos>")
          apply (simp add: sinsert_beta_first [OF b0 b1])
          apply (simp add: Range_iff Domain_Collect_Zsplit dsub_def zNats_le0 [OF zNats_zcard])
          apply (witness "r", simp add: d0)
        done
      qed

      have c2: "xa \<in> ?B \<Rightarrow> xa \<in> ?C"
      proof auto
        fix i a
        assume d0: "1 \<le> i" and d1: "i \<le> \<zcard>xs" and d2: "(a, xa) \<in> xs\<cdot>i" and d00: "i \<in> zInts"
        show "\<exists> i | 1 \<le> i \<bullet> i \<in> zInts \<and> i \<le> (\<zcard>xs + 1) \<and> xa \<in> \<zran> ((sinsert x xs)\<cdot>i)"
          apply (witness "i + 1")
          apply (simp add: d1)
          apply (subst sinsert_beta [OF b0 b1])
          apply (insert d0 d1)
          apply (simp add: Range_iff Domain_Collect_Zsplit dsub_def)
          apply (intro conjI zInts_add d00, simp)
          apply (witness "a", simp add: d2)
        done
      qed
      from c0 c1 c2 show "xa \<in> ?C" by auto
    next
      fix q
      assume c0: "q \<in> ?C"
      from c0 obtain i where 
        c1: "1 \<le> i" and 
        c2: "i \<le> (\<zcard>xs + 1)" and 
        c3: "q \<in> \<zran> ((sinsert x xs)\<cdot>i)" and 
        c00: "i \<in> \<int>" by (auto)
      have c4: "i = 1 \<Rightarrow> q \<in> ?A"
      proof (msafe_no_assms(inference))
        assume d0: "i = 1"
        from c3 show "q \<in> ?A"
          by (simp add: d0 sinsert_beta_first [OF b0 b1])
      qed
      have c5: "i \<noteq> 1 \<Rightarrow> q \<in> ?B"
      proof auto
        assume "i \<noteq> 1" with c1 have c1': "1 < i" by auto
        then have "(sinsert x xs)\<cdot>i = (sinsert x xs)\<cdot>((i - 1) + 1)"
        by auto
        also have 
        "... = xs\<cdot>(i - 1)"
          apply (rule sinsert_beta_back [OF b0 b1])
          apply (insert c1', simp)
        done
        finally have d0: "(sinsert x xs)\<cdot>i = xs\<cdot>(i - 1)" .

        have "(0::\<arithmos>) \<le> zcard xs" by (rule zNats_le0 [OF zNats_zcard])
        
        then show "\<exists> i | 1 \<le> i \<bullet>  i \<in> zInts \<and> i \<le> \<zcard>xs \<and> q \<in> \<zran> (xs\<cdot>i)"
          apply (witness "i - 1")
          apply (insert c1' c2)
          apply (intro conjI)
          apply (subst zInts_le_diff1_eq, simp_all add: ge_def c00)
          apply (insert c3, simp add: d0 [THEN sym] Range_iff Domain_Collect_Zsplit dsub_def)
        done
      qed
      from c4 c5 show "q \<in> ?A \<union> ?B" by auto
    qed
  qed
  from this [THEN sym] have b3: "\<zran> x \<union> {y |  (\<exists> i \<bullet> i \<in> zInts \<and> 1 \<le> i \<and> i \<le> \<zcard>xs \<and> y \<in> \<zran> (xs\<cdot>i))} = {y | \<exists> i | 1 \<le> i \<bullet> i \<in> zInts \<and> i \<le> (\<zcard>xs + 1) \<and> y \<in> \<zran> ((sinsert x xs)\<cdot>i)}"
  by (mauto(wind))

  show 
    "\<zran> (\<zcat>/[X] (sinsert x xs)) 
    = \<Union> { i | i \<in> (1 ..\<zcard>(sinsert x xs)) \<bullet> \<zran> ((sinsert x xs)\<cdot>i)}"
    apply (simp add: sdistrib_sinsert [OF b0 b1])
    apply (subst Z_sconcat_ran_union) 
    apply (rule b1)
    apply (rule sdistrib_closed [OF b0])
    apply (simp add: b2)
    apply (simp add: sinsert_zcard [OF b0 b1])
    apply (simp add: Union_eq)
    apply (simp add: b3)
    apply ((mauto(wind)))
  done
qed

lemma sdistrib_ran2:
  assumes a1: "q \<in> \<zseq> (\<zseq> X)"
  shows "\<zran> (\<zcat>/[X] q) = \<Union> (\<zran> ((\<graphof> Range) \<zbcomp> q))"
proof (rule seq_induct [OF a1])
  show "\<zran> (\<zcat>/[X] \<sempty>) = \<Union> (\<zran> ((\<graphof> Range) \<zbcomp> \<sempty>))"
    apply (simp add: sdistrib_sempty)
    apply (simp add: sempty_def Range_iff Domain_Collect_Zsplit dsub_def graph_of_def rel_bcomp_def)
    done
next
  apply_end (subst sinsert_sconcat [THEN sym], simp, simp)
  apply_end (subst sinsert_sconcat [THEN sym], simp, simp)
  fix xs x
  assume 
    b0: "xs \<in> \<zseq> (\<zseq> X)" and 
    b1: "x \<in> \<zseq> X" and 
    b2: "\<zran> (\<zcat>/[X] xs) = \<Union> (\<zran> ((\<graphof> Range) \<zbcomp> xs))"
 
  show "\<zran> (\<zcat>/[X] (sinsert x xs)) = \<Union> (\<zran> ((\<graphof> Range) \<zbcomp> (sinsert x xs)))"
    apply (simp add: sdistrib_sinsert [OF b0 b1])
    apply (simp add: Z_sconcat_ran_union [OF b1 sdistrib_closed [OF b0]])
    apply (simp add: b2)
    apply (simp add: Union_eq graph_of_def rel_bcomp_def glambda_mem conj_ac ran_eind)
  proof -
    let ?A = "\<zran> x"
    let ?B = "{ z | \<exists> a b \<bullet> z \<in> \<zran> b \<and> (a, b) \<in> xs }"
    let ?C = "{ z | \<exists> a b \<bullet> z \<in> \<zran> b \<and> (a, b) \<in> sinsert x xs }"
    show "?A \<union> ?B = ?C"
    proof (rule set_eqI, (msafe(inference)))
      fix z
      assume c0: "z \<in> ?A \<union> ?B"
      have c1: "z \<in> ?A \<Rightarrow> z \<in> ?C"
      proof auto
        fix a
        assume d0: "(a, z) \<in> x"
        show "\<exists> a b \<bullet> z \<in> \<zran> b \<and> (a, b) \<in> sinsert x xs"
          apply (witness "1-[\<arithmos>]")
          apply (witness "x")
          apply (rule conjI)
          using d0
          apply (auto simp add: sinsert_appl_first [OF b0 b1])
          done
      qed
      have c2: "z \<in> ?B \<Rightarrow> z \<in> ?C"
      proof auto
        fix xb y r
        assume d0: "(xb, y) \<in> xs" and d1: "(r, z) \<in> y"

        from d0 have "xb \<in> \<zdom> xs" by auto
        with seq_dom [OF b0] have d2: "xb \<in> (1..\<zcard>xs)" by auto

        from seq_beta [OF b0 d0] have d0': "xs\<cdot>xb = y" by this

        from d2 have d3: "(xb + 1, xs\<cdot>xb) \<in> sinsert x xs"
          apply (intro sinsert_appl [OF b0 b1])
          apply simp_all
          done
        have d4: "\<zran> y = \<zran> (xs\<cdot>xb)" by (simp add: d0')
      
        from d1 have d5: "z \<in> \<zran> y"
          by (auto simp add: Range_iff Domain_Collect_Zsplit dsub_def)
        from d3 d4 d5 show 
          "\<exists> a b \<bullet> z \<in> \<zran> b \<and> (a, b) \<in> sinsert x xs"
          apply (witness "xb + 1")
          apply (witness "xs\<cdot>xb")
          apply (intro conjI)
          apply simp_all
          done
      qed
      from c0 c1 c2 show "z \<in> ?C" by auto
    next
      fix r
      assume c0: "r \<in> ?C"
      from c0 obtain k xa y where c1: "(xa, y) \<in> sinsert x xs" and c2: "k = \<zran> y" and c3: "r \<in> k" by auto
      from c2 c3 have c3': "r \<in> \<zran> y" by auto
      have "r \<in> ?C \<Rightarrow> r \<in> ?A \<or> r \<in> ?B"
      proof (msafe(inference))
        have d0: "xa = 1 \<Rightarrow> r \<in> ?A"
        proof (msafe_no_assms(inference))
          assume e0: "xa = 1"
          from sinsert_beta [OF b0 b1] e0 have "(sinsert x xs)\<cdot>xa = x" by auto
          with seq_beta [OF sinsert_closed [OF b0 b1] c1] have "x = y" by auto
          with c2 c3 show "r \<in> ?A"
            by (simp add: Range_iff Domain_Collect_Zsplit dsub_def)
        qed
        have d1: "xa \<noteq> 1 \<Rightarrow> r \<in> ?B"
        proof (msafe_no_assms(inference))
          assume e0: "xa \<noteq> 1"
          from sinsert_beta [OF b0 b1] e0 have "(sinsert x xs)\<cdot>xa = xs\<cdot>(xa - 1)" by auto
          with seq_beta [OF sinsert_closed [OF b0 b1] c1] have c4: "xs\<cdot>(xa - 1) = y" by auto
          from c1 seq_dom [OF sinsert_closed [OF b0 b1]] have 
            c5: "xa \<in> \<int>" and c6: "xa \<in> (1..\<zcard>(sinsert x xs))" 
            by auto
          show "r \<in> ?B"
            apply simp
            apply (witness "xa - 1")
            apply (witness "y")
            apply (intro conjI)
            apply (simp add: c3')
            apply (simp add: c4 [THEN sym])
            apply (rule seq_appl [OF b0])
            apply (insert c5 c6 e0)
            apply (simp_all add: sinsert_zcard [OF b0 b1])
            done
        qed
        show "r \<in> ?A \<or> r \<in> ?B"
          apply (cases "xa = 1")
          apply (intro disjI1)
          apply (intro d0 [rule_format], simp_all)
          apply (intro disjI2)
          apply (insert d1 [rule_format], simp)
          done
      qed
      with c0 show "r \<in> ?A \<union> ?B" by auto
    qed
  qed
qed   

lemma Z_sdistrib_ran:
  assumes a0: "q \<in> \<zseq> (\<zseq> X)"
  shows "\<lch> \<zran> (\<zcat>/[X] q) 
          \<chEq> \<Union> { i | i \<in> (1..\<zcard>q) \<bullet> \<zran> (q\<cdot>i)} 
          \<chEq> \<Union> (\<zran> ((\<graphof> Range) \<zbcomp> q)) \<rch>"
proof -
  from sdistrib_ran1 [OF a0] have 
    "\<zran> (\<zcat>/[X] q) = \<Union> { i | i \<in> (1..\<zcard>q) \<bullet> \<zran> (q\<cdot>i)}" by simp
  moreover
  with sdistrib_ran2 [OF a0] have 
    "\<Union> { i | i \<in> (1..\<zcard>q) \<bullet> \<zran> (q\<cdot>i)} = \<Union> (\<zran> ((\<graphof> Range) \<zbcomp> q))" by auto
  ultimately show ?thesis
    by (simp)
qed

end 
