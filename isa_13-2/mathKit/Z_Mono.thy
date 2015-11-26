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

header {* The Z Mathkit: Order-morphic set operations *}

theory 
  Z_Mono

imports 
  Lattice_FixPoint
  Lattice_Instance

begin

lemma mono_set_def:
  "f \<in> \<mh> \<Leftrightarrow> (\<forall> S T \<bullet> S \<subseteq> T \<Rightarrow> f S \<subseteq> f T)"
  by (simp add: monotonic_ops_def mono_def)
  
definition
  rev_args :: "(['a, 'b] \<rightarrow> 'c) \<rightarrow> (['b, 'a] \<rightarrow> 'c)"
where
  rev_args_def: "rev_args \<defs> (\<olambda> f b a \<bullet> f a b)"

lemma mono2_prod_def:
  "(f::('a::order) \<rightarrow> ('b::order) \<rightarrow> ('c::order)) \<in> \<mh> \<and> rev_args f \<in> \<mh> 
  \<Leftrightarrow> (\<forall> S T U V \<bullet> S \<le> T \<and> U \<le> V \<Rightarrow> f S U \<le> f T V)"
  apply (msafe(inference))
  defer 1
  apply (simp add: monotonic_ops_def rev_args_def mono_def le_fun_def)
  apply (simp add: monotonic_ops_def rev_args_def mono_def le_fun_def)
proof -
  assume a1: "f \<in> \<mh>" and a2 [simplified rev_args_def]: "rev_args f \<in> \<mh>"
  fix S::'a and T::'a and U::'b and V::'b
  assume b1: "S \<le> T" and b2: "U \<le> V"
  from mhD [OF a1, OF b1] have "f S U \<le> f T U"
    by (simp add: le_fun_def)
  also from mhD [OF a2, OF b2] have "\<dots> \<le> f T V"
    by (simp add: le_fun_def)
  finally show "f S U \<le> f T V"
    by (this)
qed

lemma mono2_prod_set_def:
  "f \<in> \<mh> \<and> rev_args f \<in> \<mh> \<Leftrightarrow> (\<forall> S T U V \<bullet> S \<subseteq> T \<and> U \<subseteq> V \<Rightarrow> f S U \<subseteq> f T V)"
  by (simp add: mono2_prod_def)

lemma mono_set_sup:
  "f \<in> \<mh> \<Leftrightarrow> (\<forall> S T \<bullet> f S \<union> f T \<subseteq> f (S \<union> T))"
proof (msafe(inference))
  assume b1: "f \<in> \<mh>"
  fix S T
  have b2: "f S \<subseteq> f (S \<union> T)"
    apply (rule mhD [OF b1])
    apply (auto)
    done
  have b3: "f T \<subseteq> f (S \<union> T)"
    apply (rule mhD [OF b1])
    apply (auto)
    done
  from b2 b3 show "f S \<union> f T \<subseteq> f (S \<union> T)"
    by (auto)
next
  assume b1: "(\<forall> S T \<bullet> f S \<union> f T \<subseteq> f (S \<union> T))"
  show "f \<in> \<mh>"
  proof (rule mhI)
    fix S::"'a set" and T::"'a set"
    assume c1: "S \<subseteq> T"
    have "f S \<subseteq> f S \<union> f T"
      by (auto)
    also from b1 have "f S \<union> f T \<subseteq> f (S \<union> T)"
      by (auto)
    also from c1 have "S \<union> T = T"
      by (auto)
    finally show "f S \<subseteq> f T"
      by (this)   
  qed
qed

lemma mono_set_inf:
  "f \<in> \<mh> \<Leftrightarrow> (\<forall> S T \<bullet> f (S \<inter> T) \<subseteq> f S \<inter> f T)"
proof (msafe(inference))
  assume b1: "f \<in> \<mh>"
  fix S T
  have b2: "f (S \<inter> T) \<subseteq> f S"
    apply (rule mhD [OF b1])
    apply (auto)
    done
  have b3: "f (S \<inter> T) \<subseteq> f T"
    apply (rule mhD [OF b1])
    apply (auto)
    done
  from b2 b3 show "f (S \<inter> T) \<subseteq> f S \<inter> f T"
    by (auto)
next
  assume b1: "(\<forall> S T \<bullet> f (S \<inter> T) \<subseteq> f S \<inter> f T)"
  show "f \<in> \<mh>"
  proof (rule mhI)
    fix S::"'a set" and T::"'a set"
    assume c1: "S \<subseteq> T"
    from c1 have "S = S \<inter> T"
      by (auto)
    then have "f S = f (S \<inter> T)"
      by (auto)
    also from b1 have "f (S \<inter> T) \<subseteq> f S \<inter> f T"
      by (auto)
    also have "f S \<inter> f T \<subseteq> f T"
      by (auto)
    finally show "f S \<subseteq> f T"
      by (this)   
  qed
qed

lemma inf_morphic_set_def:
  "f \<in> \<mhi> \<Leftrightarrow> (\<forall> S T \<bullet> f (S \<inter> T) = f S \<inter> f T)"
  by (simp add: inf_morphic_def inf_set_def)

lemma sup_morphic_set_def:
  "f \<in> \<mhs> \<Leftrightarrow> (\<forall> S T \<bullet> f (S \<union> T) = f S \<union> f T)"
  by (simp add: sup_morphic_def sup_set_def)

lemma sup_morphic2_def:
  "f \<in> \<mhs> \<and> rev_args f \<in> \<mhs> 
  \<Leftrightarrow> (\<forall> S T U V \<bullet> 
       f (S \<lsup> T) V  = f S V \<lsup> f T V \<and> 
       f S (U \<lsup> V) = f S U \<lsup> f S V)"
  by (auto simp add: sup_morphic_def lsup_fun_def rev_args_def fun_eq_def)

lemma sup_morphic2_set_def:
  "f \<in> \<mhs> \<and> rev_args f \<in> \<mhs> 
  \<Leftrightarrow> (\<forall> S T U V \<bullet> f (S \<union> T) V  = f S V \<union> f T V \<and> f S (U \<union> V) = f S U \<union> f S V)"
  by (simp add: sup_morphic2_def sup_set_def)

lemma lfp_set_def:
  assumes 
    a1: "f \<in> \<mh>" "S = llfp f"
  shows 
    "S = (\<Inter> T | f T \<subseteq> T)"
  using a1
  by (simp add: lfp_char Inf_set_def eind_def)

lemma lfp_set_fold:
  assumes 
    a1: "f \<in> \<mh>" "(S::'a set) = llfp f"
  shows 
    "f S = S"
  using a1
  by (simp add: lfp_fold)

lemma lfp_set_induct:
  assumes 
    a1: "f \<in> \<mh>" "(S::'a set) = llfp f"
  shows 
    "(\<forall> T | f T \<subseteq> T \<bullet> S \<subseteq> T)"
  apply (msafe(inference))
  apply (simp add: a1)
  apply (rule lfp_induct)
  using a1
  apply (auto)
  done

end
