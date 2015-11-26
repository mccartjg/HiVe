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

theory xCalculus

imports
  Calculus 
  xReal_Type
  xReal_Type_nonassoc

begin


text{*

\section{Extended limits}

*}






consts
  xLIMSEQ :: "[\<nat>\<rightarrow>\<real>,\<xrealna>] \<rightarrow> \<bool>"  

notation (xsymbols output)        
  xLIMSEQ ("(_)/ \<midarrow>x\<longrightarrow> (_)" [60, 60] 60) 

notation (zed)        
  xLIMSEQ ("\<^xLIMSEQ>{:_:}{:_:}") 

defs
  xLIMSEQ_def:
    "\<^xLIMSEQ>{:X:}{:xL:} \<defs>
    \<case> xL \<of>
      -\<zinftyna> \<longrightarrow> (\<forall> BS_Delta | 0 < BS_Delta \<bullet> (\<exists> N \<bullet> (\<forall> n | N \<le> n \<bullet> (X n) < - BS_Delta)))
    | fin_na L \<longrightarrow> \<^LIMSEQ>{:X:}{:L:}
    | \<zinftyna> \<longrightarrow> (\<forall> BS_Delta | 0 < BS_Delta \<bullet> (\<exists> N \<bullet> (\<forall> n | N \<le> n \<bullet> BS_Delta < (X n))))
    \<esac>"

lemma max1:
  "(a::'a::order) \<le> max a b"
  apply (cases "a \<le> b")
  apply (auto simp add: max_def)
done

lemma max2:
  "(b::'a::linorder) \<le> max a b"
  apply (cases "a \<le> b")
  apply (auto simp add: max_def)
done

lemma convergent_finite:
  fixes L::\<real>
  shows
  "\<^LIMSEQ>{:X:}{:L:} \<turnstile> \<not>(\<forall> BS_Delta | 0 < BS_Delta \<bullet> (\<exists> N \<bullet> (\<forall> n | N \<le> n \<bullet> (X n) < - BS_Delta)))"
  apply (simp add: LIMSEQ_def)
  apply (auto simp add: abs_less_iff dist_real_def)
  apply (cases "0<L", simp_all add: linorder_not_less)
  apply (elim allE [where ?x = "L+1"])
  apply simp
  apply (witness "1::\<real>", auto)
proof-
  fix N_d_0 N
  assume Aa1: "\<forall> n \<bullet>  N_d_0 \<le> n \<Rightarrow> (X n < 2 * L + 1 \<and> -1 < X n)"
  then show
  "\<exists> n \<bullet> N \<le> n \<and> -1 \<le> X n"
    apply (witness "max N_d_0 N")
    apply (elim allE [where ?x = "max N_d_0 N"])
    apply (auto simp add: max1 max2)
  done
next
  apply_end (elim allE [where ?x = "1"], auto)
  apply_end (witness "-L+1", auto)
  fix N_d_0 N
  assume Aa1: "\<forall> n \<bullet>  N_d_0 \<le> n \<Rightarrow> ( X n - L < 1 \<and> L - X n < 1)"
  then show
  "\<exists> n \<bullet> N \<le> n \<and> L + -1 \<le> X n"
    apply (witness "max N_d_0 N")
    apply (elim allE [where ?x = "max N_d_0 N"])
    apply (auto simp add: max1 max2)
  done
qed

lemma convergent_finite':
  fixes L::\<real>
  shows
  "\<^LIMSEQ>{:X:}{:L:} \<turnstile> \<not>(\<forall> BS_Delta | 0 < BS_Delta \<bullet> (\<exists> N \<bullet> (\<forall> n | N \<le> n \<bullet> BS_Delta < (X n))))"
  apply (simp add: LIMSEQ_def dist_real_def)
  apply (auto simp add: abs_less_iff)
  apply (cases "0<L")
  apply (elim allE [where ?x = "1"], auto simp add: linorder_not_less)
  apply (witness "L+1", auto)
proof-
  fix N_d_0 N
  assume Aa1: "\<forall> n \<bullet>  N_d_0 \<le> n \<Rightarrow> (X n - L < 1 \<and> L - X n < 1)"
  then show
  "\<exists> n \<bullet> N \<le> n \<and> X n \<le> L + 1"
    apply (witness "max N_d_0 N")
    apply (elim allE [where ?x = "max N_d_0 N"])
    apply (auto simp add: max1 max2)
  done
next
  apply_end (elim allE [where ?x = "-L+1"], auto)
  apply_end (witness "1::\<real>", auto)
  fix N_d_0 N
  assume Aa1: "\<forall> n \<bullet>  N_d_0 \<le> n \<Rightarrow> (X n < 1 \<and> 2*L + - X n < 1)"
  then show
  "\<exists> n \<bullet> N \<le> n \<and> X n \<le> 1"
    apply (witness "max N_d_0 N")
    apply (elim allE [where ?x = "max N_d_0 N"])
    apply (auto simp add: max1 max2)
  done
qed

lemma divergent_different:
  fixes L::\<real>
  shows
  "(\<forall> (BS_Delta::\<real>) | 0 < BS_Delta \<bullet> (\<exists> (N::\<nat>) \<bullet> (\<forall> n | N \<le> n \<bullet> BS_Delta < (X n)))) 
  \<turnstile> \<not>(\<forall> BS_Delta | 0 < BS_Delta \<bullet> (\<exists> N \<bullet> (\<forall> n | N \<le> n \<bullet> (X n) < - BS_Delta)))"
  apply auto
  apply (witness "1::\<real>")
  apply (elim allE [where ?x = "1"], auto simp add: linorder_not_less)
proof-
  fix N N'
  assume Aa1: "\<forall> n \<bullet>  N \<le> n \<Rightarrow> 1 < X n"
  then show
  "\<exists> n \<bullet> N' \<le> n \<and> -1 \<le> X n"
    apply (witness "max N N'")
    apply (elim allE [where ?x = "max N N'"])
    apply (auto simp add: max1 max2)
  done
qed

lemma xLIMSEQ_unique:
  "\<lbrakk> \<^xLIMSEQ>{:X:}{:xL:}; \<^xLIMSEQ>{:X:}{:xL':} \<rbrakk> \<turnstile> xL = xL'"
  apply (multi_cases "xL" "xL'")
  apply (simp_all add: xLIMSEQ_def convergent_finite convergent_finite' divergent_different)
  apply (rule LIMSEQ_unique)
  apply simp_all
done


definition
  xlim :: "(\<nat>\<rightarrow>\<real>) \<rightarrow> \<xrealna>" ("\<^xlim>{:_:}")
where
  xlim_def:
    "\<^xlim>{:X:} \<defs> (\<mu> xL | \<^xLIMSEQ>{:X:}{:xL:})"

lemma xlim_ninfty:
  assumes A1: "(\<forall> BS_Delta | 0 < BS_Delta \<bullet> (\<exists> N \<bullet> (\<forall> n | N \<le> n \<bullet> (X n) < - BS_Delta)))"
  shows
  "\<^xlim>{:X:} = -\<zinftyna>"
  apply (unfold xlim_def, rule the_equality)
  apply (insert A1, simp add: xLIMSEQ_def) 
  apply (rule xLIMSEQ_unique, simp) 
  apply (simp add: xLIMSEQ_def) 
done

lemma xlim_fin:
  assumes A1: "\<^LIMSEQ>{:X:}{:L:}"
  shows
  "\<^xlim>{:X:} = \<^finna>{:L:}"
  apply (unfold xlim_def, rule the_equality)
  apply (insert A1, simp add: xLIMSEQ_def) 
  apply (rule xLIMSEQ_unique, simp) 
  apply (simp add: xLIMSEQ_def) 
done

lemma xlim_infty:
  assumes A1: "(\<forall> BS_Delta | 0 < BS_Delta \<bullet> (\<exists> N \<bullet> (\<forall> n | N \<le> n \<bullet> BS_Delta < (X n))))"
  shows
  "\<^xlim>{:X:} = \<zinftyna>"
  apply (unfold xlim_def, rule the_equality)
  apply (insert A1, simp add: xLIMSEQ_def) 
  apply (rule xLIMSEQ_unique, simp) 
  apply (simp add: xLIMSEQ_def) 
done


text{*

\section{Extended summation}

Perhaps a corresponding theory of summation of series is useful.

*}



consts
   xsums  :: "(\<nat> \<rightarrow> \<real>) \<rightarrow> \<xrealna> \<rightarrow> \<bool>"     (infixr "xsumsTo" 80)
defs
  xsums_def:
    "f xsumsTo xS \<defs> \<^xLIMSEQ>{:\<olambda> n \<bullet> setsum f {0..<n}:}{:xS:}"

definition
   xsuminf   :: "(\<nat>\<rightarrow>\<real>) \<rightarrow> \<xrealna>" 
where
    "xsuminf f \<defs> (\<mu> xS | f xsumsTo xS)"

syntax (zed)
  "_xsuminf" :: "idt \<rightarrow> \<real> \<rightarrow> \<xrealna>"    ("\<xSum>_ \<bullet> _" [0, 10] 10)
translations
  "\<xSum>i \<bullet> b" == "CONST xsuminf (\<olambda> i \<bullet> b)"




end
