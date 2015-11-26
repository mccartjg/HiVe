(*<*)
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
  Z_Numbers_Chap
  
imports 
  Z_Fun
  Orders
  Equipotence

begin(*>*)

lemma fin_card_dom:
  assumes
    a1: "finite f" and
    a2: "card (\<zdom> f) = card f"
  shows
    "functional f"
proof -
  from a1 have
    b1: "card (\<zdom> f) = card f \<Rightarrow> functional f" (is "?P f")
  proof (induct f set: finite)
    show
      "?P \<emptyset>"
      by (simp add: empty_functional)
  next
  apply_end (tactic {* split_all_tac @{context} 1 *} )
    fix
      f x y
    assume
      c1: "finite f" and
      c2: "(x \<mapsto> y) \<notin> f" and
      c3: "?P f"
    show
      "?P (insert (x \<mapsto> y) f)"
    proof 
      assume
        d1: "card (\<zdom> (insert (x \<mapsto> y) f)) = card (insert (x \<mapsto> y) f)"
      from c1 c2 have
        d2: "card (insert (x \<mapsto> y) f) = card f + 1"
        by (simp)
      have
        d3: "\<zdom> f \<subseteq> \<fst>\<lparr>f\<rparr>"
        by (auto simp add: image_def)
      from c1 c1 [THEN fun_finite_dom] have
        d4: "card (\<zdom> (insert (x \<mapsto> y) f)) \<le> card (\<zdom> f) + 1"
        by (simp add: insert_dom card_insert_if)
      with c1 c2 have
        "card f \<le> card (\<zdom> f)"
        apply (simp only: d1)
        apply (simp)
        done
      moreover from c1 c1 [THEN fun_finite_dom] subepIsurj [OF d3] have
        "card (\<zdom> f) \<le> card f"
        by (simp add: finite_subequipotent_card)
      ultimately have
        d5: "card (\<zdom> f) = card f"
        by (auto)
      with c1 c2 have
        d6: "card (\<zdom> (insert (x \<mapsto> y) f)) = card (\<zdom> f) + 1"
        apply (simp only: d1)
        apply (auto)
        done 
      from d5 c3 have
        "functional f"
        by (simp)
      then show
        "functional (insert (x \<mapsto> y) f)"
        apply (rule insert_functionalI)
        using d6 c1 [THEN fun_finite_dom]
        apply (simp add: card_insert_if)
        apply (cases "x \<in> \<zdom> f")
        apply (auto)
        done
    qed
  qed
  with a2 show
    "?thesis"
    by (simp)
qed

chapter {* The Z Mathkit: Numbers *}

(*<*)end(*>*)
