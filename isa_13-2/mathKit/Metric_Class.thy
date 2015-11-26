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

theory Metric_Class
 
imports 
  Metric_Locale

begin

text {*
This theory introduces the metric space class.
%We include instance results here -- largely because it is a small theory but also because the fact that the reals is a metri%c space is a natural result to show continuity of the distance function.
%It might be that later this should be rationalised into the Metric_Topology theory, but it might also be nice to keep some clean results separately.


A metric space has a distance function between its elements.

*}

class dist =
  fixes
    distance :: "['a, 'a] \<rightarrow> \<real>"

notation (xsymbols output)
  distance ("\<rho>'(_, _')")

notation (zed)
  distance ("\<^mcdist>{:_:}{:_:}") 

class metric = dist +
assumes
  class_nonneg: "0 \<le> \<^mcdist>{:x:}{:y:}" and
  class_refl: "\<^mcdist>{:x:}{:y:} = 0 \<Leftrightarrow> x = y"  and 
  class_sym: "\<^mcdist>{:x:}{:y:} = \<^mcdist>{:y:}{:x:}" and
  class_subadd: "\<^mcdist>{:x:}{:z:} \<le> \<^mcdist>{:x:}{:y:} + \<^mcdist>{:y:}{:z:}"
begin

  lemma class_zero_dist: 
  shows "\<^mcdist>{:x:}{:x:} = 0"
  by (auto simp add: class_refl)


  lemma metric_class_diff_triangle:
  "abs (\<^mcdist>{:x:}{:z:} - \<^mcdist>{:y:}{:z:})\<le> \<^mcdist>{:x:}{:y:}"
  proof-
    have
    "\<^mcdist>{:x:}{:z:} \<le> \<^mcdist>{:x:}{:y:} + \<^mcdist>{:y:}{:z:}"
    by (rule class_subadd)
    then have R1:
    "\<^mcdist>{:x:}{:z:} - \<^mcdist>{:y:}{:z:} \<le> \<^mcdist>{:x:}{:y:}"
    by auto
    have
    "\<^mcdist>{:z:}{:y:} \<le> \<^mcdist>{:z:}{:x:} + \<^mcdist>{:x:}{:y:}"
    by (rule class_subadd)
    then have
    "- \<^mcdist>{:x:}{:y:} \<le> \<^mcdist>{:z:}{:x:} - \<^mcdist>{:z:}{:y:}"
    by auto
    then have R2:
    "- \<^mcdist>{:x:}{:y:} \<le> \<^mcdist>{:x:}{:z:} - \<^mcdist>{:y:}{:z:}"
    by (auto simp add: class_sym)
    from R1 R2 show
      ?thesis
    by (auto simp add: abs_if)
  qed
  
end

lemmas metric_class_defs = class_nonneg class_refl class_sym class_subadd class_zero_dist
  
theorem metric_classI:
  assumes 
    a1: "\<^metricspace>{:\<univ>-[('a::dist)]:}{:distance:}"
  shows 
  "OFCLASS('a::dist, metric_class)"
  apply (intro_classes)
  apply (auto intro!: 
         metric_space.nonneg [OF a1]
         metric_space.strict [OF a1]
         metric_space.symmetric [OF a1]
         metric_space.subadd [OF a1])
done

lemma metric_classD:
  "\<^metricspace>{:\<univ>-[('a::metric)]:}{:distance:}"
  apply (unfold_locales)
  apply simp
  apply (intro metric_class_defs)+
done


end






















