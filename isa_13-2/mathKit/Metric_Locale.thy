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
 
theory Metric_Locale 

imports
  Z_Toolkit
begin

text {*

This theory introduces metric space, shows instantiation for different 
types and defines limits and continuity for functions in metric 
spaces.  We develop a set-based approach.

A metric space has a distance function between its elements.
Note that by building this on carrier we assume that the space is not empty.
This is a change, so have to be sure that don't run into trouble!

*}

locale metric_sig = carrier X 
  for X :: "'a set" +
  fixes
    distance :: "['a, 'a] \<rightarrow> \<real>" ("\<^mdist>{:_:}{:_:}")
   
locale metric_space = metric_sig +
  assumes
    nonneg: "\<And> x y \<bullet> \<lbrakk> x \<in> X; y \<in> X \<rbrakk> \<turnstile> 0 \<le> \<^mdist>{:x:}{:y:}" and
    strict: "\<And> x y \<bullet> \<lbrakk> x \<in> X; y \<in> X \<rbrakk> \<turnstile> \<^mdist>{:x:}{:y:} = 0 \<Leftrightarrow> x = y" and
    symmetric: "\<And> x y \<bullet> \<lbrakk> x \<in> X; y \<in> X \<rbrakk> \<turnstile> \<^mdist>{:x:}{:y:} = \<^mdist>{:y:}{:x:}" and
    subadd: "\<And> x y z \<bullet>\<lbrakk>  x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<turnstile> \<^mdist>{:x:}{:z:} \<le> \<^mdist>{:x:}{:y:} + \<^mdist>{:y:}{:z:}"
begin

  lemma zero_dist: 
  "\<And> x \<bullet> x \<in> X \<turnstile> \<^mdist>{:x:}{:x:} = 0"
  by (auto simp add: strict)


  lemma diff_triangle:
  "\<And> x y z \<bullet> \<lbrakk> x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<turnstile> abs (\<^mdist>{:x:}{:z:} - \<^mdist>{:y:}{:z:}) \<le> \<^mdist>{:x:}{:y:}"
  proof-
    fix x y z :: 'a
    assume inX:  "x \<in> X" "y \<in> X" "z \<in> X"
    from inX have
    "\<^mdist>{:x:}{:z:} \<le> \<^mdist>{:x:}{:y:} + \<^mdist>{:y:}{:z:}"
    by (intro subadd, auto)
    then have R1:
    "\<^mdist>{:x:}{:z:} - \<^mdist>{:y:}{:z:} \<le> \<^mdist>{:x:}{:y:}"
    by (auto)
    from inX have
    "\<^mdist>{:z:}{:y:} \<le> \<^mdist>{:z:}{:x:} + \<^mdist>{:x:}{:y:}"
    by (intro subadd, auto)
    then have
    "- \<^mdist>{:x:}{:y:} \<le> \<^mdist>{:z:}{:x:} - \<^mdist>{:z:}{:y:}"
    by (auto)
    with inX have R2:
    "- \<^mdist>{:x:}{:y:} \<le> \<^mdist>{:x:}{:z:} - \<^mdist>{:y:}{:z:}"
    by (auto simp add: symmetric)
    from R1 R2 show
    "abs (\<^mdist>{:x:}{:z:} - \<^mdist>{:y:}{:z:}) \<le> \<^mdist>{:x:}{:y:}"
    by (auto simp add: abs_le_interval_iff)
  qed
  
end

lemmas metric_space_def' = metric_space_def metric_space_axioms_def metric_sig_def carrier_def'   

notation (zed)
  metric_space ("\<^metricspace>{:_:}{:_:}")

end
