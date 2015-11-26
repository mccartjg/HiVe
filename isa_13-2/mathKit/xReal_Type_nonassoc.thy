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

theory xReal_Type_nonassoc 

imports
  Z_Toolkit
  Metric_Class

begin

text {*

We develop the extended reals without unfortunate elaborations.

The extended reals add @{text "\<plusminus>\<zinftyna>"}, being at the
respective extremities of the real order.

*}

datatype
  xreal_na = ninfty_na | fin_na real ("\<^finna>{:_:}") | infty_na

type_notation (xsymbols output)
  xreal_na ("\<real>\<^sub>\<infinity>\<^isup>N")

type_notation (zed)
  xreal_na ("\<xrealna>")

notation (xsymbols output)
  ninfty_na ("-\<infinity>\<^isup>N") and
  infty_na ("\<infinity>\<^isup>N")

notation (zed)
  ninfty_na ("-\<zinftyna>") and
  infty_na ("\<zinftyna>")

text {*

The zero of the extended reals is the finite zero.

*}

instantiation xreal_na  :: "{zero,one}"
begin

  definition
    xreal_na_zero_def:  "0 \<defs> \<^finna>{:0:}" 

  definition
    xreal_na_one_def:  "1 \<defs> \<^finna>{:1:}"

  instance
  by (intro_classes)

end


text {*

Addition is extended to the extremities.  The group properties of the reals
cannot be preserved in the extended reals so we simply leave the sum of the
bottom and top elements undetermined.  Note that in xreal_na\_Type we force that
the result must be in the boundary set -- with this choice we have a semigroup
structure under addition; i.e., the addition is associative.  If the result
were finite then , e.g., $\infty_na + (-\infty_na + x) = \infty_na + -\infty_na \neq
(\infty_na + -\infty_na) + x$. 

Here we don't make this additional assumption.

*}

text {*

Multiplication is also extended in the obvious way, with @{text "0 *
\<zinftyna>"} set to @{text 0} by convention.  Royden states that this is a
convention, I'm not precisely sure what the term means here.  Then multiplying
anything by $0$ leaves $0$.  Again, alternatives will give us problems with
associativity.  If the result were $\infty_na * 0 = a$, then $(\infty_na * 0) * x =
\infty_na * (0 * x)$ implies that $a * x = a$.  

Again, here we simply leave this undefined.

*}

text {*

The interesting case for inverse is of course @{text 0}, where the result is
left completely undetermined.  

*}


instantiation  
  xreal_na :: "{plus,uminus,minus,times,inverse}"  
begin

  definition
    xreal_na_add_def: "x + y \<defs> 
    \<case> x \<of>
      -\<zinftyna> \<longrightarrow> (\<case> y \<of> -\<zinftyna> \<longrightarrow>
-\<zinftyna> | \<^finna>{:b:} \<longrightarrow> -\<zinftyna> | \<zinftyna> \<longrightarrow> \<arb> \<esac>)
    | \<^finna>{:a:} \<longrightarrow> (\<case> y \<of> -\<zinftyna> \<longrightarrow> -\<zinftyna> | \<^finna>{:b:} \<longrightarrow> \<^finna>{:(a+b):} | \<zinftyna> \<longrightarrow> \<zinftyna> \<esac>)
    | \<zinftyna> \<longrightarrow> (\<case> y \<of> -\<zinftyna> \<longrightarrow> \<arb> | \<^finna>{:b:} \<longrightarrow> \<zinftyna> | \<zinftyna> \<longrightarrow> \<zinftyna> \<esac>)
    \<esac>"

  definition
    xreal_na_mult_def: "x * y \<defs> 
    \<case> x \<of>
      -\<zinftyna> \<longrightarrow> 
        \<case> y \<of> 
          -\<zinftyna> \<longrightarrow> \<zinftyna> 
        | \<^finna>{:b:} \<longrightarrow> 
            \<if> b < 0 \<then> \<zinftyna> 
            \<else> \<if> b = 0 \<then> 0 \<else> -\<zinftyna> \<fi>
            \<fi>
        | \<zinftyna> \<longrightarrow> -\<zinftyna> 
        \<esac>
    | \<^finna>{:a:} \<longrightarrow> 
        \<case> y \<of> 
          -\<zinftyna> \<longrightarrow>  
            \<if> a < 0 \<then> \<zinftyna> 
            \<else> \<if> a = 0 \<then> 0 \<else> -\<zinftyna> \<fi>
            \<fi> 
        | \<^finna>{:b:} \<longrightarrow> \<^finna>{:(a*b):} 
        | \<zinftyna> \<longrightarrow>  
            \<if> a < 0 \<then> -\<zinftyna> 
            \<else> \<if> a = 0 \<then> 0 \<else> \<zinftyna> \<fi>
            \<fi>
        \<esac>
    | \<zinftyna> \<longrightarrow> 
        \<case> y \<of> 
          -\<zinftyna> \<longrightarrow> -\<zinftyna> 
        | \<^finna>{:b:} \<longrightarrow>  
            \<if> b < 0 \<then> -\<zinftyna> 
            \<else> \<if> b = 0 \<then> 0 \<else> \<zinftyna> \<fi>
            \<fi>
        | \<zinftyna> \<longrightarrow> \<zinftyna> 
        \<esac>
    \<esac>"

  definition
    xreal_na_uminus_def: "- x \<defs>
    \<case> x \<of>
      -\<zinftyna> \<longrightarrow> \<zinftyna>
    | \<^finna>{:a:} \<longrightarrow> \<^finna>{:(- a):}
    | \<zinftyna> \<longrightarrow> -\<zinftyna>
    \<esac>"

  definition
    xreal_na_diff_def: "x - (y::xreal_na) \<defs> x + (- y)"


  lemma uminus_idem [simp]: "-(-(x::xreal_na)) = x"
  by (cases x, auto simp add: xreal_na_uminus_def)

  definition
    xreal_na_inverse_def: "inverse x \<defs>
    \<case> x \<of>
      -\<zinftyna> \<longrightarrow> 0
    | \<^finna>{:a:} \<longrightarrow> \<if> a = 0 \<then> \<arb> \<else> \<^finna>{:(inverse a):} \<fi>
    | \<zinftyna> \<longrightarrow> 0
    \<esac>"

  definition
  xreal_na_divide_def: "x / (y::xreal_na) \<defs> x * (inverse y)"

  instance
  by intro_classes

end

(*
text {

We activate binary number representations for the extended reals.

}

(* B: numeral class requires additive associativity ! 
 * Possibly could overload numeral to act onxreal_na, but would have no simplification properties.
 * Might be possible to use an injection from integers to xreal_na and a syntactic sugar for
 * of_int (numeral n)?
 *)


instance xreal_na :: numeral ..

lemma 
  "(8::xreal) + 0 = 8"
  "(8::xreal) + 1 = 9"
  "(8::xreal) + 4 = 12"
  "(8::xreal) + 11 = 19"
  by (auto)


instantiation 
  xreal_na :: number
begin

  definition
    xreal_na_number_of_def [simp]:
    "number_of x \<defs> \<^finna>{:(number_of x):}"

  instance 
   by (intro_classes)

end
*)
 
lemmas xreal_na_reduce_0 = 
  xreal_na_zero_def xreal_na_one_def 
  xreal_na_add_def 
  xreal_na_mult_def 
  xreal_na_uminus_def xreal_na_diff_def 
  xreal_na_inverse_def xreal_na_divide_def


lemma xreal_na_All:
  "(\<forall> (x::\<xrealna>) \<bullet> P x) = ((P -\<zinftyna>) \<and> (\<forall> r \<bullet> P \<^finna>{:r:}) \<and> (P \<zinftyna>))"
proof auto
  fix x :: \<xrealna>
  assume 
    b1: "(P -\<zinftyna>)" "(\<forall> r \<bullet> P \<^finna>{:r:})" "(P \<zinftyna>)"
  then show "P x" 
    apply (cases x)
    apply (auto)
    done
qed

lemma xreal_na_Ex:
  "(\<exists> (x::\<xrealna>) \<bullet> P x) = ((P -\<zinftyna>) \<or> (\<exists> r \<bullet> P \<^finna>{:r:}) \<or> (P \<zinftyna>))"
  apply (auto)
  apply (rule contrapos_pp)
  apply (assumption)
  apply (thin_tac "?P", simp)
proof -
  fix x :: \<xrealna> and r :: \<real>
  assume 
    "\<not> (P -\<zinftyna>)" "(\<forall> r \<bullet> \<not> (P \<^finna>{:r:}))" "\<not> (P \<zinftyna>)"
  then show "\<not> (P x)" by (cases x, auto)
qed


text{*

\subsection{Algebraic structure}

*}


instantiation xreal_na :: semigroup_mult
begin

  instance
    apply intro_classes
    apply (simp add: atomize_all xreal_na_All, (msafe_no_assms(inference)))
    apply (simp_all add: xreal_na_reduce_0 mult_neg_neg
                         linorder_not_less order_le_less
                         mult_pos_neg mult_pos_neg2 mult_pos_pos)
  done

end

instantiation xreal_na :: ab_semigroup_mult
begin

  instance
  proof intro_classes
    fix a b :: \<xrealna>
    show
    "a * b = b * a"
      apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
      apply (simp_all add: xreal_na_reduce_0)
    done
  qed

end

instantiation xreal_na :: comm_monoid_mult
begin

  instance
  proof intro_classes
    fix a :: \<xrealna>
    show
    "1 * a = a"
      apply (cases "a")
      apply (simp_all add: xreal_na_reduce_0 disj_commute)
    done
  qed

end

text{*
There is no great reason to look for the algebraic structure since we haven't
even an associative addition.  Still, at least it's abelian!
*}

lemma xreal_na_add_ab: 
"(a::\<xrealna>) + b = b + a"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce_0)
done

text{*
I'll just list the rest which don't immediately fail.
*}

lemma xreal_na_add_imp_eq'1:
  "\<^finna>{:x:} + b = \<^finna>{:x:} + c \<turnstile> b = c"
  apply (multi_cases "b" "c")
  apply (auto simp add: xreal_na_reduce_0 disj_commute)
done

lemma xreal_na_add_imp_eq'2:
  "-\<^finna>{:x:} + b = -\<^finna>{:x:} + c \<turnstile> b = c"
  apply (multi_cases "b" "c")
  apply (auto simp add: xreal_na_reduce_0 disj_commute)
done

lemma xreal_na_add_imp_eq:
  "a + b = a + c \<turnstile> a = \<zinftyna> \<or> a = -\<zinftyna> \<or> b = c"
  apply (multi_cases "a" "b" "c")
  apply (auto simp add: xreal_na_reduce_0 disj_commute)
done

lemma xreal_na_add_left_cancel1 [simp]:
     "(\<^finna>{:x:} + b = \<^finna>{:x:} + c) = (b = c)"
by (blast dest: xreal_na_add_imp_eq'1) 

lemma xreal_na_add_left_cancel2 [simp]:
     "(-\<^finna>{:x:} + b = -\<^finna>{:x:} + c) = (b = c)"
by (blast dest: xreal_na_add_imp_eq'2) 

lemma xreal_na_add_right_cancel1 [simp]:
     "(b + \<^finna>{:x:} = c + \<^finna>{:x:}) = (b = c)"
by (simp add: xreal_na_add_ab [where ?b = "\<^finna>{:x:}"])

lemma xreal_na_add_right_cancel2 [simp]:
     "(b + -\<^finna>{:x:} = c + -\<^finna>{:x:}) = (b = c)"
by (simp add: xreal_na_add_ab [where ?b = "-\<^finna>{:x:}"])

(*
Also, xreal_na is not an abelian group under addition since the inverse fails on infinity.
*)

lemma xreal_na_left_minus [simp]:
  "- \<^finna>{:x:} + \<^finna>{:x:} = 0"
by (simp add: xreal_na_reduce_0 disj_commute)

lemma xreal_na_right_minus [simp]:
  "\<^finna>{:x:} + - \<^finna>{:x:} = 0"
by (simp add: xreal_na_reduce_0 disj_commute)

lemma xreal_na_diff_minus:
  "(a::\<xrealna>) - b = a + (-b)"
by (simp add: xreal_na_reduce_0 disj_commute)

lemma xreal_na_minus_minus [simp]:
  "- (- (a::\<xrealna>)) = a"
  apply (cases "a")
  apply (simp add: xreal_na_reduce_0 disj_commute)+
done

lemma xreal_na_minus_zero [simp]: "- 0 = (0::\<xrealna>)"
by (simp add: xreal_na_reduce_0 disj_commute)

lemma xreal_na_diff_self1 [simp]: "\<^finna>{:x:} - \<^finna>{:x:} = 0"
by (simp add: xreal_na_reduce_0 disj_commute)

lemma xreal_na_diff_self2 [simp]: "-\<^finna>{:x:} + \<^finna>{:x:} = 0"
by (simp add: xreal_na_reduce_0 disj_commute)

lemma xreal_na_diff_0 [simp]: "(0::\<xrealna>) - a = -a"
  apply (case_tac "a")
  apply (auto simp add: xreal_na_reduce_0)
done

lemma xreal_na_diff_0_right [simp]: "a - (0::\<xrealna>) = a" 
  apply (case_tac "a")
  apply (auto simp add: xreal_na_reduce_0)
done

lemma xreal_na_diff_minus_eq_add [simp]: "a - - b = a + (b::\<xrealna>)"
by (simp add: xreal_na_diff_minus)

lemma xreal_na_neg_equal_iff_equal [simp]: "(-a = -b) = (a = (b::\<xrealna>))" 
proof 
  assume "- a = - b"
  hence "- (- a) = - (- b)"
    by simp
  thus "a=b" by simp
next
  assume "a=b"
  thus "-a = -b" by simp
qed

lemma xreal_na_neg_equal_0_iff_equal [simp]: "(-a = 0) = (a = (0::\<xrealna>))"
  apply (cases "a")
  apply (simp add: xreal_na_reduce_0 disj_commute)+
done

lemma xreal_na_neg_0_equal_iff_equal [simp]: "(0 = -a) = (0 = (a::\<xrealna>))"
  apply (cases "a")
  apply (simp add: xreal_na_reduce_0 disj_commute)+
done

lemma xreal_na_minus_add_distrib1 [simp]: "- (\<^finna>{:x:} + b) = -\<^finna>{:x:} + -b"
  apply (cases "b")
  apply (simp add: xreal_na_reduce_0 disj_commute)+
done

lemma xreal_na_minus_add_distrib2 [simp]: "- (a + \<^finna>{:y:}) = -a + -\<^finna>{:y:}"
  apply (cases "a")
  apply (simp add: xreal_na_reduce_0 disj_commute)+
done

lemma xreal_na_minus_add_distrib3 [simp]: "- (-\<^finna>{:x:} + b) = \<^finna>{:x:} + -b"
  apply (cases "b")
  apply (simp add: xreal_na_reduce_0 disj_commute)+
done

lemma xreal_na_minus_add_distrib4 [simp]: "- (a + -\<^finna>{:y:}) = -a + \<^finna>{:y:}"
  apply (cases "a")
  apply (simp add: xreal_na_reduce_0 disj_commute)+
done

lemma xreal_na_minus_diff_eq1 [simp]: "- (\<^finna>{:x:} - b) = b - \<^finna>{:x:}"
  apply (cases "b")
  apply (simp add: xreal_na_reduce_0 disj_commute)+
done

lemma xreal_na_minus_diff_eq2 [simp]: "- (a - \<^finna>{:y:}) = \<^finna>{:y:} - a"
  apply (cases "a")
  apply (simp add: xreal_na_reduce_0 disj_commute)+
done

lemma xreal_na_minus_diff_eq3 [simp]: "- (-\<^finna>{:x:} - b) = b + \<^finna>{:x:}"
  apply (cases "b")
  apply (simp add: xreal_na_reduce_0 disj_commute)+
done

lemma xreal_na_diff_eq_eq: "(a-\<^finna>{:x:} = c) = (a = c + \<^finna>{:x:})"
  apply (multi_cases "a" "c")
  apply (auto simp add: xreal_na_reduce_0 disj_commute)
done

lemma xreal_na_eq_diff_eq: "(a = c-\<^finna>{:x:}) = (a + \<^finna>{:x:} = c)"
  apply (multi_cases "a" "c")
  apply (auto simp add: xreal_na_reduce_0 disj_commute)
done

lemma xreal_na_diff_diff_eq1a: "(a - \<^finna>{:x:}) - c = a - (\<^finna>{:x:} + c)"
  apply (multi_cases "a" "c")
  apply (auto simp add: xreal_na_reduce_0 disj_commute)
done

lemma xreal_na_diff_diff_eq2b: "a - (b - \<^finna>{:x:}) = (a + \<^finna>{:x:}) - b"
  apply (multi_cases "a" "b")
  apply (auto simp add: xreal_na_reduce_0 disj_commute)
done

lemma xreal_na_diff_add_cancel: "a - \<^finna>{:x:} + \<^finna>{:x:} = (a::\<xrealna>)"
  apply (multi_cases "a")
  apply (auto simp add: xreal_na_reduce_0 disj_commute)
done

lemma xreal_na_add_diff_cancel: "a + \<^finna>{:x:} - \<^finna>{:x:} = (a::\<xrealna>)"
  apply (multi_cases "a")
  apply (auto simp add: xreal_na_reduce_0 disj_commute)
done

lemmas xreal_na_compare_rls_0 = 
  xreal_na_diff_eq_eq
  xreal_na_eq_diff_eq
  xreal_na_diff_diff_eq1a
  xreal_na_diff_diff_eq2b

lemmas xreal_na_group_eq_simps =
  mult_ac
  xreal_na_diff_eq_eq
  xreal_na_eq_diff_eq
  xreal_na_diff_diff_eq1a
  xreal_na_diff_diff_eq2b

lemma xreal_na_eq_iff_diff_eq_0_1: "(a = \<^finna>{:x:}) = (a-\<^finna>{:x:} = 0)"
  apply (multi_cases "a")
  apply (auto simp add: xreal_na_reduce_0 disj_commute)
done

lemma xreal_na_eq_iff_diff_eq_0_2: "(\<^finna>{:x:} = a) = (\<^finna>{:x:} - a = 0)"
  apply (cases "a")
  apply (simp_all add: xreal_na_reduce_0)
done

lemmas xreal_na_diff_eq_0_iff_eq =
  xreal_na_eq_iff_diff_eq_0_1 [symmetric]
  xreal_na_eq_iff_diff_eq_0_2 [symmetric]

declare xreal_na_diff_eq_0_iff_eq [simp]

text{*

Of course, $\isasymxreal_na$ is not a field: but we can still salvage a fair bit
of the simp rules.
*}


instantiation xreal_na :: zero_neq_one
begin

  instance
    apply intro_classes
    apply (simp add: xreal_na_reduce_0)
  done

end

instantiation xreal_na :: no_zero_divisors
begin

  instance
  proof intro_classes
    fix a b :: \<xrealna>
    assume "a \<noteq> 0" and "b \<noteq> 0"
    then show
    "(a * b) \<noteq> 0"
      apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
      apply (auto simp add: xreal_na_reduce_0)
    done
  qed

end

text{*

The semigroup structure is broken by the $\infty_na - \infty_na$ problem.

*}

lemma xreal_na_left_distrib1:
  "(\<^finna>{:x:} + b) * \<^finna>{:y:} = \<^finna>{:x:} * \<^finna>{:y:} + b * \<^finna>{:y:}"
  apply (cases "b")
  apply (auto simp add: xreal_na_reduce_0 distrib)
done

lemma xreal_na_left_distrib2:
  "(b + \<^finna>{:x:}) * \<^finna>{:y:} = \<^finna>{:x:} * \<^finna>{:y:} + b * \<^finna>{:y:}"
  apply (cases "b")
  apply (auto simp add: xreal_na_reduce_0 distrib)
done

lemma xreal_na_left_distrib3:
  "(\<^finna>{:x:} + \<^finna>{:y:}) * \<zinftyna> = \<^finna>{:x + y:} * \<zinftyna>"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_left_distrib4:
  "(\<^finna>{:x:} + \<^finna>{:y:}) * -\<zinftyna> = - \<^finna>{:x + y:} * \<zinftyna>"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_distrib_left1:
  "\<^finna>{:y:} * (\<^finna>{:x:} + b)  = \<^finna>{:y:} * \<^finna>{:x:} + \<^finna>{:y:} * b"
  apply (cases "b")
  apply (auto simp add: xreal_na_reduce_0 ring_distribs)
done

lemma xreal_na_distrib_left2:
  "\<^finna>{:y:} * (b + \<^finna>{:x:}) = \<^finna>{:y:} * \<^finna>{:x:} + \<^finna>{:y:} * b"
  apply (cases "b")
  apply (auto simp add: xreal_na_reduce_0 ring_distribs)
done

lemma xreal_na_distrib_left3:
  "\<zinftyna> * (\<^finna>{:x:} + \<^finna>{:y:}) = \<zinftyna> * \<^finna>{:x + y:}"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_distrib_left4:
  "-\<zinftyna> * (\<^finna>{:x:} + \<^finna>{:y:}) = -\<zinftyna> * \<^finna>{:x + y:}"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_left_diff_distrib1:
  "(\<^finna>{:x:} - b) * \<^finna>{:y:} = \<^finna>{:x:} * \<^finna>{:y:} - b * \<^finna>{:y:}"
  apply (cases "b")
  apply (auto simp add: xreal_na_reduce_0 distrib)
done

lemma xreal_na_left_diff_distrib2:
  "(b - \<^finna>{:x:}) * \<^finna>{:y:} = b * \<^finna>{:y:} - \<^finna>{:x:} * \<^finna>{:y:}"
  apply (cases "b")
  apply (auto simp add: xreal_na_reduce_0 distrib)
done

lemma xreal_na_left_diff_distrib3:
  "(\<^finna>{:x:} - \<^finna>{:y:}) * \<zinftyna> = \<^finna>{:x - y:} * \<zinftyna>"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_left_diff_distrib4:
  "(\<^finna>{:x:} - \<^finna>{:y:}) * -\<zinftyna> = - \<^finna>{:x - y:} * \<zinftyna>"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_right_diff_distrib1:
  "\<^finna>{:y:} * (\<^finna>{:x:} - b) = \<^finna>{:y:} * \<^finna>{:x:} - \<^finna>{:y:} * b"
  apply (cases "b")
  apply (auto simp add: xreal_na_reduce_0 ring_distribs)
done

lemma xreal_na_right_diff_distrib2:
  "\<^finna>{:y:} * (b - \<^finna>{:x:}) = \<^finna>{:y:} * b - \<^finna>{:y:} * \<^finna>{:x:}"
  apply (cases "b")
  apply (auto simp add: xreal_na_reduce_0 ring_distribs)
done

lemma xreal_na_right_diff_distrib3:
  "\<zinftyna> * (\<^finna>{:x:} - \<^finna>{:y:}) = \<zinftyna> * \<^finna>{:x - y:}"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_right_diff_distrib4:
  "-\<zinftyna> * (\<^finna>{:x:} - \<^finna>{:y:}) = -\<zinftyna> * \<^finna>{:x - y:}"
by (auto simp add: xreal_na_reduce_0)

lemmas xreal_na_ring_eq_simps = xreal_na_group_eq_simps
  xreal_na_left_distrib1
  xreal_na_left_distrib2
  xreal_na_left_distrib3
  xreal_na_left_distrib4
  xreal_na_distrib_left1
  xreal_na_distrib_left2
  xreal_na_distrib_left3
  xreal_na_distrib_left4
  xreal_na_left_diff_distrib1
  xreal_na_left_diff_distrib2
  xreal_na_left_diff_distrib3
  xreal_na_left_diff_distrib4 
  xreal_na_right_diff_distrib1
  xreal_na_right_diff_distrib2
  xreal_na_right_diff_distrib3
  xreal_na_right_diff_distrib4 


lemma xreal_na_left_inverse1 [simp]:
  "x \<noteq> 0 ==> inverse \<^finna>{:x:} * \<^finna>{:x:} = 1"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_left_inverse2 [simp]:
  "inverse 0 * 0 = (0::\<xrealna>)"
  apply (simp add: xreal_na_inverse_def xreal_na_zero_def)
  apply (cases "\<arb>::\<xrealna>")
  apply (simp add: xreal_na_reduce_0) defer
  apply (simp add: xreal_na_reduce_0)
proof-
  fix r :: \<real>
  assume Aa1: "(\<arb>::\<xrealna>) = \<^finna>{:r:}"
  show
  "\<arb>*\<^finna>{:0:} = \<^finna>{:0:}"
    apply (subst Aa1)
    apply (simp add: xreal_na_reduce_0)
  done
qed

lemma xreal_na_left_inverse3 [simp]:
  "inverse \<zinftyna> * \<zinftyna> = (0::\<xrealna>)"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_left_inverse4 [simp]:
  "inverse (-\<zinftyna>) * (-\<zinftyna>) = (0::\<xrealna>)"
by (auto simp add: xreal_na_reduce_0)


lemma xreal_na_right_inverse1 [simp]:
  "x \<noteq> 0 ==> \<^finna>{:x:} * inverse \<^finna>{:x:} = 1"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_right_inverse2 [simp]:
  "0 * inverse 0 = (0::\<xrealna>)"
  apply (simp add: xreal_na_inverse_def xreal_na_zero_def)
  apply (cases "(\<arb>::\<xrealna>)")
  apply (simp add: xreal_na_reduce_0) defer
  apply (simp add: xreal_na_reduce_0)
proof-
  fix r :: \<real>
  assume Aa1: "(\<arb>::\<xrealna>) = \<^finna>{:r:}"
  show
  "\<^finna>{:0:}*\<arb> = \<^finna>{:0:}"
    apply (subst Aa1)
    apply (simp add: xreal_na_reduce_0)
  done
qed

lemma xreal_na_right_inverse3 [simp]:
  "\<zinftyna> * inverse \<zinftyna> = (0::\<xrealna>)"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_right_inverse4 [simp]:
  "(-\<zinftyna>) * inverse (-\<zinftyna>) = (0::\<xrealna>)"
by (auto simp add: xreal_na_reduce_0)

lemma xreal_na_mult_zero_left [simp]:
  "0 * a = (0::\<xrealna>)"
  apply (cases "a")
  apply (simp add: xreal_na_reduce_0)+
done

lemma xreal_na_mult_zero_right [simp]:
  "a * 0 = (0::\<xrealna>)"
  apply (cases "a")
  apply (simp add: xreal_na_reduce_0)+
done

lemma xreal_na_field_mult_eq_0_iff [simp]:
  "(a*b = (0::\<xrealna>)) = (a = 0 \<or> b = 0)"
  apply (multi_cases "a" "b")
  apply (simp add: xreal_na_reduce_0)+
done


lemma xreal_na_minus_mult_minus [simp]:
  "(- a) * (- b) = a * (b::\<xrealna>)"
  apply (multi_cases "a" "b")
  apply (simp add: xreal_na_reduce_0)+
done

text{*

\subsection{Arithmetic of infinities}

These should be gathered up into an axclass.

*}

lemma xreal_na_infinity_add1 [simp]:
  "\<zinftyna> + \<^finna>{:x:} = \<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_infinity_add2 [simp]:
  "\<zinftyna> + \<zinftyna> = \<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_ninfinity_add1 [simp]:
  "-\<zinftyna> + \<^finna>{:x:} = -\<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_ninfinity_add2 [simp]:
  "-\<zinftyna> + -\<zinftyna> = -\<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_infinity_diff1 [simp]:
  "\<zinftyna> - \<^finna>{:x:} = \<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_infinity_diff2 [simp]:
  "\<^finna>{:x:} - \<zinftyna> = -\<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_ninfinity_diff1 [simp]:
  "-\<zinftyna> - \<^finna>{:x:} = -\<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_ninfinity_diff2 [simp]:
  "-\<zinftyna> - \<zinftyna> = -\<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_infinity_mult1 [simp]:
  "\<zinftyna> * \<^finna>{:x:} = \<if> 0 < x \<then> \<zinftyna> \<else> \<if> x < 0 \<then> - \<zinftyna> \<else> 0 \<fi> \<fi>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_infinity_mult2 [simp]:
  "\<zinftyna> * -\<zinftyna> = -\<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_infinity_mult3 [simp]:
  "\<zinftyna> * \<zinftyna> = \<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_ninfinity_mult1 [simp]:
  "-\<zinftyna> * \<^finna>{:x:} = \<if> 0 < x \<then> -\<zinftyna> \<else> \<if> x < 0 \<then> \<zinftyna> \<else> 0 \<fi> \<fi>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_ninfinity_mult2 [simp]:
  "-\<zinftyna> * -\<zinftyna> = \<zinftyna>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_infinity_divide1 [simp]:
  "\<zinftyna> / \<^finna>{:x:} = \<if> 0 < x \<then> \<zinftyna> \<else> \<if> x < 0 \<then> - \<zinftyna> \<else> \<zinftyna> * \<arb> \<fi> \<fi>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_infinity_divide2 [simp]:
  "a / \<zinftyna> = 0"
  apply (cases "a")
  apply (simp_all add: xreal_na_reduce_0)
done

lemma xreal_na_ninfinity_divide1 [simp]:
  "-\<zinftyna> / \<^finna>{:x:} = \<if> 0 < x \<then> -\<zinftyna> \<else> \<if> x < 0 \<then> \<zinftyna> \<else> -\<zinftyna> * \<arb> \<fi> \<fi>"
by (simp add: xreal_na_reduce_0)

lemma xreal_na_ninfinity_divide2 [simp]:
  "a / -\<zinftyna> = 0"
  apply (cases "a")
  apply (simp_all add: xreal_na_reduce_0)
done

lemma xreal_na_zero_divide [simp]:
  "(0::\<xrealna>) / a = 0"
  apply (cases "a")
  apply (simp_all add: xreal_na_divide_def)
done

text{*

Several of these may be superseded by the following simp rules.  
The simp set should be adjusted if these become problematic.

*}

lemma xreal_na_finite_arithmetic_reduce [simp]:
  "\<^finna>{:x:} + \<^finna>{:y:} = \<^finna>{:x + y:}"
  "\<^finna>{:x:} - \<^finna>{:y:} = \<^finna>{:x - y:}"
  "\<^finna>{:x:} * \<^finna>{:y:} = \<^finna>{:x * y:}"
  "\<^finna>{:x:} / \<^finna>{:y:} = \<^finna>{:x:} * inverse \<^finna>{:y:}"
  "inverse \<^finna>{:y:} = \<if> y \<noteq> 0 \<then> \<^finna>{:inverse y:} \<else> \<arb> \<fi>"
  "\<^finna>{:0:} + a = a"
  "a + \<^finna>{:0:} = a"
  "\<^finna>{:0:} * a = \<^finna>{:0:}"
  "a * \<^finna>{:0:} = \<^finna>{:0:}"
  "\<^finna>{:0:}/a = \<^finna>{:0:}"
  "\<^finna>{:1:} * a = a"
  "a * \<^finna>{:1:} = a"
  apply (simp add: xreal_na_reduce_0)+
  apply (cases "a",
         simp add: xreal_na_reduce_0,simp add: xreal_na_reduce_0,simp add: xreal_na_reduce_0)+
  apply (cases "a",
         simp add: xreal_na_reduce_0, simp add: xreal_na_divide_def) defer
  apply (simp add: xreal_na_reduce_0)
  apply (cases "a",
         simp add: xreal_na_reduce_0,simp add: xreal_na_reduce_0,simp add: xreal_na_reduce_0)+
proof-
  fix r :: \<real>
  show
  "\<^finna>{:0:} * inverse \<^finna>{:r:} = \<^finna>{:0:}"
  by (cases "inverse \<^finna>{:r:}", 
      simp_all add: xreal_na_mult_def xreal_na_zero_def)
qed

(*
Note that arithmetic of the inifinities themselves is already included in xreal_na\_Type.thy.  Maybe
rationalise these.
*)

lemma xreal_na_infinite_arithmetic [simp]:
  "\<^finna>{:x:} + \<zinftyna> = \<zinftyna>"
  "\<^finna>{:x:} + -\<zinftyna> = -\<zinftyna>"
  "\<^finna>{:x:} - \<zinftyna> = -\<zinftyna>"
  "\<^finna>{:x:} - -\<zinftyna> = \<zinftyna>"
  "\<^finna>{:x:} * \<zinftyna> = \<if> 0 < x \<then> \<zinftyna> \<else> \<if> x < 0 \<then> -\<zinftyna> \<else> 0 \<fi> \<fi>"
  "\<^finna>{:x:} * -\<zinftyna> = \<if> 0 < x \<then> -\<zinftyna> \<else> \<if> x < 0 \<then> \<zinftyna> \<else> 0 \<fi> \<fi>"
  "\<zinftyna> + \<^finna>{:x:} = \<zinftyna>"
  "-\<zinftyna> + \<^finna>{:x:} = -\<zinftyna>"
  "\<zinftyna> - \<^finna>{:x:} = \<zinftyna>"
  "-\<zinftyna> - \<^finna>{:x:} = -\<zinftyna>"
  "\<zinftyna> * \<^finna>{:x:} = \<if> 0 < x \<then> \<zinftyna> \<else> \<if> x < 0 \<then> -\<zinftyna> \<else> 0 \<fi> \<fi>"
  "-\<zinftyna> * \<^finna>{:x:} = \<if> 0 < x \<then> -\<zinftyna> \<else> \<if> x < 0 \<then> \<zinftyna> \<else> 0 \<fi> \<fi>"

  "\<zinftyna> + \<zinftyna>  = \<zinftyna>"
  "-\<zinftyna> + -\<zinftyna>  = -\<zinftyna>"
  "inverse \<zinftyna> = 0"
  "inverse -\<zinftyna> = 0"
  apply (auto simp add: xreal_na_reduce_0)
done


text{*
Finally, the following may be more useful in its removal!  (I.e., as ninfty_na\_reduce [THEN sym]!
*}

lemma ninfty_na_reduce:
  "-\<zinftyna> = - \<zinftyna>"
by (simp add: xreal_na_reduce_0)

text{*

\section{Embedding in the extended reals}

*}

consts
   (* overloaded constant for injecting other types into "xreal_na" *)
   xreal_na :: "'a => \<xrealna>" ("\<^xrealna>{:_:}")



instantiation  xreal_na :: order
begin

  definition
    le_xreal_na_def: "x \<le> y \<defs>
    \<case> x \<of>
      -\<zinftyna> \<longrightarrow> 
        \<case> y \<of> 
          -\<zinftyna> \<longrightarrow> \<True> 
        | fin_na b \<longrightarrow> \<True>
        | \<zinftyna> \<longrightarrow> \<True>
        \<esac>
    | fin_na a \<longrightarrow> 
        \<case> y \<of> 
          -\<zinftyna> \<longrightarrow> \<False>
        | fin_na b \<longrightarrow> a \<le> b 
        | \<zinftyna> \<longrightarrow> \<True>
        \<esac>
    | \<zinftyna> \<longrightarrow> 
        \<case> y \<of> 
          -\<zinftyna> \<longrightarrow> \<False>
        | fin_na b \<longrightarrow> \<False>
        | \<zinftyna> \<longrightarrow> \<True>
        \<esac>
    \<esac>"

  definition
  lt_xreal_na_def: "x < (y::xreal_na) \<defs> x \<le> y \<and> x \<noteq> y"

  instance 
  proof (intro_classes) -- reflection
    fix x::xreal_na
    show "x \<le> x" by (cases x, auto simp add: le_xreal_na_def)
  next -- transitivity
    fix x::xreal_na and y::xreal_na and z::xreal_na
    assume a1: "x \<le> y" and a2: "y \<le> z"
    from a1 a2 show "x \<le> z"
    by (multi_cases x y z, auto simp add: le_xreal_na_def)
  next -- asymmetry 
    fix x::xreal_na and y::xreal_na
    assume a1: "x \<le> y" and a2: "y \<le> x"
    from a1 a2 show "x = y"
    by (multi_cases x y, auto simp add: le_xreal_na_def)
  next -- "lt irreflexive"
    fix x::xreal_na and y::xreal_na
    show "(x < y)  = (x \<le> y \<and> \<not> (y \<le> x))" 
    by (multi_cases "x" "y",auto simp add: lt_xreal_na_def le_xreal_na_def)
  qed
  
end


lemmas xreal_na_reduce = xreal_na_reduce_0
  le_xreal_na_def
  lt_xreal_na_def


text {*

Unary negation is an order reflection.

*}

lemma uminus_amono: "(-x \<le> -y) = (y \<le> (x::xreal_na))"
proof (cases x)
  assume a1: "x = -\<zinftyna>"
  show ?thesis by (cases y, insert a1, auto simp add: le_xreal_na_def xreal_na_uminus_def)
next
  fix a assume a1: "x = fin_na a"
  show ?thesis by (cases y, insert a1, auto simp add: le_xreal_na_def xreal_na_uminus_def)
next
  assume a1: "x = \<zinftyna>"
  show ?thesis by (cases y, insert a1, auto simp add: le_xreal_na_def xreal_na_uminus_def)
qed


text {* The embedding of reals is an order embedding.  *}


lemma fin_na_order_embed:
  "r \<le> r' \<Leftrightarrow> \<^finna>{:r:} \<le> \<^finna>{:r':}"
by (simp add: xreal_na_reduce)


text {*

The extended reals are a linear order.

*}

instantiation xreal_na :: linorder
begin

  instance
  proof (intro_classes)
    fix x::xreal_na and y::xreal_na
    show "x \<le> y \<or> y \<le> x"
    proof (cases x)
      assume b1: "x = -\<zinftyna>"
      show "x \<le> y \<or> y \<le> x"
      by (cases y, auto simp add: le_xreal_na_def b1)
    next
      fix a assume b1: "x = fin_na a"
      show "x \<le> y \<or> y \<le> x"      
      by (cases y, auto simp add: le_xreal_na_def b1)
    next
      assume b1: "x = \<zinftyna>"
      show "x \<le> y \<or> y \<le> x"
      by (cases y, auto simp add: le_xreal_na_def b1)
    qed
  qed

end

text{*

\subsection{Algebraic structure}

*}


lemma xreal_na_le_minus_iff: 
"(a \<le> - b) = (b \<le> - (a::\<xrealna>))"
  apply (multi_cases "a" "b")
  apply (auto simp add: xreal_na_reduce)
done

lemma xreal_na_neg_le_iff_le: "- (b::\<xrealna>) \<le> - a \<Leftrightarrow> a \<le> b"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce) 
done


lemma xreal_na_neg_le_0_iff_le [simp]: "- (a::\<xrealna>) \<le> 0 \<Leftrightarrow> 0 \<le> a"
by (subst xreal_na_neg_le_iff_le [symmetric], simp)

lemma xreal_na_neg_0_le_iff_le [simp]: "0 \<le> - (a::\<xrealna>) \<Leftrightarrow> a \<le> 0"
by (subst xreal_na_neg_le_iff_le [symmetric], simp)

lemma xreal_na_neg_less_iff_less [simp]: "- b < - (a::\<xrealna>) \<Leftrightarrow> a < b"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce) 
  apply auto
done

lemma xreal_na_neg_less_0_iff_less [simp]: "- (a::\<xrealna>) < 0 \<Leftrightarrow> 0 < a"
by (subst xreal_na_neg_less_iff_less [symmetric], simp)

lemma xreal_na_neg_0_less_iff_less [simp]: "0 < - (a::\<xrealna>) \<Leftrightarrow> a < 0"
by (subst xreal_na_neg_less_iff_less [symmetric], simp)





(*
Again, the cancel version fails.
*)

lemma xreal_na_add_le_imp_le_left:
  "\<^finna>{:x:} + a \<le> \<^finna>{:x:} + b \<turnstile> a \<le> b"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce)
done

lemma xreal_na_add_le_imp_le_left1:
  "a + b \<le> a + c \<turnstile> a = \<zinftyna> \<or> a = -\<zinftyna> \<or> b \<le> c"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>" "c")
  apply (simp_all add: xreal_na_reduce)
done

lemma xreal_na_add_less_cancel_left [simp]:
    "(\<^finna>{:x:}+a < \<^finna>{:x:}+b) = (a < b)"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce)
done

lemma xreal_na_add_less_cancel_right [simp]:
    "(a+\<^finna>{:x:} < b+\<^finna>{:x:}) = (a < b)"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce)
done

lemma xreal_na_add_le_cancel_left [simp]:
    "(\<^finna>{:x:}+a \<le> \<^finna>{:x:}+b) = (a \<le> b)"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce)
done

lemma xreal_na_add_le_cancel_right [simp]:
    "(a+\<^finna>{:x:} \<le> b+\<^finna>{:x:}) = (a \<le> b)"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce)
done

lemma xreal_na_mult_left_mono:
  "(a::\<xrealna>) \<le> b \<Rightarrow> 0 \<le> c \<Rightarrow> c * a \<le> c * b"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>" "c")
  apply (simp_all add: xreal_na_reduce)
  apply (simp add: xreal_na_reduce disj_commute mult_left_mono)
done

lemma xreal_na_mult_right_mono:
  "(a::\<xrealna>) \<le> b \<Rightarrow> 0 \<le> c \<Rightarrow> a * c \<le> b * c"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>" "c")
  apply (simp_all add: xreal_na_reduce)
  apply (simp add: xreal_na_reduce disj_commute mult_right_mono)
done

lemma xreal_na_mult_pos_pos:
  "\<lbrakk> (0::\<xrealna>) < a; 0 < b \<rbrakk> \<turnstile> 0 < a*b"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce mult_nonneg_nonneg)
done

lemma xreal_na_mult_nonneg_nonneg:
  "\<lbrakk> (0::\<xrealna>) \<le> a; 0 \<le> b \<rbrakk> \<turnstile> 0 \<le> a*b"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce mult_nonneg_nonneg)
done

lemma xreal_na_mult_pos_neg:
  "\<lbrakk> (0::\<xrealna>) < a; b < 0 \<rbrakk> \<turnstile> a*b < 0"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce mult_nonneg_nonpos)
done

lemma xreal_na_mult_nonneg_nonpos:
  "\<lbrakk> (0::\<xrealna>) \<le> a; b \<le> 0 \<rbrakk> \<turnstile> a*b \<le> 0"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce mult_nonneg_nonpos)
done

lemma xreal_na_mult_pos_neg2:
  "\<lbrakk> (0::\<xrealna>) < a; b < 0 \<rbrakk> \<turnstile> b*a < 0" 
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce mult_nonneg_nonpos2)
done

lemma xreal_na_mult_nonneg_nonpos2:
  "\<lbrakk> (0::\<xrealna>) \<le> a; b \<le> 0 \<rbrakk> \<turnstile> b*a \<le> 0" 
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce mult_nonneg_nonpos2)
done

lemma xreal_na_mult_neg_neg:
  "\<lbrakk> a < (0::\<xrealna>); b < 0 \<rbrakk> \<turnstile> 0 < a*b"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce mult_nonpos_nonpos)
done

lemma xreal_na_mult_nonpos_nonpos:
  "\<lbrakk> a \<le> (0::\<xrealna>); b \<le> 0 \<rbrakk> \<turnstile> 0 \<le> a*b"
  apply (multi_cases "a::\<xrealna>" "b::\<xrealna>")
  apply (simp_all add: xreal_na_reduce mult_nonpos_nonpos)
done

lemma xreal_na_zero_less_mult_pos:
  "\<lbrakk> 0 < a*b; 0 < a\<rbrakk> \<turnstile> 0 < (b::\<xrealna>)"
  apply (multi_cases "b \<le> 0")
  apply (auto simp add: order_le_less linorder_not_less)
  apply (drule_tac xreal_na_mult_pos_neg [of a b]) 
  apply (auto dest: order_less_not_sym)
done

lemma xreal_na_zero_less_mult_pos2:
  "\<lbrakk> 0 < b*a; 0 < a\<rbrakk> \<turnstile> 0 < (b::\<xrealna>)"
  apply (cases "b \<le> 0") 
  apply (auto simp add: order_le_less linorder_not_less)
  apply (drule_tac xreal_na_mult_pos_neg2 [of a b]) 
  apply (auto dest: order_less_not_sym)
done

lemma xreal_na_zero_less_mult_iff:
  "((0::\<xrealna>) < a*b) = (0 < a \<and> 0 < b \<or> a < 0 \<and> b < 0)"
  apply (auto simp add: order_le_less linorder_not_less xreal_na_mult_pos_pos 
  xreal_na_mult_neg_neg)
  apply (blast dest: xreal_na_zero_less_mult_pos) 
  apply (blast dest: xreal_na_zero_less_mult_pos2)
done



lemma xreal_na_zero_less_one [simp]:
  "0 < (1::\<xrealna>)"
by (simp add: xreal_na_reduce)


lemma xreal_na_zero_le_one [simp]:
 "(0::\<xrealna>) \<le> 1"
by (simp add: xreal_na_reduce)

lemma xreal_na_not_one_le_zero [simp]:
  "\<not> (1::\<xrealna>) \<le> 0"
by (simp add: xreal_na_reduce)

lemma xreal_na_not_one_less_zero [simp]:
  "\<not> (1::\<xrealna>) < 0"
by (simp add: xreal_na_reduce)

lemma xreal_na_mult_cancel_right [simp]:
  "(a * c = b * c) 
  \<Leftrightarrow> (c = (0::\<xrealna>) \<or> a=b \<or> (c = \<zinftyna> \<and> 0 < a*b) \<or> (c = -\<zinftyna> \<and> 0 < a*b))"
  apply (multi_cases "a" "b" "c")
  apply ((simp add: xreal_na_reduce disj_commute)+ |
         (simp add: mult_cancel_right linorder_not_less linorder_not_le order_le_less
                    mult_pos_pos mult_neg_neg mult_pos_neg mult_pos_neg2))+
done

lemma xreal_na_mult_cancel_left [simp]:
  "(c*a = c*b) \<Leftrightarrow> (c = (0::\<xrealna>) \<or> a=b \<or> (c = \<zinftyna> \<and> 0 < a*b) \<or> (c = -\<zinftyna> \<and> 0 < a*b))"
  apply (multi_cases "a" "b" "c")
  apply ((simp add: xreal_na_reduce disj_commute)+ |
         (simp add: mult_cancel_right linorder_not_less linorder_not_le order_le_less
                    mult_pos_pos mult_neg_neg mult_pos_neg mult_pos_neg2))+
done

lemma xreal_na_mult_cancel_right1 [simp]:
fixes c :: "\<xrealna>"
  shows 
  "(c = b * c) \<Leftrightarrow> (c = 0 \<or> b=1 \<or> c = \<zinftyna> \<and> 0 < b \<or> c = -\<zinftyna> \<and> 0 < b)"
by (insert xreal_na_mult_cancel_right [of 1 c b], force)

lemma xreal_na_mult_cancel_right2 [simp]:
fixes c :: "\<xrealna>"
  shows 
  "(a * c = c) \<Leftrightarrow> (c = 0 \<or> a=1 \<or> c = \<zinftyna> \<and> 0 < a \<or> c = -\<zinftyna> \<and> 0 < a)"
by (insert xreal_na_mult_cancel_right [of a c 1], simp)
 
lemma xreal_na_mult_cancel_left1 [simp]:
fixes c :: "\<xrealna>"
  shows 
  "(c = c*b) \<Leftrightarrow> (c = 0 \<or> b=1 \<or> c = \<zinftyna> \<and> 0 < b \<or> c = -\<zinftyna> \<and> 0 < b)"
by (insert xreal_na_mult_cancel_left [of c 1 b], force)

lemma xreal_na_mult_cancel_left2 [simp]:
fixes c :: "\<xrealna>"
  shows 
  "(c*a = c) = (c = 0 \<or> a=1 \<or> c = \<zinftyna> \<and> 0 < a \<or> c = -\<zinftyna> \<and> 0 < a)"
by (insert xreal_na_mult_cancel_left [of c a 1], simp)

lemmas xreal_na_mult_compare_0 =
  xreal_na_mult_pos_pos
  xreal_na_mult_nonneg_nonneg
  xreal_na_mult_pos_neg
  xreal_na_mult_nonneg_nonpos
  xreal_na_mult_pos_neg2
  xreal_na_mult_nonneg_nonpos2
  xreal_na_mult_neg_neg
  xreal_na_mult_nonpos_nonpos


lemma xreal_na_divide_pos_pos:
  "0 < (x::\<xrealna>) \<turnstile> 0 < y \<turnstile> 0 \<le> x / y"
  apply (multi_cases "x" "y")
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
  apply (msafe_no_assms(inference))
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
done

lemma xreal_na_divide_nonneg_pos:
  "0 \<le> (x::\<xrealna>) \<turnstile> 0 < y \<turnstile> 0 \<le> x / y"
  apply (multi_cases "x" "y")
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
  apply (msafe_no_assms(inference))
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
done

lemma xreal_na_divide_neg_pos:
  "(x::\<xrealna>) < 0 \<turnstile> 0 < y \<turnstile> x / y \<le> 0"
  apply (multi_cases "x" "y")
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
  apply (msafe_no_assms(inference))
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
done

lemma xreal_na_divide_nonpos_pos:
  "(x::\<xrealna>) \<le> 0 \<turnstile> 0 < y \<turnstile> x / y \<le> 0"
  apply (multi_cases "x" "y")
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
  apply (msafe_no_assms(inference))
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
done

lemma xreal_na_divide_pos_neg:
  "0 < (x::\<xrealna>) \<turnstile> y < 0 \<turnstile> x / y \<le> 0"
  apply (multi_cases "x" "y")
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
  apply (msafe_no_assms(inference))
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
done

lemma xreal_na_divide_nonneg_neg:
  "0 \<le> (x::\<xrealna>) \<turnstile> y < 0 \<turnstile> x / y \<le> 0"
  apply (multi_cases "x" "y")
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
  apply (msafe_no_assms(inference))
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
done

lemma xreal_na_divide_neg_neg:
  "(x::\<xrealna>) < 0 \<turnstile> y < 0 \<turnstile> 0 \<le> x / y"
  apply (multi_cases "x" "y")
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
  apply (msafe_no_assms(inference))
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
done

lemma xreal_na_divide_nonpos_neg:
  "(x::\<xrealna>) \<le> 0 \<turnstile> y < 0 \<turnstile> 0 \<le> x / y"
  apply (multi_cases "x" "y")
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
  apply (msafe_no_assms(inference))
  apply (simp_all add: xreal_na_reduce
                       order_le_less
                       mult_neg_neg mult_pos_neg mult_pos_neg2 mult_pos_pos)
done

lemmas xreal_na_divide_compare_0 =
  xreal_na_divide_pos_pos
  xreal_na_divide_nonneg_pos
  xreal_na_divide_neg_pos
  xreal_na_divide_nonpos_pos
  xreal_na_divide_pos_neg
  xreal_na_divide_nonneg_neg
  xreal_na_divide_neg_neg
  xreal_na_divide_nonpos_neg


text{*Further subtraction laws*}

lemma xreal_na_less_iff_diff_less_0:
  "(a < b) = (a \<noteq> b \<and> a - b < (0::\<xrealna>))"
  apply (multi_cases "a" "b")
  apply (simp_all add: xreal_na_reduce)
  apply (simp_all add: xreal_na_reduce diff_minus [THEN sym])
  apply (rule iffI)
  apply simp+
done

lemma xreal_na_diff_less_eq:
  "(a-\<^finna>{:x:} < c) = (a < c + \<^finna>{:x:})"
  apply (multi_cases "a" "c")
  apply (simp_all add: xreal_na_reduce)
  apply (rule xreal_na_less_iff_diff_less_0 [of _ c, THEN ssubst])
  apply (auto simp add: xreal_na_diff_def add_ac xreal_na_right_minus)
done

lemma xreal_na_less_diff_eq:
  "(a < c-\<^finna>{:x:}) = (a + \<^finna>{:x:} < c)"
  apply (multi_cases "a" "c")
  apply (simp_all add: xreal_na_reduce)
  apply (auto simp add: xreal_na_diff_def add_ac xreal_na_left_minus)
done

lemma xreal_na_diff_le_eq:
  "(a-\<^finna>{:x:} \<le> c) = (a \<le> c + \<^finna>{:x:})"
by (auto simp add: order_le_less xreal_na_diff_less_eq 
                   xreal_na_diff_add_cancel xreal_na_add_diff_cancel)

lemma xreal_na_le_diff_eq:
  "(a \<le> c-\<^finna>{:x:}) = (a + \<^finna>{:x:} \<le> c)"
by (auto simp add: order_le_less xreal_na_less_diff_eq 
                   xreal_na_diff_add_cancel xreal_na_add_diff_cancel)

lemmas xreal_na_compare_rls_1 = xreal_na_compare_rls_0
  xreal_na_diff_less_eq
  xreal_na_less_diff_eq
  xreal_na_diff_le_eq
  xreal_na_le_diff_eq

lemma xreal_na_less_iff_diff_less_0_1:
  "(a < \<^finna>{:x:}) = (a - \<^finna>{:x:} < 0)"
  apply (cases "a")
  apply (simp_all add: xreal_na_reduce diff_minus [THEN sym])
done

lemma xreal_na_less_iff_diff_less_0_2:
  "(\<^finna>{:x:} < b) = (\<^finna>{:x:} - b < 0)"
  apply (cases "b")
  apply (simp_all add: xreal_na_reduce diff_minus [THEN sym])
done

lemmas xreal_na_diff_less_0_iff_less =
  xreal_na_less_iff_diff_less_0_1 [symmetric]
  xreal_na_less_iff_diff_less_0_2 [symmetric]
declare xreal_na_diff_less_0_iff_less [simp]

lemma xreal_na_le_iff_diff_le_0_1:
  "(a \<le> \<^finna>{:x:}) = (a-\<^finna>{:x:} \<le> 0)"
  apply (cases "a")
  apply (simp_all add: xreal_na_reduce xreal_na_compare_rls_1 algebra_simps)
done

lemma xreal_na_le_iff_diff_le_0_2:
  "(\<^finna>{:x:} \<le> b) = (\<^finna>{:x:}-b \<le> 0)"
  apply (cases "b")
  apply (auto simp add: xreal_na_reduce)
done

lemmas xreal_na_diff_le_0_iff_le =
  xreal_na_le_iff_diff_le_0_1 [symmetric]
  xreal_na_le_iff_diff_le_0_2 [symmetric]

declare xreal_na_diff_le_0_iff_le [simp]

(*
lemma xreal_na_reduce_eq_0a [simp]:
  "\<^finna>{:x:} = 0 \<iff> x = 0"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_eq_0b [simp]:
  "0 = \<^finna>{:x:} \<iff> x = 0"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_eq_1a [simp]:
  "\<^finna>{:x:} = 1 \<iff> x = 1"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_eq_1b [simp]:
  "1 = \<^finna>{:x:} \<iff> x = 1"
by (auto simp add: xreal_na_reduce)
*)

lemma xreal_na_reduce_le_0a [simp]:
  "\<^finna>{:x:} \<le> \<^finna>{:0:} \<Leftrightarrow> x \<le> 0"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_le_0b [simp]:
  "\<^finna>{:0:} \<le> \<^finna>{:x:} \<Leftrightarrow> 0 \<le> x"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_le_0c [simp]:
  "-\<zinftyna> \<le> \<^finna>{:0:}"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_le_0d [simp]:
  "\<^finna>{:0:} \<le> \<zinftyna>"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_le_1a [simp]:
  "\<^finna>{:x:} \<le> \<^finna>{:1:} \<Leftrightarrow> x \<le> 1"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_le_1b [simp]:
  "\<^finna>{:1:} \<le> \<^finna>{:x:} \<Leftrightarrow> 1 \<le> x"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_le_1c [simp]:
  "-\<zinftyna> \<le> \<^finna>{:1:}"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_le_1d [simp]:
  "\<^finna>{:1:} \<le> \<zinftyna>"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_less_0a [simp]:
  "\<^finna>{:x:} < \<^finna>{:0:} \<Leftrightarrow> x < 0"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_less_0b [simp]:
  "\<^finna>{:0:} < \<^finna>{:x:} \<Leftrightarrow> 0 < x"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_less_0c [simp]:
  "-\<zinftyna> < \<^finna>{:0:}"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_less_0d [simp]:
  "\<^finna>{:0:} < \<zinftyna>"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_less_1a [simp]:
  "\<^finna>{:x:} < \<^finna>{:1:} \<Leftrightarrow> x < 1"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_less_1b [simp]:
  "\<^finna>{:1:} < \<^finna>{:x:} \<Leftrightarrow> 1 < x"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_less_1c [simp]:
  "-\<zinftyna> < \<^finna>{:1:}"
by (auto simp add: xreal_na_reduce)

lemma xreal_na_reduce_less_1d [simp]:
  "\<^finna>{:1:} < \<zinftyna>"
by (auto simp add: xreal_na_reduce)

lemmas xreal_na_compare_rls = xreal_na_compare_rls_1
  xreal_na_zero_def
  xreal_na_one_def
  xreal_na_reduce_le_0a
  xreal_na_reduce_le_0b
  xreal_na_reduce_le_0c
  xreal_na_reduce_le_0d
  xreal_na_reduce_le_1a
  xreal_na_reduce_le_1b
  xreal_na_reduce_le_1c
  xreal_na_reduce_le_1d
  xreal_na_reduce_less_0a
  xreal_na_reduce_less_0b
  xreal_na_reduce_less_0c
  xreal_na_reduce_less_0d
  xreal_na_reduce_less_1a
  xreal_na_reduce_less_1b
  xreal_na_reduce_less_1c
  xreal_na_reduce_less_1d

text{*
Again, it seems worthwhile to supersede these with some more general simp rules.
Note refl is already [iff].

*}


(*
lemma
  "\<arb>[:\<xrealna>:] = \<^finna>{:0:} \<turnstile> \<arb> < \<^finna>{:1:}"
thm subst
  apply (rule ssubst [where ?t = "\<arb>"], assumption)
  apply (thin_tac "?P")
  apply (simp add: xreal_na_reduce)
*)

lemma xreal_na_finite_comparison_reduce [simp]:
  "\<^finna>{:x:} \<le> \<^finna>{:y:} = (x \<le> y)"
  "\<^finna>{:x:} < \<^finna>{:y:} = (x < y)"
by (auto simp add: xreal_na_reduce)+

lemma xreal_na_infinite_comparison_reduce [simp]:
  "-\<zinftyna> \<le> a"
  "-\<zinftyna> \<le> (\<zinftyna> + -\<zinftyna>)"
  "a \<le> \<zinftyna>"
  "(\<arb>::\<xrealna>) \<le> \<zinftyna>"
  "-\<zinftyna> < \<^finna>{:x:}"
  "-\<zinftyna> < \<zinftyna>"
  "\<^finna>{:x:} < \<zinftyna>"
  apply (multi_cases "a" "(\<arb>::\<xrealna>)")
  apply (simp add: xreal_na_reduce)+ defer
  apply (cases "a")
  apply (simp add: xreal_na_reduce, simp add: xreal_na_reduce, simp add: xreal_na_reduce)
  apply (cases "(\<arb>::\<xrealna>)")
  apply (simp add: xreal_na_reduce) defer
  apply (simp add: xreal_na_reduce)+
  apply (cases "(\<arb>::\<xrealna>)")
  apply (simp add: xreal_na_reduce)
  apply (rule ssubst [where ?t = "\<arb>"], assumption)
  apply (thin_tac "?P")
  apply (simp add: xreal_na_reduce)
  apply (simp add: xreal_na_reduce)
  apply (rule ssubst [where ?t = "\<arb>"], assumption)
  apply (thin_tac "?P")
  apply (simp add: xreal_na_reduce)
done


text{*
\section{Embedding into reals}

*}


defs (overloaded)
  real_of_xreal_na_def: "real x \<defs>
    \<case> x \<of>
      -\<zinftyna> \<longrightarrow> -1
    | \<^finna>{:a:} \<longrightarrow> a/(1 + (abs a))
    | \<zinftyna> \<longrightarrow> 1
    \<esac>"


lemma real_of_xreal_na_zero [simp]: "real (0::\<xrealna>) = 0"  
by (simp add: real_of_xreal_na_def xreal_na_zero_def) 

lemma real_of_xreal_na_one [simp]: "real (1::\<xrealna>) = (1/2::real)"
by (simp add: real_of_xreal_na_def xreal_na_one_def) 

lemma real_of_xreal_na_minus [simp]: "real(-x) = -real (x::\<xrealna>)"
  apply (simp add: real_of_xreal_na_def) 
  apply (cases "x", auto simp add: xreal_na_reduce)
done


lemma real_of_xreal_na_inject [iff]: "(real (x::\<xrealna>) = real y) = (x = y)"
proof-
 {fix r :: \<real>
  have "r < 1 + abs r"
  by (auto simp add: abs_if)
  then have
  "1 + abs r \<noteq> r" by auto
  } note R1 = this
 {fix r :: \<real>
  have "-r < 1 + abs r"
  by (auto simp add: abs_if)
  then have
  "r \<noteq> - (1 + abs r)" by auto
  then have 
  "r/(1 + abs r) \<noteq> - (1 + abs r)/(1 + abs r)" by (auto simp add: abs_if)
  then have
  "r/(1 + abs r) \<noteq> -1" 
  by (subst (asm) minus_divide_left [THEN sym], simp+)
  } note R2 = this
  show ?thesis
    apply (simp add: real_of_xreal_na_def) 
    apply (multi_cases "x" "y", simp_all)
    apply (auto simp add: R1 R2)
  proof-
    fix r r' :: \<real>
    assume Aa1: "r / (1 + abs r) = r' / (1 + abs r')"
    then have
    "r  = (r' / (1 + abs r')) * (1 + abs r)" 
thm  nonzero_divide_eq_eq [THEN iffD1]
      apply (intro nonzero_divide_eq_eq [THEN iffD1]) 
      apply (auto simp add: abs_if)
    done
    then have
    "r  = ((r'  * (1 + abs r))/ (1 + abs r'))"  by auto
    then have Ra1:
    "(r * (1 + abs r')) = (r'  * (1 + abs r))" 
      apply (intro nonzero_divide_eq_eq [THEN iffD1, THEN sym]) 
      apply (auto simp add: abs_if)
    done
    have
    "(0 \<le> r \<and> 0 \<le> r') \<or> (r < 0 \<and> r' < 0)"
      apply (rule Ra1 [THEN contrapos_pp])
      apply (simp add: linorder_not_le linorder_not_less)
      apply (msafe_no_assms(inference))
      apply (simp add: order_le_less) defer
      apply (simp only: order_le_less, elim disjE) defer apply simp
      apply (simp add: order_le_less) 
      apply (simp only: order_le_less, elim disjE) defer apply simp
      apply (simp only: linorder_neq_iff, rule disjI2) 
      apply (rule order_less_trans)
      apply (rule mult_strict_right_mono, simp, simp, simp only: mult_zero_left)
      apply (rule mult_pos_pos, simp+)
      apply (simp only: linorder_neq_iff, rule disjI1) 
      apply (rule order_less_trans)
      apply (rule mult_strict_right_mono, simp, simp, simp only: mult_zero_left)
      apply (rule mult_pos_pos, simp+)
    done
    with Ra1
    show
    "r = r'"
    by (auto simp add: distrib_left linorder_not_le)
  qed
qed





lemma real_of_xreal_na_mono:
  "(a::\<xrealna>) \<le> b \<turnstile> real a \<le> real b"
proof-
  assume Aa1: "a \<le> b"
  from Aa1 show ?thesis
    apply (multi_cases "a" "b")
    apply (auto simp add: real_of_xreal_na_def xreal_na_reduce)
    apply (subst pos_le_divide_eq, simp add: abs_if, simp add: abs_if)    apply (subst pos_le_divide_eq) 
    apply (simp add: abs_if, simp)    
    apply (subst pos_divide_le_eq) 
    apply (simp add: abs_if)    
    apply (auto simp add: abs_if distrib_left linorder_not_less)
  proof-
    fix r r' :: \<real>
    assume Aa1: "0 \<le> r'"
    assume Aa2: "r < 0"
    from Aa1 have
    "0 < (2*r'+1)" by auto
    with Aa2 have
    "r*(2*r'+1) < r*0" by (simp only: mult_less_cancel_left_disj, simp)
    with Aa1 show
    "2 * (r*r') + r \<le> r'"    
    by (auto simp add: distrib_left mult_assoc mult_left_commute)
  qed
qed


text{*
\section{Extended real intervals}

A similar treatment of course applies to the extended reals.

*}


instantiation
  xreal_na :: linlat
begin

definition
  inf_xreal_na_def: "oinf \<defs> (\<olambda> (x::\<xrealna>) y \<bullet> \<if> x \<le> y \<then> x \<else> y \<fi>)"

definition
  sup_xreal_na_def: "osup \<defs> (\<olambda> (x::\<xrealna>) y \<bullet> \<if> x \<le> y \<then> y \<else> x \<fi>)"

instance
  apply (intro_classes)
  apply (simp_all add: inf_xreal_na_def sup_xreal_na_def)
  done

end

interpretation 
  lattice_xreal_na: Lattice_Locale.lattice "\<univ>-[\<xrealna>]" "op \<le>"
  by (unfold_locales)


lemma real_ex_Sup': 
  assumes 
    A1: "(S::real set) \<noteq> \<emptyset>" and
    A2: "\<^ubp>{:\<univ>-[\<real>]:}{:op \<le>:} S u"
  shows
    "(\<exists>\<subone> Sup \<bullet> \<^lubp>{:\<univ>-[\<real>]:}{:op \<le>:} S Sup)"
proof -
  from A1 A2 have 
      "(\<exists> Sup \<bullet> isLub \<univ>-[\<real>] S Sup)" 
    by (intro reals_complete, auto simp add: isUb_def setle_def is_ub_def)
  then obtain Sup where 
      "\<^lubp>{:\<univ>-[\<real>]:}{:op \<le>:} S Sup" 
    by (auto simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
  then show 
      ?thesis
    apply (intro ex1I, assumption)
    apply (rule order_classD [THEN partial_order.lub_unique, of S], assumption+)
    done
qed

theorem real_ex_Inf': 
  assumes 
    A1: "(S::real set) \<noteq> \<emptyset>" and
    A2: "\<^lbp>{:\<univ>-[\<real>]:}{:op \<le>:} S u"
  shows
    "(\<exists>\<subone> Inf \<bullet> \<^glbp>{:\<univ>-[\<real>]:}{:op \<le>:} S Inf)"
proof -
txt {* 
The proof relies on the observation that Infs and Sups 
are dual under negation.
*}
  let ?SM = "uminus \<lparr>S\<rparr>"
  from A2 have "\<^ubp>{:\<univ>-[\<real>]:}{:op \<le>:} ?SM (-u)"
  by (auto simp add: is_ub_def is_lb_def)
  from A1 this [THEN [2] real_ex_Sup'] obtain Sup where 
  "\<^lubp>{:\<univ>-[\<real>]:}{:op \<le>:} ?SM Sup" 
  by auto
  then have
  "\<^glbp>{:\<univ>-[\<real>]:}{:op \<le>:} S (-Sup)"
    apply (auto simp add: is_lub_def is_least_def is_glb_def is_greatest_def )
    apply (simp add: is_ub_def is_lb_def, auto)
    apply (subst neg_le_iff_le [THEN sym])
    apply (subst minus_minus)
    apply (elim allE impE)
  defer
    apply assumption
    apply (auto simp add: is_ub_def is_lb_def)
  done
  then show ?thesis
    apply (intro ex1I, assumption)
    apply (rule order_classD [THEN partial_order.glb_unique, of S], assumption+)
  done
qed


lemma xreal_na_ex_Sup': 
  assumes A1: "(S::xreal_na set) \<noteq> \<emptyset>"
  shows
    "\<exists>\<subone> Sup \<bullet> \<^lubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} S Sup"
  apply (cases "\<exists> (r::\<real>) \<bullet> \<^ubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} S \<^finna>{:r:}")
  apply (cases "S = {-\<zinftyna>}", (msafe_no_assms(inference)))
proof-  
  fix r :: \<real>
  assume Aa1: "S = {-\<zinftyna>}"
  then have
  "\<^lubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} S -\<zinftyna>"
  by (auto simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
  then show ?thesis
    apply (intro ex1I, assumption)
    apply (rule order_classD [THEN partial_order.lub_unique, of S], assumption+)
  done
next
  fix r :: \<real>
  assume Aa1: "S \<noteq> {-\<zinftyna>}"
  assume Aa2: "\<^ubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} S \<^finna>{:r:}"

  let ?S' = "{r' | \<^finna>{:r':} \<in> S}"
(*
  from A1 Aa1 Aa2 have
  "\<forall> x | x \<in> S - {-\<zinftyna>} \<bullet> (\<exists> (r'::\<real>) \<bullet> x = \<^finna>{:r':})"
    apply (simp only: xreal_na_All, (msafe_no_assms(inference)))
    apply (simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (intro exI, simp)
    apply (simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (elim allE [where ?x = "\<zinftyna>"], simp add: xreal_na_reduce)
  done
*)
  from Aa2 have Ra0:
  "\<zinftyna> \<notin> S"
    apply (simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (simp only: xreal_na_All, (msafe_no_assms(inference)))
    apply (simp add: xreal_na_reduce)
  done

  from A1 Aa1 Ra0 have Ra1:
  "S - {-\<zinftyna>} = fin_na \<lparr>?S'\<rparr>"  
    apply (subst set_eq_def)
    apply (simp add: xreal_na_All, (msafe_no_assms(inference)))
    apply (simp_all add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (simp_all add: xreal_na_reduce image_def)
  done
  have Ra2:
  "\<^ubp>{:\<univ>-[\<real>]:}{:op \<le>:} ?S' r"
    apply (simp_all add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (subst fin_na_order_embed)
    apply ((msafe_no_assms(inference)), intro Aa2 [THEN order_class.is_ubD], assumption)
  done
  from A1 Aa1 Ra0 have Ra3:
  "?S' \<noteq> \<emptyset>"
    apply auto
    apply (simp_all only: atomize_all atomize_imp)
    apply (simp_all only: xreal_na_All xreal_na_Ex, (msafe_no_assms(inference)))
    apply (simp_all add: image_def xreal_na_reduce)
  done
  from Ra2 Ra3 have "\<exists>\<subone> Sup \<bullet> \<^lubp>{:\<univ>-[\<real>]:}{:op \<le>:} ?S' Sup" 
  by (intro real_ex_Sup', simp_all)
  then obtain Sup where real_lub: "\<^lubp>{:\<univ>-[\<real>]:}{:op \<le>:} ?S' Sup" 
  by (auto)
  have
      "\<^lubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} (fin_na \<lparr>?S'\<rparr>) \<^finna>{:Sup:}"
    apply (rule order_class.is_lubI, simp_all add: image_def)
    apply auto
    apply (rule real_lub [THEN order_class.is_lubD1 [THEN order_class.is_ubD]])
    apply (simp_all only: atomize_all atomize_imp)
    apply (simp_all only: xreal_na_All xreal_na_Ex, (msafe_no_assms(inference)))
    apply (simp_all add: xreal_na_reduce)
    apply (insert Ra3, simp add: image_def)
    apply (rule real_lub [THEN order_class.is_lubD2'])
    apply (simp_all)
    done
  then have
      "\<^lubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} S \<^finna>{:Sup:}"
    apply (simp add: Ra1 [THEN sym])
    apply (simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (simp_all only: xreal_na_All xreal_na_Ex, (msafe_no_assms(inference)))
    apply (simp_all add: xreal_na_reduce)
    done
  then show 
      ?thesis
    apply (intro ex1I, assumption)
    apply (rule order_class.lub_unique, simp_all) 
    done
next
  apply_end simp
  assume 
    Aa1: "\<forall> r \<bullet> \<not> (\<^ubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} S \<^finna>{:r:})"
  then have
       "\<^lubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} S \<zinftyna>"
    apply (cases "\<zinftyna> \<in> S")
    apply (simp_all add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def not_le)
    apply (msafe_no_assms(inference))
  proof -
    assume 
      c1: "\<zinftyna> \<notin> S"
    fix x
    assume
      c2: "(\<forall> r \<bullet> (\<exists> y \<bullet> y \<in> S \<and> \<^finna>{:r:} < y))" and
      c3: "(\<forall> y \<bullet> y \<in> S \<Rightarrow> y \<le> x)"
    from c3 show
      "\<zinftyna> \<le> x"
      apply (cases x)
      apply (simp_all)
    proof -
      assume 
        d1: "(\<forall> y \<bullet> y \<in> S \<Rightarrow> y \<le> -\<zinftyna>)"
      from c2 [rule_format, of "0"] obtain y where
        d2: "y \<in> S" and d3: "\<^finna>{:0:} < y"
        by (auto)
      from d3 have 
        d4: "y \<noteq> -\<zinftyna>"
        by (auto simp add: xreal_na_reduce)
      from d2 d1 have 
        d4': "y \<le> -\<zinftyna>"
        by (auto)
      from d4 d4' show
        "\<zinftyna> \<le> -\<zinftyna>"
        apply (cases y)
        apply (auto simp add: xreal_na_reduce)
        done
    next
      fix r
      assume 
        d1: "(\<forall> y \<bullet> y \<in> S \<Rightarrow> y \<le> \<^finna>{:r:})"
      from c2 [rule_format, of "r"] obtain y where
        d2: "y \<in> S" and d3: "\<^finna>{:r:} < y"
        by (auto)
      with d1 show 
        "\<zinftyna> \<le> \<^finna>{:r:}"
        by (auto)
    qed
  qed
  then show ?thesis
    apply (intro ex1I, assumption)
    apply (rule order_class.lub_unique, simp_all) 
    done
qed

theorem xreal_na_ex_Inf': 
  assumes 
    A1: "(S::xreal_na set) \<noteq> \<emptyset>"
  shows
      "(\<exists>\<subone> Inf \<bullet> \<^glbp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} S Inf)"
proof -
txt {* 
The proof relies on the observation that Infs and Sups 
are dual under negation.
*}
  let ?SM = "uminus \<lparr>S\<rparr>"
  from A1 have 
      "?SM \<noteq> \<emptyset>"
    by (auto simp add: image_def)
  from this [THEN xreal_na_ex_Sup'] obtain Sup where 
      "\<^lubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} ?SM Sup" 
    by auto
  then have
      "\<^glbp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} S (-Sup)"
    apply (auto simp add: is_lub_def is_least_def is_glb_def is_greatest_def )
    apply (simp add: is_ub_def is_lb_def, auto)
thm neg_le_iff_le
    apply (subst xreal_na_neg_le_iff_le [THEN sym])
    apply (subst xreal_na_minus_minus)
    apply (rule allE, assumption, thin_tac "?P")
    apply (elim impE) defer 
    apply assumption defer
    apply simp
    apply (rotate_tac 1)
    apply (rule allE, assumption, thin_tac "?P")
    apply (elim impE) defer
    apply (subst xreal_na_le_minus_iff, assumption)
    apply (rotate_tac 1, thin_tac "?P")
    apply (auto simp add: is_ub_def is_lb_def)
    apply (subst xreal_na_neg_le_iff_le [THEN sym])
    apply (simp add: xreal_na_minus_minus)
    done
  then show 
      ?thesis
    apply (intro ex1I, assumption)
    apply (rule order_class.glb_unique, assumption+)
    done
qed

theorem xreal_na_clattice:
    "\<^clattice>{:\<univ>-[\<xrealna>]:}{:op \<le>:}"
proof (rule order_class.clatticeI)
  fix 
    X :: "\<xrealna> set"
  assume 
    A2: "X \<subseteq> \<univ>-[\<xrealna>]"
  show
      "(\<exists> z \<bullet> \<^glbp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} X z)"
  proof (cases "X = \<emptyset>")
    assume 
      A11: "X = \<emptyset>"
    from A2 A11 show 
        ?thesis
      apply (auto simp add: is_glb_def is_lb_def is_greatest_def)
      apply (witness "\<zinftyna>")
      apply (simp only: xreal_na_All xreal_na_Ex, (msafe_no_assms(inference)))
      apply (auto simp add: xreal_na_reduce)
      done
  next
    assume 
      A11: "X \<noteq> \<emptyset>"
    then have
        "(\<exists>\<subone> Inf \<bullet> \<^glbp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} X Inf)"
      by (intro xreal_na_ex_Inf', simp)
    then show
        "(\<exists> Inf \<bullet> \<^glbp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} X Inf)"
      by auto
  qed
next
  fix 
    X :: "\<xrealna> set"
  assume 
    A2: "X \<subseteq> \<univ>-[\<xrealna>]"
  show
      "(\<exists> z \<bullet> \<^lubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} X z)"
  proof (cases "X = \<emptyset>")
    assume 
      A11: "X = \<emptyset>"
    from A2 A11 show 
        ?thesis
      apply (auto simp add: is_lub_def is_ub_def is_least_def)
      apply (witness "-\<zinftyna>")
      apply (simp only: xreal_na_All xreal_na_Ex, (msafe_no_assms(inference)))
      apply (auto simp add: xreal_na_reduce)
      done
  next
    assume 
      A11: "X \<noteq> \<emptyset>"
    then have
        "(\<exists>\<subone> Sup \<bullet> \<^lubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} X Sup)"
      by (intro xreal_na_ex_Sup', simp)
    then show
        "(\<exists> Sup \<bullet> \<^lubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} X Sup)"
      by auto
  qed
qed


theorem xreal_na_interval_clattice:
    "(a::\<xrealna>) \<le> b 
    \<turnstile> \<^clattice>{:\<lclose>a\<dots>b\<rclose>:}{:\<^subord>{:op \<le>:}{:\<lclose>a\<dots>b\<rclose>:}:}"
proof-
  assume 
    A1: "a \<le> b"
  from A1 interpret 
    po_interval: partial_order "\<lclose>a\<dots>b\<rclose>" "\<^subord>{:op \<le>:}{:\<lclose>a\<dots>b\<rclose>:}"
    by (auto simp add: partial_order_def' carrier_def setrel_axioms_def reflexive_axioms_def transitive_axioms_def antisymmetric_axioms_def rel_def interval_defs subset_order_def op2rel_def rel2op_def)
  show 
      ?thesis
  proof (rule po_interval.clatticeI)
    fix 
      X :: "\<xrealna> set"
    assume 
      A2: "X \<subseteq> \<lclose>a\<dots>b\<rclose>"
    show
        "(\<exists> z \<bullet> \<^glbp>{:\<lclose>a\<dots>b\<rclose>:}{:\<^subord>{:op \<le>:}{:\<lclose>a\<dots>b\<rclose>:}:} X z)"
    proof (cases "X = \<emptyset>")
      assume 
        A11: "X = \<emptyset>"
      from A1 A2 A11 show 
          ?thesis
        apply (auto simp add: is_glb_def is_lb_def is_greatest_def)
        apply (auto simp add: interval_defs subset_order_def op2rel_def rel2op_def)
        done
    next
      assume 
        A11: "X \<noteq> \<emptyset>"
      from A11 obtain x where 
        R0': "x \<in> X" 
        by auto
      from A1 A2 A11 have 
          "(\<exists>\<subone> Inf \<bullet> \<^glbp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} X Inf)"
        by (intro xreal_na_ex_Inf',simp)
      then obtain Inf where 
        R1': "(\<forall> x | x \<in> X \<bullet> Inf \<le> x) \<and> (\<forall> l | (\<forall> x | x \<in> X \<bullet> l \<le> x) \<bullet> l \<le> Inf)" 
        by (auto simp add: is_lb_def is_glb_def is_greatest_def)
      from R1' have 
        R2a: "(\<forall> x | x \<in> X \<bullet> Inf \<le> x)"
        by (auto)
      from R1' have 
        R2b: "(\<forall> l | (\<forall> x | x \<in> X \<bullet> l \<le> x) \<bullet> l \<le> Inf)"
        by (auto)
      have R2c:
          "Inf \<in> \<lclose>a\<dots>b\<rclose>"
      proof (auto simp add: interval_defs)
        from R0' have 
            "Inf 
            \<le> x"
          by (intro R2a [rule_format])
        also from R0' A1 A2 have "... 
            \<le> b"
          by (auto simp add: interval_defs)
        finally show
            "Inf \<le> b"
          by (this)
      next
        from A1 A2 show 
            "a \<le> Inf"
          apply (intro R2b [rule_format])
          apply (auto simp add: interval_defs) 
          done
      qed
      from A1 A2 R2c show 
          ?thesis
        apply (intro exI [where ?x = "Inf"])
        apply (auto simp add: is_glb_def is_lb_def is_greatest_def)
        apply (auto simp add: subset_order_def op2rel_def rel2op_def)
        apply (intro R2a [rule_format])
        apply (auto)
        apply (intro R2b [rule_format])
        apply (auto)
        done
    qed
  next
    fix 
      X :: "\<xrealna> set"
    assume 
      A2: "X \<subseteq> \<lclose>a\<dots>b\<rclose>"
    show
        "(\<exists> z \<bullet> \<^lubp>{:\<lclose>a\<dots>b\<rclose>:}{:\<^subord>{:op \<le>:}{:\<lclose>a\<dots>b\<rclose>:}:} X z)"
    proof (cases "X = \<emptyset>")
      assume 
        A11: "X = \<emptyset>"
      from A1 A2 A11 show 
          ?thesis
        apply (auto simp add: is_lub_def is_ub_def is_least_def)
        apply (auto simp add: interval_defs subset_order_def op2rel_def rel2op_def)
        done
    next
      assume 
        A11: "X \<noteq> \<emptyset>"
      from A11 obtain x where 
        R0': "x \<in> X" 
        by auto
      from A1 A2 A11 have 
          "(\<exists>\<subone> Sup \<bullet> \<^lubp>{:\<univ>-[\<xrealna>]:}{:op \<le>:} X Sup)"
        by (intro xreal_na_ex_Sup', simp)
      then obtain Sup where 
        R1': "(\<forall> x | x \<in> X \<bullet> x \<le> Sup) \<and> (\<forall> u | (\<forall> x | x \<in> X \<bullet> x \<le> u) \<bullet> Sup \<le> u)" 
        by (auto simp add: is_ub_def is_lub_def is_least_def)
      from R1' have 
        R2a: "(\<forall> x | x \<in> X \<bullet> x \<le> Sup)"
        by (auto)
      from R1' have
        R2b: "(\<forall> u | (\<forall> x | x \<in> X \<bullet> x \<le> u) \<bullet> Sup \<le> u)"
        by (auto)
      have 
        R2c: "Sup \<in> \<lclose>a\<dots>b\<rclose>"
      proof (auto simp add: interval_defs)
        from R0' A1 A2 have 
            "a 
            \<le> x"
          by (auto simp add: interval_defs)
        also from R0' have "... 
            \<le> Sup"
          by (intro R2a [rule_format])
        finally show
            "a \<le> Sup"
          by (this)
      next
        from A1 A2 show 
            "Sup \<le> b"
          apply (intro R2b [rule_format])
          apply (auto simp add: interval_defs)
          done
      qed
      from A1 A2 R2c show 
          ?thesis
        apply (intro exI [where ?x = "Sup"])
        apply (auto simp add: is_lub_def is_ub_def is_least_def)
        apply (auto simp add: subset_order_def op2rel_def rel2op_def)
        apply (intro R2a [rule_format])
        apply (auto)
        apply (intro R2b [rule_format])
        apply (auto)
        done
    qed
  qed
qed







text {* The non associative extended real numbers are an instance of metric. *}

instantiation xreal_na :: metric
begin

definition
  distance_xreal_na_def:  "\<^mcdist>{:x::\<xrealna>:}{:y:} \<defs> abs ((real x) - (real y))"


instance 
  apply (intro_classes)
  apply (simp add: distance_xreal_na_def | (msafe_no_assms(inference)))+
  done

end





end
