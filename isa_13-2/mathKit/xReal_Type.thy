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
  xReal_Type 
  
imports 
  Z_Toolkit 
  Metric_Class
begin

text {*

Following Royden~\cite{royden:realanal} we develop the extended reals.

The extended reals add @{text "\<plusminus>\<infinity>"}, being at the
respective extremities of the real order.

*}

datatype
  xreal = ninfty | fin real | infty

type_notation (xsymbols output)
  xreal ("\<real>\<^sub>\<zinfty>")

type_notation (zed)
  xreal ("\<xreal>")

notation (xsymbols output)
  fin ("_") and
  ninfty ("-\<zinfty>") and
  infty ("\<zinfty>")

notation (zed)
  fin ("\<^fin>{:_:}") and
  ninfty ("-\<zinfty>") and
  infty ("\<zinfty>")

text {*

The zero and one of the extended reals are the finite embeddings.
We activate binary number representations for the extended reals.

*}

instantiation xreal :: "{zero,one}"
begin

definition 
  xreal_zero_def:  "0 \<defs> \<^fin>{:0:}"
definition 
  xreal_one_def:  "1 \<defs> \<^fin>{:1:}"
(*
this for instantiation xreal :: number... gone!
definition
  xreal_number_of_def [simp]:
    "number_of x \<defs> \<^fin>{:(number_of x):}"
*)

instance
  by (intro_classes)  

end

text {*

Addition is extended to the extremities.  The group properties of the reals
cannot be preserved in the extended reals so we simply leave the sum of the
bottom and top elements underdetermined: the result must be in the boundary
set.  With this choice we have a semigroup structure under addition; i.e., the
addition is associative.  If the result were finite then , e.g., 
@{text "\<zinfty> + (-\<zinfty> + x) = \<zinfty> + -\<zinfty> \<noteq> (\<zinfty> + -\<zinfty>) + x"}.  
The following
technical lemmas show that Hilbert choice implements this restriction.

*}


lemma xreal_choose_bdy:
  "(\<some> a | a = \<zinfty> \<or> a = -\<zinfty>) = \<zinfty> 
  \<or> (\<some> a | a = \<zinfty> \<or> a = -\<zinfty>) = -\<zinfty>"
  by (rule someI_ex, auto)

lemma xreal_choose_bdy2:
  "(\<some> a | a \<in> { -\<zinfty>, \<zinfty>}) = \<zinfty> 
  \<or> (\<some> a | a \<in> { -\<zinfty>, \<zinfty>}) = -\<zinfty>"
  by (auto simp add: xreal_choose_bdy disj_commute)

text {*

Multiplication is also extended in the obvious way, with 
@{text "0 * \<zinfty>"} set to @{text 0} by convention.  Then multiplying anything by 
@{text "0"} leaves @{text "0"}.  
Again, alternatives will give us problems with associativity.  If
the result were @{text "\<zinfty> * 0 = a"}, then @{text "(\<zinfty> * 0) * x = \<zinfty> * (0 * x)"}
implies that @{text "a * x = a"}.
*}

text {*

The interesting case for inverse is of course @{text 0}, where the result is
left completely undetermined.  

*}

instantiation
  xreal :: "{plus,uminus,minus,times,inverse}"
begin

definition
  xreal_add_def: "x + y \<defs> 
    \<case> x \<of>
      -\<zinfty> \<longrightarrow> (\<case> y \<of> -\<zinfty> \<longrightarrow>
-\<zinfty> | \<^fin>{:b:} \<longrightarrow> -\<zinfty> | \<zinfty> \<longrightarrow> (\<some> a | a \<in> { -\<zinfty>, \<zinfty>}) \<esac>)
    | \<^fin>{:a:} \<longrightarrow> (\<case> y \<of> -\<zinfty> \<longrightarrow> -\<zinfty> | \<^fin>{:b:} \<longrightarrow> \<^fin>{:(a+b):} | \<zinfty> \<longrightarrow> \<zinfty> \<esac>)
    | \<zinfty> \<longrightarrow> (\<case> y \<of> -\<zinfty> \<longrightarrow> (\<some> a | a \<in> { -\<zinfty>, \<zinfty>}) | \<^fin>{:b:} \<longrightarrow> \<zinfty> | \<zinfty> \<longrightarrow> \<zinfty> \<esac>)
    \<esac>"

definition
  xreal_mult_def: "x * y \<defs> 
    \<case> x \<of>
      -\<zinfty> \<longrightarrow> 
        \<case> y \<of> 
          -\<zinfty> \<longrightarrow> \<zinfty> 
        | \<^fin>{:b:} \<longrightarrow> 
            \<if> b < 0 \<then> \<zinfty> 
            \<else> \<if> b = 0 \<then> 0 \<else> -\<zinfty> \<fi>
            \<fi>
        | \<zinfty> \<longrightarrow> -\<zinfty> 
        \<esac>
    | \<^fin>{:a:} \<longrightarrow> 
        \<case> y \<of> 
          -\<zinfty> \<longrightarrow>  
            \<if> a < 0 \<then> \<zinfty> 
            \<else> \<if> a = 0 \<then> 0 \<else> -\<zinfty> \<fi>
            \<fi> 
        | \<^fin>{:b:} \<longrightarrow> \<^fin>{:(a*b):} 
        | \<zinfty> \<longrightarrow>  
            \<if> a < 0 \<then> -\<zinfty> 
            \<else> \<if> a = 0 \<then> 0 \<else> \<zinfty> \<fi>
            \<fi>
        \<esac>
    | \<zinfty> \<longrightarrow> 
        \<case> y \<of> 
          -\<zinfty> \<longrightarrow> -\<zinfty> 
        | \<^fin>{:b:} \<longrightarrow>  
            \<if> b < 0 \<then> -\<zinfty> 
            \<else> \<if> b = 0 \<then> 0 \<else> \<zinfty> \<fi>
            \<fi>
        | \<zinfty> \<longrightarrow> \<zinfty> 
        \<esac>
    \<esac>"

definition
  xreal_uminus_def: "- x \<defs>
    \<case> x \<of>
      -\<zinfty> \<longrightarrow> \<zinfty>
    | \<^fin>{:a:} \<longrightarrow> \<^fin>{:(- a):}
    | \<zinfty> \<longrightarrow> -\<zinfty>
    \<esac>"

definition
  xreal_diff_def: "x - (y::xreal) \<defs> x + (- y)"

definition
  xreal_inverse_def: "inverse x \<defs>
    \<case> x \<of>
      -\<zinfty> \<longrightarrow> 0
    | \<^fin>{:a:} \<longrightarrow> \<if> a = 0 \<then> (\<some> b | \<True>) \<else> \<^fin>{:(inverse a):} \<fi>
    | \<zinfty> \<longrightarrow> 0
    \<esac>"

definition
  xreal_divide_def: "x / (y::xreal) \<defs> x * (inverse y)"

instance
  by (intro_classes)

end

lemma uminus_idem [simp]: "-(-(x::xreal)) = x"
  by (cases x, auto simp add: xreal_uminus_def)


text {* \section{The extended real numbers are linearly ordered} *}

instantiation xreal :: order
begin

  definition
    le_xreal_def: "x \<le> y \<defs>
    \<case> x \<of>
      -\<zinfty> \<longrightarrow> 
        \<case> y \<of> 
          -\<zinfty> \<longrightarrow> \<True> 
        | fin b \<longrightarrow> \<True>
        | \<zinfty> \<longrightarrow> \<True>
        \<esac>
    | fin a \<longrightarrow> 
        \<case> y \<of> 
          -\<zinfty> \<longrightarrow> \<False>
        | fin b \<longrightarrow> a \<le> b 
        | \<zinfty> \<longrightarrow> \<True>
        \<esac>
    | \<zinfty> \<longrightarrow> 
        \<case> y \<of> 
          -\<zinfty> \<longrightarrow> \<False>
        | fin b \<longrightarrow> \<False>
        | \<zinfty> \<longrightarrow> \<True>
        \<esac>
    \<esac>"

  definition
    lt_xreal_def: "x < (y::xreal) \<defs> x \<le> y \<and> x \<noteq> y"


  instance
  proof (intro_classes) -- reflection
    fix x::xreal
    show "x \<le> x" by (cases x, auto simp add: le_xreal_def lt_xreal_def)
  next -- transitivity
    fix x::xreal and y::xreal and z::xreal
    assume a1: "x \<le> y" and a2: "y \<le> z"
    from a1 a2 show "x \<le> z"
    by (multi_cases x y z, auto simp add: le_xreal_def lt_xreal_def)
  next -- asymmetry 
    fix x::xreal and y::xreal
    assume a1: "x \<le> y" and a2: "y \<le> x"
    from a1 a2 show "x = y"
    by (multi_cases x y, auto simp add: le_xreal_def lt_xreal_def)
  next -- "lt irreflexive"
    fix x::xreal and y::xreal
    show "x < y \<Leftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
    by (multi_cases x y, auto simp add: le_xreal_def lt_xreal_def)
  qed


end

lemma le_xreal_simps:
  "-\<zinfty> \<le> r"
  "-\<zinfty> < fin a"
  "\<not>(fin a \<le> -\<zinfty>)"
  "\<not>(fin a < -\<zinfty>)"
  "fin a \<le> fin b \<Leftrightarrow> a \<le> b"
  "fin a < fin b \<Leftrightarrow> a < b"
  "fin a < \<zinfty>"
  "\<not>(\<zinfty> < fin a)"
  "\<not>(\<zinfty> \<le> fin a)"
  "r \<le> \<zinfty>"
  apply (auto simp add: le_xreal_def lt_xreal_def)
  apply (cases r, auto)+
  done

text {*

Unary negation is an order reflection.

*}

lemma uminus_amono: "-x \<le> -y \<Leftrightarrow> y \<le> (x::xreal)"
proof (cases x)
  assume a1: "x = -\<zinfty>"
  show ?thesis by (cases y, insert a1, auto simp add: xreal_uminus_def le_xreal_def lt_xreal_def)
next
  fix a assume a1: "x = fin a"
  show ?thesis by (cases y, insert a1, auto simp add: xreal_uminus_def le_xreal_def lt_xreal_def)
next
  assume a1: "x = \<zinfty>"
  show ?thesis by (cases y, insert a1, auto simp add: xreal_uminus_def le_xreal_def lt_xreal_def)
qed


text {* The embedding of reals is an order embedding.  *}


lemma fin_order_embed:
  "r \<le> r' \<Leftrightarrow> \<^fin>{:r:} \<le> \<^fin>{:r':}"
by (simp add:  le_xreal_def lt_xreal_def)


text {*

We prove linear order, and then some further arithmetic properties.

*}

instantiation xreal :: linorder
begin

  instance
  proof (intro_classes)
    fix x::xreal and y::xreal
    show "x \<le> y \<or> y \<le> x"
    by (multi_cases x y, auto simp add: le_xreal_def lt_xreal_def)
  qed

end


lemmas xreal_reduce = 
  xreal_zero_def xreal_one_def 
  xreal_add_def 
  xreal_mult_def 
  xreal_uminus_def xreal_diff_def 
  xreal_inverse_def xreal_divide_def
  le_xreal_def lt_xreal_def

text{*

\subsection{Algebraic structure}

*}



instance xreal :: semigroup_add
proof intro_classes
  fix a b c :: \<xreal>
  show
  "a + b + c = a + (b + c)"
    apply (insert xreal_choose_bdy2, elim disjE)
    apply (multi_cases "a::\<xreal>" "b::\<xreal>" "c::\<xreal>")
    apply (simp_all add: xreal_reduce)
    apply (multi_cases "a::\<xreal>" "b::\<xreal>" "c::\<xreal>")
    apply (simp_all add: xreal_reduce)
  done
qed

instance xreal :: ab_semigroup_add
proof intro_classes
  fix a b :: \<xreal>
  show
  "a + b = b + a"
    apply (multi_cases "a::\<xreal>" "b::\<xreal>")
    apply (simp_all add: xreal_reduce)
  done
qed

instance xreal :: semigroup_mult
proof intro_classes
  fix a b c :: \<xreal>
  show
  "a * b * c = a * (b * c)"
    apply (multi_cases "a::\<xreal>" "b::\<xreal>" "c::\<xreal>")
    apply (simp_all add: xreal_reduce mult_neg_neg
                         linorder_not_less order_le_less
                         mult_pos_neg mult_pos_neg2 mult_pos_pos)
  done
qed

instance xreal :: ab_semigroup_mult
proof intro_classes
  fix a b :: \<xreal>
  show
  "a * b = b * a"
    apply (multi_cases "a::\<xreal>" "b::\<xreal>")
    apply (simp_all add: xreal_reduce)
  done
qed

instance xreal :: comm_monoid_add
proof intro_classes
  fix a :: \<xreal>
  show
  "0 + a = a"
    apply (cases "a")
    apply (simp_all add: xreal_reduce disj_commute)
  done
qed

instance xreal :: comm_monoid_mult
proof intro_classes
  fix a :: \<xreal>
  show
  "1 * a = a"
    apply (cases "a")
    apply (simp_all add: xreal_reduce disj_commute)
  done
qed

instance xreal :: numeral ..

(*
Note that ``cancel'' classes fails because infinity wipes out all finite.
*)

lemma xreal_add_imp_eq'1:
  "\<^fin>{:x:} + b = \<^fin>{:x:} + c \<turnstile> b = c"
  apply (multi_cases "b" "c")
  apply (auto simp add: xreal_reduce disj_commute)
done

lemma xreal_add_imp_eq'2:
  "-\<^fin>{:x:} + b = -\<^fin>{:x:} + c \<turnstile> b = c"
  apply (multi_cases "b" "c")
  apply (auto simp add: xreal_reduce disj_commute)
done

lemma xreal_add_imp_eq:
  "a + b = a + c \<turnstile> a = \<zinfty> \<or> a = -\<zinfty> \<or> b = c"
  apply (multi_cases "a" "b" "c")
  apply (auto simp add: xreal_reduce disj_commute)
done

lemma xreal_add_left_cancel1 [simp]:
     "(\<^fin>{:x:} + b = \<^fin>{:x:} + c) = (b = c)"
  by (blast intro: add_ac xreal_add_imp_eq'1) 

lemma xreal_add_left_cancel2 [simp]:
     "(-\<^fin>{:x:} + b = -\<^fin>{:x:} + c) = (b = c)"
  by (blast intro: add_ac xreal_add_imp_eq'2) 

lemma xreal_add_right_cancel1 [simp]:
     "(b + \<^fin>{:x:} = c + \<^fin>{:x:}) = (b = c)"
by (simp add: add_commute [where ?b = "\<^fin>{:x:}"])

lemma xreal_add_right_cancel2 [simp]:
     "(b + -\<^fin>{:x:} = c + -\<^fin>{:x:}) = (b = c)"
by (simp add: add_commute [where ?b = "-\<^fin>{:x:}"])

(*
Also, xreal is not an abelian group under addition since the inverse fails on infinity.
*)

lemma xreal_left_minus [simp]:
  "- \<^fin>{:x:} + \<^fin>{:x:} = 0"
by (simp add: xreal_reduce disj_commute)

lemma xreal_right_minus [simp]:
  "\<^fin>{:x:} + - \<^fin>{:x:} = 0"
by (simp add: xreal_reduce disj_commute)

lemma xreal_diff_minus:
  "(a::\<xreal>) - b = a + (-b)"
by (simp add: xreal_reduce disj_commute)

lemma xreal_minus_minus [simp]:
  "- (- (a::\<xreal>)) = a"
  apply (cases "a")
  apply (simp add: xreal_reduce disj_commute)+
done

lemma xreal_minus_zero [simp]: "- 0 = (0::\<xreal>)"
by (simp add: xreal_reduce disj_commute)

lemma xreal_diff_self1 [simp]: "\<^fin>{:x:} - \<^fin>{:x:} = 0"
by (simp add: xreal_reduce disj_commute)

lemma xreal_diff_self2 [simp]: "-\<^fin>{:x:} + \<^fin>{:x:} = 0"
by (simp add: xreal_reduce disj_commute)

lemma xreal_diff_0 [simp]: "(0::\<xreal>) - a = -a"
by (simp add: xreal_diff_minus)

lemma xreal_diff_0_right [simp]: "a - (0::\<xreal>) = a" 
by (simp add: xreal_diff_minus)

lemma xreal_diff_minus_eq_add [simp]: "a - - b = a + (b::\<xreal>)"
by (simp add: xreal_diff_minus)

lemma xreal_neg_equal_iff_equal [simp]: "(-a = -b) = (a = (b::\<xreal>))" 
proof 
  assume "- a = - b"
  hence "- (- a) = - (- b)"
    by simp
  thus "a=b" by simp
next
  assume "a=b"
  thus "-a = -b" by simp
qed

lemma xreal_neg_equal_0_iff_equal [simp]: "(-a = 0) = (a = (0::\<xreal>))"
  apply (cases "a")
  apply (simp add: xreal_reduce disj_commute)+
done

lemma xreal_neg_0_equal_iff_equal [simp]: "(0 = -a) = (0 = (a::\<xreal>))"
  apply (cases "a")
  apply (simp add: xreal_reduce disj_commute)+
done

lemma xreal_minus_add_distrib1 [simp]: "- (\<^fin>{:x:} + b) = -\<^fin>{:x:} + -b"
  apply (cases "b")
  apply (simp add: xreal_reduce disj_commute)+
done

lemma xreal_minus_add_distrib2 [simp]: "- (a + \<^fin>{:y:}) = -a + -\<^fin>{:y:}"
  apply (cases "a")
  apply (simp add: xreal_reduce disj_commute)+
done

lemma xreal_minus_add_distrib3 [simp]: "- (-\<^fin>{:x:} + b) = \<^fin>{:x:} + -b"
  apply (cases "b")
  apply (simp add: xreal_reduce disj_commute)+
done

lemma xreal_minus_add_distrib4 [simp]: "- (a + -\<^fin>{:y:}) = -a + \<^fin>{:y:}"
  apply (cases "a")
  apply (simp add: xreal_reduce disj_commute)+
done

lemma xreal_minus_diff_eq1 [simp]: "- (\<^fin>{:x:} - b) = b - \<^fin>{:x:}"
  apply (cases "b")
  apply (simp add: xreal_reduce disj_commute)+
done

lemma xreal_minus_diff_eq2 [simp]: "- (a - \<^fin>{:y:}) = \<^fin>{:y:} - a"
  apply (cases "a")
  apply (simp add: xreal_reduce disj_commute)+
done

lemma xreal_minus_diff_eq3 [simp]: "- (-\<^fin>{:x:} - b) = b + \<^fin>{:x:}"
  apply (cases "b")
  apply (simp add: xreal_reduce disj_commute)+
done

lemma xreal_add_diff_eq: "a + (b - c) = (a + b) - (c::\<xreal>)"
by (simp add: xreal_diff_def add_ac)

lemma xreal_diff_add_eq: "(a - b) + c = (a + c) - (b::\<xreal>)"
by (simp add: xreal_diff_def add_ac)

lemma xreal_diff_eq_eq: "(a-\<^fin>{:x:} = c) = (a = c + \<^fin>{:x:})"
by (auto simp add: xreal_diff_def add_ac)

lemma xreal_eq_diff_eq: "(a = c-\<^fin>{:x:}) = (a + \<^fin>{:x:} = c)"
by (auto simp add: xreal_diff_def add_assoc)

lemma xreal_diff_diff_eq1a: "(a - \<^fin>{:x:}) - c = a - (\<^fin>{:x:} + c)"
by (simp add: xreal_diff_def add_ac)

lemma xreal_diff_diff_eq1b: "(a - b) - \<^fin>{:x:} = a - (b + \<^fin>{:x:})"
by (simp add: xreal_diff_def add_ac)

lemma xreal_diff_diff_eq1c: "(a - \<zinfty>) - \<zinfty> = a - (\<zinfty> + \<zinfty>)"
  apply (simp add: xreal_diff_def add_ac)
  apply (cases "a", auto simp add: xreal_reduce)
done

lemma xreal_diff_diff_eq2a: "a - (\<^fin>{:x:} - c) = (a + c) - \<^fin>{:x:}"
by (simp add: xreal_diff_def add_ac)

lemma xreal_diff_diff_eq2b: "a - (b - \<^fin>{:x:}) = (a + \<^fin>{:x:}) - b"
by (simp add: xreal_diff_def add_ac)

lemma xreal_diff_add_cancel: "a - \<^fin>{:x:} + \<^fin>{:x:} = (a::\<xreal>)"
by (simp add: xreal_diff_def add_ac)

lemma xreal_add_diff_cancel: "a + \<^fin>{:x:} - \<^fin>{:x:} = (a::\<xreal>)"
by (simp add: xreal_diff_def add_ac)

lemmas xreal_compare_rls = 
  xreal_add_diff_eq
  xreal_diff_add_eq
  xreal_diff_eq_eq
  xreal_eq_diff_eq
  xreal_diff_diff_eq1a
  xreal_diff_diff_eq1b
  xreal_diff_diff_eq1c
  xreal_diff_diff_eq2a
  xreal_diff_diff_eq2b

lemmas xreal_group_eq_simps =
  mult_ac
  add_ac
  xreal_add_diff_eq
  xreal_diff_add_eq
  xreal_diff_eq_eq
  xreal_eq_diff_eq
  xreal_diff_diff_eq1a
  xreal_diff_diff_eq1b
  xreal_diff_diff_eq1c
  xreal_diff_diff_eq2a
  xreal_diff_diff_eq2b

lemma xreal_eq_iff_diff_eq_0_1: "(a = \<^fin>{:x:}) = (a-\<^fin>{:x:} = 0)"
by (simp add: xreal_compare_rls)

lemma xreal_eq_iff_diff_eq_0_2: "(\<^fin>{:x:} = a) = (\<^fin>{:x:} - a = 0)"
  apply (cases "a")
  apply (simp_all add: xreal_reduce)
done

lemmas xreal_diff_eq_0_iff_eq =
  xreal_eq_iff_diff_eq_0_1 [symmetric]
  xreal_eq_iff_diff_eq_0_2 [symmetric]

declare xreal_diff_eq_0_iff_eq [simp]

text{*

Of course, @{text "\<xreal>"} is not a field: but we can still salvage a fair bit
of the simp rules.
*}


instance xreal :: zero_neq_one
  apply intro_classes
  apply (simp add: xreal_reduce)
done

instance xreal :: no_zero_divisors
proof intro_classes
  fix a b :: \<xreal>
  assume "a \<noteq> 0" and "b \<noteq> 0"
  then show
  "(a * b) \<noteq> 0"
    apply (multi_cases "a::\<xreal>" "b::\<xreal>")
    apply (auto simp add: xreal_reduce)
  done
qed

text{*

The semiring structure is broken by the @{text "\<zinfty> - \<zinfty>"} problem.

*}

lemma xreal_left_distrib1:
  "(\<^fin>{:x:} + b) * \<^fin>{:y:} = \<^fin>{:x:} * \<^fin>{:y:} + b * \<^fin>{:y:}"
  apply (cases "b")
  apply (auto simp add: xreal_reduce Rings.distrib)
done

lemma xreal_left_distrib2:
  "(b + \<^fin>{:x:}) * \<^fin>{:y:} = \<^fin>{:x:} * \<^fin>{:y:} + b * \<^fin>{:y:}"
  apply (cases "b")
  apply (auto simp add: xreal_reduce Rings.distrib)
done

lemma xreal_left_distrib3:
  "(\<^fin>{:x:} + \<^fin>{:y:}) * \<zinfty> = \<^fin>{:x + y:} * \<zinfty>"
by (auto simp add: xreal_reduce)

lemma xreal_left_distrib4:
  "(\<^fin>{:x:} + \<^fin>{:y:}) * -\<zinfty> = - \<^fin>{:x + y:} * \<zinfty>"
by (auto simp add: xreal_reduce)

lemma xreal_right_distrib1:
  "\<^fin>{:y:} * (\<^fin>{:x:} + b)  = \<^fin>{:y:} * \<^fin>{:x:} + \<^fin>{:y:} * b"
  apply (cases "b")
  apply (auto simp add: xreal_reduce ring_distribs)
done

lemma xreal_right_distrib2:
  "\<^fin>{:y:} * (b + \<^fin>{:x:}) = \<^fin>{:y:} * \<^fin>{:x:} + \<^fin>{:y:} * b"
  apply (cases "b")
  apply (auto simp add: xreal_reduce ring_distribs)
done

lemma xreal_right_distrib3:
  "\<zinfty> * (\<^fin>{:x:} + \<^fin>{:y:}) = \<zinfty> * \<^fin>{:x + y:}"
by (auto simp add: xreal_reduce)

lemma xreal_right_distrib4:
  "-\<zinfty> * (\<^fin>{:x:} + \<^fin>{:y:}) = -\<zinfty> * \<^fin>{:x + y:}"
by (auto simp add: xreal_reduce)

lemma xreal_left_diff_distrib1:
  "(\<^fin>{:x:} - b) * \<^fin>{:y:} = \<^fin>{:x:} * \<^fin>{:y:} - b * \<^fin>{:y:}"
  apply (cases "b")
  apply (auto simp add: xreal_reduce Rings.distrib)
done

lemma xreal_left_diff_distrib2:
  "(b - \<^fin>{:x:}) * \<^fin>{:y:} = b * \<^fin>{:y:} - \<^fin>{:x:} * \<^fin>{:y:}"
  apply (cases "b")
  apply (auto simp add: xreal_reduce Rings.distrib)
done

lemma xreal_left_diff_distrib3:
  "(\<^fin>{:x:} - \<^fin>{:y:}) * \<zinfty> = \<^fin>{:x - y:} * \<zinfty>"
by (auto simp add: xreal_reduce)

lemma xreal_left_diff_distrib4:
  "(\<^fin>{:x:} - \<^fin>{:y:}) * -\<zinfty> = - \<^fin>{:x - y:} * \<zinfty>"
by (auto simp add: xreal_reduce)

lemma xreal_right_diff_distrib1:
  "\<^fin>{:y:} * (\<^fin>{:x:} - b) = \<^fin>{:y:} * \<^fin>{:x:} - \<^fin>{:y:} * b"
  apply (cases "b")
  apply (auto simp add: xreal_reduce ring_distribs)
done

lemma xreal_right_diff_distrib2:
  "\<^fin>{:y:} * (b - \<^fin>{:x:}) = \<^fin>{:y:} * b - \<^fin>{:y:} * \<^fin>{:x:}"
  apply (cases "b")
  apply (auto simp add: xreal_reduce ring_distribs)
done

lemma xreal_right_diff_distrib3:
  "\<zinfty> * (\<^fin>{:x:} - \<^fin>{:y:}) = \<zinfty> * \<^fin>{:x - y:}"
by (auto simp add: xreal_reduce)

lemma xreal_right_diff_distrib4:
  "-\<zinfty> * (\<^fin>{:x:} - \<^fin>{:y:}) = -\<zinfty> * \<^fin>{:x - y:}"
by (auto simp add: xreal_reduce)

lemmas xreal_ring_eq_simps = xreal_group_eq_simps
  xreal_left_distrib1
  xreal_left_distrib2
  xreal_left_distrib3
  xreal_left_distrib4
  xreal_right_distrib1
  xreal_right_distrib2
  xreal_right_distrib3
  xreal_right_distrib4
  xreal_left_diff_distrib1
  xreal_left_diff_distrib2
  xreal_left_diff_distrib3
  xreal_left_diff_distrib4 
  xreal_right_diff_distrib1
  xreal_right_diff_distrib2
  xreal_right_diff_distrib3
  xreal_right_diff_distrib4 


lemma xreal_left_inverse1 [simp]:
  "x \<noteq> 0 ==> inverse \<^fin>{:x:} * \<^fin>{:x:} = 1"
by (auto simp add: xreal_reduce)

lemma xreal_left_inverse2 [simp]:
  "inverse 0 * 0 = (0::\<xreal>)"
  apply (auto simp add: xreal_reduce)
  apply (cases "(\<some> b::\<xreal> | \<True>)")
  apply (auto simp add: xreal_reduce)
done

lemma xreal_left_inverse3 [simp]:
  "inverse \<zinfty> * \<zinfty> = (0::\<xreal>)"
by (auto simp add: xreal_reduce)

lemma xreal_left_inverse4 [simp]:
  "inverse (-\<zinfty>) * (-\<zinfty>) = (0::\<xreal>)"
by (auto simp add: xreal_reduce)


lemma xreal_right_inverse1 [simp]:
  "x \<noteq> 0 ==> \<^fin>{:x:} * inverse \<^fin>{:x:} = 1"
by (auto simp add: xreal_reduce)

lemma xreal_right_inverse2 [simp]:
  "0 * inverse 0 = (0::\<xreal>)"
  apply (auto simp add: xreal_reduce)
  apply (cases "(\<some> b::\<xreal> | \<True>)")
  apply (auto simp add: xreal_reduce)
done

lemma xreal_right_inverse3 [simp]:
  "\<zinfty> * inverse \<zinfty> = (0::\<xreal>)"
by (auto simp add: xreal_reduce)

lemma xreal_right_inverse4 [simp]:
  "(-\<zinfty>) * inverse (-\<zinfty>) = (0::\<xreal>)"
by (auto simp add: xreal_reduce)

lemma xreal_mult_zero_left [simp]:
  "0 * a = (0::\<xreal>)"
  apply (cases "a")
  apply (simp add: xreal_reduce)+
done

lemma xreal_mult_zero_right [simp]:
  "a * 0 = (0::\<xreal>)"
  apply (cases "a")
  apply (simp add: xreal_reduce)+
done

lemma xreal_field_mult_eq_0_iff [simp]:
  "(a*b = (0::\<xreal>)) = (a = 0 \<or> b = 0)"
  apply (multi_cases "a" "b")
  apply (simp add: xreal_reduce)+
done


lemma xreal_minus_mult_minus [simp]:
  "(- a) * (- b) = a * (b::\<xreal>)"
  apply (multi_cases "a" "b")
  apply (simp add: xreal_reduce)+
done

text{*

\subsection{Arithmetic of infinities}

These should be gathered up into an axclass.

*}

lemma xreal_infinity_add1 [simp]:
  "\<zinfty> + \<^fin>{:x:} = \<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_infinity_add2 [simp]:
  "\<zinfty> + \<zinfty> = \<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_ninfinity_add1 [simp]:
  "-\<zinfty> + \<^fin>{:x:} = -\<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_ninfinity_add2 [simp]:
  "-\<zinfty> + -\<zinfty> = -\<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_infinity_diff1 [simp]:
  "\<zinfty> - \<^fin>{:x:} = \<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_infinity_diff2 [simp]:
  "\<^fin>{:x:} - \<zinfty> = -\<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_ninfinity_diff1 [simp]:
  "-\<zinfty> - \<^fin>{:x:} = -\<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_ninfinity_diff2 [simp]:
  "-\<zinfty> - \<zinfty> = -\<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_infinity_mult1 [simp]:
  "\<zinfty> * \<^fin>{:x:} 
  = \<if> 0 < x \<then> \<zinfty> \<else> \<if> x < 0 \<then> - \<zinfty> \<else> 0 \<fi> \<fi>"
by (simp add: xreal_reduce)

lemma xreal_infinity_mult2 [simp]:
  "\<zinfty> * -\<zinfty> = -\<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_infinity_mult3 [simp]:
  "\<zinfty> * \<zinfty> = \<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_ninfinity_mult1 [simp]:
  "-\<zinfty> * \<^fin>{:x:} 
  = \<if> 0 < x \<then> -\<zinfty> \<elif> x < 0 \<then> \<zinfty> \<else> 0 \<fi>"
by (simp add: xreal_reduce)

lemma xreal_ninfinity_mult2 [simp]:
  "-\<zinfty> * -\<zinfty> = \<zinfty>"
by (simp add: xreal_reduce)

lemma xreal_infinity_divide1 [simp]:
  "\<zinfty> / \<^fin>{:x:} 
  = \<if> 0 < x \<then> \<zinfty> \<elif> x < 0 \<then> - \<zinfty> \<else> \<zinfty> * (\<some> b | \<True>) \<fi>"
by (simp add: xreal_reduce)

lemma xreal_infinity_divide2 [simp]:
  "a / \<zinfty> = 0"
  apply (cases "a")
  apply (simp_all add: xreal_reduce)
done

lemma xreal_ninfinity_divide1 [simp]:
  "-\<zinfty> / \<^fin>{:x:} 
  = \<if> 0 < x \<then> -\<zinfty> \<elif> x < 0 \<then> \<zinfty> \<else> -\<zinfty> * (\<some> b | \<True>) \<fi>"
by (simp add: xreal_reduce)

lemma xreal_ninfinity_divide2 [simp]:
  "a / -\<zinfty> = 0"
  apply (cases "a")
  apply (simp_all add: xreal_reduce)
done

lemma xreal_zero_divide [simp]:
  "(0::\<xreal>) / a = 0"
  apply (cases "a")
  apply (simp_all add: xreal_reduce)
  apply (cases "(\<some> (b::\<xreal>) | \<True>)")
  apply (simp_all add: xreal_reduce)
done

text{*

Several of these may be superseded by the following simp rules.  
The simp set should be adjusted if these become problematic.

*}

lemma xreal_finite_arithmetic_reduce [simp]:
  "\<^fin>{:x:} + \<^fin>{:y:} = \<^fin>{:x + y:}"
  "\<^fin>{:x:} - \<^fin>{:y:} = \<^fin>{:x - y:}"
  "\<^fin>{:x:} * \<^fin>{:y:} = \<^fin>{:x * y:}"
  "\<^fin>{:x:} / \<^fin>{:y:} = \<^fin>{:x:} * inverse \<^fin>{:y:}"
  "inverse \<^fin>{:y:} = \<if> y \<noteq> 0 \<then> \<^fin>{:inverse y:} \<else> (\<some> b | \<True>) \<fi>"
  "\<^fin>{:0:} + a = a"
  "a + \<^fin>{:0:} = a"
  "\<^fin>{:0:} * a = \<^fin>{:0:}"
  "a * \<^fin>{:0:} = \<^fin>{:0:}"
  "\<^fin>{:0:}/a = \<^fin>{:0:}"
  "\<^fin>{:1:} * a = a"
  "a * \<^fin>{:1:} = a"
  apply (auto simp add: xreal_reduce)
  apply (cases "a",
         auto simp add: xreal_reduce)
  apply (cases "a",
         auto simp add: xreal_reduce)
  apply (cases "a",
         auto simp add: xreal_reduce)
  apply (cases "a",
         auto simp add: xreal_reduce)
  apply (multi_cases "a" "(\<some> (b::\<xreal>) | \<True>)",
         auto simp add: xreal_reduce)
  apply (cases "a",
         auto simp add: xreal_reduce)
  apply (cases "a",
         auto simp add: xreal_reduce)
done


(*
Note that arithmetic of the inifinities themselves is already included in xReal\_Type.thy.  Maybe
rationalise these.
*)

lemma xreal_infinite_arithmetic [simp]:
  "\<^fin>{:x:} + (\<zinfty> + -\<zinfty>) = (\<zinfty> + -\<zinfty>)"
  "\<^fin>{:x:} - (\<zinfty> + -\<zinfty>) = - (\<zinfty> + -\<zinfty>)"
  "\<^fin>{:x:}/ (\<zinfty> + -\<zinfty>) = 0"
  "\<^fin>{:x:} * (\<zinfty> + -\<zinfty>) = \<if> 0 < x \<then> (\<zinfty> + -\<zinfty>) \<else> \<if> x < 0 \<then> - (\<zinfty> + -\<zinfty>) \<else> 0 \<fi> \<fi>"
  "(\<zinfty> + -\<zinfty>) + \<^fin>{:x:} = (\<zinfty> + -\<zinfty>)"
  "(\<zinfty> + -\<zinfty>) - \<^fin>{:x:} = (\<zinfty> + -\<zinfty>)"
  "(\<zinfty> + -\<zinfty>) / \<^fin>{:x:} = (\<zinfty> + -\<zinfty>) * (inverse \<^fin>{:x:})"
  "(\<zinfty> + -\<zinfty>) * \<^fin>{:x:} = \<if> 0 < x \<then> (\<zinfty> + -\<zinfty>) \<else> \<if> x < 0 \<then> - (\<zinfty> + -\<zinfty>) \<else> 0 \<fi> \<fi>"
  "(\<zinfty> + -\<zinfty>) + (\<zinfty> + -\<zinfty>) = (\<zinfty> + -\<zinfty>)"
  "(\<zinfty> + -\<zinfty>) - (\<zinfty> + -\<zinfty>) = (\<zinfty> + -\<zinfty>)"
  "(\<zinfty> + -\<zinfty>) / (\<zinfty> + -\<zinfty>) = 0"

  "\<zinfty> + (\<zinfty> + -\<zinfty>)  = (\<zinfty> + -\<zinfty>)"
  "-\<zinfty> + (\<zinfty> + -\<zinfty>) = (\<zinfty> + -\<zinfty>)"

  "(\<zinfty> + -\<zinfty>) + \<zinfty> = (\<zinfty> + -\<zinfty>)"
  "(\<zinfty> + -\<zinfty>) + -\<zinfty> = (\<zinfty> + -\<zinfty>)"
  "(\<zinfty> + -\<zinfty>) - \<zinfty> = (\<zinfty> + -\<zinfty>)"
  "(\<zinfty> + -\<zinfty>) / (\<zinfty> + -\<zinfty>) = 0"
  "(\<zinfty> + -\<zinfty>) / \<zinfty> = 0"
  "(\<zinfty> + -\<zinfty>) / -\<zinfty> = 0"
  "\<zinfty> / (\<zinfty> + -\<zinfty>) = 0"
  "-\<zinfty> / (\<zinfty> + -\<zinfty>) = 0"
  "inverse (\<zinfty> + -\<zinfty>) = 0"
  "inverse \<zinfty> = 0"
  "inverse -\<zinfty> = 0"
  apply (insert xreal_choose_bdy2, elim disjE)
  apply (auto simp add: xreal_reduce)
done

(*
lemma xreal_infinite_arithmetic_reduce [simp]:
  "a + (\<zinfty> + -\<zinfty>) = (\<zinfty> + -\<zinfty>)"
  "\<^fin>{:x:} - (\<zinfty> + -\<zinfty>) = - (\<zinfty> + -\<zinfty>)"
  "a / (\<zinfty> + -\<zinfty>) = 0"
  "a / \<zinfty> = 0"
  "a / -\<zinfty> = 0"
  "\<^fin>{:x:} * (\<zinfty> + -\<zinfty>) = \<if> 0 < x \<then> (\<zinfty> + -\<zinfty>) \<else> \<if> x < 0 \<then> - (\<zinfty> + -\<zinfty>) \<else> 0 \<fi> \<fi>"
  "(\<zinfty> + -\<zinfty>) + a = (\<zinfty> + -\<zinfty>)"
  "(\<zinfty> + -\<zinfty>) - a = (\<zinfty> + -\<zinfty>)"
  "(\<zinfty> + -\<zinfty>) /  a = (\<zinfty> + -\<zinfty>) * (inverse a)"
  "(\<zinfty> + -\<zinfty>) * \<^fin>{:x:} = \<if> 0 < x \<then> (\<zinfty> + -\<zinfty>) \<else> \<if> x < 0 \<then> - (\<zinfty> + -\<zinfty>) \<else> 0 \<fi> \<fi>"
  "inverse (\<zinfty> + -\<zinfty>) = 0"
  "inverse \<zinfty> = 0"
  "inverse -\<zinfty> = 0"
  apply (insert xreal_choose_bdy, elim disjE)
  apply (cases "a",
         auto simp add: xreal_reduce)+
done;
*)

text{*

Finally, the following may be more useful in its removal!  (I.e., as 
@{text "ninfty_reduce [THEN sym]"}!

*}

lemma ninfty_reduce:
  "-\<zinfty> = - \<zinfty>"
by (simp add: xreal_reduce)

text{*

\section{Embedding in the extended reals}

*}

consts
   (* overloaded constant for injecting other types into "xreal" *)
   xreal :: "'a => \<xreal>" ("\<xreal>")



instance xreal :: ordered_ab_semigroup_add
proof intro_classes
  fix a b c :: \<xreal>
  assume Aa1: "a \<le> b"
  then show
  "c + a \<le> c + b"
    apply (multi_cases "a::\<xreal>" "b::\<xreal>" c "(\<some> a | a = \<zinfty> \<or> a = -\<zinfty>)" "(\<some> a | a = -\<zinfty> \<or> a = \<zinfty>)")
    apply (simp_all add: xreal_reduce le_xreal_def)
  done
qed


lemma xreal_neg_le_iff_le: "- (b::\<xreal>) \<le> - a \<Leftrightarrow> a \<le> b"
  apply (multi_cases "a::\<xreal>" "b::\<xreal>" "(\<some> a | a = \<zinfty> \<or> a = -\<zinfty>)")
  apply (simp_all add: xreal_reduce le_xreal_def) 
done

lemma xreal_neg_le_0_iff_le [simp]: "- (a::\<xreal>) \<le> 0 \<Leftrightarrow> 0 \<le> a"
by (subst xreal_neg_le_iff_le [symmetric], simp)

lemma xreal_neg_0_le_iff_le [simp]: "0 \<le> - (a::\<xreal>) \<Leftrightarrow> a \<le> 0"
by (subst xreal_neg_le_iff_le [symmetric], simp)

lemma xreal_neg_less_iff_less [simp]: "- b < - (a::\<xreal>) \<Leftrightarrow> a < b"
  apply (multi_cases "a::\<xreal>" "b::\<xreal>" "(\<some> a | a = \<zinfty> \<or> a = -\<zinfty>)")
  apply (simp_all add: xreal_reduce) 
  apply auto
done

lemma xreal_neg_less_0_iff_less [simp]: "- (a::\<xreal>) < 0 \<Leftrightarrow> 0 < a"
by (subst xreal_neg_less_iff_less [symmetric], simp)

lemma xreal_neg_0_less_iff_less [simp]: "0 < - (a::\<xreal>) \<Leftrightarrow> a < 0"
by (subst xreal_neg_less_iff_less [symmetric], simp)


text {* 
\section{Embedding into the reals}

We use the induced metric via mapping through ``arctan'' 
This is put here just to keep everything together.

*}

defs (overloaded)
  real_of_xreal_def: "real x \<defs>
    \<case> x \<of>
      -\<zinfty> \<longrightarrow> -1
    | \<^fin>{:a:} \<longrightarrow> a/(1 + (abs a))
    | \<zinfty> \<longrightarrow> 1
    \<esac>"


lemma real_of_xreal_zero [simp]: "real (0::\<xreal>) = 0"  
by (simp add: real_of_xreal_def xreal_zero_def) 

lemma real_of_xreal_one [simp]: "real (1::\<xreal>) = (1/2::real)"
by (simp add: real_of_xreal_def xreal_one_def) 

lemma real_of_xreal_minus [simp]: "real(-x) = -real (x::\<xreal>)"
  apply (simp add: real_of_xreal_def) 
  apply (cases "x", auto simp add: xreal_reduce)
done


lemma real_of_xreal_inject [iff]: "(real (x::\<xreal>) = real y) = (x = y)"
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
    apply (simp add: real_of_xreal_def) 
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




lemma xreal_All:
  "(\<forall> (x::\<xreal>) \<bullet> P x) = ((P -\<zinfty>) \<and> (\<forall> r \<bullet> P \<^fin>{:r:}) \<and> (P \<zinfty>))"
proof auto
  fix x :: \<xreal>
  assume "(P -\<zinfty>)" and "(\<forall> r \<bullet> P \<^fin>{:r:})" and "(P \<zinfty>)"
  then show "P x" by (cases x, auto)
qed

lemma xreal_Ex:
  "(\<exists> (x::\<xreal>) \<bullet> P x) = ((P -\<zinfty>) \<or> (\<exists> r \<bullet> P \<^fin>{:r:}) \<or> (P \<zinfty>))"
proof auto
  apply_end (rule contrapos_pp, assumption, thin_tac "?P", simp)
  fix x :: \<xreal> and r :: \<real>
  assume "\<not> (P -\<zinfty>)" and "(\<forall> r \<bullet> \<not> (P \<^fin>{:r:}))" and "\<not> (P \<zinfty>)"
  then show "\<not> (P x)" by (cases x, auto)
qed

lemma real_of_xreal_mono:
  "(a::\<xreal>) \<le> b \<turnstile> real a \<le> real b"
proof-
  assume Aa1: "a \<le> b"
  {
  fix r :: \<real>
  have "abs r \<le> 1 + abs r"
  by auto
  }
  note R1 = this
  from Aa1 show ?thesis
    apply (multi_cases "a" "b")
    apply (auto simp add: real_of_xreal_def le_xreal_def)
    apply (subst pos_le_divide_eq, simp add: abs_if, simp add: abs_if)
    apply (subst pos_le_divide_eq) 
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
Lattice structure

*}



instantiation
  xreal :: linlat
begin

definition
  inf_xreal_def: "oinf \<defs> (\<olambda> (x::\<xreal>) y \<bullet> \<if> x \<le> y \<then> x \<else> y \<fi>)"

definition
  sup_xreal_def: "osup \<defs> (\<olambda> (x::\<xreal>) y \<bullet> \<if> x \<le> y \<then> y \<else> x \<fi>)"

instance
  apply (intro_classes)
  apply (simp_all add: inf_xreal_def sup_xreal_def)
  done

end

interpretation lattice_xreal: Lattice_Locale.lattice "\<univ>-[\<xreal>]" "op \<le>"
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
    apply (rule order_class.lub_unique [of S], assumption+)
  done
qed

theorem real_ex_Inf': 
  assumes A1: "(S::real set) \<noteq> \<emptyset>"
  assumes A2: "\<^lbp>{:\<univ>-[\<real>]:}{:op \<le>:} S u"
  shows
    "\<exists>\<subone> Inf \<bullet> \<^glbp>{:\<univ>-[\<real>]:}{:op \<le>:} S Inf"
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


lemma xreal_ex_Sup': 
  assumes A1: "(S::xreal set) \<noteq> \<emptyset>"
  shows
    "\<exists>\<subone> Sup \<bullet> \<^lubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} S Sup"
  apply (cases "\<exists> (r::\<real>) \<bullet> \<^ubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} S \<^fin>{:r:}")
  apply (cases "S = {-\<zinfty>}", (msafe_no_assms(inference)))
proof-  
  fix r :: \<real>
  assume Aa1: "S = {-\<zinfty>}"
  then have
  "\<^lubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} S -\<zinfty>"
  by (auto simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
  then show ?thesis
    apply (intro ex1I, assumption)
    apply (rule order_classD [THEN partial_order.lub_unique, of S], assumption+)
  done
next
  fix r :: \<real>
  assume Aa1: "S \<noteq> {-\<zinfty>}"
  assume Aa2: "\<^ubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} S \<^fin>{:r:}"

  let ?S' = "{r' | \<^fin>{:r':} \<in> S}"
(*
  from A1 Aa1 Aa2 have
  "\<forall> x | x \<in> S - {-\<zinfty>} \<bullet> (\<exists> (r'::\<real>) \<bullet> x = \<^fin>{:r':})"
    apply (simp only: xreal_All, (msafe_no_assms(inference)))
    apply (simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (intro exI, simp)
    apply (simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (elim allE [where ?x = "\<zinfty>"], simp add: xreal_reduce)
  done
*)
  from Aa2 have Ra0:
  "\<zinfty> \<notin> S"
    apply (simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (simp only: xreal_All, (msafe_no_assms(inference)))
    apply (simp add: xreal_reduce)
  done

  from A1 Aa1 Ra0 have Ra1:
  "S - {-\<zinfty>} = fin \<lparr>?S'\<rparr>"  
    apply (subst set_eq_def)
    apply (simp add: xreal_All, (msafe_no_assms(inference)))
    apply (simp_all add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (simp_all add: xreal_reduce image_def)
  done
  have Ra2:
  "\<^ubp>{:\<univ>-[\<real>]:}{:op \<le>:} ?S' r"
    apply (simp_all add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (subst fin_order_embed)
    apply (msafe_no_assms(inference), intro Aa2 [THEN order_class.is_ubD], assumption)
  done
  from A1 Aa1 Ra0 have Ra3:
  "?S' \<noteq> \<emptyset>"
    apply auto
    apply (simp_all only: atomize_all atomize_imp)
    apply (simp_all only: xreal_All xreal_Ex, (msafe_no_assms(inference)))
    apply (simp_all add: image_def xreal_reduce)
  done
  from Ra2 Ra3 have "\<exists>\<subone> Sup \<bullet> \<^lubp>{:\<univ>-[\<real>]:}{:op \<le>:} ?S' Sup" 
  by (intro real_ex_Sup', simp_all)
  then obtain Sup where real_lub: "\<^lubp>{:\<univ>-[\<real>]:}{:op \<le>:} ?S' Sup" 
  by (auto)
  have
  "\<^lubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} (fin \<lparr>?S'\<rparr>) \<^fin>{:Sup:}"
    apply (rule order_class.is_lubI, simp_all add: image_def)
    apply (auto simp add: le_xreal_def)
    apply (rule real_lub [THEN order_class.is_lubD1, THEN order_class.is_ubD])
    apply (simp_all only: atomize_all atomize_imp)
    apply (simp_all only: xreal_All xreal_Ex, (msafe_no_assms(inference)))
    apply (simp_all add: xreal_reduce)
    apply (insert Ra3, simp add: image_def)
    apply (rule real_lub [THEN order_class.is_lubD2'])
    apply (simp_all)
  done
  then have
  "\<^lubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} S \<^fin>{:Sup:}"
    apply (simp add: Ra1 [THEN sym])
    apply (simp add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def)
    apply (simp_all only: xreal_All xreal_Ex, (msafe_no_assms(inference)))
    apply (simp_all add: xreal_reduce)
  done
  then show ?thesis
    apply (intro ex1I, assumption)
    apply (rule order_class.lub_unique, simp_all) 
  done
next
  apply_end simp
  assume Aa1: "\<forall> r \<bullet> \<not> (\<^ubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} S \<^fin>{:r:})"
  then have
  "\<^lubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} S \<zinfty>"
    apply (cases "\<zinfty> \<in> S")
    apply (simp_all add: isLub_def isUb_def leastP_def setle_def setge_def is_lub_def is_least_def is_ub_def le_xreal_simps not_le)
    apply (msafe_no_assms(inference))
  proof -
    assume 
      c1: "\<zinfty> \<notin> S"
    fix x
    assume
      c2: "(\<forall> r \<bullet> (\<exists> y \<bullet> y \<in> S \<and> fin r < y))" and
      c3: "(\<forall> y \<bullet> y \<in> S \<Rightarrow> y \<le> x)"
    from c3 show
      "\<zinfty> \<le> x"
      apply (cases x)
      apply (simp_all)
    proof -
      assume 
        d1: "(\<forall> y \<bullet> y \<in> S \<Rightarrow> y \<le> -\<zinfty>)"
      from c2 [rule_format, of "0"] obtain y where
        d2: "y \<in> S" and d3: "fin 0 < y"
        by (auto)
      from d3 have 
        d4: "y \<noteq> -\<zinfty>"
        by (auto simp add: le_xreal_simps)
      from d2 d1 have 
        d4': "y \<le> -\<zinfty>"
        by (auto)
      from d4 d4' show
        "\<zinfty> \<le> -\<zinfty>"
        apply (cases y)
        apply (auto simp add: le_xreal_simps)
        done
    next
      fix r
      assume 
        d1: "(\<forall> y \<bullet> y \<in> S \<Rightarrow> y \<le> fin r)"
      from c2 [rule_format, of "r"] obtain y where
        d2: "y \<in> S" and d3: "fin r < y"
        by (auto)
      with d1 show 
        "\<zinfty> \<le> fin r"
        by (auto simp add: le_xreal_simps)
    qed
  qed
  then show ?thesis
    apply (intro ex1I, assumption)
    apply (rule order_class.lub_unique, simp_all) 
  done
qed

theorem xreal_ex_Inf': 
  assumes A1: "(S::xreal set) \<noteq> \<emptyset>"
  shows
    "\<exists>\<subone> Inf \<bullet> \<^glbp>{:\<univ>-[\<xreal>]:}{:op \<le>:} S Inf"
proof -
  let ?SM = "uminus \<lparr>S\<rparr>"
  from A1 have "?SM \<noteq> \<emptyset>"
  by (auto simp add: image_def)
  from this [THEN xreal_ex_Sup'] obtain Sup where Sup_ext:
  "\<^lubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} ?SM Sup" 
  by auto
  have
  "\<^glbp>{:\<univ>-[\<xreal>]:}{:op \<le>:} S (-Sup)"
    apply (simp add: is_glb_def is_lb_def is_greatest_def del: le_xreal_def)
    apply (msafe_no_assms(inference))
  proof-
    fix x
    assume Aa1: "x \<in> S"
    then have "-x \<le> Sup" by (intro Sup_ext [THEN order_class.is_lubD1'], simp)
    then show "- Sup \<le> x" by (subst xreal_neg_le_iff_le [THEN sym], subst xreal_minus_minus)
  next
    fix x
    assume Aa1: "\<forall> y \<bullet> y \<in> S \<Rightarrow> x \<le> y"
    then have Ra1: 
    "\<forall> y \<bullet> y \<in> uminus\<lparr>S\<rparr> \<Rightarrow> y \<le> -x"
    by (subst xreal_neg_le_iff_le [THEN sym], subst xreal_minus_minus, auto)
    then have "Sup \<le> -x" by (intro Sup_ext [THEN order_class.is_lubD2'], auto)
    then show "x \<le> - Sup" by (subst xreal_neg_le_iff_le [THEN sym], subst xreal_minus_minus)
  qed
  then show ?thesis
    apply (intro ex1I, assumption)
    apply (rule order_classD [THEN partial_order.glb_unique], assumption+)
  done
qed

theorem xreal_clattice:
"\<^clattice>{:\<univ>-[\<xreal>]:}{:op \<le>:}"
proof (rule order_classD [THEN partial_order.clatticeI])
  fix X :: "\<xreal> set"
  assume A2: "X \<subseteq> \<univ>-[\<xreal>]"
  show
  "\<exists> z \<bullet> \<^glbp>{:\<univ>-[\<xreal>]:}{:op \<le>:} X z"
  proof (cases "X = \<emptyset>")
    assume A11: "X = \<emptyset>"
    from A2 A11 show ?thesis
      apply (auto simp add: is_glb_def is_lb_def is_greatest_def)
      apply (witness "\<zinfty>")
      apply (simp only: xreal_All xreal_Ex, (msafe_no_assms(inference)))
      apply (auto simp add: xreal_reduce)
    done
  next
    assume A11: "X \<noteq> \<emptyset>"
    then have
    "\<exists>\<subone> Inf \<bullet> \<^glbp>{:\<univ>-[\<xreal>]:}{:op \<le>:} X Inf"
    by (intro xreal_ex_Inf', simp)
    then show
    "\<exists> Inf \<bullet> \<^glbp>{:\<univ>-[\<xreal>]:}{:op \<le>:} X Inf"
    by auto
  qed
next
  fix X :: "\<xreal> set"
  assume A2: "X \<subseteq> \<univ>-[\<xreal>]"
  show
  "\<exists> z \<bullet> \<^lubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} X z"
  proof (cases "X = \<emptyset>")
    assume A11: "X = \<emptyset>"
    from A2 A11 show ?thesis
      apply (auto simp add: is_lub_def is_ub_def is_least_def)
      apply (witness "-\<zinfty>")
      apply (simp only: xreal_All xreal_Ex, (msafe_no_assms(inference)))
      apply (auto simp add: xreal_reduce)
    done
  next
    assume A11: "X \<noteq> \<emptyset>"
    then have
    "\<exists>\<subone> Sup \<bullet> \<^lubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} X Sup"
    by (intro xreal_ex_Sup', simp)
    then show
    "\<exists> Sup \<bullet> \<^lubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} X Sup"
    by auto
  qed
qed

theorem xreal_interval_clattice:
    "(a::\<xreal>) \<le> b 
    \<turnstile> \<^clattice>{:\<lclose>a\<dots>b\<rclose>:}{:\<^subord>{:op \<le>:}{:\<lclose>a\<dots>b\<rclose>:}:}"
proof-
  assume A1: "a \<le> b"
  from A1 interpret 
    po_interval: partial_order "\<lclose>a\<dots>b\<rclose>" "\<^subord>{:op \<le>:}{:\<lclose>a\<dots>b\<rclose>:}"
    apply (fold default_order_def)
    apply (rule default_po)
    apply (auto simp only: interval_defs)
    done
  show ?thesis
  proof (rule po_interval.clatticeI)
    fix 
      X :: "\<xreal> set"
    assume 
      A2: "X \<subseteq> \<lclose>a\<dots>b\<rclose>"
    show
        "(\<exists> z \<bullet> \<^glbp>{:\<lclose>a\<dots>b\<rclose>:}{:\<^subord>{:op \<le>:}{:\<lclose>a\<dots>b\<rclose>:}:} X z)"
    proof (cases "X = \<emptyset>")
      assume 
        A11: "X = \<emptyset>"
      from A1 A2 A11 show 
          ?thesis
        apply (auto simp only: is_glb_def is_lb_def is_greatest_def)
        apply (auto simp only: interval_defs subset_order_def op2rel_def rel2op_def)
        apply (auto simp add: eind_def)
        done
    next
      assume 
        A11: "X \<noteq> \<emptyset>"
      from A11 obtain x where 
        R0': "x \<in> X" 
        by auto
      from A1 A2 A11 have 
          "(\<exists>\<subone> Inf \<bullet> \<^glbp>{:\<univ>-[\<xreal>]:}{:op \<le>:} X Inf)"
        by (intro xreal_ex_Inf',simp)
      then obtain Inf where 
        R1': "(\<forall> x | x \<in> X \<bullet> Inf \<le> x) \<and> (\<forall> l | (\<forall> x | x \<in> X \<bullet> l \<le> x) \<bullet> l \<le> Inf)" 
        by (auto simp add: is_lb_def is_glb_def is_greatest_def)
      from R1' have 
        R2a: "\<forall> x | x \<in> X \<bullet> Inf \<le> x"
        by (auto)
      from R1' have 
        R2b: "(\<forall> l | (\<forall> x | x \<in> X \<bullet> l \<le> x) \<bullet> l \<le> Inf)"
        by (auto)
      have 
        R2c: "Inf \<in> \<lclose>a\<dots>b\<rclose>"
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
          by (intro R2b [rule_format], auto simp add: interval_defs)
      qed
      from A1 A2 R2c show 
          ?thesis
        apply (intro exI [where ?x = "Inf"])
        apply (auto simp add: is_glb_def is_lb_def is_greatest_def)
        apply (auto simp add: subset_order_def op2rel_def rel2op_def subset_def)
        apply (intro R2a [rule_format])
        apply (auto)
        apply (intro R2b [rule_format])
        apply (auto)
        done
    qed
  next
    fix 
      X :: "\<xreal> set"
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
          "(\<exists>\<subone> Sup \<bullet> \<^lubp>{:\<univ>-[\<xreal>]:}{:op \<le>:} X Sup)"
        by (intro xreal_ex_Sup',simp)
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




text {* The extended real numbers are an instance of metric. *}

instantiation xreal :: metric
begin

definition
  distance_xreal_def:  "\<^mcdist>{:x::\<xreal>:}{:y:} \<defs> abs ((real x) - (real y))"

instance 
  apply (intro_classes)
  apply (simp add: distance_xreal_def | (msafe_no_assms(inference)))+
  done

end


end
