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

header {* Some useful operators for calculational reasoning *}

theory 
  xHOL_Defs

imports 
  xHOL_Defs_Chap

begin

section {* Chained relations *}

text {*

We introduce syntax to aid in writing chained relation terms.

A chained relation is a conjunction of binary relations in which conjunctions and repeated
arguments and relations are elided for compactness of representation.

For example, the term 
@{text [display] "    a = b \<and> b \<le> c \<and> b \<le> d"} 
might be written in the following form
@{text [display] "    \<lch>a \<chEq> b \<chLe> c, d\<rch>."}

*}

definition
  ch_tail :: "'a set \<rightarrow> ('a set \<times> ('a \<rightarrow> \<bool>))"
where 
  ch_tail_def [simp]: "ch_tail \<defs> (\<olambda> As \<bullet> (As, (\<olambda> a \<bullet> \<True>)))"

definition
  ch_cons :: "['a set, ['a, 'b] \<rightarrow> \<bool>, ('b set \<times> ('b \<rightarrow> \<bool>))] \<rightarrow> ('a set \<times> ('a \<rightarrow> \<bool>))"
where 
  ch_cons_def: "ch_cons \<defs> (\<olambda> As r (Bs, BS_phi) \<bullet> (As, (\<olambda> a \<bullet> (\<forall> b | b \<in> Bs \<bullet> r a b \<and> BS_phi b))))"

definition
  ch_head :: "('a set \<times> ('a \<rightarrow> \<bool>)) \<rightarrow> \<bool>"
where 
  ch_head_def: "ch_head \<defs> (\<olambda> (As, BS_phi) \<bullet> (\<forall> a | a \<in> As \<bullet> BS_phi a))"

definition
  ch_acc :: "['a set, ['a, 'b] \<rightarrow> \<bool>, ('b set \<times> ('b \<rightarrow> \<bool>))] \<rightarrow> ('a \<rightarrow> \<bool>)"
where
  ch_acc_def: "ch_acc \<defs> (\<olambda> a r (Bs, BS_phi) a \<bullet> (\<forall> b | b \<in> Bs \<bullet> r a b \<and> BS_phi b))"

lemma ch_cons_acc [simp]:
  "ch_cons As r (Bs, BS_phi) = (As, ch_acc As r (Bs, BS_phi))"
  by (simp add: ch_cons_def ch_acc_def)

lemma ch_acc_ins [simp]:
  "ch_acc As r (insert b BS, BS_phi) = (\<olambda> a \<bullet> r a b \<and> BS_phi b \<and> ch_acc As r (BS, BS_phi) a)"
  by (auto intro!: ext simp add: ch_acc_def)

lemma ch_acc_nil [simp]:
  "ch_acc As r (\<emptyset>, BS_phi) = (\<olambda> a \<bullet> \<True>)"
  by (auto intro!: ext simp add: ch_acc_def)

lemma ch_head_ins [simp]: 
  "ch_head (insert a As, BS_phi) \<Leftrightarrow> BS_phi a \<and> ch_head (As, BS_phi)"
  by (auto simp add: ch_head_def)

lemma ch_head_nil [simp]: 
  "ch_head (\<emptyset>, BS_phi) \<Leftrightarrow> \<True>"
  by (auto simp add: ch_head_def)

nonterminal
  chainrel and
  chainelt

syntax (xsymbols output)
  "_xHOL_Defs\<ZZ>ch_true" :: "chainrel \<rightarrow> \<bool>" ("_")
  "_xHOL_Defs\<ZZ>ch_base" :: "args \<rightarrow> chainelt" ("_")

syntax (zed)
  "_xHOL_Defs\<ZZ>ch_true" :: "chainrel \<rightarrow> \<bool>" ("\<lch>_")
  "" :: "chainrel \<rightarrow> chainelt" ("_")
  "_xHOL_Defs\<ZZ>ch_base" :: "args \<rightarrow> chainelt" ("_\<rch>")

parse_translation {*

let

fun set_tr (Const("_args", _) $ a $ As) = Const("insert", dummyT) $ a $ set_tr As
  | set_tr a = Const("insert", dummyT) $ a $ Const("Set.empty", dummyT);

fun chTrue_tr _ [X] = Const(@{const_syntax "ch_head"}, dummyT) $ X;

fun chBase_tr _ [As] = Const(@{const_syntax "ch_tail"}, dummyT) $ (set_tr As);

in

[
  ("_xHOL_Defs\<ZZ>ch_true", chTrue_tr),
  ("_xHOL_Defs\<ZZ>ch_base", chBase_tr)
]

end;

*}

definition
  ch_eq :: "['a, 'a] \<rightarrow> \<bool>"
where
  ch_eq_def [simp]: "ch_eq x y \<defs> x = y"

definition
  ch_iff :: "[\<bool>, \<bool>] \<rightarrow> \<bool>"
where
  ch_iff_def [simp]: "ch_iff x y \<defs> x \<Leftrightarrow> y"

definition
  ch_neq :: "['a, 'a] \<rightarrow> \<bool>"
where
  ch_neq_def [simp]: "ch_neq x y \<defs> x \<noteq> y"

definition
  ch_le :: "['a::ord, 'a] \<rightarrow> \<bool>"
where
  ch_le_def [simp]: "ch_le x y \<defs> x \<le> y"

definition
  ch_lt :: "['a::ord, 'a] \<rightarrow> \<bool>"
where
  ch_lt_def [simp]: "ch_lt x y \<defs> x < y"

definition
  ch_subeq :: "['a set, 'a set] \<rightarrow> \<bool>"
where
  ch_subeq_def [simp]: "ch_subeq x y \<defs> x \<subseteq> y"

definition
  ch_sub :: "['a set, 'a set] \<rightarrow> \<bool>"
where
  ch_sub_def [simp]: "ch_sub x y \<defs> x \<subset> y"

definition
  ch_imp :: "[\<bool>, \<bool>] \<rightarrow> \<bool>"
where
  ch_imp_def [simp]: "ch_imp x y \<defs> x \<Rightarrow> y"

definition
  ch_in :: "['a, 'a set] \<rightarrow> \<bool>"
where
  ch_in_def [simp]: "ch_in x y \<defs> x \<in> y"

syntax (xsymbols output)
  "_xHOL_Defs\<ZZ>ch_eq" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "=" 50)
  "_xHOL_Defs\<ZZ>ch_iff" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<Leftrightarrow>" 50)
  "_xHOL_Defs\<ZZ>ch_neq" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<noteq>" 50)
  "_xHOL_Defs\<ZZ>ch_le" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<le>" 50)
  "_xHOL_Defs\<ZZ>ch_lt" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "<" 50)
  "_xHOL_Defs\<ZZ>ch_subeq" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<subseteq>" 50)
  "_xHOL_Defs\<ZZ>ch_sub" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<subset>" 50)
  "_xHOL_Defs\<ZZ>ch_imp" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<Rightarrow>" 50)
  "_xHOL_Defs\<ZZ>ch_in" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<in>" 50)

syntax (zed)
  "_xHOL_Defs\<ZZ>ch_eq" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chEq>" 50)
  "_xHOL_Defs\<ZZ>ch_iff" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chIff>" 50)
  "_xHOL_Defs\<ZZ>ch_neq" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chNeq>" 50)
  "_xHOL_Defs\<ZZ>ch_le" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chLe>" 50)
  "_xHOL_Defs\<ZZ>ch_lt" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chLt>" 50)
  "_xHOL_Defs\<ZZ>ch_subeq" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chSubseteq>" 50)
  "_xHOL_Defs\<ZZ>ch_sub" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chSubset>" 50)
  "_xHOL_Defs\<ZZ>ch_imp" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chImp>" 50)
  "_xHOL_Defs\<ZZ>ch_in" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chIn>" 50)

ML {*


local 

fun set_tr (Const("_args", _) $ a $ As) = Const("insert", dummyT) $ a $ set_tr As
  | set_tr a = Const("insert", dummyT) $ a $ Const("Set.empty", dummyT);

fun mk_simpOp th r = Const("\<^const>"^th^"."^r, dummyT);

in

fun chNode_tr th r = ("_"^th^"\<ZZ>"^r, (fn _ => (fn [As, X] => Const(@{const_syntax "ch_cons"}, dummyT) $ (set_tr As) $ (mk_simpOp th r) $ X)));

end;

*}

parse_translation {*

[chNode_tr "xHOL_Defs" "ch_eq", chNode_tr "xHOL_Defs" "ch_iff", chNode_tr "xHOL_Defs" "ch_neq", chNode_tr "xHOL_Defs" "ch_lt", chNode_tr "xHOL_Defs" "ch_le", chNode_tr "xHOL_Defs" "ch_subeq", chNode_tr "xHOL_Defs" "ch_sub", chNode_tr "xHOL_Defs" "ch_imp", chNode_tr "xHOL_Defs" "ch_in"]

*}

ML {*

local

fun args_of (Const(@{const_syntax "Set.insert"}, _) $ a $ Const(@{const_syntax "Set.empty"}, _)) = a
  | args_of (Const(@{const_syntax "Set.insert"}, _) $ a $ As) = Const("_args", dummyT) $ a $ (args_of As);

in

fun simpOp_tr' R [] = Const(R, dummyT);

fun ch_head_tr' _ [X] = Const("_xHOL_Defs\<ZZ>ch_true", dummyT) $ X;

fun ch_cons_tr' _ [As, r, X] = (r) $ (args_of As) $ X;

fun ch_tail_tr' _ [As] = Const("_xHOL_Defs\<ZZ>ch_base", dummyT) $ (args_of As);

fun chNode_tr' th s = ("\<^const>"^th^"."^s, (fn _ => fn t => funap_tr (Const("_"^th^"\<ZZ>"^s, dummyT)) t));

end;

*}

print_translation {*

[ 
  (@{const_syntax "ch_head"}, ch_head_tr'),
  (@{const_syntax "ch_tail"}, ch_tail_tr'),
  (@{const_syntax "ch_cons"}, ch_cons_tr')
];

*}

print_translation {*

  [ chNode_tr' "xHOL_Defs" "ch_eq", chNode_tr' "xHOL_Defs" "ch_neq", chNode_tr' "xHOL_Defs" "ch_iff", 
    chNode_tr' "xHOL_Defs" "ch_le", chNode_tr' "xHOL_Defs" "ch_lt", chNode_tr' "xHOL_Defs" "ch_subeq", 
    chNode_tr' "xHOL_Defs" "ch_sub", chNode_tr' "xHOL_Defs" "ch_imp", chNode_tr' "xHOL_Defs" "ch_in"];

*}

subsection {* Reverse implication *}

text {*

A reverse implication operator is useful for doing calculational proofs.

*}

definition
  rimplies :: "[\<bool>, \<bool>] \<rightarrow> \<bool>" (infixr "\<Leftarrow>" 25)
where
  impliedby_def: "a \<Leftarrow> b \<defs> b \<Rightarrow> a"

lemma [trans]: "\<lbrakk>a \<Leftarrow> b; b \<Leftarrow> c \<rbrakk> \<turnstile> a \<Leftarrow> c"
  by (auto simp add: impliedby_def)
  
lemma [trans]: "\<lbrakk>a \<Leftarrow> b; b = c \<rbrakk> \<turnstile> a \<Leftarrow> c"
  by (auto simp add: impliedby_def)

lemma [trans]: "\<lbrakk>a = b; b \<Leftarrow> c \<rbrakk> \<turnstile> a \<Leftarrow> c"
  by (auto simp add: impliedby_def)

lemma [trans]: "\<lbrakk> a; b \<Leftarrow> a \<rbrakk> \<turnstile> b"
  by (auto simp add: impliedby_def)

lemma [trans]: "\<lbrakk> b \<Leftarrow> a; a \<rbrakk> \<turnstile> b"
  by (auto simp add: impliedby_def)

lemma [iff]: "a \<Leftarrow> a"
  by (unfold impliedby_def, blast)

lemmas impbyI [intro!] =  impI [folded impliedby_def]

lemma impbyD [dest!]: "\<lbrakk>a \<Leftarrow> b; b \<rbrakk> \<turnstile> a"
  by (auto simp add: impliedby_def)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Leftarrow> B) \<turnstile> A \<and> C \<Leftarrow> B \<and> C"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Leftarrow> B) \<turnstile> A \<and> C \<Leftarrow> C \<and> B"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Leftarrow> B) \<turnstile> C \<and> A \<Leftarrow> C \<and> B"
  by (auto)

lemma [mintro!(wind)]: "(C \<turnstile> A \<Leftarrow> B) \<turnstile> C \<and> A \<Leftarrow> B \<and> C"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> A \<Leftarrow> A \<and> B"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> A \<Leftarrow> B \<and> A"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> A \<and> B \<Leftarrow> A"
  by (auto)

lemma [mintro!(wind)]: "(A \<turnstile> B) \<turnstile> B \<and> A \<Leftarrow> A"
  by (auto)

definition
  ch_rimp :: "[\<bool>, \<bool>] \<rightarrow> \<bool>"
where
  ch_rimp_def [simp]: "ch_rimp x y \<defs> x \<Leftarrow> y"

syntax (xsymbols output)
  "_xHOL_Defs\<ZZ>ch_rimp" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<Leftarrow>" 50)

syntax (zed)
  "_xHOL_Defs\<ZZ>ch_rimp" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chRimp>" 50)

parse_translation {*

[chNode_tr "xHOL_Defs" "ch_rimp"]

*}

print_translation {*

[chNode_tr' "xHOL_Defs" "ch_rimp"]

*}

subsection {* Reverse ordering *}

text {*

Equally reverse ordering is also useful in calculational reasoning. 
The base HOL library includes a reverse ordering syntax, but an actual
operator works better with the calculational reasoning package.

*}

context ord

begin

no_notation (input)
  Orderings.greater (infix ">" 50) and           
  Orderings.greater_eq (infix ">=" 50)

no_notation (input)
  Orderings.greater_eq (infix "\<ge>" 50)

definition
  great_eq :: "['a, 'a] => bool"
where
  ge_def: "great_eq \<defs> (\<olambda> x y \<bullet> y \<le> x)"

definition
  great :: "['a, 'a] => bool"
where
  gt_def: "great \<defs> (\<olambda> x y \<bullet> y < x)"

notation
  great ("op >") and
  great_eq ("op >=") and
  great ("(_/ > _)"  [51, 51] 50) and
  great_eq ("(_/ >= _)" [51, 51] 50)

notation (xsymbols output)
  great_eq ("op \<ge>") and
  great_eq ("(_/ \<ge> _)"  [51, 51] 50)

notation (zed)
  great_eq ("(_/ \<ge> _)"  [51, 51] 50)

end

definition
  ch_ge :: "['a::ord, 'a] => bool"
where
  ch_ge_def [simp]: "ch_ge x y \<defs> x \<ge> y"

definition
  ch_gt :: "['a::ord, 'a] => bool"
where
  ch_gt_def [simp]: "ch_gt x y \<defs> x > y"

syntax (xsymbols output)
  "_xHOL_Defs\<ZZ>ch_ge" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<ge>" 50)
  "_xHOL_Defs\<ZZ>ch_gt" :: "[args, chainelt] \<rightarrow> chainrel" (infixr ">" 50)

syntax (zed)
  "_xHOL_Defs\<ZZ>ch_ge" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chGe>" 50)
  "_xHOL_Defs\<ZZ>ch_gt" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chGt>" 50)

parse_translation {*

[
  chNode_tr "xHOL_Defs" "ch_gt",
  chNode_tr "xHOL_Defs" "ch_ge"
]

*}

print_translation {*

[ 
  chNode_tr' "xHOL_Defs" "ch_gt", 
  chNode_tr' "xHOL_Defs" "ch_ge" 
]

*}

no_notation (xsymbols)
  Set.supset ("op \<supset>") and
  Set.supset  ("(_/ \<supset> _)" [51, 51] 50) and
  Set.supset_eq  ("op \<supseteq>") and
  Set.supset_eq  ("(_/ \<supseteq> _)" [51, 51] 50)

abbreviation
  supset :: "'a set \<rightarrow> 'a set \<rightarrow> bool" where
  "supset \<equiv> great"

abbreviation
  supset_eq :: "'a set \<rightarrow> 'a set \<rightarrow> bool" where
  "supset_eq \<equiv> great_eq"

notation (xsymbols)
  supset  ("op \<supset>") and
  supset  ("(_/ \<supset> _)" [50, 51] 50) and
  supset_eq  ("op \<supseteq>") and
  supset_eq  ("(_/ \<supseteq> _)" [50, 51] 50)

lemma [trans]: "\<lbrakk>(a::'a::order) = b; b > c \<rbrakk> \<turnstile> a > c"
  by (auto simp add: gt_def)

lemma [trans]: "\<lbrakk>(a::'a::order) > b; b = c \<rbrakk> \<turnstile> a > c"
  by (auto simp add: gt_def)

lemma [trans]: "\<lbrakk>(a::'a::order) > b; b > c \<rbrakk> \<turnstile> a > c"
  by (auto simp add: gt_def)

lemma [trans]: "\<lbrakk>(a::'a::order) > b; b > a \<rbrakk> \<turnstile> P"
  by (auto simp add: gt_def)

lemma [trans]: "\<lbrakk>(a::'a::order) = b; b \<ge> c \<rbrakk> \<turnstile> a \<ge> c"
  by (auto simp add: ge_def)
  
lemma [trans]: "\<lbrakk>(a::'a::order) \<ge> b; b = c \<rbrakk> \<turnstile> a \<ge> c"
  by (auto simp add: ge_def)

lemma [trans]: "\<lbrakk>(a::'a::order) \<ge> b; b \<ge> c \<rbrakk> \<turnstile> a \<ge> c"
  by (auto simp add: ge_def)

lemma [trans]: "\<lbrakk>(a::'a::order) \<ge> b; b \<ge> a \<rbrakk> \<turnstile> a = b"
  by (auto simp add: ge_def)

lemma [trans]: "\<lbrakk>(a::'a::order) > b; b \<ge> c \<rbrakk> \<turnstile> a > c"
  by (auto simp add: ge_def gt_def)

lemma [trans]: "\<lbrakk>(a::'a::order) \<ge> b; b > c \<rbrakk> \<turnstile> a > c"
  by (auto simp add: ge_def gt_def)

lemma [trans]: "\<lbrakk>(a::'a::order) \<ge> b; a \<noteq> b \<rbrakk> \<turnstile> a > b"
  by (auto simp add: ge_def gt_def)

lemma [trans]: "\<lbrakk>(a::'a::order) \<noteq> b; a \<ge> b \<rbrakk> \<turnstile> a > b"
  by (auto simp add: ge_def gt_def)

lemma [iff]: "(a::'a::order) \<ge> a"
  by (unfold ge_def, blast)

(*

lemma [trans]:
  "\<lbrakk>(a::'a::order) = f b; b > (c::'b::order); \<And> x y \<bullet> x < y \<turnstile> f x < f y\<rbrakk> \<turnstile> a > f c"
  by (subgoal_tac "f b > f c", unfold gt_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) > b; f b = (c::'b::order); \<And> x y \<bullet> x < y \<turnstile> f x < f y\<rbrakk> \<turnstile> f a > c"
  by (subgoal_tac "f a > f b", unfold gt_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) = f b; b \<ge> (c::'b::order); \<And> x y \<bullet> x \<le> y \<turnstile> f x \<le> f y\<rbrakk> \<turnstile> a \<ge> f c"
  by (subgoal_tac "f b \<ge> f c", unfold ge_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) \<ge> b; f b = (c::'b::order); \<And> x y \<bullet> x \<le> y \<turnstile> f x \<le> f y\<rbrakk> \<turnstile> f a \<ge> c"
  by (subgoal_tac "f a \<ge> f b", unfold ge_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) \<ge> f b; b \<ge> (c::'b::order); \<And> x y \<bullet> x \<le> y \<turnstile> f x \<le> f y\<rbrakk> \<turnstile> a \<ge> f c"
  by (subgoal_tac "f b \<ge> f c", unfold ge_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) \<ge> b; f b \<ge> (c::'b::order); \<And> x y \<bullet> x \<le> y \<turnstile> f x \<le> f y\<rbrakk> \<turnstile> f a \<ge> c"
  by (subgoal_tac "f a \<ge> f b", unfold ge_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) > f b; b \<ge> (c::'b::order); \<And> x y \<bullet> x \<le> y \<turnstile> f x \<le> f y\<rbrakk> \<turnstile> a > f c"
  by (subgoal_tac "f b \<ge> f c", unfold gt_def ge_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) > b; f b \<ge> (c::'b::order); \<And> x y \<bullet> x < y \<turnstile> f x < f y\<rbrakk> \<turnstile> f a > c"
  by (subgoal_tac "f a > f b", unfold gt_def ge_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) \<ge> f b; b > (c::'b::order); \<And> x y \<bullet> x < y \<turnstile> f x < f y\<rbrakk> \<turnstile> a > f c"
  by (subgoal_tac "f b > f c", unfold gt_def ge_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) \<ge> b; f b > (c::'b::order); \<And> x y \<bullet> x \<le> y \<turnstile> f x \<le> f y\<rbrakk> \<turnstile> f a > c"
  by (subgoal_tac "f a \<ge> f b", unfold gt_def ge_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) > f b; b > (c::'b::order); \<And> x y \<bullet> x < y \<turnstile> f x < f y\<rbrakk> \<turnstile> a > f c"
  by (subgoal_tac "f b > f c", unfold gt_def ge_def, force, force)

lemma [trans]:
  "\<lbrakk>(a::'a::order) > b; f b > (c::'b::order); \<And> x y \<bullet> x < y \<turnstile> f x < f y\<rbrakk> \<turnstile> f a > c"
  by (subgoal_tac "f a > f b", unfold gt_def ge_def, force, force)
*)

section {* Product space operators *}

subsection {* Finite set products *}

definition
  linsert :: "['b, 'a set] \<rightarrow> ('b \<times> 'a) set"
where
  linsert_def: "linsert b A \<defs> { a | a \<in> A \<bullet> (b, a) }"

lemma finite_cross [simp]:
  "{} \<times> A = {}"
  "(insert b B) \<times> A = linsert b A \<union> (B \<times> A)"
  "linsert b (insert a A) = insert (b, a) (linsert b A)"
  "linsert b {} = {}"
  by (auto simp add: linsert_def)

lemma linsert_mem [simp]:
  "(b, a) \<in> linsert c A \<Leftrightarrow> b = c \<and> a \<in> A"
  by (auto simp add: linsert_def)

subsection {* Product functions *}

text {*

We consider reasoning about functions on tuples.

Pair-valued functions admit a splitting law.

*}

lemma PairFunE: "(\<And> g h \<bullet> f = (\<olambda> c \<bullet> (g c, h c)) \<turnstile> P) \<turnstile> P"
proof -
  assume a1: "\<And> g h \<bullet> f = (\<olambda> c \<bullet> (g c, h c)) \<turnstile> P"
  have a2: "f = (\<olambda> c \<bullet> (fst (f c),snd (f c)))"
    by (intro ext, rule surjective_pairing)
  from a1 a2 show "P" 
    by (this)
qed

text {*

In fact we find it useful to introduce an operator for expressing tuple valued
functions.

*}

definition
  ffst :: "('a \<rightarrow> ('b \<times> 'c)) \<rightarrow> 'a \<rightarrow> 'b"
where
  ffst_def: "ffst g \<defs> (\<olambda> x \<bullet> fst (g x))"

definition
  fsnd :: "('a \<rightarrow> ('b \<times> 'c)) \<rightarrow> 'a \<rightarrow> 'c"
where
  fsnd_def: "fsnd g \<defs> (\<olambda> x \<bullet> snd (g x))"

definition
  fusion :: "['a \<rightarrow> 'b, 'a \<rightarrow> 'c] \<rightarrow> 'a \<rightarrow> ('b \<times> 'c)"
where
  fusion_def: "fusion f g \<defs> (\<olambda> a \<bullet> (f a, g a))"

notation (xsymbols output)
  fusion (infixr "\<nabla>" 80)

notation (zed)
  fusion (infixr "\<fus>" 80)

lemma PairFunE': "(\<And> g h \<bullet> f = g \<fus> h \<turnstile> P) \<turnstile> P"
  apply (cases f rule: PairFunE)
  apply (simp add: fusion_def)
  done 

text {*

Next we introduce support for definition of fusions using case-statements and argument patterns.

*}

definition
  fusion_case :: "(['a \<rightarrow> 'b, 'a \<rightarrow> 'c] \<rightarrow> 'd) \<rightarrow> (('a \<rightarrow> ('b \<times> 'c)) \<rightarrow> 'd)"
where
  fusion_case_def: "fusion_case \<defs> (\<olambda> F f \<bullet> F (ffst f) (fsnd f))"

nonterminal
  ftuple_args and
  fpatterns

syntax ("" output)
  "_xHOL_Defs\<ZZ>fpattern"    :: "[pttrn, fpatterns] \<rightarrow> pttrn"         ("'(_ \\'/ _')")
  "_xHOL_Defs\<ZZ>fpatterns"   :: "[pttrn, fpatterns] \<rightarrow> fpatterns"      ("_ \\'/ _")

syntax (xsymbols output)
  "_xHOL_Defs\<ZZ>fpattern"    :: "[pttrn, fpatterns] \<rightarrow> pttrn"         ("'(_ \<nabla>/ _')")
  "_xHOL_Defs\<ZZ>fpatterns"   :: "[pttrn, fpatterns] \<rightarrow> fpatterns"      ("_ \<nabla>/ _")

syntax (zed)
  "_xHOL_Defs\<ZZ>fpattern"    :: "[pttrn, fpatterns] \<rightarrow> pttrn"         ("'(_ \<fus>/ _')")
  ""            :: "pttrn \<rightarrow> fpatterns"                  ("_")
  "_xHOL_Defs\<ZZ>fpatterns"   :: "[pttrn, fpatterns] \<rightarrow> fpatterns"      ("_ \<fus>/ _")

translations
  "(\<olambda> (x \<fus> y \<fus> zs) \<bullet> b)" \<rightleftharpoons> "CONST xHOL_Defs.fusion_case (\<olambda> x (y \<fus> zs) \<bullet> b)"
  "(\<olambda> (x \<fus> y) \<bullet> b)" \<rightleftharpoons> "CONST xHOL_Defs.fusion_case (\<olambda> x y \<bullet> b)"

setup {*

let

val fp = Ast.mk_appl (Ast.Constant "xHOL_Defs.fusion") [Ast.Variable "f1", Ast.Variable "f2"];
val fus = Ast.mk_appl (Ast.Constant "_case1") [fp, Ast.Variable "f"];
val ast = Ast.mk_appl (Ast.Constant "_case_syntax") [Ast.Variable "t", fus]

val fus2' = Ast.mk_appl (Ast.Constant "_abs") [Ast.Variable "f2", Ast.Variable "f"]
val fus1' = Ast.mk_appl (Ast.Constant "_abs") [Ast.Variable "f1", fus2']
val ast' = Ast.mk_appl (Ast.Constant "xHOL_Defs.fusion_case") [fus1', Ast.Variable "t"]
in
  Sign.add_trrules [Syntax.Parse_Print_Rule (ast, ast')]
end;

*}

lemma ffst_conv [simp]:
  "ffst (f \<fus> g) = f"
  apply (intro ext)
  apply (simp add: fusion_def ffst_def)
  done

lemma fsnd_conv [simp]:
  "fsnd (f \<fus> g) = g"
  apply (intro ext)
  apply (simp add: fusion_def fsnd_def)
  done

lemma fusion_collapse [simp]:
  "(ffst f \<fus> fsnd f) = f"
  apply (intro ext)
  apply (simp add: fusion_def ffst_def fsnd_def)
  done

lemma surj_fusion [simp]:
  "(\<exists> g h \<bullet> f = (g \<fus> h))"
  apply (witness "ffst f")
  apply (witness "fsnd f")
  apply (simp)
  done

lemma fusion_case_beta [simp]:
  "fusion_case H (f \<fus> g) = H f g"
  by (simp add: fusion_case_def ffst_conv fsnd_conv)

lemma fusion_case_beta' [simp]:
  "fusion_case H (\<olambda> x \<bullet> (f x, g x)) = H f g"
  by (simp add: fusion_case_def ffst_def fsnd_def)

lemma split_fused_Ex [simp]:
  "(\<exists> f \<bullet> P f) = (\<exists> g h \<bullet> P (g \<fus> h))"
proof (auto simp add: fusion_def)
  fix f 
  assume b1: "P f"
  then show "(\<exists> g h \<bullet> P (\<olambda> a \<bullet> (g a, h a)))"
    apply (cases f rule: PairFunE)
    apply (auto)
    done
qed

lemma split_fused_All [simp]:
  "(\<forall> f \<bullet> P f) = (\<forall> g h \<bullet> P (g \<fus> h))"
proof (auto simp add: fusion_def)
  fix f 
  assume "(\<forall> g h \<bullet> P (\<olambda> a \<bullet> (g a, h a)))"
  then show "P f"
    apply (cases f rule: PairFunE)
    apply (auto)
    done
qed

notation (xsymbols output)
  map_pair (infixr "\<parallel>" 75)

notation (zed)
  map_pair (infixr "\<par>" 75)

lemma map_fusion [simp]:
  "(f \<par> g) \<circ> (h \<fus> k) = (f \<circ> h) \<fus> (g \<circ> k)"
  apply (rule ext)
  apply (simp add: fusion_def)
  done

section {* Miscellaneous definitions *}

subsection {* Exclusive or *}

text {*

The exclusive or is also a useful operator.

*}

definition
  xor :: "[\<bool>, \<bool>] \<rightarrow> \<bool>"
where
  xor_def: "xor x y \<defs> x \<Leftrightarrow> \<not> y"

notation (xsymbols output)
  "xor" (infixr "<\<noteq>>" 30)

notation (zed)
  "xor" (infixr "\<xor>" 30)

lemma xorAC [simp]:
  shows 
    xorC: "x \<xor> y \<Leftrightarrow> y \<xor> x" and
    xorA: "(x \<xor> y) \<xor> z \<Leftrightarrow> x \<xor> (y \<xor> z)" and
    xorLC: "x \<xor> (y \<xor> z) \<Leftrightarrow> y \<xor> (x \<xor> z)"
  by (auto simp add: xor_def)

lemma xorI1 [intro]:
  assumes a1: "\<not>y \<turnstile> x" and a2: "y \<turnstile> \<not>x"
  shows "x \<xor> y"
  using a1 a2
  by (auto simp add: xor_def)

lemma xorI2 [intro]:
  assumes a1: "\<not>x \<turnstile> y" and a2: "x \<turnstile> \<not>y"
  shows "x \<xor> y"
  using a1 a2
  by (auto simp add: xor_def)

lemma xor_conv:
  "x \<xor> y \<Leftrightarrow> (x \<and> \<not>y) \<or> (y \<and> \<not>x)"
  by (auto simp add: xor_def)

lemma xorE [elim!]:
  assumes a1: "x \<xor> y" and a2: "\<lbrakk> x; \<not>y \<rbrakk> \<turnstile> R" and a3: "\<lbrakk> y; \<not>x \<rbrakk> \<turnstile> R"
  shows "R"
  using a1 a2 a3
  by (auto simp add: xor_conv)

lemma 
  assumes a1: "x \<xor> y"
  shows xorD1: "x \<turnstile> \<not>y" and xorD2: "y \<turnstile> \<not>x"
  using a1
  by (auto simp add: xor_def)
 
definition
  ch_xor :: "[\<bool>, \<bool>] \<rightarrow> \<bool>"
where
  ch_xor_def [simp]: "ch_xor x y \<defs> x \<xor> y"

syntax (xsymbols output)
  "_xHOL_Defs\<ZZ>ch_xor" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "<\<noteq>>" 50)

syntax (zed)
  "_xHOL_Defs\<ZZ>ch_xor" :: "[args, chainelt] \<rightarrow> chainrel" (infixr "\<chXor>" 50)

parse_translation {*

[chNode_tr "xHOL_Defs" "ch_xor"]

*}

print_translation {*

[chNode_tr' "xHOL_Defs" "ch_xor"]

*}

subsection {* Definedness *}

text {*

A definedness operator for optional values is useful.

*}

fun 
  defOpt :: "'a\<option> \<rightarrow> \<bool>"
where
    "defOpt \<None> = \<False>"
  | "defOpt a\<option> = \<True>"

notation (xsymbols output)
  defOpt ("\<Delta>")

notation (zed)
  defOpt ("\<defOpt>")

(*
text {*

Some Z-style syntax for the @{term Least} operator.

*}

definition
  set_Least :: "('a::ord) set \<rightarrow> 'a"
where
  set_Least_def: "set_Least X \<defs> (\<sthe> x | x \<in> X \<and> (\<forall> y \<bullet> y \<in> X \<Rightarrow> x \<le> y))"

definition
  set_Greatest :: "('a::ord) set \<rightarrow> 'a"
where
  set_Greatest_def: "set_Greatest X \<defs> (\<sthe> x | x \<in> X \<and> (\<forall> y \<bullet> y \<in> X \<Rightarrow> y \<le> x))"

syntax ("" output)
  "_xHOL_Defs\<ZZ>st_Least" :: "schematext \<rightarrow> logic" ("LEAST _" 0)
  "_xHOL_Defs\<ZZ>st_Greatest" :: "schematext \<rightarrow> logic" ("GREATEST _" 0)

syntax (xsymbols output)
  "_xHOL_Defs\<ZZ>st_Least" :: "schematext \<rightarrow> logic" ("\<mu> _" 0)
  "_xHOL_Defs\<ZZ>st_Greatest" :: "schematext \<rightarrow> logic" ("\<nu> _" 0)

syntax (zed)
  "_xHOL_Defs\<ZZ>st_Least" :: "schematext \<rightarrow> logic" ("\<LEAST> _" 0)
  "_xHOL_Defs\<ZZ>st_Greatest" :: "schematext \<rightarrow> logic" ("\<GREATEST> _" 0)

translations
  "_xHOL_Defs\<ZZ>st_Least S" \<rightleftharpoons> "CONST xHOL_Defs.set_Least (_xHOL_Syntax\<ZZ>coll S)"
  "_xHOL_Defs\<ZZ>st_Greatest S" \<rightleftharpoons> "CONST xHOL_Defs.set_Greatest (_xHOL_Syntax\<ZZ>coll S)"

lemma set_LeastI2_order:
  "\<lbrakk> (x::'a::order) \<in> X;
     (\<And> y \<bullet> y \<in> X \<turnstile> x \<le> y);
     (\<And> x \<bullet> \<lbrakk> x \<in> X; \<forall> y \<bullet> y \<in> X \<Rightarrow> x \<le> y \<rbrakk> \<turnstile> Q x) \<rbrakk>
   \<turnstile> Q (set_Least X)"
  apply (unfold set_Least_def)
  apply (rule set_theI2)
  apply (simp_all)
  apply (blast intro: order_antisym)+
  done

lemma set_GreatestI2_order:
  "\<lbrakk> (x::'a::order) \<in> X;
     (\<And> y \<bullet> y \<in> X \<turnstile> y \<le> x);
     (\<And> x \<bullet> \<lbrakk> x \<in> X; \<forall> y \<bullet> y \<in> X \<Rightarrow> y \<le> x \<rbrakk> \<turnstile> Q x) \<rbrakk>
   \<turnstile> Q (set_Greatest X)"
  apply (unfold set_Greatest_def)
  apply (rule set_theI2)
  apply (simp_all)
  apply (blast intro: order_antisym)+
  done

lemma collect_LeastI2_order:
  "\<lbrakk> P (x::'a::order);
     (\<And> y \<bullet> P y \<turnstile> x \<le> y);
     (\<And> x \<bullet> \<lbrakk> P x; \<forall> y \<bullet> P y \<Rightarrow> x \<le> y \<rbrakk> \<turnstile> Q x) \<rbrakk>
   \<turnstile> Q (set_Least (Collect P))"
  apply (unfold set_Least_def)
  apply (rule set_theI2)
  apply (simp_all)
  apply (blast intro: order_antisym)+
  done

lemma collect_GreatestI2_order:
  "\<lbrakk> P (x::'a::order);
     (\<And> y \<bullet> P y \<turnstile> y \<le> x);
     (\<And> x \<bullet> \<lbrakk> P x; \<forall> y \<bullet> P y \<Rightarrow> y \<le> x \<rbrakk> \<turnstile> Q x) \<rbrakk>
   \<turnstile> Q (set_Greatest (Collect P))"
  apply (unfold set_Greatest_def)
  apply (rule set_theI2)
  apply (simp_all)
  apply (blast intro: order_antisym)+
  done

lemma set_Least_equality:
  "\<lbrakk> (k::'a::order) \<in> X; (\<And> x \<bullet> x \<in> X \<turnstile> k \<le> x) \<rbrakk> \<turnstile> set_Least X = k"
  apply (simp add: set_Least_def)
  apply (rule set_the_equality)
  apply (auto intro!: order_antisym)
  done

lemma set_Greatest_equality:
  "\<lbrakk> (k::'a::order) \<in> X; (\<And> x \<bullet> x \<in> X \<turnstile> x \<le> k) \<rbrakk> \<turnstile> set_Greatest X = k"
  apply (simp add: set_Greatest_def)
  apply (rule set_the_equality)
  apply (auto intro!: order_antisym)
  done

lemma collect_Least_equality:
  "\<lbrakk> P (k::'a::order); (\<And> x \<bullet> P x \<turnstile> k \<le> x) \<rbrakk> \<turnstile> set_Least (Collect P) = k"
  apply (simp add: set_Least_def)
  apply (rule set_the_equality)
  apply (auto intro!: order_antisym)
  done

lemma collect_Greatest_equality:
  "\<lbrakk> P (k::'a::order); (\<And> x \<bullet> P x \<turnstile> x \<le> k) \<rbrakk> \<turnstile> set_Greatest (Collect P) = k"
  apply (simp add: set_Greatest_def)
  apply (rule set_the_equality)
  apply (auto intro!: order_antisym)
  done

lemma wellorder_set_Least_lemma [rule_format]:
  "(k::'a::wellorder) \<in> X \<Rightarrow> set_Least X \<in> X \<and> set_Least X \<le> k"
  apply (rule_tac a = k in wf [THEN wf_induct])
  apply (rule impI)
  apply (rule classical)
  apply (rule_tac s = x in set_Least_equality [THEN ssubst], auto)
  apply (auto simp add: linorder_not_less [symmetric])
  done

lemma wellorder_collect_Least_lemma [rule_format]:
  "P (k::'a::wellorder) \<Rightarrow> P (set_Least (Collect P)) \<and> set_Least (Collect P) \<le> k"
  apply (rule_tac a = k in wf [THEN wf_induct])
  apply (rule impI)
  apply (rule classical)
  apply (rule_tac s = x in collect_Least_equality [THEN ssubst], auto)
  apply (auto simp add: linorder_not_less [symmetric])
  done

lemmas set_LeastI   = wellorder_set_Least_lemma [THEN conjunct1, standard]
lemmas set_Least_le = wellorder_set_Least_lemma [THEN conjunct2, standard]

lemmas collect_LeastI   = wellorder_collect_Least_lemma [THEN conjunct1, standard]
lemmas collect_Least_le = wellorder_collect_Least_lemma [THEN conjunct2, standard]

-- "The following 3 lemmas are due to Brian Huffman"
lemma set_LeastI_ex: 
  "(\<exists> x::'a::wellorder \<bullet> x \<in> X) \<turnstile> set_Least X \<in> X"
  apply (erule exE)
  apply (erule set_LeastI)
  done

lemma collect_LeastI_ex: 
  "(\<exists> x::'a::wellorder \<bullet> P x) \<turnstile> P (set_Least (Collect P))"
  apply (erule exE)
  apply (erule collect_LeastI)
  done

lemma set_LeastI2:
  "\<lbrakk> (a::'a::wellorder) \<in> X; (\<And> x \<bullet> x \<in> X \<turnstile> Q x) \<rbrakk> \<turnstile> Q (set_Least X)"
  by (blast intro: set_LeastI)

lemma collect_LeastI2:
  "\<lbrakk> P (a::'a::wellorder); (\<And> x \<bullet> P x \<turnstile> Q x) \<rbrakk> \<turnstile> Q (set_Least (Collect P))"
  by (blast intro: collect_LeastI)

lemma not_less_set_Least: "[| k < (set_Least X) |] ==> (k::'a::wellorder) \<notin> X"
apply (simp (no_asm_use) add: linorder_not_le [symmetric])
apply (erule contrapos_nn)
apply (erule set_Least_le)
done                                                                            

lemma not_less_collect_Least: "[| k < (set_Least (Collect P)) |] ==> \<not>(P (k::'a::wellorder))"
apply (simp (no_asm_use) add: linorder_not_le [symmetric])
apply (erule contrapos_nn)
apply (erule collect_Least_le)
done

lemma set_Least_singleton:
  "set_Least {x::('a::order)} = x"
  apply (rule set_Least_equality)
  apply (auto)
  done

*)

subsection {* Disjoint sets *}

text {*

The concept of disjointness is frequently useful.

*}

definition
  disjoint :: "['a set, 'a set] \<rightarrow> \<bool>"
  where
  disjoint_def: "disjoint \<defs> (\<olambda> X Y \<bullet> X \<inter> Y = \<emptyset>)"

lemma disjoint_union:
  assumes 
    a1: "disjoint X Y" and
    a2: "x \<in> X \<union> Y"
  shows "x \<in> X \<xor> x \<in> Y"
  using a1 a2
  by (auto simp add: disjoint_def)

lemma disjointI:
  assumes
    a1: "\<And> x \<bullet> \<lbrakk> x \<in> X; x \<in> Y \<rbrakk> \<turnstile> \<False>"
  shows
    "disjoint X Y"
  by (auto intro!: a1 simp add: disjoint_def)

lemma disjointD1:
  assumes 
    a1: "disjoint X Y" and
    a2: "x \<in> X"
  shows 
    "x \<notin> Y"
  using a1 a2
  by (auto simp add: disjoint_def)

lemma disjointD2:
  assumes 
    a1: "disjoint X Y" and
    a2: "x \<in> Y"
  shows 
    "x \<notin> X"
  using a1 a2
  by (auto simp add: disjoint_def)

lemma disjointE1:
  assumes 
    a1: "disjoint X Y" "x \<in> X \<union> Y" and
    a2: "\<lbrakk> x \<in> X; x \<notin> Y \<rbrakk> \<turnstile> R" and  
    a3: "\<lbrakk> x \<in> Y; x \<notin> X \<rbrakk> \<turnstile> R" 
  shows
    "R" 
  using a1
  by (auto intro: a2 a3 simp add: disjoint_def set_eq_iff) 

lemma disjointE:
  assumes 
    a1: "disjoint X Y" and
    a2: "\<not> R \<turnstile> x \<in> X" and
    a3: "\<not> R \<turnstile> x \<in> Y"
  shows
    "R" 
  using a1 a2 a3
  by (auto simp add: disjoint_def set_eq_iff) 

lemma disjoint_el_ne:
  assumes
    a1: "disjoint X Y" and
    a2: "x \<in> X" and
    a3: "y \<in> Y"
  shows
    "x \<noteq> y"
  using a1 a2 a3
  by (auto simp add: disjoint_def)

lemma disjoint_right_mono:
  assumes
    a1: "B \<subseteq> C" "disjoint A C"
  shows
    "disjoint A B"
  using a1
  by (auto simp add: disjoint_def)

lemma disjoint_left_mono:
  assumes
    a1: "B \<subseteq> C" "disjoint C A"
  shows
      "disjoint B A"
  using a1
  by (auto simp add: disjoint_def)

lemma disjoint_right_Union_iff:
  "disjoint A (\<Union>\<B>) \<Leftrightarrow> (\<forall> B | B \<in> \<B> \<bullet> disjoint A B)"
  by (auto simp add: disjoint_def)

lemma disjoint_left_Union_iff:
  "disjoint (\<Union>\<B>) A \<Leftrightarrow> (\<forall> B | B \<in> \<B> \<bullet> disjoint B A)"
      by (auto simp add: disjoint_def) 

primrec
  disj_list :: "'a set list \<rightarrow> \<bool>"
where
  "disj_list [] \<Leftrightarrow> \<True>"
| "disj_list (A#S) \<Leftrightarrow> (\<forall> X | X \<in> set S \<bullet> disjoint A X) \<and> disj_list S"

lemma
  "disj_list [{1::nat}, {2}, {3}]"
  by (simp add: disjoint_def)

definition
  part_list :: "['a set, 'a set list] \<rightarrow> \<bool>"
where
  "part_list A \<AA> \<Leftrightarrow> disj_list \<AA> \<and> A = (\<Union>(set \<AA>))"

lemma
  "part_list {1, 2, 3} [{1::nat}, {2}, {3}]"
  "part_list {1, 2, 3} [{1::nat, 2}, {3}]"
  by (auto simp add: part_list_def disjoint_def)

lemma
  "part_list A [X, Y, Z] \<Rightarrow> X \<inter> Y = \<emptyset>"
  "part_list A [X, Y, Z] \<and> a \<in> A \<Rightarrow> a \<in> X \<or> a \<in> Y \<or> a \<in> Z"
  by (auto simp add: part_list_def disjoint_def)

definition
  "Disjoint \<X> \<Leftrightarrow> (\<forall> X Y | X \<in> \<X> \<and> Y \<in> \<X> \<bullet> disjoint X Y \<Leftrightarrow> X \<noteq> Y)"

lemma Disjoint_def':
  "Disjoint \<X> \<Leftrightarrow> (\<forall> X Y | X \<in> \<X> \<and> Y \<in> \<X> \<bullet> \<not> disjoint X Y \<Leftrightarrow> X = Y)"
  by (auto simp add: Disjoint_def)

lemma DisjointI:
  assumes
    a1: "\<emptyset> \<notin> \<X>" and
    a2: "(\<And> X Y \<bullet> \<lbrakk> X \<in> \<X>; Y \<in> \<X>; X \<noteq> Y \<rbrakk> \<turnstile> disjoint X Y)"
  shows
    "Disjoint \<X>"
  apply (simp add: Disjoint_def)
  apply (mauto(inference) mintro!: a2)
  apply (auto simp add: disjoint_def a1)
  done

lemma DisjointD0:
  assumes
    a1: "Disjoint \<X>"
  shows
    "\<emptyset> \<notin> \<X>"
  using a1
  by (auto simp add: Disjoint_def disjoint_def)

lemma DisjointD1:
  assumes
    a1: "Disjoint \<X>" and
    a2: "X \<in> \<X>" and 
    a3: "Y \<in> \<X>" and
    a4: "X \<noteq> Y"
  shows
    "disjoint X Y"
  using a1 a2 a3 a4
  by (auto simp add: Disjoint_def)

lemma DisjointD1':
  assumes
    a1: "Disjoint \<X>" and
    a2: "X \<in> \<X>" and 
    a3: "Y \<in> \<X>" and
    a4: "\<not>disjoint X Y"
  shows
    "X = Y"
  using a1 a2 a3 a4
  by (auto simp add: Disjoint_def)

lemma DisjointD2:
  assumes
    a1: "Disjoint \<X>" and
    a2: "X \<in> \<X>" and 
    a3: "Y \<in> \<X>" and
    a4: "disjoint X Y"
  shows
    "X \<noteq> Y"
  using a1 a2 a3 a4
  by (auto simp add: Disjoint_def)

lemma DisjointD2':
  assumes
    a1: "Disjoint \<X>" and
    a2: "X \<in> \<X>" and 
    a3: "Y \<in> \<X>" and
    a4: "X = Y"
  shows
    "\<not> disjoint X Y"
  using a1 a2 a3 a4
  by (auto simp add: Disjoint_def)

definition
  "Partition A \<X> \<Leftrightarrow> Disjoint \<X> \<and> \<Union>\<X> = A"

lemmas PartitionI = Partition_def [THEN iffD2, OF conjI, OF DisjointI]

lemmas PartitionD1 = Partition_def [THEN iffD1, THEN conjunct1]
lemmas PartitionD10 = PartitionD1 [THEN DisjointD0]
lemmas PartitionD11 = PartitionD1 [THEN DisjointD1]
lemmas PartitionD12 = PartitionD1 [THEN DisjointD2]
lemmas PartitionD2 = Partition_def [THEN iffD1, THEN conjunct2]

subsection {* Constant-valued functions *}

text {*

A constant valued function constructor is of occasional use.

*}

definition
  funK :: "'a \<rightarrow> ('b \<rightarrow> 'a)"
where
  funK_def: "funK c \<defs> (\<olambda> b \<bullet> c)"

notation (zed)
  funK ("\<^funK>{:_:}")

subsection {* Relation Operators *}

text {*

Although
operator relations often have their own infix syntax, this is not
always the case,
so we introduce syntax for infix application of operator relations,
similar to that for infix application of graph relations.

*}

syntax (zed)
  "_xHOL_Defs\<ZZ>infop" :: "['a, ['a, 'b] \<rightarrow> 'c, 'b] \<rightarrow> 'c" ("\<^infop>{:_:}{:_:}{:_:}")
  "_xHOL_Defs\<ZZ>infopa" :: "['a, ['a, 'b] \<rightarrow> 'c, 'b] \<rightarrow> 'c" ("\<^infopa>{:_:}{:_:}{:_:}")

translations
  "\<^infop>{:a:}{:R:}{:b:}" \<rightharpoonup> "R a b"
  "\<^infopa>{:a:}{:R:}{:b:}" \<rightharpoonup> "R a b"

subsection {* Hidden identity *}

text {*

We introduce a copy of the identity, to act either as a placeholder for translations or
else to suppress print translations.

*}

definition
  zid :: "'a \<rightarrow> 'a"
where
  zid_def [simp]: "zid a \<defs> a"

notation (xsymbols output)
  zid ("_" [1000] 1000)

notation (zed)
  zid ("\<^zid>{:_:}" [1000] 1000)

subsection {* Intervals *}

definition 
  oINTVLo :: "['a::linorder, 'a] \<rightarrow> 'a set" 
where
  oINTVLo_def: "oINTVLo a b \<defs> {x | a < x \<and> x < b}"

definition 
  oINTVLc :: "['a::linorder, 'a] \<rightarrow> 'a set" 
where
  oINTVLc_def: "oINTVLc a b \<defs> {x | a < x \<and> x \<le> b}"

definition 
  cINTVLo :: "['a::linorder, 'a] \<rightarrow> 'a set" 
where
  cINTVLo_def: "cINTVLo a b \<defs> {x | a \<le> x \<and> x < b}"

definition 
  cINTVLc :: "['a::linorder, 'a] \<rightarrow> 'a set" 
where
  cINTVLc_def: "cINTVLc a b \<defs> {x | a \<le> x \<and> x \<le> b}"

notation (xsymbols output)
  oINTVLo ("'(-_\<dots>_-')") and
  oINTVLc ("'(-_\<dots>_-]") and
  cINTVLo ("[-_\<dots>_-')") and
  cINTVLc ("[-_\<dots>_-]")

notation (zed)
  oINTVLo ("\<lopen>_\<dots>_\<ropen>") and
  oINTVLc ("\<lopen>_\<dots>_\<rclose>") and
  cINTVLo ("\<lclose>_\<dots>_\<ropen>") and
  cINTVLc ("\<lclose>_\<dots>_\<rclose>")

definition 
  neighbourhood :: "['a::{plus, minus, linorder}, 'a] \<rightarrow> 'a set"
where
  neighbourhood_def: "neighbourhood x BS_delta \<defs> {x - BS_delta<..<x + BS_delta}"

notation (xsymbols output)
  neighbourhood  ("_\<plusminus>_" [1000, 1000] 1000)

notation (zed)
  neighbourhood ("_\<plusminus>_" [1000, 1000] 1000)

lemmas interval_defs = 
  lessThan_def atMost_def greaterThan_def atLeast_def
  greaterThanLessThan_def atLeastLessThan_def greaterThanAtMost_def atLeastAtMost_def 
  oINTVLo_def oINTVLc_def cINTVLo_def cINTVLc_def neighbourhood_def

lemma [simp]:
  "x \<in> \<lopen>a\<dots>b\<ropen> \<Leftrightarrow> a < x \<and> x < b"
  "x \<in> \<lopen>a\<dots>b\<rclose> \<Leftrightarrow> a < x \<and> x \<le> b"
  "x \<in> \<lclose>a\<dots>b\<ropen> \<Leftrightarrow> a \<le> x \<and> x < b"
  "x \<in> \<lclose>a\<dots>b\<rclose> \<Leftrightarrow> a \<le> x \<and> x \<le> b"
  by (auto simp add: interval_defs)

lemma cINTVLo_atLeastLessThan:
  "\<lclose>0\<dots>N\<ropen> = {0..<N}"
  by (auto simp add: atLeastLessThan_def)

lemma cINTVLc_atLeastAtMost:
  "\<lclose>0\<dots>N\<rclose> = {0..N}"
  by (auto simp add: atLeastAtMost_def)

lemma oINTVLo_greaterThanLessThan:
  "\<lopen>0\<dots>N\<ropen> = {0<..<N}"
  by (auto simp add: greaterThanLessThan_def)

lemma oINTVLc_greaterThanAtMost:
  "\<lopen>0\<dots>N\<rclose> = {0<..N}"
  by (auto simp add: greaterThanAtMost_def)

text {*

It may sometimes be useful to force elements to be in the representation
set, for example to stop repeated unnecessary calculation of membership.

*}

definition
  force :: "['a set, 'a] \<rightarrow> 'a"
where
  force_def: "force A x \<defs> \<if> x \<in> A \<then> x \<else> (\<some> y | y \<in> A) \<fi>"

definition
  pforce :: "['a \<rightarrow> \<bool>, 'a] \<rightarrow> 'a"
where
  pforce_def: "pforce \<phi> x \<defs> \<if> \<phi> x \<then> x \<else> (\<some> y | \<phi> y) \<fi>"

text {*

A dual space is simply a distinguished copy of a given type that
can be given a variant algebraic structure. For example, we
give the dual the reverse of the original order on a type.

*}

typedef
  'a dual = "{a::'a | \<True>}"
  by (auto)

notation (xsymbols output)
  Abs_dual ("_\<^sup>\<circ>" [1000] 1000) and
  Rep_dual ("_\<^sup>\<bullet>" [1000] 1000)

notation (zed)
  Abs_dual ("\<^adual>{:_:}" [1000] 1000) and
  Rep_dual ("\<^rdual>{:_:}" [1000] 1000)
 
interpretation Abs_TD : type_definition "Rep_dual" "Abs_dual" "{ x | \<True> }"
  by (rule type_definition_dual)

lemma Abs_dual: 
  "a \<in> { x | \<True> }"
  by (simp)

lemma Abs_dual_inverse2:    
  "\<^rdual>{:(\<^adual>{:y:}):} = y"  
  by (rule Abs_dual [THEN Abs_dual_inverse])

lemma Abs_dual_inject2:    
  "\<^adual>{:x:} = \<^adual>{:y:} \<Leftrightarrow> x = y"
  by (rule Abs_dual_inject [OF Abs_dual Abs_dual])

end
