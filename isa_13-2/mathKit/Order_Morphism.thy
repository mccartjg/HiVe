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

theory Order_Morphism 
  
imports 
  Order_Locale 
  xHOL_TypeDef

begin


section {* Congruence and monotonicity *}

text {*

Consider @{text "\<^setrel>{:X:}{:BS_leq_d_X:}"} and @{text "\<^setrel>{:Y:}{:BS_leq_d_Y:}"}, we say
that a function @{text "f \<in> X \<ztfun> Y"} is {\em order-preserving} if

*}

locale carrier_tfun = 
  X_carrier X +
  Y_carrier Y
for 
  X::"'a set" and 
  Y::"'b set" +
fixes
  f::"('a \<leftrightarrow> 'b)"
assumes
  f_tfun: "f \<in> X \<ztfun> Y"

locale rel_tfun =
  X_setrel +
  carrier_tfun

locale po_tfun =
  X_partial_order +
  carrier_tfun

sublocale po_tfun \<subseteq> rel_tfun
  by (unfold_locales)

locale order_tfun =
  X_order +
  carrier_tfun

sublocale order_tfun \<subseteq> po_tfun
  by (unfold_locales)

locale rel_rel_tfun =
  Y_setrel Y s +
  rel_tfun X r Y f
for 
  X::"'a set" and 
  r::"'a orderT" and
  Y::"'b set" and
  s::"'b orderT" and
  f :: "('a \<leftrightarrow> 'b)"

locale po_rel_tfun =
  X_partial_order + 
  rel_rel_tfun

sublocale po_rel_tfun \<subseteq> po_tfun
  by (unfold_locales)

locale order_rel_tfun =
  X_order +
  po_rel_tfun

sublocale order_rel_tfun \<subseteq> order_tfun
  by (unfold_locales)

locale rel_preserving = 
  rel_rel_tfun +
assumes
  preserves: "(\<forall> x y | \<lch> x, y \<chIn> X \<rch> \<bullet> x \<hookrightarrow>\<^sub>X y \<Rightarrow> f\<cdot>x \<hookrightarrow>\<^sub>Y f\<cdot>y)"

begin

lemma  rel_preservesD:
  assumes
    a1: "x \<in> X" and
    a2: "y \<in> X" and
    a3: "x \<hookrightarrow>\<^sub>X y"
  shows
    "f\<cdot>x \<hookrightarrow>\<^sub>Y f\<cdot>y"
  apply (rule preserves [rule_format])
  apply (auto simp add: a1 a2 a3)
  done

end

locale po_preserving = 
  rel_preserving + 
  po_rel_tfun

term "po_preserving"

abbreviation (zed)
  po_preserving_set :: "['a set, 'a orderT, 'b set, 'b orderT] \<rightarrow> ('a \<leftrightarrow> 'b) set" ("\<^oprefun>{:_:}{:_:}{:_:}{:_:}")
where
  "\<^oprefun>{:X:}{:BS_leq_d_X:}{:Y:}{:BS_leq_d_Y:} \<defs> Collect (po_preserving X BS_leq_d_X Y BS_leq_d_Y)"
(*
notation (zed)
  po_preserving ("\<^oprefun>{:_:}{:_:}{:_:}{:_:}")
*)

locale order_preserving = 
  rel_preserving + 
  order_rel_tfun

text {*

and an {\em embedding} if

*}

locale rel_embedding = 
  rel_rel_tfun +
assumes
  embeds: "(\<forall> x y | \<lch> x, y \<chIn> X \<rch> \<bullet> x \<hookrightarrow>\<^sub>X y \<Leftrightarrow> f\<cdot>x \<hookrightarrow>\<^sub>Y f\<cdot>y)"

begin

lemma  rel_embedsD:
  assumes
    a1: "x \<in> X" and
    a2: "y \<in> X"
  shows
    "x \<hookrightarrow>\<^sub>X y \<Leftrightarrow> f\<cdot>x \<hookrightarrow>\<^sub>Y f\<cdot>y"
  apply (rule embeds [rule_format])
  apply (auto simp add: a1 a2)
  done

end

sublocale rel_embedding \<subseteq> rel_preserving
  apply (unfold_locales)
  apply (simp add: embeds [rule_format])
  done

locale po_embedding = 
  rel_embedding + 
  po_rel_tfun


abbreviation (zed)
  po_embedding_set :: "['a set, 'a orderT, 'b set, 'b orderT] \<rightarrow> ('a \<leftrightarrow> 'b) set" ("\<^oembfun>{:_:}{:_:}{:_:}{:_:}")
where
  "\<^oembfun>{:X:}{:BS_leq_d_X:}{:Y:}{:BS_leq_d_Y:} \<defs> Collect (po_embedding X BS_leq_d_X Y BS_leq_d_Y)"
(*
notation (zed)
  po_embedding ("\<^oembfun>{:_:}{:_:}{:_:}{:_:}")
*)


locale order_embedding = 
  rel_embedding + 
  order_rel_tfun

text {*

If the source and target preorders in question are partial orders, 
we use the term monotonic for order-preserving, and 
if they are equivalences, we use the term congruence for order embeddings.

*}

locale po_morphism = 
  Y_partial_order +
  po_rel_tfun

locale monotonic = 
  po_preserving + 
  po_morphism

locale congruence = 
  po_embedding + 
  po_morphism


abbreviation (zed)
  monotonic_set :: "['a set, 'a orderT, 'b set, 'b orderT] \<rightarrow> ('a \<leftrightarrow> 'b) set" ("\<^monofun>{:_:}{:_:}{:_:}{:_:}")
where
  "\<^monofun>{:X:}{:BS_leq_d_X:}{:Y:}{:BS_leq_d_Y:} \<defs> Collect (monotonic X BS_leq_d_X Y BS_leq_d_Y)"

abbreviation (zed)
  congruence_set :: "['a set, 'a orderT, 'b set, 'b orderT] \<rightarrow> ('a \<leftrightarrow> 'b) set" ("\<^ucongfun>{:_:}{:_:}{:_:}{:_:}")
where
  "\<^ucongfun>{:X:}{:BS_leq_d_X:}{:Y:}{:BS_leq_d_Y:} \<defs> Collect (congruence X BS_leq_d_X Y BS_leq_d_Y)"
(*
notation (zed)
  monotonic ("\<^monofun>{:_:}{:_:}{:_:}{:_:}") and
  congruence ("\<^ucongfun>{:_:}{:_:}{:_:}{:_:}")
*)

locale order_morphism = 
  Y_order +
  order_rel_tfun

text {*

A relation is said to be congruent if it is congruent in both its arguments.

*}

definition
  r_congruent :: "['a orderT, 'a orderT] \<rightarrow> \<bool>"
where
  r_congruent_def: 
    "r_congruent BS_sim BS_leq \<defs> 
      (\<forall> x_d_1 x_d_2 y_d_1 y_d_2 \<bullet> \<^infopa>{:x_d_1:}{:BS_sim:}{:x_d_2:} \<and> \<^infopa>{:y_d_1:}{:BS_sim:}{:y_d_2:} \<Rightarrow> (\<^infopa>{:x_d_1:}{:BS_leq:}{:y_d_1:} \<Leftrightarrow> \<^infopa>{:x_d_2:}{:BS_leq:}{:y_d_2:}))"

text {*

If an order-embedding from a poset 
@{text "\<^setrel>{:X:}{:BS_leq_d_X:}"} to @{text "\<^setrel>{:Y:}{:BS_leq_d_Y:}"} is bijective,
then @{text "\<^setrel>{:Y:}{:BS_leq_d_Y:}"} is also a poset.

*}

locale carrier_bij =
  carrier_tfun +
assumes
  f_bij: "f \<in> X \<zbij> Y"

locale rel_bij = 
  rel_tfun + 
  carrier_bij

locale po_bij = 
  po_tfun + 
  carrier_bij

sublocale po_bij \<subseteq> rel_bij
  by (unfold_locales)

locale order_bij = 
  order_tfun + 
  carrier_bij

sublocale order_bij \<subseteq> po_bij
  by (unfold_locales) 

locale po_bij_embedding =
  po_embedding + 
  po_bij

begin

lemma finv_embeds:
    "(\<forall> x y | \<lch> x, y \<chIn> Y \<rch> \<bullet> x \<hookrightarrow>\<^sub>Y y \<Leftrightarrow> (f\<^sup>\<sim>)\<cdot>x \<preceq>\<^sub>X (f\<^sup>\<sim>)\<cdot>y)"
proof (intro allI impI)
  fix x y
  assume
    b1: "\<lch> x, y \<chIn> Y \<rch>"
  have 
    b3: "\<zdom> (f\<^sup>\<sim>) = Y"
    by (rule tfun_dom [of _ Y X], auto intro: f_bij)
  from b1 b3 have 
    b4: "x \<in> \<zdom> (f\<^sup>\<sim>)" 
    by (simp)
  from b1 b3 have 
    b5: "y \<in> \<zdom> (f\<^sup>\<sim>)" 
    by (simp)
  from b4 have 
    b6: "(f\<^sup>\<sim>)\<cdot>x \<in> X"
    apply (intro pfun_range [of _ Y X])
    apply (auto intro: f_bij)
    done
  from b5 have 
    b7: "(f\<^sup>\<sim>)\<cdot>y \<in> X"
    apply (intro pfun_range [of _ Y X])
    apply (auto intro: f_bij)
    done
  from f_bij b1 have 
      "x \<hookrightarrow>\<^sub>Y y 
      \<Leftrightarrow> f\<cdot>((f\<^sup>\<sim>)\<cdot>x) \<hookrightarrow>\<^sub>Y f\<cdot>((f\<^sup>\<sim>)\<cdot>y)"
    by (simp)
  also from b1 embeds have "\<dots> 
      \<Leftrightarrow> (f\<^sup>\<sim>)\<cdot>x \<preceq>\<^sub>X (f\<^sup>\<sim>)\<cdot>y"
    by (auto intro: f_bij b6 b7)
  finally show 
      "x \<hookrightarrow>\<^sub>Y y \<Leftrightarrow> (f\<^sup>\<sim>)\<cdot>x \<preceq>\<^sub>X (f\<^sup>\<sim>)\<cdot>y"
    by (this)
qed
  
lemma embed_ord:
    "x \<hookrightarrow>\<^sub>Y y \<Leftrightarrow> x \<in> Y \<and> y \<in> Y \<and> (f\<^sup>\<sim>)\<cdot>x \<preceq>\<^sub>X (f\<^sup>\<sim>)\<cdot>y"
  using finv_embeds Y.rel
  by (auto simp add: rel_def op2rel_def eind_def)

theorem iso_poI: 
    "\<^poset>{:Y:}{:(op \<hookrightarrow>\<^sub>Y):}"
proof -
  have 
    a1: "f \<in> X \<ztfun> Y" 
    by (auto intro: f_bij)
  have 
    a2: "f\<^sup>\<sim> \<in> Y \<ztfun> X" 
    by (auto intro: f_bij)
  from a1 a2 have 
    a3: "((f\<^sup>\<sim>) \<zfcomp> f) \<in> Y \<ztfun> Y" 
    by (auto)
  from f_bij have 
    a6: "\<forall> y \<bullet> y \<in> Y \<Rightarrow> (f\<^sup>\<sim>)\<cdot>y \<in> X"
    by (auto)
  show 
      ?thesis
  proof (rule partial_orderI)
    from non_empty obtain x where 
      c1: "x \<in> X" 
      by (auto)
    with f_bij have 
        "f\<cdot>x \<in> Y" 
      by (auto)
    then show 
        "Y \<noteq> \<emptyset>" 
      by (auto)
  next
    from Y.rel show 
        "\<^oprel>{:(op \<hookrightarrow>\<^sub>Y):} \<in> Y \<zrel> Y" 
      by (this)
  next
    fix y assume 
        "y \<in> Y"
    with reflD embed_ord a6 show 
        "y \<hookrightarrow>\<^sub>Y y"
      by (auto)
  next
    fix x y z 
    assume 
      c1: "x \<in> Y \<and> y \<in> Y \<and> z \<in> Y" and
      c2: "x \<hookrightarrow>\<^sub>Y y" "y \<hookrightarrow>\<^sub>Y z" 
    with embed_ord a6 show 
        "x \<hookrightarrow>\<^sub>Y z"
      by (auto intro: transD)
  next
    fix x y
    assume 
      c1: "x \<in> Y \<and> y \<in> Y" and
      c2: "x \<hookrightarrow>\<^sub>Y y" "y \<hookrightarrow>\<^sub>Y x" 
    with embed_ord a6 show 
        "x = y"
    proof (auto)
      assume 
          "(f\<^sup>\<sim>)\<cdot>x \<preceq>\<^sub>X (f\<^sup>\<sim>)\<cdot>y" "(f\<^sup>\<sim>)\<cdot>y \<preceq>\<^sub>X (f\<^sup>\<sim>)\<cdot>x"
      then have 
          "(f\<^sup>\<sim>)\<cdot>x = (f\<^sup>\<sim>)\<cdot>y" 
        by (rule antisymD)
      then have 
          "f\<cdot>((f\<^sup>\<sim>)\<cdot>x) = f\<cdot>((f\<^sup>\<sim>)\<cdot>y)"
        by (simp)
      with f_bij c1 show 
          "x = y" 
        by (simp)
    qed
  qed
qed

end (* po_bij_embedding *)

sublocale po_bij_embedding \<subseteq> Y_partial_order Y
  apply (rule Y_partial_order.intro)
  apply (rule iso_poI)
  done

locale order_bij_embedding =
  X_order +
  po_bij_embedding

begin

theorem iso_orderI:
    "\<^order>{:Y:}{:(op \<preceq>\<^sub>Y):}"
proof (rule Y.orderIa)
  fix 
    x y
  assume 
    b1: "x \<in> Y" "y \<in> Y"
  with f_bij have 
      "(f\<^sup>\<sim>)\<cdot>x \<in> X" "(f\<^sup>\<sim>)\<cdot>y \<in> X"
    by (auto)
  then have 
      "(f\<^sup>\<sim>)\<cdot>x \<preceq>\<^sub>X (f\<^sup>\<sim>)\<cdot>y \<or> (f\<^sup>\<sim>)\<cdot>y \<preceq>\<^sub>X (f\<^sup>\<sim>)\<cdot>x"
    by (rule linD)
  with b1 show 
      "x \<preceq>\<^sub>Y y \<or> y \<preceq>\<^sub>Y x"
    by (simp add: embed_ord)
qed

end

sublocale order_bij_embedding \<subseteq> Y_order
  apply (rule Y_order.intro)
  apply (rule iso_orderI)
  done

text {*

An isomorphism can also be used to induce an order on a set.

*}

definition
  image_ord :: "['a orderT, ('a \<times> 'b) set] \<rightarrow> 'b orderT"
where
  image_ord_def: "image_ord BS_leq f \<defs> \<^relop>{:{a b | \<^infopa>{:a:}{:BS_leq:}{:b:} \<bullet> f\<cdot>a \<mapsto> f\<cdot>b}:}"

notation (zed)
  image_ord ("\<^imgord>{:_:}{:_:}")

context rel_tfun

begin

abbreviation
  Y_image_ord :: "'b orderT" (infixl "\<hookrightarrow>\<^sub>f" 50)
where
  "Y_image_ord \<defs> \<^imgord>{:(op \<hookrightarrow>\<^sub>X):}{:f:}"

end

lemma (in rel_tfun) image_rel:
    "rel_preserving X (op \<hookrightarrow>\<^sub>X) Y (op \<hookrightarrow>\<^sub>f) f"
proof (unfold_locales)
  show
      "\<^oprel>{:(op \<hookrightarrow>\<^sub>f):} \<in> Y \<zrel> Y"
    by (auto simp add: image_ord_def op2rel_def rel2op_def rel_def tfun_range [OF f_tfun] X.relD1 X.relD2)
next
  show
      "(\<forall> x y \<bullet> \<lch> x, y \<chIn> X \<rch> \<Rightarrow> (x \<hookrightarrow>\<^sub>X y \<Rightarrow> f\<cdot>x \<hookrightarrow>\<^sub>f f\<cdot>y))"
    by (auto simp add: image_ord_def rel2op_def)
qed

lemma (in rel_bij) image_bij: 
    "rel_embedding X (op \<hookrightarrow>\<^sub>X) Y (op \<hookrightarrow>\<^sub>f) f"
proof (unfold_locales)
  from image_rel interpret image_rel: rel_preserving X "(op \<hookrightarrow>\<^sub>X)" Y "(op \<hookrightarrow>\<^sub>f)" f
    by (this)
  show
      "\<^oprel>{:(op \<hookrightarrow>\<^sub>f):} \<in> Y \<zrel> Y"
    by (rule image_rel.Y.rel)
  show
      "(\<forall> x y \<bullet> \<lch> x, y \<chIn> X \<rch> \<Rightarrow> (x \<hookrightarrow>\<^sub>X y \<Leftrightarrow> f\<cdot>x \<hookrightarrow>\<^sub>f f\<cdot>y))"
  proof (auto simp add: image_ord_def rel2op_def)
    fix 
      x y a b
    assume
      c1: "x \<in> X" and
      c2: "y \<in> X" and
      c3: "f\<cdot>x = f\<cdot>a" and
      c4: "f\<cdot>y = f\<cdot>b" and
      c5: "a \<hookrightarrow>\<^sub>X b"
    have
        "x = a"
      apply (rule bij_inj [OF f_bij, OF c1 _ c3])
      apply (rule X.relD1 [OF c5])
      done
    moreover have
        "y = b"
      apply (rule bij_inj [OF f_bij, OF c2 _ c4])
      apply (rule X.relD2 [OF c5])
      done
    ultimately show 
        "x \<hookrightarrow>\<^sub>X y"
      by (simp add: c5)
  qed
qed

lemma (in po_bij) image_po:
    "po_bij_embedding X (op \<hookrightarrow>\<^sub>X) Y (op \<hookrightarrow>\<^sub>f) f"
proof -
  from image_bij interpret image_bij: rel_embedding X "(op \<hookrightarrow>\<^sub>X)" Y "(op \<hookrightarrow>\<^sub>f)" f
    by (this)
  show "po_bij_embedding X (op \<hookrightarrow>\<^sub>X) Y (op \<hookrightarrow>\<^sub>f) f"
    by (unfold_locales)
qed
   
(*
lemma (in setrel) image_embed: 
  assumes a1: "f \<in> X \<zbij> Y"
  shows "f \<in> \<^oembfun>{:X:}{:r:}{:Y:}{:\<^imgord>{:r:}{:f:}:}"
proof (auto intro: relD1 relD2 simp add: 
  image_ord_def po_embeds_def rel2op_def del: ex_simps)
  from a1 show "f \<in> X \<ztfun> Y" by (auto)
next
  fix x y a b
  assume a2: "x \<in> X" and a3: "y \<in> X" and
    a4a: "f\<cdot>x = f\<cdot>a" and a4b: "f\<cdot>y = f\<cdot>b" and
    a5: "\<^infop>{:a:}{:r:}{:b:}"
  note a4a
  also have "f\<cdot>x = f\<cdot>a \<Leftrightarrow> x = a"
    by (rule bij_1to1 [OF a1 a2 relD1 [OF a5]])
  finally have a6a: "x = a" by (this)
  note a4b
  also have "f\<cdot>y = f\<cdot>b \<Leftrightarrow> y = b"
    by (rule bij_1to1 [OF a1 a3 relD2 [OF a5]])
  finally have a6b: "y = b" by (this)
  from a5 a6a a6b show "\<^infop>{:x:}{:r:}{:y:}"
    by (simp)
qed
*)

lemma (in partial_order) image_poI:
  assumes
    f_bij: "f \<in> X \<zbij> Y"
  shows
    "\<^poset>{:Y:}{:\<^imgord>{:(op \<preceq>):}{:f:}:}"
  apply (rule po_bij_embedding.iso_poI [of X "(op \<preceq>)"])
  apply (rule po_bij.image_po)
  apply (unfold_locales)
  using non_empty f_bij tfun_range [of f X Y]
  apply (auto)
  done

theorem (in order_bij) image_order:
    "order_bij_embedding X (op \<preceq>\<^sub>X) Y (op \<hookrightarrow>\<^sub>f) f"
proof -
  from image_po interpret image_po: po_bij_embedding X "(op \<hookrightarrow>\<^sub>X)" Y "(op \<hookrightarrow>\<^sub>f)" f
    by (this)
  show
      ?thesis
    by (unfold_locales)
qed

lemma (in order) image_orderI:
  assumes 
    f_bij: "f \<in> X \<zbij> Y"
  shows 
    "\<^order>{:Y:}{:\<^imgord>{:(op \<preceq>):}{:f:}:}"
  apply (rule order_bij_embedding.iso_orderI [of X "(op \<preceq>)"])
  apply (rule order_bij.image_order)
  apply (unfold_locales)
  using non_empty f_bij tfun_range [of f X Y]
  apply (auto)
  done

section {* Inducing orders on typedefs *}

text {*

Typedefs are new types introduced as isomorphic images of existing
representation sets.
The definition of a type via a typedef not only introduces a new type,
but also injective mappings to and from its representation set.
If the representation set is ordered, these injections can be used to
induce an ordering on the new type which is isomorphic to that on the
representation set.

*}

definition
  induce_ord :: "['b \<rightarrow> 'a, 'a orderT] \<rightarrow> 'b orderT"
where
  induce_ord_def: "induce_ord Rep BS_leq \<defs> (\<olambda> x y \<bullet> BS_leq (Rep x) (Rep y))"

text {*

We observe that the abstraction function from a representation
set to its defined type is a bijection. 
And that the induced order is the corresponding
image order.

*}

lemma (in type_definition) Abs_graph_bij:
    "A \<zdres> (\<graphof> Abs) \<in> A \<zbij> \<univ>"
proof (auto intro!: in_tfunI in_pfunI in_relI 
  simp add: bij_tfun_conv dres_def graph_of_def glambda_def Domain_iff Range_iff)
  fix x y
  assume 
    "x \<in> A" "y \<in> A" "Abs x = Abs y"
  then show 
      "x = y"
    by (simp add: Abs_inject)
next
  fix x
  from Abs_onto_on show 
      "\<exists> y \<bullet> y \<in> A \<and> x = Abs y"
    by (auto)
qed

lemma (in type_definition) induce_image_ord:
  assumes 
    a1: "setrel A BS_leq"
  shows 
    "induce_ord Rep BS_leq = \<^imgord>{:BS_leq:}{:A \<zdres> (\<graphof> Abs):}"
proof -
  from a1 interpret
    b1: setrel A BS_leq
    by (auto simp add: setrel_def)
  show 
      ?thesis
    by (auto 
          intro!: ext exI 
          simp add: 
            image_ord_def induce_ord_def rel2op_def graph_of_def glambda_dres 
            glambda_beta b1.relD1 b1.relD2 Abs_inverse Rep_inverse)
qed

text {*

Thus we can immediately deduce that the default order on the set @{text A}
will induce an order on the type @{text A}. 
More generally,
we can deduce that any poset structure on the set @{text A} will
also induce an order structure on the type @{text A}.

*}

lemma typedefs_order_classI:
  assumes
    a1: "type_definition (Rep::('a::ord) \<rightarrow> 'b) Abs (A::'b set)" and
    a2: "\<^poset>{:A:}{:BS_leq_d_A:}" and
    a3: "((op \<le>)::('a::ord) orderT) = induce_ord Rep BS_leq_d_A" and
    a4: "((op <)::('a::ord) orderT) = derefl (op \<le>)"
  shows 
    "OFCLASS('a::ord, order_class)"
proof -
  from a1 interpret 
    b1: type_definition Rep Abs A
    by (auto simp add: type_definition_def)
  from a2 interpret 
    b2: partial_order A BS_leq_d_A
    by (auto simp add: partial_order_def)
  show 
      "OFCLASS('a::ord, order_class)"  
    apply (rule order_classI)
    apply (simp add: a3 b1.induce_image_ord [OF b2.setrel])
    apply (rule b2.image_poI)
    apply (rule b1.Abs_graph_bij)
    apply (simp add: a4)
    done
qed

lemma typedefs_linorder_classI:
  assumes
    a1: "type_definition (Rep::('a::ord) \<rightarrow> 'b) Abs (A::'b set)" and
    a2: "\<^order>{:A:}{:BS_leq_d_A:}" and
    a3: "((op \<le>)::('a::ord) orderT) = induce_ord Rep BS_leq_d_A" and
    a4: "((op <)::('a::ord) orderT) = derefl (op \<le>)"
  shows 
    "OFCLASS('a::ord, linorder_class)"
proof -
  from a1 interpret b1: type_definition Rep Abs A
    by (auto simp add: type_definition_def)
  from a2 interpret b2: order A BS_leq_d_A
    by (auto simp add: order_def)
  show "OFCLASS('a::ord, linorder_class)"
    apply (rule linorder_classI)
    apply (simp add: a3 b1.induce_image_ord [OF b2.setrel])
    apply (rule b2.image_orderI)
    apply (rule b1.Abs_graph_bij)
    apply (simp add: a4)
    done
qed

lemma epi_typedefs_order_classI:
  assumes
    a1: "epi_type_definition (Rep::('a::ord) \<rightarrow> 'b) Abs" and
    a2: "\<^poset>{:\<univ>-['b]:}{:BS_leq:}" and
    a3: "((op \<le>)::('a::ord) orderT) = induce_ord Rep BS_leq" and
    a4: "((op <)::('a::ord) orderT) = derefl (op \<le>)"
  shows 
    "OFCLASS('a::ord, order_class)"
proof -
  interpret ETD: epi_type_definition Rep Abs
    by (rule a1)
  show
    "OFCLASS('a, order_class)"
    apply (rule typedefs_order_classI)
    apply (rule ETD.type_definition_axioms)
    apply (simp_all add: a2 a3 a4 order_classD)
    done
qed

lemma epi_typedefs_linorder_classI:
  assumes
    a1: "epi_type_definition (Rep::('a::ord) \<rightarrow> 'b) Abs" and
    a2: "\<^order>{:\<univ>-['b]:}{:BS_leq:}" and
    a3: "((op \<le>)::('a::ord) orderT) = induce_ord Rep BS_leq" and
    a4: "((op <)::('a::ord) orderT) = derefl (op \<le>)"
  shows 
    "OFCLASS('a::ord, linorder_class)"
proof -
  interpret ETD: epi_type_definition Rep Abs
    by (rule a1)
  show
    "OFCLASS('a, linorder_class)"
    apply (rule typedefs_linorder_classI)
    apply (rule ETD.type_definition_axioms)
    apply (simp_all add: a2 a3 a4 linorder_classD)
    done
qed


section {* Monotonicity and order classes*}

text {*

Monotonic functions preserve ordering.

*}

definition
  monotonic_ops :: "(('A::order) \<rightarrow> ('B::order)) set" 
where
  monotonic_ops_def: "monotonic_ops \<defs> {p | mono p}"

notation (xsymbols output)
  monotonic_ops ("M")

notation (zed)
  monotonic_ops ("\<mh>")


lemma mhE:
  assumes 
    a1: "p \<in> \<mh>" "(\<And> A B \<bullet> A \<le> B \<turnstile> p A \<le> p B) \<turnstile> R"
  shows 
      "R"
  using a1
  by (auto simp add: monotonic_ops_def monoD)

lemma mhD:
    "p \<in> \<mh> \<turnstile> A \<le> B \<turnstile> p A \<le> p B"
  by (simp add: monotonic_ops_def monoD)

lemma mh_conv:
    "p \<in> \<mh> \<Leftrightarrow> mono p"
  by (simp add: monotonic_ops_def)

lemma mhI:
  assumes 
    a1: "\<And> A B \<bullet> A \<le> B \<turnstile> p A \<le> p B"
  shows 
      "p \<in> \<mh>"
  using a1
  by (simp add: monotonic_ops_def monoI)

text {*

Utility lemmas.

*}

lemma comp_mhI:
  assumes
    a1: "f \<in> \<mh>" and
    a2: "g \<in> \<mh>"
  shows
    "f \<circ> g \<in> \<mh>"
  apply (rule mhI)
  apply (auto simp add: mhD [OF a1] mhD [OF a2])
  done

lemma comp_mhI':
  assumes
    a1: "f \<in> \<mh>" and
    a2: "g \<in> \<mh>"
  shows
    "(\<olambda> x \<bullet> f (g x)) \<in> \<mh>"
  apply (rule mhI)
  apply (auto simp add: mhD [OF a1] mhD [OF a2])
  done

end

