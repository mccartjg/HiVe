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

theory Lattice_Instance 
  
imports 
  Order_Instances 
  Lattice_Class 
  Lattice_Morphism

begin

text {*

In this section we demonstrate the lattice properties of some important
type constructors.

*}

section {* The booleans *}

text {*

The booleans form a complete, Boolean lattice with a linear order.

*}

instantiation
  bool :: clattice

begin

definition
  linf_bool_def: "(op &&) \<defs> (\<olambda> (x::\<bool>) y \<bullet> x \<and> y)"

definition
  lsup_bool_def: "(op ||) \<defs> (\<olambda> (x::\<bool>) y \<bullet> x \<or> y)"

definition
  Inf_bool_def: "Inf \<defs> (\<olambda> (X::\<bool> set) \<bullet> (\<forall> x | x \<in> X \<bullet> x))"

definition
  Sup_bool_def: "Sup \<defs> (\<olambda> (X::\<bool> set) \<bullet> (\<exists> x | x \<in> X \<bullet> x))"

definition
  bot_bool_def: "bot \<defs> \<False>"

definition
  top_bool_def: "top \<defs> \<True>"

instance
  apply (intro_classes)
  apply (unfold  le_bool_def linf_bool_def lsup_bool_def Inf_bool_def Sup_bool_def bot_bool_def top_bool_def)
  apply (fast+)
  done

end

instantiation
  bool :: boollattice
begin

definition
  lcomp_bool_def: "ocomp \<defs> Not"

instance
  apply (intro_classes)
  apply (unfold  linf_bool_def lsup_bool_def bot_bool_def top_bool_def lcomp_bool_def)
  apply (fast+)
  done

end

lemmas lat_bool_defs = 
  linf_bool_def lsup_bool_def
  Inf_bool_def Sup_bool_def
  bot_bool_def top_bool_def lcomp_bool_def

lemma [simp]:
    "\<lbot> \<Leftrightarrow> \<False>"
    "\<ltop> \<Leftrightarrow> \<True>"
    "a \<linf> b \<Leftrightarrow> a \<and> b"
    "a \<lsup> b \<Leftrightarrow> a \<or> b"
    "(\<lINF> x | BS_phi x \<bullet> f x) \<Leftrightarrow> (\<forall> x | BS_phi x \<bullet> f x)"
    "(\<lSUP> x | BS_phi x \<bullet> f x) \<Leftrightarrow> (\<exists> x | BS_phi x \<bullet> f x)"
    "\<lcomp> a \<Leftrightarrow> \<not>a"
  by (simp_all add: lat_bool_defs) 

section {* Product lattices *}

text {* The product constructor preserves all forms of lattices. *}

instantiation
  prod :: (lat, lat) lat
begin

definition
  inf_prod_def: "(op &&) \<defs> (\<olambda> (x, x') (y, y') \<bullet> (x && y, x' && y'))"

definition
  sup_prod_def: "(op ||) \<defs> (\<olambda> (x, x') (y, y') \<bullet> (x || y, x' || y'))"

instance
  by (intro_classes)

end

instantiation
  prod :: (blat, blat) blat
begin

definition
  bot_prod_def: "bot \<defs> (bot, bot)"

definition
  top_prod_def: "top \<defs> (top, top)"

instance
  by (intro_classes)

end

instantiation
  prod :: (clat, clat) clat
begin

definition
  Inf_prod_def: "Inf \<defs> (\<olambda> P \<bullet> (Inf { x | x \<in> P \<bullet> \<fst> x}, Inf { x | x \<in> P \<bullet> \<snd> x}))"

definition
  Sup_prod_def: "Sup \<defs> (\<olambda> P \<bullet> (Sup { x | x \<in> P \<bullet> \<fst> x}, Sup { x | x \<in> P \<bullet> \<snd> x}))"

instance
  by (intro_classes)

end

instantiation
  prod :: (bllat, bllat) bllat
begin

definition
  comp_prod_def: "ocomp \<defs> (\<olambda> (x, y) \<bullet> (ocomp x, ocomp y))"

instance
  by (intro_classes)

end

instance
  prod :: (lattice, lattice) lattice
  apply (intro_classes)
  apply (auto intro!: inf_lb1 inf_lb2 inf_glb sup_ub1 sup_ub2 sup_lub simp add: inf_prod_def sup_prod_def less_eq_prod_def product_order_def)
  done

instance
  prod :: (boundlattice, boundlattice) boundlattice
  apply (intro_classes)
  apply (auto simp add: bot_prod_def top_prod_def less_eq_prod_def product_order_def bot_lb top_ub)
  done

instance
  prod :: (clattice, clattice) clattice
  apply (intro_classes)
  apply (auto intro!: Inf_lb Sup_ub Inf_glb Sup_lub inf_eq sup_eq bot_eq top_eq simp add: less_eq_prod_def product_order_def Inf_prod_def Sup_prod_def)
  done

instance
  prod :: (dlattice, dlattice) dlattice
  by (intro_classes, auto simp add: inf_prod_def sup_prod_def sup_dist)

instance
  prod :: (boollattice, boollattice) boollattice
  apply (intro_classes)
  apply (auto simp add: comp_prod_def inf_prod_def sup_prod_def bot_prod_def top_prod_def comp_inf comp_sup)
  done

section {* Operator lattices *}

text {*

The function constructor preserves all forms of lattices structure in
its range type.

*}

instantiation
  "fun" :: (type, lat) lat
begin

definition
  linf_fun_def: "(op &&) \<defs> (\<olambda> f g x \<bullet> (f x) && (g x))"

definition
  lsup_fun_def: "(op ||) \<defs> (\<olambda> f g x \<bullet> (f x) || (g x))"

instance
  by (intro_classes)

end

instantiation
  "fun" :: (type, blat) blat
begin

definition
  bot_fun_def: "bot \<defs> (\<olambda> x \<bullet> bot)"

definition
  top_fun_def: "top \<defs> (\<olambda> x \<bullet> top)"

instance
  by (intro_classes)

end

instantiation
  "fun" :: (type, clat) clat
begin

definition
  Inf_fun_def: "Inf \<defs> (\<olambda> P x \<bullet> Inf { f | f \<in> P \<bullet> f x })"

definition
  Sup_fun_def: "Sup \<defs> (\<olambda> P x \<bullet> Sup { f | f \<in> P \<bullet> f x })"

instance
  by (intro_classes)

end

instantiation
  "fun" :: (type, bllat) bllat
begin

definition
  lcomp_fun_def: "ocomp \<defs> (\<olambda> f x \<bullet> ocomp (f x))"

instance
  by (intro_classes)

end

instance
  "fun" :: (type, lattice) lattice
  apply (intro_classes)
  apply (auto intro!: inf_lb1 inf_lb2 sup_ub1 sup_ub2 inf_glb sup_lub simp add: linf_fun_def lsup_fun_def le_fun_conv)
  done

lemma inf_mono_fun:
  "\<lbrakk> mono (f::('a::order) \<rightarrow> ('b::lattice)); mono g \<rbrakk> \<turnstile> mono (f \<linf> g)"
proof (simp (no_asm) add: mono_def linf_fun_def, auto)
  fix A::'a and B::'a
  assume a1: "mono f" and
    a2: "mono g" and
    a3: "A \<le> B"
  show "f A \<linf> g A \<le> f B \<linf> g B"
    by (intro inf_mono a1 [THEN monoD] a2 [THEN monoD] a3)
qed
  
lemma sup_mono_fun:
  "\<lbrakk> mono (f::('a::order) \<rightarrow> ('b::lattice)); mono g \<rbrakk> \<turnstile> mono (f \<lsup> g)"
proof (simp (no_asm) add: mono_def lsup_fun_def, auto)
  fix A::'a and B::'a
  assume a1: "mono f" and
    a2: "mono g" and
    a3: "A \<le> B"
  show "f A \<lsup> g A \<le> f B \<lsup> g B"
    by (intro sup_mono a1 [THEN monoD] a2 [THEN monoD] a3)
qed

instance
  "fun" :: (type, boundlattice) boundlattice
  apply (intro_classes)
  apply (auto intro!: bot_lb top_ub simp add: le_fun_conv bot_fun_def top_fun_def)
  done

instance
  "fun" :: (type, clattice) clattice
  apply (intro_classes)
  apply (auto intro!: Inf_lb Inf_glb Sup_ub Sup_lub inf_eq sup_eq bot_eq top_eq simp add: le_fun_conv Inf_fun_def Sup_fun_def)
  done

lemma Inf_mono_fun:
  assumes a1: "(\<And> x \<bullet> P x \<turnstile> mono ((f::'c \<rightarrow> ('a::order) \<rightarrow> ('b::clattice)) x))"
  shows "mono (\<lINF> x | P x \<bullet> f x)"
proof (simp only: mono_def Inf_fun_def, auto)
  fix A::'a and B::'a
  assume b1: "A \<le> B"
  show "(\<lINF> x | P x \<bullet> f x A) \<le> (\<lINF> x | P x \<bullet> f x B)"
  proof (rule Inf_glb, auto)
    fix x assume c1: "P x"
    show "(\<lINF> x | P x \<bullet> f x A) \<le> f x B"
      by (rule order_trans [of _ "f x A"], rule Inf_lb)
        (auto simp add: c1 intro!: b1 a1 [THEN monoD])
  qed
qed

lemma Sup_mono_fun:
  assumes a1: "(\<And> x \<bullet> P x \<turnstile> mono ((f::'c \<rightarrow> ('a::order) \<rightarrow> ('b::clattice)) x))" 
  shows "mono (\<lSUP> x | P x \<bullet> f x)"
proof (simp only: mono_def Sup_fun_def, auto)
  fix A::'a and B::'a
  assume b1: "A \<le> B"
  show "(\<lSUP> x | P x \<bullet> f x A) \<le> (\<lSUP> x | P x \<bullet> f x B)"
  proof (rule Sup_lub, auto)
    fix x assume c1: "P x"
    show "f x A \<le> (\<lSUP> x | P x \<bullet> f x B)"
      by (rule order_trans [of _ "f x B"])
        (auto simp add: c1 intro!: Sup_ub b1 a1 [THEN monoD])
  qed
qed

instance
  "fun" :: (type, dlattice) dlattice
  by (intro_classes, rule ext, simp add: linf_fun_def lsup_fun_def sup_dist)

instance
  "fun" :: (type, boollattice) boollattice
  apply (intro_classes)
  apply (auto simp add:  lcomp_fun_def linf_fun_def lsup_fun_def bot_fun_def top_fun_def comp_inf comp_sup)
  done

lemmas lat_fun_defs = 
  linf_fun_def lsup_fun_def Inf_fun_def Sup_fun_def
  bot_fun_def top_fun_def lcomp_fun_def

lemma [simp]:
    "(f \<linf> g) x = f x \<linf> g x"
    "(f \<lsup> g) x = f x \<lsup> g x"
  by (simp_all add: lat_fun_defs)

lemma [simp]:
    "(\<lINF> a | p a \<bullet> f a) x = (\<lINF> a | p a \<bullet> f a x)"
    "(\<lSUP> a | p a \<bullet> f a) x = (\<lSUP> a | p a \<bullet> f a x)"
  by (simp_all add: lat_fun_defs)

lemma [simp]:
    "\<lbot> x = \<lbot>"
    "\<ltop> x = \<ltop>"
  by (simp_all add: lat_fun_defs)

lemma [simp]:
    "(\<lcomp> f) x = \<lcomp> (f x)"
  by (simp_all add: lat_fun_defs)

text {*

The monotonic lattice functions form a complete sub-lattice.

*}

lemma bot_mh [msimp(wind)]:
  "\<lbot> \<in> \<mh>"
  by (auto intro!: mhI simp add: bot_fun_def)

lemma top_mh [msimp(wind)]:
  "\<ltop> \<in> \<mh>"
  by (auto intro!: mhI simp add: top_fun_def)

lemma inf_mh [msimp(wind)]:
  "\<lbrakk> p \<in> \<mh>; q \<in> \<mh> \<rbrakk> \<turnstile> p \<linf> q \<in> \<mh>"
  by (auto intro!: mhI dest!: mhD simp add: inf_mono linf_fun_def)

lemma sup_mh [msimp(wind)]:
  "\<lbrakk> p \<in> \<mh>; q \<in> \<mh> \<rbrakk> \<turnstile> (p \<lsup> q) \<in> \<mh>"
  by (auto intro!: mhI dest!: mhD simp add: sup_mono lsup_fun_def)

lemma Inf_mh [msimp(wind)]:
  assumes
    a1: "(\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mh>)"
  shows
    "\<lInf>CL_P \<in> \<mh>"
  apply (rule mhI)
  apply (simp add: Inf_fun_def le_fun_def)
  apply (rule QTInf_dom)
  apply (auto simp add: mhD [OF a1])
  done

lemma Sup_mh [msimp(wind)]:
  assumes
    a1: "(\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mh>)"
  shows
    "\<lSup>CL_P \<in> \<mh>"
  apply (rule mhI)
  apply (simp add: Sup_fun_def le_fun_def)
  apply (rule QTSup_dom)
  apply (auto simp add: mhD [OF a1])
  done
  
lemma pth_clat: 
    "\<^clattice>{:\<mh>-['A::Lattice_Class.clattice, 'B::Lattice_Class.clattice]:}{:\<^subord>{:(op \<le>):}{:\<mh>:}:}"
  apply (rule sub_clattice.subclatticeI' [of "\<univ>"])
  apply (auto intro!: Inf_mh Sup_mh simp add: Inf_Meet Sup_Join)
  apply (unfold_locales)
  apply (auto intro!: exI bot_mh simp add: nempty_conv)
  done

text {*

The bot/top-morphic operators also form complete lattices

*}

lemma bot_mhb:
    "\<lbot> \<in> \<mhb>"
  apply (rule mhbI)
  apply (rule bot_mh)
  apply (simp)
  done

text {*

The top of the bot-morphic lattice returns top everywhere except for bot, where 
it returns bot.

*}

definition
  mk_mhb :: "(('a::boundlattice) \<rightarrow> ('b::boundlattice)) \<rightarrow> (('a::boundlattice) \<rightarrow> ('b::boundlattice))"
where
  mk_mhb_def: "mk_mhb \<defs> (\<olambda> p A \<bullet> \<if> A = \<lbot> \<then> \<lbot> \<else> p A \<fi>)"

lemma mk_mhb_mhb:
  assumes 
    a1: "p \<in> \<mh>"
  shows
    "mk_mhb p \<in> \<mhb>"
  apply (unfold mk_mhb_def)
  apply (rule mhbI)
  apply (rule mhI) 
  apply (auto simp add: mhD [OF a1] bot_lb bot_min)
  done

lemma mk_mhb_lb:
    "mk_mhb p \<lle> p"
  by (simp add: mk_mhb_def le_fun_def bot_lb)

lemma mk_mhb_glb:
  assumes 
    a1: "q \<in> \<mhb>" and
    a2: "q \<lle> p"
  shows
    "q \<lle> mk_mhb p"
  using a2
  by (simp add: mk_mhb_def le_fun_def bot_min mhbD [OF a1])

definition
  top_b :: "('a::boundlattice) \<rightarrow> ('b::boundlattice)"
where
  top_b_def: "top_b \<defs> mk_mhb \<ltop>"

notation (xsymbols output)
  top_b ("\<top>\<^sub>b")

notation (zed)
  top_b ("\<ltopb>")

lemma top_b_mh:
    "\<ltopb> \<in> \<mh>"
  apply (unfold top_b_def)
  apply (rule mk_mhb_mhb [THEN mhbDm])
  apply (rule top_mh)
  done

lemma top_b_mhb:
    "\<ltopb> \<in> \<mhb>"
  apply (unfold top_b_def)
  apply (rule mk_mhb_mhb)
  apply (rule top_mh)
  done

lemma top_b_ub:
  assumes
    a1: "p \<in> \<mhb>"
  shows
    "p \<lle> \<ltopb>"
  apply (unfold top_b_def)
  apply (rule mk_mhb_glb)
  apply (auto simp add: a1 top_ub)
  done

lemma inf_mhb:
  assumes
    a1: "p \<in> \<mhb>" and
    a2: "q \<in> \<mhb>"
  shows
    "p \<linf> q \<in> \<mhb>"
  apply (rule mhbI)
  apply (simp add: inf_mh mhbDm a1 a2)
  apply (simp add: mhbD [OF a1] mhbD [OF a2] lat_bounds)
  done

lemma Inf_mhb:
  assumes
    a1: "CL_P \<noteq> \<emptyset>" and
    a2: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mhb>"
  shows
    "\<lInf> CL_P \<in> \<mhb>"
  apply (rule mhbI)
  apply (simp add: Inf_mh [of CL_P] mhbDm [OF a2])
proof -
  have 
      "(\<lInf>CL_P) \<lbot> 
      = (\<lINF> p | p \<in> CL_P \<bullet> p \<lbot>)"
    by (simp add: Inf_fun_def)
  also have "\<dots>
      = (\<lINF> p | p \<in> CL_P \<bullet> \<lbot>)"
    by (mauto(wind) mintro!: arg_cong [of _ _ "\<lInf>"] msimp add: mhbD [OF a2])
  also from a1 have 
      "{ p | p \<in> CL_P \<bullet> \<lbot> }
      = {\<lbot>}"
    by (auto)
  also have 
      "\<lInf>{\<lbot>}
      = \<lbot>"
    by (simp add: Inf_singleton)
  finally show
      "(\<lInf>CL_P) \<lbot> = \<lbot>"
    by (this)
qed

lemma sup_mhb:
  assumes
    a1: "p \<in> \<mhb>" and
    a2: "q \<in> \<mhb>"
  shows
    "p \<lsup> q \<in> \<mhb>"
  apply (rule mhbI)
  apply (simp add: sup_mh mhbDm a1 a2)
  apply (simp add: mhbD [OF a1] mhbD [OF a2] lat_bounds)
  done

lemma Sup_mhb:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mhb>"
  shows
    "\<lSup> CL_P \<in> \<mhb>"
  apply (rule mhbI)
  apply (simp add: Sup_mh mhbDm [OF a1])
proof -
  have 
      "(\<lSup>CL_P) \<lbot> 
      = (\<lSUP> p | p \<in> CL_P \<bullet> p \<lbot>)"
    by (simp add: Sup_fun_def)
  also have "\<dots>
      = (\<lSUP> p | p \<in> CL_P \<bullet> \<lbot>)"
    by (mauto(wind) mintro!: arg_cong [of _ _ "\<lSup>"] msimp add: mhbD [OF a1])
  also have "\<dots>
      = \<lbot>"
    apply (simp add: Sup_bot_unique)
    apply (auto)
    done
  finally show
      "(\<lSup>CL_P) \<lbot> = \<lbot>"
    by (this)
qed

text {*

The bottom of the top-morphic lattice returns bottom everywhere, except at top, where it returns top.

*}


definition
  mk_mht :: "(('a::boundlattice) \<rightarrow> ('b::boundlattice)) \<rightarrow> (('a::boundlattice) \<rightarrow> ('b::boundlattice))"
where
  mk_mht_def: "mk_mht \<defs> (\<olambda> p A \<bullet> \<if> A = \<ltop> \<then> \<ltop> \<else> p A \<fi>)"

lemma mk_mht_mht:
  assumes 
    a1: "p \<in> \<mh>"
  shows
    "mk_mht p \<in> \<mht>"
  apply (unfold mk_mht_def)
  apply (rule mhtI)
  apply (rule mhI) 
  apply (auto simp add: mhD [OF a1] top_ub top_max)
  done

lemma mk_mht_ub:
    "p \<lle> mk_mht p"
  by (simp add: mk_mht_def le_fun_def top_ub)

lemma mk_mht_lub:
  assumes 
    a1: "q \<in> \<mht>" and
    a2: "p \<lle> q"
  shows
    "mk_mht p \<lle> q"
  using a2
  by (simp add: mk_mht_def le_fun_def top_max mhtD [OF a1])

definition
  bot_t :: "('a::boundlattice) \<rightarrow> ('b::boundlattice)"
where
  bot_t_def: "bot_t \<defs> mk_mht \<lbot>"

notation (xsymbols output)
  bot_t ("\<bottom>\<^sub>t")

notation (zed)
  bot_t ("\<lbott>")

lemma bot_t_mh:
    "\<lbott> \<in> \<mh>"
  apply (unfold bot_t_def)
  apply (rule mk_mht_mht [THEN mhtDm])
  apply (rule bot_mh)
  done

lemma bot_t_mht:
    "\<lbott> \<in> \<mht>"
  apply (unfold bot_t_def)
  apply (rule mk_mht_mht)
  apply (rule bot_mh)
  done

lemma bot_t_lb:
  assumes
    a1: "p \<in> \<mht>"
  shows
    "\<lbott> \<lle> p"
  apply (unfold bot_t_def)
  apply (rule mk_mht_lub)
  apply (auto simp add: a1 bot_lb)
  done

lemma top_mht:
    "\<ltop> \<in> \<mht>"
  apply (rule mhtI)
  apply (rule top_mh)
  apply (simp)
  done

lemma inf_mht:
  assumes
    a1: "p \<in> \<mht>" and
    a2: "q \<in> \<mht>"
  shows
    "p \<linf> q \<in> \<mht>"
  apply (rule mhtI)
  apply (simp add: inf_mh mhtDm a1 a2)
  apply (simp add: mhtD [OF a1] mhtD [OF a2] lat_bounds)
  done

lemma sup_mht:
  assumes
    a1: "p \<in> \<mht>" and
    a2: "q \<in> \<mht>"
  shows
    "p \<lsup> q \<in> \<mht>"
  apply (rule mhtI)
  apply (simp add: sup_mh mhtDm a1 a2)
  apply (simp add: mhtD [OF a1] mhtD [OF a2] lat_bounds)
  done

lemma Inf_mht:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mht>"
  shows
    "\<lInf> CL_P \<in> \<mht>"
  apply (rule mhtI)
  apply (simp add: Inf_mh mhtDm [OF a1])
proof -
  have 
      "(\<lInf>CL_P) \<ltop> 
      = (\<lINF> p | p \<in> CL_P \<bullet> p \<ltop>)"
    by (simp add: Inf_fun_def)
  also have "\<dots>
      = (\<lINF> p | p \<in> CL_P \<bullet> \<ltop>)"
    by (mauto(wind) mintro!: arg_cong [of _ _ "\<lInf>"] msimp add: mhtD [OF a1])
  also have "\<dots>
      = \<ltop>"
    apply (simp add: Inf_top_unique)
    apply (auto)
    done
  finally show
      "(\<lInf>CL_P) \<ltop> = \<ltop>"
    by (this)
qed

lemma Sup_mht:
  assumes
    a1: "CL_P \<noteq> \<emptyset>" and
    a2: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mht>"
  shows
    "\<lSup> CL_P \<in> \<mht>"
  apply (rule mhtI)
  apply (simp add: Sup_mh [of CL_P] mhtDm [OF a2])
proof -
  have 
      "(\<lSup>CL_P) \<ltop> 
      = (\<lSUP> p | p \<in> CL_P \<bullet> p \<ltop>)"
    by (simp add: Sup_fun_def)
  also have "\<dots>
      = (\<lSUP> p | p \<in> CL_P \<bullet> \<ltop>)"
    by (mauto(wind) mintro!: arg_cong [of _ _ "\<lSup>"] msimp add: mhtD [OF a2])
  also from a1 have 
      "{ p | p \<in> CL_P \<bullet> \<ltop> }
      = {\<ltop>}"
    by (auto)
  also have 
      "\<lSup>{\<ltop>}
      = \<ltop>"
    by (simp add: Sup_singleton)
  finally show
      "(\<lSup>CL_P) \<ltop> = \<ltop>"
    by (this)
qed

text {*

The bot-morphic top and top-morphic bottom are also top-morphic and bot-morphic respectively.

*}

lemma top_b_mht:
  assumes
    a1: "\<lbot>-['A] \<noteq> \<ltop>-['A]"
  shows
    "\<ltopb> \<in> \<mht>-['A::boundlattice, 'B::boundlattice]"
  apply (unfold top_b_def mk_mhb_def)
  apply (rule mhtI)
  apply (rule mhI)
  apply (auto simp add: bot_min top_ub a1 a1 [symmetric])
  done

lemma bot_t_mhb:
  assumes
    a1: "\<lbot>-['A] \<noteq> \<ltop>-['A]"
  shows
    "\<lbott> \<in> \<mhb>-['A::boundlattice, 'B::boundlattice]"
  apply (unfold bot_t_def mk_mht_def)
  apply (rule mhbI)
  apply (rule mhI)
  apply (auto simp add: top_max top_ub a1 a1 [symmetric])
  done

text {* 

The inf/sup-morphic operators form (complete) semi-lattices in the monotonic operators.

*}

lemma bot_mhs:
    "\<lbot> \<in> \<mhs>"
  apply (rule mhsI)
  apply (simp add: lat_bounds)
  done

lemma top_mhs:
    "\<ltop> \<in> \<mhs>"
  apply (rule mhsI)
  apply (simp add: lat_bounds)
  done

lemma sup_mhs:
  assumes
    a1: "p \<in> \<mhs>" and
    a2: "q \<in> \<mhs>"
  shows
    "p \<lsup> q \<in> \<mhs>"
  apply (rule mhsI)
  apply (simp add: mhsD [OF a1] mhsD [OF a2] lat_com_assoc)
  done

lemma Sup_mhs:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_A \<turnstile> p \<in> \<mhs>"
  shows
    "\<lSup> CL_A \<in> \<mhs>"
proof (rule mhsI)
  fix A B
  have 
      "(\<lSup>CL_A) (A \<lsup> B)
      = (\<lSUP> p | p \<in> CL_A \<bullet> p (A \<lsup> B))"
    by (simp add: Sup_fun_def)
  also have "\<dots>
      = (\<lSUP> p | p \<in> CL_A \<bullet> p A \<lsup> p B)"
    by (mauto(wind) mintro!: arg_cong [of _ _ "\<lSup>"] msimp add: mhsD [OF a1])
  also have "\<dots> 
       = (\<lSup> ({ p | p \<in> CL_A \<bullet> p A } \<union> { p | p \<in> CL_A \<bullet> p B }))"
    by (simp add: Sup_sup')
  also have "\<dots> 
       = (\<lSup>CL_A) A \<lsup> (\<lSup>CL_A) B"
    by (simp add: Sup_fun_def Sup_sup)
  finally show 
      "(\<lSup>CL_A) (A \<lsup> B) = (\<lSup>CL_A) A \<lsup> (\<lSup>CL_A) B"
    by (this)
qed

text {*

The inf of sup-morphic operators is the sup of the sup-morphic lower bounds.

*}

definition
  gslb :: "(('a::lattice) \<rightarrow> ('b::clattice)) \<rightarrow> ('a \<rightarrow> 'b)"
where
  gslb_def: "gslb \<defs> (\<olambda> p \<bullet> (\<lSUP> t | t \<in> \<mhs> \<and> t \<lle> p))"

lemma gslb_mhs:
    "gslb p \<in> \<mhs>"
  apply (simp add: gslb_def)
  apply (rule Sup_mhs)
  apply (simp)
  done

lemma gslb_lb:
    "gslb p \<lle> p"
  apply (unfold gslb_def)
  apply (rule Sup_lub)
  apply (simp)
  done

lemma gslb_gslb:
  assumes
    a1: "q \<in> \<mhs>" and
    a2: "q \<lle> p"
  shows
    "q \<lle> gslb p"
  apply (unfold gslb_def)
  apply (rule Sup_ub)
  apply (simp add: a1 a2)
  done

definition
  inf_s :: "[('a::lattice) \<rightarrow> ('b::clattice), 'a \<rightarrow> 'b] \<rightarrow> ('a \<rightarrow> 'b)"
where
  inf_s_def: "inf_s \<defs> (\<olambda> p q \<bullet> gslb (p \<linf> q))"

notation (xsymbols output)
  inf_s (infixl "\<sqinter>\<^sub>s" 70)

notation (zed)
  inf_s (infixl "\<linfs>" 70)

lemma inf_s_mhs:
  assumes
    a1: "p \<in> \<mhs>" and
    a2: "q \<in> \<mhs>"
  shows
    "p \<linfs> q \<in> \<mhs>"
  apply (simp add: inf_s_def)
  apply (rule gslb_mhs)
  done

lemma inf_s_lb1:
    "p \<linfs> q \<lle> p"
  apply (unfold inf_s_def)
  apply (rule order_trans [OF gslb_lb inf_lb1])
  done

lemma inf_s_lb2:
    "p \<linfs> q \<lle> q"
  apply (unfold inf_s_def)
  apply (rule order_trans [OF gslb_lb inf_lb2])
  done

lemma inf_s_gslb:
  assumes
    a1: "t \<in> \<mhs>" and
    a2: "t \<lle> p" and
    a3: "t \<lle> q"
  shows
    "t \<lle> p \<linfs> q"
  apply (unfold inf_s_def)
  apply (rule gslb_gslb)
  apply (rule a1)
  apply (rule inf_glb [OF a2 a3])
  done

definition
  Inf_s :: "(('a::clattice) \<rightarrow> ('b::clattice)) set \<rightarrow> ('a \<rightarrow> 'b)"
where
  Inf_s_def: "Inf_s \<defs> (\<olambda> CL_P \<bullet> gslb (\<lInf> CL_P))"

notation (xsymbols output)
  Inf_s ("\<Sqinter>\<^sub>s")

notation (zed)
  Inf_s ("\<lInfs>")

lemma Inf_s_mhs:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mhs>"
  shows
    "\<lInfs> CL_P \<in> \<mhs>"
  apply (unfold Inf_s_def)
  apply (rule gslb_mhs)
  done

lemma Inf_s_lb:
  assumes
    a1: "p \<in> CL_P"
  shows
    "\<lInfs> CL_P \<lle> p"
  apply (unfold Inf_s_def)
  apply (rule order_trans [OF gslb_lb Inf_lb])
  apply (rule a1)
  done

lemma Inf_s_gslb:
  assumes
    a1: "t \<in> \<mhs>" and
    a2: "\<And> p \<bullet> p \<in> CL_P \<turnstile> t \<lle> p"
  shows
    "t \<lle> \<lInfs> CL_P"
  apply (unfold Inf_s_def)
  apply (rule gslb_gslb)
  apply (rule a1)
  apply (rule Inf_glb)
  apply (rule a2)
  apply (assumption)
  done

lemma bot_mhi:
    "\<lbot> \<in> \<mhi>"
  apply (rule mhiI)
  apply (simp add: lat_bounds)
  done

lemma top_mhi:
    "\<ltop> \<in> \<mhi>"
  apply (rule mhiI)
  apply (simp add: lat_bounds)
  done

lemma inf_mhi:
  assumes
    a1: "p \<in> \<mhi>" and
    a2: "q \<in> \<mhi>"
  shows
    "p \<linf> q \<in> \<mhi>"
  apply (rule mhiI)
  apply (simp add: mhiD [OF a1] mhiD [OF a2] lat_com_assoc)
  done

lemma Inf_mhi:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_A \<turnstile> p \<in> \<mhi>"
  shows
    "\<lInf> CL_A \<in> \<mhi>"
proof (rule mhiI)
  fix A B
  have 
      "(\<lInf>CL_A) (A \<linf> B)
      = (\<lINF> p | p \<in> CL_A \<bullet> p (A \<linf> B))"
    by (simp add: Inf_fun_def)
  also have "\<dots>
      = (\<lINF> p | p \<in> CL_A \<bullet> p A \<linf> p B)"
    by (mauto(wind) mintro!: arg_cong [of _ _ "\<lInf>"] msimp add: mhiD [OF a1])
  also have "\<dots> 
       = (\<lInf> ({ p | p \<in> CL_A \<bullet> p A } \<union> { p | p \<in> CL_A \<bullet> p B }))"
    by (simp add: Inf_inf')
  also have "\<dots> 
       = (\<lInf>CL_A) A \<linf> (\<lInf>CL_A) B"
    by (simp add: Inf_fun_def Inf_inf)
  finally show 
      "(\<lInf>CL_A) (A \<linf> B) = (\<lInf>CL_A) A \<linf> (\<lInf>CL_A) B"
    by (this)
qed

text {*

The sup of inf-morphic operators is the inf of the inf-morphic upper bounds.

*}

definition
  liub :: "(('a::lattice) \<rightarrow> ('b::clattice)) \<rightarrow> ('a \<rightarrow> 'b)"
where
  liub_def: "liub \<defs> (\<olambda> p \<bullet> (\<lINF> t | t \<in> \<mhi> \<and> p \<lle> t))"

lemma liub_mhi:
    "liub p \<in> \<mhi>"
  apply (simp add: liub_def)
  apply (rule Inf_mhi)
  apply (simp)
  done

lemma liub_ub:
    "p \<lle> liub p"
  apply (unfold liub_def)
  apply (rule Inf_glb)
  apply (simp)
  done

lemma liub_liub:
  assumes
    a1: "q \<in> \<mhi>" and
    a2: "p \<lle> q"
  shows
    "liub p \<lle> q"
  apply (unfold liub_def)
  apply (rule Inf_lb)
  apply (simp add: a1 a2)
  done

definition
  sup_i :: "[('a::lattice) \<rightarrow> ('b::clattice), 'a \<rightarrow> 'b] \<rightarrow> ('a \<rightarrow> 'b)"
where
  sup_i_def: "sup_i \<defs> (\<olambda> p q \<bullet> liub (p \<lsup> q))"

notation (xsymbols output)
  sup_i (infixl "\<squnion>\<^sub>i" 65)

notation (zed)
  sup_i (infixl "\<lsupi>" 65)

lemma sup_i_mhi:
  assumes
    a1: "p \<in> \<mhi>" and
    a2: "q \<in> \<mhi>"
  shows
    "p \<lsupi> q \<in> \<mhi>"
  apply (simp add: sup_i_def)
  apply (rule liub_mhi)
  done

lemma sup_i_ub1:
    "p \<lle> p \<lsupi> q"
  apply (unfold sup_i_def)
  apply (rule order_trans [OF sup_ub1 liub_ub])
  done

lemma sup_i_ub2:
    "q \<lle> p \<lsupi> q"
  apply (unfold sup_i_def)
  apply (rule order_trans [OF sup_ub2 liub_ub])
  done

lemma sup_i_liub:
  assumes
    a1: "t \<in> \<mhi>" and
    a2: "p \<lle> t" and
    a3: "q \<lle> t"
  shows
    "p \<lsupi> q \<lle> t"
  apply (unfold sup_i_def)
  apply (rule liub_liub)
  apply (rule a1)
  apply (rule sup_lub [OF a2 a3])
  done

definition
  Sup_i :: "(('a::clattice) \<rightarrow> ('b::clattice)) set \<rightarrow> ('a \<rightarrow> 'b)"
where
  Sup_i_def: "Sup_i \<defs> (\<olambda> CL_P \<bullet> liub (\<lSup> CL_P))"

notation (xsymbols output)
  Sup_i ("\<Squnion>\<^sub>i")

notation (zed)
  Sup_i ("\<lSupi>")

lemma Sup_i_mhs:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mhi>"
  shows
    "\<lSupi> CL_P \<in> \<mhi>"
  apply (unfold Sup_i_def)
  apply (rule liub_mhi)
  done

lemma Sup_i_lb:
  assumes
    a1: "p \<in> CL_P"
  shows
    "p \<lle> \<lSupi> CL_P"
  apply (unfold Sup_i_def)
  apply (rule order_trans [OF Sup_ub liub_ub])
  apply (rule a1)
  done

lemma Sup_i_liub:
  assumes
    a1: "t \<in> \<mhi>" and
    a2: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<lle> t"
  shows
    "\<lSupi> CL_P \<lle> t"
  apply (unfold Sup_i_def)
  apply (rule liub_liub)
  apply (rule a1)
  apply (rule Sup_lub)
  apply (rule a2)
  apply (assumption)
  done

text {* 

The Inf/Sup-morphic operators form (complete) semi-lattices in the monotonic operators.

*}

lemma bot_mhS:
    "\<lbot> \<in> \<mhS>"
  apply (rule mhSI)
  apply (simp add: lat_bounds nempty_conv Sup_singleton)
  done

lemma top_mhS:
    "\<ltop> \<in> \<mhS>"
  apply (rule mhSI)
  apply (simp add: lat_bounds nempty_conv Sup_singleton)
  done

lemma sup_mhS:
  assumes
    a1: "p \<in> \<mhS>" and
    a2: "q \<in> \<mhS>"
  shows
    "p \<lsup> q \<in> \<mhS>"
  apply (rule mhSI)
  apply (simp add: mhSD [OF a1] mhSD [OF a2] lat_com_assoc Sup_sup Sup_sup')
  done

lemma Sup_mhS:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_A \<turnstile> p \<in> \<mhS>"
  shows
    "\<lSup> CL_A \<in> \<mhS>"
proof (rule mhSI)
  fix CL_X::"'a set"
  assume
    b1: "CL_X \<noteq> \<emptyset>"
  have 
      "(\<lSup>CL_A) (\<lSup>CL_X)
      = (\<lSUP> p | p \<in> CL_A \<bullet> p (\<lSup>CL_X))"
    by (simp add: Sup_fun_def)
  also have "\<dots>
      = (\<lSUP> p | p \<in> CL_A \<bullet> (\<lSUP> x | x \<in> CL_X \<bullet> p x))"
    by (mauto(wind) mintro!: arg_cong [of _ _ "\<lSup>"] msimp add: mhSD [OF a1] b1)
  also have "\<dots> 
       = (\<lSUP> x | x \<in> CL_X \<bullet> (\<lSUP> p | p \<in> CL_A \<bullet> p x))"
    apply (simp add: Sup_Sup)
    apply (mauto(wind) mintro!: arg_cong [of _ _ "\<lSup>"])
    done
  also have "\<dots> 
       = (\<lSUP> x | x \<in> CL_X \<bullet> (\<lSup>CL_A) x)"
    by (simp add: Sup_fun_def)
  finally show 
      "(\<lSup>CL_A) (\<lSup>CL_X) = (\<lSUP> x | x \<in> CL_X \<bullet> (\<lSup>CL_A) x)"
    by (this)
qed

text {*

The inf of Sup-morphic operators is the sup of the Sup-morphic lower bounds.

*}

definition
  gSlb :: "(('a::clattice) \<rightarrow> ('b::clattice)) \<rightarrow> ('a \<rightarrow> 'b)"
where
  gSlb_def: "gSlb \<defs> (\<olambda> p \<bullet> (\<lSUP> t | t \<in> \<mhS> \<and> t \<lle> p))"

lemma gSlb_mhS:
    "gSlb p \<in> \<mhS>"
  apply (simp add: gSlb_def)
  apply (rule Sup_mhS)
  apply (simp)
  done

lemma gSlb_lb:
    "gSlb p \<lle> p"
  apply (unfold gSlb_def)
  apply (rule Sup_lub)
  apply (simp)
  done

lemma gSlb_gSlb:
  assumes
    a1: "q \<in> \<mhS>" and
    a2: "q \<lle> p"
  shows
    "q \<lle> gSlb p"
  apply (unfold gSlb_def)
  apply (rule Sup_ub)
  apply (simp add: a1 a2)
  done

definition
  inf_S :: "[('a::clattice) \<rightarrow> ('b::clattice), 'a \<rightarrow> 'b] \<rightarrow> ('a \<rightarrow> 'b)"
where
  inf_S_def: "inf_S \<defs> (\<olambda> p q \<bullet> gSlb (p \<linf> q))"

notation (xsymbols output)
  inf_S (infixl "\<sqinter>\<^sub>S" 70)

notation (zed)
  inf_S (infixl "\<linfS>" 70)

lemma inf_S_mhS:
  assumes
    a1: "p \<in> \<mhS>" and
    a2: "q \<in> \<mhS>"
  shows
    "p \<linfS> q \<in> \<mhS>"
  apply (simp add: inf_S_def)
  apply (rule gSlb_mhS)
  done

lemma inf_S_lb1:
    "p \<linfS> q \<lle> p"
  apply (unfold inf_S_def)
  apply (rule order_trans [OF gSlb_lb inf_lb1])
  done

lemma inf_S_lb2:
    "p \<linfS> q \<lle> q"
  apply (unfold inf_S_def)
  apply (rule order_trans [OF gSlb_lb inf_lb2])
  done

lemma inf_S_gSlb:
  assumes
    a1: "t \<in> \<mhS>" and
    a2: "t \<lle> p" and
    a3: "t \<lle> q"
  shows
    "t \<lle> p \<linfS> q"
  apply (unfold inf_S_def)
  apply (rule gSlb_gSlb)
  apply (rule a1)
  apply (rule inf_glb [OF a2 a3])
  done

definition
  Inf_S :: "(('a::clattice) \<rightarrow> ('b::clattice)) set \<rightarrow> ('a \<rightarrow> 'b)"
where
  Inf_S_def: "Inf_S \<defs> (\<olambda> CL_P \<bullet> gSlb (\<lInf> CL_P))"

notation (xsymbols output)
  Inf_S ("\<Sqinter>\<^sub>S")

notation (zed)
  Inf_S ("\<lInfS>")

lemma Inf_S_mhS:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mhS>"
  shows
    "\<lInfS> CL_P \<in> \<mhS>"
  apply (unfold Inf_S_def)
  apply (rule gSlb_mhS)
  done

lemma Inf_S_lb:
  assumes
    a1: "p \<in> CL_P"
  shows
    "\<lInfS> CL_P \<lle> p"
  apply (unfold Inf_S_def)
  apply (rule order_trans [OF gSlb_lb Inf_lb])
  apply (rule a1)
  done

lemma Inf_S_gSlb:
  assumes
    a1: "t \<in> \<mhS>" and
    a2: "\<And> p \<bullet> p \<in> CL_P \<turnstile> t \<lle> p"
  shows
    "t \<lle> \<lInfS> CL_P"
  apply (unfold Inf_S_def)
  apply (rule gSlb_gSlb)
  apply (rule a1)
  apply (rule Inf_glb)
  apply (rule a2)
  apply (assumption)
  done

lemma bot_mhI:
    "\<lbot> \<in> \<mhI>"
  apply (rule mhII)
  apply (simp add: lat_bounds nempty_conv Inf_singleton)
  done

lemma top_mhI:
    "\<ltop> \<in> \<mhI>"
  apply (rule mhII)
  apply (simp add: lat_bounds nempty_conv Inf_singleton)
  done

lemma inf_mhI:
  assumes
    a1: "p \<in> \<mhI>" and
    a2: "q \<in> \<mhI>"
  shows
    "p \<linf> q \<in> \<mhI>"
  apply (rule mhII)
  apply (simp add: mhID [OF a1] mhID [OF a2] lat_com_assoc Inf_inf Inf_inf')
  done

lemma Inf_mhI:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_A \<turnstile> p \<in> \<mhI>"
  shows
    "\<lInf> CL_A \<in> \<mhI>"
proof (rule mhII)
  fix CL_X::"'a set"
  assume
    b1: "CL_X \<noteq> \<emptyset>"
  have 
      "(\<lInf>CL_A) (\<lInf>CL_X)
      = (\<lINF> p | p \<in> CL_A \<bullet> p (\<lInf>CL_X))"
    by (simp add: Inf_fun_def)
  also have "\<dots>
      = (\<lINF> p | p \<in> CL_A \<bullet> (\<lINF> x | x \<in> CL_X \<bullet> p x))"
    by (mauto(wind) mintro!: arg_cong [of _ _ "\<lInf>"] msimp add: mhID [OF a1] b1)
  also have "\<dots> 
       = (\<lINF> x | x \<in> CL_X \<bullet> (\<lINF> p | p \<in> CL_A \<bullet> p x))"
    apply (simp add: Inf_Inf)
    apply (mauto(wind) mintro!: arg_cong [of _ _ "\<lInf>"])
    done
  also have "\<dots> 
       = (\<lINF> x | x \<in> CL_X \<bullet> (\<lInf>CL_A) x)"
    by (simp add: Inf_fun_def)
  finally show 
      "(\<lInf>CL_A) (\<lInf>CL_X) = (\<lINF> x | x \<in> CL_X \<bullet> (\<lInf>CL_A) x)"
    by (this)
qed

text {*

The sup of Inf-morphic operators is the inf of the Inf-morphic upper bounds.

*}

definition
  lIub :: "(('a::clattice) \<rightarrow> ('b::clattice)) \<rightarrow> ('a \<rightarrow> 'b)"
where
  lIub_def: "lIub \<defs> (\<olambda> p \<bullet> (\<lINF> t | t \<in> \<mhI> \<and> p \<lle> t))"

lemma lIub_mhI:
    "lIub p \<in> \<mhI>"
  apply (simp add: lIub_def)
  apply (rule Inf_mhI)
  apply (simp)
  done

lemma lIub_ub:
    "p \<lle> lIub p"
  apply (unfold lIub_def)
  apply (rule Inf_glb)
  apply (simp)
  done

lemma lIub_lIub:
  assumes
    a1: "q \<in> \<mhI>" and
    a2: "p \<lle> q"
  shows
    "lIub p \<lle> q"
  apply (unfold lIub_def)
  apply (rule Inf_lb)
  apply (simp add: a1 a2)
  done

definition
  sup_I :: "[('a::clattice) \<rightarrow> ('b::clattice), 'a \<rightarrow> 'b] \<rightarrow> ('a \<rightarrow> 'b)"
where
  sup_I_def: "sup_I \<defs> (\<olambda> p q \<bullet> lIub (p \<lsup> q))"

notation (xsymbols output)
  sup_I (infixl "\<squnion>\<^sub>I" 65)

notation (zed)
  sup_I (infixl "\<lsupI>" 65)

lemma sup_I_mhI:
  assumes
    a1: "p \<in> \<mhI>" and
    a2: "q \<in> \<mhI>"
  shows
    "p \<lsupI> q \<in> \<mhI>"
  apply (simp add: sup_I_def)
  apply (rule lIub_mhI)
  done

lemma sup_I_ub1:
    "p \<lle> p \<lsupI> q"
  apply (unfold sup_I_def)
  apply (rule order_trans [OF sup_ub1 lIub_ub])
  done

lemma sup_I_ub2:
    "q \<lle> p \<lsupI> q"
  apply (unfold sup_I_def)
  apply (rule order_trans [OF sup_ub2 lIub_ub])
  done

lemma sup_I_lIub:
  assumes
    a1: "t \<in> \<mhI>" and
    a2: "p \<lle> t" and
    a3: "q \<lle> t"
  shows
    "p \<lsupI> q \<lle> t"
  apply (unfold sup_I_def)
  apply (rule lIub_lIub)
  apply (rule a1)
  apply (rule sup_lub [OF a2 a3])
  done

definition
  Sup_I :: "(('a::clattice) \<rightarrow> ('b::clattice)) set \<rightarrow> ('a \<rightarrow> 'b)"
where
  Sup_I_def: "Sup_I \<defs> (\<olambda> CL_P \<bullet> lIub (\<lSup> CL_P))"

notation (xsymbols output)
  Sup_I ("\<Squnion>\<^sub>I")

notation (zed)
  Sup_I ("\<lSupI>")

lemma Sup_I_mhI:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mhI>"
  shows
    "\<lSupI> CL_P \<in> \<mhI>"
  apply (unfold Sup_I_def)
  apply (rule lIub_mhI)
  done

lemma Sup_I_lb:
  assumes
    a1: "p \<in> CL_P"
  shows
    "p \<lle> \<lSupI> CL_P"
  apply (unfold Sup_I_def)
  apply (rule order_trans [OF Sup_ub lIub_ub])
  apply (rule a1)
  done

lemma Sup_I_lIub:
  assumes
    a1: "t \<in> \<mhI>" and
    a2: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<lle> t"
  shows
    "\<lSupI> CL_P \<lle> t"
  apply (unfold Sup_I_def)
  apply (rule lIub_lIub)
  apply (rule a1)
  apply (rule Sup_lub)
  apply (rule a2)
  apply (assumption)
  done

text {* 

The top-Inf/bot-Sup-morphic operators form (complete) semi-lattices in the monotonic operators.

*}

lemma bot_mhbS:
    "\<lbot> \<in> \<mhbS>"
  apply (rule mhbSI)
  apply (simp add: lat_bounds nempty_conv Sup_singleton)
  apply (intro allI bot_eq Sup_lub)
  apply (auto simp add: bot_lb)
  done

lemma sup_mhbS:
  assumes
    a1: "p \<in> \<mhbS>" and
    a2: "q \<in> \<mhbS>"
  shows
    "p \<lsup> q \<in> \<mhbS>"
  apply (rule mhbSI)
  apply (simp add: mhbSD [OF a1] mhbSD [OF a2] lat_com_assoc Sup_sup Sup_sup')
  done

lemma Sup_mhbS:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_A \<turnstile> p \<in> \<mhbS>"
  shows
    "\<lSup> CL_A \<in> \<mhbS>"
proof (rule mhbSI)
  fix CL_X::"'a set"
  have 
      "(\<lSup>CL_A) (\<lSup>CL_X)
      = (\<lSUP> p | p \<in> CL_A \<bullet> p (\<lSup>CL_X))"
    by (simp add: Sup_fun_def)
  also have "\<dots>
      = (\<lSUP> p | p \<in> CL_A \<bullet> (\<lSUP> x | x \<in> CL_X \<bullet> p x))"
    by (mauto(wind) mintro!: arg_cong [of _ _ "\<lSup>"] msimp add: mhbSD [OF a1])
  also have "\<dots> 
       = (\<lSUP> x | x \<in> CL_X \<bullet> (\<lSUP> p | p \<in> CL_A \<bullet> p x))"
    apply (simp add: Sup_Sup)
    apply (mauto(wind) mintro!: arg_cong [of _ _ "\<lSup>"])
    done
  also have "\<dots> 
       = (\<lSUP> x | x \<in> CL_X \<bullet> (\<lSup>CL_A) x)"
    by (simp add: Sup_fun_def)
  finally show 
      "(\<lSup>CL_A) (\<lSup>CL_X) = (\<lSUP> x | x \<in> CL_X \<bullet> (\<lSup>CL_A) x)"
    by (this)
qed

text {*

The top/inf/Inf of bot-Sup-morphic operators is the sup of the bot-Sup-morphic lower bounds.

*}

definition
  gbSlb :: "(('a::clattice) \<rightarrow> ('b::clattice)) \<rightarrow> ('a \<rightarrow> 'b)"
where
  gbSlb_def: "gbSlb \<defs> (\<olambda> p \<bullet> (\<lSUP> t | t \<in> \<mhbS> \<and> t \<lle> p))"

lemma gbSlb_mhbS:
    "gbSlb p \<in> \<mhbS>"
  apply (unfold gbSlb_def)
  apply (rule Sup_mhbS)
  apply (simp)
  done

lemma gbSlb_lb:
    "gbSlb p \<lle> p"
  apply (unfold gbSlb_def)
  apply (rule Sup_lub)
  apply (simp)
  done

lemma gbSlb_gbSlb:
  assumes
    a1: "q \<in> \<mhbS>" and
    a2: "q \<lle> p"
  shows
    "q \<lle> gbSlb p"
  apply (unfold gbSlb_def)
  apply (rule Sup_ub)
  using a1 a2
  apply (simp)
  done

definition
  top_bS :: "('a::clattice) \<rightarrow> ('b::clattice)"
where
  top_bS_def: "top_bS \<defs> gbSlb \<ltop>"

notation (xsymbols output)
  top_bS ("\<top>\<^sub>b\<^sub>S")

notation (zed)
  top_bS ("\<ltopbS>")

lemma top_bS_mhbS:
    "\<ltopbS> \<in> \<mhbS>"
  apply (unfold top_bS_def)
  apply (rule gbSlb_mhbS)
  done

lemma top_bS_ub:
  assumes 
    a1: "p \<in> \<mhbS>"
  shows
    "p \<lle> \<ltopbS>"
  apply (unfold top_bS_def)
  apply (rule gbSlb_gbSlb [OF a1])
  apply (rule top_ub)
  done

lemma top_bS_max:
  assumes 
    a1: "p \<in> \<mhbS>"
  shows
    "\<ltopbS> \<lle> p \<Leftrightarrow> p = \<ltopbS>"
  apply (auto)
  apply (rule order_antisym)
  apply (rule top_bS_ub [OF a1])
  apply (assumption)
  done

definition
  inf_bS :: "[('a::clattice) \<rightarrow> ('b::clattice), 'a \<rightarrow> 'b] \<rightarrow> ('a \<rightarrow> 'b)"
where
  inf_bS_def: "inf_bS \<defs> (\<olambda> p q \<bullet> gbSlb (p \<linf> q))"

notation (xsymbols output)
  inf_bS (infixl "\<sqinter>\<^sub>b\<^sub>S" 70)

notation (zed)
  inf_bS (infixl "\<linfbS>" 70)

lemma inf_bS_mhbS:
  assumes
    a1: "p \<in> \<mhbS>" and
    a2: "q \<in> \<mhbS>"
  shows
    "p \<linfbS> q \<in> \<mhbS>"
  apply (unfold inf_bS_def)
  apply (rule gbSlb_mhbS)
  done

lemma inf_bS_lb1:
    "p \<linfbS> q \<lle> p"
  apply (unfold inf_bS_def)
  apply (rule order_trans [OF gbSlb_lb inf_lb1])
  done

lemma inf_bS_lb2:
    "p \<linfbS> q \<lle> q"
  apply (unfold inf_bS_def)
  apply (rule order_trans [OF gbSlb_lb inf_lb2])
  done

lemma inf_bS_gbSlb:
  assumes
    a1: "t \<in> \<mhbS>" and
    a2: "t \<lle> p" and
    a3: "t \<lle> q"
  shows
    "t \<lle> p \<linfbS> q"
  apply (unfold inf_bS_def)
  apply (rule gbSlb_gbSlb)
  apply (rule a1)
  apply (rule inf_glb [OF a2 a3])
  done

definition
  Inf_bS :: "(('a::clattice) \<rightarrow> ('b::clattice)) set \<rightarrow> ('a \<rightarrow> 'b)"
where
  Inf_bS_def: "Inf_bS \<defs> (\<olambda> CL_P \<bullet> gbSlb (\<lInf> CL_P))"

notation (xsymbols output)
  Inf_bS ("\<Sqinter>\<^sub>b\<^sub>S")

notation (zed)
  Inf_bS ("\<lInfbS>")

lemma Inf_bS_mhbS:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mhbS>"
  shows
    "\<lInfbS> CL_P \<in> \<mhbS>"
  apply (unfold Inf_bS_def)
  apply (rule gbSlb_mhbS)
  done

lemma Inf_bS_lb:
  assumes
    a1: "p \<in> CL_P"
  shows
    "\<lInfbS> CL_P \<lle> p"
  apply (unfold Inf_bS_def)
  apply (rule order_trans [OF gbSlb_lb Inf_lb])
  apply (rule a1)
  done

lemma Inf_bS_gSlb:
  assumes
    a1: "t \<in> \<mhbS>" and
    a2: "\<And> p \<bullet> p \<in> CL_P \<turnstile> t \<lle> p"
  shows
    "t \<lle> \<lInfbS> CL_P"
  apply (unfold Inf_bS_def)
  apply (rule gbSlb_gbSlb)
  apply (rule a1)
  apply (rule Inf_glb)
  apply (rule a2)
  apply (assumption)
  done

lemma top_mhtI:
    "\<ltop> \<in> \<mhIt>"
  apply (rule mhItI)
  apply (simp add: lat_bounds nempty_conv Inf_singleton)
  apply (intro allI top_eq Inf_glb)
  apply (auto simp add: top_ub)
  done

lemma inf_mhIt:
  assumes
    a1: "p \<in> \<mhIt>" and
    a2: "q \<in> \<mhIt>"
  shows
    "p \<linf> q \<in> \<mhIt>"
  apply (rule mhItI)
  apply (simp add: mhItD [OF a1] mhItD [OF a2] lat_com_assoc Inf_inf Inf_inf')
  done

lemma Inf_mhIt:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_A \<turnstile> p \<in> \<mhIt>"
  shows
    "\<lInf> CL_A \<in> \<mhIt>"
proof (rule mhItI)
  fix CL_X::"'a set"
  have 
      "(\<lInf>CL_A) (\<lInf>CL_X)
      = (\<lINF> p | p \<in> CL_A \<bullet> p (\<lInf>CL_X))"
    by (simp add: Inf_fun_def)
  also have "\<dots>
      = (\<lINF> p | p \<in> CL_A \<bullet> (\<lINF> x | x \<in> CL_X \<bullet> p x))"
    by (mauto(wind) mintro!: arg_cong [of _ _ "\<lInf>"] msimp add: mhItD [OF a1])
  also have "\<dots> 
       = (\<lINF> x | x \<in> CL_X \<bullet> (\<lINF> p | p \<in> CL_A \<bullet> p x))"
    apply (simp add: Inf_Inf)
    apply (mauto(wind) mintro!: arg_cong [of _ _ "\<lInf>"])
    done
  also have "\<dots> 
       = (\<lINF> x | x \<in> CL_X \<bullet> (\<lInf>CL_A) x)"
    by (simp add: Inf_fun_def)
  finally show 
      "(\<lInf>CL_A) (\<lInf>CL_X) = (\<lINF> x | x \<in> CL_X \<bullet> (\<lInf>CL_A) x)"
    by (this)
qed

text {*

The sup of Inf-morphic operators is the inf of the Inf-morphic upper bounds.

*}

definition
  lItub :: "(('a::clattice) \<rightarrow> ('b::clattice)) \<rightarrow> ('a \<rightarrow> 'b)"
where
  lItub_def: "lItub \<defs> (\<olambda> p \<bullet> (\<lINF> t | t \<in> \<mhIt> \<and> p \<lle> t))"

lemma lItub_mhIt:
    "lItub p \<in> \<mhIt>"
  apply (unfold lItub_def)
  apply (rule Inf_mhIt)
  apply (simp)
  done

lemma lItub_ub:
    "p \<lle> lItub p"
  apply (unfold lItub_def)
  apply (rule Inf_glb)
  apply (simp)
  done

lemma lItub_lItub:
  assumes
    a1: "q \<in> \<mhIt>" and
    a2: "p \<lle> q"
  shows
    "lItub p \<lle> q"
  apply (unfold lItub_def)
  apply (rule Inf_lb)
  using a1 a2
  apply (simp)
  done

definition
  bot_It :: "('a::clattice) \<rightarrow> ('b::clattice)"
where
  bot_It_def: "bot_It \<defs> lItub \<lbot>"

notation (xsymbols output)
  bot_It ("\<bottom>\<^sub>I\<^sub>t")

notation (zed)
  bot_It ("\<lbotIt>")

lemma bot_It_mhIt:
    "\<lbotIt> \<in> \<mhIt>"
  apply (unfold bot_It_def)
  apply (rule lItub_mhIt)
  done

lemma bot_It_lb:
  assumes 
    a1: "p \<in> \<mhIt>"
  shows
    "\<lbotIt> \<lle> p"
  apply (unfold bot_It_def)
  apply (rule lItub_lItub [OF a1])
  apply (rule bot_lb)
  done

lemma bot_It_min:
  assumes 
    a1: "p \<in> \<mhIt>"
  shows
    "p \<lle> \<lbotIt> \<Leftrightarrow> p = \<lbotIt>"
  apply (auto)
  apply (rule order_antisym)
  apply (assumption)
  apply (rule bot_It_lb [OF a1])
  done

definition
  sup_It :: "[('a::clattice) \<rightarrow> ('b::clattice), 'a \<rightarrow> 'b] \<rightarrow> ('a \<rightarrow> 'b)"
where
  sup_It_def: "sup_It \<defs> (\<olambda> p q \<bullet> lItub (p \<lsup> q))"

notation (xsymbols output)
  sup_It (infixl "\<squnion>\<^sub>I\<^sub>t" 65)

notation (zed)
  sup_It (infixl "\<lsupIt>" 65)

lemma sup_It_mhIt:
  assumes
    a1: "p \<in> \<mhIt>" and
    a2: "q \<in> \<mhIt>"
  shows
    "p \<lsupIt> q \<in> \<mhIt>"
  apply (unfold sup_It_def)
  apply (rule lItub_mhIt)
  done

lemma sup_It_ub1:
    "p \<lle> p \<lsupIt> q"
  apply (unfold sup_It_def)
  apply (rule order_trans [OF sup_ub1 lItub_ub])
  done

lemma sup_It_ub2:
    "q \<lle> p \<lsupIt> q"
  apply (unfold sup_It_def)
  apply (rule order_trans [OF sup_ub2 lItub_ub])
  done

lemma sup_It_lItub:
  assumes
    a1: "t \<in> \<mhIt>" and
    a2: "p \<lle> t" and
    a3: "q \<lle> t"
  shows
    "p \<lsupIt> q \<lle> t"
  apply (unfold sup_It_def)
  apply (rule lItub_lItub)
  apply (rule a1)
  apply (rule sup_lub [OF a2 a3])
  done

definition
  Sup_It :: "(('a::clattice) \<rightarrow> ('b::clattice)) set \<rightarrow> ('a \<rightarrow> 'b)"
where
  Sup_It_def: "Sup_It \<defs> (\<olambda> CL_P \<bullet> lItub (\<lSup> CL_P))"

notation (xsymbols output)
  Sup_It ("\<Squnion>\<^sub>I\<^sub>t")

notation (zed)
  Sup_It ("\<lSupIt>")

lemma Sup_It_mhIt:
  assumes
    a1: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<in> \<mhIt>"
  shows
    "\<lSupIt> CL_P \<in> \<mhIt>"
  apply (unfold Sup_It_def)
  apply (rule lItub_mhIt)
  done

lemma Sup_It_lb:
  assumes
    a1: "p \<in> CL_P"
  shows
    "p \<lle> \<lSupIt> CL_P"
  apply (unfold Sup_It_def)
  apply (rule order_trans [OF Sup_ub lItub_ub])
  apply (rule a1)
  done

lemma Sup_It_lItub:
  assumes
    a1: "t \<in> \<mhIt>" and
    a2: "\<And> p \<bullet> p \<in> CL_P \<turnstile> p \<lle> t"
  shows
    "\<lSupIt> CL_P \<lle> t"
  apply (unfold Sup_It_def)
  apply (rule lItub_lItub)
  apply (rule a1)
  apply (rule Sup_lub)
  apply (rule a2)
  apply (assumption)
  done

section {* Sets *}

(*
instance
  set :: (type) clat
  by (intro_classes)

instance
  set :: (type) bllat
  by (intro_classes)
*)

instantiation
  set :: (type) clattice

begin

definition
  inf_set_def: "(op &&) \<defs> (\<olambda> (x::'a set) y \<bullet> x \<inter> y)"

definition
  sup_set_def: "(op ||) \<defs> (\<olambda> (x::'a set) y \<bullet> x \<union> y)"

definition
  Inf_set_def: "Inf \<defs> (\<olambda> (X::'a set set) \<bullet> (\<Inter> x | x \<in> X \<bullet> x))"

definition
  Sup_set_def: "Sup \<defs> (\<olambda> (X::'a set set) \<bullet> (\<Union> x | x \<in> X \<bullet> x))"

definition
  bot_set_def: "bot \<defs> \<emptyset>"

definition
  top_set_def: "top \<defs> \<univ>"


instance 
  apply (intro_classes)
  apply (auto intro!: Inf_lb Inf_glb Sup_ub Sup_lub 
              simp add: inf_set_def sup_set_def Inf_set_def Sup_set_def bot_set_def top_set_def)
  done

end


lemma inf_set_conv [simp]:
  "(A \<linf> B) = (A \<inter> B)"
  by (simp add: inf_set_def)

lemma sup_set_conv [simp]:
  "(A \<lsup> B) = (A \<union> B)"
  by (simp add: sup_set_def)

(*
instance set :: (type) nonsqord
  by (intro_classes)
*)

lemma Inf_set_conv [simp]: "\<lInf>CL_A = \<Inter>CL_A"
  by (simp add: Inf_set_def)

lemma Sup_set_conv [simp]: "\<lSup>CL_A = \<Union>CL_A"
  by (simp add: Sup_set_def)

lemma bot_set_conv [simp]: "\<lbot> = \<emptyset>"
  by (simp add: bot_set_def)

lemma top_set_conv [simp]: "\<ltop> = \<univ>"
  by (simp add: top_set_def)

instantiation  set:: (type) boollattice
begin

definition
  comp_set_def: "ocomp \<defs> (\<olambda> (x::'a set) \<bullet> -x)"
(*
definition
  comp_set_def: "ocomp \<defs> (\<olambda> (x::'a set) \<bullet> \<univ> \<setminus> x)"
*)

instance
  apply (intro_classes)
  apply (auto simp add: comp_set_def)
  done

end

lemma comp_set_conv [simp]: "\<lcomp> (A::'a set) = -A"
  by (simp add: comp_set_def)





(*
lemma inf_set_def: 
  "(op &&) = (\<olambda> (x::'a set) y \<bullet> x \<inter> y)"
  apply (intro ext)
  apply (simp add: linf_fun_def Int_def linf_bool_def)
  done
  
lemma sup_set_def: 
  "(op ||) = (\<olambda> (x::'a set) y \<bullet> x \<union> y)"
  by (simp add: lsup_fun_def Un_def lsup_bool_def Collect_def mem_def)

lemma Inf_set_def: 
  "Inf = (\<olambda> (X::'a set set) \<bullet> (\<Inter> x | x \<in> X \<bullet> x))"
  apply (intro ext)
  apply (auto simp add: Inf_fun_def Inter_eq Inf_bool_def Collect_def mem_def)
  done

lemma
  Sup_set_def: "Sup = (\<olambda> (X::'a set set) \<bullet> (\<Union> x | x \<in> X \<bullet> x))"
  apply (intro ext)
  apply (auto simp add: Sup_fun_def Union_eq Sup_bool_def Collect_def mem_def)
  done

lemma
  bot_set_def: "bot = \<emptyset>"
  apply (intro set_eqI)
  apply (simp add: bot_fun_def bot_bool_def)
  apply (simp add: mem_def)
  done

lemma
  top_set_def: "top = \<univ>"
  apply (intro set_eqI)
  apply (simp add: top_fun_def top_bool_def)
  apply (simp add: mem_def)
  done

lemma
  comp_set_def: "lcomp = (\<olambda> (x::'a set) \<bullet> -x)"
  apply (intro set_eqI ext)
  apply (simp add: lcomp_fun_def lcomp_bool_def)
  apply (simp add: mem_def) 
  done

lemmas lat_set_defs = 
  inf_set_def sup_set_def Inf_set_def Sup_set_def
  bot_set_def top_set_def comp_set_def

lemma [simp]:
    "x \<in> (X \<linf> Y) \<Leftrightarrow> x \<in> X \<and> x \<in> Y" 
    "x \<in> (X \<lsup> Y) \<Leftrightarrow> x \<in> X \<or> x \<in> Y"
    "x \<in> (\<lINF> a | p a \<bullet> f a) \<Leftrightarrow> (\<forall> a | p a \<bullet> x \<in> (f a))"
    "x \<in> (\<lSUP> a | p a \<bullet> f a) \<Leftrightarrow> (\<exists> a | p a \<bullet> x \<in> (f a))"
    "x \<in> \<lbot> \<Leftrightarrow> \<False>"
    "x \<in> \<ltop> \<Leftrightarrow> \<True>"
    "x \<in> \<lcomp>X \<Leftrightarrow> x \<notin> X"
  by (simp_all add: lat_set_defs)
*)


lemmas lat_set_defs = 
  inf_set_def sup_set_def Inf_set_def Sup_set_def
  bot_set_def top_set_def comp_set_def

lemma [simp]:
    "x \<in> (X \<linf> Y) \<Leftrightarrow> x \<in> X \<and> x \<in> Y" 
    "x \<in> (X \<lsup> Y) \<Leftrightarrow> x \<in> X \<or> x \<in> Y"
    "x \<in> (\<lINF> a | p a \<bullet> f a) \<Leftrightarrow> (\<forall> a | p a \<bullet> x \<in> (f a))"
    "x \<in> (\<lSUP> a | p a \<bullet> f a) \<Leftrightarrow> (\<exists> a | p a \<bullet> x \<in> (f a))"
    "x \<in> \<lbot> \<Leftrightarrow> \<False>"
    "x \<in> \<ltop> \<Leftrightarrow> \<True>"
    "x \<in> \<lcomp>X \<Leftrightarrow> x \<notin> X"
  by (simp_all add: lat_set_defs)

section {* Predicate functions *}

text {*

Functions on predicates (predicate transformers)
offer some interesting algebraic properties, in particular a 
Galois transformation with corresponding base type functions (relations).

*}

definition
  relS :: "('a \<rightarrow> ('b::clattice)) \<rightarrow> (('a \<rightarrow> \<bool>) \<rightarrow> 'b)"
where
  relS_def: "relS \<defs> (\<olambda> r BS_phi \<bullet> (\<lSUP> a | BS_phi a \<bullet> r a))"

lemma mono_relS:
  assumes
    a1: "r \<lle> s"
  shows
    "relS r \<lle> relS s"
  using a1
  by (auto intro: QTSup_dom simp add: relS_def le_fun_def)

definition
  effS :: "(('a \<rightarrow> \<bool>) \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> ('b::clattice))"
where
  effS_def: "effS \<defs> (\<olambda> p a \<bullet> p (\<olambda> x \<bullet> x = a))"

lemma mono_effS:
  assumes
    a1: "p \<lle> q"
  shows
    "effS p \<lle> effS q"
  using a1
  by (simp add: effS_def le_fun_def)

lemma relS_inv:
    "effS (relS r) = r"
  by (simp add: relS_def effS_def Sup_singleton)

lemma relS_mhS:
    "relS r \<in> \<mhS>"
  apply (rule mhSI)
  apply (simp add: relS_def Sup_fun_def)
  apply (simp add: Sup_Sup)
  apply (rule arg_cong [of _ _ "\<lSup>"])
  apply auto
  apply (intro exI conjI)
  apply (rule refl)
  apply (rotate_tac 1, assumption+)
  done

lemma relS_mhb:
    "relS r \<in> \<mhb>"
  apply (rule mhbI)
  apply (rule mhSDm [OF relS_mhS])
  apply (simp add: relS_def Sup_empty)
  done

lemma relS_rgal: 
  assumes
    a1: "p \<in> \<mh>"
  shows 
    "relS (effS p) \<lle> p"
  apply (simp add: relS_def effS_def le_fun_def)
  apply (intro allI Sup_lub)
  apply (auto)
  apply (rule mhD [OF a1])
  apply (auto)
  done

lemma effS_inv_mhbS:
  assumes
    a1: "p \<in> \<mhbS>"
  shows 
    "relS (effS p) = p"
proof (rule ext)
  fix BS_phi
  have 
      "relS (effS p) BS_phi
      = (\<lSUP> a | BS_phi a \<bullet> p (\<olambda> b \<bullet> b = a))"
    by (auto simp add: relS_def effS_def)
  also have "\<dots>
      = p (\<lSUP> a | BS_phi a \<bullet> (\<olambda> b \<bullet> b = a))"
    by (simp add: mhbSD [OF a1])
  also have 
      "(\<lSUP> a | BS_phi a \<bullet> (\<olambda> b \<bullet> b = a)) 
      = BS_phi"
    by (simp add: Sup_fun_def)
  finally show 
      "relS (effS p) BS_phi = p BS_phi"
    by (this)
qed
 
lemma mhbS_char:
  "\<mhbS> = range relS"
proof (intro set_eqI iffI)
  fix p
  assume "p \<in> range relS"
  then show "p \<in> \<mhbS>"
    by (auto simp add: image_def relS_mhS relS_mhb)
next
  fix p::"('a \<rightarrow> \<bool>) \<rightarrow> 'b"
  assume b1: "p \<in> \<mhbS>" 
  then have "p = relS (effS p)"
    by (simp add: effS_inv_mhbS)
  then show "p \<in> range relS"
    by (auto simp add: image_def)
qed
 
lemma mhbSE:
  assumes a1: "p \<in> \<mhbS>" and
    a2: "\<And> r \<bullet> p = relS r \<turnstile> R"
  shows "R"
proof -
  from a1 obtain r where b1: "p = relS r"
    by (auto simp add: mhbS_char)
  then show "R"
    by (rule a2)
qed

lemma gbSlb_decomp: 
  assumes 
    a1: "p \<in> \<mh>"
  shows 
    "gbSlb p = relS (effS p)"
  apply (unfold gbSlb_def)
  apply (rule Sup_eq)
  apply (simp_all only: mem_Collect_eq)
  apply (msafe(inference))
proof -
  fix q
  assume 
    b1: "q \<in> \<mhbS>" and 
    b2: "q \<lle> p"
  from b1 have 
      "q = relS (effS q)"
    by (simp add: effS_inv_mhbS)
  also from b2 have 
      "\<dots> \<lle> relS (effS p)"
    by (simp add: mono_relS  mono_effS)
  finally show 
      "q \<lle> relS (effS p)"
    by (this)
next
  fix q
  assume 
    b1: "\<forall> q' | q' \<in> \<mhbS> \<and> q' \<lle> p \<bullet> q' \<lle> q"
  show "relS (effS p) \<lle> q"
  proof (rule b1 [rule_format])
    show 
        "relS (effS p) \<in> \<mhbS>"
      by (auto simp add: mhbS_char image_def)
    from a1 show 
        "relS (effS p) \<lle> p"
      by (rule relS_rgal)
  qed
qed

definition
  relI :: "('a \<rightarrow> ('b::{clattice,boollattice})) \<rightarrow> (('a \<rightarrow> \<bool>) \<rightarrow> 'b)"
where
  relI_def: "relI \<defs> (\<olambda> r BS_phi \<bullet> (\<lINF> a | \<not>(BS_phi a) \<bullet> \<lcomp>(r a)))"

lemma amono_relI:
  assumes
    a1: "r \<lle> s"
  shows
    "relI s \<lle> relI r"
  using a1
  by (auto intro!: QTInf_dom simp add: relI_def le_fun_def comp_antimono)

definition
  effI :: "(('a \<rightarrow> \<bool>) \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> ('b::{clattice,boollattice}))"
where
  effI_def: "effI \<defs> (\<olambda> p a \<bullet> \<lcomp> (p (\<olambda> x \<bullet> x \<noteq> a)))"

lemma amono_effI:
  assumes
    a1: "p \<lle> q"
  shows
    "effI q \<lle> effI p"
  using a1
  by (simp add: effI_def le_fun_def comp_antimono)

lemma relI_inv:
    "effI (relI r) = r"
  by (simp add: fun_eq_def relI_def effI_def Sup_singleton Inf_demorgan comp_involution)

lemma relI_mhI:
    "relI r \<in> \<mhI>"
  apply (rule mhII)
  apply (simp add: relI_def Inf_fun_def)
  apply (simp add: Inf_Inf)
  apply (rule arg_cong [of _ _ "\<lInf>"])
  apply (auto)
  done

lemma relI_mht:
    "relI r \<in> \<mht>"
  apply (rule mhtI)
  apply (rule mhIDm [OF relI_mhI])
  apply (simp add: relI_def Inf_empty)
  done

lemma relI_lgal: 
  assumes
    a1: "p \<in> \<mh>"
  shows 
    "p \<lle> relI (effI p)"
  apply (simp add: relI_def effI_def le_fun_def comp_involution)
  apply (intro allI Inf_glb)
  apply (auto)
  apply (rule mhD [OF a1])
  apply (auto)
  done

lemma effI_inv_mhIt:
  assumes
    a1: "p \<in> \<mhIt>"
  shows 
    "relI (effI p) = p"
proof (rule ext)
  fix BS_phi
  have 
      "relI (effI p) BS_phi
      = (\<lINF> a | \<not>(BS_phi a) \<bullet> p (\<olambda> b \<bullet> b \<noteq> a))"
    by (auto simp add: relI_def effI_def comp_involution)
  also have "\<dots>
      = p (\<lINF> a | \<not>(BS_phi a) \<bullet> (\<olambda> b \<bullet> b \<noteq> a))"
    by (simp add: mhItD [OF a1])
  also have 
      "(\<lINF> a | \<not>(BS_phi a) \<bullet> (\<olambda> b \<bullet> b \<noteq> a)) 
      = BS_phi"
    apply (rule ext)
    apply (auto simp add: Inf_fun_def)
    done
  finally show 
      "relI (effI p) BS_phi = p BS_phi"
    by (this)
qed
 
lemma mhIt_char:
  "\<mhIt> = range relI"
proof (intro set_eqI iffI)
  fix p
  assume 
      "p \<in> range relI"
  then show 
      "p \<in> \<mhIt>"
    by (auto simp add: image_def relI_mhI relI_mht)
next
  fix p::"('a \<rightarrow> \<bool>) \<rightarrow> 'b"
  assume 
    b1: "p \<in> \<mhIt>" 
  then have 
      "p = relI (effI p)"
    by (simp add: effI_inv_mhIt)
  then show 
      "p \<in> range relI"
    by (auto simp add: image_def)
qed
 
lemma mhItE:
  assumes 
    a1: "p \<in> \<mhIt>" and
    a2: "\<And> r \<bullet> p = relI r \<turnstile> R"
  shows 
    "R"
proof -
  from a1 obtain r where 
    b1: "p = relI r"
    by (auto simp add: mhIt_char)
  then show 
      "R"
    by (rule a2)
qed

lemma gItlb_decomp: 
  assumes 
    a1: "p \<in> \<mh>"
  shows 
    "lItub p = relI (effI p)"
  apply (unfold lItub_def)
  apply (rule Inf_eq)
  apply (simp_all only: mem_Collect_eq)
  apply (msafe(inference))
proof -
  fix q
  assume 
    b1: "q \<in> \<mhIt>" and 
    b2: "p \<lle> q"
  from b2 have 
      "relI (effI p) 
      \<lle> relI (effI q)"
    by (simp add: amono_relI  amono_effI)
  also from b1 have "\<dots>
      = q"
    by (simp add: effI_inv_mhIt) 
  finally show 
      "relI (effI p) \<lle> q"
    by (this)
next
  fix q
  assume 
    b1: "\<forall> q' | q' \<in> \<mhIt> \<and> p \<lle> q' \<bullet> q \<lle> q'"
  show 
      "q \<lle> relI (effI p)"
  proof (rule b1 [rule_format])
    show 
        "relI (effI p) \<in> \<mhIt>"
      by (auto simp add: mhIt_char image_def)
    from a1 show 
        "p \<lle> relI (effI p)"
      by (rule relI_lgal)
  qed
qed

section {* Total Graphs *}

text {*

Total graphs also inherit lattice properties from their ranges.

*}

lemma (in Lattice_Locale.lattice) tfun_latticeI:
  "\<^lattice>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):}"
proof (rule partial_order.latticeI)
  from partial_order show 
      "\<^poset>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):}"
    by (rule tfun_poI)
next
  fix 
    f g 
  assume 
    b1: "f \<in> Y \<ztfun> X" "g \<in> Y \<ztfun> X"
  show 
      "(\<exists> h \<bullet> \<^glbp>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):} {f, g} h)"
  proof (witness "(\<glambda> y | y \<in> Y \<bullet> f\<cdot>y \<sqinter> g\<cdot>y)")
    from b1 [THEN tfun_range] have 
      c1: "(\<forall> y | y \<in> Y \<bullet> f\<cdot>y \<sqinter> g\<cdot>y \<in> X)"
      by (auto)
    then have 
      c2: "(\<glambda> y | y \<in> Y \<bullet> f\<cdot>y \<sqinter> g\<cdot>y) \<in> Y \<ztfun> X"
      apply (mauto(fspace) msimp add: glambda_dom glambda_ran)
      apply (auto simp add: glambda_dom glambda_ran)
      done
    from b1 b1 [THEN tfun_range] c1 c2 show 
        "\<^glbp>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):} {f, g} (\<glambda> y | y \<in> Y \<bullet> f\<cdot>y \<sqinter> g\<cdot>y)"
      by (auto simp add: is_glb_def is_greatest_def is_lb_def tfun_order_def
        glambda_beta meet_lbD1 meet_lbD2 meet_glbD)
  qed
next
  fix   
    f g 
  assume 
    b1: "f \<in> Y \<ztfun> X" "g \<in> Y \<ztfun> X"
  show 
      "(\<exists> h \<bullet> \<^lubp>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):} {f, g} h)"
  proof (witness "(\<glambda> y | y \<in> Y \<bullet> f\<cdot>y \<squnion> g\<cdot>y)")
    from b1 [THEN tfun_range] have 
      c1: "(\<forall> y | y \<in> Y \<bullet> f\<cdot>y \<squnion> g\<cdot>y \<in> X)"
      by (auto)
    then have c2: "(\<glambda> y | y \<in> Y \<bullet> f\<cdot>y \<squnion> g\<cdot>y) \<in> Y \<ztfun> X"
      apply (msafe(fspace))
      apply (auto simp add: glambda_dom glambda_ran)
      done
    from b1 b1 [THEN tfun_range] c1 c2 show 
        "\<^lubp>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):} {f, g} (\<glambda> y | y \<in> Y \<bullet> f\<cdot>y \<squnion> g\<cdot>y)"
      by (auto simp add: is_lub_def is_least_def is_ub_def tfun_order_def
        glambda_beta join_ubD1 join_ubD2 join_lubD)
  qed
qed

lemma (in Lattice_Locale.clattice) tfun_clatticeI:
  "\<^clattice>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):}"
proof (rule partial_order.clatticeI)
  from partial_order show 
    b1: "\<^poset>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):}"
    by (rule tfun_poI) 
  then interpret 
    fun_po: Order_Locale.partial_order "(Y \<ztfun> X)" "(tfun_order Y X (op \<sqsubseteq>))"
    by (simp_all add: Order_Locale.partial_order_def)
{
  fix 
    F
  assume 
    b2: "F \<subseteq> Y \<ztfun> X"
  show 
      "(\<exists> f \<bullet> \<^glbp>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):} F f)"
  proof (witness "(\<glambda> y | y \<in> Y \<bullet> \<Sqinter>{f | f \<in> F \<bullet> f\<cdot>y})")
    from b2 have 
      c1: "(\<forall> y | y \<in> Y \<bullet> {f | f \<in> F \<bullet> f\<cdot>y} \<subseteq> X)"
      by (auto)
    then have 
      c2: "(\<forall> y | y \<in> Y \<bullet> is_glb {f | f \<in> F \<bullet> f\<cdot>y} (\<Sqinter>{f | f \<in> F \<bullet> f\<cdot>y}))"
      by (auto intro!: Meet_glb)
    from b2 c2 have 
      c3: "(\<glambda> y | y \<in> Y \<bullet> \<Sqinter>{f | f \<in> F \<bullet> f\<cdot>y}) \<in> Y \<ztfun> X"
      apply (msafe(fspace))
      apply (auto simp add: glambda_dom glambda_ran is_glb_def 
        is_greatest_def is_lb_def)
      done
    from b2 c1 c2 c3 show 
        "\<^glbp>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):} F (\<glambda> y | y \<in> Y \<bullet> \<Sqinter>{f | f \<in> F \<bullet> f\<cdot>y})"
      apply (intro fun_po.is_glbI [OF c3])
      apply (auto intro!: Meet_lbD Meet_glbD
        simp add: tfun_order_def glambda_beta) 
      done
  qed
}
{
  fix 
    F
  assume 
    b2: "F \<subseteq> Y \<ztfun> X"
  show 
      "(\<exists> f \<bullet> \<^lubp>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):} F f)"
  proof (witness "(\<glambda> y | y \<in> Y \<bullet> \<Squnion>{f | f \<in> F \<bullet> f\<cdot>y})")
    from b2 have 
      c1: "(\<forall> y | y \<in> Y \<bullet> {f | f \<in> F \<bullet> f\<cdot>y} \<subseteq> X)"
      by (auto)
    then have 
      c2: "(\<forall> y | y \<in> Y \<bullet> is_lub {f | f \<in> F \<bullet> f\<cdot>y} (\<Squnion>{f | f \<in> F \<bullet> f\<cdot>y}))"
      by (auto intro!: Join_lub)
    from b2 c2 have 
      c3: "(\<glambda> y | y \<in> Y \<bullet> \<Squnion>{f | f \<in> F \<bullet> f\<cdot>y}) \<in> Y \<ztfun> X"
      apply (msafe(fspace))
      apply (auto simp add: glambda_dom glambda_ran is_lub_def 
        is_least_def is_ub_def)
      done
    from b2 c1 c2 c3 show 
        "\<^lubp>{:(Y \<ztfun> X):}{:(tfun_order Y X (op \<sqsubseteq>)):} F (\<glambda> y | y \<in> Y \<bullet> \<Squnion>{f | f \<in> F \<bullet> f\<cdot>y})"
      apply (intro fun_po.is_lubI [OF c3])
      apply (auto intro!: Join_ubD Join_lubD
        simp add: tfun_order_def glambda_beta) 
      done
  qed
}
qed


section {* Dual spaces *}

text {*

Dual spaces preserve all of the lattice structure of the original space.

*}

instantiation
  dual :: (lat) lat
begin

definition
  linf_dual_def: "(op &&) \<defs> (\<olambda> x y \<bullet> \<^adual>{:(\<^rdual>{:x:} || \<^rdual>{:y:}):})"

definition
  lsup_dual_def: "(op ||) \<defs> (\<olambda> x y \<bullet> \<^adual>{:(\<^rdual>{:x:} && \<^rdual>{:y:}):})"

instance
  by (intro_classes)

end

instantiation
  dual :: (blat) blat
begin

definition
  bot_dual_def: "bot \<defs> \<^adual>{:top:}"

definition
  top_dual_def: "top \<defs> \<^adual>{:bot:}"

instance
  by (intro_classes)

end

instantiation
  dual :: (clat) clat
begin

definition
  Inf_dual_def: "Inf \<defs> (\<olambda> P \<bullet> \<^adual>{:(Sup { x | x \<in> P \<bullet> \<^rdual>{:x:} }):})"

definition
  Sup_dual_def: "Sup \<defs> (\<olambda> P \<bullet> \<^adual>{:(Inf { x | x \<in> P \<bullet> \<^rdual>{:x:} }):})"

instance
  by (intro_classes)

end

instantiation
  dual :: (bllat) bllat
begin

definition
  lcomp_dual_def: "ocomp \<defs> (\<olambda> x \<bullet> \<^adual>{:(ocomp \<^rdual>{:x:}):})"

instance
  by (intro_classes)

end

instance
  dual :: (lattice) lattice
  apply (intro_classes)
  apply (auto intro: inf_lb1 inf_lb2 sup_ub1 sup_ub2 inf_glb sup_lub simp add: linf_dual_def lsup_dual_def less_eq_dual_conv Abs_dual_inverse2)
  done

instance
  dual :: (boundlattice) boundlattice
  apply (intro_classes)
  apply (auto intro: bot_lb top_ub simp add: bot_dual_def top_dual_def less_eq_dual_conv Abs_dual_inverse2)
  done

instance
  dual :: (clattice) clattice
  apply (intro_classes)
  apply (auto intro!: Inf_lb Inf_glb Sup_ub Sup_lub arg_cong [of _ _ "Inf"] arg_cong [of _ _ "Sup"] simp add: Inf_dual_def Sup_dual_def linf_dual_def inf_Inf lsup_dual_def sup_Sup bot_dual_def bot_Inf top_dual_def top_Sup less_eq_dual_conv Abs_dual_inverse2 Abs_dual_inject2)
  apply (auto intro!: exI Abs_dual_inverse2 [symmetric])
  done

lemma Inf_dual_conv:
  "\<lInf> P = \<^adual>{:(\<lSUP> x | x \<in> P \<bullet> \<^rdual>{:x:}):}"
  by (simp add: Inf_dual_def)

lemma QInf_dual_conv:
  "(\<lINF> x | P x) = \<^adual>{:(\<lSUP> x | P x \<bullet> \<^rdual>{:x:}):}"
  by (simp add: Inf_dual_def)

lemma TQInf_dual_conv:
  "(\<lINF> x | P x \<bullet> f x) = \<^adual>{:(\<lSUP> x | P x \<bullet> \<^rdual>{:(f x):}):}"
  by (simp add: Inf_dual_def)

lemma Sup_dual_conv:
  "\<lSup> P = \<^adual>{:(\<lINF> x | x \<in> P \<bullet> \<^rdual>{:x:}):}"
  by (simp add: Sup_dual_def)

lemma QSup_dual_conv:
  "(\<lSUP> x | P x) = \<^adual>{:(\<lINF> x | P x \<bullet> \<^rdual>{:x:}):}"
  by (simp add: Sup_dual_def)

lemma TQSup_dual_conv:
  "(\<lSUP> x | P x \<bullet> f x) = \<^adual>{:(\<lINF> x | P x \<bullet> \<^rdual>{:(f x):}):}"
  by (simp add: Sup_dual_def)

instance
  dual :: (dlattice) dlattice
  apply (intro_classes)
  apply (simp add: linf_dual_def lsup_dual_def Abs_dual_inverse2 Abs_dual_inject2 inf_dist)
  done

instance
  dual :: (boollattice) boollattice
  apply (intro_classes)
  apply (auto simp add: linf_dual_def lsup_dual_def bot_dual_def top_dual_def lcomp_dual_def comp_inf comp_sup Abs_dual_inverse2 Abs_dual_inject2)
  done

section {* The unit lattice *}

instantiation
  unit :: clat
begin

definition
  linf_unit_def: "(op &&) \<defs> (\<olambda> (x::unit) y \<bullet> ())"

definition
  lsup_unit_def: "(op ||) \<defs> (\<olambda> (x::unit) y \<bullet> ())"

definition
  Inf_unit_def: "Inf \<defs> (\<olambda> (X::unit set) \<bullet> ())"

definition
  Sup_unit_def: "Sup \<defs> (\<olambda> (X::unit set) \<bullet> ())"

definition
  bot_unit_def: "bot \<defs> ()"

definition
  top_unit_def: "top \<defs> ()"

instance
  by (intro_classes)

end
 
instantiation
 unit :: bllat
begin

definition
  lcomp_unit_def: "ocomp \<defs> (\<olambda> (x::unit) \<bullet> ())"

instance
  by (intro_classes)

end

instance
  unit :: clattice
  apply (intro_classes)
  apply (auto simp add: linf_unit_def lsup_unit_def Inf_unit_def Sup_unit_def bot_unit_def top_unit_def)
  done

instance
  unit :: boollattice
  apply (intro_classes)
  apply (auto simp add: linf_unit_def lsup_unit_def bot_unit_def top_unit_def lcomp_unit_def)
  done

section {* (Bounded) Reals *}

text {*

The reals as a whole form a linear order -- and so, of course, a lattice.
Such results are obvious from default\_order and linorder_classD.

*}

instantiation
  real :: linlat
begin

definition
  inf_real_def: "oinf \<defs> (\<olambda> (x::\<real>) y \<bullet> \<if> x \<le> y \<then> x \<else> y \<fi>)"

definition
  sup_real_def: "osup \<defs> (\<olambda> (x::\<real>) y \<bullet> \<if> x \<le> y \<then> y \<else> x \<fi>)"

instance
  apply (intro_classes)
  apply (simp_all add: inf_real_def sup_real_def)
  done

end

interpretation 
  real_lattice: Lattice_Locale.lattice "\<univ>-[\<real>]" "op \<le>"
  by (unfold_locales)

text{*
The reals as a whole are not a complete lattice, but they are locally complete in the
sense that any bounded subset is a complete lattice. We introduce a useful class of 
complete sub-orders of the reals in the form of real intervals bounded by a given natural 
number.
The naturals are convenient for this purpose as they are positive by construction.

*}

definition
  ball :: "\<nat> \<rightarrow> \<real> set"
where
  ball_def: "ball N \<defs> { x | \<^abs>{:x:} \<le> of_nat N }"

text {* 
\subsection{Bounded reals}

We begin with some technical lemmas about these intervals.

*}

lemma ball_nempty:
  "ball N \<noteq> \<emptyset>"
  apply (auto simp add: ball_def)
  apply (witness "0::\<real>")
  apply (auto)
  done

lemma ball_inv_sub:
  assumes 
    a1: "X \<subseteq> ball N"
  shows 
    "{ y | -y \<in> X } \<subseteq> ball N"
  using a1
  by (auto simp add: ball_def)

lemma ball_inv_sub':
  assumes 
    a1: "X \<subseteq> ball N"
  shows 
    "{ y | y \<in> X \<bullet> -y } \<subseteq> ball N"
  using a1
  by (auto simp add: ball_def)

text {*

We note that the reals are a linear order and hence that each natural interval is a 
linear order.

*}


interpretation bound_real_order: Order_Locale.order "ball N" "default_order (ball N)"
  apply (insert default_order [OF ball_nempty])
  apply (auto simp add: Order_Locale.order_def)
  done

text {*

We introduce some technical lemmas about the real order.

*}
(*
lemma default_order_elim:
  "default_order UNIV = (op \<le>)"
  by (auto simp add: fun_eq_def)
*)

lemma neg_leI:
  fixes x::"\<real>" and y::"\<real>"
  assumes a1: "-x \<le> y"
  shows "-y \<le> x"
  apply (rule le_iff_diff_le_0 [THEN iffD2])
  apply (insert a1 [THEN le_iff_diff_le_0 [THEN iffD1]])
  apply (auto)
  done

lemma le_negI:
  fixes x::"\<real>" and y::"\<real>"
  assumes a1: "x \<le> -y"
  shows "y \<le> -x"
  apply (rule le_iff_diff_le_0 [THEN iffD2])
  apply (insert a1 [THEN le_iff_diff_le_0 [THEN iffD1]])
  apply (auto)
  done

lemma neg_le_negE:
  fixes x::"\<real>" and y::"\<real>"
  assumes a1: "-x \<le> -y"
  shows "y \<le> x"
  apply (rule le_iff_diff_le_0 [THEN iffD2])
  apply (insert a1 [THEN le_iff_diff_le_0 [THEN iffD1]])
  apply (auto)
  done

lemma neg_le_negI:
  fixes x::"\<real>" and y::"\<real>"
  assumes a1: "x \<le> y"
  shows "-y \<le> -x"
  apply (rule le_iff_diff_le_0 [THEN iffD2])
  apply (insert a1 [THEN le_iff_diff_le_0 [THEN iffD1]])
  apply (auto)
  done

text {*

The Isabelle base library records that bounded sets do have least upper bounds. To make
use of this result we have to reinterpret it in terms of the order operators of 
@{text "Order_Locale"}.

*}

lemma isLub_is_lub: "isLub UNIV X x \<Leftrightarrow> is_lub UNIV (op \<le>) X x"
  by (simp add: is_lub_def is_least_def is_ub_def isLub_def isUb_def leastP_def setle_def setge_def)

lemma isUb_is_ub: "isUb UNIV X x \<Leftrightarrow> is_ub UNIV (op \<le>) X x"
  by (simp add: is_ub_def isUb_def setle_def setge_def)

text {*

The existence of greatest lower bounds may be induced from the existence least upper bounds
by applying the duality principle.

*}

lemma is_glb_negative:
  "is_glb UNIV (op \<le>) X (x::\<real>) \<Leftrightarrow> is_lub UNIV (op \<le>) { y | y \<in> X \<bullet> -y } (-x)"
proof (rule iffI)
  assume b1: "is_glb UNIV (op \<le>) X (x::\<real>)"
  show "is_lub UNIV (op \<le>) { y | y \<in> X \<bullet> -y } (-x)"
    apply (simp add: is_lub_def is_ub_def is_least_def)
    apply (msafe(inference))
  proof -
    fix y
    assume "y \<in> X"
    with b1 show "x \<le> y"
      by (simp add: is_glb_def is_lb_def is_greatest_def)
  next
    fix x' 
    assume c1 [rule_format]: "(\<forall> y \<bullet> y \<in> X \<Rightarrow> -y \<le> x')"
    from b1 show "-x \<le> x'"
      apply (simp add: is_glb_def is_lb_def is_greatest_def)
      apply (msafe(inference))
    proof -
      assume d1 [rule_format]: "(\<forall> y \<bullet> y \<in> X \<Rightarrow> x \<le> y)" and
        d2 [rule_format]: "(\<forall> x' \<bullet> (\<forall> y \<bullet> y \<in> X \<Rightarrow> x' \<le> y) \<Rightarrow> x' \<le> x)"
      show "-x \<le> x'"
        apply (rule neg_leI)
        apply (rule d2)
        apply (rule neg_leI)
        apply (rule c1)
        apply (assumption)
        done
    qed
  qed
next
  assume b1: "is_lub UNIV (op \<le>) { y | y \<in> X \<bullet> -y } (-x)"
  show "is_glb UNIV (op \<le>) X (x::\<real>)"
    apply (simp add: is_glb_def is_lb_def is_greatest_def)
    apply (msafe(inference))
  proof -
    fix y
    assume "y \<in> X"
    with b1 show "x \<le> y"
      by (simp add: is_lub_def is_ub_def is_least_def)
  next
    fix x' 
    assume c1 [rule_format]: "(\<forall> y \<bullet> y \<in> X \<Rightarrow> x' \<le> y)"
    from b1 show "x' \<le> x"
      apply (simp add: is_lub_def is_ub_def is_least_def)
      apply (msafe(inference))
    proof -
      assume d1 [rule_format]: "(\<forall> y \<bullet> y \<in> X \<Rightarrow> x \<le> y)" and
        d2 [rule_format]: "(\<forall> x' \<bullet> (\<forall> y \<bullet> y \<in> X \<Rightarrow> -y \<le> x') \<Rightarrow> -x \<le> x')"
      show "x' \<le> x"
        apply (rule neg_le_negE)
        apply (rule d2)
        apply (rule neg_le_negI)
        apply (rule c1)
        apply (assumption)
        done
    qed
  qed
qed

text {*

We are now in a position to use the result from to infer the existence
of least upper bounds and greatest loweer bounds for subsets of the natural intervals.

*}

lemma ball_Join_is_lub:
  assumes 
    nempty: "X \<noteq> \<emptyset>" and
    sub_ball: "X \<subseteq> ball N"
  shows 
    "is_lub UNIV (op \<le>) X (\<^Join>{:UNIV:}{:(op \<le>):} X)"
  apply (rule order_classD [THEN partial_order.ex_Join_lub, OF _ reals_complete [simplified isLub_is_lub isUb_is_ub]])
  using nempty sub_ball
  apply (simp_all add: nempty_conv)
  apply (witness "(of_nat N)::\<real>")
  apply (simp add: is_ub_def ball_def subset_def abs_le_interval_iff)
  done

lemma Meet_negative:
  assumes 
    nempty: "X \<noteq> \<emptyset>" and
    sub_ball: "X \<subseteq> ball N"
  shows "(\<^Meet>{:UNIV:}{:(op \<le>):} X) =  - (\<^Join>{:UNIV:}{:(op \<le>):} { y | y \<in> X \<bullet> -y })"
  apply (simp add: Meet_def)
  apply (rule set_the_equality)
  apply (auto simp add: is_glb_negative)
  apply (rule ball_Join_is_lub)
  using nempty sub_ball
  apply (fast)
  apply (rule ball_inv_sub' [OF sub_ball])
proof -
  fix x
  assume b1: "is_lub UNIV (op \<le>) { y | y \<in> X \<bullet> -y } (-x)"
  from order_classD [THEN partial_order.lub_unique , OF ball_Join_is_lub [OF _ ball_inv_sub' [OF sub_ball]] b1] b1 nempty sub_ball show 
    "x = - (\<^Join>{:UNIV:}{:(op \<le>):} { y | y \<in> X \<bullet> -y })"
    by (auto)
qed

lemma ball_Meet_is_glb:
  assumes 
    nempty: "X \<noteq> \<emptyset>" and
    sub_ball: "X \<subseteq> ball N"
  shows 
    "is_glb UNIV (op \<le>) X (\<^Meet>{:UNIV:}{:(op \<le>):} X)"
  apply (simp add: is_glb_negative Meet_negative[OF nempty sub_ball])
  apply (rule ball_Join_is_lub [OF _ ball_inv_sub'])
  using nempty sub_ball
  apply (auto)
  done

text {*
Finally we show that the natural intervals form complete lattices.

*}

interpretation 
  bound_real_clat: Lattice_Locale.clattice "ball N" "default_order (ball N)"
  apply (intro_locales)
  apply (auto simp add: Lattice_Locale.clattice_axioms_def Lattice_Locale.lattice_axioms_def isLub_is_lub)
proof -
{ fix X 
  assume 
    sub_ball: "X \<subseteq> ball N"
  show 
      "(\<exists> x \<bullet> \<^glbp>{:(ball N):}{:(default_order (ball N)):} X x)"
  proof (cases "X = \<emptyset>")
    assume 
      nempty: "X \<noteq> \<emptyset>"
    have 
      c1: "\<^Meet>{:UNIV:}{:(op \<le>):} X \<in> ball N"
    proof (auto simp add: ball_def abs_le_interval_iff)
      show 
          "-(of_nat N) \<le> \<^Meet>{:UNIV:}{:(op \<le>):} X"
        apply (rule order_class.is_glbD2' [OF ball_Meet_is_glb [OF nempty sub_ball]])
        using sub_ball
        apply (auto simp add: ball_def abs_le_interval_iff)
        done
    next
      from nempty obtain y where 
        d1: "y \<in> X"
        by (auto) 
      from d1 have 
          "\<^Meet>{:UNIV:}{:(op \<le>):} X 
          \<le> y"
        by (rule order_class.is_glbD1' [OF ball_Meet_is_glb [OF nempty sub_ball]])
      also from d1 sub_ball have 
          "y 
          \<le> of_nat N"
        by (auto simp add: ball_def abs_le_interval_iff)        
      finally show 
          "\<^Meet>{:UNIV:}{:(op \<le>):} X \<le> of_nat N"
        by (this)
    qed   
    from sub_ball have 
      c2 [rule_format]: "(\<forall> x | x \<in> X \<bullet> x \<in> ball N)"
      by (auto)
    show 
        "(\<exists> x \<bullet> is_glb (ball N) (default_order (ball N)) X x)"
      apply (witness "\<^Meet>{:UNIV:}{:(op \<le>):} X")
      apply (rule bound_real_order.is_glbI)
      apply (auto simp add: c1 c2)
    proof -
      fix 
        x 
      assume 
        d1: "x \<in> X"
      show 
          "\<^Meet>{:UNIV:}{:(op \<le>):} X \<le> x"
        apply (rule order_class.is_glbD1' [OF _ d1])
        apply (rule ball_Meet_is_glb [OF nempty sub_ball])
        done
    next
      fix 
        a
      assume 
        d1: "a \<in> ball N" and
        d2: "(\<forall> x \<bullet> x \<in> X \<Rightarrow> a \<le> x)"
      show 
          "a \<le> \<^Meet>{:UNIV:}{:(op \<le>):} X"
        apply (rule order_class.is_glbD2')
        apply (rule ball_Meet_is_glb [OF nempty sub_ball])
        using d2
        apply (auto)
        done
    qed
  next 
    assume 
      empty: "X = \<emptyset>"
    with sub_ball show 
        "(\<exists> x \<bullet> \<^glbp>{:(ball N):}{:(default_order (ball N)):} X x)"
      apply (witness "(of_nat N)::\<real>")
      apply (rule bound_real_order.is_glbI)
      apply (auto simp add: ball_def abs_le_interval_iff)
      done
  qed }
next
{ fix X 
  assume 
    sub_ball: "X \<subseteq> ball N"
  show 
    "(\<exists> x \<bullet> \<^lubp>{:(ball N):}{:(default_order (ball N)):} X x)"
  proof (cases "X = \<emptyset>")
    assume 
      nempty: "X \<noteq> \<emptyset>"
    have 
      c1: "\<^Join>{:UNIV:}{:(op \<le>):} X \<in> ball N"
    proof (auto simp add: ball_def abs_le_interval_iff)
      from nempty obtain y where 
        d1: "y \<in> X"
        by (auto) 
      from d1 sub_ball have 
          "-(of_nat N) 
          \<le> y"
        by (auto simp add: ball_def abs_le_interval_iff)
      also from d1 have 
          "y 
          \<le> \<^Join>{:UNIV:}{:(op \<le>):} X"
        by (rule order_class.is_lubD1' [OF ball_Join_is_lub [OF nempty sub_ball]])
      finally show 
          "-(of_nat N) \<le> \<^Join>{:UNIV:}{:(op \<le>):} X"
        by (this)
    next
      show 
          "\<^Join>{:UNIV:}{:(op \<le>):} X \<le> of_nat N"
        apply (rule order_class.is_lubD2' [OF ball_Join_is_lub [OF nempty sub_ball]])
        using sub_ball
        apply (auto simp add: ball_def abs_le_interval_iff)
        done
    qed
    from sub_ball have 
      c2 [rule_format]: "(\<forall> x | x \<in> X \<bullet> x \<in> ball N)"
      by (auto)
    show 
        "(\<exists> x \<bullet> \<^lubp>{:(ball N):}{:(default_order (ball N)):} X x)"
      apply (witness "\<^Join>{:UNIV:}{:(op \<le>):} X")
      apply (rule bound_real_order.is_lubI)
      apply (auto simp add: c1 c2)
    proof -
     fix x 
      assume 
        d1: "x \<in> X"
      show 
          "x \<le> \<^Join>{:UNIV:}{:(op \<le>):} X"
        apply (rule order_class.is_lubD1' [OF _ d1])
        apply (rule ball_Join_is_lub [OF nempty sub_ball])
        done
    next
      fix 
        a
      assume 
        d1: "a \<in> ball N" and
        d2: "(\<forall> x \<bullet> x \<in> X \<Rightarrow> x \<le> a)"
      show 
          "\<^Join>{:UNIV:}{:(op \<le>):} X \<le> a"
        apply (rule order_class.is_lubD2')
        apply (rule ball_Join_is_lub [OF nempty sub_ball])
        using d2
        apply (auto)
        done
    qed
  next 
    assume 
      empty: "X = \<emptyset>"
    with sub_ball show 
        "(\<exists> x \<bullet> \<^lubp>{:(ball N):}{:(default_order (ball N)):} X x)"
      apply (witness "-(of_nat N)::\<real>")
      apply (rule bound_real_order.is_lubI)
      apply (auto simp add: ball_def abs_le_interval_iff)
      done
  qed } 
qed

text {*

\subsection{Bounded meet and join}

Finally we introduce bounded meet and join operators for the reals. These may,
on occasion, be preferable to explicitly restricting your model to a natural interval.

*}

definition
  brInf :: "[\<nat>, \<real> set] \<rightarrow> \<real>"
where
  brInf_def: "brInf N \<defs> (\<olambda> X \<bullet> \<if> (\<exists> x | x \<in> X \<bullet> x < -(of_nat N)) \<then> -(of_nat N) \<else> \<^Meet>{:\<univ>:}{:(op \<le>):} X \<fi>)"

definition
  brSup :: "[\<nat>, \<real> set] \<rightarrow> \<real>"
where
  brSup_def: "brSup N \<defs> (\<olambda> X \<bullet> \<if> (\<exists> x | x \<in> X \<bullet> of_nat N < x) \<then> of_nat N \<else> \<^Join>{:\<univ>:}{:(op \<le>):} X \<fi>)"

notation (zed)
  brInf ("\<^brInf>{:_:}") and
  brSup ("\<^brSup>{:_:}")

lemma brSup_is_lub:
  assumes 
    a1: "X \<noteq> \<emptyset>" and
    a2: "(\<forall> x | x \<in> X \<bullet> x \<le> of_nat N)"
  shows 
    "is_lub \<univ> (op \<le>) X (\<^brSup>{:N:} X)"
  using a1 a2
  apply (auto simp add: brSup_def)
  apply (rule order_classD [THEN partial_order.ex_Join_lub, OF _ reals_complete [simplified isLub_is_lub isUb_is_ub]])
  apply (auto simp add: is_ub_def)
  done

lemma brInf_negative:
  assumes 
    a1: "X \<noteq> \<emptyset>" and 
    a2: "(\<forall> x | x \<in> X \<bullet> -(of_nat N) \<le> x)"
  shows "(\<^brInf>{:N:} X) =  - (\<^brSup>{:N:} { y | y \<in> X \<bullet> -y })"
  using a1 a2
  apply (auto simp add: brSup_def brInf_def)
  apply (simp add: Meet_def)
  apply (rule set_the_equality)
  apply (auto simp add: is_glb_negative)
  apply (rule order_classD [THEN partial_order.ex_Join_lub, OF _ reals_complete [simplified isLub_is_lub isUb_is_ub]])
  apply (auto intro: neg_leI simp add: is_ub_def)
proof -
  fix x
  assume 
    b1: "is_lub UNIV (op \<le>) { y | y \<in> X \<bullet> -y } (-x)"
  from a2 have 
    b2: "\<not>(\<exists> x | x \<in> X \<bullet> of_nat N < -x)"
    by (auto intro: neg_leI simp add: linorder_not_less)
  have "is_lub \<univ> (op \<le>) { y | y \<in> X \<bullet> -y } (\<^brSup>{:N:} { y | y \<in> X \<bullet> -y })"
    apply (rule brSup_is_lub)
    using a1 a2 b1 b2
    apply (auto)
    done
  then have 
    b3: "is_lub \<univ> (op \<le>) { y | y \<in> X \<bullet> -y } (\<^Join>{:UNIV:}{:(op \<le>):} { y | y \<in> X \<bullet> -y })"
    by (auto simp add: brSup_def b2)
  from order_classD [THEN partial_order.lub_unique, OF b3 b1] 
  show 
    "x = - (\<^Join>{:UNIV:}{:(op \<le>):} { y | y \<in> X \<bullet> -y })"
    by (auto)
qed

lemma brInf_is_glb:
  assumes 
    a1: "X \<noteq> \<emptyset>" and 
    a2: "(\<forall> x | x \<in> X \<bullet> -(of_nat N) \<le> x)"
  shows "is_glb \<univ> (op \<le>) X (\<^brInf>{:N:} X)"
  apply (simp add: is_glb_negative brInf_negative [OF a1 a2])
  apply (rule brSup_is_lub)
  using a1 a2
  apply (auto)
  done


text{*
\subsection{Real intervals}

It seems worthwhile showing that closed intervals form a complete lattice.
This is a small generalisation of the above.

*}


lemma interval_poset:
"(a::\<real>) \<le> b \<turnstile> \<^poset>{:\<lclose>a\<dots>b\<rclose>:}{:default_order \<lclose>a\<dots>b\<rclose>:}"
  apply (rule default_po)
  apply (auto simp add: interval_defs)
done

lemma interval_order:
  assumes A1: "(a::\<real>) \<le> b"
  shows
  "Order_Locale.order \<lclose>a\<dots>b\<rclose> (default_order \<lclose>a\<dots>b\<rclose>)"
  apply (insert A1 [THEN interval_poset], unfold_locales)
  apply (simp_all add: partial_order_def')
  apply (auto simp add: interval_defs)  
done

theorem interval_lattice:
  assumes 
    a1: "(a::\<real>) \<le> b"
  shows
      "\<^lattice>{:\<lclose>a\<dots>b\<rclose>:}{:default_order \<lclose>a\<dots>b\<rclose>:}"
  apply (simp add: default_order_def)
  apply (rule sub_lattice.sublatticeI' [of "\<univ>"])
  apply (msafe(inference))
proof -
  fix
    x y
  assume
    b1: "x \<in> \<lclose>a\<dots>b\<rclose>" and
    b2: "y \<in> \<lclose>a\<dots>b\<rclose>"
  from b1 b2 show
      "x \<^meet>{:\<univ>:}{:(op \<le>):} y \<in> \<lclose>a\<dots>b\<rclose>"
    by (simp add: interval_defs inf_meet [THEN fun_cong, THEN fun_cong, of x y, symmetric] inf_real_def)
  from b1 b2 show
      "x \<^join>{:\<univ>:}{:(op \<le>):} y \<in> \<lclose>a\<dots>b\<rclose>"
    by (simp add: interval_defs sup_join [THEN fun_cong, THEN fun_cong, of x y, symmetric] sup_real_def)
next
  show 
      "sub_lattice \<univ> (op \<le>) \<lclose>a\<dots>b\<rclose>"
    apply (unfold_locales)
    apply (auto simp add: nempty_conv a1 interval_defs)
    done
qed

lemma domain_of_suborder_closed: 
    "\<zdom> \<^oprel>{:\<^subord>{:op \<le>:}{:\<lclose>(a::\<real>)\<dots>b\<rclose>:}:} = \<lclose>a\<dots>b\<rclose>"
  by (auto simp add: subset_order_def op2rel_def rel2op_def)


theorem real_ex_Sup: 
  assumes 
    a1: "(P::real set) \<noteq> \<emptyset>" and      
    a2: "\<^ubp>{:\<univ>-[\<real>]:}{:(op \<le>):} P u"
  shows
      "(\<exists> Sup \<bullet> \<^lubp>{:\<univ>-[\<real>]:}{:(op \<le>):} P Sup)"
proof -
  from a1 a2 have 
      "(\<exists> t \<bullet> isLub UNIV P t)"
    by (intro reals_complete, auto simp add:  isUb_is_ub)
  then show 
      ?thesis
    by (auto simp add: isLub_is_lub)
qed

theorem real_ex_Inf: 
  assumes 
    A1: "(P::real set) \<noteq> \<emptyset>" and        
    A2: "\<^lbp>{:\<univ>-[\<real>]:}{:(op \<le>):} P l"
  shows
      "(\<exists> Inf \<bullet> \<^glbp>{:\<univ>-[\<real>]:}{:(op \<le>):} P Inf)"
proof -
  let ?PM = "{y | y \<in> P \<bullet> -y}"
  from A1 have 
    a_notempty: "?PM \<noteq> \<emptyset>" 
    by (auto)
  from A2 have 
    a_ub: "\<^ubp>{:\<univ>-[\<real>]:}{:(op \<le>):} ?PM (-l)" 
    by (auto simp add: is_ub_def is_lb_def)
  from a_ub [THEN a_notempty [THEN real_ex_Sup]] obtain Sup where 
    a4: "\<^lubp>{:\<univ>-[\<real>]:}{:(op \<le>):} ?PM Sup" 
    by auto
  show 
      ?thesis
    apply (witness "-Sup")
    apply (simp add: is_glb_negative)
    apply (rule a4)
  done
qed


theorem real_interval_clattice:
  assumes 
    A1: "(a::\<real>) \<le> b"
  shows
      "\<^clattice>{:\<lclose>a\<dots>b\<rclose>:}{:default_order \<lclose>a\<dots>b\<rclose>:}"
proof-
  interpret 
    po_interval: partial_order "\<lclose>a\<dots>b\<rclose>" "default_order \<lclose>a\<dots>b\<rclose>"
    by (rule default_po, auto simp only: A1 interval_defs)
  show 
      ?thesis
  proof (rule po_interval.clatticeI)
    fix 
      X :: "\<real> set"
    assume 
      A2: "X \<subseteq> \<lclose>a\<dots>b\<rclose>"
    show
        "(\<exists> z \<bullet> \<^glbp>{:\<lclose>a\<dots>b\<rclose>:}{:(default_order \<lclose>a\<dots>b\<rclose>):} X z)"
    proof (cases "X = \<emptyset>")
      assume 
        A11: "X = \<emptyset>"
      from A1 A2 A11 show 
          ?thesis
        by (auto simp add: is_glb_def is_lb_def is_greatest_def interval_defs)
    next
      assume 
        A11: "X \<noteq> \<emptyset>"
      from A11 obtain x where 
        R0': "x \<in> X" 
        by auto 
      from A1 A2 A11 have 
        R0'': "\<^lbp>{:\<univ>-[\<real>]:}{:(op \<le>):} X a"
        by (intro order_class.is_lbI, auto simp add: interval_defs)
      from R0'' [THEN A11 [THEN real_ex_Inf]] obtain Inf where 
        R1': "\<^glbp>{:\<univ>-[\<real>]:}{:(op \<le>):} X Inf"
        by auto
      have  
        R2': "Inf \<in> \<lclose>a\<dots>b\<rclose>"
      proof -
        have 
          Rb1: "a \<le> Inf" 
          apply (rule R1' [THEN order_class.is_glbD2'], simp)
          apply (rule R0'' [THEN order_class.is_lbD], simp)
          done
        from R0' have 
            "Inf \<le> x" 
          by (rule R1' [THEN order_class.is_glbD1'])
        with R0' Rb1 A1 A2 show 
          ?thesis 
          by (auto simp add: interval_defs)
      qed
    
      with A1 A2 show
          ?thesis
        apply (witness "Inf")
        apply (rule po_interval.is_glbI, simp_all add: default_order_conv)
        apply (msafe(inference))
        apply (simp add: subset_eq interval_defs)
        apply (simp add: subset_eq interval_defs)
        apply (rule R1' [THEN order_class.is_glbD1'], simp)
        apply (rule R1' [THEN order_class.is_glbD2'], auto)
        done
    qed
  next
    fix 
      X :: "\<real> set"
    assume 
      A2: "X \<subseteq> \<lclose>a\<dots>b\<rclose>"
    show
        "(\<exists> z \<bullet> \<^lubp>{:\<lclose>a\<dots>b\<rclose>:}{:(default_order \<lclose>a\<dots>b\<rclose>):} X z)"
    proof (cases "X = \<emptyset>")
      assume 
        A11: "X = \<emptyset>"
      from A1 A2 A11 show 
          ?thesis
        by (auto simp add: is_lub_def is_ub_def is_least_def interval_defs)
    next
      assume 
        A11: "X \<noteq> \<emptyset>"
      from A11 obtain x where 
        R0': "x \<in> X" 
        by auto
      from A1 A2 A11 have 
        R0'': "\<^ubp>{:\<univ>-[\<real>]:}{:(op \<le>):} X b"
        by (intro order_class.is_ubI, auto simp add: interval_defs)
      from R0'' [THEN A11 [THEN real_ex_Sup]] obtain Sup where 
        R1': "\<^lubp>{:\<univ>-[\<real>]:}{:(op \<le>):} X Sup"
        by auto
      have 
        R2': "Sup \<in> \<lclose>a\<dots>b\<rclose>"
      proof-
        have 
          Rb1: "Sup \<le> b" 
          apply (rule R1' [THEN order_class.is_lubD2'], simp)
          apply (rule R0'' [THEN order_class.is_ubD], simp)
          done
        from R0' have 
          "x \<le> Sup" 
          by (rule R1' [THEN order_class.is_lubD1'])
        with R0' Rb1 A1 A2 show 
            ?thesis 
          by (auto simp add: interval_defs)
      qed
    
      with A1 A2 show 
          ?thesis
        apply (witness "Sup")
        apply (rule po_interval.is_lubI, simp_all add: default_order_conv)
        apply (msafe(inference))
        apply (simp add: subset_eq)
        apply (simp add: subset_eq)
        apply (rule R1' [THEN order_class.is_lubD1'], simp)
        apply (rule R1' [THEN order_class.is_lubD2'], auto)
        done
    qed
  qed
qed


end

