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

(*  Title:      multiclassical.ML

Clone of standard classical reasoning set, with allowance for the definition and use of multiple
reasoning sets.
*)

(*higher precedence than := facilitates use of references*)
infix 4 maddSIs maddSEs maddSDs maddIs maddEs maddDs mdelrules
  maddSWrapper mdelSWrapper maddWrapper mdelWrapper
  maddSbefore maddSafter maddbefore maddafter
  maddD2 maddE2 maddSD2 maddSE2;

signature MPROVER_DATA =
sig
  include CLASSICAL_DATA
  structure Splitter: SPLITTER
  val notE: thm
  val iffD1: thm
  val iffD2: thm
end;


signature BASIC_MPROVER =
sig
  type claset
  val mprint_clasimpset: (Symtab.key * Proof.context) -> unit
  val maddDs: (Symtab.key * Proof.context) * thm list -> (Symtab.key * Proof.context)
  val maddEs: (Symtab.key * Proof.context) * thm list -> (Symtab.key * Proof.context)
  val maddIs: (Symtab.key * Proof.context) * thm list -> (Symtab.key * Proof.context)
  val maddSDs: (Symtab.key * Proof.context) * thm list -> (Symtab.key * Proof.context)
  val maddSEs: (Symtab.key * Proof.context) * thm list -> (Symtab.key * Proof.context)
  val maddSIs: (Symtab.key * Proof.context) * thm list -> (Symtab.key * Proof.context)
  val mdelrules: (Symtab.key * Proof.context) * thm list -> (Symtab.key * Proof.context)
  val maddSWrapper: (Symtab.key * claset) * (string * (Proof.context -> wrapper)) -> (Symtab.key * claset)
  val mdelSWrapper: (Symtab.key * claset) *  string -> (Symtab.key * claset)
  val maddWrapper: (Symtab.key * claset) * (string * (Proof.context -> wrapper)) -> (Symtab.key * claset)
  val mdelWrapper: (Symtab.key * claset) *  string -> (Symtab.key * claset)
  val maddSbefore: (Symtab.key * claset) * (string * (int -> tactic)) -> (Symtab.key * claset)
  val maddSafter: (Symtab.key * claset) * (string * (int -> tactic)) -> (Symtab.key * claset)
  val maddbefore: (Symtab.key * claset) * (string * (int -> tactic)) -> (Symtab.key * claset)
  val maddafter: (Symtab.key * claset) * (string * (int -> tactic)) -> (Symtab.key * claset)
  val maddD2: (Symtab.key * claset) * (string * thm) -> (Symtab.key * claset)
  val maddE2: (Symtab.key * claset) * (string * thm) -> (Symtab.key * claset)
  val maddSD2: (Symtab.key * claset) * (string * thm) -> (Symtab.key * claset)
  val maddSE2: (Symtab.key * claset) * (string * thm) -> (Symtab.key * claset)
  val mappSWrappers: (Symtab.key * Proof.context) -> wrapper
  val mappWrappers: (Symtab.key * Proof.context) -> wrapper

(*
  val madd_simp: (Symtab.key * Proof.context) * thm -> (Symtab.key * Proof.context)
  val mdel_simp: (Symtab.key * Proof.context) * thm -> (Symtab.key * Proof.context) 
*)
(*
  val madd_simp: thm -> (Symtab.key * simpset) -> (Symtab.key * simpset)
  val mdel_simp: thm -> (Symtab.key * simpset) -> (Symtab.key * simpset)
  val madd_eqcong: thm -> (Symtab.key * simpset) -> (Symtab.key * simpset)
  val mdel_eqcong: thm -> (Symtab.key * simpset) -> (Symtab.key * simpset)
  val madd_cong: thm -> (Symtab.key * simpset) -> (Symtab.key * simpset)
  val mdel_cong: thm -> (Symtab.key * simpset) -> (Symtab.key * simpset)
*)

  val mglobal_clasimpset_of: Symtab.key * theory -> (claset * simpset)
  val mclasimpset_of: Symtab.key * Proof.context -> (claset * simpset)
  val mmap_clasimpset: Symtab.key -> ((claset * simpset) -> (claset * simpset)) -> Proof.context -> Proof.context
  val mput_clasimpset: Symtab.key -> (claset * simpset) -> Proof.context -> Proof.context

  val mglobal_claset_of: Symtab.key * theory -> claset
  val mclaset_of: Symtab.key * Proof.context -> claset
  val mmap_claset: Symtab.key -> (claset -> claset) -> Proof.context -> Proof.context
  val mput_claset: Symtab.key -> claset -> Proof.context -> Proof.context

  val mfast_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mfast_no_assms_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mslow_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mslow_no_assms_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mastar_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mastar_no_assms_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mslow_astar_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mslow_no_assms_astar_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mbest_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mbest_no_assms_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mfirst_best_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mfirst_no_assms_best_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mslow_best_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mslow_no_assms_best_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mdepth_tac: (Symtab.key * Proof.context) -> int -> int -> tactic
  val mdepth_no_assms_tac: (Symtab.key * Proof.context) -> int -> int -> tactic
  val mdeepen_tac: (Symtab.key * Proof.context) -> int -> int -> tactic
  val mdeepen_no_assms_tac: (Symtab.key * Proof.context) -> int -> int -> tactic

  val mdup_step_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mhaz_step_tac: (Symtab.key * Proof.context) -> int -> tactic
  val msafe_tac: (Symtab.key * Proof.context) -> tactic
  val msafe_steps_tac: (Symtab.key * Proof.context) -> int -> tactic
  val msafe_step_tac: (Symtab.key * Proof.context) -> int -> tactic
  val msafe_no_assms_tac: (Symtab.key * Proof.context) -> tactic
  val msafe_no_assms_steps_tac: (Symtab.key * Proof.context) -> int -> tactic
  val msafe_no_assms_step_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mclarify_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mclarify_step_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mclarify_no_assms_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mclarify_no_assms_step_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mstep_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mstep_no_assms_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mslow_step_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mslow_no_assms_step_tac: (Symtab.key * Proof.context) -> int -> tactic
  val minst_step_tac: (Symtab.key * Proof.context) -> int -> tactic
  val minst0_step_tac: (Symtab.key * Proof.context) -> int -> tactic
  val minstp_step_tac: (Symtab.key * Proof.context) -> int -> tactic
end;


signature CLASSICAL_MPROVER =
sig
  include BASIC_MPROVER
  type netpair = (int * (bool * thm)) Net.net * (int * (bool * thm)) Net.net
  val rep_cs: claset ->
   {safeIs: thm Item_Net.T,
    safeEs: thm Item_Net.T,
    hazIs: thm Item_Net.T,
    hazEs: thm Item_Net.T,
    swrappers: (string * (Proof.context -> wrapper)) list,
    uwrappers: (string * (Proof.context -> wrapper)) list,
    safe0_netpair: netpair,
    safep_netpair: netpair,
    haz_netpair: netpair,
    dup_netpair: netpair,
    xtra_netpair: Context_Rules.netpair}
  val new_css: Symtab.key -> Context.generic -> Context.generic
 (* val get_cs: Symtab.key -> Context.generic -> claset *)
  val map_cs: Symtab.key -> (claset -> claset) -> Context.generic -> Context.generic
  val safe_dest: Symtab.key -> int option -> attribute
  val safe_elim: Symtab.key -> int option -> attribute
  val safe_intro: Symtab.key -> int option -> attribute
  val haz_dest: Symtab.key -> int option -> attribute
  val haz_elim: Symtab.key -> int option -> attribute
  val haz_intro: Symtab.key -> int option -> attribute
  val rule_del: Symtab.key -> attribute
  val mcla_modifiers: Symtab.key -> Method.modifier parser list
  val cla_method:
    (Symtab.key * Proof.context -> tactic) -> (Proof.context -> Proof.method) context_parser
  val cla_method':
    (Symtab.key * Proof.context -> int -> tactic) -> (Proof.context -> Proof.method) context_parser
(*  val setup: theory -> theory *)
end;

signature MPROVER =
sig
  include CLASSICAL_MPROVER
  val multiclasimpset_of: Proof.context -> (claset * simpset) Symtab.table
  val maddSss: bool -> (Symtab.key * Proof.context) -> (Symtab.key * Proof.context)
  val maddss: bool -> (Symtab.key * Proof.context) -> (Symtab.key * Proof.context)
  val mclarsimp_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mclarsimp_no_assms_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mmk_auto_tac: bool -> (Symtab.key * Proof.context) -> int -> tactic
  val mauto_tac: bool -> (Symtab.key * Proof.context) -> tactic
  val mmk_auto_no_assms_tac: bool -> (Symtab.key * Proof.context) -> int -> tactic
  val mauto_no_assms_tac: bool -> (Symtab.key * Proof.context) -> tactic
  val mforce_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mforce_no_assms_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mfast_force_tac:(Symtab.key * Proof.context) -> int -> tactic
  val mslow_simp_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mbest_simp_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mfast_no_assms_force_tac:(Symtab.key * Proof.context) -> int -> tactic
  val mslow_no_assms_simp_tac: (Symtab.key * Proof.context) -> int -> tactic
  val mbest_no_assms_simp_tac: (Symtab.key * Proof.context) -> int -> tactic

  val msimp_add: Symtab.key -> attribute
  val msimp_del: Symtab.key -> attribute
  val mcong_add: Symtab.key -> attribute
  val mcong_del: Symtab.key -> attribute

  val miff_add: Symtab.key -> attribute
  val miff_add': Symtab.key -> attribute 
  val miff_del: Symtab.key -> attribute
  val miff_modifiers: Symtab.key -> Method.modifier parser list
  val mclasimp_modifiers: Symtab.key -> Method.modifier parser list
(*  val mclasimp_setup: theory -> theory *)
  val setup: theory -> theory
end;


functor MProver(Data: MPROVER_DATA): MPROVER =
struct


val flat_rule = Conv.fconv_rule (Conv.prems_conv ~1 Object_Logic.atomize_prems);

val swapped = Thm.rule_attribute (fn _ => fn th => th RSN (2, Data.swap));

(* type netpair = (int * (bool * thm)) Net.net * (int * (bool * thm)) Net.net; *)
type netpair = Classical.netpair;

(* type wrapper = (int -> tactic) -> int -> tactic; *)
type wrapper = Classical.wrapper;


datatype claset =
  CS of
   {safeIs         : thm Item_Net.T,          (*safe introduction rules*)
    safeEs         : thm Item_Net.T,          (*safe elimination rules*)
    hazIs          : thm Item_Net.T,          (*unsafe introduction rules*)
    hazEs          : thm Item_Net.T,          (*unsafe elimination rules*)
    swrappers      : (string * (Proof.context -> wrapper)) list, (*for transforming safe_step_tac*)
    uwrappers      : (string * (Proof.context -> wrapper)) list, (*for transforming step_tac*)
    safe0_netpair  : netpair,                 (*nets for trivial cases*)
    safep_netpair  : netpair,                 (*nets for >0 subgoals*)
    haz_netpair    : netpair,                 (*nets for unsafe rules*)
    dup_netpair    : netpair,                 (*nets for duplication*)
    xtra_netpair   : Context_Rules.netpair};  (*nets for extra rules*)


val empty_netpair = (Net.empty, Net.empty);

val empty_cs =
  CS
   {safeIs = Thm.full_rules,
    safeEs = Thm.full_rules,
    hazIs = Thm.full_rules,
    hazEs = Thm.full_rules,
    swrappers = [],
    uwrappers = [],
    safe0_netpair = empty_netpair,
    safep_netpair = empty_netpair,
    haz_netpair = empty_netpair,
    dup_netpair = empty_netpair,
    xtra_netpair = empty_netpair};

fun rep_cs (CS args) = args;


(*** Adding (un)safe introduction or elimination rules.

    In case of overlap, new rules are tried BEFORE old ones!!
***)

fun joinrules' (intrs, elims) =
  map (pair true) elims @ map (pair false) intrs;
(*Priority: prefer rules with fewest subgoals,
  then rules added most recently (preferring the head of the list).*)
fun tag_brls _ [] = []
  | tag_brls k (brl::brls) =
      (1000000*subgoals_of_brl brl + k, brl) ::
      tag_brls (k+1) brls;

fun tag_brls' _ _ [] = []
  | tag_brls' w k (brl::brls) = ((w, k), brl) :: tag_brls' w (k + 1) brls;

fun insert_tagged_list rls = fold_rev Tactic.insert_tagged_brl rls;

(*Insert into netpair that already has nI intr rules and nE elim rules.
  Count the intr rules double (to account for swapify).  Negate to give the
  new insertions the lowest priority.*)
fun insert (nI, nE) = insert_tagged_list o (tag_brls (~(2*nI+nE))) o joinrules;
fun insert' w (nI, nE) = insert_tagged_list o tag_brls' w (~(nI + nE)) o joinrules';

fun delete_tagged_list rls = fold_rev Tactic.delete_tagged_brl rls;
fun delete x = delete_tagged_list (joinrules x);
fun delete' x = delete_tagged_list (joinrules' x);

fun string_of_thm NONE = Display.string_of_thm_without_context
  | string_of_thm (SOME (_, context)) = Display.string_of_thm (Context.proof_of context);

fun make_elim context th =
  if has_fewer_prems 1 th then
    error ("Ill-formed destruction rule\n" ^ string_of_thm context th)
  else Tactic.make_elim th;

fun warn_thm opt_context msg th =
  if (case opt_context of (SOME (_, context)) => Context_Position.is_visible (Context.proof_of context) | NONE => false)
  then warning (msg ^ string_of_thm opt_context th)
  else ();

fun warn_rules context msg rules th =
  Item_Net.member rules th andalso (warn_thm context msg th; true);

fun claset_id_msg (SOME nm) msg = "["^nm^"]- "^msg
  | claset_id_msg NONE msg = msg;

fun the_cid (SOME (cid, _)) = cid
  | the_cid NONE = NONE

fun warn_claset context th (CS {safeIs, safeEs, hazIs, hazEs, ...}) =
  warn_rules context (claset_id_msg (the_cid context) "Rule already declared as safe introduction (intro!)\n") safeIs th orelse
  warn_rules context (claset_id_msg (the_cid context) "Rule already declared as safe elimination (elim!)\n") safeEs th orelse
  warn_rules context (claset_id_msg (the_cid context) "Rule already declared as introduction (intro)\n") hazIs th orelse
  warn_rules context (claset_id_msg (the_cid context) "Rule already declared as elimination (elim)\n") hazEs th;

(*** Safe rules ***)

fun addSI w context th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if warn_rules context "Ignoring duplicate safe introduction (intro!)\n" safeIs th then cs
  else
    let
      val th' = flat_rule th;
      val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
        List.partition Thm.no_prems [th'];
      val nI = Item_Net.length safeIs + 1;
      val nE = Item_Net.length safeEs;
      val _ = warn_claset context th cs;
    in
      CS
       {safeIs = Item_Net.update th safeIs,
        safe0_netpair = insert (nI,nE) (safe0_rls, []) safe0_netpair,
        safep_netpair = insert (nI,nE) (safep_rls, []) safep_netpair,
        safeEs = safeEs,
        hazIs = hazIs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        haz_netpair = haz_netpair,
        dup_netpair = dup_netpair,
        xtra_netpair = insert' (the_default 0 w) (nI,nE) ([th], []) xtra_netpair}
    end;

fun addSE w context th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if warn_rules context "Ignoring duplicate safe elimination (elim!)\n" safeEs th then cs
  else if has_fewer_prems 1 th then
    error ("Ill-formed elimination rule\n" ^ string_of_thm context th)
  else
    let
      val th' = Classical.classical_rule (flat_rule th);
      val (safe0_rls, safep_rls) = (*0 subgoals vs 1 or more*)
        List.partition (fn rl => nprems_of rl=1) [th'];
      val nI = Item_Net.length safeIs;
      val nE = Item_Net.length safeEs + 1;
      val _ = warn_claset context th cs;
    in
      CS
       {safeEs = Item_Net.update th safeEs,
        safe0_netpair = insert (nI,nE) ([], safe0_rls) safe0_netpair,
        safep_netpair = insert (nI,nE) ([], safep_rls) safep_netpair,
        safeIs = safeIs,
        hazIs = hazIs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        haz_netpair = haz_netpair,
        dup_netpair = dup_netpair,
        xtra_netpair = insert' (the_default 0 w) (nI,nE) ([], [th]) xtra_netpair}
    end;

fun addSD w context th = addSE w context (make_elim context th);


(*** Hazardous (unsafe) rules ***)

fun addI w context th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if warn_rules context "Ignoring duplicate introduction (intro)\n" hazIs th then cs
  else
    let
      val th' = flat_rule th;
      val nI = Item_Net.length hazIs + 1;
      val nE = Item_Net.length hazEs;
      val _ = warn_claset context th cs;
    in
      CS
       {hazIs = Item_Net.update th hazIs,
        haz_netpair = insert (nI, nE) ([th'], []) haz_netpair,
        dup_netpair = insert (nI, nE) ([dup_intr th'], []) dup_netpair,
        safeIs = safeIs,
        safeEs = safeEs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = insert' (the_default 1 w) (nI, nE) ([th], []) xtra_netpair}
    end
    handle THM ("RSN: no unifiers", _, _) => (*from dup_intr*)  (* FIXME !? *)
      error ("Ill-formed introduction rule\n" ^ string_of_thm context th);

fun addE w context th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if warn_rules context "Ignoring duplicate elimination (elim)\n" hazEs th then cs
  else if has_fewer_prems 1 th then
    error ("Ill-formed elimination rule\n" ^ string_of_thm context th)
  else
    let
      val th' = Classical.classical_rule (flat_rule th);
      val nI = Item_Net.length hazIs;
      val nE = Item_Net.length hazEs + 1;
      val _ = warn_claset context th cs;
    in
      CS
       {hazEs = Item_Net.update th hazEs,
        haz_netpair = insert (nI, nE) ([], [th']) haz_netpair,
        dup_netpair = insert (nI, nE) ([], [dup_elim th']) dup_netpair,
        safeIs = safeIs,
        safeEs = safeEs,
        hazIs = hazIs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = insert' (the_default 1 w) (nI, nE) ([], [th]) xtra_netpair}
    end;

fun addD w context th = addE w context (make_elim context th);



(*** Deletion of rules
     Working out what to delete, requires repeating much of the code used
        to insert.
***)

fun delSI th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if Item_Net.member safeIs th then
    let
      val th' = flat_rule th;
      val (safe0_rls, safep_rls) = List.partition Thm.no_prems [th'];
    in
      CS
       {safe0_netpair = delete (safe0_rls, []) safe0_netpair,
        safep_netpair = delete (safep_rls, []) safep_netpair,
        safeIs = Item_Net.remove th safeIs,
        safeEs = safeEs,
        hazIs = hazIs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        haz_netpair = haz_netpair,
        dup_netpair = dup_netpair,
        xtra_netpair = delete' ([th], []) xtra_netpair}
    end
  else cs;

fun delSE th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if Item_Net.member safeEs th then
    let
      val th' = Classical.classical_rule (flat_rule th);
      val (safe0_rls, safep_rls) = List.partition (fn rl => nprems_of rl = 1) [th'];
    in
      CS
       {safe0_netpair = delete ([], safe0_rls) safe0_netpair,
        safep_netpair = delete ([], safep_rls) safep_netpair,
        safeIs = safeIs,
        safeEs = Item_Net.remove th safeEs,
        hazIs = hazIs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        haz_netpair = haz_netpair,
        dup_netpair = dup_netpair,
        xtra_netpair = delete' ([], [th]) xtra_netpair}
    end
  else cs;

fun delI context th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if Item_Net.member hazIs th then
    let val th' = flat_rule th in
      CS
       {haz_netpair = delete ([th'], []) haz_netpair,
        dup_netpair = delete ([dup_intr th'], []) dup_netpair,
        safeIs = safeIs,
        safeEs = safeEs,
        hazIs = Item_Net.remove th hazIs,
        hazEs = hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = delete' ([th], []) xtra_netpair}
    end
  else cs
  handle THM ("RSN: no unifiers", _, _) => (*from dup_intr*)  (* FIXME !? *)
    error ("Ill-formed introduction rule\n" ^ string_of_thm context th);

fun delE th
    (cs as CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
      safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  if Item_Net.member hazEs th then
    let val th' = Classical.classical_rule (flat_rule th) in
      CS
       {haz_netpair = delete ([], [th']) haz_netpair,
        dup_netpair = delete ([], [dup_elim th']) dup_netpair,
        safeIs = safeIs,
        safeEs = safeEs,
        hazIs = hazIs,
        hazEs = Item_Net.remove th hazEs,
        swrappers = swrappers,
        uwrappers = uwrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        xtra_netpair = delete' ([], [th]) xtra_netpair}
    end
  else cs;

(*Delete ALL occurrences of "th" in the claset (perhaps from several lists)*)
fun delrule context th (cs as CS {safeIs, safeEs, hazIs, hazEs, ...}) =
  let val th' = Tactic.make_elim th in
    if Item_Net.member safeIs th orelse Item_Net.member safeEs th orelse
      Item_Net.member hazIs th orelse Item_Net.member hazEs th orelse
      Item_Net.member safeEs th' orelse Item_Net.member hazEs th'
    then delSI th (delSE th (delI context th (delE th (delSE th' (delE th' cs)))))
    else (warn_thm context "Undeclared classical rule\n" th; cs)
  end;




(** claset data **)

(* wrappers *)

fun map_swrappers f
  (CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  CS {safeIs = safeIs, safeEs = safeEs, hazIs = hazIs, hazEs = hazEs,
    swrappers = f swrappers, uwrappers = uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    haz_netpair = haz_netpair, dup_netpair = dup_netpair, xtra_netpair = xtra_netpair};

fun map_uwrappers f
  (CS {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers,
    safe0_netpair, safep_netpair, haz_netpair, dup_netpair, xtra_netpair}) =
  CS {safeIs = safeIs, safeEs = safeEs, hazIs = hazIs, hazEs = hazEs,
    swrappers = swrappers, uwrappers = f uwrappers,
    safe0_netpair = safe0_netpair, safep_netpair = safep_netpair,
    haz_netpair = haz_netpair, dup_netpair = dup_netpair, xtra_netpair = xtra_netpair};


(* merge_cs, merge_css *)

(*Merge works by adding all new rules of the 2nd claset into the 1st claset,
  in order to preserve priorities reliably.*)

fun merge_thms add thms1 thms2 =
  fold_rev (fn thm => if Item_Net.member thms1 thm then I else add thm) (Item_Net.content thms2);

fun merge_cs (cs as CS {safeIs, safeEs, hazIs, hazEs, ...},
    cs' as CS {safeIs = safeIs2, safeEs = safeEs2, hazIs = hazIs2, hazEs = hazEs2,
      swrappers, uwrappers, ...}) =
  if pointer_eq (cs, cs') then cs
  else
    cs
    |> merge_thms (addSI NONE NONE) safeIs safeIs2
    |> merge_thms (addSE NONE NONE) safeEs safeEs2
    |> merge_thms (addI NONE NONE) hazIs hazIs2
    |> merge_thms (addE NONE NONE) hazEs hazEs2
    |> map_swrappers (fn ws => AList.merge (op =) (K true) (ws, swrappers))
    |> map_uwrappers (fn ws => AList.merge (op =) (K true) (ws, uwrappers));

fun merge_css ((cs1, ss1), (cs2, ss2)) =
    (merge_cs (cs1, cs2), merge_ss (ss1, ss2));






(* data *)

structure MultiClasimpset = Generic_Data
(
  type T = (claset * simpset) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.join (fn _ => merge_css);
);


val global_multiclasimpset_of = MultiClasimpset.get o Context.Theory;
val multiclasimpset_of = MultiClasimpset.get o Context.Proof;

fun multiclasimpset_lookup cid mcss =
  case Symtab.lookup mcss cid of
    NONE => error("Unknown reasoning set "^cid)
  | SOME css => css;

fun mglobal_clasimpset_of (cid, ctxt) = 
  multiclasimpset_lookup cid (global_multiclasimpset_of ctxt);

val mglobal_claset_of = fst o mglobal_clasimpset_of
val mglobal_simpset_of = snd o mglobal_clasimpset_of

fun mclasimpset_of (cid, ctxt) = 
  multiclasimpset_lookup cid (multiclasimpset_of ctxt);

val mclaset_of = fst o mclasimpset_of
val msimpset_of = snd o mclasimpset_of

val msimpset_of_with_context = msimpset_of;

fun ss_full_with_context (cid, ctxt) =
  let 
    val ss = msimpset_of (cid, ctxt);
    val ss' = Simplifier.merge_ss (Simplifier.simpset_of ctxt, ss)
  in
    ss'
  end;

fun simpset_of_with_context ctxt = Simplifier.simpset_of ctxt;


fun rep_claset_of (cid, ctxt) = rep_cs (mclaset_of (cid, ctxt));

fun new_css cid = 
  let
    val ss = simpset_of (put_simpset HOL_basic_ss @{context} addsimps
                             @{thms "simp_thms" "equal"} addsimprocs
                             [@{simproc defined_All}, @{simproc defined_Ex}, @{simproc neq}, @{simproc let_simp}]);
  in
    MultiClasimpset.map (Symtab.update_new (cid, (empty_cs, ss)))
  end;


fun get_css cid ctxt = multiclasimpset_lookup cid (MultiClasimpset.get ctxt);
fun map_css cid f ctxt = MultiClasimpset.map (Symtab.map_entry cid f) ctxt;
fun mmap_clasimpset cid f = Context.proof_map (map_css cid f);
fun mput_clasimpset cid cs = mmap_clasimpset cid (K cs);

fun map_cs cid f ctxt =  map_css cid (fn (cs, ss) => (f cs, ss)) ctxt;
fun mmap_claset cid f = Context.proof_map (map_cs cid f);
fun mput_claset cid cs = mmap_claset cid (K cs);

fun map_ss cid f ctxt =  map_css cid (fn (cs, ss) => (cs, f ss)) ctxt;
fun gmap_ss cid f ctxt =  map_css cid (fn (cs, ss) => (cs, f ctxt ss)) ctxt;
fun mmap_simpset cid f = Context.proof_map (map_ss cid f);
fun mput_simpset cid ss = mmap_simpset cid (K ss);

fun mprint_mprover_ids ctxt =
  Pretty.str_list "active provers:" "" (Symtab.keys (multiclasimpset_of ctxt)) |> Pretty.writeln;

fun pretty_cs ctxt cs =
  let
    val {safeIs, safeEs, hazIs, hazEs, swrappers, uwrappers, ...} = rep_cs cs;
    val pretty_thms = map (Display.pretty_thm ctxt) o Item_Net.content;
  in
    [Pretty.big_list "safe introduction rules (intro!):" (pretty_thms safeIs),
      Pretty.big_list "introduction rules (intro):" (pretty_thms hazIs),
      Pretty.big_list "safe elimination rules (elim!):" (pretty_thms safeEs),
      Pretty.big_list "elimination rules (elim):" (pretty_thms hazEs),
      Pretty.strs ("safe wrappers:" :: map #1 swrappers),
      Pretty.strs ("unsafe wrappers:" :: map #1 uwrappers)]
    |> Pretty.chunks
  end;

fun mprint_clasimpset (cid, ctxt) =
  let 
    val css = mclasimpset_of (cid, ctxt);
  in
    (Pretty.writeln o Pretty.chunks) [
      Pretty.block [
        Pretty.str "classical reasoning set:",
        Pretty.fbrk,
        pretty_cs ctxt (fst css)
      ],
      Pretty.block [
        Pretty.str "classical simpset:",
        Pretty.fbrk,
        Simplifier.pretty_simpset (put_simpset (snd css) ctxt)
      ]
    ]
  end


(* old-style declarations *)

fun decl f ((cid, ctxt), ths) = (cid, mmap_claset cid (fold_rev (f (SOME (SOME cid, Context.Proof ctxt))) ths) ctxt);


val op maddSIs = decl (addSI NONE);
val op maddSEs = decl (addSE NONE);
val op maddSDs = decl (addSD NONE);
val op maddIs = decl (addI NONE);
val op maddEs = decl (addE NONE);
val op maddDs = decl (addD NONE);
val op mdelrules = decl delrule;




(*** Modifying the wrapper tacticals ***)

fun mappSWrappers (cid, ctxt) = fold (fn (_, w) => w ctxt) (#swrappers (rep_claset_of (cid, ctxt)));
fun mappWrappers (cid, ctxt) = fold (fn (_, w) => w ctxt) (#uwrappers (rep_claset_of (cid, ctxt)));


fun update_warn cid msg (p as (key : string, _)) xs =
  (if AList.defined (op =) xs key then warning (claset_id_msg (SOME cid) msg) else (); AList.update (op =) p xs);

fun delete_warn cid msg (key : string) xs =
  if AList.defined (op =) xs key then AList.delete (op =) key xs
  else (warning (claset_id_msg (SOME cid) msg); xs);


(*Add/replace a safe wrapper*)
fun (cid, cs) maddSWrapper new_swrapper =
  (cid, map_swrappers (update_warn cid ("Overwriting safe wrapper " ^ fst new_swrapper) new_swrapper) cs);

(*Add/replace an unsafe wrapper*)
fun (cid, cs) maddWrapper new_uwrapper =
  (cid, map_uwrappers (update_warn cid ("Overwriting unsafe wrapper " ^ fst new_uwrapper) new_uwrapper) cs);


(*Remove a safe wrapper*)
fun (cid, cs) mdelSWrapper name =
  (cid, map_swrappers (delete_warn cid ("No such safe wrapper in claset: " ^ name) name) cs);

(*Remove an unsafe wrapper*)
fun (cid, cs) mdelWrapper name =
  (cid, map_uwrappers (delete_warn cid ("No such unsafe wrapper in claset: " ^ name) name) cs);

(* compose a safe tactic alternatively before/after safe_step_tac *)
fun (cid, cs) maddSbefore (name, tac1) = (cid, cs) maddSWrapper (name, fn _ => fn tac2 => tac1 ORELSE' tac2);
fun (cid, cs) maddSafter (name, tac2) = (cid, cs) maddSWrapper (name, fn _ => fn tac1 => tac1 ORELSE' tac2);

(*compose a tactic alternatively before/after the step tactic *)
fun (cid, cs) maddbefore (name, tac1) = (cid, cs) maddWrapper (name, fn _ => fn tac2 => tac1 APPEND' tac2);
fun (cid, cs) maddafter (name, tac2) = (cid, cs) maddWrapper (name, fn _ => fn tac1 => tac1 APPEND' tac2);

fun (cid, cs) maddD2 (name, thm) = (cid, cs) maddafter (name, dtac thm THEN' assume_tac);
fun (cid, cs) maddE2 (name, thm) = (cid, cs) maddafter (name, etac thm THEN' assume_tac);
fun (cid, cs) maddSD2 (name, thm) = (cid, cs) maddSafter (name, dmatch_tac [thm] THEN' eq_assume_tac);
fun (cid, cs) maddSE2 (name, thm) = (cid, cs) maddSafter (name, ematch_tac [thm] THEN' eq_assume_tac);


(**** Simple tactics for theorem proving ****)

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun msafe_step_tac ctxt =
  let val {safe0_netpair, safep_netpair, ...} = rep_claset_of ctxt in
    mappSWrappers ctxt
      (FIRST'
       [eq_assume_tac,
        eq_mp_tac,
        bimatch_from_nets_tac safe0_netpair,
        FIRST' (map (fn f => f (snd ctxt)) Data.hyp_subst_tacs), 
        bimatch_from_nets_tac safep_netpair])
  end;

fun msafe_no_assms_step_tac ctxt =
  let val {safe0_netpair, safep_netpair, ...} = rep_claset_of ctxt in
    mappSWrappers ctxt
      (FIRST'
       [eq_assume_tac,
        eq_mp_tac,
        bimatch_from_nets_tac safe0_netpair,
(*        FIRST' Data.hyp_subst_tacs, *)
        bimatch_from_nets_tac safep_netpair])
  end;


(*Repeatedly attack a subgoal using safe inferences -- it's deterministic!*)
fun msafe_steps_tac ctxt =
  REPEAT_DETERM1 o (fn i => COND (has_fewer_prems i) no_tac (msafe_step_tac ctxt i));

fun msafe_no_assms_steps_tac ctxt =
  REPEAT_DETERM1 o (fn i => COND (has_fewer_prems i) no_tac (msafe_no_assms_step_tac ctxt i));

(*Repeatedly attack subgoals using safe inferences -- it's deterministic!*)
fun msafe_tac ctxt = REPEAT_DETERM1 (FIRSTGOAL (msafe_steps_tac ctxt));

fun msafe_no_assms_tac ctxt = REPEAT_DETERM1 (FIRSTGOAL (msafe_no_assms_steps_tac ctxt));


(*** Clarify_tac: do safe steps without causing branching ***)

fun nsubgoalsP n (_, brl) = (subgoals_of_brl brl = n);

(*version of bimatch_from_nets_tac that only applies rules that
  create precisely n subgoals.*)
fun n_bimatch_from_nets_tac n =
  biresolution_from_nets_tac (order_list o filter (nsubgoalsP n)) true;

fun eq_contr_tac i = ematch_tac [Data.not_elim] i THEN eq_assume_tac i;
val eq_assume_contr_tac = eq_assume_tac ORELSE' eq_contr_tac;

(*Two-way branching is allowed only if one of the branches immediately closes*)
fun bimatch2_tac netpair i =
  n_bimatch_from_nets_tac 2 netpair i THEN
  (eq_assume_contr_tac i ORELSE eq_assume_contr_tac (i + 1));

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun mclarify_step_tac ctxt =
  let val {safe0_netpair, safep_netpair, ...} = rep_claset_of ctxt in
    mappSWrappers ctxt
     (FIRST'
       [eq_assume_contr_tac,
        bimatch_from_nets_tac safe0_netpair,
        FIRST' (map (fn f => f (snd ctxt)) Data.hyp_subst_tacs), 
        n_bimatch_from_nets_tac 1 safep_netpair,
        bimatch2_tac safep_netpair])
  end;

fun mclarify_no_assms_step_tac ctxt =
  let val {safe0_netpair, safep_netpair, ...} = rep_claset_of ctxt in
    mappSWrappers ctxt
     (FIRST'
       [eq_assume_contr_tac,
        bimatch_from_nets_tac safe0_netpair,
(*        FIRST' Data.hyp_subst_tacs, *)
        n_bimatch_from_nets_tac 1 safep_netpair,
        bimatch2_tac safep_netpair])
  end;

fun mclarify_tac ctxt = SELECT_GOAL (REPEAT_DETERM (mclarify_step_tac ctxt 1));

fun mclarify_no_assms_tac ctxt = SELECT_GOAL (REPEAT_DETERM (mclarify_no_assms_step_tac ctxt 1));


(*** Unsafe steps instantiate variables or lose information ***)

(*Backtracking is allowed among the various these unsafe ways of
  proving a subgoal.  *)
fun minst0_step_tac ctxt =
  assume_tac APPEND'
  contr_tac APPEND'
  biresolve_from_nets_tac (#safe0_netpair (rep_claset_of ctxt));

(*These unsafe steps could generate more subgoals.*)
fun minstp_step_tac ctxt =
  biresolve_from_nets_tac (#safep_netpair (rep_claset_of ctxt));

(*These steps could instantiate variables and are therefore unsafe.*)
fun minst_step_tac ctxt = minst0_step_tac ctxt APPEND' minstp_step_tac ctxt;

fun mhaz_step_tac ctxt =
  biresolve_from_nets_tac (#haz_netpair (rep_claset_of ctxt));

(*Single step for the prover.  FAILS unless it makes progress. *)
fun mstep_tac ctxt i =
  msafe_tac ctxt ORELSE mappWrappers ctxt (minst_step_tac ctxt ORELSE' mhaz_step_tac ctxt) i;

fun mstep_no_assms_tac ctxt i =
  msafe_no_assms_tac ctxt ORELSE mappWrappers ctxt (minst_step_tac ctxt ORELSE' mhaz_step_tac ctxt) i;

(*Using a "safe" rule to instantiate variables is unsafe.  This tactic
  allows backtracking from "safe" rules to "unsafe" rules here.*)
fun mslow_step_tac ctxt i =
  msafe_tac ctxt ORELSE mappWrappers ctxt (minst_step_tac ctxt APPEND' mhaz_step_tac ctxt) i;

fun mslow_no_assms_step_tac ctxt i =
  msafe_no_assms_tac ctxt ORELSE mappWrappers ctxt (minst_step_tac ctxt APPEND' mhaz_step_tac ctxt) i;



(**** The following tactics all fail unless they solve one goal ****)

(*Dumb but fast*)
fun mfast_tac ctxt =
  Object_Logic.atomize_prems_tac THEN' SELECT_GOAL (DEPTH_SOLVE (mstep_tac ctxt 1));

fun mfast_no_assms_tac ctxt =
  Object_Logic.atomize_prems_tac THEN' SELECT_GOAL (DEPTH_SOLVE (mstep_no_assms_tac ctxt 1));

(*Slower but smarter than fast_tac*)
fun mbest_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, Data.sizef) (mstep_tac ctxt 1));

fun mbest_no_assms_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, Data.sizef) (mstep_no_assms_tac ctxt 1));

(*even a bit smarter than best_tac*)
fun mfirst_best_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, Data.sizef) (FIRSTGOAL (mstep_tac ctxt)));

fun mfirst_no_assms_best_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, Data.sizef) (FIRSTGOAL (mstep_no_assms_tac ctxt)));

fun mslow_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (DEPTH_SOLVE (mslow_step_tac ctxt 1));

fun mslow_no_assms_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (DEPTH_SOLVE (mslow_no_assms_step_tac ctxt 1));

fun mslow_best_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, Data.sizef) (mslow_step_tac ctxt 1));

fun mslow_no_assms_best_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, Data.sizef) (mslow_no_assms_step_tac ctxt 1));



(***ASTAR with weight weight_ASTAR, by Norbert Voelker*)

val weight_ASTAR = 5;

fun mastar_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL
    (ASTAR (has_fewer_prems 1, fn lev => fn thm => size_of_thm thm + weight_ASTAR * lev)
      (mstep_tac ctxt 1));

fun mastar_no_assms_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL
    (ASTAR (has_fewer_prems 1, fn lev => fn thm => size_of_thm thm + weight_ASTAR * lev)
      (mstep_no_assms_tac ctxt 1));

fun mslow_astar_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL
    (ASTAR (has_fewer_prems 1, fn lev => fn thm => size_of_thm thm + weight_ASTAR * lev)
      (mslow_step_tac ctxt 1));

fun mslow_no_assms_astar_tac ctxt =
  Object_Logic.atomize_prems_tac THEN'
  SELECT_GOAL
    (ASTAR (has_fewer_prems 1, fn lev => fn thm => size_of_thm thm + weight_ASTAR * lev)
      (mslow_no_assms_step_tac ctxt 1));



(**** Complete tactic, loosely based upon LeanTaP.  This tactic is the outcome
  of much experimentation!  Changing APPEND to ORELSE below would prove
  easy theorems faster, but loses completeness -- and many of the harder
  theorems such as 43. ****)

(*Non-deterministic!  Could always expand the first unsafe connective.
  That's hard to implement and did not perform better in experiments, due to
  greater search depth required.*)
fun mdup_step_tac ctxt =
  biresolve_from_nets_tac (#dup_netpair (rep_claset_of ctxt));

(*Searching to depth m. A variant called nodup_depth_tac appears in clasimp.ML*)
local
  fun mslow_step_tac' ctxt = mappWrappers ctxt (minstp_step_tac ctxt APPEND' mdup_step_tac ctxt);
in
  fun mdepth_tac ctxt m i state = SELECT_GOAL
    (msafe_steps_tac ctxt 1 THEN_ELSE
      (DEPTH_SOLVE (mdepth_tac ctxt m 1),
        minst0_step_tac ctxt 1 APPEND COND (K (m = 0)) no_tac
          (mslow_step_tac' ctxt 1 THEN DEPTH_SOLVE (mdepth_tac ctxt (m - 1) 1)))) i state;

  fun mdepth_no_assms_tac ctxt m i state = SELECT_GOAL
    (msafe_no_assms_steps_tac ctxt 1 THEN_ELSE
      (DEPTH_SOLVE (mdepth_no_assms_tac ctxt m 1),
        minst0_step_tac ctxt 1 APPEND COND (K (m = 0)) no_tac
          (mslow_step_tac' ctxt 1 THEN DEPTH_SOLVE (mdepth_no_assms_tac ctxt (m - 1) 1)))) i state;
end;

(*Search, with depth bound m.
  This is the "entry point", which does safe inferences first.*)
fun msafe_depth_tac ctxt m = SUBGOAL (fn (prem, i) =>
  let
    val deti = (*No Vars in the goal?  No need to backtrack between goals.*)
      if exists_subterm (fn Var _ => true | _ => false) prem then DETERM else I;
  in
    SELECT_GOAL (TRY (msafe_tac ctxt) THEN DEPTH_SOLVE (deti (mdepth_tac ctxt m 1))) i
  end);

fun msafe_no_assms_depth_tac ctxt m = SUBGOAL (fn (prem, i) =>
  let
    val deti = (*No Vars in the goal?  No need to backtrack between goals.*)
      if exists_subterm (fn Var _ => true | _ => false) prem then DETERM else I;
  in
    SELECT_GOAL (TRY (msafe_no_assms_tac ctxt) THEN DEPTH_SOLVE (deti (mdepth_no_assms_tac ctxt m 1))) i
  end);

fun mdeepen_tac ctxt = DEEPEN (2, 10) (msafe_depth_tac ctxt);

fun mdeepen_no_assms_tac ctxt = DEEPEN (2, 10) (msafe_no_assms_depth_tac ctxt);



(* simp as classical wrapper *)

fun 
  mclasimp f name tac loc (cid, ctxt) 
  = 
  let
    val ss 
        = if loc 
          then msimpset_of_with_context (cid, ctxt)
          else Raw_Simplifier.merge_ss (msimpset_of_with_context (cid, ctxt), Raw_Simplifier.simpset_of ctxt);
  in
    (cid, mmap_claset cid (fn cs => snd (f ((cid, cs), (name, CHANGED o tac (put_simpset ss ctxt))))) ctxt)
  end;

fun 
  mclasimp_full f name tac loc (cid, ctxt) 
  = 
    let
    val ss 
        = if loc 
          then ss_full_with_context (cid, ctxt)
          else Raw_Simplifier.merge_ss (ss_full_with_context (cid, ctxt), Raw_Simplifier.simpset_of ctxt);
  in
    (cid, mmap_claset cid (fn cs => snd (f ((cid, cs), (name, CHANGED o tac (put_simpset ss ctxt))))) ctxt) 
  end;

(*Add a simpset to the claset!*)
(*Caution: only one simpset added can be added by each of maddSss and maddss*)
val maddSss = mclasimp (op maddSafter) "safe_asm_full_simp_tac" Simplifier.safe_asm_full_simp_tac;
val madd_fullSss = mclasimp_full (op maddSafter) "safe_asm_full_simp_tac" Simplifier.safe_asm_full_simp_tac;
val maddss = mclasimp (op maddbefore) "asm_full_simp_tac" Simplifier.asm_full_simp_tac;
val madd_fullss = mclasimp_full (op maddbefore) "asm_full_simp_tac" Simplifier.asm_full_simp_tac;

(* tactics *)
(*
fun mclarsimp_tac ctxt =
  Simplifier.safe_asm_full_simp_tac (msimpset_of ctxt) THEN_ALL_NEW
  mclarify_tac (maddSss ctxt);

fun mclarsimp_no_assms_tac ctxt =
  Simplifier.safe_asm_full_simp_tac (msimpset_of ctxt) THEN_ALL_NEW
  mclarify_no_assms_tac (maddSss ctxt);
*)

fun mclarsimp_tac ctxt =
  Simplifier.safe_asm_full_simp_tac (put_simpset (msimpset_of_with_context ctxt) (snd ctxt)) THEN_ALL_NEW
  mclarify_tac (maddSss true ctxt);

fun mclarsimp_no_assms_tac ctxt =
  Simplifier.safe_asm_full_simp_tac (put_simpset (msimpset_of_with_context ctxt) (snd ctxt)) THEN_ALL_NEW
  mclarify_no_assms_tac (maddSss true ctxt);

fun mclarsimp_full_tac ctxt =
  Simplifier.safe_asm_full_simp_tac (put_simpset (ss_full_with_context ctxt) (snd ctxt)) THEN_ALL_NEW
  mclarify_tac (maddSss true ctxt);

(* mauto_tac *)

(* a variant of mdepth_tac that avoids interference of the simplifier
   with mdup_step_tac when they are combined by mauto_tac *)
local

fun mslow_step_tac' ctxt =
  mappWrappers ctxt
    (minstp_step_tac ctxt APPEND' mhaz_step_tac ctxt);

in

fun mnodup_depth_tac ctxt m i st =
  SELECT_GOAL
    (msafe_steps_tac ctxt 1 THEN_ELSE
      (DEPTH_SOLVE (mnodup_depth_tac ctxt m 1),
        minst0_step_tac ctxt 1 APPEND COND (K (m = 0)) no_tac
          (mslow_step_tac' ctxt 1 THEN DEPTH_SOLVE (mnodup_depth_tac ctxt (m - 1) 1)))) i st;

fun mnodup_no_assms_depth_tac ctxt m i st =
  SELECT_GOAL
    (msafe_no_assms_steps_tac ctxt 1 THEN_ELSE
      (DEPTH_SOLVE (mnodup_no_assms_depth_tac ctxt m 1),
        minst0_step_tac ctxt 1 APPEND COND (K (m = 0)) no_tac
          (mslow_step_tac' ctxt 1 THEN DEPTH_SOLVE (mnodup_no_assms_depth_tac ctxt (m - 1) 1)))) i st;

end;

(* Designed to be idempotent *)


fun 
  mmk_auto_tac loc ctxt n =
  let
    val main_tac =
(* J: perhaps put back the parameter... here just have the "4" for mauto!
*)
      Blast.depth_tac (snd ctxt) 4  (* fast but can't use wrappers *)
      ORELSE'
      (CHANGED o mnodup_depth_tac (maddss loc ctxt) n);  (* slower but more general *)
  in
    PARALLEL_GOALS (ALLGOALS (Simplifier.asm_full_simp_tac (put_simpset (msimpset_of_with_context ctxt) (snd ctxt)))) THEN
    TRY (msafe_tac ctxt) THEN
    REPEAT_DETERM (FIRSTGOAL main_tac) THEN
    TRY (msafe_tac (maddSss loc ctxt)) THEN
    prune_params_tac
  end;

fun mmk_auto_no_assms_tac loc ctxt n =
  let
    val main_tac =
(*
      Blast.depth_tac ctxt m  (* fast but can't use wrappers *)
      ORELSE'
*)
      (CHANGED o mnodup_no_assms_depth_tac (maddss loc ctxt) n);  (* slower but more general *)
  in
    PARALLEL_GOALS (ALLGOALS (Simplifier.asm_full_simp_tac (put_simpset (msimpset_of_with_context ctxt) (snd ctxt)))) THEN
    TRY (msafe_no_assms_tac ctxt) THEN
    REPEAT_DETERM (FIRSTGOAL main_tac) THEN
    TRY (msafe_no_assms_tac (maddSss loc ctxt)) THEN
    prune_params_tac
  end;


fun mauto_tac loc ctxt = mmk_auto_tac loc ctxt 2;

fun mauto_no_assms_tac loc ctxt = mmk_auto_no_assms_tac loc ctxt 2;

fun mmk_auto_full_tac loc ctxt n =
  let
    val main_tac =
(* J: perhaps put back the parameter... here just have the "4" for mauto!
*)
      Blast.depth_tac (snd ctxt) 4  (* fast but can't use wrappers *)
      ORELSE'
      (CHANGED o mnodup_depth_tac (madd_fullss loc ctxt) n);  (* slower but more general *)
  in
    PARALLEL_GOALS (ALLGOALS (Simplifier.asm_full_simp_tac (put_simpset (ss_full_with_context ctxt) (snd ctxt)))) THEN
    TRY (msafe_tac ctxt) THEN
    REPEAT_DETERM (FIRSTGOAL main_tac) THEN
    TRY (msafe_tac (madd_fullSss loc ctxt)) THEN
    prune_params_tac
  end;


fun mauto_full_tac loc ctxt = mmk_auto_full_tac loc ctxt 2;



(* force_tac *)

(* aimed to solve the given subgoal totally, using whatever tools possible *)

fun mforce_tac ctxt =
  let val ctxt' = maddss true ctxt in
    SELECT_GOAL
     (mclarify_tac ctxt' 1 THEN
      IF_UNSOLVED (Simplifier.asm_full_simp_tac (put_simpset (msimpset_of_with_context ctxt) (snd ctxt)) 1) THEN
      ALLGOALS (mfirst_best_tac ctxt'))
  end;

fun mforce_no_assms_tac ctxt =
  let val ctxt' = maddss true ctxt in
    SELECT_GOAL
     (mclarify_no_assms_tac ctxt' 1 THEN
      IF_UNSOLVED (Simplifier.asm_full_simp_tac (put_simpset (msimpset_of_with_context ctxt) (snd ctxt)) 1) THEN
      ALLGOALS (mfirst_no_assms_best_tac ctxt'))
  end;

(* basic combinations *)

val mfast_force_tac = mfast_tac o (maddss true);
val mslow_simp_tac = mslow_tac o (maddss true);
val mbest_simp_tac = mbest_tac o (maddss true);

val mfast_no_assms_force_tac = mfast_no_assms_tac o (maddss true);
val mslow_no_assms_simp_tac = mslow_no_assms_tac o (maddss true);
val mbest_no_assms_simp_tac = mbest_no_assms_tac o (maddss true);

(* cs attributes *)

(*
fun cs_attrib cid f  =
  Thm.declaration_attribute (fn th => fn context => map_cs cid (f (SOME (SOME cid, context)) th) context);
*)

fun cs_attrib cid f  =
  Thm.declaration_attribute (fn th => fn context => (
    let
      val context' = map_cs cid (f (SOME (SOME cid, context)) th) context;
(*
     val ctxt' = (Context.proof_of context');
      val _ = writeln(Display.string_of_thm ctxt' th);
      val _ = Pretty.writeln(pretty_cs ctxt' (fst (get_css cid context'))); 
*)
    in
      context'
    end
  )
);


fun safe_elim cid = (cs_attrib cid) o addSE;
fun safe_intro cid = (cs_attrib cid) o addSI;
fun safe_dest cid = (cs_attrib cid) o addSD;
fun haz_elim cid = (cs_attrib cid) o addE;
fun haz_intro cid = (cs_attrib cid) o addI;
fun haz_dest cid = (cs_attrib cid) o addD;
 

fun rule_del cid =
  Thm.declaration_attribute (fn th => fn context =>
    context |> map_cs cid (delrule (SOME (SOME cid, context)) th) |>
    Thm.attribute_declaration Context_Rules.rule_del th);

val scan_plus = Args.$$$ "*";

val scan_id = (Args.$$$ "(" |-- Args.name) --|  Args.$$$ ")";

fun add a b x =
  (Scan.lift (
    (Args.bang >> K a || Scan.succeed b) --
    scan_id -- 
    Scan.option Parse.nat) >> (fn ((f, i), n) => f i n)) x


val setup_cs_attrs =
  Attrib.setup @{binding mintro} (add safe_intro haz_intro) 
    "declaration of Classical introduction rule" #>
  Attrib.setup @{binding melim} (add safe_elim haz_elim) 
    "declaration of Classical elimination rule" #>
  Attrib.setup @{binding mdest} (add safe_dest haz_dest)
    "declaration of Classical destruction rule" #>
  Attrib.setup @{binding mrule} (Scan.lift (scan_id -- (Args.del >> K rule_del)) >> (fn (i, f) => f i))
    "remove declaration of intro/elim/dest rule"


(* ss attributes *)

fun ss_attrib cid f  =
  Thm.declaration_attribute (fn th => fn context => (
    let
      val ctxt = Context.proof_of context;      
      fun fss ss = simpset_of (f th (put_simpset ss ctxt));
      val context' = map_ss cid fss context;
    in
      context'
    end
  )
);

fun madd_simp thm ss = Simplifier.addsimps (ss, [thm]);

fun mdel_simp thm ss = Simplifier.delsimps (ss, [thm]);

fun msimp_add cid = (ss_attrib cid madd_simp);

fun msimp_del cid = (ss_attrib cid mdel_simp);

fun mcong_add cid = (ss_attrib cid Simplifier.add_cong);

fun mcong_del cid = (ss_attrib cid Simplifier.del_cong);

fun msplit_add cid = ss_attrib cid Splitter.add_split;

fun msplit_del cid = ss_attrib cid Splitter.del_split;

(*

fun msimp_add cid = (ss_attrib cid Simplifier.add_simp);

fun msimp_del cid = (ss_attrib cid Simplifier.del_simp);
fun add_del add del x =
  (Scan.lift (
    (Args.add >> K add || Args.del >> K del || Scan.succeed add) --
    scan_id) >> (fn (f, i) => f i)) x
*)

fun add_del add del x =
  (Scan.lift (scan_id -- 
    (Args.add >> K add || Args.del >> K del || Scan.succeed add)) >> (fn (i, f) => (f i))) x


val setup_ss_attrs =
  Attrib.setup @{binding msimp} (add_del msimp_add msimp_del) 
    "declaration of Simplifier rewrite rule"  #>
  Attrib.setup @{binding msplit} (add_del msplit_add msplit_del) 
    "declaration of Simplifier split rule"  #>
  Attrib.setup @{binding mcong} (add_del mcong_add mcong_del) 
    "declaration of Simplifier congruence rule"  





(* iffs: addition of rules to simpsets and clasets simultaneously *)

local

(*Takes (possibly conditional) theorems of the form A<->B to
        the Safe Intr     rule B==>A and
        the Safe Destruct rule A==>B.
  Also ~A goes to the Safe Elim rule A ==> ?R
  Failing other cases, A is added as a Safe Intr rule*)

fun add_iff safe unsafe =
  Thm.declaration_attribute (fn th =>
    let
      val n = nprems_of th;
      val (elim, intro) = if n = 0 then safe else unsafe;
      val zero_rotate = zero_var_indexes o rotate_prems n;
    in
      Thm.attribute_declaration intro (zero_rotate (th RS Data.iffD2)) #>
      Thm.attribute_declaration elim (Tactic.make_elim (zero_rotate (th RS Data.iffD1)))
      handle THM _ =>
        (Thm.attribute_declaration elim (zero_rotate (th RS Data.notE))
          handle THM _ => Thm.attribute_declaration intro th)
    end);

fun del_iff del = Thm.declaration_attribute (fn th =>
  let val zero_rotate = zero_var_indexes o rotate_prems (nprems_of th) in
    Thm.attribute_declaration del (zero_rotate (th RS Data.iffD2)) #>
    Thm.attribute_declaration del (Tactic.make_elim (zero_rotate (th RS Data.iffD1)))
    handle THM _ =>
      (Thm.attribute_declaration del (zero_rotate (th RS Data.notE))
        handle THM _ => Thm.attribute_declaration del th)
  end);

in

fun miff_add cid =
  Thm.declaration_attribute (fn th =>
    Thm.attribute_declaration (add_iff
      (safe_elim cid NONE, safe_intro cid NONE)
      (haz_elim cid NONE, haz_intro cid NONE)) th
    #> Thm.attribute_declaration (msimp_add cid) th 
    #> Thm.attribute_declaration Simplifier.simp_add th);

fun miff_add' _ =
  add_iff
    (Context_Rules.elim_query NONE, Context_Rules.intro_query NONE)
    (Context_Rules.elim_query NONE, Context_Rules.intro_query NONE);

fun miff_del cid =
  Thm.declaration_attribute (fn th =>
    Thm.attribute_declaration (del_iff (rule_del cid)) th #>
    Thm.attribute_declaration (del_iff Context_Rules.rule_del) th #>
    Thm.attribute_declaration (msimp_del cid) th #>
    Thm.attribute_declaration Simplifier.simp_del th);

end;



(** proof methods **)

local

fun msome_rule_tac (cid, ctxt) facts = SUBGOAL (fn (goal, i) =>
  let
    val [rules1, rules2, rules4] = Context_Rules.find_rules false facts goal ctxt;
    val {xtra_netpair, ...} = rep_claset_of (cid, ctxt);
    val rules3 = Context_Rules.find_rules_netpair true facts goal xtra_netpair;
    val rules = rules1 @ rules2 @ rules3 @ rules4;
    val ruleq = Drule.multi_resolves facts rules;
  in
    Method.trace ctxt rules;
    fn st => Seq.maps (fn rule => Tactic.rtac rule i st) ruleq
  end)
  THEN_ALL_NEW Goal.norm_hhf_tac;

in

fun mrule_tac ctxt [] facts = msome_rule_tac ctxt facts
  | mrule_tac _ rules facts = Method.rule_tac rules facts;

fun mdefault_tac (cid, ctxt) rules facts =
  HEADGOAL (mrule_tac (cid, ctxt) rules facts) ORELSE
  Class.default_intro_tac ctxt facts;

end;


(* automatic methods *)


val mintroN = "mintro";
val melimN = "melim";
val mdestN = "mdest";
val mdelN = "mdel";

fun mcla_modifiers cid =
 [Args.$$$ mdestN -- Args.bang_colon >> K ((I, safe_dest cid NONE): Method.modifier),
  Args.$$$ mdestN -- Args.colon >> K (I, haz_dest cid NONE),
  Args.$$$ melimN -- Args.bang_colon >> K (I, safe_elim cid NONE),
  Args.$$$ melimN -- Args.colon >> K (I, haz_elim cid NONE),
  Args.$$$ mintroN -- Args.bang_colon >> K (I, safe_intro cid NONE),
  Args.$$$ mintroN -- Args.colon >> K (I, haz_intro cid NONE),
  Args.$$$ mdelN -- Args.colon >> K (I, rule_del cid)];

fun cla_method tac = Scan.lift scan_id :-- (fn cid => (Method.sections (mcla_modifiers cid))) >> (fn (cid, _) => (SIMPLE_METHOD o (fn ctxt => (tac (cid, ctxt)))));
fun cla_method' tac = Scan.lift scan_id :-- (fn cid => Method.sections (mcla_modifiers cid)) >> (fn (cid, _) => (SIMPLE_METHOD' o (fn ctxt => tac (cid, ctxt))));


val setup_methods =
  Method.setup @{binding mdefault}
   (Scan.lift scan_id -- Attrib.thms >> (fn (cid, rules) => fn ctxt => METHOD (mdefault_tac (cid, ctxt) rules)))
    "apply some intro/elim rule (potentially classical)" #>
  Method.setup @{binding mrule}
    (Scan.lift scan_id -- Attrib.thms >> (fn (cid, rules) => fn ctxt => METHOD (HEADGOAL o mrule_tac (cid, ctxt) rules)))
    "apply some intro/elim rule (potentially classical)" #>
  Method.setup @{binding mclarify} (cla_method' (CHANGED_PROP oo mclarify_tac))
    "repeatedly apply safe steps" #>
  Method.setup @{binding mfast} (cla_method' mfast_tac) "classical prover (depth-first)" #>
  Method.setup @{binding mslow} (cla_method' mslow_tac) "classical prover (slow depth-first)" #>
  Method.setup @{binding mbest} (cla_method' mbest_tac) "classical prover (best-first)" #>
  Method.setup @{binding mdeepen}
   (Scan.lift scan_id :-- (fn cid => Scan.lift (Scan.optional Parse.nat 4) --| Method.sections (mcla_modifiers cid))
      >> (fn (cid, n) => fn ctxt => SIMPLE_METHOD' (mdeepen_tac (cid, ctxt) n)))
    "classical prover (iterative deepening)" #>
  Method.setup @{binding msafe} (cla_method (CHANGED_PROP o msafe_tac))
    "classical prover (apply safe rules)" #>
  Method.setup @{binding msafe_step} (cla_method' msafe_step_tac)
    "single classical step (safe rules)" #>
  Method.setup @{binding minst_step} (cla_method' minst_step_tac)
    "single classical step (safe rules, allow instantiations)" #>
  Method.setup @{binding mstep} (cla_method' mstep_tac)
    "single classical step (safe and unsafe rules)" #>
  Method.setup @{binding mslow_step} (cla_method' mslow_step_tac)
    "single classical step (safe and unsafe rules, allow backtracking)" #>
  Method.setup @{binding mclarify_step} (cla_method' mclarify_step_tac)
    "single classical step (safe rules, without splitting)" #>
  Method.setup @{binding mclarify_no_assms} (cla_method' (CHANGED_PROP oo mclarify_no_assms_tac))
    "repeatedly apply safe steps" #>
  Method.setup @{binding mfast_no_assms} (cla_method' mfast_no_assms_tac) "classical prover (depth-first)" #>
  Method.setup @{binding mslow_no_assms} (cla_method' mslow_no_assms_tac) "classical prover (slow depth-first)" #>
  Method.setup @{binding mbest_no_assms} (cla_method' mbest_no_assms_tac) "classical prover (best-first)" #>
  Method.setup @{binding mdeepen_no_assms}
   (Scan.lift scan_id :-- (fn cid => Scan.lift (Scan.optional Parse.nat 4) --| Method.sections (mcla_modifiers cid))
      >> (fn (cid, n) => fn ctxt => SIMPLE_METHOD' (mdeepen_no_assms_tac (cid, ctxt) n)))
    "classical prover (iterative deepening)" #>
  Method.setup @{binding msafe_no_assms} (cla_method (CHANGED_PROP o msafe_no_assms_tac))
    "classical prover (apply safe rules)" #>
  Method.setup @{binding msafe_no_assms_step} (cla_method' msafe_no_assms_step_tac)
    "single classical step (safe rules)" #>
  Method.setup @{binding mstep_no_assms} (cla_method' mstep_no_assms_tac)
    "single classical step (safe and unsafe rules)" #>
  Method.setup @{binding mslow_no_assms_step} (cla_method' mslow_no_assms_step_tac)
    "single classical step (safe and unsafe rules, allow backtracking)" #>
  Method.setup @{binding mclarify_no_assms_step} (cla_method' mclarify_no_assms_step_tac)
    "single classical step (safe rules, without splitting)";




(** concrete syntax **)

(* attributes *)

fun miff_att x = (Scan.lift (
 scan_id -- (Args.del >> K miff_del ||
  Scan.option Args.add -- Args.query >> K miff_add' ||
  Scan.option Args.add >> K miff_add)) >> (fn (i, f) => f i)) x;


(* method modifiers *)

val miffN = "miff";
val msimpN = "msimp";
val mcongN = "mcong";
val monlyN = "only";
val msplitN = "msplit";

fun miff_modifiers cid =
 [Args.$$$ miffN -- Scan.option Args.add -- Args.colon >> K ((I, miff_add cid): Method.modifier),
  Args.$$$ miffN -- Scan.option Args.add -- Args.query_colon >> K (I, miff_add' cid),
  Args.$$$ miffN -- Args.del -- Args.colon >> K (I, miff_del cid)];

fun mcong_modifiers cid =
 [Args.$$$ mcongN -- Args.colon >> K ((I, mcong_add cid) : Method.modifier),
  Args.$$$ mcongN -- Args.add -- Args.colon >> K (I, mcong_add cid),
  Args.$$$ mcongN -- Args.del -- Args.colon >> K (I, mcong_del cid)]

fun msimp_modifiers cid =
  let
    val clear_ss = (fn ss => simpset_of (Raw_Simplifier.clear_simpset (put_simpset ss @{context})))
  in
    [Args.$$$ msimpN -- Args.colon >> K (I, msimp_add cid),
     Args.$$$ msimpN -- Args.add -- Args.colon >> K (I, msimp_add cid),
     Args.$$$ msimpN -- Args.del -- Args.colon >> K (I, msimp_del cid),
     Args.$$$ msimpN -- Args.$$$ monlyN -- Args.colon
       >> K (Context.proof_map (map_ss cid clear_ss), msimp_add cid)]
      @ (mcong_modifiers cid)
end

fun msplit_modifiers cid =
 [Args.$$$ msplitN -- Args.colon >> K ((I, msplit_add cid): Method.modifier),
  Args.$$$ msplitN -- Args.add -- Args.colon >> K (I, msplit_add cid),
  Args.$$$ msplitN -- Args.del -- Args.colon >> K (I, msplit_del cid)];

fun mclasimp_modifiers cid =
  Simplifier.simp_modifiers @ (msplit_modifiers cid) @
  (mcla_modifiers cid) @ (miff_modifiers cid) @ (msimp_modifiers cid);


(* methods *)

fun mclasimp_method' tac =
  Scan.lift scan_id :-- (fn cid => Method.sections (mclasimp_modifiers cid)) >> (fn (cid, _) => (SIMPLE_METHOD' o (fn ctxt => tac (cid, ctxt))));

val mauto_method =
  (Scan.lift (Scan.option scan_plus) -- Scan.lift (Scan.option Parse.nat) -- (Scan.lift scan_id))  :--
    (fn (_, cid) => Method.sections (mclasimp_modifiers cid)) >> 
    (fn (((loc, NONE), cid), _) => SIMPLE_METHOD o CHANGED_PROP o (fn ctxt => (mauto_tac ((is_none loc)) (cid, ctxt)))
    |   (((loc, SOME n), cid), _) => (fn ctxt => SIMPLE_METHOD (CHANGED_PROP (mmk_auto_tac ((is_none loc)) (cid, ctxt) n))));

val mauto_no_assms_method =
  (Scan.lift (Scan.option Parse.nat) -- (Scan.lift scan_id))  :--
    (fn (_, cid) => Method.sections (mclasimp_modifiers cid)) >> (fn ((NONE, cid), _) => 
  SIMPLE_METHOD o CHANGED_PROP o (fn ctxt => (mauto_no_assms_tac true (cid, ctxt)))
    | ((SOME n, cid), _) => (fn ctxt => SIMPLE_METHOD (CHANGED_PROP (mmk_auto_no_assms_tac true (cid, ctxt) n))));

val mauto_full_method =
  (Scan.lift (Scan.option Parse.nat) -- (Scan.lift scan_id))  :--
    (fn (_, cid) => Method.sections (mclasimp_modifiers cid)) >> (fn ((NONE, cid), _) => 
  SIMPLE_METHOD o CHANGED_PROP o (fn ctxt => (mauto_full_tac true (cid, ctxt)))
    | ((SOME n, cid), _) => (fn ctxt => SIMPLE_METHOD (CHANGED_PROP (mmk_auto_full_tac true (cid, ctxt) n))));

(* theory setup *)

val mclasimp_setup =
  Attrib.setup @{binding miff} miff_att "declaration of Simplifier / Classical rules" #>
  Method.setup @{binding mfastforce} (mclasimp_method' mfast_force_tac) "combined fast and simp" #>
  Method.setup @{binding mslowsimp} (mclasimp_method' mslow_simp_tac) "combined slow and simp" #>
  Method.setup @{binding mbestsimp} (mclasimp_method' mbest_simp_tac) "combined best and simp" #>
  Method.setup @{binding mforce} (mclasimp_method' mforce_tac) "force" #>
  Method.setup @{binding mauto} mauto_method "auto" #> 
  Method.setup @{binding mauto_full} mauto_full_method "auto" #> 
  Method.setup @{binding mclarsimp} (mclasimp_method' (CHANGED_PROP oo mclarsimp_tac))
    "clarify simplified goal" #>
  Method.setup @{binding mfastforce_no_assms} (mclasimp_method' mfast_no_assms_force_tac) "combined fast and simp" #>
  Method.setup @{binding mslowsimp_no_assms} (mclasimp_method' mslow_no_assms_simp_tac) "combined slow and simp" #>
  Method.setup @{binding mbestsimp_no_assms} (mclasimp_method' mbest_no_assms_simp_tac) "combined best and simp" #>
  Method.setup @{binding mforce_no_assms} (mclasimp_method' mforce_no_assms_tac) "force" #>
  Method.setup @{binding mauto_no_assms} mauto_no_assms_method "auto" #> 
  Method.setup @{binding mclarsimp_no_assms} (mclasimp_method' (CHANGED_PROP oo mclarsimp_no_assms_tac))
    "clarify simplified goal";


(** theory setup **)

val setup = setup_cs_attrs #> setup_ss_attrs #> setup_methods #> mclasimp_setup;

fun define_css cid thy =
  thy |> Context.theory_map (new_css cid);

val _ =
(*  Outer_Syntax.local_theory @{command_spec "declare_mprover"} "declare new prover set"
    (Args.name >> (fn cid => Context.proof_map (new_css cid))); *)
  Outer_Syntax.command @{command_spec "declare_mprover"} "declare new prover set"
    (Parse.xname >> (fn cid => Toplevel.theory (define_css cid)));

val _ =
  Outer_Syntax.improper_command @{command_spec "print_mprovers"} "print context of Classical Reasoner"
    (Scan.succeed (Toplevel.unknown_context o
      Toplevel.keep (fn state =>
        let 
          val ctxt = Toplevel.context_of state
        in 
          mprint_mprover_ids (ctxt) 
        end
      )
    )
  );

val _ =
  Outer_Syntax.improper_command @{command_spec "print_mclasimpset"} "print context of Classical Reasoner"
    (Args.name >> (fn cid => Toplevel.unknown_context o
      Toplevel.keep (fn state =>
        let 
          val ctxt = Toplevel.context_of state;
(*
          val _ = mprint_mprover_ids (ctxt);
          val _ = writeln("-"^cid^"-");
*)
        in 
          mprint_clasimpset (cid, ctxt) 
        end
      )
    )
  );




end;
