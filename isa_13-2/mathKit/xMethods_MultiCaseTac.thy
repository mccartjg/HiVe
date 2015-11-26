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

header {* The \isa{multi{\isacharunderscore}cases} Method *}

theory 
  xMethods_MultiCaseTac 
  
imports 
  xHOL_Syntax
  xMethods_Chap

begin



ML{*

fun ALLGOALS_RANGE tf i j  =
  if i > j then all_tac else ((TRY (tf j)) THEN (ALLGOALS_RANGE tf i (j-1)));
*}


ML{*
(*
fun infer_tname state i aterm =
  let
    val sign = Thm.theory_of_thm state;
    val (_, _, Bi, _) = Thm.dest_state (state, i)
    val params = Logic.strip_params Bi;   (*params of subgoal i*)
    val params = rev (Term.rename_wrt_term Bi params);   (*as they are printed*)
    val (types, sorts) = Drule.types_sorts state;
    fun types' (a, ~1) = (case AList.lookup (op =) params a of NONE => types(a, ~1) | sm => sm)
      | types' ixn = types ixn;
    val ([ct], _) = Thm.read_def_cterms (sign, types', sorts) [] false [(aterm, TypeInfer.anyT [])];
  in case #T (rep_cterm ct) of
       Type (tn, _) => tn
     | _ => error ("Cannot determine type of " ^ quote aterm)
  end;
*);

  fun check_type ctxt t =
    let
      val u = singleton (Variable.polymorphic ctxt) t;
      val U = Term.fastype_of u;
      val _ = Term.is_TVar U andalso
        error ("Cannot determine type of " ^ Syntax.string_of_term ctxt u);
    in
      (u, U)
    end;


*}

ML {*

fun multi_case_tac ctxt0 (t::ts) i state =
let

  fun mct (inst::insts) i' state' = 
    let  
      val ((_, goal'), ctxt') = Variable.focus_subgoal i' state' ctxt0;
      val rule' =
            (case Induct.find_casesT ctxt'
                (#2 (check_type ctxt' (Proof_Context.read_term_schematic ctxt' inst))) of
              rule :: _ => rule
            | [] => @{thm case_split});
      val _ = Method.trace ctxt' [rule'];

      val nc' = length (prems_of rule')

      val xi' =
        (case Induct.vars_of (Thm.term_of (Thm.cprem_of rule' 1)) of
          Var (xi, _) :: _ => xi
        | _ => raise THM ("Malformed cases rule", 0, [rule']));
      val etac' = res_inst_tac ctxt' [(xi', inst)] rule' i' 
      val res_tac' = (etac' THEN (ALLGOALS_RANGE (fn i'' => mct insts i'') i' (i'+nc'-1)))
    in 
      res_tac' state'
    end
    | mct [] i' state' = all_tac state'
    handle THM _ => Seq.empty

  val ((_, goal), ctxt) = Variable.focus_subgoal i state ctxt0;
  val rule =
        (case Induct.find_casesT ctxt
            (#2 (check_type ctxt (Proof_Context.read_term_schematic ctxt t))) of
          rule :: _ => rule
        | [] => @{thm case_split});
  val _ = Method.trace ctxt [rule];

  val nc = length (prems_of rule)

  val xi =
    (case Induct.vars_of (Thm.term_of (Thm.cprem_of rule 1)) of
      Var (xi, _) :: _ => xi
    | _ => raise THM ("Malformed cases rule", 0, [rule]));
  val etac = res_inst_tac ctxt [(xi, t)] rule i 
  val res = (etac THEN (ALLGOALS_RANGE (fn i'' => mct ts i'') i (i+nc-1))) state
in 
  res
end
  | multi_case_tac ctxt0 [] i state = error("The multi case tactic requires at least one variable to instantiate")
handle THM _ => Seq.empty;


*}

ML {*

val multi_case_setup = Method.setup @{binding "multi_cases"} (Scan.lift ((Scan.repeat1 Args.name : (string list) parser) >> (fn x => (fn ctxt =>  Method.SIMPLE_METHOD (multi_case_tac ctxt x 1))))) "A complete case splitting over several variables"
*}

setup{* multi_case_setup *}

end
