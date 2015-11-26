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
  xMethods_Multi_Prover

imports
  xMethods_Chap

keywords 
  "print_mprovers" "print_mclasimpset" :: diag and
  "declare_mprover" :: thy_decl

begin

ML_file "multiprover.ML"

ML {*

structure MProver = MProver
(
  structure Splitter = Splitter
  val imp_elim = @{thm imp_elim}
  val not_elim = @{thm notE}
  val swap = @{thm swap}
  val classical = @{thm classical}
  val sizef = Drule.size_of_thm
  val hyp_subst_tacs = [Hypsubst.hyp_subst_tac]
  val notE = @{thm notE}
  val iffD1 = @{thm iffD1}
  val iffD2 = @{thm iffD2}
);

structure Basic_MProver: BASIC_MPROVER = MProver; 
open Basic_MProver;

*}

ML {*
MProver.mmap_claset
*}

setup MProver.setup

(*
setup {* MProver.setup *}
*)

(*

Look at adding an antiquotation.

setup {*
  ML_Antiquote.value @{binding claset}
    (Scan.succeed "Classical.claset_of ML_context")
*}

*)

end
