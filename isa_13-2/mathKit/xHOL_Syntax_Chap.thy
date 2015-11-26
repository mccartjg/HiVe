(*<*)
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
  xHOL_Syntax_Chap
  
imports 
  Complex_Main
(*  Multivariate_Analysis *)
(* Cannot include full development because of conflict over product order definition 
   (in Linear_Algebra.thy, and seemingly not used in the development): 
   using private copy with conflict resolved
   If included then can omit Countable_Set import below.
*)
(*J: 19/11/2015 
  "Multivariate_Analysis/Multivariate_Analysis"
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
   "pGCL/pGCL"
*)
  "~~/src/HOL/Library/Infinite_Set"
(*  "~~/src/HOL/Multivariate_Analysis/L2_Norm"
  "~~/src/HOL/Multivariate_Analysis/Finite_Cartesian_Product"
  "~~/src/HOL/Multivariate_Analysis/Integration" 
*)
  "~~/src/HOL/Library/Countable_Set"
  "~~/src/HOL/Library/Wfrec"
  "~~/src/HOL/Library/Old_Recdef"
  "~~/src/HOL/Library/AList"
  "~~/src/HOL/Library/DAList"
  "~~/src/HOL/Library/Zorn"


(*  Hyperreal *) 
  
begin(*>*)

chapter {* A Z-like syntax for HOL *}

(*<*)end(*>*)
