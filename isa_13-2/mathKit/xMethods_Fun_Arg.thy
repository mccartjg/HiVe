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

header {* The \isa{fcong} Method *}

theory 
  xMethods_Fun_Arg 

imports
  xMethods_Witness

begin

ML {*

fun fun_arg_tac i st = 
if prems_of st = [] then no_tac st else
let 
  val sgn = theory_of_thm st;
  fun sps k (Const("==>", _) $ _ $ g) = sps k g
   |  sps k (Const("all", _) $ Abs(n, T, g)) = sps (k+1) (subst_bound (Var((n,k), T), g))
   |  sps k g = g;
  val tm = (sps 0 (hd (prems_of st)));
  fun inst_fun_cong f g x =
  let
    val cf = cterm_of sgn f;
    val cg = cterm_of sgn g;
    val cx = cterm_of sgn x;
    val {T = Type(_, [xT, fxT]), ...} = rep_cterm cf;
    val cxT = ctyp_of sgn xT;
    val cfxT = ctyp_of sgn fxT;
  in
    Drule.instantiate' [SOME cxT, SOME cfxT] [SOME cf, SOME cg, SOME cx] fun_cong
  end;  
  fun inst_arg_cong f x y =
  let
    val cf = cterm_of sgn f;
    val cx = cterm_of sgn x;
    val cy = cterm_of sgn y;
    val {T = Type(_, [xT, fxT]), ...} = rep_cterm cf;
    val cxT = ctyp_of sgn xT;
    val cfxT = ctyp_of sgn fxT;
  in
    Drule.instantiate' [SOME cxT, SOME cfxT] [SOME cx, SOME cy, SOME cf] arg_cong
  end;  
  fun inst_fun_arg_tac (_ $ (_ $ (f $ x) $ (g $ y))) i =
    if x = y then resolve_tac [inst_fun_cong f g x] i
    else if f = g then resolve_tac [inst_arg_cong f x y] i
    else no_tac
    | inst_fun_arg_tac _ _ = no_tac;
in 
  inst_fun_arg_tac tm i st 
end;

val fun_arg_setup =
   Method.setup @{binding "fun_arg"} (Scan.succeed (K (Method.SIMPLE_METHOD' fun_arg_tac))) 
     "apply application congruence rules";

*}

setup {* fun_arg_setup *}

end
