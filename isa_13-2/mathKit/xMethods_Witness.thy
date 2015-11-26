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

header {* The \isa{witness} Method *}

theory 
  xMethods_Witness 

imports
  xHOL_Syntax
  xMethods_Chap

begin

ML {*

fun wit_meth t ctxt =
let
        val thy = Proof_Context.theory_of ctxt;
        val ct = cterm_of thy t;
        val {T, ...} = rep_cterm ct;
        val cT = ctyp_of thy T;
        val thm = (Drule.instantiate' [SOME cT] [NONE, SOME ct] exI);
in
  Method.SIMPLE_METHOD (resolve_tac [thm] 1)
end;

val witness_setup =
   Method.setup @{binding "witness"} (Args.term >> (fn x => (fn ctxt => wit_meth x ctxt))) 
     "propose witness for existential goal";

*}

setup {* witness_setup *}

end
