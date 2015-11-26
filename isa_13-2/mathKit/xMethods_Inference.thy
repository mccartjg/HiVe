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

header {* The \isa{inference} Method *}

theory 
  xMethods_Inference 

imports 
  xMethods_Multi_Prover

begin

declare_mprover "inference"

declare
  impI [mintro!(inference)]
  iffI [mintro!(inference)]
  allI [mintro!(inference)]
  conjI [mintro!(inference)]
  conjE [melim!(inference)]
  disjE [melim!(inference)]
  exE [melim!(inference)]

declaration {*

K (MProver.map_cs "inference" 
  (fn cs => 
    #2 (("inference", cs) maddSafter 
          ("use_assumptions", (eresolve_tac [impE, allE] THEN' assume_tac))))) 

*}

end
