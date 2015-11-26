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

theory Orders 

imports 
  Lattice_Morphism 
  Lattice_Instance 
  Order_Quotient  
  Lattice_FixPoint

begin

(*


ML{
val ctxt = @{context};
val ss1 = Simplifier.simpset_of ctxt

}
ML{
val ss2 = snd (MProver.mclasimpset_of ("wind",ctxt))

}
ML{
val ss2' = Simplifier.context ctxt ss2
}
ML{
Simplifier.merge_ss (ss1, ss2')
}






ML{
( with Lattice_Instance and Order_Quotient has conext NONE in simpset! )
MProver.mclasimpset_of ("wind", @{context})
}

print_mclasimpset "wind"

lemma "{ p | p \<in> CL_A \<bullet> { x | x \<in> CL_X \<bullet> p x}} = { x | x \<in> CL_X \<bullet> { p | p \<in> CL_A \<bullet> p x}}"
    apply (mauto(wind))
sorry
lemma "(\<lSUP> p | p \<in> CL_A \<bullet> (\<lSUP> x | x \<in> CL_X \<bullet> p x)) = (\<lSUP> x | x \<in> CL_X \<bullet> (\<lSUP> p | p \<in> CL_A \<bullet> p x))"
  apply (simp add: Sup_Sup)
  apply (mauto(wind))
  done
*)

end
