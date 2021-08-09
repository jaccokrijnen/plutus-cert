# Problematic case

(* FAIL: *) empty |- "Bool" -> "Bool" :: * 
(* OKAY: *) empty |-ok ("Bool" = True | False with matchBool)         
(* OKAY: *) empty,"Bool" |- (\x : "Bool". x) : "Bool" -> "Bool"     
-----------------------------------------------------------------------------
(* FAIL: *)
empty |- let ("Bool" = True | False with matchBool) 
         in (\x : "Bool". x) 
      : "Bool" -> "Bool"



# Ignore below

(* OKAY: *) empty |- (forall R, R -> R -> R) -> (forall R, R -> R -> R) :: *       
(* OKAY: *) empty |-ok ("Bool" = True | False with matchBool)         
(* FAIL: *) empty,Bool |- (\x : "Bool". x) 
                       : (forall R, R -> R -> R) -> (forall R, R -> R -> R)
-----------------------------------------------------------------------------
empty |- let ("Bool" = True | False with matchBool) 
         in (\x : "Bool". x) 
      : (forall R, R -> R -> R) -> (forall R, R -> R -> R)