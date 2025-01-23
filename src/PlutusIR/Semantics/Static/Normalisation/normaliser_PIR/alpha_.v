Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
From PlutusCert Require Import PlutusIR.

Inductive AlphaVar : list (string * string) -> string -> string -> Set :=
| alpha_var_refl x : AlphaVar [] x x
| alpha_var_cons x y z w R :
    x = z ->
    y = w ->
    AlphaVar ((x, y) :: R) z w
| alpha_var_diff x y z w R :
    x <> z -> 
    y <> w -> 
    AlphaVar R z w -> 
    AlphaVar ((x, y) :: R) z w.

Inductive Alpha : list (string * string) -> ty -> ty -> Set :=
| alpha_var x y R : 
    AlphaVar R x y -> 
    Alpha R (Ty_Var x) (Ty_Var y)
| alpha_fun s1 s2 t1 t2 R :
    Alpha R s1 s2 -> 
    Alpha R t1 t2 -> 
    Alpha R (Ty_Fun s1 t1) (Ty_Fun s2 t2)
| alpha_ifix f1 f2 t1 t2 R :
    Alpha R f1 f2 -> 
    Alpha R t1 t2 -> 
    Alpha R (Ty_IFix f1 t1) (Ty_IFix f2 t2)
| alpha_forall x y A s1 s2 R :
    Alpha ((x, y) :: R) s1 s2 -> 
    Alpha R (Ty_Forall x A s1) (Ty_Forall y A s2)
| alpha_builtin b R:
    Alpha R (Ty_Builtin b) (Ty_Builtin b)    
| alpha_lam x y A s1 s2 R :
    Alpha ((x, y) :: R) s1 s2 -> 
    Alpha R (Ty_Lam x A s1) (Ty_Lam y A s2)
| alpha_app s1 s2 t1 t2 R :
    Alpha R s1 s2 -> 
    Alpha R t1 t2 -> 
    Alpha R (Ty_App s1 t1) (Ty_App s2 t2)
.