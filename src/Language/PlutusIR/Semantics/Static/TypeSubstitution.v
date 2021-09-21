Require Import PlutusCert.Language.PlutusIR. 
Import NamedTerm.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

(** * Substitution of types *)

(** ** Implementation as a fixpoint *)
Fixpoint substituteT (X : tyname) (S T : Ty) : Ty :=
  match T with
  | Ty_Var Y => 
    if X =? Y then S else Ty_Var Y
  | Ty_Fun T1 T2 =>
    Ty_Fun (substituteT X S T1) (substituteT X S T2)
  | Ty_IFix F T =>
    Ty_IFix (substituteT X S F) (substituteT X S T)
  | Ty_Forall Y K T' =>
    if X =? Y then Ty_Forall Y K T' else Ty_Forall Y K (substituteT X S T')
  | Ty_Builtin u => 
    Ty_Builtin u
  | Ty_Lam Y K1 T' =>
    if X =? Y then Ty_Lam Y K1 T' else Ty_Lam Y K1 (substituteT X S T')
  | Ty_App T1 T2 =>
    Ty_App (substituteT X S T1) (substituteT X S T2)
  end.



(** * Multi-substitutions of types*)

Definition env := list (tyname * Ty).

Fixpoint msubstT (ss : env) (T : Ty) : Ty :=
  match ss with
  | nil => T
  | (a, T0) :: ss' => msubstT ss' (substituteT a T0 T)
  end.