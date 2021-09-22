From PlutusCert Require Import
  Language.PlutusIR
  Semantics.Static
  Semantics.Static.Implementations.Named
  Semantics.Static.Weakening
  .
Import NamedTerm.

From Coq Require Import
  Strings.String.

Open Scope string_scope.

(*
T : K
F : (K => * ) => (K => * )
---------
ifix F T : *


*)


(* Convenience: type-level non-recursive let *)
Definition Ty_Let var k ty_bound ty_body : Ty :=
  Ty_App (Ty_Lam var k ty_body) (ty_bound).

Definition k_star_star := (Kind_Arrow Kind_Base Kind_Base).
Definition ty_id := Ty_Lam "X" Kind_Base (Ty_Var "X").



(* Encode the Z combinator *)

(* Type to instantiate IFix for regular fixpoint
   combinator. "F" in IFix F T, this fixes
   the kind K of T to be * -> *
*)
Definition Fix_0_inst : Ty :=
  (Ty_Lam "Rec" (Kind_Arrow k_star_star Kind_Base)
    (Ty_Lam "F" (k_star_star)
      (Ty_App (Ty_Var "F")
        (Ty_App (Ty_Var "Rec") (Ty_Var "F"))
      )
    )
  ).

Definition Fix_0 (t : Ty) : Ty :=
  Ty_IFix Fix_0_inst t
.

Lemma Fix_0_well_kinded : forall t,
  emptyContext |-* t : k_star_star ->
  emptyContext |-* (Fix_0 t) : Kind_Base.
Proof. repeat econstructor. assumption. Qed.

(* wrap specialized to Fix0_inst *)
Definition wrap_0 (ty : Ty) (t : Term) : Term :=
  IWrap Fix_0_inst ty t.

(* Instantiation for the second argument of IFix
   (first argument of Fix_0)
   This has to be of kind * -> * (not as a meta-construction that
   accepts types, otherwise it cannot be used as argument of wrap or IFix
*)
Definition Self_inst :=
  (Ty_Lam "A" Kind_Base
    ( Ty_Lam "Rec" Kind_Base
        ( Ty_Fun (Ty_Var "Rec") (Ty_Var "A") )
    )
  ).

Definition Self :=
  (Ty_Lam "A" Kind_Base
    (Fix_0 (Ty_App Self_inst (Ty_Var "A"))
    )
  ).

Lemma Self_well_kinded : emptyContext |-* Self : k_star_star.
Proof. repeat econstructor. Qed.

Definition self_type :=
  (
    Ty_Forall "A" Kind_Base
    (
      (Ty_Fun
        (Ty_Fun
          (Ty_App Self (Ty_Var "A"))
          (Ty_Var "A")
        )
        (Ty_App Self (Ty_Var "A")
        )
      )
    )
  ).

Definition self :=
  TyAbs "A" Kind_Base
    ( LamAbs "f" (Ty_Fun (Ty_App Self (Ty_Var "A")) (Ty_Var "A"))
        (wrap_0 Self_inst (Var "f"))
    ).


Definition beta := beta_reduce _ _ substituteT.
Eval cbv in beta self_type.
Lemma self_well_typed :
  emptyContext |-+ self : (beta self_type).
Proof.
  unfold self_type, self, Self, wrap_0, Fix_0.
  unfold Self_inst.
  simpl.
  repeat econstructor.
  (* we are stuck, since the type has to be normalized *)
  Fail apply T_LamAbs.
Abort.
