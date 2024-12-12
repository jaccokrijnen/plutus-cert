Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

From PlutusCert Require Import Util.List.

Inductive ty := TyBool.

Inductive term := 
    | TBool : bool -> term
    | TVar : string -> term
    | TLet : TB -> term -> term
    with TB := TBI : string -> ty -> term -> TB.

Inductive has_type : list (string * ty) -> term -> ty -> Prop :=
    | Ty_Bool : forall Γ b, has_type Γ (TBool b) TyBool
    | Ty_Var : forall x Γ T, lookup x Γ = Some T -> has_type Γ (TVar x) T
    | Ty_Let : forall x T_x t_x t T Γ, 
        b_wf Γ (TBI x T_x t_x) ->
        has_type ((x, T_x)::Γ) t T -> 
        has_type Γ (TLet (TBI x T_x t_x) t) T
with b_wf : list (string * ty) -> TB -> Prop :=
    | W_term : forall Γ x T_x t_x, 
        has_type Γ t_x T_x ->
        b_wf Γ (TBI x T_x t_x).

Definition b_wf_check (type_check : list (string * ty) -> term -> option ty) (Γ : list (string * ty)) (t : term) (T : ty) : bool :=
    match type_check Γ t with
    | Some T => true
    | _ => false
    end.

Fixpoint type_check (Γ : list (string * ty))  (term : term) : option ty :=
    match term with
    | TBool b => Some TyBool
    | TVar x => lookup x Γ
    | TLet (TBI x T_x t_x) t => if b_wf_check type_check Γ t_x T_x then
                                    type_check ((x, T_x)::Γ) t else None
    end.

Theorem type_check_complete Γ t T :
    has_type Γ t T -> type_check Γ t = Some T.
Proof.
    intros.
    induction H.
    - admit.
    - admit.
    - simpl.
      rewrite IHhas_type.
      (* ????*)
Admitted.
