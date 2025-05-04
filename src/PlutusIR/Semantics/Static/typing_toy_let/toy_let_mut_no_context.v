Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

From PlutusCert Require Import Util.List.

Inductive ty := TyBool.

Inductive term := 
    (* | TBool : bool -> term *)
    (* | TVar : string -> term *)
    | TLet : TB -> term -> term
    with TB := TBI : string -> ty -> term -> TB.

Inductive has_type :  term -> ty -> Prop :=
    (* | HT_Bool : forall Γ b, has_type Γ (TBool b) TyBool *)
    (* | Ty_Var : forall x Γ T, lookup x Γ = Some T -> has_type Γ (TVar x) T *)
    | HT_Let : forall x T' t' t T, 
        b_wf (TBI x T' t') ->
        has_type t T -> 
        has_type (TLet (TBI x T' t') t) T
with b_wf :TB -> Prop :=
    | W_term : forall x T' t', 
        has_type t' T' ->
        b_wf (TBI x T' t').

Scheme has_type_mut_ind := Induction for has_type Sort Prop
with b_wf_mut_ind := Induction for b_wf Sort Prop.

Check has_type_ind.
Check has_type_mut_ind.


Definition b_wf_check (type_check : term -> option ty) (t : term) (T : ty) : bool :=
    match type_check t with
    | Some T => true
    | _ => false
    end.

Fixpoint type_check (term : term) : option ty :=
    match term with
    (* | TBool b => Some TyBool *)
    (* | TVar x => lookup x Γ *)
    | TLet (TBI x T' t') t => if b_wf_check type_check t' T' then
                                    type_check t else None
    end.



(* works without context changes!*)
Theorem type_check_complete t T :
    has_type t T -> type_check t = Some T.
Proof.
    intros.
    apply has_type_mut_ind with 
    (P0 := fun b (g : b_wf b) => match b with | TBI x T t => type_check t = Some T end) 
        
        (P := fun (t : term) (T : ty) (uhm : has_type t T) => type_check t = Some T).
    - intros. simpl. rewrite H1.
        unfold b_wf_check.
        rewrite H0.
        reflexivity.
    - intros. simpl.  auto.
    - auto.
Qed.
