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

Inductive has_type : list (string * ty) -> term -> ty -> Prop :=
    (* | HT_Bool : forall Γ b, has_type Γ (TBool b) TyBool *)
    (* | Ty_Var : forall x Γ T, lookup x Γ = Some T -> has_type Γ (TVar x) T *)
    | HT_Let : forall Γ x T' t' t T, 
        b_wf ((x, T')::Γ) (TBI x T' t') ->
        has_type ((x, T')::Γ) t T -> 
        has_type Γ (TLet (TBI x T' t') t) T
with b_wf : list (string * ty) -> TB -> Prop :=
    | W_term : forall Γ x T' t', 
        has_type Γ t' T' ->
        b_wf Γ (TBI x T' t').

Scheme has_type_mut_ind := Induction for has_type Sort Prop
with b_wf_mut_ind := Induction for b_wf Sort Prop.

Check has_type_ind.
Check has_type_mut_ind.


Definition b_wf_check (type_check : list (string * ty) -> term -> option ty) (Γ : list (string * ty)) (t : term) (T : ty) : bool :=
    match type_check Γ t with
    | Some T => true
    | _ => false
    end.

Fixpoint type_check (Γ : list (string * ty)) (term : term) : option ty :=
    match term with
    (* | TBool b => Some TyBool *)
    (* | TVar x => lookup x Γ *)
    | TLet (TBI x T' t') t => if b_wf_check type_check ((x, T')::Γ) t' T' then
                                    type_check ((x, T')::Γ) t else None
    end.



(* works without context changes!*)
Theorem type_check_complete Γ t T :
    has_type Γ t T -> type_check Γ t = Some T.
Proof.
    intros.
    (* generalize dependent Γ. *)
    apply has_type_mut_ind with 
    (P0 := fun Γ b (g : b_wf Γ b) => match b with | TBI x T t => type_check Γ t = Some T end) 
        
        (P := fun (Γ' : list (string * ty)) (t : term) (T : ty) (uhm : has_type Γ' t T) => type_check Γ' t = Some T).
    - intros. simpl. rewrite H1.
        unfold b_wf_check.
        rewrite H0.
        reflexivity.
    - intros. simpl.  auto.
    - auto.
Qed.
