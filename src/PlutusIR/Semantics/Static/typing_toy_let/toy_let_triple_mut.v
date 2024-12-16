Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

From PlutusCert Require Import Util.List.

Inductive ty := TyBool.

Inductive term := 
    | TBool : bool -> term
    (* | TVar : string -> term *)
    | TLet : list TB -> term -> term
    with TB := TBI : string -> ty -> term -> TB.

Definition flatten {A : Type} (l : list (list A)) := List.concat (rev l).

Definition binds_Gamma (b : TB) : list (string * ty) :=
  match b with
  | TBI x T t => (x, T) :: nil
  end.

Inductive has_type : (list (string * ty)) -> term -> ty -> Prop :=
    | HT_Bool : forall Γ b, has_type Γ (TBool b) TyBool
    (* | Ty_Var : forall x Γ T, lookup x Γ = Some T -> has_type Γ (TVar x) T *)
    | HT_Let : forall Γ bs t T Γ', 
        Γ' = flatten (map binds_Gamma bs) ++ Γ ->
        bs_wf Γ' bs ->
        has_type Γ' t T -> 
        has_type Γ (TLet bs t) T
with bs_wf : list (string * ty) -> list TB -> Prop :=
    | WF_bs_Nil : forall Γ, bs_wf Γ []
    | WF_bs_Cons : forall Γ b bs,
        b_wf Γ b ->
        bs_wf Γ bs ->
        bs_wf Γ (b::bs)
with b_wf : list (string * ty) -> TB -> Prop :=
    | W_term : forall Γ x T' t', 
        has_type Γ t' T' ->
        b_wf Γ (TBI x T' t').

Scheme has_type_mut_ind := Induction for has_type Sort Prop
with bs_wf_mut_ind := Induction for bs_wf Sort Prop
with b_wf_mut_ind := Induction for b_wf Sort Prop.

Check has_type_ind.
Check has_type_mut_ind.


Definition b_wf_check (type_check : list (string * ty) -> term -> option ty) (Γ : list (string * ty)) (tb : TB) : bool :=
    match tb with TBI x T t =>
        match type_check Γ t with
        | Some T => true
        | _ => false
        end
    end.

Definition bs_wf_check : (list (string * ty) -> TB -> bool) -> list (string * ty) -> (list TB) -> bool :=
    fun b_wf =>
    fix f Γ bs :=
        match bs with 
        | (b'::bs') => b_wf Γ b' && f Γ bs'
        | [] => true
        end.

Fixpoint type_check (Γ : list (string * ty)) (term : term) : option ty :=
    match term with
    | TBool b => Some TyBool
    (* | TVar x => lookup x Γ *)
    | TLet bs t => 
        let Γ' := flatten (map binds_Gamma bs) ++ Γ in
        if bs_wf_check (b_wf_check type_check) Γ' bs then
                                    type_check Γ' t else None
    end.

(* works without context changes!*)
Theorem type_check_complete Γ t T :
    has_type Γ t T -> type_check Γ t = Some T.
Proof.
    intros.
    apply has_type_mut_ind with         
        (P := fun Γ t T _ => type_check Γ t = Some T)
        (P0 := fun Γ l _ => bs_wf_check (b_wf_check type_check) Γ l = true) 
        (P1 := fun Γ b _ => b_wf_check type_check Γ b = true) 
        ; auto.
    - intros. simpl. subst. rewrite H0. auto.
    - intros. simpl. rewrite H0. auto.
    - intros. simpl. rewrite H0. auto.
Qed.
