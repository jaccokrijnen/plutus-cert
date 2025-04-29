Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Ascii.
Require Import Lia.
From Equations Require Import Equations.

Set Implicit Arguments.

From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Folds.
From PlutusCert Require Import Util.List.

Local Open Scope string_scope.

Section list_size.
  Context {A : Type} (f : A -> nat).

  Equations list_size (l : list A) : nat :=
  list_size nil := 0;
  list_size (cons x xs) := S (f x + list_size xs).

  Lemma In_list_size:
    forall x xs, In x xs -> f x < S (list_size xs).
  Proof.
    intros. funelim (list_size xs); simpl in x. destruct H.
    destruct H0.
    - subst; lia.
    - specialize (H _ H0). lia.
  Qed.
End list_size.
Transparent list_size.

Definition term_size (t : term) : nat :=
  foldTermUse (fun xs => 1 + list_sum xs) t.

Definition binding_size (b : binding) : nat :=
  foldBindingUse (fun xs => 1 + list_sum xs) b.

Definition bindings_size (bs : list binding) : nat :=
  foldBindingsUse (fun xs => 1 + list_sum xs) bs.

(*
Lemmas for showing how `term_size` (defined as a fold) reduces
*)

Axiom term_size_let : forall r t bs,
  term_size (Let r bs t)  = 1 + (term_size t) + (bindings_size bs).
(*
  unfold term_size, bindings_size, foldTermUse, foldBindingsUse.
  unfold foldTerm at 1. unfold a_Let; simpl.
  simpl.
reflexivity. Qed.
*)

Lemma term_size_apply : forall s t,
  term_size (Apply s t) = 1 + list_sum [term_size s ; term_size t].
reflexivity. Qed.

Lemma term_size_tyabs : forall n k t,
  term_size (TyAbs n k t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma term_size_lamabs : forall n k t,
  term_size (LamAbs n k t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma term_size_tyinst : forall t ty,
  term_size (TyInst t ty) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma term_size_iwrap : forall ty1 ty2 t,
  term_size (IWrap ty1 ty2 t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma term_size_unwrap : forall t,
  term_size (Unwrap t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma binding_size_TermBind s v t:
  binding_size (TermBind s v t) = 1 + list_sum [term_size t].
  reflexivity.
Qed.

(* Shorthand types for size comparison between terms *)
Definition Smaller (s s' t t' : term) : Prop :=
  term_size s + term_size s' < term_size t + term_size t'.

Definition Smaller_bs (cs cs' bs bs': list binding) : Prop :=
  length cs + length cs' < length bs + length bs'.

Definition Smaller_t_bs (t t' : term) (bs bs' : list binding) :=
  term_size t + term_size t' < bindings_size bs + bindings_size bs'.

Definition Smaller_t_b (t t' : term) (b b' : binding) :=
  term_size t + term_size t' < binding_size b + binding_size b'.

Lemma size_non_zero : forall t, term_size t > 0.
  induction t; compute; intuition.
Qed.

(*Prove that structural subterms are smaller in size*)
Lemma let_struct : forall r bs t, term_size t < term_size (Let r bs t).
Proof. intros r bs t. rewrite term_size_let. simpl. intuition. Qed.

Lemma app_struct_l : forall s t, term_size s < term_size (Apply s t).
  compute; intuition.
Qed.

Lemma app_struct_r : forall s t, term_size t < term_size (Apply s t).
Proof. intros s t. rewrite term_size_apply. simpl. lia. Qed.

Lemma tyabs_struct : forall n k t, term_size t < term_size (TyAbs n k t).
Proof. intros n k t. rewrite term_size_tyabs. simpl. intuition. Qed.

Lemma lamabs_struct : forall n ty t, term_size t < term_size (LamAbs n ty t).
Proof. intros n k t. rewrite term_size_lamabs. simpl. intuition. Qed.

Lemma tyinst_struct : forall t ty, term_size t < term_size (TyInst t ty).
Proof. intros t ty. rewrite term_size_tyinst. simpl. intuition. Qed.

Lemma iwrap_struct : forall ty1 ty2 t, term_size t < term_size (IWrap ty1 ty2 t).
Proof. intros ty1 ty2 t. rewrite term_size_iwrap. simpl. intuition. Qed.

Lemma unwrap_struct : forall t, term_size t < term_size (Unwrap t).
Proof. intros t. rewrite term_size_unwrap. simpl. intuition. Qed.

Lemma termbind_struct s v t :  term_size t < binding_size (TermBind s v t).
Proof. rewrite binding_size_TermBind. simpl. intuition. Qed.

Lemma bind_binds_struct b bs : binding_size b < bindings_size (b :: bs).
Proof. unfold bindings_size, Folds.foldBindingsUse, Folds.foldBindings. simpl. intuition. Qed.



Section NonFold.

  Definition size_binding (size : term -> nat) (b : binding) : nat :=
    1 +
    match b with
      | TermBind rec (VarDecl _ _) t => size t
      | DatatypeBind dtd => 0
      | TypeBind _ _ => 0
    end
    .

  Function size (t : term) : nat :=
    1 +
    match t with
     | Let rec bs t    => list_sum (map (size_binding size) bs) + size t
     | LamAbs n ty t   => size t
     | Var n           => 0
     | TyAbs n k t     => size t
     | Apply s t       => size s + size t
     | TyInst t ty     => size t
     | IWrap ty1 ty2 t => size t
     | Unwrap t        => size t
     | Error ty        => 0
     | Constant v      => 0
     | Builtin f       => 0
     | Constr T i ts   => list_sum (map size ts)
     | Case T t ts     => size t + list_sum (map size ts)
   end.

  Lemma size_let_cons rec b bs t :
    size (Let rec (b :: bs) t) =
    size_binding size b + size (Let rec bs t).
  Proof.
    setoid_rewrite size_equation.
    rewrite map_cons.
    rewrite cons_app.
    rewrite list_sum_app.
    simpl.
    lia.
  Qed.

End NonFold.

