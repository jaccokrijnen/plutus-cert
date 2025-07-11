From Coq Require Import
  Strings.String
  Lists.List
.
From PlutusCert Require Import
  PlutusIR.

Import ListNotations.

Definition ctx := list (string * string).


Reserved Notation "Γ ⊢ s '=-α' t" (at level 40).
Inductive alpha_var : ctx -> string -> string -> Prop :=
  | AV_refl x : alpha_var [] x x
  | AV_cons x y xs :
      alpha_var ((x, y) :: xs) x y
  | AV_diff x y z w xs :
      x <> z ->
      y <> w ->
      alpha_var xs z w ->
      alpha_var ((x, y) :: xs) z w
.

Inductive alpha : list (string * string) -> term -> term -> Prop :=
  | A_Var x x' xs :
      alpha_var xs x x' ->
      xs ⊢ Var x =-α Var x'
  | A_LamAbs x x' T t t' Γ :
      ((x, x') :: Γ) ⊢ t =-α t' ->
      Γ ⊢ LamAbs x T t =-α LamAbs x' T t'
  | A_Apply t1 t2 t1' t2' Γ :
      Γ ⊢ t1 =-α t1' ->
      Γ ⊢ t2 =-α t2' ->
      Γ ⊢ Apply t1 t2 =-α Apply t1' t2'

  where "Γ ⊢ s '=-α' t" := (alpha Γ s t)
.

Section Reflexivity.

  Definition ctx_refl (xs : ctx) := Forall (fun '(x, y) => x = y) xs.

  Lemma alpha_refl xs t :
    ctx_refl xs ->
    alpha xs t t.
  Proof.
  Admitted.

End Reflexivity.

Section Symmetry.

  Inductive pair_sym : string * string -> string * string -> Prop :=
    | PS_pair x y : pair_sym (x, y) (y, x)
  .
  Definition ctx_sym (xs ys : ctx) : Prop := Forall2 pair_sym xs ys.

  Lemma alpha_sym xs ys t t':
    ctx_sym xs ys ->
    alpha xs t t' ->
    alpha ys t' t.
  Proof.
  Admitted.

End Symmetry.

