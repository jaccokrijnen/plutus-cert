From Coq Require Import
  Strings.String
  Lists.List
.
From PlutusCert Require Import
  PlutusIR.

Import ListNotations.

Definition ctx := list (string * string).

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
      alpha xs (Var x) (Var x')
  | A_LamAbs x x' T t t' sigma :
      alpha ((x, x') :: sigma) t t' ->
      alpha sigma (LamAbs x T t) (LamAbs x' T t')
  | A_Apply t1 t2 t1' t2' sigma :
      alpha sigma t1 t1' ->
      alpha sigma t2 t2' ->
      alpha sigma (Apply t1 t2) (Apply t1' t2')
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

From PlutusCert Require Import
  Dynamic.Bigstep.

Require Import Coq.Program.Equality.

Section Substitution.


  Context
    (x x' : string)
    (s s' : term)
    (H_s : alpha [] s s')
  .

  Lemma alpha__subst : forall t t',
    alpha [(x, x')] t t' ->
    alpha [] (subst x s t) (subst x' s' t')
  .
  Proof.
    intros t.
    apply term__ind with
      (P := fun t => forall t', alpha [(x, x')] t t' -> alpha [] (subst x s t) (subst x' s' t'))
      (Q := fun b => True).

    (* Solve unimplemented cases *)
    all: try solve [intros; match goal with H : alpha _ _ _ |- _ => inversion H end].

    - (* Var *)
      intros y t' H_t.
      inversion H_t. subst x0 t'.
      rename x'0 into y'.
      autorewrite with subst.
      destruct ((x =? y)%string) eqn:H_eq; destruct ((x' =? y')%string) eqn:H_eq'; simpl.
      * assumption.
      * rewrite eqb_eq, eqb_neq in *.
        inversion H1; contradiction.
      * rewrite eqb_eq, eqb_neq in *.
        inversion H1; contradiction.
      * rewrite eqb_neq in *.
        inversion H1. subst.
        ** contradiction.
        ** subst.
           inversion H8. subst.
           auto using alpha.

    - (* LamAbs *)
      intros y T u IH_u t' H_t.
      inversion H_t;
      subst x0 T0 t0 t' sigma;
      rename x'0 into y';
      rename t'0 into u'.
      setoid_rewrite subst_unfold.
      destruct ((x =? y)%string) eqn:H_eq;
      destruct ((x' =? y')%string) eqn:H_eq'.
      (* TODO: strengthen IH with environment (xs ++ [(x, x')], such that x and
      x' do not occur in xs *)
  Admitted.

End Substitution.

Lemma alpha__fully_applied t t' :
  alpha [] t t' ->
  fully_applied t ->
  fully_applied t'
.
Proof.
Admitted.

Lemma alpha__compute_defaultfun {t t' v} :
  alpha [] t t' ->
  compute_defaultfun t = Some v -> exists v',
  compute_defaultfun t' = Some v' /\ alpha [] v v'
.
Admitted.

Lemma alpha__applied_args t t' : alpha [] t t' -> applied_args t = applied_args t'.
Admitted.

Lemma alpha__value v v' :
  alpha [] v v' ->
  value v ->
  value v'
.
Admitted.

Lemma alpha__is_error t t' :
  alpha [] t t' ->
  is_error t ->
  is_error t'
.
Proof.
  intros.
  inversion H0; subst.
  inversion H.
Qed.

Lemma alpha__eval t t' r i:
  alpha [] t t' ->
  t  =[i]=> r -> exists r',
  t' =[i]=> r' /\ alpha [] r r'.
Proof.
  intros H_alpha H_eval.
  revert H_alpha.
  revert t'.
  dependent induction H_eval; intros t' H_alpha; try solve [inversion H_alpha].
  - (* E_LamAbs *)
    exists t'.
    inversion H_alpha; subst.
    split.
    + apply E_LamAbs.
    + assumption.
  - (* E_Apply *)
    rename t0 into t.
    rename v0 into r.
    rename v2 into r2.
    inversion H_alpha as [ | | ? ? ? ? ? H_alpha_t1 H_alpha_t2 ]; subst.

    (* Use IH1*)
    specialize (IHH_eval1 _ H_alpha_t1) as [r1' [H_t1'_eval H_t1'_alpha]].
    inversion H_t1'_alpha; subst.
    (* Use IH2 *)
    specialize (IHH_eval2 _ H_alpha_t2) as [r2' [H_t2'_eval H_t2'_alpha]].

    (* Use IH3 *)
    specialize (IHH_eval3 (subst x' r2' t')).

    assert (H_subst : alpha [] (subst x r2 t) (subst x' r2' t')). {
      apply alpha__subst; assumption.
    }

    specialize (IHH_eval3 H_subst) as [r' [H_eval_subst H_alpha_r]].

    exists r'.
    split.
    + eapply E_Apply.
      * intro.
        apply H.
        apply alpha_sym with (ys := []) in H_alpha; try constructor.
        eauto using alpha__fully_applied.
      * exact H_t1'_eval.
      * exact H_t2'_eval.
      * intro.
        apply H0.
        apply alpha_sym with (ys := []) in H_t2'_alpha; try constructor.
        eauto using alpha__is_error.
      * assumption.
    + assumption.
  - (* E_Builtin_Apply_Eta *)
    inversion H_alpha; subst.
    (* Prove that partially_applied respects alpha. *)
    admit.
  - (* E_Builtin_Apply *)
    inversion H_alpha; subst.
    specialize (alpha__compute_defaultfun H_alpha H0) as [ r' [H_compute H_alpha_r]].
    exists r'.
    split.
    + eauto using alpha__fully_applied, eval.
    + eauto.
  - (* E_Error_Apply1 *)
    inversion H_alpha; subst.
    specialize (IHH_eval t1' H2) as [r' [H_eval_t' H_alpha_r']].
    inversion H_alpha_r'.
  - (* E_Error_Apply2 *)
    inversion H_alpha; subst.
    specialize (IHH_eval t2' H4) as [r' [H_eval_t' H_alpha_r']].
    inversion H_alpha_r'.
Admitted.
