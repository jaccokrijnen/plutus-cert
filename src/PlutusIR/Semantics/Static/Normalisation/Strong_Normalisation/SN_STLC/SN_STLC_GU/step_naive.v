Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
From PlutusCert Require Import STLC util variables Util
  Util.List psubs.

Local Open Scope string_scope.

Fixpoint sub (X : string) (U T : term) : term :=
  match T with
  | tmvar Y =>
    if X =? Y then U else tmvar Y
  | @tmlam B Y K1 T' =>
    @tmlam B Y K1 (sub X U T') (* X can never be equal to Y due to GU: We only ever do substitutions such that NC T [(X, U)]*)
  | @tmapp B T1 T2 =>
    @tmapp B (sub X U T1) (sub X U T2)
  | tmbuiltin d => tmbuiltin d
  end.


Lemma single_subs_is_psub X T s :
  psubs [(X, T)] s = sub X T s.
Proof.
  induction s.
  - simpl. destr_eqb_eq X s. reflexivity.
    reflexivity.
  - simpl. f_equal. apply IHs.
  - simpl. f_equal. apply IHs1. apply IHs2.
  - simpl. reflexivity.
Qed.

Lemma sub_helper {x t s} :
  ~ In x (ftv t) -> ~ In x (ftv (sub x t s)).
Proof.
  intros Hcontra.
  induction s.
  - destr_eqb_eq x s.
    + simpl. destr_eqb_eq s s. auto. contradiction.
    + simpl. destr_eqb_eq x s. auto.
      intros Hcontra2.
      apply ftv_var in Hcontra2. contradiction.
  - simpl. (* remove_string_dec s (ftv (sub x t s0)) is a subset of ftv (sub x t s0)*)
    intros Hcontra2.
    apply in_remove in Hcontra2.
    destruct Hcontra2 as [Hcontra2 _].
    contradiction.
  - simpl. apply not_in_app. split.
    + apply IHs1.
    + apply IHs2.
  - simpl. auto.
Qed.

(* need also handle btv, since substitution is nto capture avoiding*)
Lemma sub_vac x t s :
 ~ In x (ftv s) ->
 ~ In x (btv s) ->
 sub x t s = s.
Proof.
  intros.
  induction s; simpl; auto.
  - destr_eqb_eq x s; auto.
    unfold ftv in H. contradiction H. apply in_eq.
  - f_equal.
    assert (~ In x (ftv s0)).
    {
      simpl in H0.
      apply ftv_lam_negative in H; auto.
    }
    specialize (IHs H1 (not_btv_dc_lam H0)). auto.
  - f_equal.
    + eapply IHs1; eauto.
      eapply not_ftv_app_not_left; eauto. eapply not_btv_dc_appl. eauto.
    + eapply IHs2; eauto.
      eapply not_ftv_app_not_right; eauto. eapply not_btv_dc_appr. eauto.
Qed.
(* looks like sub_vacuous maybe?*)

Inductive step_naive : term -> term -> Set :=
| step_beta (x : string) (A : PlutusIR.kind) (s t : term) :
    step_naive (@tmapp App (@tmlam Lam x A s) t) ( sub x t s)
| step_appL B s1 s2 t :
    step_naive s1 s2 -> step_naive (@tmapp B s1 t) (@tmapp B s2 t)
| step_appR B s t1 t2 :
    step_naive t1 t2 -> step_naive (@tmapp B s t1) (@tmapp B s t2)
| step_abs B x A s1 s2 :
    step_naive s1 s2 -> step_naive (@tmlam B x A s1) (@tmlam B x A s2).


Lemma step_naive_preserves_no_ftv x t1 t2 :
  step_naive t1 t2 -> ~ In x (ftv t1) -> ~ In x (ftv t2).
Proof.
  intros Hstep Hftv_t1.
  induction Hstep.
  - destr_eqb_eq x x0.
    + apply sub_helper. apply not_ftv_app_not_right in Hftv_t1. auto.
    + rewrite <- single_subs_is_psub.
      apply psubs_does_not_create_ftv.
      * apply not_ftv_app_not_left in Hftv_t1. auto. eapply ftv_lam_negative; eauto.
      * unfold ftv_keys_env. simpl. apply not_in_cons. split.
        -- auto.
        -- apply not_ftv_app_not_right in Hftv_t1. rewrite app_nil_r. auto.
  - specialize (IHHstep (not_ftv_app_not_left Hftv_t1)).
    intros Hcontra.
    simpl in Hcontra.
    apply in_app_or in Hcontra.
    destruct Hcontra.
    + apply IHHstep in H.
      contradiction.
    + apply not_ftv_app_not_right in Hftv_t1.
      contradiction.
  - specialize (IHHstep (not_ftv_app_not_right Hftv_t1)).
    intros Hcontra.
    simpl in Hcontra.
    apply in_app_or in Hcontra.
    destruct Hcontra.
    + apply not_ftv_app_not_left in Hftv_t1.
      contradiction.
    + apply IHHstep in H.
      contradiction.
  - destr_eqb_eq x0 x.
    + apply ftv_lam_no_binder.
    + intros Hcontra.
      apply ftv_lam_helper in Hcontra.
      apply ftv_lam_negative in Hftv_t1.
      specialize (IHHstep Hftv_t1).
      contradiction. auto.   
Qed.

