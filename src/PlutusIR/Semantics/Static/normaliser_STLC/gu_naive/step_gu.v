From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List AutosubstSsr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import alpha_typing STLC_named STLC_named_typing ARS gu_naive.pre gu_naive.constructions.
From PlutusCert Require Import alpha.alpha alpha_rename rename util alpha_ctx_sub freshness alpha_freshness.



(* Examples
λ x. x is GU_vars
λ x. y is GU_vars
λ x. λ y. x is GU_vars

(λ x. x) y is GU_vars
(λ x. x) x is not GU_vars (* free var is equal to a bound var*)
(λ y. x) x is GU_vars (* all vars with the same name refer to the same term*)
*)

(* If a term has globally unique binders, then it has unique binders*)

Inductive step_gu : term -> term -> Type :=
| step_gu_intro s s' t : 
    Alpha [] s s' ->
    GU s' ->
    step_naive s' t ->
    step_gu s t.
(*     
    Alpha [] t' t ->
    GU_vars t ->
    step_gu s t. *)

(** **** Many-Step Reduction 
TODO: See if we can use the star from autosubst ARS again. (uses Prop instead of Set)
*)
Inductive red_gu_na : term -> term -> Type :=
| red_gu_na_star s t t':
     step_gu s t -> 
     red_gu_na t t' ->
     red_gu_na s t' 
| red_gu_na_nil s :
     red_gu_na s s.


Lemma step_naive_preserves_alpha2 s t s' R:
  GU s -> GU s' -> Alpha R s s' -> step_naive s t -> {t' & step_naive s' t' * Alpha R t t'}%type.
Proof.
  intros.
  generalize dependent R.
  generalize dependent s'.
  induction H2; subst; intros.
  - inversion H1; subst. inversion H7; subst.
    
    exists (sub y t2 s0).
    split.
    + constructor.
    + eapply alpha_rename_binder_stronger; eauto with gu_nc_db.
      constructor.
  - inversion H1; subst.
    specialize (IHstep_naive (gu_app_l H) s3 (gu_app_l H0) R H8) as [t' [Hstep_t' HR_t'] ].
    exists (@tmapp B t' t2).
    split; constructor; auto.
  - inversion H1; subst.
    specialize (IHstep_naive (gu_app_r H) t3 (gu_app_r H0) R H9) as [t' [Hstep_t' HR_t'] ].
    exists (@tmapp B s2 t').
    split; constructor; auto.
  - inv H1.
    specialize (IHstep_naive (gu_lam H) s3 (gu_lam H0) ((x, y)::R) H9) as [t' [Hstep_t' HR_t'] ].
    exists (@tmlam B y A t').
    split; constructor; auto.
Qed.

(* We need alpha here because global unique can create different terms depending on input:
  global unique does not compose
  suppose there is a free var in s2, then that must be renamed when doing step_gu (tmapp s1 s2)
  while that is not the case in step_gu s1 t1 (there s2 does not need to be taken into account)
  *)
Lemma step_gu_app_l {B} s1 s2 t1 :
  step_gu s1 t1 -> 
  {t1' & Alpha [] t1 t1' * {s2' & Alpha [] s2 s2' * step_gu (@tmapp B s1 s2) (@tmapp B t1' s2')}%type }%type.
Proof.
  intros.

  (* We cannot directly invert the (step_gu s1 t1), because we need something to be GU over s2 as well!*)
  remember (to_GU (@tmapp B s1 s2)) as app.
  remember Heqapp as Heqapp'. clear HeqHeqapp'.
  apply to_GU_app_unfold in Heqapp.
  destruct Heqapp as [s1' [s2' [ [Happ Ha_s1] Ha_s2] ] ].

  inv H.

  (* From step_naive s' t1, it then also follows that there must exist a t1' s.t. step_naive s1' t1'.*)
  apply step_naive_preserves_alpha2 with (s' := s1') (R := nil) in H2 as [t1' [Hstep_s1' Ha_t1] ].
  - exists t1'.
    split; auto.
    exists s2'.
    split; auto.
    apply step_gu_intro with (s' := (@tmapp B s1' s2')); auto.
    + rewrite Heqapp'. apply to_GU__alpha.
    + rewrite Heqapp'. apply to_GU__GU.
    + constructor. auto.
  - assumption.
  - eapply gu_app_l. erewrite Heqapp'. apply to_GU__GU.
  - eauto with α_eq_db.
Qed.

Lemma step_gu_na_lam_fold {B} x A s s' :
  step_gu s s' -> {lams' & step_gu (@tmlam B x A s) lams' * Alpha [] lams' (@tmlam B x A s')}%type.
Proof.
  intros.
  assert (Alpha [] (@tmlam B x A s) (to_GU (@tmlam B x A s)) ).
  {
    apply to_GU__alpha.
  }
  inversion H; subst.
  rename s'0 into sgu.
  inversion H0; subst.
  assert (Alpha [(x, y)] sgu s2).
  {
    eapply @alpha_trans with (t := s) (ren := ((x, x)::nil)) (ren' := ((x, y)::nil)).
    - constructor. constructor.
    - apply alpha_extend_ids. constructor. constructor. eauto with α_eq_db.
    - rewrite <- H10 in H0. inversion H0; subst. eauto.
  } 
  (* sgu and slam are both GU, so we can do step preserves 2*)
  assert ({t' & step_naive s2 t' * Alpha [(x, y)] s' t'}%type).
  {
    eapply step_naive_preserves_alpha2.
    - exact H2.
    - assert (GU (to_GU (@tmlam B x A s))) by apply to_GU__GU.
      rewrite <- H10 in H5. auto.
      eapply gu_lam. eauto.
    - eauto.
    - auto.
  }
  destruct H5 as [t' [Hstep_t' Halpha_t'] ].
  exists (@tmlam B y A t').
  split.
  - eapply step_gu_intro with (s' := tmlam y A s2); eauto.
    + rewrite <- H10 in H0. eauto.
    + assert (GU (to_GU (@tmlam B x A s))) by apply to_GU__GU.
      rewrite <- H10 in H5. auto.
    + apply step_abs. auto.
  - eapply @alpha_sym. constructor. constructor. eauto.
Qed.


Lemma step_gu_preserves_alpha {s} {s'} {t} R :
  Alpha R s t -> step_gu s s' -> {t' & prod (step_gu t t') (Alpha R s' t')}.
Proof.
  intros.
  inversion H0; subst.
  assert ({t' & step_naive (to_GU t) t' * Alpha R s' t'}%type).
  {
    eapply step_naive_preserves_alpha2; eauto.
    + apply to_GU__GU.
    + eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R); eauto with α_eq_db.
      * eapply id_left_trans.
      * eapply alpha_extend_ids.
        eapply ctx_id_left_is_id.
        eapply @alpha_sym. constructor. exact H1.
      * eapply @alpha_trans with (ren := R) (ren' := ctx_id_right R).
        -- eapply id_right_trans.
        -- eauto.
        -- eapply alpha_extend_ids.
           eapply ctx_id_right_is_id.
           eapply to_GU__alpha.
  }
  destruct H4 as [t' [Hstep_t' HR_t'] ].
  exists t'.
  split.
  - apply step_gu_intro with (s' := (to_GU t)); eauto.
    + apply to_GU__alpha.
    + apply to_GU__GU.
  - auto.
Qed.



Lemma red_gu_naive_preserves_alpha {s} {s'} {t} R :
  Alpha R s t -> red_gu_na s s' -> {t' & prod (red_gu_na t t') (Alpha R s' t')}.
Proof.
  intros.
  generalize dependent R.
  generalize dependent t.  
  induction H0; intros.
  - apply (step_gu_preserves_alpha H) in s0.
    destruct s0 as [t'0 [Hstept'0 Ha_t'0] ].
    specialize (IHred_gu_na t'0 R Ha_t'0).
    destruct IHred_gu_na as [t'1 [Hred_t'1 Ha_t'1] ].
    exists t'1.
    split; auto.
    apply red_gu_na_star with (t := t'0); auto.
  - exists t.
    split; auto.
    constructor.
Qed.

(* step_gu/red_gu always freshens binders, hence we need to work up to alpha*)
Lemma red_gu_na_lam_fold {B x A s s'} :
  red_gu_na s s' -> {lams' & red_gu_na (@tmlam B x A s) lams' * Alpha [] lams' (@tmlam B x A s')}%type.
Proof.
  intros.
  induction H.
  - destruct IHred_gu_na as [lams' [Hred Halpha] ].

    apply (@step_gu_na_lam_fold B x A) in s0.
    destruct s0 as [lams'' [Hstep'' Halpha''] ].
    assert ({lams''' & red_gu_na lams'' lams''' * Alpha [] lams' lams'''}%type).
    {
      apply @red_gu_naive_preserves_alpha with (t := lams'') (s := @tmlam B x A t); eauto with α_eq_db.
    }
    destruct H0 as [lams''' [Hred' Halpha'] ].
    exists lams'''.
    split.
    + eapply red_gu_na_star.
      * exact Hstep''.
      * eauto.
    + eauto with α_eq_db.
  - exists (@tmlam B x A s).
    split.
    + apply red_gu_na_nil.
    + apply alpha_refl. constructor.
Qed.

Lemma step_gu_na_appl_fold {B s1 s2 t1 }:
  step_gu s1 s2 -> {app & step_gu (@tmapp B s1 t1) app * Alpha [] app (@tmapp B s2 t1)}%type.
Proof.
  intros Hstep_gu.
  inversion Hstep_gu; subst.
  assert (Hgu_a: nil ⊢ (@tmapp B s1 t1) ~ (to_GU (@tmapp B s1 t1))) by apply to_GU__alpha.
  inversion Hgu_a; subst.

  assert (Hstep_na': {s2' & step_naive s3 s2' * Alpha [] s2 s2'}%type).
  {
    eapply step_naive_preserves_alpha2; eauto.
    - assert (Hgu_app: GU (to_GU (@tmapp B s1 t1))) by apply to_GU__GU.
      rewrite <- H7 in Hgu_app.
      eapply gu_app_l. eauto.
    - assert (Alpha [] s1 (to_GU s1)) by apply to_GU__alpha.
      eauto with α_eq_db.
  }
  destruct Hstep_na' as [s2' [Hstep_s2' Ha_s2'] ].
  exists (@tmapp B s2' t2).
  split.
  - eapply step_gu_intro with (s' := @tmapp B s3 t2).
    + rewrite H7. auto.
    + rewrite H7. apply to_GU__GU.
    + apply step_appL. auto.
  - constructor; eauto with α_eq_db.
Qed.

Lemma step_gu_na_appr_fold {B s1 t1 t2 } : 
  step_gu t1 t2 -> {app & step_gu (@tmapp B s1 t1) app * Alpha [] app (@tmapp B s1 t2)}%type.
Proof.
  intros Hstep_gu.
  inversion Hstep_gu; subst.
  assert (Hgu_a: nil ⊢ (@tmapp B s1 t1) ~ (to_GU (@tmapp B s1 t1))) by apply to_GU__alpha.
  inversion Hgu_a; subst.

  assert (Hstep_na': {t2' & step_naive t3 t2' * Alpha [] t2 t2'}%type).
  {
    eapply step_naive_preserves_alpha2; eauto.
    - assert (Hgu_app: GU (to_GU (@tmapp B s1 t1))) by apply to_GU__GU.
      rewrite <- H7 in Hgu_app.
      eapply gu_app_r. eauto.
    - assert (Alpha [] t1 (to_GU t1)) by apply to_GU__alpha.
      eauto with α_eq_db.
  }
  destruct Hstep_na' as [t2' [Hstep_t2' Ha_t2'] ].
  exists (@tmapp B s2 t2').
  split.
  - eapply step_gu_intro with (s' := @tmapp B s2 t3).
    + rewrite H7. auto.
    + rewrite H7. apply to_GU__GU.
    + apply step_appR. auto.
  - constructor; eauto with α_eq_db.
Qed.

Lemma red_gu_na_trans s t u :
  red_gu_na s t -> red_gu_na t u -> red_gu_na s u.
Proof.
  intros.
  generalize dependent u.
  induction H; intros.
  - generalize dependent s.
    generalize dependent t.
    induction H0; intros.
    + eapply IHred_gu_na with (t := t0).
      * eapply IHred_gu_na0.
        eapply red_gu_na_star; eauto. constructor.
      * intros.
        eapply IHred_gu_na0.
        eapply red_gu_na_star; eauto.
      * auto.
    + eapply red_gu_na_star; eauto.
  - induction H0.
    + eapply red_gu_na_star; eauto.
    + constructor.
Qed.

Lemma red_gu_na_appl_fold {B s1 s2 t} :
  red_gu_na s1 s2 -> {app & red_gu_na (@tmapp B s1 t) app * Alpha [] app (@tmapp B s2 t)}%type.
Proof.
  intros H0.
  induction H0.
    + destruct IHred_gu_na as [app [Hred Halpha] ].
      eapply (@step_gu_na_appl_fold) with (s1 := s) (t1 := t) in s0.
      destruct s0 as [app' [Hred' Halpha'] ].
      assert ({app'' & red_gu_na app' app'' * Alpha [] app app''}%type).
      {
        eapply @red_gu_naive_preserves_alpha with (s := tmapp t0 t); eauto with α_eq_db.
      }
      destruct H as [app'' [Hred'' Halpha'' ] ].
      exists app''.
      split.
      * eapply red_gu_na_star.
        -- exact Hred'.
        -- eauto.
      * eauto with α_eq_db.
    + exists (@tmapp B s t).
      split.
      * apply red_gu_na_nil.
      * apply alpha_refl. constructor. 
Qed.

Lemma red_gu_na_appr_fold {B s1 t1 t2} :
  red_gu_na t1 t2 -> {app & red_gu_na (@tmapp B s1 t1) app * Alpha [] app (@tmapp B s1 t2)}%type.
Proof.
  intros H0.
  induction H0.
    + destruct IHred_gu_na as [app [Hred Halpha] ].
      eapply (@step_gu_na_appr_fold) with (s1 := s1) (t1 := s) (t2 := t) in s0.
      destruct s0 as [app' [Hred' Halpha'] ].
      assert ({app'' & red_gu_na app' app'' * Alpha [] app app''}%type).
      {
        eapply @red_gu_naive_preserves_alpha with (s := tmapp s1 t); eauto with α_eq_db.
      }
      destruct H as [app'' [Hred'' Halpha'' ] ].
      exists app''.
      split.
      * eapply red_gu_na_star.
        -- exact Hred'.
        -- eauto.
      * eauto with α_eq_db.
    + exists (@tmapp B s1 s).
      split.
      * apply red_gu_na_nil.
      * apply alpha_refl. constructor.
Qed.

Lemma red_gu_na_app_fold {B s1 s2 t1 t2} :
  red_gu_na s1 s2 -> red_gu_na t1 t2 -> {app & red_gu_na (@tmapp B s1 t1) app * Alpha [] app (@tmapp B s2 t2)}%type.
Proof.
  intros.
  eapply @red_gu_na_appl_fold with (t := t1) in H.
  destruct H as [app [Hred Halpha] ].

  eapply @red_gu_na_appr_fold with (s1 := s2) in H0.
  destruct H0 as [app' [Hred' Halpha'] ].

  assert ({app'' & red_gu_na app app'' * Alpha [] app' app''}%type).
  {
    eapply @red_gu_naive_preserves_alpha with (s := tmapp s2 t1); eauto with α_eq_db.
  }
  destruct H as [app'' [Hred'' Halpha'' ] ].
  exists app''.
  split.
  - eapply red_gu_na_trans; eauto.
  - eauto with α_eq_db.
Qed.
