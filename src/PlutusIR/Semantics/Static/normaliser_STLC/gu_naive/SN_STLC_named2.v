From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import List AutosubstSsr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import STLC_named STLC_named_typing ARS.
From PlutusCert Require Import alpha alpha_rename rename util alpha_ctx_sub freshness alpha_freshness alpha_step step alpha_sub.
From PlutusCert Require Import SN_STLC_named_naive.

(* Define an infix operator for bind *)
Infix ">>=" := bind (at level 50, left associativity).

  (** Normal types *)
Inductive normal_Ty : term -> Prop :=
  | NO_TyLam : forall x K T,
      normal_Ty T ->
      normal_Ty (tmlam x K T)
  | NO_neutral : forall T,
      neutral_Ty T ->
      normal_Ty T

with neutral_Ty : term -> Prop :=
  | NE_TyVar : forall X,
      neutral_Ty (tmvar X)
  | NE_TyApp : forall T1 T2,
      neutral_Ty T1 ->
      normal_Ty T2 ->
      neutral_Ty (tmapp T1 T2).

Inductive step_d : term -> term -> Set :=
| step_beta_d (x : string) (A : type) (s t : term) :
    normal_Ty s ->
    normal_Ty t ->
    step_d (tmapp (tmlam x A s) t) (substituteTCA x t s) (* capture avoiding conservative substitutions *)
| step_appL_d s1 s2 t :
    step_d s1 s2 -> step_d (tmapp s1 t) (tmapp s2 t)
| step_appR_d s t1 t2 :
    normal_Ty s ->
    step_d t1 t2 -> step_d (tmapp s t1) (tmapp s t2)
| step_abs_d x A s1 s2 :
    step_d s1 s2 -> step_d (tmlam x A s1) (tmlam x A s2).


Lemma GU_substituteTCA_substituteT A x t s : 
    GU_vars (tmapp (tmlam x A s) t) -> substituteTCA x t s = substituteT x t s.
Proof.
intros.
induction s; simpl.
- admit.
- assert (x =? s = false) by admit. (* GU *)
  rewrite H0.
  autorewrite with substituteTCA.
  rewrite H0.
  assert (existsb (eqb s) (ftv t) = false) by admit. (* GU *)
  rewrite H1.
  f_equal.
  apply IHs.
  inversion H; auto; subst.
  constructor.
  + inversion H4.
    constructor. subst.
    inversion H6. auto. (* notin btv extends to lambdabody *) admit.
  + assumption.
  + intros.
    specialize (H_btv_btv_empty x0 H2). admit.
  + intros.
    (* x0 in btv (tmlam x A s0), so also in btv (tmlam x A (tmlam s t0 s0))*)
    admit.
  + intros.
     (* we can use H_ftv_btv_empty, and deduce that s is not equal to any of the btv of t.*)
Admitted.

(* If t has globally unique binders (and free variables to make it easier)
    then deterministic step and naive step coincide*)
Lemma GU_step_d_implies_step_na t t' : 
    GU_vars t -> step_d t t' -> step_naive t t'.
Proof.
    intros HGU_vars H.
    induction H.
    - (* we can be sure that no binder in s appears in t by global uniqueness*)
     assert (substituteTCA x t s = substituteT x t s) as Hsub.
     { 
        eapply GU_substituteTCA_substituteT.
        eauto.
      }
     rewrite Hsub.
     apply step_beta.
    - apply step_appL. auto. inversion HGU_vars; auto.
    - apply step_appR. auto. inversion HGU_vars; auto.
    - apply step_abs. auto. inversion HGU_vars; auto.
Qed.

Lemma alpha_capms_to_naive X U T:
  {T' & Alpha [] T T' * Alpha [] (substituteTCA X U T) (substituteT X U T')}.
Proof.
exists (to_unique_binders T).
  split; try apply to_unique_binders_alpha.
  induction T.
  - admit.
  - 
Admitted.

Lemma alpha_rename_binder_substituteT {y : string } {s : term} s' x t t' ren:
  Alpha ((x, y)::ren) s s' ->
  Alpha ren t t' ->
  Alpha ren (substituteT x t s) (substituteT y t' s').
Proof.
(* My assumption is that this is easier than for substituteTCA*)
Admitted.

Lemma alpha_preserves_normal_Ty s s' R :
  R ⊢ s ~ s' -> normal_Ty s -> normal_Ty s'.
Proof.
(* a normal_Ty cannot step.
Suppose s' steps. Then by alpha_preserves_step we have that there is a corresponding step for s. Contradiction.
*)
Admitted.

(* Main lemma for going from using t alpha t' in SN t' to SN t*)
Lemma step_d_preserves_alpha ren s t s' :
  Alpha ren s t -> step_d s s' -> {t' & (step_d t t') * (Alpha ren s' t')}%type.
Proof.
(* exists s'' s.t. step_gu_naive s s'' and s' ~ s''

  We know s ~ t.

  Supposinng we have step_gu_naive preserves alpha:
  exists t'' s.t. step_gu_naive t t''   and s'' ~ t''

  I think we then also have
  exists t''' step_d t t'''. And since we also have s' ~ t'', the t' we are looking for is t''
  
  *)
  intros Halpha Hstep.
  generalize dependent t.
  generalize dependent ren.
  induction Hstep; intros ren t0 Halpha; inversion Halpha; subst.
  - inversion H2; subst.
    remember (alpha_capms_to_naive x t s).
    destruct s1 as [s' [Halpha1 Halpha2] ].
    eexists.
    split.
    + apply step_beta_d; eapply alpha_preserves_normal_Ty; eauto.
    + eapply @alpha_trans with (t := substituteT x t s').
      * apply id_left_trans.
      * change (ctx_id_left ren) with (nil ++ ctx_id_left ren).
        apply alpha_extend_ids_right.
        -- apply ctx_id_left_is_id.
        -- auto.
      * remember (alpha_capms_to_naive y t2 s0).
        destruct s1 as [t' [Halpha1' Halpha2'] ].
      
        eapply @alpha_trans with (t := substituteT y t2 t').
        -- apply id_right_trans.
        -- eapply alpha_rename_binder_substituteT.
           ++ admit.
           ++ exact H4.
        -- change (ctx_id_right ren) with (nil ++ ctx_id_right ren).
           apply alpha_extend_ids_right.
           ++ apply ctx_id_right_is_id.
           ++ eapply alpha_sym. constructor. eauto.
  - destruct (IHHstep ren s3 H2) as [t1_α [Hstep' Halpha'] ].
    exists (tmapp t1_α t2); split.
    + apply step_appL_d. assumption.
    + apply alpha_app; assumption.
  - destruct (IHHstep ren t4 H4) as [tα [Hstep' Halpha'] ].
    exists (tmapp s2 tα); split.
    + apply step_appR_d.
      * eapply alpha_preserves_normal_Ty; eauto.
      * assumption.
    + apply alpha_app; assumption.
  - destruct (IHHstep ((x, y)::ren) s3 H4) as [tα [Hstep' Halpha'] ].
    exists (tmlam y A tα); split.
    + apply step_abs_d. assumption.
    + apply alpha_lam; assumption.    
Admitted.

Lemma step_d_implies_step_gu_na t t' : 
    step_d t t' ->  
    {t_α & step_gu_naive t t_α * (nil ⊢ t' ~ t_α)}.
Proof.
    remember (to_unique_binders t) as t_GU.
    assert (nil ⊢ t ~ t_GU) as H_alpha.
    {
      subst.
      apply to_unique_binders_alpha.
    }
    assert (GU_vars t_GU) as H_GU.
    {
      subst.
      apply to_unique_binders_unique.
    }
    intros.
    remember (step_d_preserves_alpha H_alpha H) as Hstep_GU.
    destruct Hstep_GU as [t_GU' [Hstep_GU Halpha_GU] ].
    exists t_GU'.
    split.
    - clear HeqHstep_GU.
        apply GU_step_d_implies_step_na in Hstep_GU.
        + subst. constructor. auto.
        + auto.
    - auto. 
Qed.

Theorem α_preserves_sn_d s s' :
  Alpha [] s s' -> (@sn step_d) s -> (@sn step_d) s'.
Proof.
  intros Hα Hsn.
  generalize dependent s'.
  induction Hsn. intros s' Hα.
  apply SNI.
  intros y1 Hstep.
  assert ({y1_α & prod (step_d x y1_α) (nil ⊢ y1 ~ y1_α)}) as [y1_α [Hstep' Hα'] ].
  {
    eapply step_d_preserves_alpha; auto.
    - eapply alpha_sym in Hα. exact Hα. apply alpha_sym_nil.
    - assumption.
  }
  eapply H.
  - exact Hstep'.
  - eapply alpha_sym. apply alpha_sym_nil. exact Hα'.
Qed.

Lemma SN_na_to_SN_d t : (@sn step_gu_naive) t -> (@sn step_d) t.
Proof.
  intros Hsn_nd.
  apply SNI.
  intros t' Hstep.
  generalize dependent t'.
  induction Hsn_nd; intros t Hstep_d.
  assert (Hstep_alpha: {t' & prod (step_gu_naive x t') (Alpha nil t t')}).
  {
    eapply step_d_implies_step_gu_na; eauto.
  }
  destruct Hstep_alpha as [t' [Hstep Halpha] ].
  specialize (H t' Hstep).
  apply α_preserves_sn_d with t'.
  - eapply alpha_sym; [apply alpha_sym_nil |].
    assumption.
  - apply SNI. 
    exact H.
Qed.