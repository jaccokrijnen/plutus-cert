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
From PlutusCert Require Import SN_STLC_named_naive pre constructions.

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

(* induction principle for mutual induction*)
Scheme normal_Ty_mut := Induction for normal_Ty Sort Prop
with neutral_Ty_mut := Induction for neutral_Ty Sort Prop.

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

Lemma in_ftv_existsb_true t s :
  In s (ftv t) -> existsb (eqb s) (ftv t) = true.
Proof.
  intros Hin.
  apply existsb_exists.
  exists s.
  split; auto.
  apply eqb_eq. auto.
Qed.

Lemma not_in_ftv_existsb_false t s :
  ~ In s (ftv t) <-> existsb (eqb s) (ftv t) = false.
Proof.
  split.
  - intros H.
    apply Bool.not_true_iff_false.
    intros He. apply existsb_exists in He.
    destruct He as [x [Hin Heqb] ].
    apply eqb_eq in Heqb. subst.
    contradiction.
  - intros H.
    intros Hcontra. apply in_ftv_existsb_true in Hcontra.
    rewrite H in Hcontra. discriminate.
Qed.


(* We need to change this to: GU s and no binder in s is free in t. Isnt that simply NC?*)
Lemma GU_substituteTCA_sub x t s : 
    NC s ((x, t)::nil) -> substituteTCA x t s = sub x t s.
Proof.
intros.
induction s; simpl.
- destr_eqb_eq x s.
  + autorewrite with substituteTCA. rewrite String.eqb_refl. reflexivity.
  + autorewrite with substituteTCA. rewrite <- String.eqb_neq in H0. rewrite H0. reflexivity.
- assert (x =? s = false).
  {
    apply nc_ftv_env with (x := s) in H. 
    - unfold ftv_keys_env in H. apply not_in_cons in H.  destruct H as [H _]. rewrite <- String.eqb_sym. 
      rewrite <- String.eqb_neq in H. assumption.
    - apply btv_lam.
  }
  autorewrite with substituteTCA.
  rewrite H0.
  assert (existsb (eqb s) (ftv t) = false).
  {
    apply nc_ftv_env with (x := s) in H. 
    - unfold ftv_keys_env in H. apply not_in_cons in H.  destruct H as [_ H]. apply not_in_app in H as [H _].
      apply not_in_ftv_existsb_false. assumption.
    - apply btv_lam.
  } 
  rewrite H1.
  f_equal.
  apply IHs.
  eapply nc_lam. eauto.
- autorewrite with substituteTCA. f_equal.
  + eapply IHs1; eapply nc_app_l. eauto.
  + eapply IHs2; eapply nc_app_r. eauto.
Qed.

(* If t has globally unique binders (and free variables to make it easier)
    then deterministic step and naive step coincide*)
Lemma GU_step_d_implies_step_na t t' : 
    GU t -> step_d t t' -> step_naive t t'.
Proof.
    intros HGU_vars H.
    induction H.
    - (* we can be sure that no binder in s appears in t by global uniqueness*)
      assert (substituteTCA x t s = sub x t s) as Hsub.
      { 
          eapply GU_substituteTCA_sub.
          eapply gu_applam_to_nc. eauto.
        }
      rewrite Hsub.
      apply step_beta.
    - apply step_appL. auto. inversion HGU_vars; auto.
    - apply step_appR. auto. inversion HGU_vars; auto.
    - apply step_abs. auto. inversion HGU_vars; auto.
Qed.

Lemma substituteTCA_vacuous X T s s' R : Alpha R s s' -> ~ In X (ftv s) -> Alpha R (substituteTCA X T s) s'.
Proof.
  intros Ha_s H.
  generalize dependent s.
  generalize dependent R.
  induction s'; intros; simpl; 
      inversion Ha_s; subst; 
      autorewrite with substituteTCA.
  - apply not_in_ftv_var in H. 
    rewrite <- String.eqb_neq in H.
    rewrite H. constructor. auto.
  - destr_eqb_eq X x; auto.
    destruct (existsb (eqb x) (ftv T)).
    + apply ftv_lam_negative in H; auto.
      remember (fresh2 [(x, tmvar x); (X, T)] s1) as Y'; simpl.
      constructor.
      apply IHs'; eauto.
      * eapply alpha_trans_rename_left; eauto.
      * apply ftv_not_in_rename; auto.
        symmetry. 
        eapply fresh2_over_key_sigma; intuition.
    + constructor.
      eapply IHs'; auto.
      eapply ftv_lam_negative; eauto.
  - constructor.
    + eapply IHs'1; eauto. eapply not_ftv_app_not_left; eauto.
    + eapply IHs'2; eauto. eapply not_ftv_app_not_right; eauto.
Qed.

Lemma subs_preserves_alpha' X T i : forall s s' R1 R2 R,
  R ⊢ (tmvar X) ~ (tmvar X) ->
  R ⊢ T ~ T ->
  αCtxTrans R1 R2 R ->
  R1 ⊢ s ~ i ->
  R2 ⊢ i ~ s' ->
  R ⊢ substituteTCA X T s ~ substituteTCA X T s'.
Proof.
  induction i as [xi | xi ? bi | i1 IHi1 i2 IHi2];
  intros s s' R1 R2 R Ha_X Ha_T Htrans Hαs Hαs';
  inversion Hαs as [xs ? ? Hαvs | xs ? ? bs ? ? Hαbs | s1 ? s2 ? ? Hαs1 Hαs2 ]; subst;
  inversion Hαs' as [? xs' ? Hαvs' |? xs' ? ? bs' ? Hαbs' | ? s1' ? s2' ? Hαs1' Hαs2']; subst;
  autorewrite with capms; simpl.
  - (* Case: tmvar *)
    repeat rewrite substituteTCA_equation_1.
    assert (Hαv: AlphaVar R xs xs'). { eapply alpha_var_trans; eauto. }
    destr_eqb_eq X xs.
    + inversion Ha_X; subst.
      apply (alphavar_unique_right H2) in Hαv. subst. rewrite String.eqb_refl. 
      assumption.
    + inversion Ha_X; subst.
      remember (Hαv) as Hαv'. clear HeqHαv'.
      apply (alphavar_unique_not_left H H3) in Hαv.
      rewrite <- String.eqb_neq in Hαv.
      rewrite Hαv. 
      constructor.
      auto.
  - (* Case: tmlam *)
    
    (* remember (fresh2 _ bs) as b; rewrite cons_to_append in Heqb.
    remember (fresh2 _ bs') as b'; rewrite cons_to_append in Heqb'. *)
    (* idk, but it is true.*)
    destr_eqb_eq xs X.
    + rewrite substituteTCA_equation_2.
      remember (fresh2 _ bs) as b; rewrite cons_to_append in Heqb.
      rewrite String.eqb_refl.
      eapply @alpha_sym with (ren := sym_alpha_ctx R); eauto with α_eq_db.
      eapply substituteTCA_vacuous; eauto with α_eq_db.
      eapply @alpha_preserves_no_ftv with (x := X) (s := tmlam X t bs).
      * apply ftv_lam_no_binder.
      * eauto with α_eq_db.
      * inversion Ha_X; eauto.
    + destr_eqb_eq xs' X.
      * assert (substituteTCA X T (tmlam X t bs') = tmlam X t bs').
        {
          rewrite substituteTCA_equation_2.
          rewrite String.eqb_refl.
          reflexivity.
        }
        rewrite H0.
        eapply substituteTCA_vacuous; eauto with α_eq_db.
        eapply @alpha_preserves_no_ftv with (x := X) (s := tmlam X t bs').
        -- apply ftv_lam_no_binder.
        -- eauto with α_eq_db.
        -- inversion Ha_X; eauto. eapply @alphavar_sym with (ren := R); eauto with α_eq_db.
      * autorewrite with substituteTCA.
        rewrite <- String.eqb_neq in H. rewrite String.eqb_sym in H. rewrite H.
        rewrite <- String.eqb_neq in H0. rewrite String.eqb_sym in H0. rewrite H0.

        destruct (existsb (eqb xs) (ftv T)) eqn:Hin; destruct (existsb (eqb xs') (ftv T)) eqn:Hin'.
        -- simpl.
           remember (fresh2 _ bs) as Y'.
           remember (fresh2 _ bs') as Y''.
           constructor.
           eapply IHbi; eauto.
           ++ eapply alpha_extend_fresh; auto.
              ** eapply fresh2_over_key_sigma with (X := X) in HeqY'.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_cons. apply in_eq.
              ** eapply fresh2_over_key_sigma with (X := X) in HeqY''.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_cons. apply in_eq.
           ++ eapply alpha_extend_fresh; auto.
              ** eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY'.
                 intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
                 apply in_cons. apply in_eq.
              ** eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY''.
                 intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
                 apply in_cons. apply in_eq.
           ++ constructor; eauto.
           ++ eapply alpha_trans_rename_left; eauto.
           ++ eapply alpha_trans_rename_right; eauto.
        -- simpl.
           remember (fresh2 _ bs) as Y'.
           constructor.
            eapply IHbi; eauto.
            ++ eapply alpha_extend_fresh; auto.
              ** eapply fresh2_over_key_sigma with (X := X) in HeqY'.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_cons. apply in_eq.
              ** intros Hcontra. apply ftv_var in Hcontra. subst.
                 rewrite String.eqb_neq in H0. contradiction.
            ++ eapply alpha_extend_fresh; auto.
              ** eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY'.
                 intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
                 apply in_cons. apply in_eq.
              ** eapply not_in_ftv_existsb_false. auto.
            ++ eauto with α_eq_db.
            ++ eapply alpha_trans_rename_left; eauto.
        -- simpl.
           remember (fresh2 _ _) as Y'.
           constructor.
           eapply IHbi; eauto. 
           ++ eapply alpha_extend_fresh; auto.
              ** intros Hcontra. apply ftv_var in Hcontra; subst.
                  rewrite String.eqb_neq in H. contradiction.
              **  
                eapply fresh2_over_key_sigma with (X := X) in HeqY'.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_cons. apply in_eq.

           ++ eapply alpha_extend_fresh; auto.
              eapply not_in_ftv_existsb_false. auto.
              eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY'.
              intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
              apply in_cons. apply in_eq.
           ++ constructor; eauto.
           ++ eapply alpha_trans_rename_right; eauto.
        -- constructor; eapply IHbi; eauto.
           ++ apply alpha_extend_fresh; auto.
              ** intros Hcontra. apply ftv_var in Hcontra; subst.
                  rewrite String.eqb_neq in H. contradiction.
              ** intros Hcontra. apply ftv_var in Hcontra; subst.
                  rewrite String.eqb_neq in H0. contradiction.
           ++ eapply alpha_extend_fresh; auto.
              eapply not_in_ftv_existsb_false. auto.
              eapply not_in_ftv_existsb_false. auto.
           ++ eauto with α_eq_db.  
  - autorewrite with substituteTCA.
    constructor.
    + eapply IHi1; eauto.
    + eapply IHi2; eauto.
Qed.

Lemma substituteTCA_preserves_alpha s s' ren X U:
  ren ⊢ (tmvar X) ~ (tmvar X) ->
  (ren ⊢ U ~ U) ->
  (ren ⊢ s ~ s') ->
  Alpha ren (substituteTCA X U s) (substituteTCA X U s').
Proof.
  intros.
  apply (@subs_preserves_alpha' X U s s s' (nil ++ ctx_id_left ren) ren ren); auto.
  - apply id_left_trans; auto.
  - apply alpha_extend_ids_right.
    + apply ctx_id_left_is_id.
    + apply alpha_refl. apply alpha_refl_nil.
Qed.

Lemma alpha_capms_to_naive X U T:
  {T' & Alpha [] T T' * Alpha [] (substituteTCA X U T) (sub X U T') * NC T' ((X, U)::nil)}.
Proof.
  exists (to_GU' X U T).
  split; [split|].
  - apply to_GU'__alpha.
  - eapply @alpha_trans with (t := substituteTCA X U (to_GU' X U T)).
    constructor.
    + eapply substituteTCA_preserves_alpha. eapply alpha_refl. constructor. eapply alpha_refl. constructor. apply to_GU'__alpha.
    + erewrite GU_substituteTCA_sub.
      * apply alpha_refl. constructor.
      * apply to_GU'__NC.
  - apply to_GU'__NC.
Qed.

Lemma alpha_preserves_normal_Ty__neutral_Ty s s' R :
  R ⊢ s ~ s' -> ((normal_Ty s -> normal_Ty s') * (neutral_Ty s -> neutral_Ty s')).
Proof.
  intros Ha_s.
  generalize dependent R.
  generalize dependent s'.
  induction s; intros s' R Ha_s; inversion Ha_s; subst.
  - split; repeat constructor.
  - edestruct IHs; eauto.
    split.
    + intros. constructor. eapply n. inversion H; subst. auto. inversion H0.
    + intros. inversion H.
  - edestruct IHs1; eauto.
    edestruct IHs2; eauto.
    split.
    + intros. constructor. constructor.
      * eapply n0. inversion H. inversion H0; subst. auto.
      * inversion H; subst. inversion H0. auto.
    + intros. inversion H; subst. constructor; eauto.
Qed.

Lemma alpha_preserves_normal_Ty s s' R :
  R ⊢ s ~ s' -> normal_Ty s -> normal_Ty s'.
Proof.
  intros Ha_s Hn.
  edestruct (alpha_preserves_normal_Ty__neutral_Ty Ha_s) as [H _].
  auto.
Qed.

(* Main lemma for going from using t alpha t' in SN t' to SN t*)
Lemma step_d_preserves_alpha ren s t s' :
  Alpha ren s t -> step_d s s' -> {t' & (step_d t t') * (Alpha ren s' t')}%type.
Proof.
  intros Halpha Hstep.
  generalize dependent t.
  generalize dependent ren.
  induction Hstep; intros ren t0 Halpha; inversion Halpha; subst.
  - inversion H2; subst.
    remember (alpha_capms_to_naive x t s).
    destruct s1 as [s' [ [Halpha1 Halpha2] Halpha3] ].
    eexists.
    split.
    + apply step_beta_d; eapply alpha_preserves_normal_Ty; eauto.
    + eapply @alpha_trans with (t := sub x t s').
      * apply id_left_trans.
      * change (ctx_id_left ren) with (nil ++ ctx_id_left ren).
        apply alpha_extend_ids_right.
        -- apply ctx_id_left_is_id.
        -- auto.
      * remember (alpha_capms_to_naive y t2 s0).
        destruct s1 as [t' [ [Halpha1' Halpha2'] Halpha3' ] ].
      
        eapply @alpha_trans with (t := sub y t2 t').
        -- apply id_right_trans.
        -- eapply alpha_rename_binder_stronger with (Rs := ((x, y)::ren)); eauto.
           ++ eapply @alpha_trans with (t := s) (ren := ctx_id_left ((x, y)::ren)) (ren' := ((x, y)::ren)); eauto with α_eq_db.
              ** apply id_left_trans.
              ** apply alpha_extend_ids.
                 --- apply ctx_id_left_is_id.
                 --- eapply alpha_sym. constructor. eauto.
              ** eapply @alpha_trans with (t := s0) (ren := ((x, y)::ren)) (ren' := ctx_id_right ((x, y)::ren)); eauto with α_eq_db.
                  --- apply id_right_trans.
                  --- apply alpha_extend_ids.
                      +++ apply ctx_id_right_is_id.
                      +++ eapply alpha_sym. constructor. eauto with α_eq_db.
           ++ constructor. apply legalRenSwap_id.
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
Qed.

Lemma step_d_implies_step_gu_na t t' : 
    step_d t t' ->  
    {t_α & step_gu_naive t t_α * (nil ⊢ t' ~ t_α)}.
Proof.
    remember (to_GU t) as t_GU.
    assert (nil ⊢ t ~ t_GU) as H_alpha.
    {
      subst.
      apply to_GU__alpha.
    }
    assert (GU t_GU) as H_GU.
    {
      subst.
      apply to_GU__GU.
    }
    intros.
    remember (step_d_preserves_alpha H_alpha H) as Hstep_GU.
    destruct Hstep_GU as [t_GU' [Hstep_GU Halpha_GU] ].
    exists t_GU'.
    split; auto.
    clear HeqHstep_GU.
    apply GU_step_d_implies_step_na in Hstep_GU.
    + apply step_gu_naive_intro with (s' := t_GU); auto.
    + subst. auto.
Qed.

Theorem α_preserves_sn_d s s' :
  Alpha [] s s' -> (@sn term step_d) s -> (@sn term step_d) s'.
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
  eapply X.
  - exact Hstep'.
  - eapply alpha_sym. apply alpha_sym_nil. exact Hα'.
Qed.

Lemma SN_na_to_SN_d t : (@sn term step_gu_naive) t -> (@sn term step_d) t.
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
  specialize (X t' Hstep).
  apply α_preserves_sn_d with t'.
  - eapply alpha_sym; [apply alpha_sym_nil |].
    assumption.
  - apply SNI. 
    exact X.
Qed.

Theorem strong_normalization E s T : has_type E s T -> (@sn term step_d) s.
  intros.
  apply SN_naive in H. 
  apply SN_na_to_SN_d.
  assumption.
Qed.