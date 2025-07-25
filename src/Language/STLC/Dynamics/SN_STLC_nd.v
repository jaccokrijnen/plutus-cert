From mathcomp Require Import ssreflect ssrbool eqtype.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import
  Free
  SN_STLC_GU
  step_naive
  GU_NC
  step_gu
  STLC
  STLC.Kinding
  Alpha.alpha
  alpha_rename
  util
  variables
  alpha_freshness
  alpha_sub
  alpha_vacuous
  construct_GU
.

(* Non-deterministic STLC reduction relation using naive beta reduction *)
(* NOTE: In the codebase there is no step_d, instead we address going from step_nd to a deterministic reduction for the whole of PIR later in the embedding argument.
In the thesis we postulate a step_d for readability.*)
Inductive step_nd : term -> term -> Type :=
| step_beta_nd (x : string) (A : PlutusIR.kind) (s t : term) :
    step_nd (@tmbin App (@tmabs Lam x A s) t) (substituteTCA x t s)
| step_appL_nd B s1 s2 t :
    step_nd s1 s2 -> step_nd (@tmbin B s1 t) (@tmbin B s2 t)
| step_appR_nd B s t1 t2 :
    step_nd t1 t2 -> step_nd (@tmbin B s t1) (@tmbin B s t2)
| step_abs_nd B x A s1 s2 :
    step_nd s1 s2 -> step_nd (@tmabs B x A s1) (@tmabs B x A s2).

(* No-capture during substitution implies equivalence of naive and capture-avoiding substitutions *)
Lemma NC__substituteTCA_is_sub x t s :
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
        apply not_in_existsb. assumption.
      - apply btv_lam.
    }
    rewrite H1.
    f_equal.
    apply IHs.
    eapply nc_lam. eauto.
  - autorewrite with substituteTCA. f_equal.
    + eapply IHs1; eapply nc_app_l. eauto.
    + eapply IHs2; eapply nc_app_r. eauto.
  - autorewrite with substituteTCA. auto.
Qed.

(* If t has globally unique binders (and free variables to make it easier)
    then deterministic step and naive step coincide*)
Lemma GU_step_d_implies_step_na t t' :
    GU t -> step_nd t t' -> step_naive t t'.
Proof.
    intros HGU_vars Hstep.
    induction Hstep.
    all: try solve [constructor; auto; inversion HGU_vars; auto].
    (* we can be sure that no binder in s appears in t by global uniqueness*)
    assert (substituteTCA x t s = sub x t s) as Hsub.
    {
        eapply NC__substituteTCA_is_sub.
        eapply gu_applam_to_nc. eauto.
      }
    rewrite Hsub.
    apply step_beta.
Qed.

(* A vacuous capture-avoiding substitution can still rename binders to fresh variables, hence we need α-equivalence here. *)
Lemma substituteTCA_vacuous' : forall R X U T T',
    Alpha R T T' ->
    ~ In X (ftv T) ->
    Alpha R (substituteTCA X U T) T'.
Proof.
  intros.
  generalize dependent T.
  generalize dependent R.
  induction T'; intros.
  all: inversion H; subst.
  all: autorewrite with substituteTCA.
  - apply not_in_ftv_var in H0.
    rewrite <- String.eqb_neq in H0.
    now rewrite H0.
  - destr_eqb_eq X x; [now constructor|].
    assert (~ In X (ftv s1)) by now apply ftv_lam_negative in H0.
    destruct (existsb (eqb x) (ftv U)) eqn:sinU.
    + simpl.
      remember (fresh2 _ s1) as Y.
      constructor.
      eapply IHT'.
      * eapply alpha_trans_rename_left; eauto.
      * apply ftv_not_in_rename; auto.
        eapply fresh2_over_key_sigma in HeqY. symmetry. eauto.
        apply in_eq.
    + constructor; auto.
  - constructor.
    + eapply IHT'1; eauto.
      now apply not_ftv_app_not_left in H0.
    + eapply IHT'2; eauto.
      now apply not_ftv_app_not_right in H0.
  - auto.
Qed.

Corollary substituteTCA_vacuous X U T:
  ~ In X (ftv T) ->
  Alpha nil (substituteTCA X U T) T.
Proof.
  eapply substituteTCA_vacuous'; try apply alpha_refl; auto; repeat constructor.
Qed.

(* Strengthened version of: α-equivalence preserves capture-avoiding substitutions*)
(* α-preservation of substitution with capture-avoiding substitutions
  requires transtitivity arguments because of renamings in each substitution
  this is what we prevent by using globally unique reductions later on*)
Lemma substituteTCA_preserves_alpha' X T i : forall s s' R1 R2 R,
  Alpha R (tmvar X) (tmvar X) ->
  Alpha R T T ->
  αCtxTrans R1 R2 R ->
  Alpha R1 s i ->
  Alpha R2 i s' ->
  Alpha R (substituteTCA X T s) (substituteTCA X T s').
Proof.
  induction i as [xi | B xi ? bi | B i1 IHi1 i2 IHi2|d];
  intros s s' R1 R2 R Ha_X Ha_T Htrans Hαs Hαs';
    inversion Hαs as [xs ? ? Hαvs | xs ? ? bs ? ? Hαbs | s1 ? s2 ? ? Hαs1 Hαs2 |]; subst;
    inversion Hαs' as [? xs' ? Hαvs' |? xs' ? ? bs' ? Hαbs' | ? s1' ? s2' ? Hαs1' Hαs2'|];
    subst; simpl.
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
  - (* Case: tmabs *)
    destr_eqb_eq x X.
    + rewrite substituteTCA_equation_2.
      remember (fresh2 _ s1) as b; rewrite cons_to_append in Heqb.
      rewrite String.eqb_refl.
      eapply @alpha_sym with (R := sym_alpha_ctx R); eauto with α_eq_db.
      eapply substituteTCA_vacuous'; eauto with α_eq_db.
      eapply @alpha_preserves_no_ftv with (x := X) (s := tmabs X k s1).
      * apply ftv_lam_no_binder.
      * eauto with α_eq_db.
      * inversion Ha_X; eauto.
    + destr_eqb_eq y X.
      * assert (Hvac_sub: substituteTCA X T (@tmabs B X k s2) = @tmabs B X k s2).
        {
          rewrite substituteTCA_equation_2.
          rewrite String.eqb_refl.
          reflexivity.
        }
        rewrite Hvac_sub.
        eapply substituteTCA_vacuous'; eauto with α_eq_db.
        eapply @alpha_preserves_no_ftv with (x := X) (s := tmabs X k s2).
        -- apply ftv_lam_no_binder.
        -- eauto with α_eq_db.
        -- inversion Ha_X; eauto. eapply @alphavar_sym with (R := R); eauto with α_eq_db.
      * autorewrite with substituteTCA.
        rewrite <- String.eqb_neq in H1. rewrite String.eqb_sym in H1. rewrite H1.
        rewrite <- String.eqb_neq in H2. rewrite String.eqb_sym in H2. rewrite H2.

        destruct (existsb (eqb x) (ftv T)) eqn:Hin; destruct (existsb (eqb y) (ftv T)) eqn:Hin'.
        -- simpl.
           remember (fresh2 _ s1) as Y'.
           remember (fresh2 _ s2) as Y''.
           constructor.
           eapply IHbi; eauto.
           ++ eapply alpha_extend_vacuous_ftv; auto.
              ** eapply fresh2_over_key_sigma with (X := X) in HeqY'.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_eq.
              ** eapply fresh2_over_key_sigma with (X := X) in HeqY''.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_eq.
           ++ eapply alpha_extend_vacuous_ftv; auto.
              ** eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY'.
                 intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
                 apply in_eq.
              ** eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY''.
                 intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
                 apply in_eq.
           ++ constructor; eauto.
           ++ eapply alpha_trans_rename_left; eauto.
           ++ eapply alpha_trans_rename_right; eauto.
        -- simpl.
           remember (fresh2 _ s1) as Y'.
           constructor.
            eapply IHbi; eauto.
            ++ eapply alpha_extend_vacuous_ftv; auto.
              ** eapply fresh2_over_key_sigma with (X := X) in HeqY'.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_eq.
              ** intros Hcontra. apply ftv_var in Hcontra. subst.
                 rewrite String.eqb_neq in H2. contradiction.
            ++ eapply alpha_extend_vacuous_ftv; auto.
              ** eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY'.
                 intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
                 apply in_eq.
              ** eapply not_in_existsb. auto.
            ++ eauto with α_eq_db.
            ++ eapply alpha_trans_rename_left; eauto.
        -- simpl.
           remember (fresh2 _ s2) as Y'.
           constructor.
           eapply IHbi; eauto.
           ++ eapply alpha_extend_vacuous_ftv; auto.
              ** intros Hcontra. apply ftv_var in Hcontra; subst.
                  rewrite String.eqb_neq in H1. contradiction.
              **
                eapply fresh2_over_key_sigma with (X := X) in HeqY'.
                 intros Hcontra. apply ftv_var in Hcontra.  subst. contradiction.
                 apply in_eq.

           ++ eapply alpha_extend_vacuous_ftv; auto.
              eapply not_in_existsb. auto.
              eapply fresh2_over_tv_value_sigma with (X := X) (s := T) in HeqY'.
              intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
              apply in_eq.
           ++ constructor; eauto.
           ++ eapply alpha_trans_rename_right; eauto.
        -- constructor; eapply IHbi; eauto.
           ++ apply alpha_extend_vacuous_ftv; auto.
              ** intros Hcontra. apply ftv_var in Hcontra; subst.
                  rewrite String.eqb_neq in H1. contradiction.
              ** intros Hcontra. apply ftv_var in Hcontra; subst.
                  rewrite String.eqb_neq in H2. contradiction.
           ++ eapply alpha_extend_vacuous_ftv; auto.
              eapply not_in_existsb. auto.
              eapply not_in_existsb. auto.
           ++ eauto with α_eq_db.
  - autorewrite with substituteTCA.
    constructor.
    + eapply IHi1; eauto.
    + eapply IHi2; eauto.
  - autorewrite with substituteTCA.
    constructor.
Qed.

(* α-equivalence preserves capture-avoiding substitutions*)
Lemma substituteTCA_preserves_alpha s s' R X U:
  Alpha R (tmvar X) (tmvar X) ->
  Alpha R U U ->
  Alpha R s s' ->
  Alpha R (substituteTCA X U s) (substituteTCA X U s').
Proof.
  intros.
  apply (@substituteTCA_preserves_alpha' X U s s s' (nil ++ ctx_id_left R) R R); auto.
  - apply id_left_trans; auto.
  - apply alpha_extend_ids_right.
    + apply ctx_id_left_is_id.
    + apply alpha_refl. apply id_ctx_nil.
Qed.

(* There always exists an α-equivalent representative such that naive and capture-avoiding substitutions coincide. *)
Lemma alpha_substituteTCA_sub X U T:
  {T' & Alpha [] T T' * Alpha [] (substituteTCA X U T) (sub X U T') * NC T' ((X, U)::nil)}%type.
Proof.
  exists (to_GU' X U T).
  split; [split|].
  - apply to_GU'__alpha.
  - eapply @alpha_trans with (t := substituteTCA X U (to_GU' X U T)).
    constructor.
    + eapply substituteTCA_preserves_alpha. eapply alpha_refl. constructor. eapply alpha_refl. constructor. apply to_GU'__alpha.
    + erewrite NC__substituteTCA_is_sub.
      * apply alpha_refl. constructor.
      * apply to_GU'__NC.
  - apply to_GU'__NC.
Qed.

(* Non-deterministic step preserves α-equivalence *)
Lemma step_nd_preserves_alpha ren s t s' :
  Alpha ren s t -> step_nd s s' -> {t' & (step_nd t t') * (Alpha ren s' t')}%type.
Proof.
  intros Halpha Hstep.
  generalize dependent t.
  generalize dependent ren.
  induction Hstep; intros ren t0 Halpha; inversion Halpha; subst.
  - inversion H4; subst.
    destruct (alpha_substituteTCA_sub x t s) as [s' [ [Halpha1 Halpha2] Halpha3] ].
    eexists.
    split; try constructor.
    eapply @alpha_trans with (t := sub x t s') (R := ctx_id_left ren) (R1 := ren); eauto with α_eq_db α_eq_db_trans.
    destruct (alpha_substituteTCA_sub y t2 s0) as [t' [ [Halpha1' Halpha2'] Halpha3' ] ].
    eapply @alpha_trans with (t := sub y t2 t'); eauto with α_eq_db α_eq_db_trans.
    eapply alpha_rename_binder_stronger with (Rs := ((x, y)::ren)); eauto with α_eq_db.
    + eapply @alpha_trans with (t := s) (R := ctx_id_left ((x, y)::ren)) (R1 := ((x, y)::ren)); eauto with α_eq_db α_eq_db_trans.
    + constructor.
  - destruct (IHHstep ren s3 H4) as [t1_α [Hstep' Halpha'] ].
    exists (@tmbin B t1_α t2); split.
    + apply step_appL_nd. assumption.
    + apply alpha_app; assumption.
  - destruct (IHHstep ren t4 H5) as [tα [Hstep' Halpha'] ].
    exists (@tmbin B s2 tα); split.
    + apply step_appR_nd; auto.
    + apply alpha_app; assumption.
  - destruct (IHHstep ((x, y)::ren) s3 H5) as [tα [Hstep' Halpha'] ].
    exists (@tmabs B y A tα); split.
    + apply step_abs_nd. assumption.
    + apply alpha_lam; assumption.
Qed.

(* Non-deterministic step is globally unique step up to α-equivalence *)
Lemma step_nd_implies_step_gu t t' :
    step_nd t t' ->
    {t_α & step_gu t t_α * (Alpha [] t' t_α)}%type.
Proof.
    intros.
    remember (step_nd_preserves_alpha) as Hstep_GU.
    edestruct Hstep_GU with (s := t) (t := to_GU t) as [t_GU' [Hstep_GU' Halpha_GU] ]; eauto with to_GU_db.
    exists t_GU'.
    split; auto.
    apply GU_step_d_implies_step_na in Hstep_GU'; eauto with to_GU_db.
    eapply step_gu_intro; eauto with to_GU_db.
Qed.

(* Strong normalization using step_nd is preserved under α-equivalence *)
Theorem α_preserves_sn_nd s s' :
  Alpha [] s s' -> (@sn term step_nd) s -> (@sn term step_nd) s'.
Proof.
  intros Hα Hsn.
  generalize dependent s'.
  induction Hsn. intros s' Hα.
  apply SNI.
  intros y1 Hstep.
  edestruct step_nd_preserves_alpha with (s := s') (t := x) as [y1_α [Hstep' Hα']]; eauto with α_eq_db.
Qed.

(* Forward simulatino argument to go from globally uniquifying strong normalization, to non-deterministic step strong normalization *)
Lemma SN_na_to_SN_nd t : (@sn term step_gu) t -> (@sn term step_nd) t.
Proof.
  intros Hsn_nd.
  apply SNI.
  intros t' Hstep.
  generalize dependent t'.
  induction Hsn_nd; intros t Hstep_d.
  edestruct step_nd_implies_step_gu with (t := x) as [t' [Hstep Halpha] ]; eauto with α_eq_db.
  specialize (X t' Hstep).
  apply α_preserves_sn_nd with t'; eauto with α_eq_db.
  apply SNI.
  exact X.
Qed.

(* STLC with a non-deterministic capture-avoiding step relation is strongly normalizing *)
Theorem strong_normalization_nd Δ s T : STLC.Kinding.has_kind Δ s T -> (@sn term step_nd) s.
  intros.
  apply strong_normalization_gu in H.
  apply SN_na_to_SN_nd.
  assumption.
Qed.
