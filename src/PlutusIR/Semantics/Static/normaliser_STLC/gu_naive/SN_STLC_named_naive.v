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
From PlutusCert Require Import STLC_named STLC_named_typing ARS pre constructions.
From PlutusCert Require Import alpha alpha_rename rename util alpha_ctx_sub freshness alpha_freshness.




Create HintDb gu_nc_db.
Hint Resolve gu_app_r : gu_nc_db.
Hint Resolve gu_app_l : gu_nc_db.
Hint Resolve gu_lam : gu_nc_db.
Hint Resolve nc_app_r : gu_nc_db.
Hint Resolve nc_app_l : gu_nc_db.
Hint Resolve nc_lam : gu_nc_db.
Hint Resolve gu_applam_to_nc : gu_nc_db.
Hint Resolve nc_ftv_env : gu_nc_db.



(* We need a legal ren swap because the new binders get in front of the (x, y) in the inductive step of the lambda*)
Lemma alpha_rename_binder_stronger x y s t t' : forall Rt s' Rs,
  Alpha Rs s s' ->
  Alpha Rt t t' ->
  LegalRenSwap ((x, y)::Rt) Rs -> 
  NC s [(x, t)] ->
  NC s' [(y, t')] ->
  Alpha Rt (sub x t s) (sub y t' s').
Proof with eauto with gu_nc_db.
  intros.
  generalize dependent Rt.
  generalize dependent Rs.
  generalize dependent t.
  generalize dependent t'.
  generalize dependent s'.
  induction s; intros; inversion H; subst; simpl.
  - destr_eqb_eq x s; destr_eqb_eq y y0; eauto.
    + exfalso.
      apply lrs_sym in H1.
      apply (alpha_swap H1) in H.
      inversion H; subst.
      inversion H9; subst.
      contradiction H4; auto.
      contradiction H10; auto.
    + exfalso.
      apply lrs_sym in H1.
      apply (alpha_swap H1) in H.
      inversion H; subst.
      inversion H9; subst.
      contradiction H4; auto.
      contradiction H13; auto.
    + eapply @alpha_swap with (ren' := ((x, y)::Rt)) in H.
      inversion H; subst.
      inversion H10; subst; try contradiction.
      apply alpha_var.
      assumption.
      apply lrs_sym. auto.
  - constructor.
    eapply IHs; eauto...
    + eapply alpha_extend_vacuous_ftv.
      * apply nc_ftv_env with (x := s) in H2.
        simpl in H2.
        intuition. apply btv_lam.
      * apply nc_ftv_env with (x := y0) in H3.
        simpl in H3.
        intuition. apply btv_lam.
      * assumption.
    + eapply @lrs_trans with (ren2 := ((s, y0)::(x, y)::Rt)).
      * constructor. 
        -- apply nc_ftv_env with (x := s) in H2.
           simpl in H2. intuition. apply btv_lam.
        -- apply nc_ftv_env with (x := y0) in H3.
           simpl in H3. intuition. apply btv_lam.
        -- apply legalRenSwap_id.
      * constructor. assumption.
  - constructor; eauto with gu_nc_db.
Qed.

Lemma step_naive_preserves_alpha2 s t s' R:
  GU s -> GU s' -> Alpha R s s' -> step_naive s t -> {t' & step_naive s' t' * Alpha R t t'}%type.
Proof.
  intros.
  generalize dependent R.
  generalize dependent s'.
  induction H2; subst; intros.
  - inversion H1; subst. inversion H5; subst.
    exists (sub y t2 s0).
    split.
    + constructor.
    + eapply alpha_rename_binder_stronger; eauto with gu_nc_db.
      constructor. apply legalRenSwap_id.
  - inversion H1; subst.
    specialize (IHstep_naive (gu_app_l H) s3 (gu_app_l H0) R H6) as [t' [Hstep_t' HR_t'] ].
    exists (tmapp t' t2).
    split; constructor; auto.
  - inversion H1; subst.
    specialize (IHstep_naive (gu_app_r H) t3 (gu_app_r H0) R H8) as [t' [Hstep_t' HR_t'] ].
    exists (tmapp s2 t').
    split; constructor; auto.
  - inv H1.
    specialize (IHstep_naive (gu_lam H) s3 (gu_lam H0) ((x, y)::R) H8) as [t' [Hstep_t' HR_t'] ].
    exists (tmlam y A t').
    split; constructor; auto.
Qed.

(* Examples
λ x. x is GU_vars
λ x. y is GU_vars
λ x. λ y. x is GU_vars

(λ x. x) y is GU_vars
(λ x. x) x is not GU_vars (* free var is equal to a bound var*)
(λ y. x) x is GU_vars (* all vars with the same name refer to the same term*)
*)

(* If a term has globally unique binders, then it has unique binders*)

Inductive step_gu_naive : term -> term -> Set :=
| step_gu_naive_intro s s' t : 
    Alpha [] s s' ->
    GU s' ->
    step_naive s' t ->
    step_gu_naive s t.
(*     
    Alpha [] t' t ->
    GU_vars t ->
    step_gu_naive s t. *)

(* used to be prop (TODO: Defined also in SN_STCL_named )*)
Inductive sn {e : term -> term -> Set } x : Set :=
| SNI : (forall y, e x y -> sn y) -> sn x.

Notation SN_na := (@sn step_gu_naive).

Lemma step_gu_naive_preserves_alpha {s} {s'} {t} R :
  Alpha R s t -> step_gu_naive s s' -> {t' & prod (step_gu_naive t t') (Alpha R s' t')}.
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
  - apply step_gu_naive_intro with (s' := (to_GU t)); eauto.
    + apply to_GU__alpha.
    + apply to_GU__GU.
  - auto.
Qed.


Inductive star {e : term -> term -> Set } (x : term) : term -> Set :=
| starR : star x x
| starSE y z : star x y -> e y z -> star x z.


(** **** Many-Step Reduction 
TODO: See if we can use the star from autosubst ARS again. (uses Prop instead of Set)
*)
Inductive red_gu_na : term -> term -> Set :=
| red_gu_na_star s t t':
     step_gu_naive s t -> 
     red_gu_na t t' ->
     red_gu_na s t' 
| red_gu_na_nil s :
     red_gu_na s s.


Lemma red_gu_naive_preserves_alpha {s} {s'} {t} R :
  Alpha R s t -> red_gu_na s s' -> {t' & prod (red_gu_na t t') (Alpha R s' t')}.
Proof.
  intros.
  generalize dependent R.
  generalize dependent t.  
  induction H0; intros.
  - apply (step_gu_naive_preserves_alpha H) in s0.
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

Theorem α_preserves_SN_R s s' R :
  Alpha R s s' -> SN_na s -> SN_na s'.
Proof.
  intros Hα Hsn.
  generalize dependent s'.
  generalize dependent R.
  induction Hsn. intros R s' Hα.
  apply SNI.
  intros y1 Hstep.
  assert ({y1_α & prod (step_gu_naive x y1_α) (sym_alpha_ctx R ⊢ y1 ~ y1_α)}) as [y1_α [Hstep' Hα'] ].
  {
    eapply step_gu_naive_preserves_alpha; auto.
    - eauto with α_eq_db.
    - exact Hstep.
  }
  eapply H; eauto with α_eq_db.
Qed.

Lemma sn_preimage {e : term -> term -> Set} (h : term -> term) x :
  (forall x y, e x y -> e (h x) (h y)) -> @sn e (h x) -> @sn e x.
Proof.
  intros A B.
  remember (h x) as v. (* this allows us to keep B : sn v as an hypothesis*)
  generalize dependent h.
  generalize dependent x.
  induction B.
  intros x0 h A eqn.
  apply SNI.
  intros y C.
  apply A in C.
  specialize (H (h y)).
  rewrite <- eqn in C.
  eapply H.
  - assumption.
  - exact A.
  - reflexivity.
Qed.

(* TODO: It is currently for step only, not for general relation e anymore.
Idea: Previous lemma sn_preimage above strengthened IH with remember (h x) as v.
We strenghen IH with (h x) ~ v.
 *)
Lemma sn_preimage_α' (h : term -> term) x v :
  (forall x y, step_gu_naive x y -> {y_h & prod (step_gu_naive (h x) y_h) (nil ⊢ y_h ~ (h y))}) -> @sn step_gu_naive v -> nil ⊢ v ~ h x -> @sn step_gu_naive x.
Proof.
  intros A B Halpha.
  generalize dependent h.
  generalize dependent x.
  (* remember (h x) as v. (* this allows us to keep B : sn v as an hypothesis*)
  generalize dependent h.
  generalize dependent x.
  assert (forall x h, (forall x0 y, e x0 y -> {y_h & prod(e (h x0) y_h) (nil ⊢ y_h ~ h y)}) -> nil ⊢ v ~ h x -> @sn e x).
  {
  intros x h A. *)
  (* So we are now not proving sn (h x) -> sn x anymore.
    We are proving: sn v ->  v ~ h x  -> sn x
  *)
  induction B.
  intros x0 h A eqn.
  apply SNI.
  intros y C.
  apply A in C.
  (* x ~ h x0.
    step (h x0) y_h  /\ y_h ~ h y

    exists y_h' s.t. step x y_h' /\ y_h' ~ y_h   ( and then y_h'  ~  h y)
  *)
  assert ({y_h' & prod (step_gu_naive x y_h') (nil ⊢ y_h' ~ h y)}).
  {
    destruct C as [yh [ehy yh_alpha] ].
    eapply alpha_sym in eqn; [|apply alpha_sym_nil].
    apply (step_gu_naive_preserves_alpha eqn) in ehy.
    destruct ehy as [t' [stept' alphat'] ].
    exists t'.
    split.
    - assumption.
    - eapply alpha_trans.
      + apply alpha_trans_nil.
      + eapply alpha_sym. apply alpha_sym_nil. exact alphat'.
      + assumption.
  }
  destruct H0 as [yh' [ehy' yh_alpha'] ].
  specialize (H yh').
  eapply H.
  - assumption.
  - exact A.
  - assumption.
Qed.

Lemma sn_preimage_α (h : term -> term) x :
  (forall x y, step_gu_naive x y -> {y_h & prod (step_gu_naive (h x) y_h) (nil ⊢ y_h ~ (h y))}) -> @sn step_gu_naive (h x) -> @sn step_gu_naive x.
Proof.
  intros A B.
  apply sn_preimage_α' with (v := h x) (h := h); eauto.
  apply alpha_refl. apply alpha_refl_nil.
Qed.

(* We need alpha here because global unique can create different terms depending on input:
  global unique does not compose
  suppose there is a free var in s2, then that must be renamed when doing step_gu_naive (tmapp s1 s2)
  while that is not the case in step_gu_naive s1 t1 (there s2 does not need to be taken into account)
  *)
Lemma step_gu_naive_app_l s1 s2 t1 :
  step_gu_naive s1 t1 -> 
  {t1' & Alpha [] t1 t1' * {s2' & Alpha [] s2 s2' * step_gu_naive (tmapp s1 s2) (tmapp t1' s2')}%type }%type.
Proof.
  intros.
  assert ({s1' & { s2' & Alpha [] (tmapp s1 s2) (tmapp s1' s2') * GU (tmapp s1' s2')}}%type).
  {
    (* just renaming binders *)
    admit.
  }
  destruct H0 as [s1' [s2' [Ha_app H_gu] ] ].
  (* I think we then need a step_gu_naive_alpha*)
  assert (Alpha [] s1 s1') by now inv Ha_app.
  assert (Alpha [] s2 s2') by now inv Ha_app.
  apply (step_gu_naive_preserves_alpha H0) in H.
  destruct H as [t' [Hstep_s1' Ha_t1] ].
  inv Hstep_s1'.
  assert (Alpha [] s1 s').
  {
    eapply alpha_trans; eauto. constructor.
  }
  assert (Alpha [] (tmapp s1 s2) (tmapp s' s2')).
  {
    constructor; eauto.
  }
  clear Ha_app.

  (* tbh, i don't understand the flow of this, but it's all just renaming binders ;)*)

  exists t'.
  split; auto.
  assert ({s2'' & GU (tmapp s' s2'') * Alpha [] s2 s2''}%type) by admit. (* just renaming binders*)
  destruct H6 as [s2'' [Hgu_app Ha_s2'] ].
  exists s2''.
  split; auto.
  clear H5.
  econstructor; eauto.
  - constructor; eauto.
  - apply step_appL. auto.
Admitted.

Lemma sn_closedL t s : SN_na (tmapp s t) -> SN_na s.
Proof.
  apply: (sn_preimage_α (h := tmapp^~t)) => x y.
  intros.
  apply (step_gu_naive_app_l t) in H.
  destruct H as [t1' [Ha_t1' [s2' [Ha_t Hstep] ] ] ].
  exists (tmapp t1' s2').
  intuition.
  constructor; eapply alpha_sym; intuition; constructor.
Qed.

Lemma psubs_vac_var sigma x :
  ~ In x (map fst sigma) ->
  psubs sigma (tmvar x) = (tmvar x).
Proof.
  intros.
  induction sigma.
  - reflexivity.
  - admit.
Admitted.


Lemma subs_vac_var sigma x :
  ~ In x (map fst sigma) ->
  subs sigma (tmvar x) = (tmvar x).
Proof.
  intros.
  induction sigma.
  - reflexivity.
  - admit.
Admitted.

(* need also handle btv, since substitution is nto capture avoiding*)
Lemma sub_vac x t s :
 ~ In x (ftv s) ->
 ~ In x (btv s) ->
 sub x t s = s.
Admitted.
(* looks like sub_vacuous maybe?*)


(* May also work on sequential substiutions with additional assumptions.
  For now only needed for parallel substitutions
*)
Lemma subs_preserves_alpha_σ_R s : forall R s' sigma sigma',
  NC s sigma ->
  NC s' sigma' ->
  Alpha R s s' ->
  αCtxSub R sigma sigma' ->
  Alpha R (psubs sigma s) (psubs sigma' s').
Proof with eauto with gu_nc_db.
  induction s; intros; inv H1; simpl.
  - destruct (lookup s sigma) eqn:lookup_x_sigma.
    + destruct (alpha_ctx_right_ex H2 H5 lookup_x_sigma) as [t' [Hlookupy_sigma' Ht'_a] ].
      now rewrite Hlookupy_sigma'.
    + rewrite (alpha_ctx_right_nex H2 H5 lookup_x_sigma).
      constructor. assumption.
  - constructor.
    eapply IHs...
    * eapply alpha_ctx_ren_extend_fresh_ftv; auto;
      eapply nc_ftv_env; eauto; apply btv_lam.
  - constructor...
Qed.

Definition subs' sigma s := subs sigma (to_GU s). (* something like that*)




(* I devised this to make soundness var case easier, but is not getting easier
  so maybe I try to switch to paralell substs anyway.


(* what if we have ((x, t), (y, λx. x)) applied to y
  then in sequential substs, we replace y by the lambda, and then the next sub goes under the binder and gets caught
  in parallel we replace y by the lambda and are done...

  hence we need x not a btv as well? oooof.
*)

*)
Lemma psubs_nil s : psubs nil s = s.
Admitted.

Inductive ParSeq : list (string * term) -> Set :=
| ParSeq_nil : ParSeq []
| ParSeq_cons x t sigma :
    ParSeq sigma -> 
    (* ~ In x (List.concat (map ftv (map snd sigma))) ->  *)
    ~ In x (ftv_keys_env sigma) -> (* UPDATE Feb 27: we cannot have that x is a key in sigma either
      look e.g. at (x, a)::(x, b). As a sequential sub applied to tmvar x, we get b.
                                    As a parallel, we get a.

    *)
    ~ In x (btv_env sigma) -> (* Update Mar 6: OTHERWISE WE CAN GET CAPTURE IN sigma *)
    ParSeq ((x, t)::sigma).
(* This says that one subsitutions does not have effect on the next one
  In other word, no substiutions chains, where x -> t, and then t -> y, etc.

  This also means that if we define lookup as right oriented, that
    lookup_left x sigma = Some T   -> subs sigma (tmvar x) = T
*)

(* Say (x, t)::sig2, and sigma =sig1++sig2
  Say y in ftv t. Then we have a problem if y in lhs sig1.
  But, this cannot happen by blabla.

  Also, we will use right-biased lookup.

  TODO: Do we need to enforce that we cannot have twice the same key? 
  For now: righthanded lookup will do the job
*)
Lemma parseq_smaller {sigma x t} :
  ParSeq ((x, t)::sigma) -> ParSeq sigma.
Admitted.

Lemma psubs_to_subs {s sigma} :
  ParSeq sigma -> subs sigma s = psubs sigma s.
Proof.
  intros.
  induction sigma.
  - simpl. rewrite psubs_nil. reflexivity.
  - destruct a as [a1 a2].
    remember (parseq_smaller H) as Hsmall.
    simpl.
    generalize dependent sigma.
    induction s.
    + intros.
      destr_eqb_eq a1 s.
      * simpl. rewrite String.eqb_refl.
        assert (subs sigma (tmvar s) = (tmvar s)).
        {
          apply subs_vac_var.
          inversion H; subst.
          (* well yes.. definition mismatch, but trivial *) admit.
        }
        rewrite H0.
        simpl.
        rewrite String.eqb_refl.
        reflexivity.
      * simpl.
        rewrite <- String.eqb_neq in H0.
        rewrite H0.
        assert (sub a1 a2 (subs sigma (tmvar s)) = (subs sigma (tmvar s))).
        {
          
          rewrite <- single_subs_is_sub.
          apply sub_vac. (* NOTE: Because this also talks about btvs, that is why we needed to add the btv condeition in parseq*)
          inversion H; subst.
          - (* by a1 not s, and a1 not in ftv keys env sigma and subs does not introduce new ftv*) admit.
          - inversion H; subst. (* by a1 not in btv_env sigma and subs does not introduce new btv*) admit.
        }
        rewrite H1.
        eapply IHsigma.
        auto.
    + intros.
      simpl.
      autorewrite with subs_db.
      simpl.
      f_equal.
      eapply IHs.
      * intros.
        specialize (IHsigma H0).
        autorewrite with subs_db in IHsigma.
        simpl in IHsigma.
        inversion IHsigma.
        auto.
      * eauto.
    + intros.
      autorewrite with subs_db.
      simpl.
      f_equal.
      * eapply IHs1.
        -- intros.
           specialize (IHsigma H0).
           autorewrite with subs_db in IHsigma.
           simpl in IHsigma.
           inversion IHsigma.
           auto.
        -- eauto.
      * eapply IHs2.
        -- intros.
           specialize (IHsigma H0).
           autorewrite with subs_db in IHsigma.
           simpl in IHsigma.
           inversion IHsigma.
           auto.
        -- eauto.
Admitted.

Lemma single_parseq x t : ParSeq [(x, t)].
Admitted.

Lemma sub_vacuous x t s :
  ~ In x (ftv s) -> NC s ((x, t)::nil) -> sub x t s = s.
Proof.
  intros.
  induction s; simpl; auto.
  - destr_eqb_eq x s; auto. unfold ftv in H. contradiction H. apply in_eq.
  - f_equal. 
    assert (s <> x).
    {
      apply nc_ftv_env with (x := s) in H0. 
      simpl in H0.
      intuition.
      apply btv_lam.

    }
    apply ftv_lam_negative in H.
    apply IHs. intuition.
    eapply nc_lam; eauto. auto.
  - f_equal.
    + eapply IHs1; eauto.
      eapply not_ftv_app_not_left. eauto. eapply nc_app_l; eauto.
    + eapply IHs2; eauto. 
      eapply not_ftv_app_not_right. eauto. eapply nc_app_r; eauto.
Qed.

Lemma ftv_keys_env__no_keys sigma x :
  ~ In x (ftv_keys_env sigma) -> ~ In x (map fst sigma).
Admitted.

Lemma ftv_keys_env__no_values sigma x :
  ~ In x (ftv_keys_env sigma) -> (forall val, In val (map snd sigma) -> ~ In x (ftv val)).
Admitted.

Lemma ftv_keys_env_helper sigma x :
  ~ In x (map fst sigma) -> (forall ftvs, In ftvs (map snd sigma) -> ~ In x (ftv ftvs)) 
    -> ~ In x (ftv_keys_env sigma).
Admitted.

(* substitutions do not introduce new free variables 
*)
Lemma psubs_no_ftv x sigma y:
  ~ In x (ftv_keys_env sigma) -> x <> y -> ~ In x (ftv (psubs sigma (tmvar y))).
Proof.
  intros.
  unfold psubs.
  destruct (lookup y sigma) eqn:lookup_y_sigma.
  - eapply ftv_keys_env__no_values in H; eauto.
    apply lookup_In in lookup_y_sigma.
    apply in_map_iff. exists (y, t). simpl. auto.
  - simpl. intuition.
Qed.



(* I want to be in a position where the binders are chosen thus that I can do substitueT
  without checking if we are tyring to substitute a binder:
    i.e. no checks in substituteT 
    Then we ahve the property:
    subsT x t (tmlam y T s) = tmlam y T (subsT x t s) even if x = y (because that cannot happen anymore)
      Then also NC can go into the lambda
    this can be put into the NC property?
    *)
  (* Maybe we can leave out the R by switching to a renaming approach? *)

(* TODO: These sigma's can be single substitutions I think!
  - Used in step_subst, there it can be single substs
    - Used in beta_expansion: single substs *)
Lemma commute_sub_naive R x s t (sigma sigma' : list (string * term)) xtsAlpha:
  Alpha R (sub x t s) xtsAlpha ->
  αCtxSub R sigma sigma' -> (* TODO: Vars in R not in sigma?*)

  (* these two just say: x not in key or ftv sigma*)
  ~ In x (map fst sigma) ->
  (forall ftvs, In ftvs (map snd sigma) -> ~ In x (ftv ftvs)) -> 
  NC xtsAlpha sigma' ->
  NC s [(x, t)] ->
  NC s sigma ->
  NC t sigma ->
  NC (psubs sigma s) [(x, psubs sigma t)] ->
  (* s.t. substituteTs sigma xtsAlpha does not capture 
    e.g. suppose sigma:= [y := x]
    and xtsAlpha = λx. y.
    then substituting would capture.
    But we can always choose an alpha equivalent xtsAlpha with 
    different binder names not occuring in the rhs of sigma
  *)
  R ⊢ (sub x (psubs sigma t) (psubs sigma s))
      ~ (psubs sigma' xtsAlpha).
Proof with eauto with gu_nc_db.
  intros.
  generalize dependent xtsAlpha.
  generalize dependent R.
  induction s; intros.
  - (* We need to have that x does not occur in lhs or rhs of sigma! We have control over x
    when calling this function, so we should be good.*)
    destr_eqb_eq x s.
    + simpl in H. rewrite String.eqb_refl in H.
      destruct (in_dec String.string_dec s (map fst sigma)).
      * contradiction.
      * assert (psubs sigma (tmvar s) = tmvar s) by now apply psubs_vac_var. (* DONE: s not in sigma*)
        rewrite H8.
        simpl.
        rewrite String.eqb_refl.
        eapply subs_preserves_alpha_σ_R; eauto.
    + simpl in H. 
      rewrite <- String.eqb_neq in H8.
      rewrite H8 in H.
      inversion H; subst.
      destruct (in_dec String.string_dec s (map fst sigma)).
      (* 
        by s in keys, ther emust be a value. Hmm. But these are sequential substs...
      *)
      * rewrite sub_vacuous; auto.
        {
          eapply subs_preserves_alpha_σ_R; eauto.
        }
        apply psubs_no_ftv.
        -- apply ftv_keys_env_helper; auto.
        -- apply String.eqb_neq. assumption.
        

      * assert (psubs sigma (tmvar s) = tmvar s) by now apply psubs_vac_var. (* DONE : s not in fst sigma *)
        rewrite H9.
        unfold sub.
        rewrite H8.
        rewrite <- H9.
        eapply subs_preserves_alpha_σ_R; eauto.

  - inversion H; subst.
    autorewrite with subs_db in *.
    constructor.
    eapply IHs; try eapply nc_lam; eauto.
    apply alpha_ctx_ren_extend_fresh_ftv; eauto.
    + eapply nc_ftv_env in H5; eauto. apply btv_lam.
    + eapply nc_ftv_env in H3; eauto. apply btv_lam.
  - simpl in H.
    inversion H; subst.
    autorewrite with subs_db in *.
    constructor. fold sub.
    + eapply IHs1...
    + eapply IHs2...
Qed.



Lemma step_subst_single R {x p s t t' } :
  step_naive s t -> 
  GU s ->  (*  We could return them, but we don't want to. Current idea: have GU in NC *)
  NC s [(x, p)] -> (* no free vars in sigma are binders in s'*)
  Alpha R t t' -> 
  αCtxSub R [(x, p)] [(x, p)] -> 
  (* GU t' -> *)
  NC t' [(x, p)] ->
  {aT : term & 
  (step_gu_naive (subs ((x, p)::nil) s) aT) * (Alpha R aT (subs ((x, p)::nil) t'))}%type.
Proof with eauto with sconstr2_db.
  intros. rename H into Hstep. generalize dependent t'. generalize dependent R. induction Hstep; intros.
  - 
    (* The difficult case. The whole reason we need to do global uniqueness every step
      *)
      
      autorewrite with subs_db. 
      remember (sconstr1 x x0 p s t) as sconstr1_.
      destruct sconstr1_ as [sub_s sub_t].

      exists (sub x0 sub_t sub_s).
      split.
      + eapply step_gu_naive_intro with (s' := (tmapp (tmlam x0 A sub_s) sub_t)).
        * constructor. 
          -- constructor. eapply alpha_extend_ids. constructor. constructor. eapply @alpha_sym; eauto. constructor.
             eapply sconstr1_alpha_s. eauto.
          -- eapply @alpha_sym. constructor. eauto. eapply sconstr1_alpha_t. eauto.
        * eapply sconstr1_gu. eauto.
        * apply step_beta.
      + (* Invert some stuff to end up with a single sub *)
        remember (sconstr2 x0 t x p s ) as sconstr2_.
        destruct sconstr2_ as [ [s' t'0] p'].

        eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R) (t := sub x0 (subs ((x, p')::nil) t'0) (subs ((x, p')::nil) s')).
        * eapply id_left_trans.
        * eapply alpha_extend_ids.
          eapply ctx_id_left_is_id.
          repeat rewrite <- single_subs_is_sub.
          repeat rewrite psubs_to_subs; try apply single_parseq.
          eapply subs_preserves_alpha_σ_R with (R := nil).
          -- eapply gu_applam_to_nc. eapply sconstr1_gu. eauto.
          -- eapply sconstr2_nc_sub; eauto.
          -- rewrite <- psubs_to_subs; [|apply single_parseq].
             eapply @alpha_trans. constructor. 
             ++ eapply sconstr1_alpha_s. eauto.
             ++ repeat rewrite psubs_to_subs; try apply single_parseq.
                eapply subs_preserves_alpha_σ_R.
                ** exact (nc_lam (nc_app_l H1)).
                ** eapply sconstr2_nc_s; eauto.
                ** eapply sconstr2_alpha_s; eauto.
                ** constructor. constructor. constructor.
                   eapply sconstr2_alpha_p; eauto.
          -- constructor. constructor. constructor.
             eapply @alpha_trans. constructor.
             ++ eapply sconstr1_alpha_t. eauto.
             ++ repeat rewrite psubs_to_subs; try apply single_parseq.
                eapply subs_preserves_alpha_σ_R.
                ** exact (nc_app_r H1).
                ** eapply sconstr2_nc_t; eauto.
                ** eapply sconstr2_alpha_t; eauto.
                ** constructor. constructor. constructor.
                   eapply sconstr2_alpha_p; eauto.
        * 
        repeat rewrite psubs_to_subs; try apply single_parseq.
        {
          eapply commute_sub_naive; eauto.
          * eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R) (t := sub x0 t s).
            - eapply id_left_trans.
            - eapply alpha_extend_ids.
              eapply ctx_id_left_is_id.
              repeat rewrite <- single_subs_is_sub.
              repeat rewrite psubs_to_subs; try apply single_parseq.
              eapply subs_preserves_alpha_σ_R with (R := nil).
              + eapply sconstr2_nc_s_t; eauto.
              + eapply gu_applam_to_nc. eauto.
              + eapply @alpha_sym. constructor. eapply sconstr2_alpha_s; eauto.
              + constructor. constructor. constructor. eapply @alpha_sym. constructor. eapply sconstr2_alpha_t. eauto.
            - assumption.
          * eapply αctx_trans with (R1 := ctx_id_left R) (R2 := R) (R := R) (σ' := ((x, p)::nil)); auto.
            - eapply id_left_trans.
            - constructor. constructor. 
              + apply alphavar_extend_ids. apply ctx_id_left_is_id. constructor.
              + apply alpha_extend_ids. apply ctx_id_left_is_id. eapply @alpha_sym. constructor. eapply sconstr2_alpha_p. eauto.
          * apply nc_ftv_env with (x := x0) in H1. simpl in H1. simpl. intuition. unfold btv. left. reflexivity.
          * intros.
            intros Hcontra.
            simpl in H.
            destruct H; auto.
            rewrite <- H in *.
            
            apply nc_ftv_env with (x := x0) in H1.
            - simpl in H1.
              destruct H1.
              right.
              apply @alpha_preserves_ftv with (ren := nil) (x' := x0) (s' := p) in Hcontra.
              + auto with *.
              + eapply @alpha_sym. constructor. eapply sconstr2_alpha_p. eauto.
              + constructor.
            - simpl. intuition.
          * eapply sconstr2_nc_s_t. eauto.
          * eapply sconstr2_nc_s. eauto.
          * eapply sconstr2_nc_t. eauto.
          * eapply sconstr2_nc_sub; eauto.
        }
  - inversion H2; subst.
    
    
    specialize (IHHstep (gu_app_l H0) (nc_app_l H1) R H3 s3 H7 (nc_app_l H4)) as [sigS1 [HstepS1 HalphaS1] ].
    autorewrite with subs_db.

    inv HstepS1.

    remember (to_GU (tmapp s' (subs ((x, p)::nil) t))) as st_gu.
    
    destruct (to_GU_app_unfold Heqst_gu) as [sigS1Alpha [sigtalpha [ [Happ Ha_s] Ha_t ] ] ].

    (* like lam case, we then alpha step *)
    assert ({s''step & step_naive sigS1Alpha s''step * Alpha [] sigS1 s''step}%type).
    {
      eapply step_naive_preserves_alpha2 with (s := s') (t := sigS1); eauto.
      - eapply gu_app_l; eauto.
        rewrite Heqst_gu in Happ.
        rewrite <- Happ.
        eapply to_GU__GU.
    }
    destruct H8 as [s''step [Halpha_s'' Hstep_s'' ] ].

    exists (tmapp s''step sigtalpha).
    split.
    + econstructor; auto.
      * constructor.
        -- eapply @alpha_trans. constructor. eauto. eauto.
        -- eauto.
      * eauto. subst. rewrite <- Happ. apply to_GU__GU.
      * constructor. eauto.
    + eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R). 
      * eapply id_left_trans. 
      * apply alpha_extend_ids. apply ctx_id_left_is_id. constructor. eapply alpha_sym. constructor. eauto. eapply alpha_sym. constructor. eauto.
      * constructor. eauto. 
        repeat rewrite psubs_to_subs; try apply single_parseq.
        eapply subs_preserves_alpha_σ_R; eauto.
        -- exact (nc_app_r H1).
        -- exact (nc_app_r H4).
  - (* analogous*) admit.
  - inversion H2; subst.
    autorewrite with subs_db.
    specialize (IHHstep (gu_lam H0)).

    assert (HctxSub: αCtxSub ((x0, y)::R) ((x, p)::nil) ((x, p)::nil)).
    {
      apply alpha_ctx_ren_extend_fresh_ftv.
      - apply nc_ftv_env with (x := x0) in H1. auto. simpl. auto.
      - apply nc_ftv_env with (x := y) in H4. auto. simpl. auto.
      - assumption.
    }

    specialize (IHHstep (nc_lam H1) ((x0, y)::R) HctxSub s3 H9 (nc_lam H4)).
    destruct IHHstep as [subSigmaS2 [Hsteps1 Halpha] ].

    inversion Hsteps1; subst.

    (* Same term, but rename (possibly occuring) x binders to something else, 
        so that we get GU with the wrapping tmlam x still
      This should be seen as a composability argument. GU composes up to alpha
    *)
    remember (to_GU'' x0 s') as s''.

    (* alpha preserves step_naive, so that we can use this new s'' from above*)
    assert ({s''step & step_naive s'' s''step * Alpha [] subSigmaS2 s''step }%type).
    {
      eapply step_naive_preserves_alpha2 with (s := s'); eauto.
      - eapply gu_lam; eauto.
        subst.
        eapply to_GU''__GU_lam.
      - subst.
        eapply to_GU''__alpha.
    }
    destruct H7 as [s''step [Halpha_s'' Hstep_s'' ] ].
    exists (tmlam x0 A s''step).
    split.
    + apply step_gu_naive_intro with (s' := tmlam x0 A s''); auto. 
      * constructor.
        apply alpha_extend_ids. constructor. constructor.
        eapply @alpha_trans. constructor. eauto. eauto.
        subst. eapply to_GU''__alpha.
      * subst. eapply to_GU''__GU_lam.
      * constructor. assumption.
    + constructor.
      eapply @alpha_trans with (ren := ctx_id_left ((x0, y)::R)) (ren' := ((x0, y)::R)).
      * eapply id_left_trans.
      * apply alpha_extend_ids. apply ctx_id_left_is_id. eapply @alpha_sym. eauto. constructor. eauto.
      * assumption.
Admitted.

Create HintDb to_GU'_db.
Hint Resolve to_GU'__alpha to_GU'__GU to_GU'__NC : to_GU'_db.

Definition sub_gu (X : string) (T : term) (s : term) := sub X T (to_GU' X T s).

Lemma sn_subst X T s : NC s ((X, T)::nil) -> SN_na (sub X T s) -> SN_na s.
Proof with eauto with to_GU'_db.
  intros nc.
  assert (Alpha [] (sub X T s) (sub X T (to_GU' X T s))).
  {
    repeat rewrite <- single_subs_is_psub.
    eapply subs_preserves_alpha_σ_R; eauto.
    eapply to_GU'__NC.
    eapply to_GU'__alpha.
    constructor. constructor. constructor. apply alpha_refl. constructor.
  }
  (* intros.
  eapply α_preserves_SN_R with (R := nil) (s := (to_GU' X T s)).
  - eapply @alpha_sym; auto. constructor. apply to_GU'__alpha.
  -  *)
  intros.
    rewrite <- single_subs_is_psub in H0.
    eapply α_preserves_SN_R with (s := psubs ((X, T)::nil) s) (s' := psubs((X, T)::nil) (to_GU' X T s)) in H0.
    {
      rewrite single_subs_is_psub in H0.
      revert H0.
      
    apply (sn_preimage_α (h := sub_gu X T)) => x y. 
    intros.
    (* eapply (@step_gu_naive_preserves_alpha) with (R := nil) (t := to_GU' X T x) in H1... (* so that we already have a GU term*)
    destruct H1 as [t' [Hstep H_a] ]. *)
    (* to_GU' is created such that we have GU s and NC s ((X, T))*)
    repeat rewrite <- single_subs_is_sub.
    inversion H0; subst.
    eapply step_naive_preserves_alpha2 with (R := nil) (t:= y) (s' := to_GU' X T x) in H3; auto with α_eq_db.
    {
      destruct H3 as [t'' [Hstep_t'' Ha_t''] ].
      eapply @step_subst_single with (s := (to_GU' X T x)) (t := t''); eauto...
      - apply @alpha_trans with (t := y) (ren := nil) (ren' := nil); repeat constructor...
        eauto with α_eq_db.
      - eauto with α_eq_db.
    }
    - apply to_GU'__GU.
    - eapply @alpha_trans with (t := x); eauto with α_eq_db. apply to_GU'__alpha.
  }
  eapply subs_preserves_alpha_σ_R with (R := nil); eauto.
  - apply to_GU'__NC.
  - apply to_GU'__alpha.
  - constructor. constructor. constructor. apply alpha_refl. constructor.
Qed.

Definition cand := term -> Set.

Definition neutral (s : term) : bool :=
  match s with
    | tmlam _ _ _ => false
    | _ => true
  end.

Record reducible (P : cand) : Set := {
  p_sn : forall s, P s -> SN_na s;
  p_cl : forall s t, P s -> step_gu_naive s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step_gu_naive s t -> P t) -> P s
}.

(* Since we are only interested in globally unique alpha terms, we do an exists here.
But we should do a little study if that is necessary.

we want this to hold for [x := t] meaning substituteT:
Lemma beta_expansion A B x s t :p
  SN_na t -> L A ([x := t] s) ->
  L A (tmapp (tmlam x B s) t).

It also has to hold for A := Kind_Base, in which case it is proved by showing SN_na.
We only have that these two terms mean the same thing if we are allowed to forget about capture in the sbustitution
Hence only if t is globally unique with respect to s. We can enforce that by changing the definition of L.

JACCO and WOUTER think it is a bad idea to change the LR and that using L_preserves_alpha will allow us to use original LR.

*)
Fixpoint L (T : type) : cand :=
match T with
  | tp_base => SN_na 
  | tp_arrow A B => fun s => forall t, L A t -> L B (tmapp s t)
end.




Lemma α_preserves_L_R A s s' R :
  Alpha R s s' -> L A s -> L A s'.
Proof.
  intros.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent R.
  induction A; intros.
  - simpl. simpl in H0.
    eapply α_preserves_SN_R with (s := s); eauto.
  - simpl in H0.
    simpl.
    intros t' Ht.

    remember (sym_alpha_ctx R) as R'.
    assert (Alpha R' s' s).
    {
      subst.
      eauto with α_eq_db.
    }

    destruct (axiomatized_construction t' H1) as [t [R_ [Ha_t0 Ha_s] ] ].
    
    (* first arg of R_extender needs to live in the same alpha land as the last*)
    eapply (IHA2 (sym_alpha_ctx R_) _ (tmapp s t)).
    + eapply @alpha_sym. eapply sym_alpha_ctx_is_sym.
      constructor; eauto.
    + 
    eapply H0. eapply (IHA1 R_ t t'); eauto with α_eq_db.
Qed.

Lemma reducible_sn : reducible SN_na.
Proof. 
  constructor; eauto using ARS.sn. by move=> s t [f] /f. 
  intros s.  elim: s => //.
Qed.

Global Hint Resolve reducible_sn : core.

Lemma reducible_var P x : reducible P -> P (tmvar x).
Proof. move/p_nc. apply=> // t st.
  inv st. inv H. inv H1.
Qed.

Lemma L_reducible A :
  reducible (L A).
Proof with eauto using step_gu_naive.
  elim: A => /=[|A ih1 B ih2].
  - apply reducible_sn.
  - constructor.
    + move=> s h. apply: (@sn_closedL (tmvar "x")). apply: (p_sn (P := L B))...
      eapply h. eapply reducible_var; eauto.
    + intros. specialize (H t0 H1).
      eapply step_gu_naive_app_l with (s1 := s) (t1 := t) (s2 := t0) in H0. 
      * destruct H0 as [t1' [ Ha_t [s2' [Ha_s2' Hstep] ] ] ].
        eapply p_cl with (s := (tmapp s t0)) in H; auto.
        2: exact Hstep.
        eapply α_preserves_L_R.
        2: exact H.
        constructor; eapply alpha_sym; eauto; constructor.
    + move=> s ns h t la.
      have snt := p_sn ih1 la.
      elim: snt la => {} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      inv H.  inv H1=> //...
      * inv H5. discriminate ns.
      * assert (Hgn: step_gu_naive s s0).
        {
          apply gu_app_l in H0.
          econstructor; eauto.
        }
        specialize (h s0 Hgn).
        eapply α_preserves_L_R with (s' := t2) in la; eauto.
      * assert (step_gu_naive t t0).
        {
          apply gu_app_r in H0.
          econstructor; eauto.    
        }
        specialize (ih3 t0 H).
        apply (p_cl ih1 la) in H.
        specialize (ih3 H).
        eapply α_preserves_L_R; eauto.
        constructor; eauto. eapply alpha_refl. constructor.
Qed.

Corollary L_sn A s : L A s -> SN_na s.
Proof. intros Las. assert (reducible (L A)) by apply (L_reducible A).
   apply (p_sn H). assumption.
Qed.

Corollary L_cl T s t : L T s -> step_gu_naive s t -> L T t.
Proof.
  intros Hstep Hst.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_cl H Hstep); assumption.
Qed.

Corollary L_nc T s :
  neutral s -> (forall t, step_gu_naive s t -> L T t) -> L T s.
Proof. 
  intros Hneut Hstep.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_nc H); assumption.
Qed.

Corollary L_var T x : L T (tmvar x).
Proof.
  apply L_nc; first by []. intros t st. inversion st. subst.
  inversion H. subst. inversion H1.
Qed.

Corollary L_cl_star T s t :
  L T s -> red_gu_na s t -> L T t.
Proof.
  intros Ls red_st. induction red_st.
  - eapply IHred_st. eapply L_cl; eauto.
  - assumption.
Qed.

Definition EL (Gamma : list (string * type)) 
          (sigma : list (string * term)) : Set :=
  forall x T, lookup x Gamma = Some T ->
    { t & prod (lookup x sigma = Some t) (L T t)}.

(* is true! *)
Lemma extend_EL (Gamma : list (string * type)) (sigma : list (string * term)) x T t :
  EL Gamma sigma -> L T t -> EL ((x, T) :: Gamma) ((x, t) :: sigma).
Proof.
  intros.
  unfold EL.
  intros.
  destr_eqb_eq x0 x.
  - exists t.
    split.
    + simpl. rewrite String.eqb_refl. reflexivity.
    + simpl in H1. rewrite String.eqb_refl in H1. inversion H1. subst. assumption.
  - simpl in H1. rewrite <- String.eqb_neq in H2. rewrite String.eqb_sym in H2. rewrite H2 in H1.
    unfold EL in H.
    specialize (H x0 T0 H1).
    
    destruct H as [t' [H3 H4] ].
    exists t'.
    split.
    + simpl. rewrite H2. assumption.
    + assumption.
Qed.

Reserved Notation "Δ '|-*' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_type : list (string * type) -> term -> type -> Set :=
  | K_Var : forall Δ X K,
      List.lookup X Δ = Some K ->
      Δ |-* (tmvar X) : K
  | K_Lam : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-* T : K2 ->
      Δ |-* (tmlam X K1 T) : (tp_arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-* T1 : (tp_arrow K1 K2) ->
      Δ |-* T2 : K1 ->
      Δ |-* (tmapp T1 T2) : K2
where "Δ '|-*' T ':' K" := (has_type Δ T K).

(* NOTE: Proof already in alpha_typing*)
Lemma alpha_preserves_typing s t A Gamma :
  Alpha nil s t -> Gamma |-* s : A -> Gamma |-* t : A.
Admitted.

Lemma step_gu_na_lam_fold x A s s' :
  step_gu_naive s s' -> {lams' & step_gu_naive (tmlam x A s) lams' * Alpha [] lams' (tmlam x A s')}%type.
Proof.
  intros.
  assert (Alpha [] (tmlam x A s) (to_GU (tmlam x A s)) ).
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
    - rewrite <- H9 in H0. inversion H0; subst. eauto.
  } 
  (* sgu and slam are both GU, so we can do step preserves 2*)
  assert ({t' & step_naive s2 t' * Alpha [(x, y)] s' t'}%type).
  {
    eapply step_naive_preserves_alpha2.
    - exact H2.
    - assert (GU (to_GU (tmlam x A s))) by apply to_GU__GU.
      rewrite <- H9 in H5. auto.
      eapply gu_lam. eauto.
    - eauto.
    - auto.
  }
  destruct H5 as [t' [Hstep_t' Halpha_t'] ].
  exists (tmlam y A t').
  split.
  - eapply step_gu_naive_intro with (s' := tmlam y A s2); eauto.
    + rewrite <- H9 in H0. auto.
    + assert (GU (to_GU (tmlam x A s))) by apply to_GU__GU.
      rewrite <- H9 in H5. auto.
    + apply step_abs. auto.
  - eapply @alpha_sym. constructor. constructor. eauto.
Qed.

(* step_gu/red_gu always freshens binders, hence we need to work up to alpha*)
Lemma red_gu_na_lam_fold {x A s s'} :
  red_gu_na s s' -> {lams' & red_gu_na (tmlam x A s) lams' * Alpha [] lams' (tmlam x A s')}%type.
Proof.
  intros.
  induction H.
  - destruct IHred_gu_na as [lams' [Hred Halpha] ].

    apply (step_gu_na_lam_fold x A) in s0.
    destruct s0 as [lams'' [Hstep'' Halpha''] ].
    assert ({lams''' & red_gu_na lams'' lams''' * Alpha [] lams' lams'''}%type).
    {
      apply @red_gu_naive_preserves_alpha with (t := lams'') (s := tmlam x A t); eauto with α_eq_db.
    }
    destruct H0 as [lams''' [Hred' Halpha'] ].
    exists lams'''.
    split.
    + eapply red_gu_na_star.
      * exact Hstep''.
      * eauto.
    + eauto with α_eq_db.
  - exists (tmlam x A s).
    split.
    + apply red_gu_na_nil.
    + apply alpha_refl. constructor.
Qed.


Lemma red_gu_na_app_fold {s1 s2 t1 t2} :
  red_gu_na s1 s2 -> red_gu_na t1 t2 -> {app & red_gu_na (tmapp s1 t1) app * Alpha [] app (tmapp s2 t2)}%type.
Proof.
  intros.
Admitted.


Lemma red_beta x s t1 t2 : 
  step_gu_naive t1 t2 ->
  NC s ((x, t1)::nil) ->
  NC s ((x, t2)::nil) -> (* step does not introduce new free vars, so should be true!*)
  { a & prod 
    ( red_gu_na (sub x t1 s) a) 
    ( nil ⊢ a ~ sub x t2 s) }. 
Proof with eauto with α_eq_db. 
  intros Hstep.
  induction s.
  - intros.
    destr_eqb_eq x s.
    + simpl.
      rewrite String.eqb_refl.
      exists t2.
      split...
      apply red_gu_na_star with (t := t2); auto.
      apply red_gu_na_nil.
    + simpl.
      rewrite <- String.eqb_neq in H1.
      rewrite H1.
      exists (tmvar s).
      split...
      apply red_gu_na_nil.
  - intros.
    simpl.
    assert (x <> s).
    {
      intros contra.
      subst.
      eapply nc_ftv_env with (x := s) in H.
      + unfold ftv_keys_env in H.
        contradiction H.
        apply in_eq.
      + simpl. apply in_eq.
    }
    specialize (IHs (nc_lam H) (nc_lam H0)) as [a [Hred_a Ha_a] ].
    assert ({a0 : term &
  (red_gu_na (tmlam s t (sub x t1 s0)) a0 *
  (nil ⊢ a0 ~ tmlam s t a))%type}).
  {
    apply (red_gu_na_lam_fold Hred_a).
  }
    destruct H2 as [a0 [Hred_a0 Ha_a0] ].
    exists a0.
    split.
    + assumption.
    + eapply alpha_trans.
      * constructor.
      * eauto.
      * constructor. eapply alpha_extend_id'; auto. constructor. (* TODO: make that a lemma*)
  - intros.
    specialize (IHs1 (nc_app_l H) (nc_app_l H0)) as [g1 [Hred_g1 Ha_g1] ].
    specialize (IHs2 (nc_app_r H) (nc_app_r H0)) as [g2 [Hred_g2 Ha_g2] ].
    repeat rewrite <- single_subs_is_sub.
    repeat rewrite <- single_subs_is_sub in *.
    autorewrite with subs_db.
    repeat rewrite single_subs_is_sub.
    repeat rewrite single_subs_is_sub in *.
    
    assert ({a : term &
    (red_gu_na
      (tmapp (sub x t1 s1) (sub x t1 s2)) a *
    (nil ⊢ a ~
    tmapp g1 g2))%type}) as [app [Hred Ha] ] by apply (red_gu_na_app_fold Hred_g1 Hred_g2).
    exists app.
    split; auto.
    eapply alpha_trans; eauto with α_eq_db.
Qed.

(* Closure under beta expansion. *)
Lemma beta_expansion' A B x y s s' t :
  Alpha [(y, x)] s' s -> (* this allows us to not have to "rename free vars in t" manually*)
  GU s ->
  NC s [(x, t)] -> (* this really is the right assumption. no free variable in t is a binder in s', because these binders could be added to the environment through beta reduction and then capture*)
  SN_na t -> L A (sub x t s) ->
  L A (tmapp (tmlam y B s') t).
Proof with eauto with α_eq_db gu_nc_db.
  move=> Ha_s' gu nc snt h. have sns := sn_subst nc (L_sn h).
  assert (SN_na s').
  {
    (* eapply alpha_sym in Ha_s'. *)
    eapply α_preserves_SN_R with (s := s)...
  }
  clear sns.
  generalize dependent s.
  generalize dependent t.
  induction H.
  intros t snt s0 Ha Hnc.

  (* Now create IH for other step *)
  revert Hnc.
  revert snt.
  elim=> {}.
  intros.
  rename H0 into H10.

  apply: L_nc => // u st. 
  inversion st; subst. inv H0. inversion H6; subst. 

  inv H2 => //.
  - eapply α_preserves_L_R with (R := (nil)); eauto.
    rewrite <- single_subs_is_sub.
    eapply alpha_rename_binder_stronger...
    + constructor. constructor.
     
  - inv H5.
    assert (Alpha [(y, y0)] (to_GU x0) s4).
    {
      eapply @alpha_trans with (ren := (y, y)::nil) (t := x0).
      - eauto with α_eq_db.
      - apply alpha_extend_ids. constructor. constructor. eapply @alpha_sym; eauto. constructor. apply to_GU__alpha.
      - assumption.
    }
    assert ({s5' & step_naive (to_GU x0) s5' * Alpha [(y0, y)] s5 s5'}%type).
    {

      eapply step_naive_preserves_alpha2 with (s := s4) (t:=s5) (s' := (to_GU x0)).
      - eauto with gu_nc_db.
      - apply to_GU__GU.
      - eauto with α_eq_db.
      - assumption.
    }
    destruct H2 as [s5' [Hstep_na_s5' Ha_s5'] ].
    assert (Hstep_s5': step_gu_naive x0 s5').
    {
      apply step_gu_naive_intro with (s' := to_GU x0).
      - eapply to_GU__alpha.
      - eapply to_GU__GU.
      - assumption.
    }

    eapply α_preserves_L_R with (s := tmapp (tmlam y B s5') x1) (R := nil)...
    specialize (H s5' Hstep_s5' x1).
    clear Ha_s5'. clear H7. clear st. clear s5.
    inv Hstep_s5'.
    assert (HSN_x1: SN_na x1) by now constructor.

    (* TODO: instead of to_GU, assume gu of s0 here by NC?*)
    assert ({s'_a &  step_naive s0 s'_a * Alpha [(y, x)] s5' s'_a}%type).
    {
      eapply step_naive_preserves_alpha2 with (s := s') (s' := s0) (t := s5')...
      eapply @alpha_trans with (ren := (y, y)::nil) (ren' := (y, x)::nil) (t := x0)...
    }
    destruct H5 as [s'_a [ Hstep_s'_a Ha_s'_a ] ].
    specialize (H HSN_x1 (to_GU' x x1 s'_a)). (* just renaming binders*)
    remember (to_GU' x x1 s'_a) as s'_a1.
    assert (((y, x)::nil) ⊢ s5' ~ s'_a1).
    {
      eapply @alpha_trans with (ren := ((y, x)::nil)) (ren' := ctx_id_right ((y, x)::nil)) (t := s'_a)...
      eapply alpha_extend_ids. constructor. constructor. subst. eapply to_GU'__alpha.
    }

    eapply H; eauto.

    * subst. eapply to_GU'__GU. 
    * subst. eapply to_GU'__NC.
    * 
    assert ({α & (step_gu_naive (sub x x1 s0) α) * (nil ⊢ α ~ sub x x1 s'_a1)}%type) 
      as [alpha [Hred Halpha] ].
      {
        repeat rewrite <- single_subs_is_sub.
        eapply (@step_subst_single)...
        subst. eapply to_GU'__alpha.
        subst. eapply to_GU'__NC.
      }
    eapply α_preserves_L_R with (s := alpha) (R := nil); auto.
    eapply L_cl with (s := (sub x x1 s0)); auto.

  - eapply α_preserves_L_R with (s := (tmapp (tmlam y B x0) t0)) (R := nil)...
    eapply H10.
    + econstructor...
    + assumption.
    + eapply step_naive_pererves_nc_ctx with (s := s0); eauto.
      eapply alpha_preserves_nc_ctx; eauto.
    +  
      assert ({ a & prod 
    ( red_gu_na (sub x x1 s0) a) 
    ( nil ⊢ a ~ sub x t0 s0) }).
      { (* this has a lot of repetition with the above *)
        apply red_beta...
        - econstructor...
        - eapply step_naive_pererves_nc_ctx with (s := s0); eauto.
          eapply alpha_preserves_nc_ctx; eauto.
      }
      destruct H0 as [a [Hred_a Ha_a] ].
      eapply (L_cl_star) in h.
      * eapply α_preserves_L_R with (R := nil); eauto.
      * assumption.
Qed.

Lemma beta_expansion_subst X t sigma s A B :
  NC (subs sigma s) [(X, t)] -> (* so the substitution makes sense after "breaking"  it open*)
  SN_na t -> L A (subs ((X, t)::sigma) s) -> L A (tmapp (subs sigma (tmlam X B s)) t).
Proof.
  intros nc snt H.
  simpl in H.
  autorewrite with subs_db.
  eapply α_preserves_L_R with (R := nil) (s := (tmapp (tmlam X B (to_GU' X t (subs sigma s))) t)).
  - constructor. constructor. apply alpha_extend_ids. constructor. constructor. 
    eapply @alpha_sym. eauto. constructor. apply to_GU'__alpha. eapply alpha_refl. constructor.
  - eapply α_preserves_L_R with (R := nil) (s' := (sub X t (to_GU' X t (subs sigma s)))) in H.
    + 
      eapply beta_expansion' in H; eauto.
      * apply alpha_extend_ids. constructor. constructor. apply alpha_refl. constructor.
      * eapply to_GU'__GU.
      * eapply to_GU'__NC.
    + repeat rewrite <- single_subs_is_psub.
      eapply subs_preserves_alpha_σ_R; auto.
      * eapply to_GU'__NC.
      * eapply to_GU'__alpha.
      * apply alpha_ctx_ren_nil.
Qed.







(* The fundamental theorem. *)
Theorem soundness Gamma s A :
  has_type Gamma s A -> 
  GU s -> (* So that we know GU_vars (tmlam x A s) -> ~ In x (btv s), and btv s ∩ ftv s = ∅, important for dealing with vars in `t` that roll out of LR*)
  forall sigma, 
    Uhm sigma s ->
    NC s sigma -> (* so we get "nice" substitutions *)
    ParSeq sigma -> (* So parallel and sequential substitions are identical *)
    EL Gamma sigma -> (* So that terms in a substitution are already L *)
  L A (subs sigma s).
Proof with eauto using L_sn. 
  elim=> {Gamma s A} [Gamma X A ih gu sigma wierd nc blabla HEL |Gamma X A s B _ ih gu sigma wierd nc blabla EL|Gamma s t A B _ ih1 _ ih2 gu sigma wierd nc blabla HEL].
  - rewrite psubs_to_subs; eauto.
    unfold EL in HEL.
    specialize (HEL X A ih).
    destruct HEL as [t [HlookupSigma LAt] ].
    simpl.
    rewrite HlookupSigma.
    assumption.
  - unfold L. fold L.
    intros.

    remember (t_constr t s sigma X) as t'R.
    destruct t'R as [t' R].

    assert (Huhm: Uhm ((X, t')::sigma) s).
    {
      eapply Uhm_lam; eauto.
      - intros. eapply t_constr__uhm1 in Heqt'R; eauto.
      - intros. eapply t_constr__uhm2; eauto. 
      - intros. eapply t_constr__uhm3; eauto. 
    }
    assert (HX: ~ In X (btv s)).
    {
      intros contra.
      inversion gu; subst.
      contradiction.
    }

    specialize (ih (gu_lam gu) ((X, t')::sigma) Huhm (t_constr__nc_s HX (nc_lam nc) Heqt'R)).
    assert (Hparseq: ParSeq ((X, t')::sigma)).
    {
      (* we now need: X not a binder in sigma. *)
      constructor. auto.
      apply nc_ftv_env with (x := X) in nc.
      assumption.
      apply btv_lam.
      unfold Uhm in wierd. destruct wierd as [ [uhm1 _] _].
      intros Hcontra.
      apply uhm1 in Hcontra; auto.
      simpl in Hcontra.
      intuition.
    }

    specialize (ih Hparseq (extend_EL EL (α_preserves_L_R (t_constr__a_t Heqt'R) H))).
(* **** ih is now fully applied ********************** *)

    eapply beta_expansion_subst in ih; eauto.
    + eapply α_preserves_L_R with (s' := tmapp (subs sigma (tmlam X A s)) t) (R := sym_alpha_ctx R) in ih; eauto. constructor.
      * eapply @alpha_sym with (ren := R). apply sym_alpha_ctx_is_sym.
        repeat rewrite psubs_to_subs; auto.
        eapply subs_preserves_alpha_σ_R; eauto; [|apply (t_constr__a_sigma Heqt'R)].
        constructor. eapply alpha_extend_id''. auto; apply (t_constr__a_s (gu_lam gu) (uhm_smaller Huhm) Heqt'R).
      * eapply @alpha_sym; eauto. apply sym_alpha_ctx_is_sym.   
        apply (t_constr__a_t Heqt'R).
    + eapply t_constr__nc_subs; eauto.
      unfold Uhm in wierd. destruct wierd as [ [uhm1 _] _].
      intros Hcontra.
      apply uhm1 in Hcontra; auto.
      simpl in Hcontra.
      intuition.
    + eapply α_preserves_SN_R; eauto. 
      * eapply t_constr__a_t; eauto. 
      * eapply L_sn; eauto.
  - 
    specialize (ih1 (gu_app_l gu) sigma).

    specialize (ih1 (Uhm_appl wierd) (nc_app_l nc) blabla HEL).
    specialize (ih2 (gu_app_r gu) _ (Uhm_appr wierd) (nc_app_r nc) blabla HEL).
    autorewrite with subs_db.
    unfold L in ih1. fold L in ih1.
    specialize (ih1 (subs sigma t) ih2).
    assumption.
Qed.


(* Identity substitutions: Given a typing context E, give a list of term substitutions matching this E*)
Fixpoint id_subst (E : list (string * type)) : list (string * term) :=
  match E with
  | nil => nil
  | cons (x, A) E' => cons (x, tmvar x) (id_subst E')
  end.

From PlutusCert Require Import alpha_sub.

Lemma id_subst_is_IdSubst E :
  IdSubst (id_subst E).
Proof.
  induction E.
  - constructor.
  - simpl. destruct a. constructor. assumption.
Qed.

Lemma id_subst__id s σ :
  (* NC s σ ->  *)
  IdSubst σ -> 
  subs σ s = s. (* even when this capturs, it doesnt matter, since it captures something and then substiutes it for the same name*)
Proof.
  intros.
  induction s.
  - (* if s in sigma, then it is mapped to s by IdSubst*)
    admit.
  - autorewrite with subs_db.
    f_equal.
    apply IHs.
  - autorewrite with subs_db.
    f_equal; eauto.
Admitted.

(* The identity substitution is in the EL relation *)
Lemma id_subst__EL E :
  EL E (id_subst E).
Proof.
Admitted.

Lemma id_subst__ParSeq :
  forall (σ : list (string * term)), IdSubst σ -> ParSeq σ.
Admitted.

Lemma id_subst__nc_uhm E s :
  NC s (id_subst E) -> Uhm (id_subst E) s.
Admitted.

(* The fundamental theorem for named variables. *)
Corollary type_L (E : list (string * type)) s T : has_type E s T -> L T (subs (id_subst E) s).
Proof.
  intros Htype.
  assert (HEL: EL E (id_subst E)) by apply id_subst__EL.
  remember (s_constr s (id_subst E)) as s'.
  eapply alpha_preserves_typing with (t := s') in Htype; eauto.
  eapply soundness in Htype; eauto.
  - rewrite id_subst__id in Htype; [|apply id_subst_is_IdSubst]. 
    rewrite id_subst__id; [|apply id_subst_is_IdSubst].
    eapply α_preserves_L_R with (s := s'); eauto.
    eapply alpha_sym. eapply alpha_sym_nil. eapply s_constr__a_s; eauto.
  - eapply s_constr__gu; eauto.
  - apply id_subst__nc_uhm. eapply s_constr__nc_s; eauto.
  - eapply s_constr__nc_s; eauto.
  - apply id_subst__ParSeq. apply id_subst_is_IdSubst.
  - eapply s_constr__a_s; eauto.
Qed.



Theorem SN_naive E s T : has_type E s T -> SN_na s.
  intros.
  eapply type_L in H.
  rewrite id_subst__id in H; [|apply id_subst_is_IdSubst].
  eapply L_sn; eauto.
Qed.