From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List Util.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import alpha_vacuous construct_GU_R alpha_sub psubs step_gu alpha_typing STLC STLC_Kinding SN_STLC_GU.GU_NC_BU SN_STLC_GU.construct_GU.
From PlutusCert Require Import IdSubst step_naive alpha.alpha alpha_rename rename util alpha_ctx_sub variables alpha_freshness.

(* used to be prop (TODO: Defined also in SN_STCL_named )*)
Inductive sn {X : Type} {e : X -> X -> Type } x : Type :=
| SNI : (forall y, e x y -> sn y) -> sn x.

Notation SN_gu := (@sn term step_gu).

Theorem α_preserves_SN_R s s' R :
  Alpha R s s' -> SN_gu s -> SN_gu s'.
Proof.
  intros Hα Hsn.
  revert s' R Hα.
  induction Hsn. intros s' R Hα.
  apply SNI.
  intros y1 Hstep.
  eapply alpha_sym in Hα; eauto with α_eq_db.
  apply (step_gu_preserves_alpha Hα) in Hstep as [y1_α [Hstep' Hα']].
  eapply X; eauto with α_eq_db.
Qed.

Lemma sn_preimage_α' (h : term -> term) x v :
  (forall x y, step_gu x y -> {y_h & prod (step_gu (h x) y_h) (nil ⊢ y_h ~ (h y))}) -> @sn term step_gu v -> nil ⊢ v ~ h x -> @sn term step_gu x.
Proof.
  intros A B Halpha.
  generalize dependent h.
  generalize dependent x.
  induction B.
  intros x0 h A Ha.
  apply: SNI => y C.
  apply A in C as [yh [ehy yh_alpha] ].
  eapply (step_gu_preserves_alpha) in ehy as [yh' [ehy' yh_alpha']]; eauto with α_eq_db.
Qed.

Lemma sn_preimage_α (h : term -> term) x :
  (forall x y, step_gu x y -> {y_h & prod (step_gu (h x) y_h) (nil ⊢ y_h ~ (h y))}) -> @sn term step_gu (h x) -> @sn term step_gu x.
Proof.
  intros.
  eapply sn_preimage_α'; eauto with α_eq_db.
Qed.

Create HintDb to_GU'_db.
Hint Resolve to_GU'__alpha to_GU'__GU to_GU'__NC : to_GU'_db.

Create HintDb to_GU_db.
Hint Resolve to_GU__alpha to_GU__GU : to_GU_db.

(* This would NOT work for app because of beta reduction*)
Lemma sn_ty_fun {B s t} : B <> App -> SN_gu s -> SN_gu t -> SN_gu (@tmbin B s t).
Proof.
  intros HnotApp HSN_s HSN_t.
  generalize dependent t.
  induction HSN_s.

  (* now the other IH *)
  intros t.
  elim=> {}. intros.

  apply: SNI => y H.
  inversion H; subst.
  inversion H0; subst.
  inversion H2; subst.
  - (* B not App : contradiction *)
    contradiction.
  - eapply step_naive_preserves_alpha2 with (s' := to_GU x) (R := nil) in H7 as [C [Hstep_C Ha_C] ]; eauto with gu_nc_db α_eq_db to_GU_db.
    eapply α_preserves_SN_R with (R := []) (s := @tmbin B C t2); eauto with α_eq_db.
    eapply X with (y := C).
    + apply step_gu_intro with (s' := to_GU x); eauto with gu_nc_db α_eq_db to_GU_db.
    + eapply α_preserves_SN_R with (s := x0). eauto. constructor. auto.
  - eapply step_naive_preserves_alpha2 with (s' := to_GU x0) (R := nil) in H7 as [C [Hstep_C Ha_C] ]; eauto with gu_nc_db α_eq_db to_GU_db.
    eapply α_preserves_SN_R with (R := []) (s := @tmbin B x C); eauto with α_eq_db.
    eapply X0 with (y := C).
    apply step_gu_intro with (s' := to_GU x0); eauto with to_GU_db.
Qed.

Lemma sn_ty_forall {B X K T} : SN_gu T -> SN_gu (@tmabs B X K T).
Proof.
  intros HSN_T.
  induction HSN_T.
  apply SNI.
  intros y Hstep.
  inversion Hstep; subst.
  inversion H; subst.
  inversion H1; subst.

  eapply step_naive_preserves_alpha2 with (s' := to_GU x) (R := ((y0, X)::nil)) in H7 as [C [Hstep_C Hα_C] ].
  - 
    assert (Alpha [] (@tmabs B y0 K s0) (@tmabs B X K C) * step_gu x C)%type as [Hα Hstep_BForall].
    {
      split.
      - constructor; eauto.
      - apply step_gu_intro with (s' := to_GU x); eauto.
        + eapply to_GU__alpha.
        + eapply to_GU__GU.
    }
    eapply α_preserves_SN_R with (R := []) (s := @tmabs B X K C) in X0; eauto.
    eauto with α_eq_db.
  
  - eapply gu_lam. eauto.
  - eapply to_GU__GU.
  - eapply @alpha_trans with (t := x).
    + repeat constructor.
    + eauto with α_eq_db.
    + eapply alpha_extend_ids. constructor. constructor. apply to_GU__alpha.
Qed.

Lemma sn_closedL {B} t s : SN_gu (@tmbin B s t) -> SN_gu s.
Proof.
  apply: (sn_preimage_α (h := tmbin^~t)) => x y H.
  eapply (@step_gu_app_l B) in H as [t1' [Ha_t1' [s2' [Ha_t Hstep] ] ] ].
  eexists; eauto with *.
Qed.

(* s -> t   ==>  [p/x] s -> [p/x] t*)
Lemma step_subst_single R {x p s t t' } :
  step_naive s t -> 
  GU s ->  (*  We could return them, but we don't want to. Current idea: have GU in NC *)
  NC s [(x, p)] -> (* no free vars in sigma are binders in s'*)
  Alpha R t t' -> 
  αCtxSub R [(x, p)] [(x, p)] -> 
  (* GU t' -> *)
  NC t' [(x, p)] ->
  {aT : term & 
  (step_gu (psubs ((x, p)::nil) s) aT) * (Alpha R aT (psubs ((x, p)::nil) t'))}%type.
Proof with eauto with sconstr2_db.
  intros. rename H into Hstep. generalize dependent t'. generalize dependent R. induction Hstep; intros.
  - 
    (* The difficult case. The whole reason we need to do global uniqueness every step
      *)
      

      assert ({x' : string & {s' & { t' & ((to_GU (@tmbin App (@tmabs Lam x0 A (psubs [(x, p)] s))
  (psubs [(x, p)] t))) = @tmbin App (@tmabs Lam x' A s') t') * Alpha ((x0, x')::nil) (psubs [(x, p)] s) s' * Alpha [] (psubs [(x, p)] t) t'} } }%type).
      {
        eapply to_GU_applam_unfold. auto.
      }
      destruct H as [x0' [sub_s [ sub_t [ [pr_eq Ha_subs] Ha_subt]]]].
      
      exists (sub x0' sub_t sub_s).
      split.
      + eapply step_gu_intro with (s' := (tmbin (tmabs x0' A sub_s) sub_t)).
        * constructor. constructor. auto. auto.
        * rewrite <- pr_eq. apply to_GU__GU.
        * apply step_beta.
      + (* Invert some stuff to end up with a single sub 
          We need to freshen s t and p to be able to use commute subst
        *)
        remember (sconstr2 x0 t x p s ) as sconstr2_.
        destruct sconstr2_ as [ [s' t'0] p'].

        eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R) 
            (t := sub x0 (psubs ((x, p')::nil) t'0) (psubs ((x, p')::nil) s')).
        * eapply id_left_trans.
        * eapply alpha_extend_ids.
          eapply ctx_id_left_is_id.

          eapply alpha_rename_binder_stronger with (Rs := ((x0', x0)::nil)).
          -- eapply @alpha_trans with (t := psubs ((x, p)::nil) s) (ren := ((x0', x0)::nil)).
            ++ eapply id_right_trans.
            ++ eauto with α_eq_db.
            ++ eapply alpha_extend_ids. constructor. constructor.
               repeat rewrite psubs_to_subs; try apply single_parseq.
               eapply psubs__α.
               ** apply (nc_lam (nc_app_l H1)).
               ** eapply sconstr2_nc_s. eauto.
               ** eapply sconstr2_alpha_s. eauto.
               ** constructor. constructor. constructor. eapply sconstr2_alpha_p. eauto.            
          -- eapply @alpha_trans with (t := psubs ((x, p)::nil) t).
              ++ constructor.
              ++ eauto with α_eq_db.
              ++ repeat rewrite psubs_to_subs; try apply single_parseq.
                 eapply psubs__α.
                 ** apply (nc_app_r H1).
                 ** eapply sconstr2_nc_t. eauto.
                 ** eapply sconstr2_alpha_t. eauto.
                 ** constructor. constructor. constructor. eapply sconstr2_alpha_p. eauto.
          -- constructor.
          -- eapply gu_applam_to_nc. rewrite <- pr_eq. apply to_GU__GU.
          -- repeat rewrite psubs_to_subs; try apply single_parseq.
             eapply sconstr2_nc_sub; eauto.
        * 
        repeat rewrite psubs_to_subs; try apply single_parseq.
        {
          eapply commute_sub_naive; eauto.
          * eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R) (t := sub x0 t s).
            - eapply id_left_trans.
            - eapply alpha_extend_ids.
              eapply ctx_id_left_is_id.
              repeat rewrite <- single_subs_is_psub.
              eapply psubs__α with (R := nil).
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
    
    
    specialize (IHHstep (gu_app_l H0) (nc_app_l H1) R H3 s3 H9 (nc_app_l H4)) as [sigS1 [HstepS1 HalphaS1] ].

    inv HstepS1.

    remember (to_GU (@tmbin B s' (psubs ((x, p)::nil) t))) as st_gu.
    
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
    destruct H7 as [s''step [Halpha_s'' Hstep_s'' ] ].

    exists (@tmbin B s''step sigtalpha).
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
      * 
        constructor. eauto. 
        repeat rewrite psubs_to_subs; try apply single_parseq.
        eapply psubs__α; eauto.
        -- exact (nc_app_r H1).
        -- exact (nc_app_r H4).
  - (* TODO: cleanup, because this is completely analogous to case above*) 
    inversion H2; subst.
    specialize (IHHstep (gu_app_r H0) (nc_app_r H1) R H3 t3 H10 (nc_app_r H4)) as [sigS1 [HstepS1 HalphaS1] ].
    repeat rewrite subs_tmbin.
    inv HstepS1.

    remember (to_GU (@tmbin B s' (psubs ((x, p)::nil) s))) as st_gu.
    
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
    destruct H7 as [s''step [Halpha_s'' Hstep_s'' ] ].

    exists (@tmbin B sigtalpha s''step).
    split.
    + econstructor; auto.
      * constructor.
        -- eauto.
        -- eapply @alpha_trans. constructor. eauto. eauto.
        
      * apply gu_app_st__gu_app_ts. rewrite <- Happ. rewrite Heqst_gu. apply to_GU__GU.
      * constructor. eauto.
    + eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R) (t := tmbin (psubs ((x, p)::nil) s) (sigS1)). 
      * eapply id_left_trans. 
      * apply alpha_extend_ids. apply ctx_id_left_is_id. constructor. eapply alpha_sym. constructor. eauto. eapply alpha_sym. constructor. eauto.
      * constructor; eauto. 
        repeat rewrite psubs_to_subs; try apply single_parseq.
        eapply psubs__α; eauto.
        -- exact (nc_app_l H1).
        -- exact (nc_app_l H4).
  - inversion H2; subst.
    specialize (IHHstep (gu_lam H0)).

    assert (HctxSub: αCtxSub ((x0, y)::R) ((x, p)::nil) ((x, p)::nil)).
    {
      apply alpha_ctx_ren_extend_fresh_ftv.
      - apply nc_ftv_env with (x := x0) in H1. auto. simpl. auto.
      - apply nc_ftv_env with (x := y) in H4. auto. simpl. auto.
      - assumption.
    }

    specialize (IHHstep (nc_lam H1) ((x0, y)::R) HctxSub s3 H10 (nc_lam H4)).
    destruct IHHstep as [subSigmaS2 [Hsteps1 Halpha] ].

    inversion Hsteps1; subst.

    (* Same term, but rename (possibly occuring) x binders to something else, 
        so that we get GU with the wrapping tmabs x still
      This should be seen as a composability argument. GU composes up to alpha
    *)
    remember (to_GU'' x0 s') as s''.

    (* alpha preserves step_naive, so that we can use this new s'' from above*)
    assert ({s''step & step_naive s'' s''step * Alpha [] subSigmaS2 s''step }%type).
    {
      eapply step_naive_preserves_alpha2 with (s := s'); eauto.
      - apply @gu_lam with (B := B) (x := x0) (A := A); eauto.
        subst.
        eapply to_GU''__GU_lam.
      - subst.
        eapply to_GU''__alpha.
    }
    destruct H7 as [s''step [Halpha_s'' Hstep_s'' ] ].
    exists (@tmabs B x0 A s''step).
    split.
    + apply step_gu_intro with (s' := @tmabs B x0 A s''); auto. 
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
Qed.

Definition sub_gu (X : string) (T : term) (s : term) := sub X T (to_GU' X T s).

Lemma sn_subst X T s : NC s ((X, T)::nil) -> SN_gu (sub X T s) -> SN_gu s.
Proof with eauto with to_GU'_db.
  intros nc.
  assert (Alpha [] (sub X T s) (sub X T (to_GU' X T s))).
  {
    repeat rewrite <- single_subs_is_psub.
    eapply psubs__α; eauto.
    eapply to_GU'__NC.
    eapply to_GU'__alpha.
    constructor. constructor. constructor. apply alpha_refl. constructor.
  }
  (* intros.
  eapply α_preserves_SN_R with (R := nil) (s := (to_GU' X T s)).
  - eapply @alpha_sym; auto. constructor. apply to_GU'__alpha.
  -  *)
  intros.
    rewrite <- single_subs_is_psub in X0.
    eapply α_preserves_SN_R with (s := psubs ((X, T)::nil) s) (s' := psubs((X, T)::nil) (to_GU' X T s)) in X0.
    {
      rewrite single_subs_is_psub in X0.
      revert X0.
      
    apply (sn_preimage_α (h := sub_gu X T)) => x y. 
    intros.
    (* eapply (@step_gu_preserves_alpha) with (R := nil) (t := to_GU' X T x) in H1... (* so that we already have a GU term*)
    destruct H1 as [t' [Hstep H_a] ]. *)
    (* to_GU' is created such that we have GU s and NC s ((X, T))*)
    unfold sub_gu.
    repeat rewrite <- single_subs_is_psub.
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
  eapply psubs__α with (R := nil); eauto.
  - apply to_GU'__NC.
  - apply to_GU'__alpha.
  - constructor. constructor. constructor. apply alpha_refl. constructor.
Qed.

Definition cand := term -> Type.

(* TODO: This is different then neutral_Ty*)
Definition neutral (s : term) : bool :=
  match s with
    | tmabs _ _ _ => false
    | _ => true
  end.

Record reducible (P : cand) : Type := {
  p_sn : forall s, P s -> SN_gu s;
  p_cl : forall s t, P s -> step_gu s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step_gu s t -> P t) -> P s
}.

Fixpoint L (T : PlutusIR.kind) : cand :=
match T with
  | PlutusIR.Kind_Base => SN_gu 
  | PlutusIR.Kind_Arrow A B => fun s => forall t, L A t -> L B (@tmbin App s t)
end.

Create HintDb a_constr_db.
Hint Resolve a_constr__s_alpha a_constr__t_alpha : a_constr_db.

Lemma α_preserves_L_R A s s' R :
  Alpha R s s' -> L A s -> L A s'.
Proof with eauto with α_eq_db a_constr_db.
  intros.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent R.
  induction A.
  all: intros. simpl. simpl in *.
  - eapply α_preserves_SN_R with (s := s); eauto.
  - intros t' Ht.
  
    remember (@a_constr (sym_alpha_ctx R) s' s t') as Rt.
    destruct Rt as [R_ t].
    
    eapply (IHA2 (sym_alpha_ctx R_) _ (tmbin s t)).
    + eapply @alpha_sym. eapply sym_alpha_ctx_is_sym.
      constructor; eauto...
    + eapply X. eapply (IHA1 R_ t t'); eauto...
Qed.

Lemma reducible_sn : reducible SN_gu.
Proof. 
  constructor; eauto. by move=> s t [f] /f. 
  intros s.  elim: s => //.
Qed.

Global Hint Resolve reducible_sn : core.

Lemma reducible_var P x : reducible P -> P (tmvar x).
Proof. move/p_nc. apply=> // t st.
  inv st. inv H. inv H1.
Qed.

Lemma SN_var x : SN_gu (tmvar x).
Proof. 
  econstructor.
  intros.
  inversion H; subst.
  inversion H0; subst.
  inversion H2; subst.
Qed.

Lemma L_reducible A :
  reducible (L A).
Proof with eauto using step_gu.
  elim: A => /=[|A ih1 B ih2].
  - apply reducible_sn.
  - constructor.
    + move=> s h.
     apply: (@sn_closedL App (tmvar "x")). apply: (p_sn (P := L B))...
      eapply h. eapply reducible_var; eauto.
    + intros. specialize (X t0 X0).
      eapply step_gu_app_l with (s1 := s) (t1 := t) (s2 := t0) in H. 
      * destruct H as [t1' [ Ha_t [s2' [Ha_s2' Hstep] ] ] ].
        eapply p_cl with (s := (tmbin s t0)) in X; auto.
        2: exact Hstep.
        eapply α_preserves_L_R.
        2: eauto.
        constructor; eapply alpha_sym; eauto; constructor.
    + move=> s ns h t la.
      have snt := p_sn ih1 la.
      elim: snt la => {} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      inv H.  inv H1=> //...
      * inv H7. discriminate ns.
      * assert (Hgn: step_gu s s0).
        {
          apply gu_app_l in H0.
          econstructor; eauto.
        }
        eapply α_preserves_L_R with (s' := t2) in la; eauto.
      * assert (step_gu t t0).
        {
          apply gu_app_r in H0.
          econstructor; eauto.    
        }
        specialize (ih3 t0 H).
        eapply α_preserves_L_R; eauto.
        constructor; eauto. eapply alpha_refl. constructor.
        eapply p_cl in H; eauto.
Qed.

Corollary L_sn A s : L A s -> SN_gu s.
Proof. intros Las. assert (reducible (L A)) by apply (L_reducible A).
   apply (p_sn X). assumption.
Qed.

Corollary L_cl T s t : L T s -> step_gu s t -> L T t.
Proof.
  intros Hstep Hst.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_cl H Hstep); assumption.
Qed.

Corollary L_nc T s :
  neutral s -> (forall t, step_gu s t -> L T t) -> L T s.
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

Definition EL (Gamma : list (string * PlutusIR.kind)) 
          (sigma : list (string * term)) : Type :=
  forall x T, lookup x Gamma = Some T ->
    { t & prod (lookup x sigma = Some t) (L T t)}.

Lemma extend_EL (Gamma : list (string * PlutusIR.kind)) (sigma : list (string * term)) x T t :
  EL Gamma sigma -> L T t -> EL ((x, T) :: Gamma) ((x, t) :: sigma).
Proof.
  intros.
  unfold EL.
  intros.
  destr_eqb_eq x0 x.
  - exists t.
    split.
    + simpl. rewrite String.eqb_refl. reflexivity.
    + simpl in H. rewrite String.eqb_refl in H. inversion H. subst. assumption.
  - simpl in H. rewrite <- String.eqb_neq in H0. rewrite String.eqb_sym in H0. rewrite H0 in H.
    unfold EL in X.
    specialize (X x0 T0 H).
    
    destruct X as [t' [H3 H4] ].
    exists t'.
    split.
    + simpl. rewrite H0. assumption.
    + assumption.
Qed.


Lemma red_beta x s t1 t2 : 
  step_gu t1 t2 ->
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
  (red_gu_na (@tmabs USort s k (sub x t1 s0)) a0 *
  (nil ⊢ a0 ~ @tmabs USort s k a))%type}).
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
    repeat rewrite single_subs_is_sub.
    repeat rewrite single_subs_is_sub in *.
    
    assert ({a : term &
    (red_gu_na
      (@tmbin BSort (sub x t1 s1) (sub x t1 s2)) a *
    (nil ⊢ a ~
    @tmbin BSort g1 g2))%type}) as [app [Hred Ha] ] by apply (red_gu_na_app_fold Hred_g1 Hred_g2).
    exists app.
    split; auto.
    eapply alpha_trans; eauto with α_eq_db.
  - intros.
    simpl.
    exists (tmbuiltin d).
    split.
    + constructor.
    + constructor.
Qed.

(* Closure under beta expansion. *)
Lemma beta_expansion' {BA BL} A B x y s s' t :
  Alpha [(y, x)] s' s -> (* this allows us to not have to "rename free vars in t" manually*)
  GU s ->
  NC s [(x, t)] -> (* this really is the right assumption. no free variable in t is a binder in s', because these binders could be added to the environment through beta reduction and then capture*)
  SN_gu t -> 
  L A (sub x t s) ->
  L A (@tmbin BA (@tmabs BL y B s') t).
Proof with eauto with α_eq_db gu_nc_db.
  move=> Ha_s' gu nc snt h. have sns := sn_subst nc (L_sn h).
  assert (SN_gu s').
  {
    (* eapply alpha_sym in Ha_s'. *)
    eapply α_preserves_SN_R with (s := s)...
  }
  clear sns.
  generalize dependent s.
  generalize dependent t.
  induction X.
  intros t snt s0 Ha Hnc.

  (* Now create IH for other step *)
  revert Hnc.
  revert snt.
  elim=> {}.
  intros.
  rename X0 into H10.

  apply: L_nc => // u st. 
  inversion st; subst. inv H. inversion H7; subst. 

  inv H1 => //.
  - eapply α_preserves_L_R with (R := (nil)); eauto.
    (* repeat rewrite <- single_subs_is_sub. *)
    eapply alpha_rename_binder_stronger with (Rs := ((x, y0)::nil))...
    constructor.
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

      eapply step_naive_preserves_alpha2 with (s := s4) (t:=s5) (s' := (to_GU x0))...
      apply to_GU__GU.
    }
    destruct H1 as [s5' [Hstep_na_s5' Ha_s5'] ].
    assert (Hstep_s5': step_gu x0 s5').
    {
      apply step_gu_intro with (s' := to_GU x0).
      - eapply to_GU__alpha.
      - eapply to_GU__GU.
      - assumption.
    }

    eapply α_preserves_L_R with (s := tmbin (tmabs y B s5') x1) (R := nil)...
    specialize (X s5' Hstep_s5' x1).
    clear Ha_s5'. clear H7. clear st. 
    inv Hstep_s5'.
    assert (HSN_x1: SN_gu x1) by now constructor.

    (* TODO: instead of to_GU, assume gu of s0 here by NC?*)
    assert ({s'_a &  step_naive s0 s'_a * Alpha [(y, x)] s5' s'_a}%type).
    {
      eapply step_naive_preserves_alpha2 with (s := s') (s' := s0) (t := s5')...
      eapply @alpha_trans with (ren := (y, y)::nil) (ren' := (y, x)::nil) (t := x0)...
    }
    destruct H4 as [s'_a [ Hstep_s'_a Ha_s'_a ] ].
    specialize (X HSN_x1 (to_GU' x x1 s'_a)). (* just renaming binders*)
    remember (to_GU' x x1 s'_a) as s'_a1.
    assert (((y, x)::nil) ⊢ s5' ~ s'_a1).
    {
      eapply @alpha_trans with (ren := ((y, x)::nil)) (ren' := ctx_id_right ((y, x)::nil)) (t := s'_a)...
      eapply alpha_extend_ids. constructor. constructor. subst. eapply to_GU'__alpha.
    }

    eapply X; eauto.

    * subst. eapply to_GU'__GU. 
    * subst. eapply to_GU'__NC.
    * 
    assert ({α & (step_gu (sub x x1 s0) α) * (nil ⊢ α ~ sub x x1 s'_a1)}%type) 
      as [alpha [Hred Halpha] ].
      {
        repeat rewrite <- single_subs_is_psub.
        eapply (@step_subst_single)...
        subst. eapply to_GU'__alpha.
        subst. eapply to_GU'__NC.
      }
    eapply α_preserves_L_R with (s := alpha) (R := nil); auto.
    eapply L_cl with (s := (sub x x1 s0)); auto.

  - eapply α_preserves_L_R with (s := (tmbin (tmabs y B x0) t0)) (R := nil)...
    eapply H10.
    + econstructor...
    + assumption.
    + eapply step_naive_preserves_nc_ctx with (s := s0); eauto.
      eapply alpha_preserves_nc_ctx; eauto.
    +  
      assert ({ a & prod 
    ( red_gu_na (sub x x1 s0) a) 
    ( nil ⊢ a ~ sub x t0 s0) }).
      { (* this has a lot of repetition with the above *)
        apply red_beta...
        - econstructor...
        - eapply step_naive_preserves_nc_ctx with (s := s0); eauto.
          eapply alpha_preserves_nc_ctx; eauto.
      }
      destruct H as [a [Hred_a Ha_a] ].
      eapply (L_cl_star) in h.
      * eapply α_preserves_L_R with (R := nil); eauto.
      * assumption.
Qed.

Lemma beta_expansion_subst {BA BL} X t sigma s A B :
  ParSeq ((X, t)::sigma) ->
  NC (psubs sigma s) [(X, t)] -> (* so the substitution makes sense after "breaking"  it open*)
  SN_gu t -> L A (psubs ((X, t)::sigma) s) -> L A (@tmbin BA (psubs sigma (@tmabs BL X B s)) t).
Proof.
  intros HPS nc snt H.
  simpl in H.
  eapply α_preserves_L_R with (R := nil) (s := (@tmbin BA (@tmabs BL X B (to_GU' X t (psubs sigma s))) t)).
  - constructor. constructor. apply alpha_extend_ids. constructor. constructor. 
    eapply @alpha_sym. eauto. constructor. apply to_GU'__alpha. eapply alpha_refl. constructor.
  - eapply α_preserves_L_R with (R := nil) (s' := (sub X t (to_GU' X t (psubs sigma s)))) in H.
    + 
      eapply beta_expansion' in H; eauto.
      * apply alpha_extend_ids. constructor. constructor. apply alpha_refl. constructor.
      * eapply to_GU'__GU.
      * eapply to_GU'__NC.
    + repeat rewrite <- single_subs_is_psub.
      assert (psubs ((X, t)::sigma) s = psubs [(X, t)] (psubs sigma s)).
      {
        apply psubs_unfold; auto.
      }
      rewrite H0.
      apply psubs__α; auto.
      * eapply to_GU'__NC.
      * eapply to_GU'__alpha.
      * apply alpha_ctx_ren_nil.
Qed.

(* The fundamental theorem. *)
Theorem soundness Gamma s A :
  has_kind Gamma s A -> 
  GU s -> (* So that we know GU_vars (tmabs x A s) -> ~ In x (btv s), and btv s ∩ ftv s = ∅, important for dealing with vars in `t` that roll out of LR*)
  forall sigma, 
    BU sigma s -> (* so btv sigma is disjoint from tv s + ftv_env sigma: Allows adding btvs 
                        to alpha context without accidentally renaming ftvs*)
    NC s sigma -> (* so we get "nice" substitutions (is contained in BU) *)
    ParSeq sigma -> (* So parallel and sequential substitions are identical *)
    EL Gamma sigma -> (* So that terms in a substitution are already L *)
  L A (psubs sigma s).
Proof with eauto using L_sn. 
  elim=> {Gamma s A}.
  - intros Gamma X A ih gu sigma wierd nc blabla HEL.
    unfold EL in HEL.
    specialize (HEL X A ih).
    destruct HEL as [t [HlookupSigma LAt] ].
    simpl.
    rewrite HlookupSigma.
    assumption.
  - (* FUN*)
    intros.
    unfold L.
    eapply sn_ty_fun.
    + unfold not. intros Hcontra. inversion Hcontra.
    + eapply X; eauto with gu_nc_db.
      eapply BU_appl; eauto.
    + eapply X0; eauto with gu_nc_db.
      eapply BU_appr; eauto.
  - (* IFix *)
    intros.
    unfold L.
    eapply sn_ty_fun.
    + unfold not. intros Hcontra. inversion Hcontra.
    + eapply L_sn.
      eapply X0; eauto with gu_nc_db.
      eapply BU_appl; eauto.
    + eapply L_sn.
      eapply X; eauto with gu_nc_db.
      eapply BU_appr; eauto.
  - (* Forall *)
    intros.
    unfold L.
    eapply sn_ty_forall.
    assert (psubs sigma T = psubs ((X, tmvar X)::sigma) T).
    {
      apply psubs_extend_new.
      eapply nc_ftv_env  with (x := X) in H1; eauto.
      apply ftv_keys_env__no_keys; auto.
      simpl. left. auto.
    } 
    fold psubs.
    rewrite H3.
    eapply X0 with (sigma := ((X, tmvar X)::sigma)); eauto with gu_nc_db.
    + eapply BU_lam_id; eauto.
    + constructor; auto.
      * eapply nc_lam; eauto.
      * intros.
        destr_eqb_eq y X.
        -- exfalso.
           inversion H; subst.
           contradiction.
        -- split; auto.
           unfold ftv. simpl. unfold not. intros Hcontra. intuition.
    + unfold BU in H0.
      destruct H0 as [ BU1 BU2].
      constructor; auto.
      * assert (~ In X (ftv_keys_env sigma)).
        {
          intros contra.
          eapply nc_ftv_env with (x := X) in H1.
          contradiction.
          apply btv_lam.
        }
        intros Hcontra.
        apply ftv_keys_env_sigma_remove in Hcontra. contradiction.
      * intros Hcontra.
        apply BU1 in Hcontra; auto.
        simpl in Hcontra.
        intuition.
    + eapply extend_EL. eauto. apply L_var.
  - (* Builtin *)
    intros.
    unfold L.
    constructor.
    intros.
    inv H3. inv H4. inv H6. (* no step from builtin *)
  - intros Gamma X A s B _ ih gu sigma wierd nc blabla EL.
    unfold L. fold L.
    intros.

    remember (t_constr t s sigma X) as t'R.
    destruct t'R as [t' R].

    assert (HBU: BU ((X, t')::sigma) s).
    {
      eapply BU_lam2; eauto.
    }
    assert (HX: ~ In X (btv s)).
    {
      intros contra.
      inversion gu; subst.
      contradiction.
    }

    specialize (ih (gu_lam gu) ((X, t')::sigma) HBU (t_constr__nc_s HX (nc_lam nc) Heqt'R)).
    assert (Hparseq: ParSeq ((X, t')::sigma)).
    {
      (* we now need: X not a binder in sigma. *)
      constructor. auto.
        - assert (~ In X (ftv_keys_env sigma)).
        {
          intros contra.
          eapply nc_ftv_env with (x := X) in nc.
          contradiction.
          apply btv_lam.
        }
        intros Hcontra.
        apply ftv_keys_env_sigma_remove in Hcontra. contradiction.
      - unfold BU in wierd. destruct wierd as [ BU1 _].
        intros Hcontra.
        apply BU1 in Hcontra; auto.
        simpl in Hcontra.
        intuition.
    }

    specialize (ih Hparseq (extend_EL EL (α_preserves_L_R (t_constr__a_t Heqt'R) X0))).
  (* **** ih tis now fully applied ********************** *)

    eapply beta_expansion_subst in ih; auto.
    + eapply α_preserves_L_R with (s' := tmbin (psubs sigma (tmabs X A s)) t) (R := sym_alpha_ctx R) in ih; eauto. constructor.
      * eapply @alpha_sym with (ren := R). apply sym_alpha_ctx_is_sym.
        repeat rewrite psubs_to_subs; auto.
        apply (BU_smaller) in HBU.
        eapply psubs__α; eauto; [|apply (t_constr__a_sigma HBU (nc_lam nc) Heqt'R)].
        constructor. eapply alpha_extend_id''. auto; apply (t_constr__a_s (gu_lam gu) HBU Heqt'R).
      * eapply @alpha_sym; eauto. apply sym_alpha_ctx_is_sym.   
        apply (t_constr__a_t Heqt'R).
    + eapply t_constr__nc_subs; eauto.
      unfold BU in wierd. destruct wierd as [ BU1 _ ].
      intros Hcontra.
      apply BU1 in Hcontra; auto.
      simpl in Hcontra.
      intuition.
    + eapply α_preserves_SN_R; eauto. 
      * eapply t_constr__a_t; eauto. 
      * eapply L_sn; eauto.
  - intros Gamma s t A B _ ih1 _ ih2 gu sigma wierd nc blabla HEL.
    specialize (ih1 (gu_app_l gu) sigma).

    specialize (ih1 (BU_appl wierd) (nc_app_l nc) blabla HEL).
    specialize (ih2 (gu_app_r gu) _ (BU_appr wierd) (nc_app_r nc) blabla HEL).
    repeat rewrite subs_tmbin.
    unfold L in ih1. fold L in ih1.
    specialize (ih1 (psubs sigma t) ih2).
    assumption.
Qed.

(* The identity substitution is in the EL relation *)
Lemma id_subst__EL E :
  EL E (id_subst E).
Proof.
  induction E.
  - intros. simpl. unfold EL. intros. inversion H.
  - intros.
    destruct a as [x K].
    simpl.
    apply extend_EL; eauto.
    apply L_var.
Qed.

(* The fundamental theorem for named variables. *)
Corollary type_L (E : list (string * PlutusIR.kind)) s T : has_kind E s T -> L T (psubs (id_subst E) s).
Proof.
  intros Htype.
  assert (HEL: EL E (id_subst E)) by apply id_subst__EL.
  remember (s_constr s (id_subst E)) as s'.
  eapply alpha_preserves_typing with (t := s') (sigma := nil) (Gamma := E) in Htype; eauto.
  {
    eapply soundness in Htype; eauto.
    - rewrite id_subst__id in Htype; [|apply id_subst_is_IdSubst]. 
      rewrite id_subst__id; [|apply id_subst_is_IdSubst].
      eapply α_preserves_L_R with (s := s'); eauto.
      eapply alpha_sym. eapply alpha_sym_nil. eapply s_constr__a_s; eauto.
    - eapply s_constr__gu; eauto.
    - apply id_subst__nc_BU. eapply s_constr__nc_s; eauto.
    - eapply s_constr__nc_s; eauto.
    - apply id_subst__ParSeq. apply id_subst_is_IdSubst.
  }
  - eapply s_constr__a_s; eauto.
  - constructor.
Qed.

Theorem SN_gu' E s T : has_kind E s T -> @sn term step_gu s.
  intros.
  eapply type_L in H.
  rewrite id_subst__id in H; [|apply id_subst_is_IdSubst].
  eapply L_sn; eauto.
Qed.

(* Print Assumptions SN_gu. *)