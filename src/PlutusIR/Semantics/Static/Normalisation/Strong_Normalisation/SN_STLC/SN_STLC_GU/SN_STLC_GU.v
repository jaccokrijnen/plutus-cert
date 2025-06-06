From mathcomp Require Import ssreflect ssrbool eqtype.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List Util.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import alpha_vacuous construct_GU_R alpha_sub psubs step_gu alpha_typing STLC STLC_Kinding SN_STLC_GU.GU_NC_BU SN_STLC_GU.construct_GU.
From PlutusCert Require Import IdSubst step_naive alpha.alpha alpha_rename util alpha_ctx_sub variables alpha_freshness.

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

(* This would NOT work for app because of beta reduction*)
Lemma sn_ty_fun {B s t} : B <> App -> SN_gu s -> SN_gu t -> SN_gu (@tmbin B s t).
Proof with eauto with gu_nc_db α_eq_db to_GU_db.
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
  - eapply step_naive_preserves_alpha2 with (s' := to_GU x) (R := nil) in H7 as [C [Hstep_C Ha_C] ]...
    eapply α_preserves_SN_R with (R := []) (s := @tmbin B C t2)...
    eapply X with (y := C).
    + apply step_gu_intro with (s' := to_GU x)...
    + eapply α_preserves_SN_R... constructor; auto.
  - eapply step_naive_preserves_alpha2 with (s' := to_GU x0) (R := nil) in H7 as [C [Hstep_C Ha_C] ]...
    eapply α_preserves_SN_R with (R := []) (s := @tmbin B x C)...
    eapply X0 with (y := C).
    apply step_gu_intro with (s' := to_GU x0)...
Qed.

Lemma sn_ty_forall {B X K T} : SN_gu T -> SN_gu (@tmabs B X K T).
Proof with eauto with α_eq_db gu_nc_db to_GU_db.
  induction 1.
  apply SNI; intros y Hstep.
  inversion Hstep; subst.
  inversion H; subst.
  inversion H1; subst.
  eapply step_naive_preserves_alpha2 with (s' := to_GU x) (R := ((y0, X)::nil)) in H7 as [C [Hstep_C Hα_C] ]...
  - eapply α_preserves_SN_R with (R := []) (s := @tmabs B X K C) in X0...
    apply step_gu_intro with (s' := (to_GU x))...
  - eapply @alpha_trans with (t := x)...
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
  GU s -> 
  NC s [(x, p)] -> 
  Alpha R t t' -> 
  αCtxSub R [(x, p)] [(x, p)] -> 
  NC t' [(x, p)] ->
  {aT : term & 
  (step_gu (psubs ((x, p)::nil) s) aT) * (Alpha R aT (psubs ((x, p)::nil) t'))}%type.
Proof with eauto with sconstr2_db gu_nc_db α_eq_db to_GU_db to_GU''_db.
  intros. rename H into Hstep. generalize dependent t'. generalize dependent R. induction Hstep; intros.
  - (* The difficult case. The whole reason we need to do global uniqueness every step *)
    (* Globally uniquified version of the termt to step is of the same shape: tmbin (tmabs ...) ...*)
    assert ({x' : string & {s' & { t' & 
      ((to_GU (@tmbin App (@tmabs Lam x0 A (psubs [(x, p)] s)) (psubs [(x, p)] t))) = @tmbin App (@tmabs Lam x' A s') t') 
        * Alpha ((x0, x')::nil) (psubs [(x, p)] s) s' * Alpha [] (psubs [(x, p)] t) t'} } }%type).
    {
      eapply to_GU_applam_unfold. auto.
    }
    destruct H as [x0' [sub_s [ sub_t [ [pr_eq Ha_subs] Ha_subt]]]]; subst.
    
    exists (sub x0' sub_t sub_s). (* Instantiate with ingredients of globally unique term*)
    split.
    + eapply step_gu_intro with (s' := (tmbin (tmabs x0' A sub_s) sub_t)).
      * constructor. constructor. auto. auto.
      * rewrite <- pr_eq. apply to_GU__GU.
      * apply step_beta.
    + (* Freshen s t and p to be able to use commute subst *)
      remember (sconstr2 x0 t x p s ) as sconstr2_.
      destruct sconstr2_ as [ [s' t'0] p'].

      eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R) 
          (t := sub x0 (psubs ([(x, p')]) t'0) (psubs ([(x, p')]) s')); eauto with α_eq_db_trans...
      * eapply alpha_extend_ids.
        eapply ctx_id_left_is_id.

        eapply alpha_rename_binder_stronger with (Rs := ((x0', x0)::nil)); eauto...
        -- eapply @alpha_trans with (t := psubs ((x, p)::nil) s) (ren := ((x0', x0)::nil)); eauto with α_eq_db.
           eapply alpha_extend_ids. constructor. constructor.
           eapply psubs__α; eauto with gu_nc_db sconstr2_db α_eq_db.
        -- eapply @alpha_trans with (t := psubs ((x, p)::nil) t); eauto with α_eq_db.
           eapply psubs__α...
        -- constructor.
        -- eapply gu_applam_to_nc. rewrite <- pr_eq. apply to_GU__GU.
      * eapply commute_sub_naive; eauto...
        -- eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R) (t := sub x0 t s); eauto with α_eq_db_trans.
           eapply alpha_extend_ids.
           eapply ctx_id_left_is_id.
           repeat rewrite <- single_subs_is_psub.
           eapply psubs__α with (R := nil)...
        -- eapply αctx_trans with (R1 := ctx_id_left R) (R2 := R) (R := R) (σ' := ((x, p)::nil)); auto; eauto with α_eq_db_trans.
           constructor. constructor. 
           ++ apply alphavar_extend_ids. apply ctx_id_left_is_id. constructor.
           ++ apply alpha_extend_ids... apply ctx_id_left_is_id. 
        -- apply nc_ftv_env with (x := x0) in H1. simpl in H1. simpl. intuition. unfold btv. left. reflexivity.
        -- intros ftvs HftvsIn Hcontra.
           destruct HftvsIn; auto.
           rewrite <- H in *.
           apply nc_ftv_env with (x := x0) in H1; simpl; auto with *.
           destruct H1.
           apply @alpha_preserves_ftv with (ren := nil) (x' := x0) (s' := p) in Hcontra...
           right; auto with *.
  - inversion H2; subst.
    edestruct IHHstep as [sigS1 [HstepS1 HalphaS1] ]...
    inv HstepS1.
    remember (to_GU (@tmbin B s' (psubs ((x, p)::nil) t))) as st_gu.
    destruct (to_GU_app_unfold Heqst_gu) as [sigS1Alpha [sigtalpha [ [Happ Ha_s] Ha_t ] ] ]; subst.
    eapply step_naive_preserves_alpha2 with (s := s') (s' := sigS1Alpha) (t := sigS1) 
      in H6 as [s''step [Halpha_s'' Hstep_s'' ] ]...
    2: eapply gu_app_l; eauto; rewrite <- Happ; apply to_GU__GU.

    exists (@tmbin B s''step sigtalpha).
    split.
    + apply step_gu_intro with (s' := (@tmbin B sigS1Alpha sigtalpha )); auto...
      * subst. rewrite <- Happ. apply to_GU__GU.
      * constructor. eauto.
    + eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R). 
      * eapply id_left_trans. 
      * apply alpha_extend_ids. apply ctx_id_left_is_id. constructor. eapply alpha_sym. constructor. eauto. eapply alpha_sym. constructor. eauto.
      * constructor. eauto. 
        eapply psubs__α; eauto...
  - (* TODO: cleanup, because this is completely analogous to case above*) 
    inversion H2; subst.
    edestruct IHHstep as [sigS1 [HstepS1 HalphaS1] ]...
    inv HstepS1.
    remember (to_GU (@tmbin B s' (psubs ((x, p)::nil) s))) as st_gu.
    destruct (to_GU_app_unfold Heqst_gu) as [sigS1Alpha [sigtalpha [ [Happ Ha_s] Ha_t ] ] ]; subst.
    eapply step_naive_preserves_alpha2 with (s := s') (s' := sigS1Alpha) (t := sigS1) 
      in H6 as [s''step [Halpha_s'' Hstep_s'' ] ]...
    2: eapply gu_app_l; eauto; rewrite <- Happ; apply to_GU__GU.

    exists (@tmbin B sigtalpha s''step); split.
    + apply step_gu_intro with (s' :=  (@tmbin B sigtalpha sigS1Alpha))...
      * apply gu_app_st__gu_app_ts. rewrite <- Happ. apply to_GU__GU.
      * constructor; auto.
    + eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R) (t := tmbin (psubs ((x, p)::nil) s) (sigS1)).
      * eapply id_left_trans. 
      * apply alpha_extend_ids... apply ctx_id_left_is_id. 
      * constructor; auto.
        eapply psubs__α; eauto...
  - inversion H2; subst.
    edestruct IHHstep with (t' := s3) (R := ((x0, y)::R)) as [subSigmaS2 [Hsteps1 Halpha] ]...
    + apply alpha_ctx_ren_extend_fresh_ftv.
      * apply nc_ftv_env with (x := x0) in H1. auto. simpl. auto.
      * apply nc_ftv_env with (x := y) in H4. auto. simpl. auto.
      * assumption.
    + inversion Hsteps1 as [? ? ? ? ? Hstep_na]; subst.
      (* Uniquify s' s.t. x0 not used as binder: Composability: GU composes up to alpha *)
      eapply step_naive_preserves_alpha2 with (s' := to_GU'' x0 s') in Hstep_na as [s''step [Halpha_s'' Hstep_s'' ] ]; eauto...
      exists (@tmabs B x0 A s''step).
      split.
      * apply step_gu_intro with (s' := @tmabs B x0 A (to_GU'' x0 s')); eauto...
        -- subst. eapply to_GU''__GU_lam.
        -- constructor; assumption.
      * constructor.
        eapply @alpha_trans with (ren := ctx_id_left ((x0, y)::R)) (ren' := ((x0, y)::R))...
        -- eapply id_left_trans.
        -- apply alpha_extend_ids... apply ctx_id_left_is_id. 
Qed.

Definition sub_gu (X : string) (T : term) (s : term) := sub X T (to_GU' X T s).

Lemma sn_subst X T s : NC s ((X, T)::nil) -> SN_gu (sub X T s) -> SN_gu s.
Proof with eauto with to_GU'_db.
  intros Hnc HSN_sub.
  rewrite <- single_subs_is_psub in HSN_sub.
  eapply α_preserves_SN_R with (s := psubs ((X, T)::nil) s) (s' := psubs((X, T)::nil) (to_GU' X T s)) 
    in HSN_sub; eauto using psubs__α with α_eq_db...
  2: eapply psubs__α with (R := nil); eauto with α_eq_db...
  rewrite single_subs_is_psub in HSN_sub.
  revert HSN_sub.
  apply (sn_preimage_α (h := sub_gu X T)) => x y Hstep.
  unfold sub_gu.
  repeat rewrite <- single_subs_is_psub.
  inversion Hstep; subst.
  eapply step_naive_preserves_alpha2 with (R := nil) (t:= y) (s' := to_GU' X T x) 
    in H1 as [t'' [Hstep_t'' Ha_t''] ]; eauto with α_eq_db...
  2: eapply @alpha_trans with (t := x); eauto with α_eq_db...
  eapply @step_subst_single with (s := (to_GU' X T x)) (t := t''); eauto with α_eq_db...
  apply @alpha_trans with (t := y) (ren := nil) (ren' := nil); repeat constructor...
  eauto with α_eq_db.  
Qed.

Lemma red_beta x s t1 t2 : 
  step_gu t1 t2 ->
  NC s ((x, t1)::nil) ->
  { a & prod 
    ( red_gu_na (sub x t1 s) a) 
    ( nil ⊢ a ~ sub x t2 s) }. 
Proof with eauto with α_eq_db. 
  intros Hstep HNC_t1.
  induction s.
  - eexists; split...
    destr_eqb_eq x s; simpl.
    + rewrite String.eqb_refl.
      apply red_gu_na_star with (t := t2); auto; constructor.
    + rewrite <- String.eqb_neq in H; rewrite H; constructor.
  - specialize (IHs (nc_lam HNC_t1)) as [a [Hred_a Ha_a] ].
    assert ({a0 : term & (red_gu_na (@tmabs USort s k (sub x t1 s0)) a0 *
                            (nil ⊢ a0 ~ @tmabs USort s k a))%type}) 
      as [a0 [Hred_a0 Ha_a0]] by apply (red_gu_na_lam_fold Hred_a).
    eexists; split...
  - specialize (IHs1 (nc_app_l HNC_t1) ) as [g1 [Hred_g1 ?] ].
    specialize (IHs2 (nc_app_r HNC_t1) ) as [g2 [Hred_g2 ?] ].
    assert ({a : term & (red_gu_na (@tmbin BSort (sub x t1 s1) (sub x t1 s2)) a *
                          (nil ⊢ a ~ @tmbin BSort g1 g2))%type}) 
      as [app [Hred Ha] ] by apply (red_gu_na_app_fold Hred_g1 Hred_g2).
    eexists; split...
  - eexists. split; constructor.
Qed.

Definition cand := term -> Type.

(* Note: This is different then neutral_Ty*)
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
        eapply α_preserves_L_R; eauto.
        constructor; eapply alpha_sym; eauto; constructor.
    + move=> s ns h t la.
      have snt := p_sn ih1 la.
      elim: snt la => {} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      inv H.  inv H1=> //...
      * inv H7. discriminate ns.
      * eapply α_preserves_L_R with (s' := t2) in la; eauto.
        apply gu_app_l in H0; eauto using step_gu_intro.
      * assert (step_gu t t0).
        {
          apply gu_app_r in H0; eauto using step_gu_intro.
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

(* Reverse of beta reduction. *)
Lemma beta_expansion' {BA BL} A B x y s s' t :
  Alpha [(y, x)] s' s -> 
  GU s ->
  NC s [(x, t)] -> 
  SN_gu t -> 
  L A (sub x t s) ->
  L A (@tmbin BA (@tmabs BL y B s') t).
Proof with eauto with α_eq_db gu_nc_db.
  move=> Ha_s' gu nc snt h.
  assert (Hsns': SN_gu s').
  { eapply α_preserves_SN_R with (s := s)... 
    apply (sn_subst nc (L_sn h)).
  }
  generalize dependent s.
  generalize dependent t.
  induction Hsns' as [? ? IH1]; intros t snt s0 Ha Hnc.
  (* Now create IH for other step *)
  revert Hnc.
  revert snt.
  induction 1 as [? ? IH2]; intros Hgu Hnc HL.

  apply: L_nc => // u st. 
  inversion st; subst. inv H. inversion H7; subst; clear st.
  inv H1 => //.
  - eapply α_preserves_L_R with (R := (nil)); eauto.
    eapply alpha_rename_binder_stronger with (Rs := ((x, y0)::nil))...
    constructor.
  - inv H5.
    assert ({s5' & step_naive (to_GU x0) s5' * Alpha [(y0, y)] s5 s5'}%type)
      as [s5' [Hstep_na_s5' Ha_s5'] ].
    {
      eapply step_naive_preserves_alpha2 with (s := s4) (t:=s5) (s' := (to_GU x0))...
      apply to_GU__GU.
      eapply @alpha_trans with (ren' := (y, y)::nil) (t := x0)...
      apply alpha_extend_ids; eauto with to_GU_db. repeat constructor.
    }
    eapply step_gu_intro in Hstep_na_s5'; eauto with to_GU_db...
    eapply α_preserves_L_R with (s := tmbin (tmabs y B s5') x1) (R := nil)...
    specialize (IH1 _ Hstep_na_s5').
    inv Hstep_na_s5'.
    edestruct step_naive_preserves_alpha2 with (R := [(y, x)]) (s' := s0) (t := s5') as [s'_a [Hstep_s'_a Ha_s'_a] ]...
    1: eapply @alpha_trans with (ren := (y, y)::nil) (ren' := (y, x)::nil) (t := x0)...
    eapply IH1 with (s := (to_GU' x x1 s'_a)); subst; eauto with to_GU'_db α_eq_db...
    + now constructor.
    + assert ({α & (step_gu (sub x x1 s0) α) * (nil ⊢ α ~ sub x x1 (to_GU' x x1 s'_a))}%type) 
        as [alpha [Hred Halpha] ].
      {
        repeat rewrite <- single_subs_is_psub.
        eapply (@step_subst_single); eauto with to_GU'_db...
      }
      eapply α_preserves_L_R with (s := alpha) (R := nil); auto.
      eapply L_cl with (s := (sub x x1 s0)); auto.
  - eapply α_preserves_L_R with (s := (tmbin (tmabs y B x0) t0)) (R := nil)...
    eapply IH2; auto.
    + econstructor...
    + eapply step_naive_preserves_nc_ctx with (s := s0); eauto.
      eapply alpha_preserves_nc_ctx; eauto.
    + edestruct red_beta as [a [Hred_a Ha_a]] in H5; eauto.
      * econstructor... 
      * eapply (L_cl_star) with (t := a) in HL; auto.
        eapply α_preserves_L_R with (R := nil); eauto.
Qed.

Definition EL (Δ : list (string * PlutusIR.kind)) 
          (sigma : list (string * term)) : Type :=
  forall x T, lookup x Δ = Some T ->
    { t & prod (lookup x sigma = Some t) (L T t)}.

Lemma extend_EL (Δ : list (string * PlutusIR.kind)) (sigma : list (string * term)) x T t :
  EL Δ sigma -> L T t -> EL ((x, T) :: Δ) ((x, t) :: sigma).
Proof.
  intros HEL HL.
  unfold EL. intros x0 T0 Hl.
  destr_eqb_eq x0 x.
  - exists t.
    split; simpl.
    + rewrite String.eqb_refl. reflexivity.
    + simpl in Hl. rewrite String.eqb_refl in Hl. inversion Hl. subst. assumption.
  - simpl in Hl. rewrite <- String.eqb_neq in H. rewrite String.eqb_sym in H. rewrite H in Hl.
    unfold EL in HEL.
    specialize (HEL x0 T0 Hl).
    
    destruct HEL as [t' [H3 H4] ].
    exists t'.
    split; auto.
    simpl. rewrite H. assumption.
Qed.

Lemma beta_expansion_subst {BA BL} X t sigma s A B :
  ParSeq ((X, t)::sigma) ->
  NC (psubs sigma s) [(X, t)] -> (* so the substitution makes sense after "breaking"  it open*)
  SN_gu t -> 
  L A (psubs ((X, t)::sigma) s) -> L A (@tmbin BA (psubs sigma (@tmabs BL X B s)) t).
Proof with eauto with α_eq_db to_GU'_db.
  intros HPS nc snt HL.
  eapply α_preserves_L_R with (R := []) (s := (@tmbin BA (@tmabs BL X B (to_GU' X t (psubs sigma s))) t)).
  - constructor; eauto...
  - eapply α_preserves_L_R with (R := []) (s' := (sub X t (to_GU' X t (psubs sigma s)))) in HL.
    + eapply beta_expansion' in HL; eauto...
    + repeat rewrite <- single_subs_is_psub.
      rewrite psubs_unfold; auto.
      apply psubs__α; auto...
Qed.

(* The fundamental theorem of L. *)
Theorem fundamental Δ s A :
  Δ |-* s : A -> 
  GU s -> (* So that we know GU_vars (tmabs x A s) -> ~ In x (btv s), and btv s ∩ ftv s = ∅, important for dealing with vars in `t` that roll out of LR*)
  forall sigma, 
    BU sigma s -> (* Allows adding btvs to alpha context without accidentally renaming ftvs*)
    NC s sigma -> (* so we get no capture substitutions *)
    ParSeq sigma -> (* So parallel and sequential substitions are identical *)
    EL Δ sigma -> (* So that terms in a substitution are already L *)
  L A (psubs sigma s).
Proof with eauto using L_sn with gu_nc_db bu_db. 
  elim=> {Δ s A}.
  - (* K_Var *)
    intros Δ X A ih gu sigma bu nc ps HEL.
    unfold EL in HEL.
    destruct (HEL X A ih) as [t [HlookupSigma LAt] ]; simpl.
    rewrite HlookupSigma; auto.
  - (* FUN*)
    intros.
    unfold L.
    eapply sn_ty_fun.
    + unfold not. intros Hcontra. inversion Hcontra.
    + eapply X...
    + eapply X0...
  - (* IFix *)
    intros.
    unfold L.
    eapply sn_ty_fun.
    all: try eapply L_sn...
    unfold not. intros Hcontra. inversion Hcontra.
  - (* Forall *)
    intros.
    unfold L.
    eapply sn_ty_forall.
    fold psubs.
    assert (psubs sigma T = psubs ((X, tmvar X)::sigma) T).
    {
      apply psubs_extend_new.
      eapply nc_ftv_env  with (x := X) in H1; eauto.
      apply ftv_keys_env__no_keys; auto.
      simpl. left. auto.
    } 
    fold psubs.
    rewrite H3.
    eapply X0 with (sigma := ((X, tmvar X)::sigma)); eauto with gu_nc_db bu_db.
    + constructor; eauto...
      intros.
      destr_eqb_eq y X.
      -- exfalso.
         inversion H; subst.
         contradiction.
      -- split; auto.
         unfold ftv. simpl. unfold not. intros Hcontra. intuition.
    + destruct H0 as [BU1 BU2]. 
      constructor; auto; intros Hcontra.
      * apply ftv_keys_env_sigma_remove in Hcontra.
        eapply nc_ftv_env with (x := X) in H1.
        contradiction.
        apply btv_lam.
      * apply BU1 in Hcontra; auto.
        simpl in Hcontra.
        intuition.
    + eapply extend_EL. eauto. apply L_var.
  - (* Builtin *)
    intros.
    unfold L.
    constructor.
    intros.
    inv H3. inv H4. inv H6. (* no step from builtin *)
  - (* K_Lam *)
    intros Δ X A s B _ ih gu sigma bu nc ps EL.
    simpl L; intros t HLA.
    remember (t_constr t s sigma X) as t'R.
    destruct t'R as [t' R].
    assert (HBU: BU ((X, t')::sigma) s).
    { eapply BU_lam2; eauto. }
    assert (HX: ~ In X (btv s)).
    { 
      intros contra.
      inversion gu; subst.
      contradiction.
    }
    assert (Hparseq: ParSeq ((X, t')::sigma)).
    {
      constructor; auto; intros Hcontra.
      - apply ftv_keys_env_sigma_remove in Hcontra. 
        apply nc_ftv_env with (x := X) in nc; [|apply btv_lam].
        contradiction.
      - destruct bu as [ BU1 _ ].
        apply BU1 in Hcontra; auto.
        simpl in Hcontra.
        intuition.
    }
    specialize (ih (gu_lam gu) ((X, t')::sigma) HBU (t_constr__nc_s HX (nc_lam nc) Heqt'R) Hparseq (extend_EL EL (α_preserves_L_R (t_constr__a_t Heqt'R) HLA))).
    (* **** ih is now fully applied ********************** *)
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
      destruct bu as [ BU1 _ ].
      intros Hcontra.
      apply BU1 in Hcontra; auto.
      simpl in Hcontra.
      intuition.
    + eapply α_preserves_SN_R; eauto. 
      * eapply t_constr__a_t; eauto. 
      * eapply L_sn; eauto.
  - intros Δ s t A B _ ih1 _ ih2 gu sigma bu nc ps HEL.
    simpl L in ih1; eauto.
    apply ih1; eauto with gu_nc_db bu_db.
Qed.

(* The identity substitution is in the EL relation *)
Lemma id_subst__EL Δ :
  EL Δ (id_subst Δ).
Proof.
  induction Δ; intros; simpl.
  - unfold EL. intros. inversion H.
  - destruct a as [x K].
    apply extend_EL; eauto.
    apply L_var.
Qed.

(* The fundamental theorem for named variables. *)
Corollary type_L Δ s T : Δ |-* s : T -> L T (psubs (id_subst Δ) s).
Proof with eauto using id_subst__EL with s_constr_db id_subst_db.
  intros Hkind.
  remember (s_constr s (id_subst Δ)) as s'.
  eapply alpha_preserves_typing with (t := s') (sigma := nil) (Gamma := Δ) in Hkind; eauto...
  {
    eapply fundamental in Hkind; eauto...
    - rewrite id_subst__id in Hkind...
      rewrite id_subst__id...
      eapply α_preserves_L_R with (s := s'); eauto with α_eq_db s_constr_db.
  }
  constructor.
Qed.

Theorem strong_normalization_gu Δ s T : Δ |-* s : T -> @sn term step_gu s.
  intros Hkind.
  eapply type_L in Hkind.
  rewrite id_subst__id in Hkind; [|apply id_subst_is_IdSubst].
  eapply L_sn; eauto.
Qed.