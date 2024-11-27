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



(* ********************
      Beta reduction
*)


(* Lemma sred_up sigma tau : 
  sred sigma tau -> sred (up sigma) (up tau).
Proof. move=> A [|n] //=. asimpl. apply/red_subst/A. Qed. *)

Global Hint Resolve red_app red_abs 
(* sred_hup  *)
: red_congr.

(* Lemma red_compat sigma tau s :
  sred sigma tau -> red ([x := sigma] s) ([x := tau] s).
Proof.
  elim: s sigma tau; intros; asimpl; eauto with red_congr.
Qed. *)

(* Note: 27 nov: this ren_comp_exsits may be an alternative to the alpha trans arguments*)

(* NOTE: A little pen and paper study strongly suggests that this is still true for named. *)
(* NOTE: At first I would expect that it would step on the right hand side (instead of multistep=red)
    but it doesnt because of the following example:
    Let t1 = (\x.x)w and t2 = w (which steps by step_beta)
    Let s = \y. (\z. x) x
    Then [x := t1] s = \y. (\z. t1) t1 = \y. (\z. (\x.x) w) ((\x.x) w)
    And [x := t2] s = \y. (\z. t2) t2 = \y. (\z. w) w

    there is no single step from the first to the second, since we have to perform
    step_beta in two different places.
    *)

(* TODO: cant we make it a relation? mren rho1 (mren rho2 s) in Mren s*)
Lemma ren_comp rho1 rho2 s : exists rho', mren rho1 (mren rho2 s) = mren rho' s.
Proof.
  (* TODO: Figure out on pen and paper first.*)
Admitted.


Require Import Ascii.

    (*
    
    Hmm: we know [x := t1] s ~ [x' := t1'] s' under R if all the ingredients are.
    
    sooooo suppose there is only one var y∈ U.
    Let R = [(y, y' = "b" ++ fresh2 x t1 s)]. 

    Suppose y <> x

    Then we know (y, y') |- [x := t1] s ~ [x := ren y y' t1] (ren y y' s)

    (y, y')::ren t1 (ren y y' t1).
    (y, y')::ren t2 (ren y y' t2). => (y, y')::ren t1 ~ t2, because y notin t2


    *)

Lemma add_vacuous x t1 t2 s s' s'' ren1 ren2 ren :
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  ren ⊢ t2 ~ t2 ->
  AlphaVar ren x x ->
  αCtxTrans ren1 ren2 ren ->
  ren ⊢ ([x := t2] s') ~ (((x, t2)::(x, t1)::nil) [[s'']]).
Proof.
  intros HalphaS1 HalphaS2 Halphat2 Halphax HalphaTrans.
  generalize dependent s'.
  generalize dependent s''.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.
  induction s; intros.
  - inversion HalphaS1; subst.
    inversion HalphaS2; subst.
    assert (AlphaVar ren x0 y). { eapply alpha_var_trans; eauto. }
    destr_eqb_eq x x0.
    {
      assert (y = x0). { apply (alphavar_unique_right Halphax) in H. symmetry. auto. }  subst.
      rewrite capms_var_helper.
      rewrite capms_var_helper.
      assumption.
    }
    {
      assert (y <> x). { apply (alphavar_unique_not_left H0 Halphax) in H. symmetry. auto. }
      rewrite capms_var_single_not.
      rewrite capms_var_multi_not.
      rewrite capms_var_single_not.
      eapply alpha_trans; eauto.
      - symmetry; auto.
      - symmetry; auto.
      - auto.
    }
  - inversion HalphaS1; subst.
    inversion HalphaS2; subst.
    autorewrite with capms.
    simpl.
    remember (fresh2 _ s1) as b1.
    remember (fresh2 _ s3) as b2.
    apply alpha_lam.
    eapply IHs.
    + eapply alpha_extend_fresh.
      * eapply fresh2_over_tv_value_sigma in Heqb1.
        -- intros Hcontra. 
           apply extend_ftv_to_tv in Hcontra.
           apply Heqb1 in Hcontra.
           contradiction.
        -- apply in_cons; apply in_eq.
      * eapply fresh2_over_tv_value_sigma in Heqb2.
        -- intros Hcontra. 
           apply extend_ftv_to_tv in Hcontra.
           apply Heqb2 in Hcontra.
           contradiction.
        -- apply in_cons; apply in_eq.
      * assumption.
    + apply alpha_var_diff.
      * eapply fresh2_over_key_sigma in Heqb1.
        -- intros Hcontra. 
           apply Heqb1 in Hcontra.
           contradiction.
        -- apply in_cons; apply in_eq.
      * eapply fresh2_over_key_sigma in Heqb2.
        -- intros Hcontra. 
           apply Heqb2 in Hcontra.
           contradiction.
        -- apply in_cons; apply in_eq.
      * assumption.
    + apply alpha_trans_cons.
      eauto.
    + eapply alpha_trans_rename_right; eauto.
    + eapply alpha_trans_rename_left; eauto.
  - inversion HalphaS1.
    inversion HalphaS2; subst.
    autorewrite with capms.
    apply alpha_app.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto.
Qed.

Lemma red_beta'' x s t1 t2 : 
  step t1 t2 ->
  forall s' s'' ren1 ren2 ren,
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  ren ⊢ t1 ~ t1 ->
  ren ⊢ t2 ~ t2 ->
  AlphaVar ren x x ->
  αCtxTrans ren1 ren2 ren ->
  { a & prod 
    ( red ([x := t1] s') a)
    ( ren ⊢ a ~ (((x, t2)::(x, t1)::nil) [[s'']])) }. (* Ugly cheat: adding the x, t1 makes sure it does not generate fresh vars equal to ftv of t1...*)
Proof. 

  intros Hstep.
  induction s; intros s' s'' ren1 ren2 ren HalphaS1 HalphaS2 Halphat1 Halphat2 Halphax HalphaTrans.
  - inversion HalphaS1; subst.
    inversion HalphaS2; subst.
    (* Do we have ren |- t1 ~ t1 ?
    
      Maybe if the condition is: forall (u, v) in ren
      if v notin ftv t2, then u notin ftv t1

      But suppose there was some x in ftv t1, that disappears in the step.

      Can we then get the situtaion (x, y) |- t1 ~ t1 ? 
      y notin ftv t2, so y notin ftv t1
    *)
    autorewrite with capms.
     admit.
  - (* tmlam *)
    inversion HalphaS1; subst.
    inversion HalphaS2; subst.
    autorewrite with capms; simpl.
    remember (fresh2 _ s1) as b1.
    remember (fresh2 _ s3) as b2.
    eexists (tmlam b2 t _).

    remember (fresh2 [(b1, t1); (b2, t2); (x, tmvar x)] s0) as b3.
    specialize (IHs (rename x0 b1 s1) (rename y b2 s3) ((b1, s)::ren1) ((s, b2)::ren2) ((b1, b2)::ren)).
    assert ({a : term & prod
        (((b1, b2) :: ren)
        ⊢ [x := t1] rename x0 b1 s1 ~ a ) (
        red a (((x, t2)::(x, t1)::nil) [[rename y b2 s3]] ))}) as [a' [Halpha' Hstep'] ].
    {
      eapply IHs.
      - eapply alpha_trans_rename_left; eauto.
      - eapply alpha_trans_rename_right; eauto. 
      - (* such a cheat!!!! *)
           
        admit.
      - admit.
      - admit.
      - apply alpha_trans_cons.
        eauto.
    
    }
    split.
    + apply alpha_lam.
      (* instantiate (1 := ). *)

      (* 

      *)
      admit.
    + apply red_abs.
      (* ?Goal1 := (rename b3 b2 a') 
        Because then ((b1, b2)::ren) [x := t1] rename x0 b1 s1 ~ rename b3 b2 a'.

        Do we then have:

        red (rename b3 b2 a') ([x := t2] rename y b2 s3)?

        We know
          red a' ([x := t2] rename y b3 s3).
          Then also
          red (rename b3 b2 a') ([x := t2] rename b3 b2 (rename y b3 s3)) probably...
          nah, it is unclear why we could do rename b3 b2 a'. What if b2 already in a'?
          it cant be, because it isnt in [x := t2] (rename y b3 s3). ... annoying argument.
      *)
      
Admitted.

Lemma red_beta' x s t1 t2 :
  step t1 t2 ->
  forall s' s'' ren1 ren2 ren,
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  ren ⊢ t1 ~ t1 ->
  ren ⊢ t2 ~ t2 ->
  AlphaVar ren x x ->
  αCtxTrans ren1 ren2 ren ->
  { a & prod 
    (red ([x := t1] s') a)
    ( ren ⊢ a ~ (((x, t2)::nil) [[s'']])) }.
Proof.
  intros.
  assert ({a & prod 
    (red ([x := t1] s') a)
    ( ren ⊢ a ~ (((x, t2)::(x, t1)::nil) [[s'']])) }) as [a [Halpha Hred] ].
  {
    eapply red_beta''; eauto.
  }
  exists a.
  split.
  - assumption.
  - eapply alpha_trans.
    + apply id_right_trans.
    + exact Hred.
    + change (ctx_id_right ren) with (nil ++ ctx_id_right ren).
      apply alpha_extend_ids_right.
      * apply ctx_id_right_is_id.
      * eapply alpha_sym. apply alpha_sym_nil.
        eapply add_vacuous.
        -- apply alpha_refl. apply alpha_refl_nil.
        -- apply alpha_refl. apply alpha_refl_nil.
        -- apply alpha_refl. apply alpha_refl_nil.
        -- apply alpha_var_refl.
        -- apply alpha_trans_nil.
Qed.

Lemma red_beta x s t1 t2 :
  step t1 t2 ->
  { α & prod 
      (red ([x := t1] s) α)
      (nil ⊢ α ~ ([x := t2] s))
  }.
Proof.
  intros Hstep.
  eapply red_beta'; auto; 
    solve [try apply alpha_refl; try apply alphavar_refl; constructor].
Qed.

(* Strong Normalization *)

(* used to be prop *)
Inductive sn {e : term -> term -> Set } x : Set :=
| SNI : (forall y, e x y -> sn y) -> sn x.

(*
Intuition:
h x is strongly normalizing.
then every reduction sequence starting from (h x) is finite.
The first condition (e x y -> e (h x) (h y)) says that each step has a corresponding step under h.
So in extension, each reduction chain starting from x has a corresponding reduction chain starting from h x.

So, since h x is SN, every reduction chain starting from h x is finite.
Then, by the extension, every reduction chain starting from x is finite.
*)
Lemma sn_preimage {e : term -> term -> Set} (h : term -> term) x :
  (forall x y, e x y -> e (h x) (h y)) -> @sn e (h x) -> @sn e x.
Proof.

  move eqn:(h x) => v A B.
  generalize dependent h.
  generalize dependent x.
  elim: B => {} v _ ih x h eqn.
  intros A.
  apply: SNI => y /A.
  

  
  rewrite eqn => /ih. eauto.
Qed.

Lemma sn_preimage_alpha {e : term -> term -> Set} (h : term -> term) x :
  (forall x y, e x y -> { a : term & prod(Alpha [] (h y) a) (e (h x) a) }) -> 
  @sn e (h x) -> { a2 : term & prod(Alpha [] x a2) (@sn e a2)}.
Proof.
  (* move eqn:(h x) => v A B. elim: B h x A eqn => {} v _ ih h x A eqn.
  eexists.
  split.
  - admit.
  - 
  apply: SNI => y /A. rewrite eqn => /ih. apply/ih; eauto. *)
Admitted.

Notation SN := (@sn step).

Lemma sn_closedL t s : SN (tmapp s t) -> SN s.
Proof. apply: (sn_preimage (h := tmapp^~t)) => x y. exact: step_appL. Qed.

Lemma sn_subst sigma s : SN (sigma [[s]]) -> SN s.
Proof.
Admitted.

(* Not sure yet how to use the step_subst lemma in this*)
Lemma sn_subst_alpha sigma s : SN (sigma [[s]]) -> {alphaS & prod (Alpha [] alphaS s) (SN alphaS)}.
Proof.
  (* intros H.
  apply sn_preimage_alpha in H. 
    - destruct H as [alphaS [Halpha Hsn] ].
    exists alphaS.
      split.
      + eapply alpha_sym.
        * constructor.
        * assumption.
      + assumption.
    - intros x y Hstep.
      apply (@step_subst_sigma x y sigma) in Hstep.
      destruct Hstep as [alphaSigmaT [Hred Halpha] ].
      exists alphaSigmaT.
      split.
      * eapply alpha_sym.
        -- constructor.
        -- assumption.
      * assumption. *)
Admitted.

(* The Reducibility Candidates/Logical Predicate*)

Definition cand := term -> Set.

Definition neutral (s : term) : bool :=
  match s with
    | tmlam _ _ _ => false
    | _ => true
  end.

Record reducible (P : cand) : Set := {
  p_sn : forall s, P s -> SN s;
  p_cl : forall s t, P s -> step s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step s t -> P t) -> P s
}.

(* **** The logical relation for proving Strong normalization, 
        strengthens the IH to say something about labmda bodies*)
Fixpoint L (T : type) : cand :=
  match T with
    | tp_base => SN 
    | tp_arrow A B => fun s => forall t, L A t -> L B (tmapp s t)
  end.

Require Import Coq.Program.Equality.

(* Very important result that shows why working up to alpha equivalence is well founded *)
Theorem α_preserves_SN s s' :
  Alpha [] s s' -> SN s -> SN s'.
Proof.
  intros Hα Hsn.
  generalize dependent s'.
  induction Hsn. intros s' Hα.
  apply SNI.
  intros y1 Hstep.
  assert ({y1_α & prod (step x y1_α) (nil ⊢ y1 ~ y1_α)}) as [y1_α [Hstep' Hα'] ].
  {
    eapply step_preserves_alpha; auto.
    - eapply alpha_sym in Hα. exact Hα. apply alpha_sym_nil.
    - assumption.
  }
  eapply H.
  - exact Hstep'.
  - eapply alpha_sym. apply alpha_sym_nil. exact Hα'.
Qed.

(* integrally depends on α_preserves_SN *)
Lemma α_preserves_L A s s' :
  Alpha [] s s' -> L A s -> L A s'.
Proof.
  intros.
  generalize dependent s.
  generalize dependent s'.
  induction A; intros.
  - simpl. simpl in H0.
    apply α_preserves_SN with s; assumption.
  - simpl in H0.
    simpl.
    intros t Ht.
    specialize (H0 t Ht).
    assert (nil ⊢ (tmapp s t) ~ (tmapp s' t)).
    {
      apply alpha_app.
      - assumption.
      - apply alpha_refl. apply alpha_refl_nil.
    }
    specialize (IHA2 (tmapp s' t) (tmapp s t) H1 H0).
    assumption.
Qed.

(* TODO: Compare with Inductive instantiation from normalisation in
  PLF: that has a cleaner definition, but restraints the order*)
Definition EL (Gamma : list (string * type)) 
          (sigma : list (string * term)) : Set :=
  forall x T, lookup x Gamma = Some T ->
    { t & prod (lookup x sigma = Some t) (L T t)}.

(* is true! *)
Lemma extend_EL (Gamma : list (string * type)) (sigma : list (string * term)) x T t :
  EL Gamma sigma -> L T t -> EL ((x, T) :: Gamma) ((x, t) :: sigma).
Proof.
Admitted.

(* Facts about reducible sets. *)

Lemma reducible_sn : reducible SN.
Proof. 
  constructor; eauto using ARS.sn. by move=> s t [f] /f. 
  intros s.  elim: s => //.
Qed.

Global Hint Resolve reducible_sn : core.

Lemma reducible_var P x : reducible P -> P (tmvar x).
Proof. move/p_nc. apply=> // t st. inversion st. Qed.

Lemma L_reducible A :
  reducible (L A).
Proof with eauto using step.
  elim: A => /=[|A ih1 B ih2].
  - apply reducible_sn.
  - constructor.
    + move=> s h. apply: (@sn_closedL (tmvar "x")). apply: (p_sn (P := L B))...
      eapply h. eapply reducible_var; eauto.
    + move=> s t h st u la. apply: (p_cl _ (s := tmapp s u))...
    + move=> s ns h t la.
      have snt := p_sn ih1 la.
      elim: snt la => {} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      (* Note: Case L B ([x := t] s0. By using Autosubst's "inv" instead of normal inversion, this goal vanishes. Why? *) (* Todo: Think, this case doesn't happen in db variant*)
      * apply: ih3 => //. exact: (p_cl ih1) la _.
Qed.

Corollary L_sn A s : L A s -> SN s.
Proof. intros Las. assert (reducible (L A)) by apply (L_reducible A).
   apply (p_sn H). assumption.
Qed.

Corollary L_cl T s t : L T s -> step s t -> L T t.
Proof.
  intros Hstep Hst.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_cl H Hstep); assumption.
Qed.

Corollary L_nc T s :
  neutral s -> (forall t, step s t -> L T t) -> L T s.
Proof. 
  intros Hneut Hstep.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_nc H); assumption.
Qed.

Corollary L_var T x : L T (tmvar x).
Proof.
  apply L_nc; first by []. intros t st. inversion st.
Qed. 

Corollary L_cl_star T s t :
  L T s -> red s t -> L T t.
Proof.
  intros Ls red_st. induction red_st.
  - assumption.
  - apply L_cl with y; assumption.
Qed.

(* Closure under beta expansion. *)
Lemma beta_expansion A B x s t :
  SN t -> L A ([x := t] s) ->
  L A (tmapp (tmlam x B s) t).
Proof with eauto.
  move=> snt h. have sns := sn_subst (L_sn h).
  elim: sns t snt h => {} s sns ih1 t. elim=> {} t snt ih2 h.
  apply: L_nc => // u st. inv st => //.
  - inv H2. apply: ih1 => //. 
    assert ({α & prod (step ([x := t] s) (α)) (nil ⊢ α ~ [x := t] s0)}).
    {
      eapply step_subst.
      assumption.
    }
    destruct H as [alpha [Hred Halpha] ].
    apply (L_cl h) in Hred.
    apply α_preserves_L with (s := alpha); assumption.
  - apply: ih2 => //. 
    assert ({α & prod (nil ⊢ [x := t] s ~ α) (red α ([x := t2] s))}).
    {
      eapply red_beta. assumption.
    }
    destruct H as [alpha [Halpha Hred] ].
    apply α_preserves_L with (s' := alpha) in h.
    + apply (L_cl_star h) in Hred.
      assumption.
    + assumption.
Qed.

Lemma beta_expansion_subst X t sigma s A B :
  SN t -> L A (((X, t)::sigma) [[s]]) -> L A (tmapp (sigma [[tmlam X B s]]) t).
Proof.
  intros snt H.
  remember (fresh2 ((X, tmvar X)::sigma) s) as X'.
  assert (L A ([X' := t] (sigma [[(rename X X' s)]])) -> L A (tmapp (tmlam X' B (sigma [[rename X X' s]])) t)).
  {
    apply beta_expansion; assumption.
  }

  (* Now we use H to show the assumption of H0 holds. Then we rewrite the conclusion into the goal*)
  assert (HsigIntoLam: tmapp (tmlam X' B (sigma [[rename X X' s]])) t = tmapp (sigma [[tmlam X B s]]) t).
  {
    rewrite capms_lam.
    rewrite HeqX'.
    reflexivity.
  }
  rewrite <- HsigIntoLam.
  apply H0.
  assert (HalphaCool: nil ⊢ ([X' := t] (sigma [[rename X X' s]])) ~ ((X, t)::sigma) [[s]]).
  {
    eapply alpha_trans.
    + apply id_left_trans.
    + simpl.
      eapply subs_preserves_alpha.
      * apply alpha_ctx_ren_nil.
      * eapply ren_sub_compose_instantiated.
        assumption.
    + eapply merge_sub.
      change ((X, tmvar X)::sigma) with (((X, tmvar X)::nil) ++ sigma) in HeqX'.
      exact HeqX'.
  }
  eapply alpha_sym in HalphaCool.
  - apply (α_preserves_L HalphaCool H).
  - apply alpha_sym_nil.
Qed.

(** Kinding of types *)
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

(* The fundamental theorem. *)
Theorem soundness Gamma s A :
  has_type Gamma s A -> forall sigma,
    EL Gamma sigma -> L A (sigma [[s]]).
Proof with eauto using L_sn. 
  elim=> {Gamma s A} [Gamma X A |Gamma X A s B _ ih sigma EL|Gamma s t A B _ ih1 _ ih2 sigma HEL].
  - intros HlookupGamma sigma HEL.
    unfold EL in HEL.
    specialize (HEL X A HlookupGamma).
    destruct HEL as [t [HlookupSigma LAt] ].
    apply capms_var in HlookupSigma.
    rewrite HlookupSigma.
    assumption.
  - move=> t h.
    specialize (ih ((X, t)::sigma) (extend_EL EL h)).
    apply: beta_expansion_subst...
  - specialize (ih1 _ HEL). specialize (ih2 _ HEL).
    unfold L in ih1. fold L in ih1. specialize (ih1 (sigma [[t]]) ih2).
    rewrite capms_equation_3.
    assumption.
Qed.

(* Identity substitutions: Given a typing context E, give a list of term substitutions matching this E*)
Fixpoint id_subst (E : list (string * type)) : list (string * term) :=
  match E with
  | nil => nil
  | cons (x, A) E' => cons (x, tmvar x) (id_subst E')
  end.

Lemma id_subst_is_IdSubst E :
  IdSubst (id_subst E).
Proof.
  induction E.
  - constructor.
  - simpl. destruct a. constructor. assumption.
Qed.

(* The identity substitution is in the EL relation *)

Lemma id_subst_EL :
  forall (E : list (string * type)),  EL E (id_subst E).
Proof.
Admitted.

(* The fundamental theorem for named variables. *)
Corollary type_L (E : list (string * type)) s T : has_type E s T -> L T (id_subst E [[s]]).
Proof.
  intros Htype.
  assert (HEL: EL E (id_subst E)) by apply id_subst_EL.
  assert (Hsound: L T ((id_subst E) [[s]])) by apply (soundness Htype HEL).
  assumption.
Qed.

Corollary strong_normalization_alpha E s T : has_type E s T -> SN (id_subst E [[s]]).
Proof.
  intros Hty.
  apply type_L in Hty.
  apply L_sn in Hty.
  assumption.
Qed.

Theorem strong_normalization E s T : has_type E s T -> SN s.
Proof.
  intros Hty.
  remember Hty as Hty_copy; clear HeqHty_copy.
  apply strong_normalization_alpha in Hty.
  apply α_preserves_SN with (s := id_subst E [[s]]).
  eapply alpha_sym. apply alpha_sym_nil.
  apply id_subst_alpha.
  apply id_subst_is_IdSubst.
  assumption.
Qed.

(* Monad maybe*)
(* Define the bind function for option type *)
Definition bind {A B : Type} (xx : option A) (f : A -> option B) : option B :=
  match xx with
  | None => None
  | Some a => f a
  end.

Fixpoint is_normal (t : term) : bool :=
  match t with
  | tmlam X K T => is_normal T
  | tmvar X => true
  | tmapp T1 T2 => is_neutral T1 && is_normal T2
  end

with is_neutral (t : term) : bool :=
  match t with
  | tmvar X => true
  | tmapp T1 T2 => is_neutral T1 && is_normal T2
  | _ => false
  end.

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

(* Define an infix operator for bind *)
Infix ">>=" := bind (at level 50, left associativity).

(* Deterministic step *)
Fixpoint step_d_f (t : term) : option term :=
    match t with
    | tmvar i => None
    | tmapp s t => 
        if is_normal s then
            if is_normal t then
                match s with
                | tmlam x A s' => Some ([x := t] s')
                | _ => None
                end
            else step_d_f t >>= fun t' => Some (tmapp s t')
        else step_d_f s >>= fun s' => Some (tmapp s' t)
    | tmlam x A s => (* step' s >>= _ does the normality check for us implicitly*)
        step_d_f s >>= fun s' => Some (tmlam x A s')
    end.

Inductive step_d : term -> term -> Set :=
| step_beta_d (x : string) (A : type) (s t : term) :
    normal_Ty s ->
    normal_Ty t ->
    step_d (tmapp (tmlam x A s) t) ([x := t] s)
| step_appL_d s1 s2 t :
    step_d s1 s2 -> step_d (tmapp s1 t) (tmapp s2 t)
| step_appR_d s t1 t2 :
    normal_Ty s ->
    step_d t1 t2 -> step_d (tmapp s t1) (tmapp s t2)
| step_abs_d x A s1 s2 :
    step_d s1 s2 -> step_d (tmlam x A s1) (tmlam x A s2).


(* step_nd is a subset of step
This is not true since step_d should use a different kind of substitution (only freshening when necessary)
*)
Lemma step_d_implies_step t t' : step_d t t' -> step t t'.
Proof.
  (* elim=> H; constructor; try assumption. *)
Abort.

Lemma step_d_implies_step_alpha t t' : step_d t t' -> { t'_alpha : term & prod(Alpha [] t' t'_alpha) (step t t'_alpha)}.
Proof.
  intros Hstep.
  induction Hstep.
  - (* this is proving that if substituteTCA x t s is alpha to [x := t] s (capmsfr)*) admit.
  - admit.
  - admit.
  - destruct IHHstep as [IHHt' [IHHalpha IHHstep'] ].
    exists (tmlam x A IHHt').
    split.
    + apply alpha_lam.
      apply alpha_extend_id'.
      * assumption.
      * apply not_break_shadow_nil.
    + apply step_abs.
      assumption.
Admitted.

(* Does this still work now we no longer have step_d_implies_step?
  Maybe if we make it up to alhpa
 *)
Lemma SN_d : forall t, (@sn step) t -> {t_alpha : term & prod (Alpha [] t t_alpha) ((@sn step_d) t_alpha)}.
Proof.
  intros t HSN.
  induction HSN.
  eexists.
  split.
  - admit.
  - (* oof. I dont know how to prove this. Maybe we need a weaker SN notion or something:
    @sn step_d x -> exists z, Alpha [] x z AND forall y, step z y -> SN y
   *)
Admitted.

(* Main lemma for going from using t alpha t' in SN t' to SN t*)
Lemma step_preserves_alpha_d sigma s t s' t' :
  Alpha sigma s t -> step_d s s' -> step_d t t' -> Alpha sigma s' t'.
Proof.
Admitted.

Require Import Coq.Program.Equality.

(*I do not like these lemmas. Maybe we can change the definition of normality to equal not being able to step? *)
Lemma is_normal_no_step_d t :
  is_normal t = true -> step_d_f t = None.
Proof.
Admitted.

Lemma is_normal_then_step_d t :
  is_normal t = false -> ~ step_d_f t = None.
Proof.
Admitted.

(* We also need this for sound/completeness, so we can assume it is true/a good approach*)
Lemma is_normal_then_normal_Ty t : 
  is_normal t = true -> normal_Ty t.
Proof.
Admitted.


Lemma step_d_f_to_step_d : forall t t', step_d_f t = Some t' -> step_d t t'.
Proof.
  intros t t' Hstep_d_f.
  dependent induction t. (* we needed IH over t' *)
  - discriminate.
  - destruct (is_normal t0) eqn: Hnormal_s.
    + apply is_normal_no_step_d in Hnormal_s.
      inversion Hstep_d_f.
      rewrite Hnormal_s in H0.
      inversion H0.
      (* If t0 is normal, then also tmlam s t t0*)
    + destruct (step_d_f t0) eqn: Hstep_t.
      * inversion Hstep_d_f.
        rewrite Hstep_t in H0.
        inversion H0.
        apply step_abs_d.
        specialize (IHt t1).
        apply IHt.
        reflexivity.
      * apply is_normal_then_step_d in Hnormal_s.
        contradiction.
  - inversion Hstep_d_f.
    destruct (is_normal t1) eqn: Hnormal_s.
    + destruct (is_normal t2) eqn: Hnormal_t.
      * destruct t1. (* case step_beta *)
        -- discriminate.
        -- inversion Hnormal_s.
           inversion Hnormal_t.
           inversion H0.
           apply step_beta_d.
           ++ apply is_normal_then_normal_Ty.
              assumption. (* is_normal -> normal_ty, we need that anyway for sound/completeness*)
           ++ apply is_normal_then_normal_Ty.
              assumption.
        -- discriminate.
      * destruct (step_d_f t2) eqn: Hstep_t. (* IH was not strong enough, so dependent induction *)
        -- inversion H0.
           apply step_appR_d.
           ++ apply is_normal_then_normal_Ty.
              assumption.
           ++ apply IHt2. 
              reflexivity.
        -- discriminate.
    + destruct (step_d_f t1) eqn: Hstep_s.
      * inversion H0.
        apply step_appL_d.
        apply IHt1.
        reflexivity.
      * discriminate.
Qed.

(* eq_refl didnt work, this does, thank Copilot, but I dont understand *)
Lemma eq_proof {A : Type} (x : A) : x = x.
Proof. reflexivity. Qed.

(* Terminating normalization procedure helper.
  We can normalize a term given that we know that an 
  alpha equivalent term is strongly normalizing
*)
Fixpoint normalizer' {sigma : list (string * string)} (t t' : term) (HAlpha : Alpha sigma t t') (HSN : (@sn step_d) t') : term :=
  match step_d_f t as res return (step_d_f t = res -> term) with
  | None => fun _ => t
  | Some t1 => fun Hstep =>
      match step_d_f t' as res' return (step_d_f t' = res' -> term) with
      | None => fun _ => t1 (* Uhm. Cannot happen. How to show this to coq? *)
      | Some t'1 => fun Hstep' =>
          let HStep_d := step_d_f_to_step_d Hstep in
          let HStep_d' := step_d_f_to_step_d Hstep' in
          let HAlpha' := step_preserves_alpha_d HAlpha HStep_d HStep_d' in
          let HSN' := match HSN with
                      | SNI f => f t'1 HStep_d'
                      end in
          @normalizer' sigma t1 t'1 HAlpha' HSN'
      end (eq_proof (step_d_f t'))
  end (eq_proof (step_d_f t)).

(* Normalization procedure for well typed terms *)
Definition normalizer E T (t : term) (Htype : has_type E t T) : term :=
  let t' := id_subst E [[t]] in
  let HSN := strong_normalization Htype in
  let (t'', p ) := SN_d HSN in
  let (HAlpha', SNstep_d_t'') := p in
      @normalizer' [] t t'' HAlpha' SNstep_d_t''.


(* Local Variables: *)
(* coq-load-path: (("." "Ssr")) *)
(* End: *)


