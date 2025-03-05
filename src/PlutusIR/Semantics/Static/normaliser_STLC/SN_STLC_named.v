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
From PlutusCert Require Import alpha_rename alpha rename util alpha_ctx_sub freshness alpha_freshness step alpha_sub.

From PlutusCert Require Import alpha_step.



(* ********************
      Beta reduction
*)


Global Hint Resolve red_app red_abs 
(* sred_hup  *)
: red_congr.


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
    ( red (((x, t1)::(x, t2)::nil) [[s']]) a) (* ugly cheating, adding (x, t2) just for more freshness guarantees*)
    ( ren ⊢ a ~ (((x, t2)::(x, t1)::nil) [[s'']])) }. (* Ugly cheat: adding the x, t1 makes sure it does not generate fresh vars equal to ftv of t1...*)
Proof. 

  intros Hstep.
  induction s; intros s' s'' ren1 ren2 ren HalphaS1 HalphaS2 Halphat1 Halphat2 Halphax HalphaTrans.
  - inversion HalphaS1; subst.
    inversion HalphaS2; subst.
    assert (Hx0y: AlphaVar ren x0 y). { eapply alpha_var_trans; eauto. }
    destr_eqb_eq x0 x.
    + assert (y = x). { apply (alphavar_unique_right Halphax) in Hx0y. symmetry. auto. } subst.
      repeat rewrite capms_var_helper.
      exists t2.
      split.
      * eapply starSE. apply starR. assumption.
      * assumption.
    + assert (y <> x). { apply (alphavar_unique_not_left H Hx0y) in Halphax. symmetry. auto. }
      rewrite capms_var_multi_not; auto.
      rewrite capms_var_single_not; auto.
      rewrite capms_var_multi_not; auto.
      rewrite capms_var_single_not; auto.
      exists (tmvar x0).
      split.
      * apply starR.
      * apply alpha_var.
        assumption.
  - (* tmlam *)
    inversion HalphaS1; subst.
    inversion HalphaS2; subst.
    autorewrite with capms; simpl.
    remember (fresh2 _ s1) as b1.
    remember (fresh2 _ s3) as b2.

    specialize (IHs (rename x0 b1 s1) (rename y b2 s3) ((b1, s)::ren1) ((s, b2)::ren2) ((b1, b2)::ren)).
    assert ({a : term & prod
        
        (red (((x, t1)::(x, t2)::nil) [[rename x0 b1 s1]]) a ) 
        (((b1, b2)::ren) ⊢ a ~ (((x, t2)::(x, t1)::nil) [[rename y b2 s3]] ))
        }) as [a' [Halpha' Hstep'] ].
    {
      eapply IHs.
      - eapply alpha_trans_rename_left; eauto.
      - eapply alpha_trans_rename_right; eauto. 
      - apply alpha_extend_fresh; auto; intros Hcontra; apply extend_ftv_to_tv in Hcontra.
        + eapply fresh2_over_tv_value_sigma with (X := x) (s := t1) in Heqb1; eauto with *.
        + eapply fresh2_over_tv_value_sigma with (X := x) (s := t1) in Heqb2; eauto with *.
      - apply alpha_extend_fresh; auto; intros Hcontra; apply extend_ftv_to_tv in Hcontra.
        + eapply fresh2_over_tv_value_sigma with (X := x) (s := t2) in Heqb1; eauto with *.
        + eapply fresh2_over_tv_value_sigma with (X := x) (s := t2) in Heqb2; eauto with *.
      - apply alpha_var_diff; auto; eapply fresh2_over_key_sigma with (X := x) (s := t2); eauto with *.
      - apply alpha_trans_cons.
        eauto.
    
    }
    eexists.
    split.
    + apply red_abs.
      exact Halpha'.
    + apply alpha_lam.
      exact Hstep'.
  - (* tmapp *)
    inversion HalphaS1; subst.
    inversion HalphaS2; subst.
    autorewrite with capms.
    specialize (IHs1 s0 s4 ren1 ren2 ren).
    specialize (IHs1 H3 H2 Halphat1 Halphat2 Halphax HalphaTrans) as [a1 [Hred1 Halpha1] ].
    specialize (IHs2 t0 t4 ren1 ren2 ren).
    specialize (IHs2 H4 H6 Halphat1 Halphat2 Halphax HalphaTrans) as [a2 [Hred2 Halpha2] ].
    exists (tmapp a1 a2).
    split.
    + eapply red_app; auto.
    + apply alpha_app; auto.
Qed.

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
    (red (((x, t1)::(x, t2)::nil) [[s']]) a)
    ( ren ⊢ a ~ (((x, t2)::(x, t1)::nil) [[s'']])) }) as [a [Halpha Hred] ].
  {
    eapply red_beta''; eauto.
  }

  assert (nil ⊢ ((x, t1)::(x, t2)::nil) [[s']] ~ ((x, t1)::nil) [[s']]).
  {
    apply @alpha_sym with (ren := nil) (ren' := nil); [apply alpha_sym_nil|].
    eapply add_vacuous.
    - apply alpha_refl. apply alpha_refl_nil.
    - apply alpha_refl. apply alpha_refl_nil.
    - apply alpha_refl. apply alpha_refl_nil.
    - apply alpha_var_refl.
    - apply alpha_trans_nil.
  }
  assert ({b & prod (red (((x, t1)::nil) [[s']]) b) (nil ⊢ a ~ b) }).
  {
    now apply (red_preserves_alpha nil H6) in Halpha.
  }
  destruct H7 as [b [Hredb Halphab] ].
  exists b.
  split.
  - assumption.
  - eapply alpha_trans.
    + apply id_left_trans.
    + eapply @alpha_sym with (ren' := nil) in Halphab; [|apply alpha_sym_nil].
      change (ctx_id_left ren) with (nil ++ ctx_id_left ren).
      apply alpha_extend_ids_right.
      * apply ctx_id_left_is_id.
      * exact Halphab.
    + {
    eapply alpha_trans.
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
    }
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
  (* apply A in C. *)
  (* intros C. *)
  (* apply A in C. *)
  (* revert C. *)
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
  (forall x y, step x y -> {y_h & prod (step (h x) y_h) (nil ⊢ y_h ~ (h y))}) -> @sn step v -> nil ⊢ v ~ h x -> @sn step x.
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
  assert ({y_h' & prod (step x y_h') (nil ⊢ y_h' ~ h y)}).
  {
    destruct C as [yh [ehy yh_alpha] ].
    eapply alpha_sym in eqn; [|apply alpha_sym_nil].
    apply (step_preserves_alpha nil eqn) in ehy.
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
  (forall x y, step x y -> {y_h & prod (step (h x) y_h) (nil ⊢ y_h ~ (h y))}) -> @sn step (h x) -> @sn step x.
Proof.
  intros A B.
  apply sn_preimage_α' with (v := h x) (h := h); eauto.
  apply alpha_refl. apply alpha_refl_nil.
Qed.

Notation SN := (@sn step).

Lemma sn_closedL t s : SN (tmapp s t) -> SN s.
Proof. apply: (sn_preimage (h := tmapp^~t)) => x y. exact: step_appL. Qed.

Lemma sn_subst X T s : SN ([X := T] s) -> SN s.
Proof.
  apply: (sn_preimage_α (h := capms ((X, T)::nil))) => x y.  exact: step_subst_sigma.
Qed.

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

Fixpoint Lα (T : type) : cand :=
match T with
  | tp_base => SN 
  | tp_arrow A B => fun s => forall t, Lα A t -> {t' & nil ⊢ t ~ t' * Lα B (tmapp s t')}
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
  SN t -> L A ([x := t] s) -> (* To add: s unique binders wrt freevars t*)
  L A (tmapp (tmlam x B s) t).
Proof with eauto.
  move=> snt h. have sns := sn_subst (L_sn h).
  elim: sns t snt h => {} s sns ih1 t. elim=> {} t snt ih2 h.
  apply: L_nc => // u st. inv st => //.
  - inv H2. apply: ih1 => //. 
    assert ({α & prod (step ([x := t] s) (α)) (nil ⊢ α ~ [x := t] s0)}) 
      as [alpha [Hred Halpha] ] by now eapply step_subst_sigma.
    apply (L_cl h) in Hred.
    apply α_preserves_L with (s := alpha); assumption.
  - apply: ih2 => //. 
    assert ({α & prod (red ([x := t] s) α) (nil ⊢ α ~ ([x := t2] s))}) 
      as [alpha [Hred Halpha] ] by now eapply red_beta.
    apply (L_cl_star h) in Hred.
    now apply α_preserves_L with (s := alpha).
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
    (* We would have to change here to an s that is alpha to actual s 
    and is globally unique wrt t
    can we also do that in ih? yes by subs_preserves_alpha
    *)
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

Lemma normal_Ty_dec : forall t, {normal_Ty t} + {~normal_Ty t}.
Proof.
  intros t.
  induction t.
  - left. constructor. constructor.
  - destruct IHt.
    + left. constructor. auto.
    + right. intros Hcontra. inversion Hcontra. 
      * subst. contradiction.
      * subst. inversion H.
  - destruct IHt1; destruct IHt2.
    (* + 
    + right. intros Hcontra. inversion Hcontra.
      * subst. contradiction.
      * subst. inversion H.
    + right. intros Hcontra. inversion Hcontra.
      * subst. contradiction.
      * subst. inversion H.
    + right. intros Hcontra. inversion Hcontra.
      * subst. contradiction.
      * subst. inversion H. *)
  (* Prove decidability here, or assume it if it is clear. *)
Admitted.

Lemma alpha_preserves_normal_Ty s s' R :
  R ⊢ s ~ s' -> normal_Ty s -> normal_Ty s'.
Proof.

(* a normal_Ty cannot step.
Suppose s' steps. Then by alpha_preserves_step we have that there is a corresponding step for s. Contradiction.
*)
Admitted.

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
                | tmlam x A s' => Some (substituteTCA x t s')
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
    step_d (tmapp (tmlam x A s) t) (substituteTCA x t s) (* conservative substitutions *)
| step_appL_d s1 s2 t :
    step_d s1 s2 -> step_d (tmapp s1 t) (tmapp s2 t)
| step_appR_d s t1 t2 :
    normal_Ty s ->
    step_d t1 t2 -> step_d (tmapp s t1) (tmapp s t2)
| step_abs_d x A s1 s2 :
    step_d s1 s2 -> step_d (tmlam x A s1) (tmlam x A s2).

Notation SN_d := (@sn step_d).

Lemma orb_false_elim : forall a b : bool,
  orb a b = false -> a = false /\ b = false.
Proof.
  intros a b H.
  destruct a, b; simpl in H; try discriminate; auto.
Qed.

(* I really don't want to have to write such fundamental lemmas that have nothing to do with what I am proving*)
Lemma existsb_false_to_in_dec y l :
  existsb (String.eqb y) l = false -> ~ In y l.
Proof.
  intros Hexistsb.
  induction l.
  - simpl. auto.
  - simpl. intros Hcontra.
    unfold existsb in Hexistsb.
    destruct (y =? a) eqn:yisa.
    + simpl in Hexistsb.
      discriminate.
    + destruct Hcontra.
      * subst. rewrite String.eqb_refl in yisa. discriminate.
      * simpl in Hexistsb. apply IHl in Hexistsb.
        contradiction.
Qed.

(* Liberal and conservative subsitutions are alpha equivalent
  (which is why we are allowed to use liberal substitutions)
*)
Lemma lib_con_sub_alpha_stronger x s t : forall s' s'' ren ren1 ren2,
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  αCtxTrans ren1 ren2 ren ->
  ren ⊢ tmvar x ~ tmvar x ->
  ren ⊢ t ~ t ->
  ren ⊢ [x := t] s' ~ substituteTCA x t s''.
Proof.
  induction s; intros s' s'' ren ren1 ren2 Halphas' Halphas'' Htrans Halphax Halphat.
  - inversion Halphas'; subst.
    inversion Halphas''; subst.
    (* destr eqb here and then use capms_var_helper?*)
    destr_eqb_eq x x0.
    {
      rewrite capms_var_helper.
      assert (x0 = y).
      {
        apply alphavar_unique_right with (X := x0) (ren := ren).
        - inversion Halphax. assumption.
        - eapply alpha_var_trans; eauto.
      }
      subst.
      autorewrite with substituteTCA.
      rewrite String.eqb_refl.
      assumption.
    }
    {
      assert (x <> y).
      {
        apply alphavar_unique_not_left with (X := x) (X' := x0) (ren := ren).
        - assumption.
        - inversion Halphax; assumption.
        - eapply alpha_var_trans; eauto.
      }
      rewrite capms_var_single_not.
      autorewrite with substituteTCA.
      rewrite <- String.eqb_neq in H0.
      rewrite H0.
      apply alpha_var.
      eapply alpha_var_trans; eauto.
      assumption.
    }
  - inversion Halphas'; subst.
    inversion Halphas''; subst.
    autorewrite with capms.
    simpl.
    remember (fresh2 _ s1) as b1.
    autorewrite with substituteTCA.
    destr_eqb_eq x y.
    { (* There is no substitution *)

      remember (fresh2 _ s1) as b1.
      apply alpha_lam.
      destr_eqb_eq x0 y.
      {
        remember (fresh2 _ s1) as b1.
        assert (~ In y (ftv (rename y b1 s1))).
        {
          apply ftv_not_in_after_rename.
          symmetry.
          eapply fresh2_over_key_sigma; eauto with *.
        }
        eapply alpha_trans.
        - apply id_left_trans.
        - change (ctx_id_left ((b1, y)::ren)) with (nil ++ ctx_id_left ((b1, y)::ren)).
          apply alpha_extend_ids_right.
          + apply ctx_id_left_is_id.
          + now apply sub_vacuous_single.
        - eapply alpha_trans.
          * apply alpha_trans_cons. eauto.
          * eapply alpha_trans_rename_left; eauto.
          * exact H5.
      } 
      {
        assert (Hynotins1: ~ In y (ftv s1)).
        {
          intros Hcontra.
          assert (In y (ftv (tmlam x0 t0 s1))).
          {
            simpl.
            apply in_remove.
            split.
            - assumption.
            - auto.
          }
          assert (In y (ftv (tmlam y t0 s3))).
          {
            eapply alpha_preserves_ftv.
            - exact H0.
            - eapply alpha_trans; eauto.
            - inversion Halphax.
              assumption.
          }
          simpl in H1.
          apply in_remove in H1 as [_ ynoty].
          contradiction.
        }

        assert (Hynotafterrename: ~ In y (ftv (rename x0 b1 s1))).
        {
          apply ftv_not_in_rename.
          - symmetry; eapply fresh2_over_key_sigma; auto with *.
          - assumption.
        }
        eapply alpha_trans.
        - apply id_left_trans.
        - change (ctx_id_left ((b1, y)::ren)) with (nil ++ ctx_id_left ((b1, y)::ren)).
          apply alpha_extend_ids_right.
          + apply ctx_id_left_is_id.
          + now apply sub_vacuous_single.
        - eapply alpha_trans.
          * apply alpha_trans_cons. eauto.
          * eapply alpha_trans_rename_left; eauto.
          * exact H5.
      }
    }
    {
      destruct (existsb (String.eqb y) (ftv t)) eqn:Hftv.
      {
        
        (* it exists, so we need to avoid capture, so they are identical*)
        simpl.
        remember (fresh2 _ s3) as b2. (* Uhm, different fresh! oof *)
        apply alpha_lam.
        eapply IHs with (s' := rename x0 b1 s1) (s'' := (rename y b2 s3)).
        - eapply alpha_trans_rename_left; eauto.
        - eapply @alpha_trans with (ren := (s, y)::ren2) (ren' := (y, b2)::(ctx_id_right ren2)).
          + apply alpha_trans_cons.
            apply id_right_trans.
          + exact H5.
          + change ((y, b2):: ctx_id_right ren2) with (((y, b2)::nil) ++ ctx_id_right ren2).
            apply alpha_extend_ids_right.
            * apply ctx_id_right_is_id.
            * apply alphaRename.
              now apply fresh2_over_tv_term in Heqb2.
        - apply alpha_trans_cons.
          eauto.
        - apply alpha_var. apply alpha_var_diff; [| |inversion Halphax; assumption ];
          eapply fresh2_over_key_sigma with (X := x) (s := t); auto with *.
        - apply alpha_extend_fresh; auto.
          + intros Hcontra; apply extend_ftv_to_tv in Hcontra. eapply fresh2_over_tv_value_sigma with (X := x) (s := t) in Heqb1; [contradiction | auto with *].
          + intros Hcontra; apply extend_ftv_to_tv in Hcontra; eapply fresh2_over_tv_value_sigma with (X := x) (s := t); eauto with *.
          
      }
      {
        apply alpha_lam.
        eapply IHs with (s' := rename x0 b1 s1) (s'' := s3) (ren2 := ((s, y)::ren2)) (ren1 := ((b1, s)::ren1)).
        - eapply alpha_trans_rename_left; eauto.
        - exact H5.
        - apply alpha_trans_cons.
          eauto.
        - apply alpha_var. apply alpha_var_diff; [| |inversion Halphax]; auto.
          eapply fresh2_over_key_sigma with (X := x) (s := t); auto with *.
        - apply alpha_extend_fresh; auto. 
          + eapply fresh2_over_tv_value_sigma with (X := x) (s := t) in Heqb1; eauto with *. 
            intros Hcontra.
            apply extend_ftv_to_tv in Hcontra.
            contradiction.
          + now apply existsb_false_to_in_dec in Hftv.
      }
    }
  
  - inversion Halphas'; subst.
    inversion Halphas''; subst.
    autorewrite with capms.
    autorewrite with substituteTCA.
    apply alpha_app.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto.
Qed.

Lemma lib_con_sub_alpha x s t :
  nil ⊢ [x := t] s ~ substituteTCA x t s.
Proof.
  eapply lib_con_sub_alpha_stronger; eauto.
  - eapply alpha_refl. eapply alpha_refl_nil.
  - eapply alpha_refl. eapply alpha_refl_nil.
  - apply alpha_trans_nil.
  - apply alpha_refl. apply alpha_refl_nil.
  - apply alpha_refl. apply alpha_refl_nil.
Qed.

Lemma alpha_capms_to_naive X U T:
  {T' & Alpha [] T T' * Alpha [] (substituteTCA X U T) (substituteT X U T')}.
Proof.
Admitted.

Lemma alpha_rename_binder_substituteT {y : string } {s : term} s' x t t' ren:
  Alpha ((x, y)::ren) s s' ->
  Alpha ren t t' ->
  Alpha ren (substituteT x t s) (substituteT y t' s').
Proof.
(* My assumption is that this is easier than for substituteTCA*)
Admitted.

(* step_nd is a subset of step
This is not true since step_d should use a different kind of substitution (only freshening when necessary)
*)
Lemma step_d_implies_step t t' u ren : step_d t t' -> (ren ⊢ t ~ u) -> {t_α & prod (step u t_α) (Alpha ren t' t_α)}.
Proof.
  intros Hstep Halpha.
  generalize dependent u.
  generalize dependent ren.
  induction Hstep; intros ren u Halpha; inversion Halpha; subst.
  - inversion H2; subst.
    exists ([y := t2] s0).
    split.
    + apply step_beta.
    + eapply alpha_trans.
      * apply id_left_trans.
      * change (ctx_id_left ren) with (nil ++ ctx_id_left ren).
        apply alpha_extend_ids_right.
        -- apply ctx_id_left_is_id.
        -- eapply alpha_sym. apply alpha_sym_nil.
           apply lib_con_sub_alpha.
      * eapply alpha_rename_binder; assumption.
  - destruct (IHHstep ren s3 H2) as [s2_α [IHHstep' IHHalpha'] ].
    exists (tmapp s2_α t2); split.
    + apply step_appL. assumption.
    + apply alpha_app.
      * assumption.
      * assumption.
  - destruct (IHHstep ren t3 H4) as [t2_α [IHHstep' IHHalpha'] ].
    exists (tmapp s2 t2_α); split.
    + apply step_appR. assumption.
    + apply alpha_app.
      * assumption. 
      * assumption.
  - destruct (IHHstep ((x, y)::ren) s3 H4) as [s2_α [IHHstep' IHHalpha'] ].
    exists (tmlam y A s2_α); split.
    + apply step_abs. assumption.
    + apply alpha_lam. assumption.
Qed.

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

Lemma SN_nd_to_SN_d t : (@sn step) t -> (@sn step_d) t.
Proof.
  intros Hsn_nd.
  apply SNI.
  intros t' Hstep.
  generalize dependent t'.
  induction Hsn_nd; intros t Hstep_d.
  assert (Hstep_alpha: {t' & prod (step x t') (Alpha nil t t')}).
  {
    eapply step_d_implies_step; eauto.
    eapply alpha_refl; apply alpha_refl_nil.
  }
  destruct Hstep_alpha as [t' [Hstep Halpha] ].
  specialize (H t' Hstep).
  apply α_preserves_sn_d with t'.
  - eapply alpha_sym; [apply alpha_sym_nil |].
    assumption.
  - apply SNI. 
    exact H.
Qed.

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


(* We also need this for sound/completeness, so we can assume it is true/a good approach
    Mutual induction with neutral?
*)
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



Theorem strong_normalization_d E s T : has_type E s T -> SN_d s.
Proof.
  intros Htype.
  apply (strong_normalization) in Htype.
  apply SN_nd_to_SN_d.
  assumption.
Qed.
  


(* Local Variables: *)
(* coq-load-path: (("." "Ssr")) *)
(* End: *)


