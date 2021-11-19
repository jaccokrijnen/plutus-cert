Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.



(** * Helper lemmas *)

Lemma subst_b__preserves_bindsD : forall b v x,
    binds_Delta <{ [v / x][b] b }> = binds_Delta b.
Proof with eauto.
  intros.
  destruct b.
  all: simpl.
  - destruct v0...
  - destruct t...
  - destruct d...
Qed.

Lemma subst_b__preserves_bindsG : forall b v x,
    binds_Gamma <{ [v / x][b] b }> = binds_Gamma b.
Proof with eauto.
  intros.
  destruct b.
  all: simpl.
  - destruct v0...
  - destruct t...
  - destruct d...
Qed.

Lemma subst_bnr__preserves_bindsD : forall bs v x,
    map binds_Delta <{ [v / x][bnr] bs }> = map binds_Delta bs.
Proof with eauto.
  induction bs; intros...
  - simpl.
    destruct (existsb (eqb x) (bvb a)).
    all: simpl.
    all: f_equal.
    all: eauto using subst_b__preserves_bindsD.
Qed.

Lemma subst_bnr__preserves_bindsG : forall bs v x,
    map binds_Gamma <{ [v / x][bnr] bs }> = map binds_Gamma bs.
Proof with eauto.
  induction bs; intros...
  - simpl.
    destruct (existsb (eqb x) (bvb a)).
    all: simpl.
    all: f_equal.
    all: eauto using subst_b__preserves_bindsG.
Qed.

Lemma subst_br__preserves_bindsD : forall bs v x,
    map binds_Delta <{ [v / x][br] bs }> = map binds_Delta bs.
Proof with eauto.
  induction bs; intros...
  - simpl.
    f_equal.
    all: eauto using subst_b__preserves_bindsD.
Qed.

Lemma subst_br__preserves_bindsG : forall bs v x,
    map binds_Gamma <{ [v / x][br] bs }> = map binds_Gamma bs.
Proof with eauto.
  induction bs; intros...
  - simpl.
    f_equal.
    all: eauto using subst_b__preserves_bindsG.
Qed.

(** * Propositions *)

Definition P_Term (t : Term) :=
  forall Delta Gamma x U Un v T,
    Delta ,, (x |-> U; Gamma) |-+ t : T ->
    normalise U Un ->
    empty ,, empty |-+ v : Un ->
    Delta ,, Gamma |-+ <{ [v / x] t }> : T.

Definition P_Binding (b : Binding) : Prop :=
  forall Delta Gamma x U Un v,
    Delta ,, (x |-> U; Gamma) |-ok_b b ->
    normalise U Un ->
    empty ,, empty |-+ v : Un ->
    Delta ,, Gamma |-ok_b <{ [v / x][b] b }>.

#[export] Hint Unfold
  P_Term
  P_Binding
  : core.



(** * Binding sequences *)

Lemma SPT__Bindings_NonRec : forall bs,
    Util.ForallP P_Binding bs ->
    forall Delta Gamma x U Un v,
      Delta ,, (x |-> U; Gamma) |-oks_nr bs ->
      normalise U Un ->
      empty ,, empty |-+ v : Un ->
      Delta ,, Gamma |-oks_nr <{ [v / x][bnr] bs }>.
Proof with (eauto with typing).
  induction bs. all: intros...
  - simpl.
    inversion H0. subst.
    destruct (existsb (eqb x) (bvb a)) eqn:Hexb.
    + eapply W_ConsB_NonRec...
      * eapply Util.ForallP_hd in H.
        eapply H...
      * rewrite subst_b__preserves_bindsG...
      * rewrite subst_b__preserves_bindsD...
        eapply existsb_exists in Hexb.
        destruct Hexb as [x0 [HIn Heqb]].
        apply eqb_eq in Heqb as Heq.
        subst.
        apply In_bvb_bindsG in HIn.
        eapply In__map_normalise in H8...
        rewrite mupdate_shadow_In in H9...
    + eapply W_ConsB_NonRec...
      * eapply Util.ForallP_hd in H.
        eapply H...
      * rewrite subst_b__preserves_bindsG...
      * rewrite subst_b__preserves_bindsD...
        eapply IHbs...
        -- eapply Util.ForallP_tl...
        -- eapply Util.existsb_nexists in Hexb.
           assert (~ In x (bvb a)). {
             intros Hcon.
             apply Hexb.
             exists x.
             split...
             apply eqb_refl.
           }
           apply notIn_bvb_bindsG in H3.
           eapply notIn__map_normalise in H8...
           rewrite mupdate_permute_In in H9...
Qed.

Lemma SPT__Bindings_Rec : forall bs,
    Util.ForallP P_Binding bs ->
    forall Delta Gamma x U Un v,
      Delta ,, (x |-> U; Gamma) |-oks_r bs ->
      normalise U Un ->
      empty ,, empty |-+ v : Un ->
      Delta ,, Gamma |-oks_r <{ [v / x][br] bs }>.
Proof with (eauto with typing).
  induction bs. all: intros...
  - simpl.
    inversion H0. subst.
    eapply W_ConsB_Rec...
    + eapply Util.ForallP_hd in H...
    + eapply Util.ForallP_tl in H...
Qed.



(** * Main lemmas *)

Lemma substitution_preserves_typing : 
  (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof with eauto.
  apply Term__multind with 
    (P := P_Term) 
    (Q := P_Binding).
  all: intros; autounfold; intros.
  all: try solve [try (inversion H || inversion H0 || inversion H1); subst; eauto with typing].
  - inversion H1. all: subst.
    + simpl.
      destruct (existsb (eqb x) (bvbs bs)) eqn:Hexb.
      * eapply T_Let...
        -- rewrite subst_bnr__preserves_bindsG...
        -- eapply SPT__Bindings_NonRec...
        -- rewrite subst_bnr__preserves_bindsD...
            eapply existsb_exists in Hexb.
            destruct Hexb as [x0 [HIn Heqb]].
            apply eqb_eq in Heqb as Heq.
            subst.
            apply In_bvbs_bindsG in HIn.
            eapply In__map_normalise in HIn...
            rewrite mupdate_shadow_In in H14...
      * eapply T_Let...
        -- rewrite subst_bnr__preserves_bindsG...
        -- eapply SPT__Bindings_NonRec...
        -- rewrite subst_bnr__preserves_bindsD...
           eapply H0...
            eapply Util.existsb_nexists in Hexb.
            assert (~ In x (bvbs bs)). {
              intros Hcon.
              apply Hexb.
              exists x.
              split...
              apply eqb_refl.
            }
            apply notIn_bvbs_bindsG in H4.
            eapply notIn__map_normalise in H4...
            rewrite mupdate_permute_In in H14...
    + simpl.
      destruct (existsb (eqb x) (bvbs bs)) eqn:Hexb.
      * eapply existsb_exists in Hexb.
        destruct Hexb as [x0 [HIn Heqb]].
        apply eqb_eq in Heqb as Heq.
        subst.
        apply In_bvbs_bindsG in HIn.
        eapply In__map_normalise in HIn...
        rewrite mupdate_shadow_In in H12...
        rewrite mupdate_shadow_In in H14...
        eapply T_LetRec...
      * eapply Util.existsb_nexists in Hexb.
        assert (~ In x (bvbs bs)). {
          intros Hcon.
          apply Hexb.
          exists x.
          split...
          rewrite eqb_refl...
        }
        apply notIn_bvbs_bindsG in H4...
        eapply notIn__map_normalise in H4...
        rewrite mupdate_permute_In in H12...
        rewrite mupdate_permute_In in H14...
        eapply T_LetRec...
        -- rewrite subst_br__preserves_bindsG...
        -- rewrite subst_br__preserves_bindsD...
            eapply SPT__Bindings_Rec...
        -- rewrite subst_br__preserves_bindsD...
  - (* Var *)
    simpl.
    destruct (x =? s)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      inversion H.
      subst.
      rewrite update_eq in H3.
      inversion H3. subst.
      assert (Un = T) by eauto using normalisation__deterministic.
      subst.
      eapply Typing.weakening_empty; eauto.
    + apply eqb_neq in Heqb as Hneq.
      inversion H. subst.
      eapply T_Var...
      rewrite update_neq in H3...
  - (* LamAbs *)
    inversion H0. subst.
    simpl.
    destruct (x =? s)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq. 
      subst.
      apply T_LamAbs...
      rewrite update_shadow in H11...
    + apply eqb_neq in Heqb as Hneq.
      apply T_LamAbs...
      rewrite update_permute in H11...
Qed.

Corollary substitution_preserves_typing__Term : forall t Delta Gamma x U Un v T,
    Delta ,, (x |-> U; Gamma)  |-+ t : T ->
    normalise U Un ->
    empty ,, empty |-+ v : Un ->
    Delta ,, Gamma |-+ <{ [v / x] t }> : T.
Proof. apply substitution_preserves_typing. Qed.

Corollary substitution_preserves_typing__Binding : forall b Delta Gamma x U Un v,
    Delta ,, (x |-> U; Gamma) |-ok_b b ->
    normalise U Un ->
    empty ,, empty |-+ v : Un ->
    Delta ,, Gamma |-ok_b <{ [v / x][b] b }>.
Proof. apply substitution_preserves_typing. Qed.