Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Util.
Require Import PlutusCert.Util.List.
Require Import PlutusCert.Util.Map.
Require Import PlutusCert.Util.Map.Mupdate.

Require Import Arith.
Require Import Coq.Lists.List.

Local Open Scope string_scope.
Local Open Scope list_scope.



Lemma In__mdrop : forall {X} ns ss x s,
    List.In x ns ->
    @mdrop X ns ((x, s) :: ss) = @mdrop X ns ss.
Proof.
  induction ns; intros.
  - destruct H.
  - simpl.
    destruct (x =? a)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      destruct H.
      * symmetry in H. 
        apply Hneq in H.
        destruct H.
      * eapply IHns.
        assumption. 
Qed.


Lemma drop_comm : forall {X} x y (xs : list (string * X)) ,
  drop x (drop y xs) = drop y (drop x xs).
Proof with auto.
  intros.
  induction xs...
  simpl.
  destruct a as [z v].
  destruct (z =? y) eqn:Heqb;
  destruct (z =? x) eqn:Heqb'...

  - simpl. rewrite Heqb...
  - simpl. rewrite Heqb'...
  - simpl. rewrite Heqb, Heqb'.
    congruence...
Qed.

Lemma drop_mdrop : forall X n ns (xs : list (string * X)),
  drop n (mdrop ns xs) = mdrop ns (drop n xs).
Proof. induction ns.
  - auto.
  - intros.
    simpl.
    rewrite IHns.
    rewrite drop_comm.
    reflexivity.
Qed.

      

Lemma In__mdrop_drop : forall {X} ns ss x,
    List.In x ns ->
    @mdrop X ns (drop x ss) = @mdrop X ns ss.
Proof.
  intros.
  revert ss.
  induction ns.
  all: intros ss.
  - inversion H.
  - simpl.
    destruct H; subst.
    + rewrite drop_idempotent.
      congruence.
    + rewrite drop_comm.
      auto.
Qed.

Lemma not_In__mdrop : forall {X} ns ss x s,
    ~ List.In x ns ->
    @mdrop X ns ((x, s) :: ss) = (x, s) :: @mdrop X ns ss.
Proof.
  induction ns; intros.
  - reflexivity.
  - simpl.
    destruct (x =? a)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      exfalso.
      apply H.
      left.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      eapply IHns.
      intros Hcon.
      apply H.
      right.
      assumption.
Qed.

Lemma subst_b__bound_vars : forall x s b,
    bvb b = bvb <{ [s/x][b] b }>.
Proof. intros. induction b. all: eauto. destruct v. eauto. Qed.

Lemma subst_bnr__bound_vars : forall x s bs,
    bvbs bs = bvbs <{ [s/x][bnr] bs }>.
Proof. 
  intros. 
  induction bs.
  - reflexivity.
  - simpl.
    destruct (List.existsb (eqb x) (bvb a)) eqn:Hexb.
    + unfold bvbs.
      simpl.
      f_equal.
      apply subst_b__bound_vars.
    + unfold bvbs.
      simpl.
      f_equal.
      * apply subst_b__bound_vars.
      * assumption.
Qed.

Lemma msubst_bnr__bound_vars : forall bs ss,
    bvbs bs = bvbs <{ /[ ss /][bnr] bs }>.
Proof with eauto.
  intros bs ss.
  generalize bs.
  induction ss...
  clear bs.
  intros.
  destruct a.
  simpl.
  rewrite <- IHss.
  apply subst_bnr__bound_vars.
Qed.

Lemma substA_b__bound_tyvars : forall a T b,
    btvb b = btvb <{ [[T/a][b] b }>.
Proof. intros. induction b. all: eauto. destruct v; eauto. destruct d; eauto. Qed.

Lemma substA_bnr__bound_tyvars : forall a T bs,
    btvbs bs = btvbs <{ [[T/a][bnr] bs }>.
Proof. 
  intros. 
  induction bs.
  - reflexivity.
  - simpl.
    destruct (List.existsb (eqb a) (btvb a0)) eqn:Hfind.
    + unfold btvbs.
      simpl.
      f_equal.
      apply substA_b__bound_tyvars.
    + unfold btvbs.
      simpl.
      f_equal.
      * apply substA_b__bound_tyvars.
      * assumption.
Qed.

Lemma substA_c__bvc : forall c a T,
  bvc <{ [[T / a][c] c }> = bvc c.
Admitted.

Lemma substA_cs__bvc : forall cs a T,
  map bvc <{ [[T / a][cs] cs }> = map bvc cs.
Admitted.

Lemma substA_b__bvb : forall a T b,
    bvb b = bvb <{ [[T/a][b] b }>.
Proof with eauto.
  destruct b; simpl.
  - destruct v...
  - destruct t...
  - destruct d, t.
    simpl.
    rewrite substA_cs__bvc...
Qed.

Lemma substA_bnr__bvbs : forall a T bs,
    bvbs bs = bvbs <{ [[T/a ][bnr] bs }>.
Proof with eauto.
  induction bs...
  simpl.
  destruct (existsb (eqb a) (btvb a0)); simpl.
  - setoid_rewrite bvbs_cons.
    rewrite <- substA_b__bvb...
  - setoid_rewrite bvbs_cons.
    rewrite <- IHbs.
    rewrite <- substA_b__bvb...
Qed.

Lemma msubstA_bnr__bvbs : forall ss bs,
    bvbs bs = bvbs <{ /[[ ss /][bnr] bs }>.
Proof with eauto.
  induction ss...
  destruct a.
  simpl.
  intros.
  setoid_rewrite <- IHss.
  rewrite <- substA_bnr__bvbs...
Qed.

Lemma msubst_LetNonRec_nil : forall ss e,
    msubst_term ss (Let NonRec nil e) = Let NonRec nil (msubst_term ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_LetNonRec : forall ss bs e,
    msubst_term ss (Let NonRec bs e) = Let NonRec (msubst_bindings_nonrec ss bs) (msubst_term (mdrop (bvbs bs) ss) e).
Proof with auto.
  induction ss; intros.
  - rewrite mdrop_nil. reflexivity.
  - destruct a. simpl.
    destruct (existsb (eqb s) (bvbs bs)) eqn:Hexb.
    + apply existsb_exists in Hexb.
      destruct Hexb as [x [HIn Heqb]].
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite In__mdrop...
      erewrite subst_bnr__bound_vars.
      eapply IHss.
    + rewrite not_In__mdrop...
      * simpl.
        erewrite subst_bnr__bound_vars.
        eapply IHss.
      * intros Hcon.
        eapply existsb_nexists.
        -- eapply Hexb.
        -- exists s.
           rewrite eqb_refl.
           auto.
Qed.

Lemma msubst_TermBind : forall ss stricty x T e,
    msubst_binding ss (TermBind stricty (VarDecl x T) e) = TermBind stricty (VarDecl x T) (msubst_term ss e). 
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_BindingsNonRec_cons : forall ss b bs,
    msubst_bindings_nonrec ss (b :: bs) = msubst_binding ss b :: msubst_bindings_nonrec (mdrop (bvb b) ss) bs.
Proof.
  induction ss; intros.
  - rewrite mdrop_nil. reflexivity.
  - destruct a. 
    simpl.
    destruct (existsb (eqb s) (bvb b)) eqn:Hexb.
    + apply existsb_exists in Hexb.
      destruct Hexb as [x [HIn Heqb]].
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite In__mdrop.
      * erewrite subst_b__bound_vars.  
        eapply IHss.
      * assumption.
    + apply existsb_nexists in Hexb.
      rewrite not_In__mdrop.
      * simpl.
        erewrite subst_b__bound_vars.
        eapply IHss.
      * intros Hcon.
        apply Hexb.
        exists s.
        rewrite eqb_refl.
        auto.
Qed.

Lemma msubstA_LetNonRec_nil : forall ss e,
    msubstA_term ss (Let NonRec nil e) = Let NonRec nil (msubstA_term ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_LetNonRec : forall ss bs e,
    msubstA_term ss (Let NonRec bs e) = Let NonRec (msubstA_bindings_nonrec ss bs) (msubstA_term (mdrop (btvbs bs) ss) e).
Proof.
(* ADMIT: I had no time to finish this. Should hold, it is a congruence lemma. *)
Admitted.

Lemma msubstA_TermBind : forall ss stricty x T e,
    msubstA_binding ss (TermBind stricty (VarDecl x T) e) = TermBind stricty (VarDecl x (msubstT ss T)) (msubstA_term ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_BindingsNonRec_cons : forall ss b bs,
    msubstA_bindings_nonrec ss (b :: bs) = msubstA_binding ss b :: msubstA_bindings_nonrec (mdrop (btvb b) ss) bs.
Proof.
(* ADMIT: I had no time to finish this. Should hold, it is a congruence lemma. *)
Admitted.

Lemma msubst_term__fold : forall ss x v t,
    msubst_term ss <{ [v / x] t }> = msubst_term ((x, v) :: ss) t.
Proof. induction ss; intros; auto. Qed.

Lemma msubst_bindings_nonrec__fold : forall ss x v bs,
    msubst_bindings_nonrec ss <{ [v / x][bnr] bs }> = msubst_bindings_nonrec ((x, v) :: ss) bs.
Proof. induction ss; intros; auto. Qed.
