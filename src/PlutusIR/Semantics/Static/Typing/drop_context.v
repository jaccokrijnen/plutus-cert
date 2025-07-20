Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.

Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Typing.Typing.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Export PlutusCert.PlutusIR.Analysis.FreeVars.

From PlutusCert Require Import util Util.

Require Import Coq.Program.Equality.
Import Coq.Lists.List.
Import ListNotations.
Import Coq.Strings.String.
Local Open Scope string_scope.
Open Scope list_scope.
From Coq Require Import Bool.

(* ************* drop_ty_var ************* *)

(* Using drop_ty_var creates a smaller list in the sense of inclusion *)
Lemma drop_ty_var__inclusion X Γ :
  List.inclusion (drop_ty_var X Γ) Γ.
Proof.
  unfold List.inclusion.
  intros x v Hl.
  induction Γ.
  - inversion Hl.
  - simpl.
    destruct a as [a1 a2].
    destruct (string_dec a1 x); subst.
    + rewrite String.eqb_refl.
      f_equal.
      (* ADMITTED:
        Suppose X in a2. Then by Hl
        we have that a2 <> v

        But then by drop_ty_var, all keys "x" will be removed from Hl,
        hence contradiction, because then it would have been None.

        Hence we must have X not in a2.
        Then by Hl we have lookup x ((x, a2)::...) = Some v => a2 = v
      *)
      admit.
    + rewrite <- String.eqb_neq in n.
      rewrite n.
      (* ADMITTED:
        a1 <> x
        lookup x (drop ((a1, a2)::Γ) = Some v)
        Well, it is not the first one (a1), and the result is Some v.
        Hence we must have lookup x (drop Γ) = Some v. (possibly with even smaller Gamma, if a2 contains X)
        since drop Γ is a subset of Γ, we must have then also lookup x Γ = Some v.
      *)
      admit.

Admitted.

(* Drop_ty_var preserves inclusion *)
Lemma drop_ty_var__inclusion_preserving : forall X Γ Γ',
    List.inclusion Γ Γ' -> List.inclusion (drop_ty_var X Γ) (drop_ty_var X Γ').
Proof.
intros X Γ Γ' Hincl.
unfold List.inclusion in Hincl.
unfold List.inclusion.
intros x v Hl.
(* by contradiction:
  Suppose lookup x (drop_ty_var X Γ') = None

    By drop_ty_var__inclusion,
      we have lookup x Γ' = Some v.

      then
        (x, v) in Gamma' and X in v (not possible by Hl)
      OR
        (x, v') in Gamma' and X in v', then also (x, v) gets removed

        But if this (x, v') occured to the right of (x, v), then still (x, v) in Gamma
        If it occurred to the left, we would have had
        lookup x Γ' = Some v' with v <> v'. Contradiction.
*)
Admitted.

(* If x is present after drop_ty_var, then it was also present before drop_ty_var *)
Lemma drop_ty_var__lookup_some : forall X Γ x T,
    lookup x (drop_ty_var X Γ) = Some T ->
    exists T', lookup x Γ = Some T'.
(* Drop ty var cannot remove anything, so we cannot get None
  we are not guaranteed to get the same, as (x, S(X)) could be dropped and in front of (x, T).
*)
Admitted.

(* Drop Δ *)

(* Dropping nothing is identity *)
Lemma drop_Δ_nil : forall Δ,
    drop_Δ Δ nil = Δ.
Proof.
  intros Δ.
  unfold drop_Δ.
  induction Δ.
  - simpl. reflexivity.
  - simpl. f_equal.
    auto.
Qed.

(* All elements in bind_Delta b are dropped by drop_Δ _ b... *)
Lemma drop_Δ__weaken : forall Δ b bs,
  drop_Δ Δ (b::bs) = drop_Δ (binds_Delta b ++ Δ) (b::bs).
Proof.
  intros Δ b bs; unfold drop_Δ.
  induction b.
  - simpl. reflexivity.
  - simpl. destruct t.
    unfold drop_Δ'.
    remember (fun x : string * kind => _) as f.

    assert (Hf_nil: filter f [(b, k)] = []).
    {
      subst; simpl.
      assert (Hin: (inb_string b (btvbs (TypeBind (TyVarDecl b k) t0 :: bs))) = true).
      {
        unfold btvbs; simpl.
        rewrite inb_string_true_iff.
        apply in_eq.
      }
      rewrite Hin; auto.
    }
    assert (Hf_app: filter f Δ = filter f [(b, k)] ++ filter f Δ).
    {
      rewrite Hf_nil.
      rewrite app_nil_l.
      reflexivity.
    }
    rewrite Hf_app.
    rewrite filter_app; auto.
  - simpl. destruct d. destruct t.
    unfold drop_Δ'.
    remember (fun x : string * kind => _) as f.
    assert (Hf_nil: filter f [(b0, k)] = []).
    {
      subst; simpl.
      assert (Hin: (inb_string b0 (btvbs (DatatypeBind (Datatype (TyVarDecl b0 k) l b l0) :: bs))) = true).
      {
        unfold btvbs; simpl.
        rewrite inb_string_true_iff.
        apply in_eq.
      }
      rewrite Hin; auto.
    }
    assert (Hf_app: filter f Δ = filter f [(b0, k)] ++ filter f Δ).
    {
      rewrite Hf_nil.
      rewrite app_nil_l.
      reflexivity.
    }
    rewrite Hf_app.
    rewrite filter_app; auto.
Qed.


(* drop_Δ with multiple bindings can be unfolded *)
Lemma drop_Δ__unfold : forall Δ b bs,
  drop_Δ Δ (b::bs) = drop_Δ (drop_Δ Δ bs) [b].
Proof.
  intros Δ b bs.
  induction Δ.
  - simpl. reflexivity.
  - simpl.
    destruct (inb_string (fst a) (btvbs (b :: bs))) eqn:Heqn1.
    + (* a = b or In a (btvb bs)*)
      simpl.
      destruct (inb_string (fst a) (btvbs bs)) eqn:Heqn2.
      * (* a in bs *)
        simpl.
        apply IHΔ.
      * (* a notin bs, so then a = b*)
        simpl.
        assert (inb_string (fst a) (btvbs [b]) = true ).
        {
          rewrite btvbs_cons in Heqn1.
          rewrite inb_string_true_iff in Heqn1.
          rewrite in_app_iff in Heqn1.
          destruct Heqn1 as [Heqn1 | Heqn1].
          - rewrite <- inb_string_true_iff in Heqn1.
            unfold btvbs; simpl.
            rewrite app_nil_r.
            assumption.
          - rewrite <- inb_string_true_iff in Heqn1.
            rewrite Heqn1 in Heqn2.
            inversion Heqn2.
        }
        simpl.
        rewrite H.
        simpl.
        apply IHΔ.
    + (* ~ In a (btvbs (b :: bs))*)
      assert (
        (inb_string (fst a) (btvbs bs)) = false).
      {
        rewrite btvbs_cons in Heqn1.
        rewrite inb_string_false_iff in Heqn1.
        rewrite not_in_app in Heqn1.
        destruct Heqn1 as [_ Heqn1].
        rewrite <- inb_string_false_iff in Heqn1.
        assumption.
      }
      rewrite H.
      simpl.
      assert ((inb_string (fst a) (btvbs [b])) = false).
      {
        rewrite btvbs_cons in Heqn1.
        rewrite inb_string_false_iff in Heqn1.
        rewrite not_in_app in Heqn1.
        destruct Heqn1 as [Heqn1 _].
        rewrite <- inb_string_false_iff in Heqn1.
        unfold btvbs. simpl.
        rewrite app_nil_r.
        assumption.
      }
      rewrite H0; simpl.
      f_equal.
      apply IHΔ.
Qed.

(* Trivial helper: Drop_Δ nil preserves kinding (and is identical)*)
Lemma drop_Δ_nil__kinding : forall Δ T K,
    drop_Δ Δ nil |-* T : K -> Δ |-* T : K.
Proof.
  intros.
  rewrite drop_Δ_nil in H.
  assumption.
Qed.

(* drop_Δ' drops everything in the list *)
Lemma drop_Δ'__lookup_None : forall Δ xs x,
  In x (xs) -> lookup x (drop_Δ' Δ xs) = None.
Proof.
  intros Δ xs x Hbtvbs.
  induction Δ; simpl.
  - reflexivity.
  - destruct a as [a1 a2]; simpl.
    destruct (negb (inb_string a1 (xs))) eqn:Heqn.
    + destruct (string_dec a1 x).
      * subst.
        exfalso.
        rewrite negb_true_iff in Heqn.
        rewrite inb_string_false_iff in Heqn.
        contradiction.
      * simpl.
        rewrite <- String.eqb_neq in n.
        rewrite n.
        exact IHΔ.
  + assumption.
Qed.

(* drop_Δ drops all introduced binder names *)
Lemma drop_Δ__lookup_None : forall Δ bs x,
  In x (BoundVars.btvbs bs) -> lookup x (drop_Δ Δ bs) = None.
Proof.
  intros.
  unfold drop_Δ.
  eapply drop_Δ'__lookup_None.
  assumption.
Qed.

(* drop_Δ'__lookup_None, but for In instead of lookup*)
Lemma dropped_not_in_drop_Δ' : forall Δ xs x,
  In x xs ->
  ~ In x (map fst (drop_Δ' Δ xs)).
Proof.
  intros Δ xs x Hin.
  apply drop_Δ'__lookup_None with (Δ := Δ) in Hin.
  apply lookup__not_in in Hin.
  assumption.
Qed.

(* drop_Δ' does not drop anything not in xs *)
Lemma lookup_None__drop_Δ' : forall Δ xs x,
  ~ In x xs ->
  lookup x (drop_Δ' Δ xs) = lookup x Δ.
Proof.
  intros Δ xs x HnotBtvb.
  induction Δ; simpl.
  - reflexivity.
  - destruct a as [a1 a2]; simpl.
    destruct ((inb_string a1 xs)) eqn:Heqn; simpl.
    + destruct (string_dec a1 x).
      * subst.
        rewrite inb_string_true_iff in Heqn.
        contradiction.
      * rewrite <- String.eqb_neq in n.
        rewrite n.
        rewrite IHΔ; auto.
    + simpl.
      destruct (string_dec a1 x).
      * subst.
        rewrite String.eqb_refl.
        reflexivity.
      * rewrite <- String.eqb_neq in n.
        rewrite n.
        rewrite IHΔ; auto.
Qed.

(* drop_Δ only drops introduced binders *)
Lemma lookup_None__drop_Δ : forall Δ bs x,
  ~ In x (BoundVars.btvbs bs) ->
  lookup x (drop_Δ Δ bs) = lookup x Δ.
Proof.
  intros.
  unfold drop_Δ.
  eapply lookup_None__drop_Δ'.
  assumption.
Qed.

(* If lookup finds something after drop_Δ', then it cannot be in the list xs that should have been dropped *)
Lemma lookup_Some__drop_Δ'_no_xs : forall Δ xs x K,
  lookup x (drop_Δ' Δ xs) = Some K ->
  ~ In x xs.
Proof.
  intros Δ xs x K Hl.
  induction Δ; simpl in *.
  - inversion Hl.
  - destruct a as [a1 a2]; simpl in *.
    destruct (inb_string a1 xs) eqn:Heqn; simpl in *.
    + destruct (string_dec a1 x).
      * apply IHΔ.
        assumption.
      * subst.
        apply IHΔ.
        exact Hl.
    + simpl in Hl.
      destruct (string_dec a1 x).
      * subst.
        rewrite inb_string_false_iff in Heqn.
        assumption.
      * rewrite <- String.eqb_neq in n.
        rewrite n in Hl.
        apply IHΔ.
        assumption.
Qed.

(* Analogous but for drop_Δ*)
Lemma lookup_Some__drop_Δ_no_btvbs : forall Δ bs x K,
  lookup x (drop_Δ Δ bs) = Some K ->
  ~ In x (BoundVars.btvbs bs).
Proof.
  intros.
  unfold drop_Δ.
  eapply lookup_Some__drop_Δ'_no_xs; eauto.
Qed.

(* drop_Δ' is included in Δ*)
Lemma drop_Δ'__inclusion : forall Δ xs,
  List.inclusion (drop_Δ' Δ xs) Δ.
Proof.
  intros.
  induction Δ; simpl.
  - unfold List.inclusion; auto.
  - destruct a as [a1 a2].
    destruct (inb_string (fst (a1, a2)) xs) eqn:Heqn; simpl in *.
    + unfold inclusion.
      intros x v Hl.
      destruct (string_dec a1 x).
      * subst.
        exfalso.
        rewrite inb_string_true_iff in Heqn.
        eapply drop_Δ'__lookup_None in Heqn.
        rewrite Hl in Heqn.
        inversion Heqn.
      * simpl.
        rewrite <- String.eqb_neq in n.
        rewrite n.
        apply IHΔ.
        assumption.
    + unfold inclusion.
      intros x v Hl.
      destruct (string_dec a1 x).
      * subst.
        inversion Hl.
        rewrite String.eqb_refl.
        simpl.
        rewrite String.eqb_refl.
        reflexivity.
      * simpl.
        rewrite <- String.eqb_neq in n.
        rewrite n.
        apply IHΔ.
        simpl in Hl.
        rewrite n in Hl.
        assumption.
Qed.

(* drop_Δ is included in Δ*)
Lemma drop_Δ__inclusion : forall Δ bs,
  List.inclusion (drop_Δ Δ bs) Δ.
Proof.
  intros.
  unfold drop_Δ.
  eapply drop_Δ'__inclusion.
Qed.


(* Not removing b and adding them to Δ is a superset *)
Lemma drop_Δ_cons__inclusion : forall Δ b bs,
    List.inclusion (drop_Δ Δ (b::bs)) (drop_Δ (binds_Delta b ++ Δ) bs).
Proof.
  intros Δ b bs.
  assert (Hweaken: drop_Δ Δ (b::bs) = drop_Δ (binds_Delta b ++ Δ) (b::bs)).
  {
    apply drop_Δ__weaken.
  }
  rewrite Hweaken; clear Hweaken.
  assert (Hunfold: drop_Δ (binds_Delta b ++ Δ) (b::bs) = drop_Δ (drop_Δ (binds_Delta b ++ Δ) bs) [b]).
  {
    apply drop_Δ__unfold.
  }
  rewrite Hunfold; clear Hunfold.
  apply drop_Δ__inclusion.
Qed.

(* drop_Δ' prserves inclusion *)
Lemma drop_Δ'__preserves__inclusion : forall Δ Δ' xs,
    List.inclusion Δ Δ' ->
    List.inclusion (drop_Δ' Δ xs) (drop_Δ' Δ' xs).
Proof.
  intros Δ Δ' xs Hincl.
  unfold inclusion in *.
  intros x v Hl.
  assert (lookup x Δ' = Some v).
  {
    apply drop_Δ'__inclusion in Hl.
    apply Hincl in Hl.
    assumption.
  }
  assert ( ~ In x xs).
  {
    eapply lookup_Some__drop_Δ'_no_xs; eauto.
  }

  induction Δ'.
  - inversion H.
  - eapply lookup_None__drop_Δ' in H0; eauto.
    rewrite H0.
    assumption.
Qed.

(* drop_Δ preserves inclusion *)
Lemma drop_Δ__preserves__inclusion : forall Δ Δ' bs,
    List.inclusion Δ Δ' ->
    List.inclusion (drop_Δ Δ bs) (drop_Δ Δ' bs).
Proof.
  intros.
  unfold drop_Δ.
  eapply drop_Δ'__preserves__inclusion.
  assumption.
Qed.

(* If the bound type variables in two lists of bindings are identical, then drop_Δ behaviour is too *)
Lemma btvbs_eq__drop_Δ_eq : forall Δ bs bs',
  btvbs bs = btvbs bs' ->
  drop_Δ Δ bs = drop_Δ Δ bs'.
Proof.
  intros Δ bs bs' Hbtvbs.
  unfold drop_Δ.
  rewrite Hbtvbs.
  reflexivity.
Qed.
