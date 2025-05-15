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
Require Import Coq.Bool.Bool.

From PlutusCert Require Import util STLC_named gu_naive.pre alpha.alpha freshness util alpha_ctx_sub alpha_freshness.


(* Pff, this must be avoidable: same set/prop trick as with kinding*)
Inductive InSet {A : Type} (x : A) : list A -> Type :=
| InSet_head : forall l, InSet x (x :: l)
| InSet_tail : forall y l, InSet x l -> InSet x (y :: l).

Lemma in_app_or_set {A} (x : A) (l1 l2 : list A) :
  InSet x (l1 ++ l2) -> sum (InSet x l1) (InSet x l2).
Proof.
    induction l1 as [|h t IH]; simpl; intros H.
  - right; exact H.
  - inversion H; subst; clear H.
    + left; apply InSet_head.
    + destruct (IH X) as [H'|H'].
      * left; apply InSet_tail; exact H'.
      * right; exact H'.
Qed.

Definition in_dec_set {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) :
  sum (InSet x l) ((InSet x l) -> False).
Proof.
  induction l as [|h t IH].
  - right; intros H; inversion H.
  - destruct (eq_dec x h) as [-> | Hneq].
    + left; apply InSet_head.
    + destruct IH as [Hin | Hnin].
      * left; apply InSet_tail; exact Hin.
      * right; intros H; inversion H; subst; [contradiction | apply Hnin; assumption].
Defined.

Theorem in_set_to_prop {A} {x : A} {l : list A} :
  InSet x l -> In x l.
Proof.
  intros.
  induction l as [|h t IH]; simpl in *.
  - inversion X.
  - inversion X; subst.
    + left; reflexivity.
    + right; apply IH; assumption.
Qed.

Fixpoint in_dec_f {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) :
  bool:=
  match l with
  | [] => false
  | h :: hs =>
      match eq_dec x h with
      | left _ => true
      | right _ => in_dec_f eq_dec x hs
      end
  end.

Theorem in_dec_f_sound {A} {eq_dec : forall x y : A, {x = y} + {x <> y}} {x : A} {l : list A} :
  in_dec_f eq_dec x l = true -> InSet x l.
Proof.
  induction l as [|h t IH]; simpl; intros H.
  - discriminate H.
  - destruct (eq_dec x h) as [-> | Hneq].
    + apply InSet_head.
    + apply InSet_tail.
      apply IH.
      auto.
Qed.

Theorem in_prop_to_set {x : string} {l : list string} :
  In x l -> InSet x l.
Proof.
  intros.
  destruct (in_dec_f string_dec x l) eqn:uhm.
  - eapply in_dec_f_sound; eauto.
  - exfalso.
    induction l.
    + inversion H.
    + inversion H; subst.
      simpl in uhm.
      destruct (string_dec x x).
      * discriminate uhm.
      * contradiction.
      * assert (in_dec_f string_dec x l = false).
        {
          simpl in uhm.
          destruct (string_dec x a).
          - discriminate uhm.
          - auto.
        }
        eapply IHl; auto.
Qed.

Inductive IdSubst : list (string * term) -> Set :=
  | id_subst_nil : IdSubst nil
  | id_subst_cons : forall x sigma , IdSubst sigma -> IdSubst ((x, tmvar x)::sigma).


Lemma id_subst__id s σ :
  (* NC s σ ->  *)
  IdSubst σ -> 
  psubs σ s = s. (* even when this capturs, it doesnt matter, since it captures something and then substiutes it for the same name*)
Proof.
  intros.
  induction s.
  - induction σ.
    + reflexivity.
    + simpl. destruct a as [x1 x2].
      inversion H; subst.
      specialize (IHσ H1).
      simpl in IHσ.
      destr_eqb_eq x1 s; auto.
  - simpl.
    f_equal.
    apply IHs.
  - simpl.
    f_equal; eauto.
  - simpl; auto.
Qed.

Lemma id_ctx_alphavar_refl R x : IdCtx R -> AlphaVar R x x.
Proof.
  intros.
  assert (Alpha R (tmvar x) (tmvar x)).
  {
    apply alpha_extend_ids; auto.
    apply alpha_refl. constructor.
  }
  inv H0.
  auto.
Qed.

Definition fresh_to_GU_ (ftvs : list string) (binders : list (string * string)) (x : string) := 
  String.concat "" (ftvs ++ map fst binders ++ map snd binders ++ x::nil ++ "a"::nil).
(* a is necessary for empty ftvs and binders*)

Lemma fresh_to_GU__fresh_over_ftvs ftvs binders x : ~ In (fresh_to_GU_ ftvs binders x) ftvs.
Admitted.

Lemma fresh_to_GU__fresh_over_snd_binders ftvs binders x : ~ In (fresh_to_GU_ ftvs binders x) (map snd binders).
Admitted.

Lemma fresh_to_GU__fresh_over_binders ftvs binders x : ~ In (fresh_to_GU_ ftvs binders x) (map fst binders ++ map snd binders).
Admitted.

Fixpoint to_GU_ (used : list string) (binders : list (string * string)) (s : term) :=
  match s with
  | tmvar x => match lookup x binders with
              | Some y => (y::used, binders, tmvar y) (* we are adding y to used to make proving stuff easier, sine it was already in binders, it would have indirectly already be in used*)
                 (* this was bound and (possibly) renamed, or free and renamed to itself*)
              | None => ((x::used), binders, tmvar x) (* this branch should never happen: all binders and ftvs should be in the map. *)
              end
  | @tmlam B x A s => (* we can freshen regardless *)
                    let x' := fresh_to_GU_ used binders x in
                    let (acc, term_body) := to_GU_ used ((x, x')::binders) s in
                    ((fst acc ++ (x::x'::nil)), binders, @tmlam B x' A term_body)
  | @tmapp B s t => let (acc_s, s') := to_GU_ used binders s in
                 let (acc_t, t') := to_GU_ (fst acc_s) binders t in (* stuff in s cannot cause us to be suddenly under more binders in t*)
                 (acc_t, @tmapp B s' t')
  | tmbuiltin d => (used, binders, tmbuiltin d)
  end.

Compute (to_GU_ nil nil (tmlam "x" PlutusIR.Kind_Base (tmvar "x"))). (* should be λxa . xa*)
Compute (to_GU_ nil nil (tmapp (tmvar "x") (tmvar "y"))). (* should be xy*)
Compute (to_GU_ nil nil (tmapp (tmlam "y" PlutusIR.Kind_Base (tmapp (tmvar "x") (tmvar "y"))) (tmvar "y"))). 
Compute (to_GU_ nil nil (tmapp (tmlam "y" PlutusIR.Kind_Base (tmvar "y")) (tmvar "y"))). (* should be x(λya . ya)*)
Compute (to_GU_ nil nil (tmapp (tmlam "y" PlutusIR.Kind_Base (tmapp (tmvar "x") (tmvar "y"))) (tmvar "x"))).
Compute (to_GU_ nil nil (tmlam "x" PlutusIR.Kind_Base (tmapp (tmlam "y" PlutusIR.Kind_Base (tmapp (tmvar "x") (tmvar "y"))) (tmvar "x")))).


(* By precalculating ftvs, we cannot get that a binder is accidentally renamed to an ftv later in the term
  this was problematic, because to_GU_ does not rename ftvs
*)
Definition to_GU (s : term) :=
let tvs := tv s in 
(* We do tv even, isntead of only ftvs: can not become problematic, 
  and helps with proofs of GU (that we already know that when we encounter any binder, that it will be in "used")
    But before we used the fact that all ftvs are unique. For tvs that is not the case.
     TODO:  hence we must also remove duplicates, to keep the UniqueRhs property.
     UPDATE Mar 14: remove the duplicates? I dont think they are necessary
  *)
snd (to_GU_ tvs  (map (fun x => (x, x)) tvs) s).

Compute (to_GU (tmapp (tmlam "y" PlutusIR.Kind_Base (tmvar "y")) (tmvar "ya"))). 
Compute (to_GU (tmapp (tmvar "ya") (tmlam "y" PlutusIR.Kind_Base (tmvar "y")))). 

Definition KindOfUniqueRhs (R : list (string * string))  := 
  forall x y, lookup x R = Some y -> AlphaVar R x y.


(* If the new fresh variable is based on everything in original R, it will be genuinly "fresh"*)
Lemma KindOfUniqueRhsFresh x R R' used : 
  KindOfUniqueRhs R -> 
  (forall y, In y (map fst R ++ map snd R) -> (In y used) \/ (In y (map fst R' ++ map snd R'))) -> 
  KindOfUniqueRhs ((x, fresh_to_GU_ used R' x)::R).
Proof.
  intros.
  unfold KindOfUniqueRhs in *.
  intros.
  destr_eqb_eq x0 x.
  - simpl in H1.
    rewrite String.eqb_refl in H1.
    inv H1.
    constructor.
  - inv H1.
    rewrite <- String.eqb_neq in H2.
    rewrite String.eqb_sym in H2.
    rewrite H2 in H4.
    remember H4 as H4_lookup.
    clear HeqH4_lookup.
    apply lookup_some_then_in_values in H4.
    assert (In y (map fst R ++ map snd R)).
    {
      apply in_app_iff. right. auto.
    }
    specialize (H0 y H1).
    apply alpha_var_diff; auto.
    + rewrite <- String.eqb_neq. auto.
    + destruct H0.
      * assert (~ In (fresh_to_GU_ used R' x) used) by apply fresh_to_GU__fresh_over_ftvs.
        intros Hcontra.
        subst.
        contradiction.
      * assert (~ In (fresh_to_GU_ used R' x) (map fst R' ++ map snd R')) by apply fresh_to_GU__fresh_over_binders.
        intros Hcontra.
        subst.
        contradiction.
Qed.

Lemma IdCtx__alphavar_refl {R x y} : IdCtx R -> AlphaVar R x y -> x = y.
Proof.
  intros.
  induction H; inv H0; auto.
Qed.

Lemma IdCtx__KindOfUniqueRhs R : IdCtx R -> KindOfUniqueRhs R.
Proof.
  intros.
  unfold KindOfUniqueRhs.
  intros.
  induction H.
  - inv H0.
  - destr_eqb_eq x x0.
    + inv H0.
      rewrite String.eqb_refl in H2.
      inv H2.
      constructor.
    + inv H0.
      rewrite <- String.eqb_neq in H1.
      rewrite String.eqb_sym in H1.
      rewrite H1 in H3.
      specialize (IHIdCtx H3).
      remember IHIdCtx as IHIdCtx'.
      clear HeqIHIdCtx'.
      eapply (IdCtx__alphavar_refl H) in IHIdCtx. subst.
      
      constructor; auto.
      * rewrite <- String.eqb_neq. auto.
      * rewrite <- String.eqb_neq. auto.
Qed.

Lemma used_never_removed s : forall used binders s' used' binders',
  ((used', binders'), s') = to_GU_ used binders s -> forall x, In x used -> In x used'.
Proof.
  induction s; intros.
  - simpl in H. destruct (lookup s binders) eqn:lookup_x_R; inv H; auto; apply in_cons; auto.
  - simpl in H.
    remember (to_GU_ used ((s, fresh_to_GU_ used binders s) :: binders) s0) as p.
    destruct p as [ [used1 binders1] s1].
    simpl in H.
    inversion H.
    apply in_app_iff.
    left.
    eapply IHs; eauto.
  - simpl in H.
    remember (to_GU_ used binders s1) as p1.
    destruct p1 as [ [used1 binders1] s1'].
    simpl in H.
    remember (to_GU_ used1 binders s2) as p2.
    destruct p2 as [ [used2 binders2] s2'].
    simpl in H.
    inversion H.
    eapply IHs2; eauto.
  - inversion H.
    auto.
Qed.


Lemma to_GU__alpha_' s R used : 
  (forall x y, In x (ftv s) -> lookup x R = Some y -> AlphaVar R x y) ->
  (forall x, In x (ftv s) -> lookup x R = None -> AlphaVar R x x) -> 
  (forall x, In x (tv s) -> In x used) -> 
  Alpha R s (snd (to_GU_ used R s)).
Proof.
  generalize dependent R.
  generalize dependent used.
  induction s; intros.
  - simpl. destruct (lookup s R) eqn:lookup_x_R.
    + constructor.
      apply H. simpl. left. auto.
      auto.
    + constructor.
      specialize (H0 s).
      assert (In s (ftv (tmvar s))) by now apply ftv_var_eq.
      eauto.
  -
     simpl. remember (to_GU_ used ((s,
    fresh_to_GU_
      used R s)
    :: R)
  s0) as p.
    simpl. destruct p as [ [used' binders'] s'].
    simpl.
    constructor.
    specialize (IHs used ((s, fresh_to_GU_ used R s) :: R)).
    rewrite <- Heqp in IHs. 
    simpl in IHs.
    eapply IHs.
    + intros.
      destr_eqb_eq s x.
      * inversion H3. subst.
        constructor.
      * constructor; auto.
        -- apply lookup_some_then_in_values in H3.
           
           assert (~ In (fresh_to_GU_ used R s) (map snd R)).
           { eapply fresh_to_GU__fresh_over_snd_binders. }
           intros Hcontra.
           subst.
           contradiction.
        -- apply H.
           simpl. apply in_remove. auto. auto.
    + intros.
      destruct_match.
      assert (Hftvlam: In x (ftv (@tmlam USort s k s0))).
      {
        apply ftv_c_lam. auto. rewrite <- String.eqb_neq. auto.
      } 
      apply alpha_var_diff. auto.
      {
        rewrite <- String.eqb_neq. auto.
      }
      * specialize (H0 x).
        specialize (H0 Hftvlam).
        specialize (H1 x (extend_ftv_to_tv Hftvlam)).
        assert (~ In (fresh_to_GU_ used R s) used) by now apply fresh_to_GU__fresh_over_ftvs.
        intros Hcontra.
        subst.
        contradiction.
      * eapply H0; auto.
    + intros.
      eapply H1.
      apply tv_c_lam. auto.
  - simpl. 
    remember (to_GU_ used R s1) as p1.
    destruct p1 as [ [used1 binders] s1'].
    simpl. 
    remember (to_GU_ used1 R s2) as p2.
    destruct p2 as [ [used2 binders'] s2'].
    simpl.
    constructor.
    + specialize (IHs1 used R).
      simpl in IHs1.
      rewrite <- Heqp1 in IHs1.
      simpl in IHs1.
      eapply IHs1.
      * intros. apply H. simpl. apply in_app_iff. left. auto. auto.
      * intros.
        eapply H0.
        apply ftv_c_appl. auto. 
        auto.
      * intros. eapply H1. apply tv_c_appl. auto.
    + specialize (IHs2 used1 R).
      rewrite <- Heqp2 in IHs2.
      simpl in IHs2.
      eapply IHs2.
      * intros. apply H. simpl. apply in_app_iff. right. auto. auto.
      * intros.
        eapply H0.
        apply ftv_c_appr. auto.
        auto.
      * intros.
        eapply used_never_removed; eauto.
        eapply H1.
        apply tv_c_appr. auto.
  - simpl. 
    constructor.
Qed.

Lemma to_GU__alpha_ s R used : 
  (forall x y, In x (ftv s) -> lookup x R = Some y -> AlphaVar R x y) ->
  (forall x, In x (ftv s) -> {y & In (x, y) R}) -> 
  Alpha R s (snd (to_GU_ used R s)).
Proof.
  generalize dependent R.
  generalize dependent used.
  induction s; intros.
  - simpl. destruct (lookup s R) eqn:lookup_x_R.
    + constructor. 
      apply H. simpl. left. auto. auto.
    + constructor.
      specialize (H0 s).
      assert (In s (ftv (tmvar s))) by now apply ftv_var_eq.
      specialize (H0 H1).
      destruct H0 as [y H2].
      apply lookup_not_In with (v := y) in lookup_x_R.
      contradiction.
  - simpl. remember (to_GU_ used ((s,
  fresh_to_GU_
    used R s)
  :: R)
  s0) as p.
    simpl. destruct p as [ [used' binders'] s'].
    simpl.
    constructor.
    specialize (IHs used ((s, fresh_to_GU_ used R s) :: R)).
    rewrite <- Heqp in IHs. 
    simpl in IHs.
    eapply IHs.
    + intros.
      destr_eqb_eq s x.
      * inversion H2.
        subst.
        constructor.
      * constructor; auto.
        -- apply lookup_some_then_in_values in H2.
           
           assert (~ In (fresh_to_GU_ used R s) (map snd R)).
           { eapply fresh_to_GU__fresh_over_snd_binders. }
           intros Hcontra.
           subst.
           contradiction.
        -- apply H.
           simpl. apply in_remove. auto. auto.
    + intros.
      destr_eqb_eq x s.
      * exists (fresh_to_GU_ used R s).
        simpl. intuition.
      * specialize (H0 x).
        assert (In x (ftv (@tmlam USort s k s0))).
        {
          apply ftv_c_lam; auto.
        } 
        specialize (H0 H3).
        destruct H0 as [y H4].
        exists y.
        right.
        assumption.
  - simpl. 
    remember (to_GU_ used R s1) as p1.
    destruct p1 as [ [used1 binders] s1'].
    simpl. 
    remember (to_GU_ used1 R s2) as p2.
    destruct p2 as [ [used2 binders'] s2'].
    simpl.
    constructor.
    + specialize (IHs1 used R).
      simpl in IHs1.
      rewrite <- Heqp1 in IHs1.
      simpl in IHs1.
      eapply IHs1.
      * intros. apply H. simpl. apply in_app_iff. left. auto. auto.
      * intros.
        assert (In x (ftv (@tmapp BSort s1 s2))) by now apply ftv_c_appl.
        specialize (H0 x H2).
        assumption.
    + specialize (IHs2 used1 R).
      rewrite <- Heqp2 in IHs2.
      simpl in IHs2.
      eapply IHs2.
      * intros. apply H. simpl. apply in_app_iff. right. auto. auto.
      * intros.
        assert (In x (ftv (@tmapp BSort s1 s2))) by now apply ftv_c_appr.
        specialize (H0 x H2).
        assumption.
  - simpl. constructor.
Qed.   

Lemma map_creates_IdCtx l : IdCtx (map (fun x => (x, x)) l).
Proof.
  induction l; simpl; constructor; auto.
Qed.

Lemma to_GU__alpha s : Alpha [] s (to_GU s).
Proof.
  remember (to_GU s) as s'.
  unfold to_GU in Heqs'.
  remember (map (fun x => (x, x)) (tv s)) as R.
  rewrite Heqs'.
  assert (R ⊢ s ~ (to_GU_ (tv s) R s).2).
  {
    assert (IdCtx R).
    {
      rewrite HeqR.
      apply map_creates_IdCtx.
    }

    eapply to_GU__alpha_'.
    - intros.
      eapply lookup_some_IdCtx_then_alphavar; eauto.

    - intros.
      apply id_ctx_alphavar_refl; auto.
    - intros. auto.
  }
  eapply alpha_weaken_ids with (idCtx := R).
  - subst.
    clear H.
    induction (tv s); simpl; constructor; auto.
  - assumption.
Qed.


Lemma no_repeated_binder used' binders' s' used binders s : 
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (map snd binders) -> ~ In x (btv s')).
Proof.
  intros.
  generalize dependent used.
  generalize dependent binders.
  generalize dependent used'.
  generalize dependent binders'.
  generalize dependent s'.
  induction s; intros.
  - simpl in H. destruct (lookup s binders) eqn:lookup_x_R.
    + inversion H; subst.
      auto.
    + inversion H; subst.
      auto.
  - simpl in H.
    remember (to_GU_ used ((s, fresh_to_GU_ used binders s) :: binders) s0) as p.
    destruct p as [ [used1 binders1] s1].
    inversion H.
    (* x <> fresh_to_GU_ used binders s) by x in map snd binders
      Hence goal is to look at body.
    *)
    assert (~ In x (btv s1)).
    {
      eapply IHs.
      2: eauto.
      simpl. right. assumption.
    }
    simpl. intros Hcontra. destruct Hcontra; auto.
    assert (~ In (fresh_to_GU_ used binders s) (map snd binders)).
    {
      eapply fresh_to_GU__fresh_over_snd_binders.
    }
    subst. contradiction.
  - simpl in H.
    remember (to_GU_ used binders s1) as p1.
    destruct p1 as [ [used1 binders1] s1'].
    remember (to_GU_ (fst (used1, binders1)) binders s2) as p2.
    destruct p2 as [ [used2 binders2] s2'].
    inversion H.
    simpl.
    apply not_in_app.
    split.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto.
  - simpl in H.
    inversion H; subst.
    auto.
Qed.

(* to_GU_ creates binders that are not in used*)
Lemma no_binder_used_contrapositive used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> (forall x,  In x used -> ~ In x (btv s')).
Proof.
  intros.
  generalize dependent s'.
  generalize dependent used'.
  generalize dependent binders'.
  generalize dependent used.
  generalize dependent binders.
  induction s; intros.
  - simpl in H. destruct (lookup s binders) eqn:lookup_x_R; inversion H; subst; auto.
  - simpl in H.
    remember (to_GU_ used ((s, fresh_to_GU_ used binders s) :: binders) s0) as p.
    destruct p as [ [used1 binders1] s1].
    simpl in H.
    inversion H.
    simpl.
    unfold not.
    intros Hcontra.
    destruct Hcontra.
    + rewrite <- H1 in H0.
      eapply fresh_to_GU__fresh_over_ftvs. eauto.
    + eapply IHs with (s' := s1) (used := used); eauto.
  - simpl in H. 
    remember (to_GU_ used binders s1) as p1.
    destruct p1 as [ [used1 binders1] s1'].
    remember (to_GU_ (fst (used1, binders1)) binders s2) as p2.
    destruct p2 as [ [used2 binders2] s2'].
    inversion H.
    simpl.
    apply not_in_app. split.
    + eapply IHs1; eauto.
    + simpl in Heqp2.
      eapply IHs2 with (used := used1); eauto.
      eapply used_never_removed; eauto.
  - inversion H.
    auto.
Qed.

(* to_GU_ creates binders that are not in used*)
Lemma no_binder_used used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (btv s') -> ~ In x used).
Proof.
  intros.
  intros Hcontra.
  
  eapply no_binder_used_contrapositive in Hcontra; eauto.
Qed.


(* to_GU_ remembers which ftvs and btvs have occurred*)
Lemma tvs_remembered used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (tv s') -> In x used').
Proof.
  intros.
  generalize dependent used.
  generalize dependent binders.
  generalize dependent used'.
  generalize dependent binders'.
  generalize dependent s'.
  induction s; intros.
  - simpl in H. destruct (lookup s binders) eqn:lookup_x_R; inversion H; subst; auto;
    apply tv_var in H0;
    left;
    auto.
  - simpl in H.
    remember (to_GU_ used ((s, fresh_to_GU_ used binders s) :: binders) s0) as p.
    destruct p as [ [used1 binders1] s1].
    simpl in H.
    inversion H.
    simpl.
    apply in_app_iff.
    destr_eqb_eq x (fresh_to_GU_ used binders s).
    + right. intuition.
    + left.
      eapply IHs with (s' := s1); eauto.
      rewrite H4 in H0.
      eapply tv_dc_lam; eauto.
  - simpl in H.
    remember (to_GU_ used binders s1) as p1.
    destruct p1 as [ [used1 binders1] s1'].
    remember (to_GU_ (fst (used1, binders1)) binders s2) as p2.
    destruct p2 as [ [used2 binders2] s2'].
    inv H.
    simpl.
    simpl in H0.
    apply in_app_iff in H0.
    destruct H0.
    + eapply used_never_removed with (used := used1); eauto.
    + eauto.
  - inv H.
    inv H0.
Qed.

Lemma sigma_to_exists {A : Type} (P : A -> Prop) :
  { y & P y } -> (exists y, P y).
Proof.
  intros H.
  destruct H as [y Hy].
  exists y. exact Hy.
Qed.



(* All ftvs are mapped by R (that's how we initialize it. (so maybe this shouldnt be a lemma, but an argument))*)
Lemma ftvs_mapped_by_R used binders s s' used' binders' :
(* This is an invariant we want to enforce on construction and in each lemma that we want to use this lemma*)
  (forall y, In y (ftv s) -> {x & (In (y, x) binders)}) -> 
  
    (* NOTE: It didnt work with sigma types*)
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (ftv s') -> (exists y, (In (y, x) binders))).
Proof.
  intros.
  generalize dependent used.
  generalize dependent binders.
  generalize dependent used'.
  generalize dependent binders'.
  generalize dependent s'.
  induction s; intros.
  - assert (s' = (tmvar x)).
    {
      unfold to_GU_ in H0.
      destruct (lookup s binders) eqn:lookup_x_R; inv H0; apply ftv_var in H1; rewrite H1; reflexivity.
    }
    specialize (H s).
    assert (In s (ftv (tmvar s))).
    {
      now apply ftv_var_eq.
    }
    specialize (H H3).
    destruct H as [x0 H].
    apply in_then_lookup_some_and_in in H as [x0' [H4_lookup H4_in] ].
    simpl in H0.
    rewrite H4_lookup in H0.
    inversion H0.
    rewrite H6 in H1.
    assert (x = x0').
    {
      apply ftv_var. auto.
    }
    subst.
    exists s.
    auto.
  - simpl in H0.
    remember (to_GU_ used ((s, fresh_to_GU_ used binders s) :: binders) s0) as p.
    destruct p as [ [used1 binders1] s1].
    simpl in H0.
    inversion H0.
    assert (In x (ftv s1)).
    {
      rewrite H5 in H1.
      apply ftv_lam_helper in H1. auto.
    }
    clear H0.
    specialize (IHs s1 H2 binders1 used1 ((s, fresh_to_GU_ used binders s):: binders)).
    assert ((forall y, y ∈ ftv s0 -> {x0 & (y, x0) ∈ ((s, fresh_to_GU_ used binders s) :: binders)})).
    {
      intros.
      specialize (H y).
      destr_eqb_eq y s.
      -exists (fresh_to_GU_ used binders s).
       simpl. left. auto.
      - assert (In y (ftv (@tmlam USort s k s0))).
        {
          apply ftv_c_lam. auto.
          auto.
        } 
        specialize (H H7).
        destruct H as [x0 H].
        exists x0.
        simpl. right. assumption.
    }
    specialize (IHs H0 used Heqp).
    destruct IHs as [y IHs].
    exists y.
    destruct IHs.
    + inversion H6; subst.
      apply ftv_lam_no_binder in H1.
      contradiction.
    + assumption.
  - simpl in H0.
    remember (to_GU_ used binders s1) as p1.
    destruct p1 as [ [used1 binders1] s1'].
    remember (to_GU_ (fst (used1, binders1)) binders s2) as p2.
    destruct p2 as [ [used2 binders2] s2'].
    inversion H0.
    rewrite H5 in H1.
    unfold ftv in H1; fold ftv in H1.
    apply in_app_iff in H1.
    
    destruct H1.
    + 
      specialize (IHs1 s1' H1 binders1 used1 binders).
      assert (forall y : string, y ∈ ftv s1 -> {x0 : string & (y, x0) ∈ binders}).
      {
        intros.
        specialize (H y).
        assert (In y (ftv (@tmapp BSort s1 s2))).
        {
          apply ftv_c_appl. auto.
        }
        specialize (H H6).
        destruct H as [x0 H].
        exists x0.
        assumption.
      }
      
      specialize (IHs1 H2 used Heqp1).
      destruct IHs1 as [y IHs1].
      eauto.
    + specialize (IHs2 s2' H1 binders2 used2 binders).
      assert (forall y : string, y ∈ ftv s2 -> {x0 : string & (y, x0) ∈ binders}).
      {
        intros.
        specialize (H y).
        assert (In y (ftv (@tmapp BSort s1 s2))).
        {
          apply ftv_c_appr. auto.
        }
        specialize (H H6).
        destruct H as [x0 H].
        exists x0.
        assumption.
      }
      specialize (IHs2 H2 used1 Heqp2).
      auto.
  - simpl in H0.
    inversion H0.
    subst.
    inversion H1.
Qed.

(* Because of decomposition behaviour of btv under lambda, this was easier to prove using contrapositive*)
Lemma no_btv_in_binders' used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (map fst binders ++ map snd binders) -> ~ In x (btv s')).
Proof.
  intros.
  generalize dependent used.
  generalize dependent binders.
  generalize dependent used'.
  generalize dependent binders'.
  generalize dependent s'.
  induction s; intros.
  - unfold to_GU_ in H. destruct (lookup s binders); inv H; intros Hcontra; apply btv_var_contradiction in Hcontra; contradiction.
  - simpl in H.
    remember (to_GU_ used ((s, fresh_to_GU_ used binders s) :: binders) s0) as p.
    destruct p as [ [used1 binders1] s1].
    simpl in H.

    inv H.
    simpl.
    unfold not.
    intros Hcontra.
    destruct Hcontra.
    + rewrite <- H in H0.
      eapply fresh_to_GU__fresh_over_binders. eauto.
    + eapply IHs with (s' := s1) (binders := ((s,
    fresh_to_GU_ used
      binders s)
    :: binders)); eauto.
      simpl. right.
      apply in_app_iff in H0. destruct H0.
      * apply in_app_iff. left. auto.
      * apply in_app_iff. right. apply in_cons. auto.
  - simpl in H. 
    remember (to_GU_ used binders s1) as p1.
    destruct p1 as [ [used1 binders1] s1'].
    simpl in H. 
    remember (to_GU_ used1 binders s2) as p2.
    destruct p2 as [ [used2 binders2] s2'].
    inv H.
    simpl.
    apply not_in_app. split.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto.
  - inv H.
    auto.
Qed.

Lemma no_btv_in_binders used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (btv s') -> ~ In x (map snd binders)).
Proof.
  intros.
  intros Hcontra.
  assert (H_all_binders: In x (map fst binders ++ map snd binders)).
  {
    apply in_app_iff.
    right.
    auto.
  }
  eapply no_btv_in_binders' in H_all_binders; eauto.
Qed.

Lemma no_btv_in_binders_fst used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (btv s') -> ~ In x (map fst binders)).
Proof.
  intros.
  intros Hcontra.
  assert (H_all_binders: In x (map fst binders ++ map snd binders)).
  {
    apply in_app_iff.
    left.
    auto.
  }
  eapply no_btv_in_binders' in H_all_binders; eauto.
Qed.

Lemma to_GU__GU_ s R used : (forall x, In x (ftv s) -> (In x (map fst R))) -> (forall x, In x (tv s) -> In x used) -> GU (to_GU_ used R s).2.
Proof.
  generalize dependent R.
  generalize dependent used.
  induction s; intros.
  - simpl. destruct (lookup s R) eqn:lookup_x_R.
    + constructor.
    + constructor.
  - simpl.
    remember (to_GU_ used ((s, fresh_to_GU_ used R s) :: R) s0) as p.
    simpl. destruct p as [ [used' binders'] s'].
    simpl.
    constructor.
    + specialize (IHs used ((s, fresh_to_GU_ used R s) :: R)).
      rewrite <- Heqp in IHs.
      simpl in IHs.
      eapply IHs.
      * intros. 
        destr_eqb_eq s x.
        -- left. reflexivity.
        -- specialize (H x).
           assert (In x (ftv (@tmlam USort s k s0))).
           {
              apply ftv_c_lam; auto.
           }
           specialize (H H3).
           right; auto.
      * intros.
        eapply H0.
        apply tv_c_lam. auto.
    + (* no binder in s' is in ((s, fresh_to_GU_ used R s) :: R)*)
      apply no_repeated_binder with (x := (fresh_to_GU_ used R s)) in Heqp; auto.
      simpl.
      left. reflexivity.

  - simpl. 
    remember (to_GU_ used R s1) as p1.
    destruct p1 as [ [used1 binders] s1'].
    simpl. 
    remember (to_GU_ used1 R s2) as p2.
    destruct p2 as [ [used2 binders'] s2'].
    simpl.
    constructor.
    + specialize (IHs1 used R).
      rewrite <- Heqp1 in IHs1.
      simpl in IHs1.
      eapply IHs1.
      * intros.
        eapply H.
        apply ftv_c_appl. auto.
      * intros.
        eapply H0.
        apply tv_c_appl. auto.
    + specialize (IHs2 used1 R).
      rewrite <- Heqp2 in IHs2.
      simpl in IHs2.
      eapply IHs2.
      * intros.
        eapply H.
        apply ftv_c_appr. auto.
      * intros.
        eapply used_never_removed; eauto.
        eapply H0.
        apply tv_c_appr. auto.
    + intros.
      intros Hcontra.
      eapply tvs_remembered with (used' := used1) in Hcontra; eauto.
      eapply no_binder_used with (used := used1)in H1; eauto.
    + intros.
      assert (~ In x used) by now apply no_binder_used with (x := x) in Heqp1.


      assert (~ In x (btv s2')).
      {
        intros Hcontra2.
        eapply no_binder_used with (used := used1) in Hcontra2.
        contradiction Hcontra2.
        assert (In x (tv s1')).
        {
          apply extend_btv_to_tv. auto.
        } 
        eapply tvs_remembered; eauto. eauto.
      }

      assert (~ In x (ftv s2')).
      {
        intros Hcontra.
        eapply ftvs_mapped_by_R with (binders := R) (s := s2) in Hcontra.
        - 
          destruct Hcontra as [y Hcontra].
          eapply no_btv_in_binders with (x := x) in Heqp1.
          assert (In x (map snd R)).
          {
            unfold map.
            apply in_map_iff.
            exists (y, x).
            split; auto.
          }
          contradiction. assumption.
        - intros.
          specialize (H y).
          assert (In y (ftv (@tmapp BSort s1 s2))).
          {
            apply ftv_c_appr. auto.
          }
          specialize (H H5).
          apply in_map_iff_sigma in H.
          assumption.
        - eauto.
      }
      
      apply not_ftv_btv_then_not_tv; auto.
    - simpl. 
      constructor.
Qed.

Lemma id_map_helper (A : Type) (x : A) l : In x l -> In (x, x) (map (fun x => (x, x)) l).
Proof.
  intros.
  apply in_map_iff.
  exists x.
  split; auto.
Qed.

Lemma to_GU__GU s : GU (to_GU s).
Proof.
  intros.
  unfold to_GU.
  eapply to_GU__GU_; auto.
  intros.
  assert (In x (tv s)).
  {
    apply extend_ftv_to_tv in H.
    auto.
  }
  apply in_map_iff.
  exists (x, x); intuition.
  apply id_map_helper. auto.
Qed.


(* We construct s in such a way that
  - Alpha [] to original
  - GU
  - NC with respect to X and T.

  We can achieve this since we only rename binders:
  - We can always generate a alpha GU term by only changing binders
  - We can then again change some binders so that they dont capture ftvs in X or T,
    this preserves GU and Alpha.

  We should try to reuse to_GU_ machinery
*)
Definition to_GU' (X : string) (T : term) (s : term) := 
  (* By adding tvs in X and T, no binders in the resulting term can be equal to tvs in X and T.
    We do tv, because mostly tv is easier to reason about than ftv*)
  let tvs := X :: tv T ++ tv s in
  (* again we need to remove duplicates *)
  snd (to_GU_ tvs (map (fun x => (x, x)) tvs) s).


Lemma to_GU'__alpha X T s : Alpha [] s (to_GU' X T s).
Proof.
    remember (to_GU' X T s) as s'.
  unfold to_GU' in Heqs'.
  remember (map (fun x => (x, x)) (X :: tv T ++ tv s)) as R.
  rewrite Heqs'.
  assert (R ⊢ s ~ (to_GU_ (X :: tv T ++ tv s) R s).2).
  {
    eapply to_GU__alpha_'.
    - intros.
      eapply lookup_some_IdCtx_then_alphavar; eauto.
      rewrite HeqR.
      apply map_creates_IdCtx.
    - intros.
      apply id_ctx_alphavar_refl; auto.
      subst. apply map_creates_IdCtx.
    - intros.
      intuition.
  }
  eapply alpha_weaken_ids with (idCtx := R).
  - subst.
    clear H.
    induction (X :: tv T ++ tv s); simpl; constructor; auto.
  - assumption.
Qed.

Lemma to_GU'__GU X T s : GU (to_GU' X T s).
Proof.
  intros.
  unfold to_GU'.
  eapply to_GU__GU_; auto.
  - intros.
    assert (In x (X :: tv T ++ tv s)).
    {
      apply extend_ftv_to_tv in H.
      auto.
      intuition.
    }
    apply in_map_iff.
    exists (x, x); intuition.
    apply id_map_helper. auto.
  - intros. (* x in tv s, then also x in supserset of tv s*)
    intuition.
Qed.

Lemma to_GU'__NC X T s : NC (to_GU' X T s) ((X, T)::nil).
Proof.
  unfold to_GU'.
  remember (to_GU_ (X :: tv T ++ tv s) (map (fun x => (x, x)) (X :: tv T ++ tv s)) s) as p.
  destruct p as [ [used' binders'] s'].
  simpl.
  constructor.
  - constructor.
  - intros.
    eapply no_binder_used in H; eauto.
    split.
    + simpl in H. intuition.
    + simpl in H. intuition.
      apply extend_ftv_to_tv in H0.
      intuition.
Qed.



(* TODO: probably we don't need this and can do inversion once we haqve defined to_GU_app? *)
Lemma to_GU_app_unfold {B s t st} :
  st = to_GU (@tmapp B s t) -> {s' & { t' & (st = @tmapp B s' t') * Alpha [] s s' * Alpha [] t t'} }%type.
Proof.
  intros.
  remember H as H'.
  clear HeqH'.
  unfold to_GU in H.
  simpl in H.
  remember (to_GU_ _ _ s) as p.
  destruct p as [ [used binders] idk].
  remember (to_GU_ _ _ t) as q.
  destruct q as [ [used' binders'] idk'].
  simpl in H.
  exists idk. exists idk'.
  assert (Alpha [] (@tmapp B idk idk') (@tmapp B s t)).
  {
    subst.
    rewrite H'.
    eapply @alpha_sym; eauto. constructor.
    eapply to_GU__alpha.
  }
  inv H0.
  auto with α_eq_db.
  split; [split|]; eauto with α_eq_db.
Qed.

Lemma to_GU_applam_unfold {BA BL A s t st} {x : string} :
  st = to_GU (@tmapp BA (@tmlam BL x A s) t) -> {x' : string & {s' & { t' & (st = @tmapp BA (@tmlam BL x' A s') t') * Alpha ((x, x')::nil) s s' * Alpha [] t t'} } }%type.
Proof.
  intros.
  remember H as H'.
  clear HeqH'.
  eapply to_GU_app_unfold in H.
  destruct H as [s' [t' [ [H1 H2] H3] ] ].
  inv H2.
  exists y. exists s2. exists t'.
  intuition.
Qed.

Definition to_GU'' (X : string) (s : term) := to_GU' X (tmvar X) s.

Lemma to_GU''__alpha X s : Alpha [] s (to_GU'' X s).
Proof.
  apply to_GU'__alpha.
Qed.

Lemma to_GU''__GU X s : GU (to_GU'' X s).
Proof.
  apply to_GU'__GU.
Qed.

Lemma to_GU''__btv X s : ~ In X (btv (to_GU'' X s)).
Proof.
  unfold to_GU''.
  assert (NC (to_GU' X (tmvar X) s) ((X, tmvar X) :: nil)).
  {
    apply to_GU'__NC.
  }
  inv H.
  intros Hcontra.
  specialize (H5 X Hcontra). intuition.
Qed.

(* This should be easy enough. It is the same as to_GU' but without a T.
    Then we know X not in ftv s and X not in btv s.
    So then GU (tmlam X A (to_GU'' X s)) by also GU (to_GU'' X s).
*)
Lemma to_GU''__GU_lam {B} X A s : GU (@tmlam B X A (to_GU'' X s)).
Proof.
  constructor.
  - apply to_GU'__GU.
  - unfold to_GU''.
    unfold to_GU'.
    remember (to_GU_ (X
:: tv (tmvar X) ++ tv s)
  (map (fun x : string => (x, x))
  (X :: tv (tmvar X) ++ tv s))
  s) as p.
    destruct p as [ [used' binders'] s'].
    simpl.
    intros Hcontra.
    eapply no_binder_used; eauto.
    apply in_eq.
Qed.


(* Fundamental property NC is trying to capture *)
Lemma nc_helper {s sigma} :
  (forall x, In x (btv s) -> ~ In x (ftv_keys_env sigma)) ->
  NC s sigma.
Proof.
  intros Hnc_eq.
  induction sigma.
  - constructor.
  - destruct a as [a1 a2].
    constructor.
    + intros.
      apply IHsigma.
      intros x Hbtv_s.
      specialize (Hnc_eq x Hbtv_s).
      simpl in Hnc_eq.
      rewrite de_morgan2 in Hnc_eq.
      destruct Hnc_eq as [_ Hnc_eq].
      apply not_in_app in Hnc_eq as [_ Hnc_eq].
      auto.
    + intros x Hbtv_s.
      specialize (Hnc_eq x Hbtv_s).
      simpl in Hnc_eq.
      rewrite de_morgan2 in Hnc_eq.
      destruct Hnc_eq as [H_n_a1_x Hnc_eq].
      apply not_in_app in Hnc_eq as [Hnc_eq _].
      auto.
Qed.





(* We first generate p. Then we can generate t with (ftv info on p).
  then we generate s with ftv info on t and p.
    This creates the required NC properties.

    For NC sub we need some more stuff, but I think it is manageable.
    Maybe we first collect ftvs for everything and that way make sure no binder has that name.
    This should not be hard since we have empty R and we will use to_GU_' everywhere probably (where we supply additional ftvs that may not be used as binders)
  *)
Definition sconstr2 (x0 : string) (t : term) (x : string) (p s : term) :=
  let ftvs := ftv t ++ ftv p ++ ftv s ++ (x0::x::nil) in
  let R := (map (fun x => (x, x)) ftvs) in (* For to_GU_ we need that all ftvs appear in R. TODO: abstract that away*)
  (snd (to_GU_ ftvs R s) , snd (to_GU_ ftvs R t), snd (to_GU_ ftvs R p)).
(* Now s t and p all get binders not equal to any of the free variables in the other*)

Lemma sconstr2_alpha_s x0 t x p s s' t' p':
  (s', t', p') = sconstr2 x0 t x p s ->
  Alpha [] s s'.
Proof.
  intros.
  unfold sconstr2 in H.
  inv H.
  eapply @alpha_weaken_ids.
  2: { eapply to_GU__alpha_. 
      - intros.
        eapply lookup_some_IdCtx_then_alphavar; eauto.
        apply map_creates_IdCtx.
      - intros.
        exists x1.
        apply id_map_helper. auto.
        apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. auto.
    }
  apply map_creates_IdCtx.
Qed.

Lemma sconstr2_alpha_t x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s->
  Alpha [] t t'.
Proof.
  intros.
  unfold sconstr2 in H.
  inv H.
  eapply @alpha_weaken_ids.
  2: { eapply to_GU__alpha_. 
      - intros.
        eapply lookup_some_IdCtx_then_alphavar; eauto.
        apply map_creates_IdCtx.
      - intros.
        exists x1.
        apply id_map_helper. auto.
        apply in_app_iff. left. auto.
    }
  apply map_creates_IdCtx.
Qed.

Lemma sconstr2_alpha_p x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s->
  Alpha [] p p'.
Proof.
  intros.
  unfold sconstr2 in H.
  inv H.
  eapply @alpha_weaken_ids.
  2: { eapply to_GU__alpha_. 
      - intros.
        eapply lookup_some_IdCtx_then_alphavar; eauto.
        apply map_creates_IdCtx.
      - intros.
        exists x1.
        apply id_map_helper. auto.
        apply in_app_iff. right. apply in_app_iff. left. auto.
    }
  apply map_creates_IdCtx.
Qed.

Lemma in_id_map_then_in_generator (x : string) l :
  In (x, x) (map (fun x => (x, x)) l) -> In x l.
Proof.
  intros.
  induction l.
  - inversion H.
  - simpl in H.
    destruct H.
    + inversion H; subst. left. reflexivity.
    + right. apply IHl. auto.
Qed.


Lemma in_generator_then_in_id_map (x : string) l :
  In x l -> In (x, x) (map (fun x => (x, x)) l).
Proof.
  intros.
  induction l.
  - inversion H.
  - simpl.
    destruct H.
    + subst. left. reflexivity.
    + right. apply IHl. auto.
Qed.

Lemma in_id_map_then_id (x y : string) l :
  In (x, y) (map (fun x => (x, x)) l) -> x = y.
Proof.
  intros.
  induction l.
  - inversion H.
  - simpl in H.
    destruct H.
    + inversion H; subst. reflexivity.
    + apply IHl. auto.
Qed.

Lemma sconstr2_nc_s x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  NC s' ((x, p')::nil).
Proof.
  intros.
  unfold sconstr2 in H.
  inv H.
  remember (to_GU_ _ _ s) as GU_s.
  destruct GU_s as [ [used_s binders_s] s'].
  remember (to_GU_ _ _ p) as GU_p.
  destruct GU_p as [ [used_p binders_p] p'].
  simpl.
  constructor.
  - constructor.
  - intros.
    eapply no_binder_used in H; eauto.

    

    destr_eqb_eq y x.
    + contradiction H.
      apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_cons. apply in_eq.
    + simpl. split; auto.

      (* todo, we could maybe better use no_ftvs_preserved_id*)
      
      
      remember (map
        (fun x1 : string =>
      (x1, x1))
        (ftv t ++
      ftv p ++
      ftv s ++ [x0; x])) as binders.
      assert (Hftvs_mapped_pre: forall y, In y (ftv p) -> { x & In (y, x) binders}).
      {
        intros.
        exists y0.
        subst.
        apply in_generator_then_in_id_map. auto.
        apply in_app_iff. right. apply in_app_iff. left. auto.
      }
      
      assert (forall x, In x (ftv p') -> exists y, In (y, x) binders).
      {
        
        eapply (ftvs_mapped_by_R  (ftv t ++
            ftv p ++
            ftv s ++ [x0; x]) binders p p' used_p binders_p Hftvs_mapped_pre).
            eauto.
      }
      intros Hcontra.
      specialize (H1 y Hcontra).
      assert (In (y, y) binders).
      {
        destruct H1 as [y0 Hyy0].
        subst.
        remember Hyy0 as Hyy0'.
        clear HeqHyy0'.
        apply in_id_map_then_id in Hyy0. subst. auto.
      } 
      assert (In y ((ftv t ++
ftv p ++
ftv s ++ [x0; x]))).
      {
        apply in_id_map_then_in_generator. subst. auto.
      }
      contradiction.
Qed.

Lemma sconstr2_preserves_ftv_t x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  forall y, In y (ftv t') -> In y (ftv t).
Proof.
  intros.
  unfold sconstr2 in H.
  inv H.
  remember (map (fun x1 : string => (x1, x1))
    (ftv t ++ ftv p ++ ftv s ++ [x0; x])) as R.
  remember ((to_GU_ (ftv t ++ ftv p ++ ftv s ++ [x0; x]) R t).2 
    ) as t'.
  assert (R ⊢ t ~ t').
  - rewrite Heqt'.
    eapply to_GU__alpha_. 
    + intros.
      eapply lookup_some_IdCtx_then_alphavar; eauto.
      rewrite HeqR.
      apply map_creates_IdCtx.
    + intros.
      exists x1.
      subst.
      apply in_generator_then_in_id_map. auto.
      apply in_app_iff. left. auto.
  - assert ([] ⊢ t ~ t').
    {
      eapply alpha_weaken_ids with (idCtx := R); eauto.
      rewrite HeqR.
      apply map_creates_IdCtx.
    }
    eapply alpha_preserves_ftv; eauto with α_eq_db.
Qed.

Lemma sconstr2_preserves_ftv_p x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  forall y, In y (ftv p') -> In y (ftv p).
Proof.
  intros.
  unfold sconstr2 in H.
  inv H.
  remember (map (fun x1 : string => (x1, x1))
    (ftv t ++ ftv p ++ ftv s ++ [x0; x])) as R.
  remember ((to_GU_ (ftv t ++ ftv p ++ ftv s ++ [x0; x]) R p).2 
    ) as p'.
  assert (R ⊢ p ~ p').
  - rewrite Heqp'.
    eapply to_GU__alpha_. 
      + intros.
        eapply lookup_some_IdCtx_then_alphavar; eauto.
        rewrite HeqR.
        apply map_creates_IdCtx.
    + intros.
      exists x1.
      subst.
      apply in_generator_then_in_id_map. auto.
      apply in_app_iff. right. apply in_app_iff. left. auto.
  - assert ([] ⊢ p ~ p').
    {
      eapply alpha_weaken_ids with (idCtx := R); eauto.
      rewrite HeqR.
      apply map_creates_IdCtx.
    }
    eapply alpha_preserves_ftv; eauto with α_eq_db.
Qed.

Lemma sconstr2_fresh_over_x0 y x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  ((In y (btv s')) \/  In y (btv t') \/ In y (btv p')) ->
  y <> x0 /\ y <> x.
Proof.
  intros.
  inversion H.
  remember (to_GU_ _ _ s) as GU_s.
  destruct H0 as [H0_s' | [H0_t' | H0_p'] ].
  {
    destruct GU_s as [ [used_s binders_s] s''].
    inv H2.
    simpl in H0_s'.
    assert (~ In y  (ftv t ++ ftv p ++ ftv s ++ [x0; x])).
      { eapply no_binder_used; eauto. }
    repeat apply not_in_app in H0 as [_ H0].
    apply not_in_cons in H0 as [H0 H2]; auto.
    apply not_in_cons in H2 as [H2 _].
    split; auto.
  }
  {
    remember (to_GU_ _ _ t) as GU_t.
    destruct GU_t as [ [used_t binders_t] t''].
    inv H2.
    simpl in H0_t'.
    assert (~ In y  (ftv t ++ ftv p ++ ftv s ++ [x0; x])).
      { eapply no_binder_used; eauto. }
    repeat apply not_in_app in H0 as [_ H0].
    apply not_in_cons in H0 as [H0 H2]; auto.
    apply not_in_cons in H2 as [H2 _].
    split; auto.
  }
  {
    remember (to_GU_ _ _ p) as GU_p.
    destruct GU_p as [ [used_p binders_p] p''].
    inv H2.
    simpl in H0_p'.
    assert (~ In y  (ftv t ++ ftv p ++ ftv s ++ [x0; x])).
      { eapply no_binder_used; eauto. }
    repeat apply not_in_app in H0 as [_ H0].
    apply not_in_cons in H0 as [H0 H2]; auto.
    apply not_in_cons in H2 as [H2 _].
    split; auto.
  }
Qed.

Lemma sconstr2_nc_s_t x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  NC s' ((x0, t')::nil).
Proof.
  intros.
  constructor. constructor.
  intros.
  split.
  - eapply sconstr2_fresh_over_x0 in H as [Hnot_x0 _];  eauto.
  - intros Hcontra.
    assert (In y (ftv t)).
    { eapply sconstr2_preserves_ftv_t; eauto. }
    inversion H; clear H4; clear H5.
    remember (to_GU_ _ _ s) as GU_s.
    destruct GU_s as [ [used_s binders_s] s''].
    inv H3.
    eapply no_binder_used; eauto.
    apply in_app_iff. left. auto.
Qed.

Lemma sconstr2_nc_t x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  NC t' ((x, p')::nil).
Proof.
  intros.
  constructor. constructor.
  intros.
  split.
  - eapply sconstr2_fresh_over_x0 in H as [_ Hnot_x].  eauto. right. auto.
  - intros Hcontra.
    assert (In y (ftv p)).
    { eapply sconstr2_preserves_ftv_p; eauto. }
    inversion H.
    remember (to_GU_ _ _ t) as GU_t.
    destruct GU_t as [ [used_t binders_t] t''].
    inv H4.
    eapply no_binder_used; eauto.
    apply in_app_iff. right. apply in_app_iff. left. auto.
Qed.

(* We have control over all binders in s' and p' and subs does not introduce new binders,
  hence we can create a construction that satisfies this*)
Lemma sconstr2_nc_sub x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  NC (psubs ((x, p')::nil) s') ((x0, (psubs ((x, p')::nil) t'))::nil).
Proof.
  intros.
  constructor. constructor.
  intros.
  apply in_btv_psubs_then_in_constituents in H0 as [H_btv_s' | H_btv_p'].
  - split.
    + eapply sconstr2_fresh_over_x0 in H as [Hnot_x0 Hnot_x]; eauto.
    + apply not_in_constituents_then_not_in_ftv_psubs.
      * intros Hcontra.
        assert (In y (ftv t)).
        { eapply sconstr2_preserves_ftv_t; eauto. }
        inversion H.
        remember (to_GU_ _ _ s) as GU_s.
        destruct GU_s as [ [used_s binders_s] s''].
        inv H2.
        eapply no_binder_used; eauto.
        apply in_app_iff. left. auto.
      * simpl. rewrite app_nil_r.
        intros Hcontra.
        assert (In y (ftv p)).
        { eapply sconstr2_preserves_ftv_p; eauto. }
        inversion H.
        remember (to_GU_ _ _ s) as GU_s.
        destruct GU_s as [ [used_s binders_s] s''].
        inv H4.
        eapply no_binder_used; eauto.
        apply in_app_iff. right. apply in_app_iff. left. auto.
  - destruct H_btv_p' as [p'' [H_eq H_btv_p'] ].
    inversion H_eq; try contradiction. simpl in H0. subst.
    split.
    + eapply sconstr2_fresh_over_x0 in H as [Hnot_x0 Hnot_x]; eauto.
    + apply not_in_constituents_then_not_in_ftv_psubs.
      * intros Hcontra.
        assert (In y (ftv t)).
        { eapply sconstr2_preserves_ftv_t; eauto. }
        inversion H.
        remember (to_GU_ _ _ p) as GU_p.
        destruct GU_p as [ [used_p binders_p] p'''].
        inv H4.
        eapply no_binder_used; eauto.
        apply in_app_iff. left. auto.
      * simpl. rewrite app_nil_r.
        intros Hcontra.
        assert (In y (ftv p)).
        { eapply sconstr2_preserves_ftv_p; eauto. }
        inversion H.
        remember (to_GU_ _ _ p) as GU_p.
        destruct GU_p as [ [used_p binders_p] p'''].
        inv H4.
        eapply no_binder_used; eauto.
        apply in_app_iff. right. apply in_app_iff. left. auto.
Qed.

Opaque sconstr2.

Create HintDb sconstr2_db.
Hint Resolve sconstr2_alpha_s sconstr2_alpha_t sconstr2_nc_sub sconstr2_nc_s sconstr2_nc_t sconstr2_nc_s_t : sconstr2_db.

Require Import List.
Import ListNotations.


Definition string_pair_dec (p1 p2 : string * string) : {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality; apply string_dec.
Defined.

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
Import ListNotations.


(* NOT DIFFICULT *)
Lemma alphavar_vacuous_prepend R1 R2 s s' :
  AlphaVar R2 s s' -> lookup s R1 = None -> lookup_r s' R1 = None -> AlphaVar (R1 ++ R2) s s'.
Proof.

  intros.
  induction R1.
  - simpl. auto.
  - destruct a.
    simpl.
    constructor.
    + intros Hcontra.
      subst.
      simpl in H0.
      rewrite String.eqb_refl in H0.
      inversion H0.
    + intros Hcontra.
      subst.
      simpl in H1.
      rewrite String.eqb_refl in H1.
      inversion H1.
    + eapply IHR1; eauto.
      * simpl in H0. destruct_match. auto.
      * simpl in H1. destruct_match. auto.
Qed.

Lemma alphavar_idk_helper R1 R2 R2' s s' :
  (AlphaVar R2 s s' -> AlphaVar R2' s s') -> (AlphaVar (R1 ++ R2) s s' -> AlphaVar (R1 ++ R2') s s').
Proof.
  intros.
  apply alphavar_lookup_helper in H0.
  destruct H0 as [Hyes | Hno].
  - destruct Hyes as [Hs Hs'].
    apply lookup_split_app_helper in Hs; auto; clear Hs'.
    destruct Hs as [HsR1 | HsR2].
    + eapply lookup_some_extend_helper in HsR1; eauto.
      eapply lookup_some_then_alphavar; intuition.
    + destruct HsR2 as [[[HsR1_None Hs'R1_None] HsR2_Some] Hs'R2_Some].
      assert (AlphaVar R2 s s').
      {
        eapply lookup_some_then_alphavar; eauto.
      } 
      specialize (H H0).
      apply alphavar_vacuous_prepend. auto. auto. auto.
  - destruct Hno as [ [Hs Hs'] Heq]; subst.
    apply lookup_app_none_helper in Hs as [HsR1 HsR2].
    apply lookup_r_app_none_helper in Hs' as [Hs'R1 Hs'R2].
    assert (AlphaVar R2 s' s').
    {
      eapply lookup_none_then_alpharefl; eauto.
    }
    specialize (H H0).
    eapply alphavar_vacuous_prepend; auto.
Qed.

Definition freshen2 used to_freshen :=
  fold_right
    (fun x acc =>
      let fresh_var := fresh_to_GU_ (used ++ to_freshen) acc x in
      (x, fresh_var) :: acc) (* New element is added at the front in `fold_right` *)
    [] to_freshen.


Definition freshen used to_freshen := fold_left
      (fun acc x =>
        let fresh_var := fresh_to_GU_ used acc x in
        (x, fresh_var) :: acc) to_freshen [].


(* forall ftvs in s, lookup that in R, to get (x, y) and add that to the new R*)
Definition a_R_constr R (s s' : term) t : list (string * string) :=
  let used := tv s ++ tv s' ++ tv t ++ (map fst R) ++ (map snd R) in

  (* rename those ftvs in t, that are not ftvs in s to fresh stuff
    all ftvs in s are already mapped by R to something else, t should follow the same 
      behaviour for these ftvs, since they refer to the same ftv.

      This also means we can easily add Rfr in front of R and still keep s-alpha
  *)
  let to_freshen := list_diff string_dec (ftv t) (ftv s) in
  let Rfr := freshen2 used to_freshen in
  Rfr ++ R.

  (*
    Suppose we have s = x   s' = y
    R = [x, y]

                    t = y   t' = ?
  *)


(* Must ahve implies, since alphavar does not imply that x and y in R.*)
(* TODO: Does this one really help so much over just alphavar_lookup_helper?*)
Lemma av_lookup_implies_right R x y :
  AlphaVar R x y -> (lookup x R = Some y -> lookup_r y R = Some x).
Proof.
(*SEE alphavar_lookup_helper *)
  intros.
  apply alphavar_lookup_helper in H.
  destruct H as [Hyes | Hno].
  - intuition.
  - destruct Hno as [[Hno _] _ ].
    rewrite Hno in H0.
    inversion H0.
Qed.

Lemma KindOfUniqueRhsFreshMultiple used R l : 
  KindOfUniqueRhs R -> KindOfUniqueRhs ((freshen2 (used ++ map fst R ++ map snd R) l ) ++ R).
Proof.
  unfold freshen2.
  remember ((used ++ map fst R ++ map snd R) ++ l) as used'.
  (* I find this interesting. We are doing this to lose information, it is like we are weakening the induction hypothesis!*)
  assert ({l' &  (used ++ map fst R ++ map snd R) ++ l' = (used ++ map fst R ++ map snd R) ++ l}%type).
  {
    exists l. auto.
  }
  destruct H as [l' Heq].
  rewrite <- Heq in Heqused'.
  clear Heq.
  subst.

  induction l.
  - simpl. auto.
  - intros.
    unfold freshen2.
    change (a :: l) with ([a] ++ l).
    rewrite fold_right_app.
    simpl.
    remember ((fold_right
        (fun (x : string) (acc : list (string * string)) =>
      _
      :: acc)
        []
        l)) as R''.
    unfold freshen2 in IHl.
    specialize (IHl H).
    change ((a, fresh_to_GU_ ((used ++ map fst R ++ map snd R) ++ (a :: l)) R'' a) :: R'' ++ R) with ((a, fresh_to_GU_ ((used ++ map fst R ++ map snd R) ++ (a :: l)) R'' a) :: (R'' ++ R)).

    eapply KindOfUniqueRhsFresh; auto.
    + intros.
      rewrite map_app in H0.
      apply in_app_iff in H0.
      rewrite map_app in H0.
      destruct H0.
      * apply in_app_iff in H0.
        destruct H0; intuition.
        left. apply in_app_iff. left. apply in_app_iff. right. intuition.
      * apply in_app_iff in H0.
        destruct H0; intuition.
        left. apply in_app_iff. intuition.
Qed.

(* We have to prove over in l and in used simultaneously, because things move from l to used*)
Lemma freshen2__fresh_not_generator {used l } {x : string } :
  (In x l \/ In x used) -> ~ In x (map snd (freshen2 used l)).
Proof.
  intros Hin.
  generalize dependent used.
  induction l; intros.
  - simpl in Hin. simpl. auto.
  - destruct Hin.
    + (* In x l case*)
      destruct H.
      *
      { 
        subst. 
        unfold freshen2.
        simpl.
        apply de_morgan2.
        split.
        * assert (~ In (fresh_to_GU_ (used ++ x :: l)
    (fold_right
    (fun (x0 : string) (acc : list (string * string)) =>
  (x0, fresh_to_GU_ (used ++ x :: l) acc x0) :: acc)
    []
    l) x) (used ++ (x :: l))).
          {
            apply fresh_to_GU__fresh_over_ftvs.
          }
          apply not_in_app in H as [_ H].
          apply not_in_cons in H as [H _].
          auto.
        * assert (((used ++ [x]) ++ l) = (used ++ x :: l)).
        { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
          rewrite <- H.
          eapply IHl. (* Here we use IHL where we need the simultaneous induction prniciple over used.*)
          right.
          apply in_app_iff.
          right.
          apply in_eq.
    }
    * {
      simpl.
      apply de_morgan2.
      split.
      --
        (* x not in ftvs of fresh_to_GU, but also x in l, which is in ftvs/used *)
        assert (~ In (fresh_to_GU_ (used ++ a :: l)
            (fold_right (fun (x0 : string) (acc : list (string * string)) =>
            (x0, fresh_to_GU_ (used ++ a :: l) acc x0) :: acc) [] l) a ) 
            
            (used ++ a :: l)).
        { 
          apply fresh_to_GU__fresh_over_ftvs.
        }
        intros Hcontra.
        apply not_in_app in H0 as [_ H0].
        apply not_in_cons in H0 as [_ H0].
        subst.
        contradiction.
      -- simpl in IHl.
          assert ( HChange: ((used ++ [a]) ++ l) = (used ++ a :: l)).
        { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
          rewrite <- HChange.
          eapply IHl.
          left. auto.
    }
  + (* In x used case *)
    simpl.
    apply de_morgan2.
    split.
    * remember ((fold_right _ _ _)) as fld.
      assert (~ In (fresh_to_GU_ (used ++ a :: l) fld a) (used ++ a :: l)).
      { apply fresh_to_GU__fresh_over_ftvs. }
      apply not_in_app in H0 as [H0 _].
      intros Hcontra.
      subst.
      contradiction.
    * unfold freshen2 in IHl.
      assert (HChange: ((used ++ [a]) ++ l) = (used ++ a :: l)).
      { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
      rewrite <- HChange.
      eapply IHl.
      right. apply in_app_iff. left. auto.
Qed.

Lemma freshen2__fresh_generator {used l } {y : string } :
  In y (map snd (freshen2 used l)) -> ~ In y l.
Proof.
  intros Hin Hcontra.
  eapply or_introl in Hcontra.
  eapply @freshen2__fresh_not_generator with (used := used) in Hcontra.
  contradiction.
Qed.

Lemma freshen2__fresh_map_snd {used l } {y : string } :
  In y (map snd (freshen2 used l)) -> ~ In y used.
Proof.
  intros Hin Hcontra.
  eapply or_intror in Hcontra.
  eapply @freshen2__fresh_not_generator with (l := l) in Hcontra.
  contradiction.
Qed.

Lemma in_freshen2_then_in_generator used l x :
  In x (map fst (freshen2 used l)) -> In x l.
Proof.
  intros Hin.
  generalize dependent used.
  induction l; intros.
  - simpl in Hin. auto.
  - simpl in Hin.
    destruct Hin.
    + subst. simpl. auto.
    + unfold freshen2 in IHl.
      assert (Hchange: ((used ++ [a]) ++ l) = (used ++ a :: l)).
        { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
      rewrite <- Hchange in H.
      eapply IHl in H.
      simpl.
      right.
      auto.
Qed.

Lemma in_generator_then_in_freshen2 used l x :
  In x l -> In x (map fst (freshen2 used l)).
Proof.
  intros Hin.
  generalize dependent used.
  induction l; intros.
  - simpl in Hin. auto.
  - unfold freshen2.
    simpl.
    destruct Hin.
    + subst. simpl. auto.
    + right.
      assert (Hchange: ((used ++ [a]) ++ l) = (used ++ a :: l)).
      { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
      rewrite <- Hchange.
      eapply IHl in H.
      unfold freshen2 in H.
      eauto.
Qed.

(*
THE FOLLOWING DEPENDS ON SOME CONSTRUCTIONS SO THAT IS WHY IT IS HERE:
*)

Lemma not_ftv_to_not_tv {x s}:
  ~ (In x (ftv s)) -> prod (~ (In x (tv (to_GU'' x s)))) (Alpha [] s (to_GU'' x s)).
Proof.
  intros.
  split.
  - apply not_ftv_btv_then_not_tv.
    + eapply @alpha_preserves_no_ftv with (x := x) (s := s); auto.
      apply to_GU''__alpha. constructor.
    + apply to_GU''__btv.
  - apply to_GU''__alpha.
Qed.

Lemma alpha_trans3 {R s s' s'' s'''}:
  Alpha [] s s' -> Alpha R s' s'' -> Alpha [] s'' s''' -> Alpha R s s'''.
Proof.
  intros.
  eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R).
  - { apply id_left_trans. } 
  - apply alpha_extend_ids. apply ctx_id_left_is_id. eauto.
  - eapply @alpha_trans with (ren := R) (ren' := ctx_id_right R).
    + apply id_right_trans.
    + eauto.
    + apply alpha_extend_ids. apply ctx_id_right_is_id. eauto.
Qed.

Lemma alpha_extend_vacuous_ftv {x x' s s' R}:
  ~ (In x (ftv s)) -> ~ (In x' (ftv s')) -> Alpha R s s' -> Alpha ((x, x')::R) s s'.
Proof.
  intros.
  apply not_ftv_to_not_tv in H as [Htv_s Ha_s].
  apply not_ftv_to_not_tv in H0 as [Htv_s' Ha_s'].
  assert (R ⊢ (to_GU'' x s) ~ (to_GU'' x' s')). {
    apply @alpha_trans3 with (s' := s) (s'' := s'); auto.
    eapply @alpha_sym. constructor. auto.
  }
  apply @alpha_trans3 with (s' := to_GU'' x s) (s'' := to_GU'' x' s') (s''' := s'); auto.
  - apply alpha_extend_vacuous; auto.
  - eapply @alpha_sym. constructor. auto.
Qed.

Lemma alpha_vacuous_R {s s' R1 R2}:
  (forall x, In x (map fst R1) -> (~ In x (ftv s))) -> (forall x', In x' (map snd R1) -> ~ In x' (ftv s')) -> Alpha R2 s s' -> Alpha (R1 ++ R2) s s'.
Proof.
  intros.
  induction R1.
  - rewrite app_nil_l. auto.
  - destruct a as [a1 a2].
    apply alpha_extend_vacuous_ftv.
    + apply H. apply in_eq.
    + apply H0. apply in_eq.
    + apply IHR1.
      * intros. eapply H. apply in_cons. auto.
      * intros. eapply H0. apply in_cons. auto.
Qed.

Require Import Coq.Program.Equality.

Lemma αctx_vacuous_R R σ σ' :
  (forall x, In x (map fst R) -> (~ In x (ftv_keys_env σ))) -> (forall x', In x' (map snd R) -> ~ In x' (ftv_keys_env σ')) -> αCtxSub [] σ σ' -> αCtxSub R σ σ'.
Proof.
  intros Hvac1 Hvac2 Ha.
  dependent induction σ.
  - inversion Ha; subst. constructor.
  - inversion Ha; subst.
    constructor.
    + eapply IHσ; eauto; intros.
      * 
        specialize (Hvac1 x0 H).
        simpl in Hvac1. apply de_morgan2 in Hvac1 as [_ Hvac1].
        apply not_in_app in Hvac1 as [_ Hvac1]. auto.
      * specialize (Hvac2 x' H).
        simpl in Hvac2. apply de_morgan2 in Hvac2 as [_ Hvac2].
          apply not_in_app in Hvac2 as [_ Hvac2]. auto.
    + inversion H3; subst.
      apply alphavar_refl_weaken_vacuouss. 
      * intros Hcontra.
        apply Hvac1 in Hcontra. simpl in Hcontra. 
        apply de_morgan2 in Hcontra as [Hcontra _].
        contradiction.
      * intros Hcontra.
        apply Hvac2 in Hcontra. simpl in Hcontra. 
        apply de_morgan2 in Hcontra as [Hcontra _].
        contradiction.
    + assert ((R ++ nil) ⊢ t ~ t').
      { apply alpha_vacuous_R.
        - intros.
        apply Hvac1 in H. simpl in H. apply de_morgan2 in H as [_ H].
        apply not_in_app in H as [H _]. auto.
        - intros.
        apply Hvac2 in H. simpl in H. apply de_morgan2 in H as [_ H].
        apply not_in_app in H as [H _]. auto.
        - auto.
      }
      rewrite app_nil_r in H.
      auto.
Qed.
(* END OF THAT*)

Search "alphavar".

Lemma a_R_constr_helper R R' s s' t x y :
  R' = @a_R_constr R s s' t ->
  
  In x (ftv t) ->
  lookup x R' = Some y ->
  Alpha R s s' ->
  AlphaVar R' x y.
Proof.
  intros.
  unfold a_R_constr in H.
  remember (freshen2 _ _) as Rfr.
  rewrite H in H1.
  apply lookup_app_or_extended in H1 as [H_in_fresh | [H_ni_fresh H_in_strip] ].
  - assert (AlphaVar Rfr x y).
    {
      assert (KindOfUniqueRhs (Rfr ++ nil)).
      {
        subst.
        assert ((tv s ++
            tv s' ++
            tv t ++ map fst R ++ map snd R) = (tv s ++
            tv s' ++
            tv t ++ map fst R ++ map snd R) ++ (@map (string * string) string fst []) ++ (@map (string * string) string snd [])).
        { simpl. rewrite app_nil_r. auto. }
        rewrite H.
        eapply KindOfUniqueRhsFreshMultiple.
        unfold KindOfUniqueRhs. intros. inversion H1.
      }
      unfold KindOfUniqueRhs in H1. repeat rewrite app_nil_r in H1.
      eapply H1; auto.
    }
  
    assert (lookup_r y (Rfr ++ R) = Some x).
    {
      apply lookup_r__app.
      apply av_lookup_implies_right in H1; auto.
    }
    rewrite H.
    eapply lookup_some_then_alphavar; eauto.
    + apply lookup_app_r; auto. 

  - 
    assert (AlphaVar R x y).
    {
      assert (In x (ftv s)) by admit. (* By lookup x Rfr = None*)
      (* Suppose to the contrary that there exists z, s.t. lookup_r y R = z
          with z <> x.

          By R ⊢ s ~ s' and x in ftv s, we know that needs to be mapped to y,
          but by lookup_r y R = z, that needs to be mapped back to z, contradiction.

        *)

      admit.
    }
    assert (lookup x R' = Some y).
    {
      rewrite H.
      apply lookup_none_app; auto.
      
    }
    assert (lookup_r y R' = Some x).
    {
      assert (lookup_r y Rfr = None).
      {
        assert (In y (map snd R)).
        {
          apply lookup_In in H_in_strip.
          apply in_map_iff.
          exists ((x, y)). simpl. split; auto.
        }
        
        assert (In y ((tv s ++
            tv s' ++
            tv t ++
            map fst R ++
            map snd R))).
        {

          apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. auto.
        }
            remember ((tv s ++
              tv s' ++
              tv t ++
              map fst R ++
              map snd R)) as used.
        assert (~ In y (map snd Rfr)).
        {
          rewrite HeqRfr.
          intros Hcontra.
          eapply freshen2__fresh_map_snd in Hcontra.
          contradiction.
        }
        apply not_ex__lookup_r_none. auto.
      }
      rewrite H.
      eapply lookup_r__extend.
      + auto.
      + apply alphavar_lookup_helper in H1.
        destruct H1.
        * destruct p. auto.
        * destruct p. destruct p. rewrite e0 in H_in_strip. inversion H_in_strip.
    }
    eapply lookup_some_then_alphavar; eauto.
Admitted.

(* Let t = Var x <*> Var y.     t' = Var v    [x, v] ⊢ t ~ t'
   Let s = (λx. x) * y
   Let s' = (λx. x) * z
   Let R = [y, z].

   Dan willen we vrije variabelen in t renamen.
*)
Definition a_constr {R} {s s' : term} t : prod (list (string * string)) (term) :=
  let R' := @a_R_constr R s s' t in
  let used' := tv s ++ tv s' ++ tv t ++ (map fst R') ++ (map snd R') in 
  (R', snd (to_GU_ used' R' t)).

Lemma a_R_constr_alpha_s R s s' t R' :
  R' = a_R_constr R s s' t ->
  Alpha R s s' ->
  Alpha R' s s'.
Proof.
  intros.
  unfold a_R_constr in H.
  remember (freshen2 _ _) as Rfr.
  rewrite H.
  eapply alpha_vacuous_R.
  - intros. 
    remember ((tv s ++
        tv s' ++
        tv t ++
        map fst R ++
        map snd R)) as used.
    intros Hcontra.
    apply list_diff_not with (l1 := (ftv t)) in Hcontra.
    rewrite HeqRfr in H1.
    apply in_freshen2_then_in_generator in H1.
    contradiction.
  - intros.
    rewrite HeqRfr in H1.
    apply freshen2__fresh_map_snd in H1.
    apply not_in_app in H1 as [_ H1].
    apply not_in_app in H1 as [H1 _].
    intros Hcontra.
    apply extend_ftv_to_tv in Hcontra.
    contradiction.
  - auto.
Qed.

(* Useful helper lemma that captures the AlphaVar relation *)
Lemma alphavar_id_helper {R x y} :
  AlphaVar R x y ->
  ~ In x (map fst R) ->
  y = x.
Proof.
  intros Ha Hno.
  induction Ha; auto.
  - simpl in Hno. intuition.
  - eapply IHHa.
    simpl in Hno. intuition.
Qed.
(* suppose   that   (x'  x) in R

suppose s = x. then s' = x. then s should be x' again. contradiction
*)
(* The crux of a_constr__t_alpha*)
Lemma alpha_contradiction_helper R s s' x :
  Alpha R s s' ->
  ~ In x (map fst R) ->
  In x (ftv s) ->
  ~ In x (map snd R).
Proof.
  intros.
  induction H.
  - apply ftv_var in H1; subst.
    assert (y = x0) by apply (alphavar_id_helper a H0).

    induction a.
    + auto.
    + simpl in H0. intuition.
    + subst.
      simpl.
      apply de_morgan2.
      split; auto.
      eapply IHa; eauto.
      simpl in H0. apply de_morgan2 in H0. destruct H0; auto.

  - assert (~ In x (map snd ((x0, y)::sigma))).
    {
      eapply IHAlpha.
      assert (x <> x0).
      {
        simpl in H1.
        apply in_remove in H1.
        intuition.
      }
      simpl. intuition.
      eapply ftv_lam_helper; eauto.
    }
    simpl in H2.
    apply de_morgan2 in H2.
    destruct H2 as [_ H2].
    auto.
  - simpl in H1.
    apply in_app_or in H1.
    destruct H1.
    + eapply IHAlpha1; eauto.
    + eapply IHAlpha2; eauto.
  - inversion H1.
Qed.

Lemma map_pair_helper {A : Type} (x : string) l (f : A) :
  In x l -> In x (map fst ((map (pair^~ f) l))).
Proof.
  intros.
  apply in_map_iff.
  exists (x, f).
  simpl.
  split.
  auto.
  apply in_map with (f := pair^~ f) in H.
  auto.
Qed.

Lemma a_constr__t_alpha {R s s' t R' t'} :
  (R', t') = @a_constr R s s' t ->
  Alpha R s s' ->
  Alpha R' t t'.
Proof.
  unfold a_constr.
  intros.
  inversion H.
  apply to_GU__alpha_'.
  - intros.
    eapply a_R_constr_helper.
    + eauto.
    + auto.
    + auto.
    + auto.
  - intros.
    rewrite <- H2.
    apply lookup_none_then_no_key in H4.

    assert (In x (ftv s)).
    {
      unfold a_R_constr in H3.
      remember (freshen2 _ _) as frMap.

      destruct (in_dec string_dec x (ftv s)).
      - auto.
      - exfalso.
      
         assert (In x  (list_diff string_dec
  (ftv t) (ftv s))).
        {
          apply list_diff_helper.
          auto. auto.
        } 
        exfalso.

        assert (In x (map fst frMap)).
      {

      
        subst.
        remember (list_diff _ _ _) as l.
        eapply in_generator_then_in_freshen2.
        auto.
      }

      unfold a_R_constr in H4.
      rewrite <- HeqfrMap in H4.
      rewrite map_app in H4.
      apply not_in_app in H4. destruct H4 as [H4 _].
      contradiction.


    }

    
    assert (~ In x (map snd R')).
    {
      (* Then there exists x' s.t. (x', x) in (strip_R R)*)
      eapply alpha_contradiction_helper.
      eapply a_R_constr_alpha_s; eauto.
      subst. auto.
      auto.
    }

    apply alphavar_refl_weaken_vacuouss.
    + subst. auto.
    + subst. auto.
  - intros.
    apply in_or_app.
    intuition.
Qed.

Lemma a_constr__s_alpha {R s s' t R' t'} :
  (R', t') = @a_constr R s s' t ->
  Alpha R s s' ->
  Alpha R' s s'.
Proof.
  intros.
  unfold a_constr in H.
  inversion H.
  eapply a_R_constr_alpha_s with (R' := R') (t := t) in H0; eauto.
  subst.
  eauto.
Qed.

(*

  Forall x, y in R, we do lookup x R = Some y, then we prepend x, y to R.
  Let R = (x, x'), (y, x')   and s = z   s' = z.

  Now let t = tmapp y x' z. 



*)


    (*
    THIS DOES NOT WORK, SOLUTION IS THE NEXT LIST OF POINTS AND T_CONSTR
      Doing an alpha argument on s itself does not work. It seems like we are then forced to still have NC s sigma
    NOOOOO DOESNT WORK: we cannot know αCtxSub (X, y) sigma sigma'
      So:
      1. We try to rename binders in s instead of in t. We need to rename all sorts of things then
      2. In the lam case we need to extend the subsitution with (X, t)  and (y, t').   and R = (X, y).
      3. We have a problem if X free in sigma. And we do not have no_capture to stop this (by binder in s)...
      4. What does this correspond to?: We would have capture.
    
    *)

(* 1. First we change all binders in t to  fresh binders wrs all tv in sigma and s. This process also makes it GU.
      - t' will be added to sigma, and we need to keep the 2nd Uhm property: hence fi all binders in t' are fresh, they cannot be tvs in s, and no issues

   2. We collect all binders in s and in sigma into a list  bs
      - we know these binders are not binders in t'. But they can be free variables.
      - We can safely rename them to fresh variables (rename can safely fall through lambdas, because the lhs and rhs of rename are not equal to binder names by definiton)

   3. R is then going from bs to fresh(bs). Is this problematic?

    3.1  By GU s we have that nothing in R is an ftv in s, hence we have R ⊢ s ~ s.
     .2  we rename binders in sigma, by 1st UHM they are not free in s, so we can safely rename.
     .3  By 2nd Uhm (GU uhm), we know that binders in sigma are not free in sigma, so we safely get R ⊢ sigma ~ sigma
     .4  what about binders in s that are free in sigma? If they are free in t we have a problem, becaue
          then they will be renamed in sigma and no longer R ⊢ sigma ~ sigma.
          - Not allowing this in the first place still allows identity subsitutions: they should only have to change ftvs
          - Can we then still extend with (x, t')?
            - x was a binder in (tmlam x A s), hence it is not a binder in s by GU so not problem
            - t': we have to look at ftvs in t'. they cannot be binders in s. But we renamed all x that are btv in s in t. so this is ok!
          - IN CONCLUSION: we need a third UHM property: Already added!
*)



Definition R_constr (t : term) (s : term) (sigma : list (string * term)) (X : string) : prod (list (string * string)) (list (string * string)) :=
    let tvs := tv s ++ tv_keys_env sigma in
  let btvs := btv s ++ btv_env sigma in
  let tv_t := tv t in
  let used := tv_t ++ tvs ++ [X] in
  (* a little problematic, this can construct the same ones. We need to fold instead, moving along the fresh vars in new fresh var generation*)
  (* we should nto add duplicates!*)
  let R2 := map (fun x => (x, x)) (list_diff string_dec (ftv t) btvs) in
  let R1 := freshen2 (used ++ map fst R2 ++ map snd R2) btvs in (* Mar 18: Added map fst R2 ++ map snd R2 for easier proving*)
  (* we rename those ftvs in t that are binders in s and sigma*)
  (R1, R2). 

Inductive UniqueRhs : list (string * string) -> Prop :=
| uniqueRhs_nil : UniqueRhs nil
| uniqueRhs_cons : forall x y l,
    ~ In y (map snd l) ->
    UniqueRhs l ->
    UniqueRhs ((x, y) :: l).

Lemma freshen2__uniqueRHs {used l} :
  UniqueRhs (freshen2 used l).
Proof.
  generalize dependent used.
  induction l; intros.
  - unfold freshen2. simpl. constructor.
  - unfold freshen2.
    simpl.
    constructor.
    + remember (fold_right _ _ _) as fld.
      apply fresh_to_GU__fresh_over_snd_binders.
    + unfold freshen2 in IHl.
      assert (Hchange: ((used ++ [a]) ++ l) = (used ++ a :: l)).
      { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
      rewrite <- Hchange.
      eapply IHl.
Qed.

Lemma lookup_Some__uniqueRhs__lookup_r {l x y} :
  lookup x l = Some y ->
  UniqueRhs l ->
  lookup_r y l = Some x.
Proof.
  intros Hlu Hunique.
  induction l.
  - inversion Hlu.
  - destruct a as [a1 a2].
    destr_eqb_eq a1 x.
    + simpl in Hlu.
      rewrite String.eqb_refl in Hlu.
      inversion Hlu; subst.
      simpl.
      rewrite String.eqb_refl.
      f_equal.
    + simpl in Hlu.
      rewrite <- String.eqb_neq in H.
      rewrite H in Hlu.
      inversion Hunique; subst.
      specialize (IHl Hlu H4).
      simpl.
      destr_eqb_eq a2 y.
      * exfalso.
        apply lookup_r_then_in_map_snd in IHl.
        contradiction.
      * auto.
Qed.

Lemma freshen2_lookup__lookup_r {used l x x'} :
  lookup x (freshen2 used l) = Some x' ->
  lookup_r x' (freshen2 used l) = Some x.
Proof.
  intros Hlookup.
  eapply lookup_Some__uniqueRhs__lookup_r; auto.
  apply freshen2__uniqueRHs.
Qed.

Search "alphavar".

Lemma freshen2_alpha_lookup {used l x x'} :
  lookup x (freshen2 used l) = Some x' ->
  AlphaVar (freshen2 used l) x x'.
Proof.
  intros Hlookup.
  remember (freshen2_lookup__lookup_r Hlookup) as Hlookup'; clear HeqHlookup'.
  apply lookup_some_then_alphavar; eauto.
Qed.

(* By rhs of freshen2 is unique ( each rhs element gets uniqued/freshened)*)
Lemma freshen2_alpha {used l x} :
  In x l ->
  {x' & AlphaVar (freshen2 used l) x x' * (x <> x')}%type.
Proof.
  intros Hin.
  assert (Hex: {x' & lookup x (freshen2 used l) = Some x'}).
  {
    eapply in_generator_then_in_freshen2 in Hin.
    apply in_map_iff_sigma in Hin.
    destruct Hin as [x' H_inmap].

    apply in_map__exists_lookup in H_inmap.
    eauto.
  }
  destruct Hex as [x' Hax].
  exists x'.
  split.
  - apply freshen2_alpha_lookup; auto.
  - assert (In x' (map snd (freshen2 used l))).
    { apply lookup_some_then_in_values in Hax. auto. }
    eapply freshen2__fresh_generator in H.
    intros Hcontra.
    subst.
    contradiction.
Qed.

Lemma R_constr_R2_IdCtx {t s sigma X R1 R2} :
  (R1, R2) = R_constr t s sigma X ->
  IdCtx R2.
Proof.
  intros Hconstr.
  unfold R_constr in Hconstr.
  inversion Hconstr; clear Hconstr H0 H1.
  apply map_creates_IdCtx.
Qed.


Lemma R_constr__uhm3 { R1 R2 t s sigma X} :
  (R1, R2) = R_constr t s sigma X ->
  forall x, In x (btv s ++ btv_env sigma) -> {X' & AlphaVar (R1 ++ R2) x X' * (x <> X') * (~ In x (map snd (R1 ++ R2)))}%type.
Proof.
  intros Hconstr x Hin_btvs.
  assert (Hconstr' : ((R1, R2) = R_constr t s sigma X)) by auto.
  unfold R_constr in Hconstr.
  remember (freshen2 _ _) as frs.
  remember  ((tv t ++ (tv s ++ tv_keys_env sigma) ++ [X]) ++
      map fst
        (map (fun x0 : string => (x0, x0))
        (list_diff string_dec (ftv t)
        (btv s ++ btv_env sigma))) ++
      map snd
        (map (fun x0 : string => (x0, x0))
        (list_diff string_dec (ftv t)
        (btv s ++ btv_env sigma)))) as used.
  assert (H: x
      ∈ (btv s ++
      btv_env sigma)) by auto.
  eapply freshen2_alpha in H as [x' [Ha_x' Hneq]].
  rewrite <- Heqfrs in Ha_x'.
  inversion Hconstr.
  rewrite <- H0 in *.
  rewrite <- H1 in *.
  exists x'.
  split; [split|]; eauto.
  - eapply alphavar_extend_ids_right; eauto.
    eapply R_constr_R2_IdCtx; eauto.
  - rewrite map_app.
    apply not_in_app.
    split.
    + intros Hcontra.
      rewrite Heqfrs in Hcontra.
      apply freshen2__fresh_map_snd in Hcontra.
      rewrite Heqused in Hcontra.
      apply in_app_iff in Hin_btvs.
      destruct Hin_btvs as [Hin_btvs | Hin_btv_sigma].
      * apply not_in_app in Hcontra as [Hcontra _].
        apply not_in_app in Hcontra as [_ Hcontra].
        apply not_in_app in Hcontra as [Hcontra _].
        apply not_in_app in Hcontra as [Hcontra _].
        apply extend_btv_to_tv in Hin_btvs.
        contradiction.
      * apply not_in_app in Hcontra as [Hcontra _].
        apply not_in_app in Hcontra as [_ Hcontra].
        apply not_in_app in Hcontra as [Hcontra _].
        apply not_in_app in Hcontra as [_ Hcontra].
        apply btv_env_extends_to_tv_env in Hin_btv_sigma.
        contradiction.
    + intros Hcontra.
      rewrite H1 in Hcontra.
      apply in_map_iff in Hcontra.
      destruct Hcontra as [x'' [Hx''_eq H_in_map]].
      destruct x'' as [x''0 x''1].
      simpl in Hx''_eq.
      rewrite <- Hx''_eq in *.


      assert (x''0 = x''1).
      { apply in_id_map_then_id in H_in_map; auto. }
      rewrite <- H in *.
      apply in_id_map_then_in_generator in H_in_map.
      eapply list_diff_not with (l1 := (ftv t)) in Hin_btvs.
      contradiction.
Qed.

Lemma R_constr_freshen_helper {t s sigma X R1 R2} :
  (R1, R2) = R_constr t s sigma X ->
  forall x, In x (map fst R1) -> sum (In x (btv s)) (In x (btv_env sigma)).
Proof.
  intros Hconstr x Hin.
  unfold R_constr in Hconstr.
  inversion Hconstr. clear H1 Hconstr.
  remember ((tv t ++
        tv s ++ tv_keys_env sigma) ++
        map fst
          (map
          (fun x0 : string =>
        (x0, x0))
          (list_diff string_dec
          (ftv t)
          (btv s ++ btv_env sigma))) ++
        map snd
          (map
          (fun x0 : string =>
        (x0, x0))
          (list_diff string_dec
          (ftv t)
          (btv s ++ btv_env sigma)))) as used.
  clear Heqused.
  subst.
  apply in_freshen2_then_in_generator in Hin.
  apply in_prop_to_set in Hin.
  apply in_app_or_set in Hin as [Hin | Hin].  
  + left.
    apply in_set_to_prop. auto.
  + right.
    apply in_set_to_prop. auto.
Qed.

Lemma R_constr_freshen_fresh_over_sigma {t s sigma X R1 R2} :
  (R1, R2) = R_constr t s sigma X ->
  forall x, In x (map snd R1) -> (~ In x (ftv_keys_env sigma)).
Proof.
  intros Hconstr x Hin.
  unfold R_constr in Hconstr.
  inversion Hconstr. clear H1 Hconstr.
  subst.
  apply freshen2__fresh_map_snd in Hin.
  intros Hcontra.
  apply ftv_keys_env_extends_to_tv_env in Hcontra.
  apply not_in_app in Hin as [Hin _].
  apply not_in_app in Hin as [_ Hin].
  apply not_in_app in Hin as [Hin _].
  apply not_in_app in Hin as [_ Hin].
  contradiction.
Qed.



Definition t_constr (t : term) (s : term) (sigma : list (string * term)) (X : string) : prod term (list (string * string)) :=
  let tvs := tv s ++ tv_keys_env sigma in
  let tv_t := tv t in
  let used := tv_t ++ tvs ++ [X] in
  let (R1, R2) := R_constr t s sigma X in
  (snd (to_GU_ used (R1 ++ R2) t), R1 ++ R2). 

Lemma t_constr__GU {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  GU t'.
Proof.
  intros.
  unfold t_constr in H.
  remember (R_constr t s sigma X) as p.
  destruct p as [R1 R2].
  inversion H.
  eapply to_GU__GU_; eauto.
  - intros.
    unfold R_constr in Heqp.
    destruct (in_dec string_dec x (btv s ++ btv_env sigma)).
    + inversion Heqp.
      rewrite <- H4.
      rewrite <- H5.

      (* eapply map_pair_helper in i. *)
      eapply in_generator_then_in_freshen2 in i.
      rewrite map_app. apply in_app_iff. left. rewrite H4. auto.
      unfold freshen2 in Heqp.
      eauto.


      
    + inversion Heqp.
      rewrite map_app. apply in_app_iff. right.
      apply in_map_iff.
      exists (x, x); intuition.
      apply in_generator_then_in_id_map.
      apply list_diff_helper; eauto.
  - intros.
    apply in_app_iff.
    left.
    auto.
Qed.

(* R is constructed so that all x in ftv t are either in R1 or R2*)
Lemma R_constr_contains_all_t_ftvs {t s sigma X R1 R2} :
  (R1, R2) = R_constr t s sigma X ->
  forall x, In x (ftv t) -> In x (map fst (R1 ++ R2)).
Proof.
  intros Hconstr.
  intros x Hftv.
  unfold R_constr in Hconstr.
  remember (((tv t ++ tv s ++ tv_keys_env sigma) ++
  map fst
    (map (fun x0 : string => (x0, x0))
    (list_diff string_dec (ftv t)
    (btv s ++ btv_env sigma))) ++
  map snd
    (map (fun x0 : string => (x0, x0))
  (list_diff string_dec (ftv t)
  (btv s ++ btv_env sigma))))) as used. clear Heqused.
  destruct (in_dec string_dec x (btv s ++ btv_env sigma)).
  + rewrite map_app.
    apply in_app_iff. left.
    eapply in_generator_then_in_freshen2 in i.
    inversion Hconstr.
    subst.
    eauto.
  + rewrite map_app.
    apply in_app_iff. right.
    inversion Hconstr.
    clear H0 Hconstr.
    subst.
    assert (In x  (list_diff string_dec (ftv t) (btv s ++ btv_env sigma))).
    {
      apply list_diff_helper.
      auto. auto.
    }
    apply in_map_iff.
    exists ((x, x)); split; auto.
    apply in_generator_then_in_id_map; auto.
Qed.

Lemma t_constr__a_t {t t' R s sigma X }:
  (t', R) = t_constr t s sigma X ->
  Alpha R t t'.
Proof.
  intros.
  unfold t_constr in H.
  remember (tv t ++ tv s ++ tv_keys_env sigma) as used.
  remember (R_constr t s sigma X) as R'.
  destruct R' as [R1 R2].
  inv H.
  apply to_GU__alpha_'.
  - remember (map (fun x : string => (x, x))
      (list_diff string_dec (ftv t)
      (btv s ++ btv_env sigma))) as Rid.
    unfold R_constr in HeqR'.
    inv HeqR'.
    intros.
    eapply KindOfUniqueRhsFreshMultiple; auto.
    eapply IdCtx__KindOfUniqueRhs.
    apply map_creates_IdCtx.
  - intros.
    remember HeqR' as HeqR''.
    unfold R_constr in HeqR'.
    eapply @R_constr_contains_all_t_ftvs with (R1 := R1) (R2 := R2) in H.
    apply lookup_none_then_no_key in H0.
    contradiction H0; eauto. eauto.
  - intros.
    subst.
    intuition.
Qed.



Lemma R_constr__a_s {R1 R2 t s sigma X} :
  GU s ->
  Uhm sigma s ->
  (R1, R2) = R_constr t s sigma X ->
  Alpha (R1 ++ R2) s s.
Proof.
  intros HGU H H0.
  apply alpha_vacuous_R.
  - intros.
    unfold Uhm in H.
    destruct H as [ uhm1 _].
    intros Hcontra.
    remember Hcontra as Hcontra2; clear HeqHcontra2.
    apply extend_ftv_to_tv in Hcontra.
    apply uhm1 in Hcontra; auto.
    unfold R_constr in H0.
    inv H0.
    apply in_freshen2_then_in_generator in H1.
    apply in_app_or in H1.
    destruct H1.
    * apply gu_ftv_then_no_btv in H. contradiction. auto. auto.
    * auto. 
   - (* x' is specifically in R1, which only contains fresh vars (over s)*)
       unfold R_constr in H0.
      inv H0. intros.
      apply freshen2__fresh_map_snd in H0.
      rename H0 into H1.
      apply not_in_app in H1 as [H1 _].
      apply not_in_app in H1 as [_ H1].
      apply not_in_app in H1 as [H1 _].
      apply not_in_app in H1 as [H1 _].
      intros Hcontra.
      apply extend_ftv_to_tv in Hcontra.
      contradiction.
  - apply alpha_extend_ids.
    + unfold R_constr in H0.
      inv H0.
      apply map_creates_IdCtx.
    + eapply alpha_refl. constructor.
Qed.

(* here we probably need Uhm requirements*)
Lemma t_constr__a_s {t t' R s sigma X} :
  GU s ->
  Uhm sigma s ->
  (t', R) = t_constr t s sigma X ->
  Alpha R s s.
Proof.
  intros.
  unfold t_constr in H1.
  remember (R_constr t s sigma X) as p.
  destruct p as [R1 R2].
  inversion H1.
  eapply R_constr__a_s; eauto.
Qed.

Lemma R_constr__a_sigma {R1 R2 t s sigma X} :
  Uhm sigma s ->
  NC s sigma ->
  (R1, R2) = R_constr t s sigma X ->
  αCtxSub (R1 ++ R2) sigma sigma.
Proof.
  intros HUhm Hnc HReq.
  destruct HUhm as [ Uhm1 Uhm2].
  apply αctx_sub_extend_ids_right.
  + eapply R_constr_R2_IdCtx; eauto.
  + apply αctx_vacuous_R.
    * intros.
      apply R_constr_freshen_helper with (x := x) in HReq; auto.
      destruct HReq as [H01 | H02]; auto. 
      eapply nc_ftv_env in Hnc; eauto.
    * intros.
      apply R_constr_freshen_fresh_over_sigma with (x := x') in HReq; auto.
    * apply alpha_ctx_ren_nil.
Qed.

Lemma t_constr__a_sigma {t t' R s sigma X} :
  Uhm sigma s ->
  NC s sigma ->
  (t', R) = t_constr t s sigma X ->
  αCtxSub R sigma sigma.
Proof.
  unfold t_constr.
  destruct (R_constr t s sigma X) as [R1 R2] eqn:Rconstr.
  intros Huhm Hnc Hconstr.
  inversion Hconstr. clear H0. clear Hconstr.
  eapply R_constr__a_sigma; eauto.
Qed.

(* TODO: very similar to the ones about ftv s and ftv sigma *)
Lemma t_constr__fresh_X_btv_t' {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  ~ In X (btv t').
Proof.
  intros Hconstr Hbtv_t'.
  unfold t_constr in Hconstr.
  inversion Hconstr.
  clear H1 Hconstr.
  remember ((tv t ++ (tv s ++ tv_keys_env sigma) ++ [X])) as used.
  remember ((freshen2 _ _) ++ _) as binders; clear Heqbinders.
  remember ((to_GU_ used binders t)) as p.
  destruct p as [[used' binders'] t''].
  subst.
  eapply no_binder_used with (used := tv t ++ tv s ++ tv_keys_env sigma ++ [X]) in Hbtv_t'; eauto.
  - repeat apply not_in_app in Hbtv_t' as [_ Hbtv_t'].
    contradiction Hbtv_t'.
    apply in_eq.
  - repeat rewrite app_assoc in Heqp.
    repeat rewrite app_assoc.
    eauto.
Qed.

Lemma t_constr__uhm1 {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv t') -> ~ In x (tv s).
Proof.
  intros Hconstr x Hbtv_t'.
  unfold t_constr in Hconstr.
  inversion Hconstr.
  clear H1 Hconstr.
  remember (tv t ++ (tv s ++ tv_keys_env sigma) ++ [X]) as used.
  remember ((freshen2 _ _) ++ _) as binders; clear Heqbinders.
  remember ((to_GU_ used binders t)) as p.
  destruct p as [[used' binders'] t''].
  subst.
  eapply no_binder_used with (used := tv t ++ tv s ++ tv_keys_env sigma ++ [X]) in Hbtv_t'; eauto.
  apply not_in_app in Hbtv_t' as [_ Hbtv_t'].
  apply not_in_app in Hbtv_t' as [Hbtv_t' _].
  auto; eauto. subst. eauto. simpl. eauto.
  repeat rewrite app_assoc in Heqp.
  repeat rewrite app_assoc.
  eauto.
Qed.

(* Very similar to above*)
Lemma t_constr__new_btv_not_sigma {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv t') -> ~ In x (ftv_keys_env sigma).
Proof.
  intros Hconstr x Hbtv_t'.
  unfold t_constr in Hconstr.
  inversion Hconstr.
  clear H1 Hconstr.
  remember (tv t ++ (tv s ++ tv_keys_env sigma) ++ [X]) as used.
  remember ((freshen2 _ _) ++ _) as binders; clear Heqbinders.
  remember ((to_GU_ used binders t)) as p.
  destruct p as [[used' binders'] t''].
  subst.
  eapply no_binder_used with (used := tv t ++ tv s ++ tv_keys_env sigma ++ [X]) in Hbtv_t'; eauto.
  apply not_in_app in Hbtv_t' as [_ Hbtv_t'].
  apply not_in_app in Hbtv_t' as [_ Hbtv_t'].
  apply not_in_app in Hbtv_t' as [Hbtv_t' _].
  auto.
  intros Hcontra.
  apply ftv_keys_env_extends_to_tv_env in Hcontra.
  contradiction.
  repeat rewrite app_assoc.
  repeat rewrite app_assoc in Heqp.
  simpl. eauto.
Qed.

(* fuck this shit... *)
Lemma ftv_helper_constr {t t' R  X X'} :
  R ⊢ t ~ t' ->
  ~ In X (map snd R) ->
  X <> X' ->
  AlphaVar R X X' ->
  ~ In X (btv t') ->
  ~ In X' (btv t') ->
  ~ In X (ftv t').
Proof.
  intros.
  assert (Hbinderchange: {t'' & R ⊢ t'' ~ t' * ~ In X (btv t'')}%type).
  {
    exists (to_GU'' X t).
    split.
    - eapply @alpha_trans with (t := t) (ren := ctx_id_left R) (ren' := R); eauto with α_eq_db.
      + apply id_left_trans.
      + apply alpha_extend_ids. apply ctx_id_left_is_id. eapply @alpha_sym. constructor. apply to_GU''__alpha.
    - apply to_GU''__btv.
  }
  destruct Hbinderchange as [t'' [Ha_t'' Hbtv_t''] ].
  clear H.
  (* By X not in rhs R, we should then have X in ftv t, but that doesnt work, because we have (X, X')
    I'm sure we must already have lemmas for this kind of contraddiction.
  *)
  generalize dependent t''.
  generalize dependent R.
  induction t'; intros.
  - inversion Ha_t''; subst.
    
    intros Hcontra.
    inversion Hcontra; eauto. subst. clear Hcontra.
    destr_eqb_eq x X.
    + assert (X = X').
      eapply alphavar_unique_right. eauto. eauto. contradiction.
    + assert (In (x, X) R).
      {
        clear H2.
        induction R.
        - inversion Ha_t''; subst. inversion H7; subst. contradiction.
        - simpl in H0.
          simpl.
          right.
          assert (a <> (x, X)).
          {
            intros Hcontra.
            assert (snd a = X).
            {
              destruct a.
              inversion Hcontra. subst. reflexivity.
            }
            subst.
            intuition.
          }
          eapply IHR.
          + intuition.
          + inversion H7; subst.
            * contradiction.
            * assumption.
          + inversion H7; subst; intuition.
      }
      contradiction H0.
      apply in_map_iff.
      exists (x, X). split; auto.
  - destr_eqb_eq X s.
    + intros Hcontra. simpl in Hcontra. apply in_remove in Hcontra. destruct Hcontra as [_ snots]. contradiction.
    + 
      assert (~ In X (ftv t')).
      {
        inversion Ha_t''; subst.
        eapply IHt' with (t'' := s1) (R := ((x, s)::R)); eauto.
        - eapply not_btv_dc_lam; eauto. 
        - eapply not_btv_dc_lam; eauto.
        - simpl.
          intuition.
        - constructor; auto.
          + intros Hcontra.
            subst.
            simpl in Hbtv_t''. intuition.
          + intros Hcontra.
            subst.
            simpl in H4. intuition.
        - eapply not_btv_dc_lam; eauto.
      }
      intros Hcontra.
      apply ftv_lam_helper in Hcontra.
      contradiction.
  - inversion Ha_t''; subst.
    unfold ftv. fold ftv.
    apply not_in_app.
    split; eauto.
    + eapply IHt'1; eauto; eapply not_btv_dc_appl; eauto.
    + eapply IHt'2; eauto; eapply not_btv_dc_appr; eauto.
  - intros Hcontra.
    inversion Hcontra.
Qed.


Lemma R_constr_lookup_alpha {R1 R2 t s sigma X} :
  (R1, R2) = R_constr t s sigma X ->
  forall x X', lookup x (R1 ++ R2) = Some X' -> AlphaVar (R1 ++ R2) x X'.
Proof.
  intros Hconstr.
  intros x X' Hlookup.
  assert (Hconstr' : (R1, R2) = R_constr t s sigma X) by auto.
  unfold R_constr in Hconstr.
  remember((tv t ++ tv s ++ tv_keys_env sigma) ++
  map fst
    (map (fun x0 : string => (x0, x0))
    (list_diff string_dec (ftv t)
    (btv s ++ btv_env sigma))) ++
  map snd
    (map (fun x0 : string => (x0, x0))
    (list_diff string_dec (ftv t)
    (btv s ++ btv_env sigma)))) as used.
  apply lookup_app_or_extended in Hlookup as [HinR1 | [ HnotInR1 HinR2] ].
  + assert (AlphaVar R1 x X').
    {
      inversion Hconstr. clear H1 Hconstr. subst.
      apply freshen2_alpha_lookup; auto.
    } 
    eapply alphavar_extend_ids_right in H; eauto.
    eapply R_constr_R2_IdCtx in Hconstr'; eauto.
  + remember Hconstr' as Hconstr''. clear HeqHconstr''.
    eapply R_constr_R2_IdCtx in Hconstr'; eauto.
    remember HinR2 as HinR2'. clear HeqHinR2'.
    apply lookup_idctx_refl in HinR2; eauto; subst.
    assert (HX'inftvt: In X' (ftv t)).
    {
      inversion Hconstr.
      clear H0. clear Hconstr Hconstr''.
      apply lookup_then_in_map_fst in HinR2'.
      subst.
      apply in_map_iff in HinR2'.
      destruct HinR2' as [x'' [Heq Hin_map]].
      destruct x'' as [x''0 x''1].
      simpl in Heq.
      subst.
      assert (X' = x''1).
      { apply in_id_map_then_id in Hin_map; subst; auto. }
      subst.
      apply in_id_map_then_in_generator in Hin_map.
      apply list_diff_in_first in Hin_map. auto.
    }
    assert (lookup_r X' R1 = None).
    {
      remember((tv t ++ tv s ++ tv_keys_env sigma) ++
  map fst
    (map (fun x0 : string => (x0, x0))
    (list_diff string_dec (ftv t)
    (btv s ++ btv_env sigma))) ++
  map snd
    (map (fun x0 : string => (x0, x0))
    (list_diff string_dec (ftv t)
    (btv s ++ btv_env sigma)))) as used.
      assert (~ In X' (map snd R1)).
      {
        intros Hcontra.
        inversion Hconstr.
        rewrite H0 in Hcontra.
        eapply freshen2__fresh_map_snd in Hcontra; auto.
        subst.
        apply not_in_app in Hcontra as [Hcontra _].
        apply not_in_app in Hcontra as [Hcontra _].
        apply extend_ftv_to_tv in HX'inftvt.
        contradiction.
      }
      apply not_ex__lookup_r_none. auto.
    }
    destruct (@lookup_none_extend_helper _ R2 _ HnotInR1 H) as [Hlookup Hlookup_r].
    apply lookup_some_then_alphavar; auto.
    * rewrite Hlookup. auto.
    * rewrite Hlookup_r. auto.
      apply lookup_id_then_lookup_r; auto.
Qed.

Lemma t_constr_btv_s_not_ftv_t' {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv s ++ btv_env sigma) -> ~ In x (ftv t').
Proof.
  intros.

  assert ({X' & (AlphaVar R x X') * (x <> X') * (~ In x (map snd R)) }%type) as [X' [ [HAx Hneq] HnotsndR]].
  {
    unfold t_constr in H.
    remember (R_constr t s sigma X) as p.
    destruct p as [R1 R2].
    inversion H.
    eapply R_constr__uhm3; eauto.
  }
  
  eapply ftv_helper_constr.
  - eapply t_constr__a_t; eauto.
  - auto.
  - eauto.
  - eauto.
  - 
    intros Hcontra. simpl in H.
    unfold t_constr in H.
    remember (R_constr t s sigma X) as p.
    destruct p as [R1 R2].
    inversion H.
    remember ((to_GU_ (tv t ++ (tv s ++ tv_keys_env sigma) ++ [X])
  (R1 ++ R2) t)) as q.
    destruct q as [ [used' binders'] t''].
    simpl in H2. rewrite <- H2 in *.
    eapply no_btv_in_binders_fst with (used := (tv t ++ (tv s ++ tv_keys_env sigma) ++ [X]))
      (binders' := binders')
      (used' := used')

      (binders := R1 ++ R2) in Hcontra; eauto.
    + rewrite <- H3 in Hcontra.
      subst.
      apply alphavar_lookup_helper in HAx.
      destruct HAx as [HAx1 | HAx2].
      * destruct HAx1 as [HAx1].
        apply lookup_then_in_map_fst in HAx1. contradiction.
      * destruct HAx2 as [[_ _] HAx2].
        contradiction.

  - intros Hcontra. simpl in H.
    unfold t_constr in H.
    remember (R_constr t s sigma X) as p.
    destruct p as [R1 R2].
    inversion H.
    remember ((to_GU_ (tv t ++ (tv s ++ tv_keys_env sigma) ++ [X])
  (R1 ++ R2) t)) as q.
    destruct q as [ [used' binders'] t''].
    simpl in H2. rewrite <- H2 in *.
    eapply no_btv_in_binders with (binders := R1 ++ R2) in Hcontra; eauto.
    rewrite <- H3 in Hcontra.
    subst.
    apply alphavar_lookup_helper in HAx.
    destruct HAx as [HAx1 | HAx2].
    + 
      destruct HAx1 as [HAx1].
      apply lookup_r_then_in_map_snd in e. contradiction.
    + destruct HAx2 as [[_ _] HAx2].
      contradiction.
Qed.


Lemma t_constr__nc_s {t t' R s sigma X} :
  ~ In X (btv s) ->  (* We dont have control over s or X in construction*)
  NC s sigma ->
  (t', R) = t_constr t s sigma X ->
  NC s ((X, t')::sigma).
Proof.
  intros.
  constructor; auto.
  intros.
  split.
  - intros contra.
    inversion H0.
    subst.
    apply H.
    assumption.
    subst. contradiction.
  - eapply t_constr_btv_s_not_ftv_t'. eauto. auto.
    apply in_app_iff. left. auto.
Qed.

Lemma t_constr__nc_subs {t t' R s sigma X} :
  ~ In X (btv s) -> (* We dont have control over s or X in construction*)
  ~ In X (btv_env sigma) -> (* we do not have control over sigma*)
  (t', R) = t_constr t s sigma X ->
  NC (psubs sigma s) ((X, t')::nil).
Proof.
  intros.
  constructor.
  - constructor.
  - intros.
    split.
    + intros Hcontra.
      subst.
      apply in_btv_psubs_then_in_constituents in H2.
      destruct H2 as [Hin_s | [t0 [Ht0_sigma Hin_t0]]].
      * contradiction.
      * contradiction H0.
        {
        clear H1. clear H0. clear H.
        induction sigma.
        - inversion Ht0_sigma.
        - destruct a as [ax a_t].
          simpl.
          rewrite map_cons in Ht0_sigma.
          destruct Ht0_sigma.
          + simpl in H. subst.
            apply in_app_iff.
            left. auto.
          + apply in_app_iff.
            right.
            apply IHsigma.
            auto.
       }
    + apply in_btv_psubs_then_in_constituents in H2.
      destruct H2 as [Hin_s | [t0 [Ht0_sigma Hin_t0]]].
      * apply t_constr_btv_s_not_ftv_t' with (x := y) in H1. auto. auto.
        apply in_app_iff. left. auto.
      * apply (btv_env_helper _ _ _ Hin_t0) in Ht0_sigma.
        apply t_constr_btv_s_not_ftv_t' with (x := y) in H1. auto. auto.
        apply in_app_iff. right. auto.
Qed.

Opaque t_constr.


(* defined for arbitrary substitution, while below we only need it for identity substituiosn
  maybe we can then reuse this in other parts of the code. 
  
  this is simply to_GU', but with more subsitutions.
  *)

Definition s_constr (s : term) (sigma : list (string * term)) : term := 
  (* By adding tvs in X and T, no binders in the resulting term can be equal to tvs in X and T.
    We do tv, because mostly tv is easier to reason about than ftv*)
  let tvs := tv_keys_env sigma ++ tv s in
  (* again we need to remove duplicates *)
  snd (to_GU_ tvs (map (fun x => (x, x)) tvs) s).


(* Only need to rename binders*)
Lemma s_constr__a_s {s s' sigma} :
  s' = s_constr s sigma ->
  Alpha [] s s'.
Proof.
  intros Heqs'.
  unfold s_constr in Heqs'.
  remember (map (fun x => (x, x)) (_)) as R.
  rewrite Heqs'.
  assert (R ⊢ s ~ s').
  {
    rewrite Heqs'.
    eapply to_GU__alpha_'.
    - intros.
      eapply lookup_some_IdCtx_then_alphavar; eauto.
      rewrite HeqR.
      apply map_creates_IdCtx.
    - intros.
      apply id_ctx_alphavar_refl; auto.
      subst. apply map_creates_IdCtx.
    - intros.
      intuition.
  }
  eapply alpha_weaken_ids with (idCtx := R).
  - subst.
    clear H.
    induction (tv_keys_env sigma ++ tv s); simpl; constructor; auto.
  - subst. auto.
Qed.

Lemma s_constr__gu {s s' sigma} :
  s' = s_constr s sigma ->
  GU s'.
Proof.
  intros Heqs'.
  unfold s_constr in Heqs'.
  subst.
  eapply to_GU__GU_; auto.
  - intros.
    assert (In x (tv_keys_env sigma ++ tv s)).
    {
      apply extend_ftv_to_tv in H.
      auto.
      intuition.
    }
    apply in_map_iff.
    exists (x, x); intuition.
    apply id_map_helper. auto.
  - intros. (* x in tv s, then also x in supserset of tv s*)
    intuition.
Qed.

Lemma s_constr__nc_s {s s' sigma} :
  s' = s_constr s sigma ->
  NC s' sigma.
Proof.
  intros Heqs'; subst.
  unfold s_constr.
  remember (to_GU_ (_) (map (fun x => (x, x)) (_)) s) as p.
  destruct p as [ [used' binders'] s'2].
  subst.
  apply nc_helper.
  intros.
 
  apply no_binder_used with (x := x) in Heqp; auto.
  intros Hcontra. apply extend_ftv_keys_env_to_tv in Hcontra.
  apply not_in_app in Heqp.
  destruct Heqp as [Heqp _].
  contradiction.
Qed.


Opaque to_GU'.
Opaque to_GU''.

Lemma alpha_extend_fresh_tv {x x' ren t t'}:
  ~ In x (tv t) ->
  ~ In x' (tv t') ->
  Alpha ren t t' ->  

  Alpha ((x, x')::ren) t t'.
Proof.
  intros.
  induction H1.
  - constructor.
    constructor.
    + simpl in H. auto.
    + simpl in H0. auto.
    + auto.
  - constructor.
    eapply alpha_swap with (ren := ((x, x')::(x0, y)::sigma)).
    + constructor.
      * simpl in H. auto.
      * simpl in H0. auto.
      * apply legalRenSwap_id.
    + apply IHAlpha.
      apply not_tv_dc_lam in H. auto.
      apply not_tv_dc_lam in H0. auto.
  - constructor.
    + apply IHAlpha1; auto. 
      apply not_tv_dc_appl in H. auto.
      apply not_tv_dc_appl in H0. auto.
    + apply IHAlpha2; auto.
      apply not_tv_dc_appr in H. auto.
      apply not_tv_dc_appr in H0. auto.
  - constructor.
Qed.

  (* 

It feels weird to have these ones here, but they use constructions, so they have to!

  Idea: move to some GU term that has no problematic bniders
  Alpha ren (to_GU_ x [] t) (to_GU_ x [] t')  
  ->  Alpha ((x, x')::ren) (to_GU_ x t) (to_GU_ x t')
  
  Idea works perfectly! Thanks brain :).
  *)
Lemma alpha_extend_fresh {x x' ren t t'}:
  ~ In x (ftv t) ->
  ~ In x' (ftv t') ->
  Alpha ren t t' ->  

  Alpha ((x, x')::ren) t t'.
Proof.
  intros H_nxt H_nx't' Ha_t.
  remember (to_GU'' x t) as tgu.
  remember (to_GU'' x' t') as t'gu.
  assert (ren ⊢ tgu ~ t'gu) as Ht.
  {
    eapply @alpha_trans with (t := t) (ren := ctx_id_left ren); eauto.
    eapply id_left_trans.
    eapply alpha_extend_ids.
    apply ctx_id_left_is_id.
    subst.
    apply @alpha_sym with (ren := nil); eauto.
    constructor.
    eapply to_GU''__alpha.

    eapply @alpha_trans with (t := t') (ren' := ctx_id_right ren); eauto.
    eapply id_right_trans. eapply alpha_extend_ids. apply ctx_id_right_is_id.
    subst.
    eapply to_GU''__alpha.
  }
  assert (~ In x (tv tgu)).
  {
    apply not_ftv_btv_then_not_tv; auto.
    - subst.
      eapply alpha_preserves_no_ftv.
      exact H_nxt.
      eapply to_GU''__alpha.
      constructor.
    - subst.
      apply to_GU''__btv.
  }
  assert (~ In x' (tv t'gu)).
  {
    apply not_ftv_btv_then_not_tv; auto.
    - subst.
      eapply alpha_preserves_no_ftv.
      exact H_nx't'.
      eapply to_GU''__alpha.
      constructor.
    - subst.
      apply to_GU''__btv.
  }

  assert (((x, x')::ren) ⊢ tgu ~ t'gu).
  {
    apply alpha_extend_fresh_tv; auto.

  }

  eapply @alpha_trans with (t := tgu) (ren := (ctx_id_left ((x, x')::ren))).
  eapply id_left_trans. eapply alpha_extend_ids. apply ctx_id_left_is_id.
  subst.
  eapply to_GU''__alpha.

  eapply @alpha_trans with (t := t'gu) (ren' := (ctx_id_right ((x, x')::ren))); eauto.
  eapply id_right_trans. eapply alpha_extend_ids. apply ctx_id_right_is_id.
  subst.
  eapply @alpha_sym with (ren := nil); eauto. constructor.
  eapply to_GU''__alpha.
Qed.

  (*

  We know αCtxSub ren sigma sigma'.
  g2 and g3 are both fresh over sigma and sigma', so no issue.

  But what if g2 and g3 not fresh over ren?

  well, let's look at a simpler case where sigma = [Z := t] and sigma' = [Z' := t']
  Suppose now g2 in ren. We have αCtxSub ren sigma sigma'. Since g2 not in Z or t, we cannot have that there is a (g2, B) term with B in Z or t.
  Hence it is a vacuous one, and we can remove it.
  Do this for every g2 or g3 and we are left with a ren that does not contain any g2 or g3.
  Now we can add it and it does nott break shadowing :)
*)
Lemma alpha_ctx_ren_extend_fresh_ftv sigma sigma' x x' ren:
  ~ In x (ftv_keys_env sigma) ->
  ~ In x' (ftv_keys_env sigma') ->
  αCtxSub ren sigma sigma' ->
  αCtxSub ((x, x')::ren) sigma sigma'.
Proof.
  intros H_nxσ H_nx'σ' H_α.
  induction H_α.
  - constructor.
  - constructor.
    + apply IHH_α. auto. simpl in H_nxσ. 
      * apply de_morgan2 in H_nxσ. destruct H_nxσ as [_ H_nxσ].
        apply not_in_app in H_nxσ as [_ H_nxσ]. auto.
      * apply de_morgan2 in H_nx'σ'. destruct H_nx'σ' as [_ H_nx'σ'].
        apply not_in_app in H_nx'σ' as [_ H_nx'σ']. auto.
    + constructor; auto.
      * apply de_morgan2 in H_nxσ as [H_nxσ _]; auto.
      * apply de_morgan2 in H_nx'σ' as [H_nx'σ' _]; auto.
    + apply alpha_extend_fresh; auto.
      * apply de_morgan2 in H_nxσ. destruct H_nxσ as [_ H_nxσ].
        apply not_in_app in H_nxσ as [H_nxσ _]. auto.
      * apply de_morgan2 in H_nx'σ'. destruct H_nx'σ' as [_ H_nx'σ'].
        apply not_in_app in H_nx'σ' as [H_nx'σ' _]. auto.
Qed.


(* Since we have Alpha ren s s, we know no ftv in s is in ren! (or it is identity, so we already no that we won't get breaking
  and if we do it is with variables that do not do antying to s
)*)
Lemma alpha_extend_id'' {s z ren}:
  Alpha ren s s -> Alpha ((z, z)::ren ) s s.
Proof.
  destruct (in_dec string_dec z (ftv s)).
  - intros.

    (* By contradiction: If z breaks shadowing in ren, then there is a (z, z') in there with z' <> z. 
    Then not ren ⊢ s ~ s*)
    assert (NotBreakShadowing z ren).
    {
      dependent induction H.
      - apply ftv_var in i; subst.
        induction sigma.
        + constructor.
        + destruct a0 as [a1 a2].
          inversion a; subst.
          * apply not_break_shadow_id.
          * apply not_break_shadow_cons; auto.
      - 
         assert (z <> x).
        {
          apply ftv_lam_in_no_binder in i. auto.
        }
        assert (Hs1_refl: s1 = s1) by auto.
        specialize (IHAlpha (ftv_lam_helper i) Hs1_refl).
        inversion IHAlpha; subst.
        + auto.
        + contradiction.
      - simpl in i. 
        apply in_prop_to_set in i.
        apply in_app_or_set in i.
        destruct i.
        + apply in_set_to_prop in i. apply IHAlpha1; auto.
        + apply in_set_to_prop in i. apply IHAlpha2; auto.
      - inversion i.
    }
    intros.
    eapply alpha_extend_id'; auto.
  - intros.
    apply alpha_extend_vacuous_ftv; eauto.
Qed.


Lemma Uhm_lam2 {B x A s sigma t t' R} :
  GU (@tmlam B x A s) ->
  (t', R) = t_constr t s sigma x ->

  Uhm sigma (@tmlam B x A s) -> Uhm ((x, t')::sigma) s.
Proof.
  intros HGU Htconstr HUhm.
  unfold Uhm in HUhm; destruct HUhm as [ uhm1 uhm2].
  split; intros.
  - simpl in H.
    apply in_app_iff in H as [Hinbtvt' | Hinbtvsigma].
    + eapply t_constr__uhm1 in Htconstr; eauto.
    + apply uhm1 in Hinbtvsigma. apply not_tv_dc_lam in Hinbtvsigma; auto.
  - simpl in H.
    apply in_app_iff in H as [Hinbtvt' | Hinbtvsigma].
    + 
      simpl.
      apply de_morgan2.
      split.
      * intros Hcontra; subst.
        eapply t_constr__fresh_X_btv_t'; eauto.
      * apply not_in_app; split.
        -- apply t_constr__GU in Htconstr.
           intros Hcontra.
           apply gu_ftv_then_no_btv in Hcontra; auto.
        -- eapply t_constr__new_btv_not_sigma; eauto.
    + simpl.
      apply de_morgan2.
      split.
      * intros Hcontra; subst.
        apply uhm1 in Hinbtvsigma.
        simpl in Hinbtvsigma.
        intuition.
      * apply not_in_app; split.
        -- eapply t_constr_btv_s_not_ftv_t'; eauto.
           apply in_app_iff.
           right. auto.
        -- eapply uhm2. eauto.
Qed.


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
  LegalRenSwaps ((x, y)::Rt) Rs -> 
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
      apply lrss_sym in X.
      apply (alpha_swaps X) in H.
      inversion H; subst.
      inversion H8; subst.
      contradiction H3; auto.
      contradiction H9; auto.
    + exfalso.
      apply lrss_sym in X.
      apply (alpha_swaps X) in H.
      inversion H; subst.
      inversion H8; subst.
      contradiction H3; auto.
      contradiction H12; auto.
    + eapply @alpha_swaps with (ren' := ((x, y)::Rt)) in H.
      inversion H; subst.
      inversion H9; subst; try contradiction.
      apply alpha_var.
      assumption.
      apply lrss_sym. auto.
  - constructor.
    eapply IHs; eauto...
    + eapply alpha_extend_vacuous_ftv.
      * apply nc_ftv_env with (x := s) in H1.
        simpl in H1.
        intuition. apply btv_lam.
      * apply nc_ftv_env with (x := y0) in H2.
        simpl in H2.
        intuition. apply btv_lam.
      * assumption.
    + eapply @lrss_trans with (ren2 := ((s, y0)::(x, y)::Rt)).
      * eapply starSE.
        -- apply starR.
        -- 
          ++ constructor. 
            ** apply nc_ftv_env with (x := s) in H1.
              simpl in H1. intuition. apply btv_lam.
            ** apply nc_ftv_env with (x := y0) in H2.
              simpl in H2. intuition. apply btv_lam.
            ** apply legalRenSwap_id.
      * apply lrss_cons. auto.
  - constructor; eauto with gu_nc_db.
  - constructor.
Qed.