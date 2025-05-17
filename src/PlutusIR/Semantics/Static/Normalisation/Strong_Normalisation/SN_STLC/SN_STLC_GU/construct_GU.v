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

From PlutusCert Require Import step_naive psubs util STLC SN_STLC_GU.GU_NC_BU alpha.alpha variables util alpha_ctx_sub alpha_freshness.


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
  destruct (in_dec_f string_dec x l) eqn:BU.
  - eapply in_dec_f_sound; eauto.
  - exfalso.
    induction l.
    + inversion H.
    + inversion H; subst.
      simpl in BU.
      destruct (string_dec x x).
      * discriminate BU.
      * contradiction.
      * assert (in_dec_f string_dec x l = false).
        {
          simpl in BU.
          destruct (string_dec x a).
          - discriminate BU.
          - auto.
        }
        eapply IHl; auto.
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
  | @tmabs B x A s => (* we can freshen regardless *)
                    let x' := fresh_to_GU_ used binders x in
                    let (acc, term_body) := to_GU_ used ((x, x')::binders) s in
                    ((fst acc ++ (x::x'::nil)), binders, @tmabs B x' A term_body)
  | @tmbin B s t => let (acc_s, s') := to_GU_ used binders s in
                 let (acc_t, t') := to_GU_ (fst acc_s) binders t in (* stuff in s cannot cause us to be suddenly under more binders in t*)
                 (acc_t, @tmbin B s' t')
  | tmbuiltin d => (used, binders, tmbuiltin d)
  end.

Compute (to_GU_ nil nil (tmabs "x" PlutusIR.Kind_Base (tmvar "x"))). (* should be λxa . xa*)
Compute (to_GU_ nil nil (tmbin (tmvar "x") (tmvar "y"))). (* should be xy*)
Compute (to_GU_ nil nil (tmbin (tmabs "y" PlutusIR.Kind_Base (tmbin (tmvar "x") (tmvar "y"))) (tmvar "y"))). 
Compute (to_GU_ nil nil (tmbin (tmabs "y" PlutusIR.Kind_Base (tmvar "y")) (tmvar "y"))). (* should be x(λya . ya)*)
Compute (to_GU_ nil nil (tmbin (tmabs "y" PlutusIR.Kind_Base (tmbin (tmvar "x") (tmvar "y"))) (tmvar "x"))).
Compute (to_GU_ nil nil (tmabs "x" PlutusIR.Kind_Base (tmbin (tmabs "y" PlutusIR.Kind_Base (tmbin (tmvar "x") (tmvar "y"))) (tmvar "x")))).


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

Compute (to_GU (tmbin (tmabs "y" PlutusIR.Kind_Base (tmvar "y")) (tmvar "ya"))). 
Compute (to_GU (tmbin (tmvar "ya") (tmabs "y" PlutusIR.Kind_Base (tmvar "y")))). 

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
      assert (Hftvlam: In x (ftv (@tmabs USort s k s0))).
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
        assert (In x (ftv (@tmabs USort s k s0))).
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
        assert (In x (ftv (@tmbin BSort s1 s2))) by now apply ftv_c_appl.
        specialize (H0 x H2).
        assumption.
    + specialize (IHs2 used1 R).
      rewrite <- Heqp2 in IHs2.
      simpl in IHs2.
      eapply IHs2.
      * intros. apply H. simpl. apply in_app_iff. right. auto. auto.
      * intros.
        assert (In x (ftv (@tmbin BSort s1 s2))) by now apply ftv_c_appr.
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
      - assert (In y (ftv (@tmabs USort s k s0))).
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
        assert (In y (ftv (@tmbin BSort s1 s2))).
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
        assert (In y (ftv (@tmbin BSort s1 s2))).
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
           assert (In x (ftv (@tmabs USort s k s0))).
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
          assert (In y (ftv (@tmbin BSort s1 s2))).
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
  st = to_GU (@tmbin B s t) -> {s' & { t' & (st = @tmbin B s' t') * Alpha [] s s' * Alpha [] t t'} }%type.
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
  assert (Alpha [] (@tmbin B idk idk') (@tmbin B s t)).
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
  st = to_GU (@tmbin BA (@tmabs BL x A s) t) -> {x' : string & {s' & { t' & (st = @tmbin BA (@tmabs BL x' A s') t') * Alpha ((x, x')::nil) s s' * Alpha [] t t'} } }%type.
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
    So then GU (tmabs X A (to_GU'' X s)) by also GU (to_GU'' X s).
*)
Lemma to_GU''__GU_lam {B} X A s : GU (@tmabs B X A (to_GU'' X s)).
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

