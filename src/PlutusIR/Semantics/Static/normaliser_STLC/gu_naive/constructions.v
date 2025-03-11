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

From PlutusCert Require Import STLC_named pre alpha freshness util alpha_ctx_sub.



Definition fresh_to_GU_ (ftvs : list string) (binders : list (string * string)) (x : string) := 
  String.concat "" (ftvs ++ map fst binders ++ map snd binders ++ x::nil ++ "a"::nil).
(* a is necessary for empty ftvs and binders*)

Fixpoint to_GU_ (used : list string) (binders : list (string * string)) (s : term) :=
  match s with
  | tmvar x => match lookup x binders with
              | Some y => (used, binders, tmvar y) (* this was bound and (possibly) renamed, or free and renamed to itself*)
              | None => ((x::used), binders, tmvar x) (* this branch should never happen: all binders and ftvs should be in the map. *)
              end
  | tmlam x A s => (* we can freshen regardless *)
                    let x' := fresh_to_GU_ used binders x in
                    let (acc, term_body) := to_GU_ used ((x, x')::binders) s in
                    ((fst acc ++ (x::x'::nil)), binders, tmlam x' A term_body)
  | tmapp s t => let (acc_s, s') := to_GU_ used binders s in
                 let (acc_t, t') := to_GU_ (fst acc_s) binders t in (* stuff in s cannot cause us to be suddenly under more binders in t*)
                 (acc_t, tmapp s' t')
  end.

Compute (to_GU_ nil nil (tmlam "x" tp_base (tmvar "x"))). (* should be λxa . xa*)
Compute (to_GU_ nil nil (tmapp (tmvar "x") (tmvar "y"))). (* should be xy*)
Compute (to_GU_ nil nil (tmapp (tmlam "y" tp_base (tmapp (tmvar "x") (tmvar "y"))) (tmvar "y"))). 
Compute (to_GU_ nil nil (tmapp (tmlam "y" tp_base (tmvar "y")) (tmvar "y"))). (* should be x(λya . ya)*)
Compute (to_GU_ nil nil (tmapp (tmlam "y" tp_base (tmapp (tmvar "x") (tmvar "y"))) (tmvar "x"))).
Compute (to_GU_ nil nil (tmlam "x" tp_base (tmapp (tmlam "y" tp_base (tmapp (tmvar "x") (tmvar "y"))) (tmvar "x")))).


Definition remove_dups (l : list (string * string)) := l.

Opaque remove_dups.

(* By precalculating ftvs, we cannot get that a binder is accidentally renamed to an ftv later in the term
  this was problematic, because to_GU_ does not rename ftvs
*)
Definition to_GU (s : term) :=
let tvs := tv s in 
(* We do tv even, isntead of only ftvs: can not become problematic, 
  and helps with proofs of GU (that we already know that when we encounter any binder, that it will be in "used")
    But before we used the fact that all ftvs are unique. For tvs that is not the case.
     TODO:  hence we must also remove duplicates, to keep the UniqueRhs property.
  *)
snd (to_GU_ tvs (remove_dups (map (fun x => (x, x)) tvs)) s).

Compute (to_GU (tmapp (tmlam "y" tp_base (tmvar "y")) (tmvar "ya"))). 
Compute (to_GU (tmapp (tmvar "ya") (tmlam "y" tp_base (tmvar "y")))). 

Fixpoint uniqueRHs_ (acc : list string) (R : list (string * string)) :=
  match R with
  | nil => True
  | cons (x, y) R' => ~ In y acc /\ uniqueRHs_ (y :: acc) R'
  end.

(* this is not exactly uniqueness as it allows for identical pairs, but that's ok for alpha, but not for uniqueness!*)
Definition UniqueRhs (R : list (string * string)) := uniqueRHs_ nil R.

Definition KindOfUniqueRhs (R : list (string * string)) (s : term) := 
  forall x y, lookup x R = Some y -> AlphaVar R x y.

(* fresh generates something not in R*)
Lemma uniqueRhs_fresh x R used : UniqueRhs R -> UniqueRhs ((x, fresh_to_GU_ used R x)::R).
Admitted.

(* by unique we have that (x, y) is the only pair with y. by lookup x, it is the leftmost x pair*)
Lemma uniqueRhs_lookup_Some x y R : UniqueRhs R -> lookup x R = Some y -> AlphaVar R x y.
Admitted.

Lemma to_GU__alpha_ s R used : UniqueRhs R -> (forall x, In x (ftv s) -> {y & In (x, y) R}) -> Alpha R s (snd (to_GU_ used R s)).
Proof.
  generalize dependent R.
  generalize dependent used.
  induction s; intros.
  - simpl. destruct (lookup s R) eqn:lookup_x_R.
    + constructor. 
      apply uniqueRhs_lookup_Some in lookup_x_R; auto.
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
    + eapply uniqueRhs_fresh. auto.
    + intros.
      destr_eqb_eq x s.
      * exists (fresh_to_GU_ used R s).
        simpl. intuition.
      * specialize (H0 x).
        assert (In x (ftv (tmlam s t s0))) by admit. (* x <> s)*)
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
      * assumption.
      * intros.
        assert (In x (ftv (tmapp s1 s2))) by admit. (* In ftv composes*)
        specialize (H0 x H2).
        assumption.
    + specialize (IHs2 used1 R).
      rewrite <- Heqp2 in IHs2.
      simpl in IHs2.
      eapply IHs2.
      * assumption.
      * intros.
        assert (In x (ftv (tmapp s1 s2))) by admit. (* In ftv composes*)
        specialize (H0 x H2).
        assumption.
Admitted.   



Lemma to_GU__alpha s : Alpha [] s (to_GU s).
Proof.
  remember (to_GU s) as s'.
  unfold to_GU in Heqs'.
  remember (map (fun x => (x, x)) (tv s)) as R.
  rewrite Heqs'.
  assert (R ⊢ s ~ (to_GU_ (tv s) R s).2).
  {
    eapply to_GU__alpha_.
    - (* ftvs are unique *) admit.
    - (* by constructino of R *) 
      intros.
      exists x.
      apply lookup_In.
      subst.    
      admit.
  }
  eapply alpha_weaken_ids with (idCtx := R).
  - subst.
    clear H.
    induction (tv s); simpl; constructor; auto.
  - assumption.
Admitted.


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
    admit.
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
Admitted.

(* to_GU_ creates binders that are not in used*)
Lemma no_binder_used used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (btv s') -> ~ In x used).
Admitted.

(* to_GU_ remembers which ftvs and btvs have occurred*)
Lemma idk_used3 used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (tv s') -> In x used').
Admitted.

(* All ftvs are mapped by R (that's how we initialize it. (so maybe this shouldnt be a lemma, but an argument))*)
Lemma ftvs_mapped_by_R used binders s s' used' binders' :
(* This is an invariant we want to enforce on construction and in each lemma that we want to use this lemma*)
  (forall y, In y (ftv s) -> {x & (In (y, x) binders)}) -> 
  
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (ftv s') -> {y & (In (y, x) binders)}%type).
Proof.
  intros.
  generalize dependent used.
  generalize dependent binders.
  generalize dependent used'.
  generalize dependent binders'.
  generalize dependent s'.
  induction s; intros.
  - assert (s' = (tmvar x)) by admit.
    (* forall y in ftv s, there exists x0 s.t. (In (y, x0) binders.
        Let this be so such that lookup y binders = x0.
        - If it is not, there exists another x0' such that this is true (there has to be).
    )*)
    specialize (H s).
    assert (In s (ftv (tmvar s))).
    {
      now apply ftv_var_eq.
    }
    specialize (H H3).
    destruct H as [x0 H].
    assert (lookup s binders = Some x0) by admit. (* see above.*)
    simpl in H0.
    rewrite H4 in H0.
    inversion H0.
    rewrite H8 in H1.
    assert (x = x0).
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
      admit.
      (* eapply ftv_lam. *)
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
      - assert (In y (ftv (tmlam s t s0))).
        {
          (* by In y ftv s0 and y <> s*)
          admit.
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
    assert (sum (In x (ftv s1')) (In x (ftv s2'))).
    {
      (* By In x (ftv (tmapp s1' s2'))*)
      admit.
    }
    destruct H2.
    + 
      specialize (IHs1 s1' i binders1 used1 binders).
      assert (forall y : string, y ∈ ftv s1 -> {x0 : string & (y, x0) ∈ binders}).
      {
        intros.
        specialize (H y).
        assert (In y (ftv (tmapp s1 s2))).
        {
          admit. (* in ftv composes over app*)
        }
        specialize (H H6).
        destruct H as [x0 H].
        exists x0.
        assumption.
      }
      specialize (IHs1 H2 used Heqp1).
      auto.
    + specialize (IHs2 s2' i binders2 used2 binders).
      assert (forall y : string, y ∈ ftv s2 -> {x0 : string & (y, x0) ∈ binders}).
      {
        intros.
        specialize (H y).
        assert (In y (ftv (tmapp s1 s2))).
        {
          admit. (* in ftv composes over app*)
        }
        specialize (H H6).
        destruct H as [x0 H].
        exists x0.
        assumption.
      }
      specialize (IHs2 H2 used1 Heqp2).
      auto.
Admitted.


Lemma used_never_removed used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> forall x, In x used -> In x used'.
Admitted.


Lemma no_btv_in_binders used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (btv s') -> ~ In x (map snd binders)).
Admitted.

Lemma no_btv_in_binders_fst used binders s s' used' binders' :
  ((used', binders'), s') = to_GU_ used binders s -> (forall x, In x (btv s') -> ~ In x (map fst binders)).
Admitted.

Lemma to_GU__GU_ s R used : (forall x, In x (ftv s) -> {y & In (x, y) R}) -> (forall x, In x (tv s) -> In x used) -> GU (to_GU_ used R s).2.
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
        -- (* ok??? for some reason we do have nice composition behaviour with lam. we can definitely abstract that away*)
           exists (fresh_to_GU_ used R x).
           left. reflexivity.
        -- specialize (H x).
           assert (In x (ftv (tmlam s t s0))) by admit. (* x <> s*)
           specialize (H H3).
           destruct H as [y H].
           exists y.
           right.
           assumption.
      * intros.
        eapply H0.
        admit.
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
        (* ftv composes app*)
        admit. 
      * intros.
        eapply H0.
        (* tv composes *)
        admit.
    + specialize (IHs2 used1 R).
      rewrite <- Heqp2 in IHs2.
      simpl in IHs2.
      eapply IHs2.
      * intros.
        eapply H.
        (* ftv composes app*)
        admit.
      * intros.
        eapply used_never_removed; eauto.
        eapply H0.

        (* by H0 and tv composability we get In x used. Then also In x used1 (since used1 is created from used and never removes stuff)*)
        admit.
    + intros.
      intros Hcontra.
      eapply idk_used3 with (used' := used1) in Hcontra; eauto.
      eapply no_binder_used with (used := used1)in H1; eauto.
    + intros.
      assert (~ In x used) by now apply no_binder_used with (x := x) in Heqp1.


      assert (~ In x (btv s2')).
      {
        intros Hcontra2.
        eapply no_binder_used with (used := used1) in Hcontra2.
        contradiction Hcontra2.
        assert (In x (tv s1')) by admit. (* In btv, then In tv*)
        eapply idk_used3; eauto. eauto.
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
          assert (In y (ftv (tmapp s1 s2))).
          {
            admit. (* In ftv composes over app*)
          }
          specialize (H H5).
          assumption.
        - eauto.
      }
      (* Not in ftv and not in btv: done *)
    
      admit.
Admitted.

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
  exists x.
  (* x in tv s, then x x in the map*)
  admit.
Admitted.


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
    eapply to_GU__alpha_.
    - (* ftvs are unique *) admit.
    - (* by constructino of R *) 
      intros.
      exists x.
      apply lookup_In.
      subst.    
      (* by x in ftv s => x in tv s => Hence (x, x) in R*)
      admit.
  }
  eapply alpha_weaken_ids with (idCtx := R).
  - subst.
    clear H.
    induction (X :: tv T ++ tv s); simpl; constructor; auto.
  - assumption.
Admitted.

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
      admit.
    }
    exists x.
    (* x in tv s, then x x in the map*)
    admit.
  - intros. (* x in tv s, then also x in supserset of tv s*)
    admit.
Admitted.

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
      assert (In y (tv T ++ tv s)).
      {
        intuition.
      }
      auto.
Qed.



(* TODO: probably we don't need this and can do inversion once we haqve defined to_GU_app? *)
Lemma to_GU_app_unfold {s t st} :
  st = to_GU (tmapp s t) -> {s' & { t' & (st = tmapp s' t') * Alpha [] s s' * Alpha [] t t'} }%type.
Proof.
intros.
  unfold to_GU in H.
  simpl in H.
  remember (to_GU_ (tv s ++ tv t)
  (remove_dups (map
  (fun x : string => (x, x))
  (tv s ++ tv t)))
  s) as p.
  destruct p as [ [used binders] idk].
  remember (to_GU_ (used, binders).1
  (remove_dups (map
  (fun x : string => (x, x))
  (tv s ++ tv t)))
  t) as q.
  destruct q as [ [used' binders'] idk'].
  simpl in H.
  exists idk. exists idk'.
  split.
  split; auto.
  - assert (idk = snd (to_GU_ (tv s ++ tv t)
  (remove_dups (map
  (fun x : string => (x, x))
  (tv s ++ tv t)))
  s)) by admit.
  remember (remove_dups (map
  (fun x : string => (x, x))
  (tv s ++ tv t))) as R.
  assert (R ⊢ s ~ idk).
  {
    rewrite H0.
    eapply to_GU__alpha_.
    - (* by identity renamings AND no duplicates*) admit.
    - intros.
      exists x.
      (* x in ftv s, hence x in (tv s ++ tv t), hence (x, x) in the map.
        remove_dups can not cause list lookup to start failing... done.
      *)
      admit.
  }
  eapply alpha_weaken_ids with (idCtx := R).
  + (* construction *) admit.
  + assumption.
Admitted.

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
Admitted.

(* This should be easy enough. It is the same as to_GU' but without a T.
    Then we know X not in ftv s and X not in btv s.
    So then GU (tmlam X A (to_GU'' X s)) by also GU (to_GU'' X s).
*)
Lemma to_GU''__GU_lam X A s : GU (tmlam X A (to_GU'' X s)).
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

Opaque to_GU'.
Opaque to_GU''.



(* step subst constructions, mock definitions/axiomatization
  We need two: For one we need global uniqueness properties, for the other we need to be able to write it as substs
  as in commute_subst

  (* Note: we cannot always force that subs' is of the form subs _ _, becauswe we need it to be GU
                              Counter example: subs ((x, λy. y)) (tmapp x x). No matter what binders we choose in the arguments of sub, the result can never be GU.
                                By calling the whole substitution (without specifying args) subs', we can force GU.
              *) 
*)
Definition sconstr1 (x x0 : string) p s t :=
  ((subs ((x, p)::nil) s), (subs ((x, p)::nil) t)).

(* TODO: we need nc requirement*)
Lemma sconstr1_alpha_s s x x0 p sub_s sub_t t :
  (sub_s, sub_t) = sconstr1 x x0 p s t ->
  Alpha [] sub_s (subs ((x, p)::nil) s).
Admitted.

(* TODO: we need nc requriement *)
Lemma sconstr1_alpha_t s x x0 p sub_s sub_t t :
  (sub_s, sub_t) = sconstr1 x x0 p s t ->
  Alpha [] sub_t (subs ((x, p)::nil) t).
Admitted.

Lemma sconstr1_gu A s x x0 p sub_s sub_t t :
  (sub_s, sub_t) = sconstr1 x x0 p s t ->
  GU (tmapp (tmlam x0 A sub_s) sub_t).
Admitted.


(* We first generate p. Then we can generate t with (ftv info on p).
  then we generate s with ftv info on t and p.
    This creates the required NC properties.

    For NC sub we need some more stuff, but I think it is manageable.
    Maybe we first collect ftvs for everything and that way make sure no binder has that name.
    This should not be hard since we have empty R and we will use to_GU_' everywhere probably (where we supply additional ftvs that may not be used as binders)
  *)
Definition sconstr2 (x0 : string) (t : term) (x : string) (p s : term) :=
  (s, t, p).

Lemma sconstr2_alpha_s x0 t x p s s' t' p':
  (s', t', p') = sconstr2 x0 t x p s ->
  Alpha [] s s'.
Admitted.

Lemma sconstr2_alpha_t x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s->
  Alpha [] t t'.
Admitted.

Lemma sconstr2_alpha_p x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s->
  Alpha [] p p'.
Admitted.

Lemma sconstr2_nc_s x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  NC s' ((x, p')::nil).
Admitted.

Lemma sconstr2_nc_s_t x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  NC s' ((x0, t')::nil).
Admitted.

Lemma sconstr2_nc_t x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  NC t' ((x, p')::nil).
Admitted.

(* We have control over all binders in s' and p' and subs does not introduce new binders,
  hence we can create a construction that satisfies this*)
Lemma sconstr2_nc_sub x0 t x p s s' t' p' :
  (s', t', p') = sconstr2 x0 t x p s ->
  NC (psubs ((x, p')::nil) s') ((x0, (psubs ((x, p')::nil) t'))::nil).
Admitted.

Opaque sconstr1.
Opaque sconstr2.

Create HintDb sconstr2_db.
Hint Resolve sconstr2_alpha_s sconstr2_alpha_t sconstr2_nc_sub sconstr2_nc_s sconstr2_nc_t sconstr2_nc_s_t : sconstr2_db.

Require Import List.
Import ListNotations.

(* all elements in l1 not in l2*)
Definition list_diff {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})  
  (l1 l2 : list A) : list A :=  
  filter (fun x => if in_dec eq_dec x l2 then false else true) l1.

(* We know the result is R ++ R' (i.e. prepended by argument), but that is not so 
    important here in the axiomatization, just that there exists one

  TODO: Can we use one of the other constructions, like the one for type_L?  
  I also feel like we may need conditions here on t?

  this is not trivial because:
  - suppose (x, x') in R.
  - and now suppose x' in t.
  - if then also x in t, then x gets renamed to x', and we have a clash
  - solution: rename away all ftvs in t that are not free in s, to fresh stuff
  - Then still Alpha R+ s s' (since nto free in s)

  - then for all x in ftv t. if it is in (ftv s), then R(s) gives some x' (or if its not in there identical)
      it is then also not in R+, so Alpha R' x x'.
  - now suppose we find an x in ftv t that is not in ftv s. 
      Then we rename it to smoething fresh. What if it was however in R already?

    We can use to_GU_ with this special R probably to get the alpha behaviour.
    R' will only have vars not in ftv s, so that should be fine:
    problematic is: R does nto have to have UniqueRHS. Maybe we can remove it, or remove conditions of that lemma
  *)


Fixpoint strip_R' (R : list (string * string)) (acc : list (string * string)) :=
  match R with 
  | nil => ((nil : list (string * string)), acc) 
  | (x, y) :: R' => match lookup x acc with
                    | Some z => (strip_R' R' acc)  (* already found, ignore *)
                    | None => (strip_R' R' (acc ++ (x, y)::nil))
                    end
  end.

Require Import Coq.Program.Equality.

Definition strip_R (R : list (string * string)) :=
  snd (strip_R' R nil).

Lemma strip_R_preserves_alpha R s s' :
  Alpha R s s' -> Alpha (strip_R R) s s'.
Proof.
  intros.
  generalize dependent R.
  generalize dependent s'.
  induction s; intros.
  - inversion H; subst.
    constructor.
    (* no clue*)
    admit.
  - inversion H; subst.
    constructor.
    (* no clue*)
    admit.
  - inversion H; subst.
    constructor.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto.
Admitted.

(* forall ftvs in s, lookup that in R, to get (x, y) and add that to the new R*)

Definition a_R_constr R (s s' : term) t : list (string * string) :=
  let used := tv s ++ tv s' ++ tv t ++ (map fst R) ++ (map snd R) in

  (* rename those ftvs in t, that are not ftvs in s to fresh stuff
    all ftvs in s are already mapped by R to something else, t should follow the same 
      behaviour for these ftvs, since they refer to the same ftv.

      This also means we can easily add Rfr in front of R and still keep s-alpha
  *)
  let Rfr := (map (fun x => (x, fresh18 used)) (list_diff string_dec (ftv t) (ftv s))) in
  let R_u := strip_R R in
  let R_id := map (fun x => (x, x)) (ftv t) in
  Rfr ++ R_u ++ R_id.

Definition a_constr {R} {s s' : term} t : prod (list (string * string)) (term) :=
  let R' := @a_R_constr R s s' t in
  let used' := tv s ++ tv s' ++ tv t ++ (map fst R') ++ (map snd R') in 
  (R', snd (to_GU_ used' R' t)).

Lemma a_R_constr_UniqueRHS R R' s s' t :
  R' = @a_R_constr R s s' t ->
  UniqueRhs R'.
Admitted.

Lemma a_R_constr_alpha_s R s s' t R' :
  R' = a_R_constr R s s' t ->
  Alpha R s s' ->
  Alpha R' s s'.
Proof.
Admitted.

Lemma a_constr__t_alpha {R s s' t R' t'} :
  (R', t') = @a_constr R s s' t ->
  Alpha R' t t'.
Proof.
  unfold a_constr.
  intros.
  inversion H.
  apply to_GU__alpha_.
  - eapply a_R_constr_UniqueRHS. eauto.
  - intros.
    exists x.
    apply in_app_iff.
    right.
    apply in_app_iff.
    right.
    eapply in_map with (f := (fun x0 : string =>
(x0, x0))) in H0.
    eauto.
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
  let used := tv_t ++ tvs in
  (* a little problematic, this can construct the same ones. We need to fold instead, moving along the fresh vars in new fresh var generation*)
  (* we should nto add duplicates!*)
  let R1 := (map (fun x => (x, fresh18 used)) btvs) in
  (* we rename those ftvs in t that are binders in s and sigma*)
  let R2 := map (fun x => (x, x)) (list_diff string_dec (ftv t) btvs) in
  (R1, R2). 


Definition t_constr (t : term) (s : term) (sigma : list (string * term)) (X : string) : prod term (list (string * string)) :=
  let tvs := tv s ++ tv_keys_env sigma in
  let tv_t := tv t in
  let used := tv_t ++ tvs in
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
  - (* yes by construction. either they are mapped to something fresh (if they are bound in s or sigma)
        or else there is identity subst in R2*)
    admit.
  - intros.
    apply in_app_iff.
    left.
    auto.
Admitted.

Lemma t_constr__a_t {t t' R s sigma X }:
  (t', R) = t_constr t s sigma X ->
  Alpha R t t'.
Proof.
  intros.
  unfold t_constr in H.
  remember (tv t ++ tv s ++ tv_keys_env sigma) as used.
  remember (map (pair^~ (fresh18 used)) (btv s ++ btv_env sigma)) as binders.
  inversion H.
  apply to_GU__alpha_.
  - (* we will do that by construction
        AH, here we need to NOT add (x, x) for x that is already in lhs of binders
    *)
    admit.
  - intros.
    exists x.
    apply in_app_iff.
    right.
    (* x in ftv t, so (x, x) in (map (x -> (x,x)) (ftv t))*)
Admitted.

Lemma t_constr__fresh_X_btv_t' {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  ~ In X (btv t').
Admitted.

(* by construction we rename all ftvs in t that are binders in sigma*)
Lemma t_constr__fresh_btv_env_sigma__ftv_t' {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  (forall Y, In Y (btv_env sigma) -> ~ In Y (ftv t')).
Admitted.

Lemma R_constr__a_s {R1 R2 t s sigma X} :
  GU s ->
  Uhm sigma s ->
  (R1, R2) = R_constr t s sigma X ->
  Alpha (R1 ++ R2) s s.
Proof.
  intros HGU H H0.
  apply alpha_vacuous_R.
  - intros.
    split.
    + unfold Uhm in H.
      destruct H as [ [uhm1 _] _].
      intros Hcontra.
      remember Hcontra as Hcontra2; clear HeqHcontra2.
      apply extend_ftv_to_tv in Hcontra.
      apply uhm1 in Hcontra; auto.
      (* x is in ftv s, hence not in btv s by GU s. Hence it must be in btv_env, since it is in R1.*)
      admit.
    + (* R_constr has s as argument, and does not generate anything equal to a tv in s *)
      admit.
  - apply alpha_extend_ids.
    (* R2 is always ids *)
    admit.
Admitted.

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
  (R1, R2) = R_constr t s sigma X ->
  αCtxSub (R1 ++ R2) sigma sigma.
Proof.
  intros.
  unfold Uhm in H.
  (* R2 is idenity again.
     R1 by uhm1 and uhm2: if it is in R1, then it is either in btv_env sigma or btv s, in both cases it is not in ftv_keys_env sigma, and we have vacuous_sub_ctx
  *)
Admitted.

Lemma t_constr__a_sigma {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  αCtxSub R sigma sigma.
(* Analogous to bove I think *)
Admitted.

Lemma t_constr__uhm1 {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv t') -> ~ In x (tv s).
Proof.
  (* t_constr does not generate binders that are tv in s (tv s in used)*)
Admitted.

Lemma t_constr__uhm2 {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv t') -> ~ In x (ftv_keys_env sigma).
Proof.
  (* Same by tv_keys_env in sigma and*)
Admitted.

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
Qed.

Lemma map_helper x s sigma (fr : string) :
  In x (btv s) -> In x ( map (fun x0 : string => (x0, fr).1)
    (btv s ++ btv_env sigma)).
Admitted.

Lemma R_constr_lookup_alpha {R1 R2 t s sigma X} :
  (R1, R2) = R_constr t s sigma X ->
  forall x X', lookup x (R1 ++ R2) = Some X' -> AlphaVar (R1 ++ R2) x X'.
Proof.
  (* rhs of R1 ++ R2 is unique, hence also lookup X' (swap (R1 ++ R2) = x)*)
Admitted.

Lemma t_constr__uhm3 {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv s) -> ~ In x (ftv t').
Proof.
  intros.
  assert (Hfresh_pair: {X' & In (x, X') R}).
  {
    (* intros Hcontra. simpl in H.
    unfold t_constr in H.
    remember (R_constr t s sigma X) as p.
    destruct p as [R1 R2].
    inversion H.
    remember ((to_GU_
  (tv t ++ tv s ++ tv_keys_env sigma)
  (R1 ++ R2) t)) as q.
    destruct q as [ [used' binders'] t''].
    simpl in H2. rewrite <- H2 in *.
    eapply no_btv_in_binders_fst with (binders := R1 ++ R2) in Hcontra; eauto.
    assert (In x (map fst R1)).
    {
      clear Heqq H H2 Hcontra H3.
      unfold R_constr in Heqp.
      inversion Heqp.
      clear H2.
      remember (fresh18 (tv t ++ tv s ++ tv_keys_env sigma)) as fr.
      rewrite map_map.
      apply map_helper. auto.
    }
    rewrite map_app in Hcontra.
    apply not_in_app in Hcontra.
    destruct Hcontra as [Hcontra _].
    contradiction. *)
    admit.
  }
  destruct Hfresh_pair as [X' HX'].
  assert ({X'' & lookup x R = Some X''}) by admit.
  destruct H1 as [X'' Hlookup].
  eapply @ftv_helper_constr with (R := R) (t := t) (X' := X'').
  - eapply t_constr__a_t; eauto. 
  - inversion H.
    clear H H2.
    rewrite map_app.
    apply not_in_app.
    split.
    +  (* x in btv s, hence no id x in R2, and rhs of R1 is only fresh stuff and x in btv s, hence in used, hence not fresh*) 

      admit.
    + (* R2 is an identity subst.
      By contradiction: If x in map snd R2, then x in map fst R2.
      by construction then x not in btvs, and hence x notin btv s. contradiction.
      *)
      admit.
  - (* by Xfr being fresh over used and x in btv s in used*) admit.
  - unfold t_constr in H.
    remember (R_constr t s sigma X) as p.
    destruct p as [R1 R2].
    eapply R_constr_lookup_alpha in Heqp; inversion H; eauto.
    subst. eauto.
  - intros Hcontra. simpl in H.
    unfold t_constr in H.
    remember (R_constr t s sigma X) as p.
    destruct p as [R1 R2].
    inversion H.
    remember ((to_GU_
  (tv t ++ tv s ++ tv_keys_env sigma)
  (R1 ++ R2) t)) as q.
    destruct q as [ [used' binders'] t''].
    simpl in H2. rewrite <- H2 in *.
    eapply no_btv_in_binders_fst with (binders := R1 ++ R2) in Hcontra; eauto.
    rewrite <- H3 in Hcontra.
    eapply in_map with (f := fst) in HX'.
    simpl in HX'.
    contradiction.

  - intros Hcontra. simpl in H.
    unfold t_constr in H.
    remember (R_constr t s sigma X) as p.
    destruct p as [R1 R2].
    inversion H.
    remember ((to_GU_
  (tv t ++ tv s ++ tv_keys_env sigma)
  (R1 ++ R2) t)) as q.
    destruct q as [ [used' binders'] t''].
    assert (HX'': In (x, X'') R) by admit.
    simpl in H2. rewrite <- H2 in *.
    eapply no_btv_in_binders with (binders := R1 ++ R2) in Hcontra; eauto.
    rewrite <- H3 in Hcontra.
    eapply in_map with (f := snd) in HX''.
    simpl in HX'.
    contradiction.
Admitted.


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
  - eapply t_constr__uhm3. eauto. auto.
Qed.

Lemma t_constr__nc_subs {t t' R s sigma X} :
  ~ In X (btv s) -> (* We dont have control over s or X in construction*)
  ~ In X (btv_env sigma) -> (* we do not have control over sigma*)
  (t', R) = t_constr t s sigma X ->
  NC (subs sigma s) ((X, t')::nil).
Proof.
  intros.
  constructor.
  - constructor.
  - intros.
    split.
    + (* by subs does nto introduce btvs *)
      admit.
    + (* suppose y in btv subs sigma s. Then y in sigma or s. Hence by construction. 
        sub can remove btvs, but not introduce them.
    *)
      admit.
Admitted.

Opaque t_constr.