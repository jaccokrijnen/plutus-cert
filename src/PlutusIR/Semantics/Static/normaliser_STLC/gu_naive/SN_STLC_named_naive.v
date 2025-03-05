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
From PlutusCert Require Import alpha alpha_rename rename util alpha_ctx_sub freshness alpha_freshness.

Lemma lookup_In {A} k (v : A) xs :
  lookup k xs = Some v ->
  In (k, v) xs
.
Proof.
Admitted.

Lemma lookup_not_In {A} k (v : A) xs :
  lookup k xs = None ->
  ~ In (k, v) xs.
Admitted.




Create HintDb α_eq_db.
Hint Constructors Alpha : α_eq_db.
Hint Resolve alpha_refl : α_eq_db.
Hint Resolve alpha_sym : α_eq_db.
Hint Resolve alpha_trans : α_eq_db.
Hint Constructors AlphaCtxRefl : α_eq_db.
Hint Constructors AlphaVar : α_eq_db.
Hint Constructors αCtxSub : α_eq_db.
Hint Constructors AlphaCtxSym : α_eq_db.
Hint Constructors αCtxTrans : α_eq_db.
Hint Resolve alpha_extend_ids : α_eq_db.
Hint Constructors IdCtx : α_eq_db.
Hint Resolve sym_alpha_ctx_is_sym : α_eq_db.
Hint Resolve sym_alpha_ctx_is_sym : α_eq_db.
Hint Resolve sym_alpha_ctx_left_is_sym  : α_eq_db.

Fixpoint sub (X : string) (U T : term) : term :=
  match T with
  | tmvar Y =>
    if X =? Y then U else tmvar Y
  | tmlam Y K1 T' =>
    tmlam Y K1 (sub X U T')
  | tmapp T1 T2 =>
    tmapp (sub X U T1) (sub X U T2)
  end.

Fixpoint subCA (X : string) (U T : term) : term :=
  match T with
  | tmvar Y =>
    if X =? Y then U else tmvar Y
  | tmlam Y K1 T' =>
    if X =? Y then tmlam Y K1 T' else tmlam Y K1 (subCA X U T')
  | tmapp T1 T2 =>
    tmapp (subCA X U T1) (subCA X U T2)
  end.

Inductive step_naive : term -> term -> Set :=
| step_beta (x : string) (A : type) (s t : term) :
    step_naive (tmapp (tmlam x A s) t) ( sub x t s)
| step_appL s1 s2 t :
    step_naive s1 s2 -> step_naive (tmapp s1 t) (tmapp s2 t)
| step_appR s t1 t2 :
    step_naive t1 t2 -> step_naive (tmapp s t1) (tmapp s t2)
| step_abs x A s1 s2 :
    step_naive s1 s2 -> step_naive (tmlam x A s1) (tmlam x A s2).

    

Fixpoint subs (sigma : list (string * term)) (T : term) : term :=
  match sigma with
  | nil => T
  | cons (x, t) sigma' => sub x t (subs sigma' T) (* or the other way around?*)
  end.

Lemma single_subs_is_sub X T s :
  subs [(X, T)] s = sub X T s.
Proof.
  simpl. reflexivity.
Qed.



(* parallel subs *)
Fixpoint psubs (sigma : list (string * term)) (T : term) : term :=
  match T with
  | tmvar x => match lookup x sigma with
              | Some t => t
              | None => tmvar x
              end
  | tmlam x A s => tmlam x A (psubs sigma s)
  | tmapp s t => tmapp (psubs sigma s) (psubs sigma t)
  end.

Lemma single_subs_is_psub X T s :
  psubs [(X, T)] s = sub X T s.
Proof.
  induction s.
  - simpl. destr_eqb_eq X s. reflexivity.
    reflexivity.
  - simpl. f_equal. apply IHs.
  - simpl. f_equal. apply IHs1. apply IHs2.
Qed.

(* parallel substitution *)

Fixpoint subsCA (sigma : list (string * term)) (T : term) : term :=
  match sigma with
  | nil => T
  | cons (x, t) sigma' => subCA x t (subsCA sigma' T) (* or the other way around?*)
  end.

(* Define the rewrite rules *)
Lemma subs_tmapp : forall sigma s1 s2,
  subs sigma (tmapp s1 s2) = tmapp (subs sigma s1) (subs sigma s2).
Proof.
  intros sigma s1 s2.
  induction sigma as [| [x t] sigma' IHsigma'].
  - reflexivity.
  - simpl. rewrite IHsigma'. reflexivity.
Qed.

Lemma subs_tmlam : forall sigma x A s,
  subs sigma (tmlam x A s) = tmlam x A (subs sigma s).
Proof.
  intros sigma x A s.
  induction sigma as [| [y t] sigma' IHsigma'].
  - reflexivity.
  - simpl. rewrite IHsigma'. reflexivity.
Qed.

Hint Rewrite
  (* Rewrite rule for application *)
  subs_tmapp : subs_db.

Hint Rewrite
  (* Rewrite rule for lambda abstraction *)
  subs_tmlam : subs_db.

(* Add the lemmas to the hint database *)
Hint Resolve subs_tmapp : subs_db.
Hint Resolve subs_tmlam : subs_db.

(* So sub is also rewritten when rewriting subs *)
Hint Extern 1 => simpl sub : subs_db.

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
snd (to_GU_ tvs (map (fun x => (x, x)) tvs) s).

Compute (to_GU (tmapp (tmlam "y" tp_base (tmvar "y")) (tmvar "ya"))). 
Compute (to_GU (tmapp (tmvar "ya") (tmlam "y" tp_base (tmvar "y")))). 

Fixpoint uniqueRHs_ (acc : list string) (R : list (string * string)) :=
  match R with
  | nil => True
  | cons (x, y) R' => ~ In y acc /\ uniqueRHs_ (y :: acc) R'
  end.

(* this is not exactly uniqueness as it allows for identical pairs, but that's ok for alpha, but not for uniqueness!*)
Definition UniqueRhs (R : list (string * string)) := uniqueRHs_ nil R.

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


Inductive GU : term -> Set :=
| GU_var x : GU (tmvar x)
(* in app, if s and t do not share GU_vars: *)
| GU_app s t : 
    GU s -> 
    GU t -> 
    forall (H_btv_btv_empty : forall x, In x (btv t) -> ~ In x (tv s)),
    forall (H_btv_ftv_empty : forall x, In x (btv s) -> ~ In x (tv t)),
    GU (tmapp s t)
| GU_lam x A s : 
    GU s -> 
    ~ In x (btv s) ->
    GU (tmlam x A s).

(* Not sure how to call this yet.
if we have NC t sigma
We want to have unique binders elementwise in sigma.
No binder in t can occur as free or bound variable in sigma,
  thus substituting sigma in t will not cause unwanted capture.
*)
Inductive NC : term -> list (string * term) -> Set :=
| nc_nil s :
    NC s []
| nc_cons s x t sigma :
    NC s sigma ->
    (forall y, In y (btv s) -> ((y <> x) * (~ In y (ftv t)))) -> (* no capturing *)
    NC s ((x, t) :: sigma).

Lemma nc_lam x A s sigma :
  NC (tmlam x A s) sigma -> NC s sigma.
Admitted.

Lemma nc_app_l s t sigma :
  NC (tmapp s t) sigma -> NC s sigma.
Admitted.

Lemma nc_app_r s t sigma :
  NC (tmapp s t) sigma -> NC t sigma.
Admitted.

(* No free vars are changed *)
Lemma alpha_preserves_nc_ctx s x t t':
   Alpha [] t t' -> NC s ((x, t)::nil) -> NC s ((x, t')::nil).
Admitted.

Lemma step_naive_pererves_nc_ctx s t t1 t2 x :
  step_naive t1 t2 -> NC s ((x, t1)::nil) -> NC t ((x, t2)::nil).
Admitted.

Lemma gu_app_l s t :
  GU (tmapp s t) -> GU s.
Admitted.

Lemma gu_app_r s t :
  GU (tmapp s t) -> GU t.
Admitted.

Lemma gu_lam x A s :
  GU (tmlam x A s) -> GU s.
  Admitted.

Lemma gu_applam_to_nc s t x A :
  GU (tmapp (tmlam x A s) t) -> NC s [(x, t)].
Admitted.

Lemma nc_ftv_env s sigma :
  NC s sigma -> forall x, In x (btv s) -> ~ In x (ftv_keys_env sigma).
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

Opaque to_GU'.


Create HintDb gu_nc_db.
Hint Resolve gu_app_r : gu_nc_db.
Hint Resolve gu_app_l : gu_nc_db.
Hint Resolve gu_lam : gu_nc_db.
Hint Resolve nc_app_r : gu_nc_db.
Hint Resolve nc_app_l : gu_nc_db.
Hint Resolve nc_lam : gu_nc_db.
Hint Resolve gu_applam_to_nc : gu_nc_db.
Hint Resolve nc_ftv_env : gu_nc_db.


Fixpoint btv_env (sigma : list (string * term)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => (btv t) ++ (btv_env sigma')
  end.

(* Two properties: stopping clash between sigma and s:
  forall x binder in sigma, we rename it in t, hence we need to add that name to R.
  Hence it cannot be free in s, otherwise we no longer have R ⊢ s ~ s.
  We use tv instead of ftv because that decomposes over lam, while we still allow identity substitutions

  Second property: when x is a btv in sigma, then it is not an ftv in sigma.
    e.g. if x is a binder, then we need to rename that in t.
      so then we dont want that same x to also occur free (or as key) in sigma, because then we no longer have
      R ⊢ sigma ~ sigma

    Since identity substitutions have no binders, this still allows for identity substitutions.
    In the lam case we extend sigma with (X, t').
      - X: X was a binder in s, hence a tv in s. So it was not in btv_env_sigma by first condition
      - t': we have control over binders in t', so that is no problem. But for all other binders already in sigma,
            we also need that they don't clash with ftvs in t'. But this is exactly what we are renaming in t':
              those ftv in t' that are binders in sigma! 

    This argument is tooooo subtle, need to formalise.
    What about ftv in t that are also ftv in s? they are not renamed and thus in t'. Can they be btv in sigma? No by the first argument

*)
Definition Uhm sigma s := ((forall x, In x (btv_env sigma) -> ~ In x (tv s)) 
  * (forall x, In x (btv_env sigma) -> ~ In x (ftv_keys_env sigma))
  * (forall x, In x (btv s) -> ~ In x (ftv_keys_env sigma)))%type.

(* We need a legal ren swap because the new binders get in front of the (x, y) in the inductive step of the lambda*)
Lemma alpha_rename_binder_stronger x y s t t' : forall Rt s' Rs,
  Alpha Rs s s' ->
  Alpha Rt t t' ->
  LegalRenSwap ((x, y)::Rt) Rs -> 
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
      apply lrs_sym in H1.
      apply (alpha_swap H1) in H.
      inversion H; subst.
      inversion H9; subst.
      contradiction H4; auto.
      contradiction H10; auto.
    + exfalso.
      apply lrs_sym in H1.
      apply (alpha_swap H1) in H.
      inversion H; subst.
      inversion H9; subst.
      contradiction H4; auto.
      contradiction H13; auto.
    + eapply @alpha_swap with (ren' := ((x, y)::Rt)) in H.
      inversion H; subst.
      inversion H10; subst; try contradiction.
      apply alpha_var.
      assumption.
      apply lrs_sym. auto.
  - constructor.
    eapply IHs; eauto...
    + eapply alpha_extend_vacuous_ftv.
      * apply nc_ftv_env with (x := s) in H2.
        simpl in H2.
        intuition. apply btv_lam.
      * apply nc_ftv_env with (x := y0) in H3.
        simpl in H3.
        intuition. apply btv_lam.
      * assumption.
    + eapply @lrs_trans with (ren2 := ((s, y0)::(x, y)::Rt)).
      * constructor. 
        -- apply nc_ftv_env with (x := s) in H2.
           simpl in H2. intuition. apply btv_lam.
        -- apply nc_ftv_env with (x := y0) in H3.
           simpl in H3. intuition. apply btv_lam.
        -- apply legalRenSwap_id.
      * constructor. assumption.
  - constructor; eauto with gu_nc_db.
Qed.

Lemma step_naive_preserves_alpha2 s t s' R:
  GU s -> GU s' -> Alpha R s s' -> step_naive s t -> {t' & step_naive s' t' * Alpha R t t'}%type.
Proof.
  intros.
  generalize dependent R.
  generalize dependent s'.
  induction H2; subst; intros.
  - inversion H1; subst. inversion H5; subst.
    exists (sub y t2 s0).
    split.
    + constructor.
    + eapply alpha_rename_binder_stronger; eauto with gu_nc_db.
      constructor. apply legalRenSwap_id.
  - inversion H1; subst.
    specialize (IHstep_naive (gu_app_l H) s3 (gu_app_l H0) R H6) as [t' [Hstep_t' HR_t'] ].
    exists (tmapp t' t2).
    split; constructor; auto.
  - inversion H1; subst.
    specialize (IHstep_naive (gu_app_r H) t3 (gu_app_r H0) R H8) as [t' [Hstep_t' HR_t'] ].
    exists (tmapp s2 t').
    split; constructor; auto.
  - inv H1.
    specialize (IHstep_naive (gu_lam H) s3 (gu_lam H0) ((x, y)::R) H8) as [t' [Hstep_t' HR_t'] ].
    exists (tmlam y A t').
    split; constructor; auto.
Qed.

(* Examples
λ x. x is GU_vars
λ x. y is GU_vars
λ x. λ y. x is GU_vars

(λ x. x) y is GU_vars
(λ x. x) x is not GU_vars (* free var is equal to a bound var*)
(λ y. x) x is GU_vars (* all vars with the same name refer to the same term*)
*)

(* If a term has globally unique binders, then it has unique binders*)

Inductive step_gu_naive : term -> term -> Set :=
| step_gu_naive_intro s s' t : 
    Alpha [] s s' ->
    GU s' ->
    step_naive s' t ->
    step_gu_naive s t.
(*     
    Alpha [] t' t ->
    GU_vars t ->
    step_gu_naive s t. *)

(* used to be prop (TODO: Defined also in SN_STCL_named )*)
Inductive sn {e : term -> term -> Set } x : Set :=
| SNI : (forall y, e x y -> sn y) -> sn x.

Notation SN_na := (@sn step_gu_naive).

Lemma step_gu_naive_preserves_alpha {s} {s'} {t} R :
  Alpha R s t -> step_gu_naive s s' -> {t' & prod (step_gu_naive t t') (Alpha R s' t')}.
Proof.
  intros.
  inversion H0; subst.
  assert ({t' & step_naive (to_GU t) t' * Alpha R s' t'}%type).
  {
    eapply step_naive_preserves_alpha2; eauto.
    + apply to_GU__GU.
    + eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R); eauto with α_eq_db.
      * eapply id_left_trans.
      * eapply alpha_extend_ids.
        eapply ctx_id_left_is_id.
        eapply @alpha_sym. constructor. exact H1.
      * eapply @alpha_trans with (ren := R) (ren' := ctx_id_right R).
        -- eapply id_right_trans.
        -- eauto.
        -- eapply alpha_extend_ids.
           eapply ctx_id_right_is_id.
           eapply to_GU__alpha.
  }
  destruct H4 as [t' [Hstep_t' HR_t'] ].
  exists t'.
  split.
  - apply step_gu_naive_intro with (s' := (to_GU t)); eauto.
    + apply to_GU__alpha.
    + apply to_GU__GU.
  - auto.
Qed.

Theorem α_preserves_SN_R s s' R :
  Alpha R s s' -> SN_na s -> SN_na s'.
Proof.
  intros Hα Hsn.
  generalize dependent s'.
  generalize dependent R.
  induction Hsn. intros R s' Hα.
  apply SNI.
  intros y1 Hstep.
  assert ({y1_α & prod (step_gu_naive x y1_α) (sym_alpha_ctx R ⊢ y1 ~ y1_α)}) as [y1_α [Hstep' Hα'] ].
  {
    eapply step_gu_naive_preserves_alpha; auto.
    - eauto with α_eq_db.
    - exact Hstep.
  }
  eapply H; eauto with α_eq_db.
Qed.

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
  (forall x y, step_gu_naive x y -> {y_h & prod (step_gu_naive (h x) y_h) (nil ⊢ y_h ~ (h y))}) -> @sn step_gu_naive v -> nil ⊢ v ~ h x -> @sn step_gu_naive x.
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
  assert ({y_h' & prod (step_gu_naive x y_h') (nil ⊢ y_h' ~ h y)}).
  {
    destruct C as [yh [ehy yh_alpha] ].
    eapply alpha_sym in eqn; [|apply alpha_sym_nil].
    apply (step_gu_naive_preserves_alpha eqn) in ehy.
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
  (forall x y, step_gu_naive x y -> {y_h & prod (step_gu_naive (h x) y_h) (nil ⊢ y_h ~ (h y))}) -> @sn step_gu_naive (h x) -> @sn step_gu_naive x.
Proof.
  intros A B.
  apply sn_preimage_α' with (v := h x) (h := h); eauto.
  apply alpha_refl. apply alpha_refl_nil.
Qed.

(* We need alpha here because global unique can create different terms depending on input:
  global unique does not compose
  suppose there is a free var in s2, then that must be renamed when doing step_gu_naive (tmapp s1 s2)
  while that is not the case in step_gu_naive s1 t1 (there s2 does not need to be taken into account)
  *)
Lemma step_gu_naive_app_l s1 s2 t1 :
  step_gu_naive s1 t1 -> 
  {t1' & Alpha [] t1 t1' * {s2' & Alpha [] s2 s2' * step_gu_naive (tmapp s1 s2) (tmapp t1' s2')}%type }%type.
Proof.
  intros.
  assert ({s1' & { s2' & Alpha [] (tmapp s1 s2) (tmapp s1' s2') * GU (tmapp s1' s2')}}%type).
  {
    (* just renaming binders *)
    admit.
  }
  destruct H0 as [s1' [s2' [Ha_app H_gu] ] ].
  (* I think we then need a step_gu_naive_alpha*)
  assert (Alpha [] s1 s1') by now inv Ha_app.
  assert (Alpha [] s2 s2') by now inv Ha_app.
  apply (step_gu_naive_preserves_alpha H0) in H.
  destruct H as [t' [Hstep_s1' Ha_t1] ].
  inv Hstep_s1'.
  assert (Alpha [] s1 s').
  {
    eapply alpha_trans; eauto. constructor.
  }
  assert (Alpha [] (tmapp s1 s2) (tmapp s' s2')).
  {
    constructor; eauto.
  }
  clear Ha_app.

  (* tbh, i don't understand the flow of this, but it's all just renaming binders ;)*)

  exists t'.
  split; auto.
  assert ({s2'' & GU (tmapp s' s2'') * Alpha [] s2 s2''}%type) by admit. (* just renaming binders*)
  destruct H6 as [s2'' [Hgu_app Ha_s2'] ].
  exists s2''.
  split; auto.
  clear H5.
  econstructor; eauto.
  - constructor; eauto.
  - apply step_appL. auto.
Admitted.

Lemma sn_closedL t s : SN_na (tmapp s t) -> SN_na s.
Proof.
  apply: (sn_preimage_α (h := tmapp^~t)) => x y.
  intros.
  apply (step_gu_naive_app_l t) in H.
  destruct H as [t1' [Ha_t1' [s2' [Ha_t Hstep] ] ] ].
  exists (tmapp t1' s2').
  intuition.
  constructor; eapply alpha_sym; intuition; constructor.
Qed.

Lemma subs_vac_var sigma x :
  ~ In x (map fst sigma) ->
  psubs sigma (tmvar x) = (tmvar x).
Proof.
  intros.
  induction sigma.
  - reflexivity.
  - admit.
Admitted.

(* May also work on sequential substiutions with additional assumptions.
  For now only needed for parallel substitutions
*)
Lemma subs_preserves_alpha_σ_R s : forall R s' sigma sigma',
  NC s sigma ->
  NC s' sigma' ->
  Alpha R s s' ->
  αCtxSub R sigma sigma' ->
  Alpha R (psubs sigma s) (psubs sigma' s').
Proof with eauto with gu_nc_db.
  induction s; intros; inv H1; simpl.
  - destruct (lookup s sigma) eqn:lookup_x_sigma.
    + destruct (alpha_ctx_right_ex H2 H5 lookup_x_sigma) as [t' [Hlookupy_sigma' Ht'_a] ].
      now rewrite Hlookupy_sigma'.
    + rewrite (alpha_ctx_right_nex H2 H5 lookup_x_sigma).
      constructor. assumption.
  - constructor.
    eapply IHs...
    * eapply alpha_ctx_ren_extend_fresh_ftv; auto;
      eapply nc_ftv_env; eauto; apply btv_lam.
  - constructor...
Qed.

Definition subs' sigma s := subs sigma (to_GU s). (* something like that*)




(* I devised this to make soundness var case easier, but is not getting easier
  so maybe I try to switch to paralell substs anyway.
*)
Inductive ParSeq : list (string * term) -> Set :=
| ParSeq_nil : ParSeq []
| ParSeq_cons x t sigma :
    ParSeq sigma -> 
    (* ~ In x (List.concat (map ftv (map snd sigma))) ->  *)
    ~ In x (ftv_keys_env sigma) -> (* UPDATE Feb 27: we cannot have that x is a key in sigma either
      look e.g. at (x, a)::(x, b). As a sequential sub applied to tmvar x, we get b.
                                    As a parallel, we get a.
    *)
    ParSeq ((x, t)::sigma).
(* This says that one subsitutions does not have effect on the next one
  In other word, no substiutions chains, where x -> t, and then t -> y, etc.

  This also means that if we define lookup as right oriented, that
    lookup_left x sigma = Some T   -> subs sigma (tmvar x) = T
*)

(* Say (x, t)::sig2, and sigma =sig1++sig2
  Say y in ftv t. Then we have a problem if y in lhs sig1.
  But, this cannot happen by blabla.

  Also, we will use right-biased lookup.

  TODO: Do we need to enforce that we cannot have twice the same key? 
  For now: righthanded lookup will do the job
*)
Lemma psubs_to_subs {s sigma} :
  ParSeq sigma -> subs sigma s = psubs sigma s.
Admitted.

Lemma single_parseq x t : ParSeq [(x, t)].
Admitted.

Lemma sub_vacuous x t s :
  ~ In x (ftv s) -> NC s ((x, t)::nil) -> sub x t s = s.
Proof.
  intros.
  induction s; simpl; auto.
  - destr_eqb_eq x s; auto. unfold ftv in H. contradiction H. apply in_eq.
  - f_equal. 
    assert (s <> x).
    {
      apply nc_ftv_env with (x := s) in H0. 
      simpl in H0.
      intuition.
      apply btv_lam.

    }
    apply ftv_lam_negative in H.
    apply IHs. intuition.
    eapply nc_lam; eauto. auto.
  - f_equal.
    + eapply IHs1; eauto.
      eapply not_ftv_app_not_left. eauto. eapply nc_app_l; eauto.
    + eapply IHs2; eauto. 
      eapply not_ftv_app_not_right. eauto. eapply nc_app_r; eauto.
Qed.

Lemma ftv_keys_env__no_keys sigma x :
  ~ In x (ftv_keys_env sigma) -> ~ In x (map fst sigma).
Admitted.

Lemma ftv_keys_env__no_values sigma x :
  ~ In x (ftv_keys_env sigma) -> (forall val, In val (map snd sigma) -> ~ In x (ftv val)).
Admitted.

Lemma ftv_keys_env_helper sigma x :
  ~ In x (map fst sigma) -> (forall ftvs, In ftvs (map snd sigma) -> ~ In x (ftv ftvs)) 
    -> ~ In x (ftv_keys_env sigma).
Admitted.

(* substitutions do not introduce new free variables 
*)
Lemma psubs_no_ftv x sigma y:
  ~ In x (ftv_keys_env sigma) -> x <> y -> ~ In x (ftv (psubs sigma (tmvar y))).
Proof.
  intros.
  unfold psubs.
  destruct (lookup y sigma) eqn:lookup_y_sigma.
  - eapply ftv_keys_env__no_values in H; eauto.
    apply lookup_In in lookup_y_sigma.
    apply in_map_iff. exists (y, t). simpl. auto.
  - simpl. intuition.
Qed.



(* I want to be in a position where the binders are chosen thus that I can do substitueT
  without checking if we are tyring to substitute a binder:
    i.e. no checks in substituteT 
    Then we ahve the property:
    subsT x t (tmlam y T s) = tmlam y T (subsT x t s) even if x = y (because that cannot happen anymore)
      Then also NC can go into the lambda
    this can be put into the NC property?
    *)
  (* Maybe we can leave out the R by switching to a renaming approach? *)

(* TODO: These sigma's can be single substitutions I think!
  - Used in step_subst, there it can be single substs
    - Used in beta_expansion: single substs *)
Lemma commute_sub_naive R x s t (sigma sigma' : list (string * term)) xtsAlpha:
  Alpha R (sub x t s) xtsAlpha ->
  αCtxSub R sigma sigma' -> (* TODO: Vars in R not in sigma?*)

  (* these two just say: x not in key or ftv sigma*)
  ~ In x (map fst sigma) ->
  (forall ftvs, In ftvs (map snd sigma) -> ~ In x (ftv ftvs)) -> 
  NC xtsAlpha sigma' ->
  NC s [(x, t)] ->
  NC s sigma ->
  NC t sigma ->
  NC (psubs sigma s) [(x, psubs sigma t)] ->
  (* s.t. substituteTs sigma xtsAlpha does not capture 
    e.g. suppose sigma:= [y := x]
    and xtsAlpha = λx. y.
    then substituting would capture.
    But we can always choose an alpha equivalent xtsAlpha with 
    different binder names not occuring in the rhs of sigma
  *)
  R ⊢ (sub x (psubs sigma t) (psubs sigma s))
      ~ (psubs sigma' xtsAlpha).
Proof with eauto with gu_nc_db.
  intros.
  generalize dependent xtsAlpha.
  generalize dependent R.
  induction s; intros.
  - (* We need to have that x does not occur in lhs or rhs of sigma! We have control over x
    when calling this function, so we should be good.*)
    destr_eqb_eq x s.
    + simpl in H. rewrite String.eqb_refl in H.
      destruct (in_dec String.string_dec s (map fst sigma)).
      * contradiction.
      * assert (psubs sigma (tmvar s) = tmvar s) by now apply subs_vac_var. (* DONE: s not in sigma*)
        rewrite H8.
        simpl.
        rewrite String.eqb_refl.
        eapply subs_preserves_alpha_σ_R; eauto.
    + simpl in H. 
      rewrite <- String.eqb_neq in H8.
      rewrite H8 in H.
      inversion H; subst.
      destruct (in_dec String.string_dec s (map fst sigma)).
      (* 
        by s in keys, ther emust be a value. Hmm. But these are sequential substs...
      *)
      * rewrite sub_vacuous; auto.
        {
          eapply subs_preserves_alpha_σ_R; eauto.
        }
        apply psubs_no_ftv.
        -- apply ftv_keys_env_helper; auto.
        -- apply String.eqb_neq. assumption.
        

      * assert (psubs sigma (tmvar s) = tmvar s) by now apply subs_vac_var. (* DONE : s not in fst sigma *)
        rewrite H9.
        unfold sub.
        rewrite H8.
        rewrite <- H9.
        eapply subs_preserves_alpha_σ_R; eauto.

  - inversion H; subst.
    autorewrite with subs_db in *.
    constructor.
    eapply IHs; try eapply nc_lam; eauto.
    apply alpha_ctx_ren_extend_fresh_ftv; eauto.
    + eapply nc_ftv_env in H5; eauto. apply btv_lam.
    + eapply nc_ftv_env in H3; eauto. apply btv_lam.
  - simpl in H.
    inversion H; subst.
    autorewrite with subs_db in *.
    constructor. fold sub.
    + eapply IHs1...
    + eapply IHs2...
Qed.

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

(* TODO: probably we don't need this and can do inversion once we haqve defined to_GU_app? *)
Lemma to_GU_app_unfold s t st :
  st = to_GU (tmapp s t) -> {s' & { t' & (st = tmapp s' t') * Alpha [] s s' * Alpha [] t t'} }%type.
Proof.
Admitted.

Definition to_GU'' (X : string) (s : term) := s.

Opaque to_GU''.

Lemma to_GU''__alpha X s : Alpha [] s (to_GU'' X s).
Proof.
Admitted.

Lemma to_GU''__GU X s : GU (to_GU'' X s).
Admitted.

Lemma to_GU''__GU_lam X A s : GU (tmlam X A (to_GU'' X s)).
Admitted.


Lemma step_subst_single R {x p s t t' } :
  step_naive s t -> 
  GU s ->  (*  We could return them, but we don't want to. Current idea: have GU in NC *)
  NC s [(x, p)] -> (* no free vars in sigma are binders in s'*)
  Alpha R t t' -> 
  αCtxSub R [(x, p)] [(x, p)] -> 
  (* GU t' -> *)
  NC t' [(x, p)] ->
  {aT : term & 
  (step_gu_naive (subs ((x, p)::nil) s) aT) * (Alpha R aT (subs ((x, p)::nil) t'))}%type.
Proof with eauto with sconstr2_db.
  intros. rename H into Hstep. generalize dependent t'. generalize dependent R. induction Hstep; intros.
  - 
    (* The difficult case. The whole reason we need to do global uniqueness every step
      *)
      
      autorewrite with subs_db. 
      remember (sconstr1 x x0 p s t) as sconstr1_.
      destruct sconstr1_ as [sub_s sub_t].

      exists (sub x0 sub_t sub_s).
      split.
      + eapply step_gu_naive_intro with (s' := (tmapp (tmlam x0 A sub_s) sub_t)).
        * constructor. 
          -- constructor. eapply alpha_extend_ids. constructor. constructor. eapply @alpha_sym; eauto. constructor.
             eapply sconstr1_alpha_s. eauto.
          -- eapply @alpha_sym. constructor. eauto. eapply sconstr1_alpha_t. eauto.
        * eapply sconstr1_gu. eauto.
        * apply step_beta.
      + (* Invert some stuff to end up with a single sub *)
        remember (sconstr2 x0 t x p s ) as sconstr2_.
        destruct sconstr2_ as [ [s' t'0] p'].

        eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R) (t := sub x0 (subs ((x, p')::nil) t'0) (subs ((x, p')::nil) s')).
        * eapply id_left_trans.
        * eapply alpha_extend_ids.
          eapply ctx_id_left_is_id.
          repeat rewrite <- single_subs_is_sub.
          repeat rewrite psubs_to_subs; try apply single_parseq.
          eapply subs_preserves_alpha_σ_R with (R := nil).
          -- eapply gu_applam_to_nc. eapply sconstr1_gu. eauto.
          -- eapply sconstr2_nc_sub; eauto.
          -- rewrite <- psubs_to_subs; [|apply single_parseq].
             eapply @alpha_trans. constructor. 
             ++ eapply sconstr1_alpha_s. eauto.
             ++ repeat rewrite psubs_to_subs; try apply single_parseq.
                eapply subs_preserves_alpha_σ_R.
                ** exact (nc_lam (nc_app_l H1)).
                ** eapply sconstr2_nc_s; eauto.
                ** eapply sconstr2_alpha_s; eauto.
                ** constructor. constructor. constructor.
                   eapply sconstr2_alpha_p; eauto.
          -- constructor. constructor. constructor.
             eapply @alpha_trans. constructor.
             ++ eapply sconstr1_alpha_t. eauto.
             ++ repeat rewrite psubs_to_subs; try apply single_parseq.
                eapply subs_preserves_alpha_σ_R.
                ** exact (nc_app_r H1).
                ** eapply sconstr2_nc_t; eauto.
                ** eapply sconstr2_alpha_t; eauto.
                ** constructor. constructor. constructor.
                   eapply sconstr2_alpha_p; eauto.
        * 
        repeat rewrite psubs_to_subs; try apply single_parseq.
        {
          eapply commute_sub_naive; eauto.
          * eapply @alpha_trans with (ren := ctx_id_left R) (ren' := R) (t := sub x0 t s).
            - eapply id_left_trans.
            - eapply alpha_extend_ids.
              eapply ctx_id_left_is_id.
              repeat rewrite <- single_subs_is_sub.
              repeat rewrite psubs_to_subs; try apply single_parseq.
              eapply subs_preserves_alpha_σ_R with (R := nil).
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
    
    
    specialize (IHHstep (gu_app_l H0) (nc_app_l H1) R H3 s3 H7 (nc_app_l H4)) as [sigS1 [HstepS1 HalphaS1] ].
    autorewrite with subs_db.

    inv HstepS1.

    remember (to_GU (tmapp s' (subs ((x, p)::nil) t))) as st_gu.
    
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
    destruct H8 as [s''step [Halpha_s'' Hstep_s'' ] ].

    exists (tmapp s''step sigtalpha).
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
      * constructor. eauto. 
        repeat rewrite psubs_to_subs; try apply single_parseq.
        eapply subs_preserves_alpha_σ_R; eauto.
        -- exact (nc_app_r H1).
        -- exact (nc_app_r H4).
  - (* analogous*) admit.
  - inversion H2; subst.
    autorewrite with subs_db.
    specialize (IHHstep (gu_lam H0)).

    assert (HctxSub: αCtxSub ((x0, y)::R) ((x, p)::nil) ((x, p)::nil)).
    {
      apply alpha_ctx_ren_extend_fresh_ftv.
      - apply nc_ftv_env with (x := x0) in H1. auto. simpl. auto.
      - apply nc_ftv_env with (x := y) in H4. auto. simpl. auto.
      - assumption.
    }

    specialize (IHHstep (nc_lam H1) ((x0, y)::R) HctxSub s3 H9 (nc_lam H4)).
    destruct IHHstep as [subSigmaS2 [Hsteps1 Halpha] ].

    inversion Hsteps1; subst.

    (* Same term, but rename (possibly occuring) x binders to something else, 
        so that we get GU with the wrapping tmlam x still
      This should be seen as a composability argument. GU composes up to alpha
    *)
    remember (to_GU'' x0 s') as s''.

    (* alpha preserves step_naive, so that we can use this new s'' from above*)
    assert ({s''step & step_naive s'' s''step * Alpha [] subSigmaS2 s''step }%type).
    {
      eapply step_naive_preserves_alpha2 with (s := s'); eauto.
      - eapply gu_lam; eauto.
        subst.
        eapply to_GU''__GU_lam.
      - subst.
        eapply to_GU''__alpha.
    }
    destruct H7 as [s''step [Halpha_s'' Hstep_s'' ] ].
    exists (tmlam x0 A s''step).
    split.
    + apply step_gu_naive_intro with (s' := tmlam x0 A s''); auto. 
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
Admitted.

Create HintDb to_GU'_db.
Hint Resolve to_GU'__alpha to_GU'__GU to_GU'__NC : to_GU'_db.

Lemma sn_subst X T s : NC s ((X, T)::nil) -> SN_na (sub X T s) -> SN_na s.
Proof with eauto with to_GU'_db.
  intros nc.
  apply (sn_preimage_α (h := fun s => sub X T (to_GU' X T s))) => x y. 
  intros.
  eapply (@step_gu_naive_preserves_alpha) with (R := nil) (t := (to_GU' X T x)) in H...
  destruct H as [t' [Hstep H_a] ].
  (* to_GU' is created such that we have GU s and NC s ((X, T))*)
  repeat rewrite <- single_subs_is_sub.
  inversion Hstep; subst.
  assert (GU (to_GU' X T x))...
  eapply step_naive_preserves_alpha2 with (R := nil) (t:= t') (s := s') in H2; auto with α_eq_db.
  {
    destruct H2 as [t'' [Hstep_t'' Ha_t''] ].
    eapply @step_subst_single with (s := (to_GU' X T x)) (t := t''); eauto...
    - apply @alpha_trans with (t := y) (ren := nil) (ren' := nil); repeat constructor...
      apply @alpha_trans with (t := t') (ren := nil) (ren' := nil). constructor.
      + eapply @alpha_sym. constructor. exact Ha_t''.
      + eapply @alpha_sym; eauto. constructor.
    - constructor. constructor. constructor. apply alpha_refl. constructor.
  }
  - eapply @alpha_sym. constructor. exact H.
Qed.

Definition cand := term -> Set.

Definition neutral (s : term) : bool :=
  match s with
    | tmlam _ _ _ => false
    | _ => true
  end.

Record reducible (P : cand) : Set := {
  p_sn : forall s, P s -> SN_na s;
  p_cl : forall s t, P s -> step_gu_naive s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step_gu_naive s t -> P t) -> P s
}.

(* Since we are only interested in globally unique alpha terms, we do an exists here.
But we should do a little study if that is necessary.

we want this to hold for [x := t] meaning substituteT:
Lemma beta_expansion A B x s t :p
  SN_na t -> L A ([x := t] s) ->
  L A (tmapp (tmlam x B s) t).

It also has to hold for A := Kind_Base, in which case it is proved by showing SN_na.
We only have that these two terms mean the same thing if we are allowed to forget about capture in the sbustitution
Hence only if t is globally unique with respect to s. We can enforce that by changing the definition of L.

JACCO and WOUTER think it is a bad idea to change the LR and that using L_preserves_alpha will allow us to use original LR.

*)
Fixpoint L (T : type) : cand :=
match T with
  | tp_base => SN_na 
  | tp_arrow A B => fun s => forall t, L A t -> L B (tmapp s t)
end.

Definition set_diff (l1 l2 : list string) : list string :=
  filter (fun x => negb (existsb (String.eqb x) l2)) l1.

Fixpoint fresh18 (l : list string) : string :=
  match l with
    | nil => "fr"
    | x :: xs => x ++ fresh18 xs
  end.

(*
I THINK THIS IS THE SAME PROCEDURE AS WHAT WE NEED IN BETA REDUCTION

The reason why we need to extend R
 We can always find a term that is alpha to another term with arbitrary renaming context
  except that we cannot. Take R = [x, y], t = x y.
  no. But we can find R', s.t. Alpha (R' ++ (x, y)) (x, y) (y, yfr)
  e.g. R' = (y, yfr) and t' = y yfr

  let's say s = x y, then R cannot be [x, y], because then s' cannot exist
  let's say s = y adn R = [x, y].  then also not possible to have found an s'


  R' needs exactly to contain on the rhs the ftvs in t that are not in s'
  and on the lhs some random fresh balbla

OK BUT IS THIS ACTUALLY NECESSARY:
  Whenever a ftv occurs in s, it can no longer form a problem.
  So, we could instead of extending R, also diminish R
  Different philosophy: Problem is not t, it is R.
  In the example above for example. We have [x, y] ⊢ s ~ s', hence we know y not in s.
  BUT WE CANNOT REMOVE IT!!! SO THIS IS NO SOLUTION, NVM.
    *)

(*
  We can always find a term that is alpha to another term with arbitrary renaming context
  except that we cannot. Take R = [x, y] [y, z], t = x y z.
  no. But we can find R', s.t. Alpha (R' ++ (x, y)) (x, y) (y, yfr)
  e.g. R' = (y, yfr) and t' = y yfr

  let's say s = x y, then R cannot be [x, y], because then s' cannot exist
  let's say s = y adn R = [x, y].  then also not possible to have found an s' *)

  (* problematic ones are: ftvs in t that are also in rhs of R
    but not if they are also in the lhs of R, or if they are ftv in s. Then never a problem:
    R ⊢ s ~ s' is already proving that that is not a problem.

    We can maybe play it safe. Only problematic ones are ftvs_t - ftvs_s.

    Adding for any of those a translation (even if not necessary) to the end of R, 
    will not have an influence on s.
  *)

  (* We first add identity substs for everything in s, and then that makes sure the fresh ones (second map)
    only renames the problematic ones
  *)

(* This probably works, but I have no clue how to proof things about this. What is the property this gives us?*)
Definition R_extender2 (s s' t : term) : list (string * string) :=
  let ftvs_t := ftv t in
  let ftvs_s' := ftv s' in
  let ftvs_s := ftv s in
  map (fun x => (x, x)) (ftv s) ++
  map (fun x => (x, fresh18 ((ftv s) ++ (ftv s') ++ (ftv t)))) (ftv t).


Lemma R_extender2_Nice R s s' t' :
  Nice (R ++ R_extender2 s s' t') t'.
Proof.
(* for every lhs in R, we have that its rhs is a lhs in R_extender2, and we know Nice (R_extender2 blabla)*)
(* I think that is key *)
Admitted.

Lemma some_constructive_arg2 {R s s'} t :
  Alpha R s s' -> {t' & Alpha (R ++ R_extender2 s s' t) t t' * Alpha (R ++ R_extender2 s s' t) s s'}%type.
Proof.
  intros.
  remember (R_extender2 s s' t) as R'.
  exists (mren (R ++ R') t).
  split.
  - eapply alpha_mren_specal.
    subst.
    eapply R_extender2_Nice.
  - eapply @alpha_extend_vacuous_right; auto.
    + (* by construction *) admit.
    + (* by construction *) admit.
Admitted.

(* We know the result is R ++ R' (i.e. prepended by argument), but that is not so 
    important here in the axiomatization, just that there exists one

  TODO: Can we use one of the other constructions, like the one for type_L?  
  I also feel like we may need conditions here on t?
  *)
Lemma axiomatized_construction {R s s'} t :
  Alpha R s s' -> {t' & { R' & Alpha R' t t' * Alpha R' s s'} }%type.
Admitted.

Lemma α_preserves_L_R A s s' R :
  Alpha R s s' -> L A s -> L A s'.
Proof.
  intros.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent R.
  induction A; intros.
  - simpl. simpl in H0.
    eapply α_preserves_SN_R with (s := s); eauto.
  - simpl in H0.
    simpl.
    intros t' Ht.

    remember (sym_alpha_ctx R) as R'.
    assert (Alpha R' s' s).
    {
      subst.
      eauto with α_eq_db.
    }

    destruct (axiomatized_construction t' H1) as [t [R_ [Ha_t0 Ha_s] ] ].
    
    (* first arg of R_extender needs to live in the same alpha land as the last*)
    eapply (IHA2 (sym_alpha_ctx R_) _ (tmapp s t)).
    + eapply @alpha_sym. eapply sym_alpha_ctx_is_sym.
      constructor; eauto.
    + 
    eapply H0. eapply (IHA1 R_ t t'); eauto with α_eq_db.
Qed.

Lemma reducible_sn : reducible SN_na.
Proof. 
  constructor; eauto using ARS.sn. by move=> s t [f] /f. 
  intros s.  elim: s => //.
Qed.

Global Hint Resolve reducible_sn : core.

Lemma reducible_var P x : reducible P -> P (tmvar x).
Proof. move/p_nc. apply=> // t st.
  inv st. inv H. inv H1.
Qed.

Lemma L_reducible A :
  reducible (L A).
Proof with eauto using step_gu_naive.
  elim: A => /=[|A ih1 B ih2].
  - apply reducible_sn.
  - constructor.
    + move=> s h. apply: (@sn_closedL (tmvar "x")). apply: (p_sn (P := L B))...
      eapply h. eapply reducible_var; eauto.
    + intros. specialize (H t0 H1).
      eapply step_gu_naive_app_l with (s1 := s) (t1 := t) (s2 := t0) in H0. 
      * destruct H0 as [t1' [ Ha_t [s2' [Ha_s2' Hstep] ] ] ].
        eapply p_cl with (s := (tmapp s t0)) in H; auto.
        2: exact Hstep.
        eapply α_preserves_L_R.
        2: exact H.
        constructor; eapply alpha_sym; eauto; constructor.
    + move=> s ns h t la.
      have snt := p_sn ih1 la.
      elim: snt la => {} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      inv H.  inv H1=> //...
      * inv H5. discriminate ns.
      * assert (Hgn: step_gu_naive s s0).
        {
          apply gu_app_l in H0.
          econstructor; eauto.
        }
        specialize (h s0 Hgn).
        eapply α_preserves_L_R with (s' := t2) in la; eauto.
      * assert (step_gu_naive t t0).
        {
          apply gu_app_r in H0.
          econstructor; eauto.    
        }
        specialize (ih3 t0 H).
        apply (p_cl ih1 la) in H.
        specialize (ih3 H).
        eapply α_preserves_L_R; eauto.
        constructor; eauto. eapply alpha_refl. constructor.
Qed.

Corollary L_sn A s : L A s -> SN_na s.
Proof. intros Las. assert (reducible (L A)) by apply (L_reducible A).
   apply (p_sn H). assumption.
Qed.

Corollary L_cl T s t : L T s -> step_gu_naive s t -> L T t.
Proof.
  intros Hstep Hst.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_cl H Hstep); assumption.
Qed.

Corollary L_nc T s :
  neutral s -> (forall t, step_gu_naive s t -> L T t) -> L T s.
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

Inductive star {e : term -> term -> Set } (x : term) : term -> Set :=
| starR : star x x
| starSE y z : star x y -> e y z -> star x z.


(** **** Many-Step Reduction 
TODO: See if we can use the star from autosubst ARS again. (uses Prop instead of Set)
*)
Inductive red_gu_na : term -> term -> Set :=
| red_gu_na_star s t t':
     step_gu_naive s t -> 
     red_gu_na t t' ->
     red_gu_na s t' 
| red_gu_na_nil s :
     red_gu_na s s.


Corollary L_cl_star T s t :
  L T s -> red_gu_na s t -> L T t.
Proof.
  intros Ls red_st. induction red_st.
  - eapply IHred_st. eapply L_cl; eauto.
  - assumption.
Qed.

(* If we have substituteT X U s, we need some assumption that U and s already have unique bindrs*)

Definition EL (Gamma : list (string * type)) 
          (sigma : list (string * term)) : Set :=
  forall x T, lookup x Gamma = Some T ->
    { t & prod (lookup x sigma = Some t) (L T t)}.

(* is true! *)
Lemma extend_EL (Gamma : list (string * type)) (sigma : list (string * term)) x T t :
  EL Gamma sigma -> L T t -> EL ((x, T) :: Gamma) ((x, t) :: sigma).
Proof.
Admitted.

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

(* NOTE: Proof already in alpha_typing*)
Lemma alpha_preserves_typing s t A Gamma :
  Alpha nil s t -> Gamma |-* s : A -> Gamma |-* t : A.
Admitted.

Lemma step_gu_na_lam_fold x A s s' :
  step_gu_naive s s' -> {lams' & step_gu_naive (tmlam x A s) lams' * Alpha [] lams' (tmlam x A s')}%type.
Admitted.
(* suppose x already a btv in s.
  Then step_gu_naive will change binders in (tmlam x A s), say we get (tmlam x A s'')
  with s'' ~ s.
  
  then it steps to (tmlam x A s'''). Hence we get s'' steps to s'''
  But s'' ~ s, so s''' ~ s'.


  So maybe in the statement we can say that the binder stays the same?
*)

Lemma red_gu_na_lam_fold {x A s s'} :
  red_gu_na s s' -> {lams' & red_gu_na (tmlam x A s) lams' * Alpha [] lams' (tmlam x A s')}%type.
Admitted.
(* Will it still work for multi step? yeah why not, let's not think about it lol*)

Lemma red_gu_na_app_fold {s1 s2 t1 t2} :
  red_gu_na s1 s2 -> red_gu_na t1 t2 -> {app & red_gu_na (tmapp s1 t1) app * Alpha [] app (tmapp s2 t2)}%type.
Proof.
  intros.
Admitted.


Lemma red_beta x s t1 t2 : 
  step_gu_naive t1 t2 ->
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
  (red_gu_na (tmlam s t (sub x t1 s0)) a0 *
  (nil ⊢ a0 ~ tmlam s t a))%type}).
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
    autorewrite with subs_db.
    repeat rewrite single_subs_is_sub.
    repeat rewrite single_subs_is_sub in *.
    
    assert ({a : term &
    (red_gu_na
      (tmapp (sub x t1 s1) (sub x t1 s2)) a *
    (nil ⊢ a ~
    tmapp g1 g2))%type}) as [app [Hred Ha] ] by apply (red_gu_na_app_fold Hred_g1 Hred_g2).
    exists app.
    split; auto.
    eapply alpha_trans; eauto with α_eq_db.
Qed.

(* Closure under beta expansion. *)
Lemma beta_expansion' A B x y s s' t :
  Alpha [(y, x)] s' s -> (* this allows us to not have to "rename free vars in t" manually*)
  GU s ->
  NC s [(x, t)] -> (* this really is the right assumption. no free variable in t is a binder in s', because these binders could be added to the environment through beta reduction and then capture*)
  SN_na t -> L A (sub x t s) ->
  L A (tmapp (tmlam y B s') t).
Proof with eauto with α_eq_db gu_nc_db.
  move=> Ha_s' gu nc snt h. have sns := sn_subst nc (L_sn h).
  assert (SN_na s').
  {
    (* eapply alpha_sym in Ha_s'. *)
    eapply α_preserves_SN_R with (s := s)...
  }
  clear sns.
  generalize dependent s.
  generalize dependent t.
  induction H.
  intros t snt s0 Ha Hnc.

  (* Now create IH for other step *)
  revert Hnc.
  revert snt.
  elim=> {}.
  intros.
  rename H0 into H10.

  apply: L_nc => // u st. 
  inversion st; subst. inv H0. inversion H6; subst. 

  inv H2 => //.
  - eapply α_preserves_L_R with (R := (nil)); eauto.
    rewrite <- single_subs_is_sub.
    eapply alpha_rename_binder_stronger...
    + constructor. constructor.
     
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

      eapply step_naive_preserves_alpha2 with (s := s4) (t:=s5) (s' := (to_GU x0)).
      - eauto with gu_nc_db.
      - apply to_GU__GU.
      - eauto with α_eq_db.
      - assumption.
    }
    destruct H2 as [s5' [Hstep_na_s5' Ha_s5'] ].
    assert (Hstep_s5': step_gu_naive x0 s5').
    {
      apply step_gu_naive_intro with (s' := to_GU x0).
      - eapply to_GU__alpha.
      - eapply to_GU__GU.
      - assumption.
    }

    eapply α_preserves_L_R with (s := tmapp (tmlam y B s5') x1) (R := nil)...
    specialize (H s5' Hstep_s5' x1).
    clear Ha_s5'. clear H7. clear st. clear s5.
    inv Hstep_s5'.
    assert (HSN_x1: SN_na x1) by now constructor.

    (* TODO: instead of to_GU, assume gu of s0 here by NC?*)
    assert ({s'_a &  step_naive s0 s'_a * Alpha [(y, x)] s5' s'_a}%type).
    {
      eapply step_naive_preserves_alpha2 with (s := s') (s' := s0) (t := s5')...
      eapply @alpha_trans with (ren := (y, y)::nil) (ren' := (y, x)::nil) (t := x0)...
    }
    destruct H5 as [s'_a [ Hstep_s'_a Ha_s'_a ] ].
    specialize (H HSN_x1 (to_GU' x x1 s'_a)). (* just renaming binders*)
    remember (to_GU' x x1 s'_a) as s'_a1.
    assert (((y, x)::nil) ⊢ s5' ~ s'_a1).
    {
      eapply @alpha_trans with (ren := ((y, x)::nil)) (ren' := ctx_id_right ((y, x)::nil)) (t := s'_a)...
      eapply alpha_extend_ids. constructor. constructor. subst. eapply to_GU'__alpha.
    }

    eapply H; eauto.

    * subst. eapply to_GU'__GU. 
    * subst. eapply to_GU'__NC.
    * 
    assert ({α & (step_gu_naive (sub x x1 s0) α) * (nil ⊢ α ~ sub x x1 s'_a1)}%type) 
      as [alpha [Hred Halpha] ].
      {
        repeat rewrite <- single_subs_is_sub.
        eapply (@step_subst_single)...
        subst. eapply to_GU'__alpha.
        subst. eapply to_GU'__NC.
      }
    eapply α_preserves_L_R with (s := alpha) (R := nil); auto.
    eapply L_cl with (s := (sub x x1 s0)); auto.

  - eapply α_preserves_L_R with (s := (tmapp (tmlam y B x0) t0)) (R := nil)...
    eapply H10.
    + econstructor...
    + assumption.
    + eapply step_naive_pererves_nc_ctx with (s := s0); eauto.
      eapply alpha_preserves_nc_ctx; eauto.
    +  
      assert ({ a & prod 
    ( red_gu_na (sub x x1 s0) a) 
    ( nil ⊢ a ~ sub x t0 s0) }).
      { (* this has a lot of repetition with the above *)
        apply red_beta...
        - econstructor...
        - eapply step_naive_pererves_nc_ctx with (s := s0); eauto.
          eapply alpha_preserves_nc_ctx; eauto.
      }
      destruct H0 as [a [Hred_a Ha_a] ].
      eapply (L_cl_star) in h.
      * eapply α_preserves_L_R with (R := nil); eauto.
      * assumption.
Qed.

Lemma beta_expansion_subst X t sigma s A B :
  NC (subs sigma s) [(X, t)] -> (* so the substitution makes sense after "breaking"  it open*)
  SN_na t -> L A (subs ((X, t)::sigma) s) -> L A (tmapp (subs sigma (tmlam X B s)) t).
Proof.
  intros nc snt H.
  simpl in H.
  autorewrite with subs_db.
  eapply α_preserves_L_R with (R := nil) (s := (tmapp (tmlam X B (to_GU' X t (subs sigma s))) t)).
  - constructor. constructor. apply alpha_extend_ids. constructor. constructor. 
    eapply @alpha_sym. eauto. constructor. apply to_GU'__alpha. eapply alpha_refl. constructor.
  - eapply α_preserves_L_R with (R := nil) (s' := (sub X t (to_GU' X t (subs sigma s)))) in H.
    + 
      eapply beta_expansion' in H; eauto.
      * apply alpha_extend_ids. constructor. constructor. apply alpha_refl. constructor.
      * eapply to_GU'__GU.
      * eapply to_GU'__NC.
    + repeat rewrite <- single_subs_is_psub.
      eapply subs_preserves_alpha_σ_R; auto.
      * eapply to_GU'__NC.
      * eapply to_GU'__alpha.
      * apply alpha_ctx_ren_nil.
Qed.




Lemma Uhm_appl s t sigma :
  Uhm sigma (tmapp s t) -> Uhm sigma s.
Proof.
  intros.
  unfold Uhm in H.
  destruct H as [ [uhm1 uhm2] uhm3].
  unfold Uhm.
  split; [split|]; intros.
  - specialize (uhm1 x H).
    (* (not tv) decomposes *)
    admit.
  - specialize (uhm2 x H). auto.
  - specialize (uhm3 x).
    assert (In x (btv (tmapp s t))) by admit. (* btv composes*)
    specialize (uhm3 H0).
    auto.
Admitted.

Lemma Uhm_appr s t sigma :
  Uhm sigma (tmapp s t) -> Uhm sigma t.
Proof.
Admitted.

Lemma Uhm_lam x A s sigma t :
(* we changed Uhm. Maybe we need more conditions! *)
  (* by GU s we have x not in btv s.*)

  (forall y, In y (btv t) -> ~ In y (tv s)) -> (* uhm1*)
    (forall y, In y (btv t) -> ~ In y (ftv_keys_env sigma)) -> (* uhm2*)
  (forall y, In y (btv s) -> ~ In y (ftv t)) ->  (* uhm3*)


  (* cannot combine uhm3 and uhm1: free vars in t can still be free vars in s*)
  Uhm sigma (tmlam x A s) -> Uhm ((x, t)::sigma) s.
Proof.
  intros.
  unfold Uhm.
  split; [split|]; intros.
      (* ~ In tv decomposes through tmlam.
        And we have control over binder names in t'? Yeah why not. They were not a problem yet before though...
        Where do we need the GU sigma then? I think for the alphaCtxSub sigma sigma: renaming stuff that is binder in sigma is vacuous alpha subst, but if it is also ftv, then no longer. But if it is GU (elementwise for value side), then that canot happen
        That still allows the identity substitutions!
      *)

Admitted.


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
Definition t_constr (t : term) (s : term) (sigma : list (string * term)) (X : string) : prod term (list (string * string)) :=
  (t, (("x","x")::nil)).

Opaque t_constr.

Lemma t_constr__a_t {t t' R s sigma X }:
  (t', R) = t_constr t s sigma X ->
  Alpha R t t'.
Admitted.

Lemma t_constr__a_s {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  Alpha R s s.
Admitted.

Lemma t_constr__a_sigma {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  αCtxSub R sigma sigma.
Admitted.

Lemma t_constr__uhm1 {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv t') -> ~ In x (tv s).
Admitted.
Lemma t_constr__uhm2 {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv t') -> ~ In x (ftv_keys_env sigma).
Admitted.
Lemma t_constr__uhm3 {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv s) -> ~ In x (ftv t').
Admitted.


Lemma t_constr__nc_s {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  NC s ((X, t')::sigma).
Admitted.

Lemma t_constr__nc_subs {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  NC (subs sigma s) ((X, t')::nil).
Proof.
Admitted.


(* The fundamental theorem. *)
Theorem soundness Gamma s A :
  has_type Gamma s A -> 
  GU s -> (* So that we know GU_vars (tmlam x A s) -> ~ In x (btv s), and btv s ∩ ftv s = ∅, important for dealing with vars in `t` that roll out of LR*)
  forall sigma, 
    Uhm sigma s ->
    NC s sigma -> (* so we get "nice" substitutions *)
    ParSeq sigma -> (* So parallel and sequential substitions are identical *)
    EL Gamma sigma -> (* So that terms in a substitution are already L *)
  L A (subs sigma s).
Proof with eauto using L_sn. 
  elim=> {Gamma s A} [Gamma X A ih gu sigma wierd nc blabla HEL |Gamma X A s B _ ih gu sigma wierd nc blabla EL|Gamma s t A B _ ih1 _ ih2 gu sigma wierd nc blabla HEL].
  - rewrite psubs_to_subs; eauto.
    unfold EL in HEL.
    specialize (HEL X A ih).
    destruct HEL as [t [HlookupSigma LAt] ].
    simpl.
    rewrite HlookupSigma.
    assumption.
  - unfold L. fold L.
    intros.

    remember (t_constr t s sigma X) as t'R.
    destruct t'R as [t' R].

    assert (Huhm: Uhm ((X, t')::sigma) s).
    {
      eapply Uhm_lam; eauto.
      - intros. eapply t_constr__uhm1 in Heqt'R; eauto.
      - intros. eapply t_constr__uhm2; eauto. 
      - intros. eapply t_constr__uhm3; eauto. 
    }

    specialize (ih (gu_lam gu) ((X, t')::sigma) Huhm (t_constr__nc_s Heqt'R)).
    assert (Hparseq: ParSeq ((X, t')::sigma)).
    {
      constructor. auto.
      apply nc_ftv_env with (x := X) in nc.
      assumption.
      apply btv_lam.
    }

    specialize (ih Hparseq (extend_EL EL (α_preserves_L_R (t_constr__a_t Heqt'R) H))).
(* **** ih is now fully applied ********************** *)

    eapply beta_expansion_subst in ih; eauto.
    + eapply α_preserves_L_R with (s' := tmapp (subs sigma (tmlam X A s)) t) (R := sym_alpha_ctx R) in ih; eauto. constructor.
      * eapply @alpha_sym with (ren := R). apply sym_alpha_ctx_is_sym.
        repeat rewrite psubs_to_subs; auto.
        eapply subs_preserves_alpha_σ_R; eauto; [|apply (t_constr__a_sigma Heqt'R)].
        constructor. eapply alpha_extend_id''. auto; apply (t_constr__a_s Heqt'R).
      * eapply @alpha_sym; eauto. apply sym_alpha_ctx_is_sym.   
        apply (t_constr__a_t Heqt'R).
    + eapply t_constr__nc_subs; eauto.
    + eapply α_preserves_SN_R; eauto. 
      * eapply t_constr__a_t; eauto. 
      * eapply L_sn; eauto.
  - 
    specialize (ih1 (gu_app_l gu) sigma).

    specialize (ih1 (Uhm_appl wierd) (nc_app_l nc) blabla HEL).
    specialize (ih2 (gu_app_r gu) _ (Uhm_appr wierd) (nc_app_r nc) blabla HEL).
    autorewrite with subs_db.
    unfold L in ih1. fold L in ih1.
    specialize (ih1 (subs sigma t) ih2).
    assumption.
Qed.


(* Identity substitutions: Given a typing context E, give a list of term substitutions matching this E*)
Fixpoint id_subst (E : list (string * type)) : list (string * term) :=
  match E with
  | nil => nil
  | cons (x, A) E' => cons (x, tmvar x) (id_subst E')
  end.

From PlutusCert Require Import alpha_sub.

Lemma id_subst_is_IdSubst E :
  IdSubst (id_subst E).
Proof.
  induction E.
  - constructor.
  - simpl. destruct a. constructor. assumption.
Qed.

Lemma id_subst__id s σ :
  (* NC s σ ->  *)
  IdSubst σ -> 
  subs σ s = s. (* even when this capturs, it doesnt matter, since it captures something and then substiutes it for the same name*)
Proof.
  intros.
  induction s.
  - (* if s in sigma, then it is mapped to s by IdSubst*)
    admit.
  - autorewrite with subs_db.
    f_equal.
    apply IHs.
  - autorewrite with subs_db.
    f_equal; eauto.
Admitted.

(* The identity substitution is in the EL relation *)
Lemma id_subst__EL E :
  EL E (id_subst E).
Proof.
Admitted.

Lemma id_subst__ParSeq :
  forall (σ : list (string * term)), IdSubst σ -> ParSeq σ.
Admitted.

Lemma id_subst__nc_uhm E s :
  NC s (id_subst E) -> Uhm (id_subst E) s.
Admitted.

(* defined for arbitrary substitution, while below we only need it for identity substituiosn
  maybe we can then reuse this in other parts of the code. *)
Definition s_constr (s : term) (sigma : list (string * term)) : term :=
  s.

Opaque s_constr.

(* Only need to rename binders*)
Lemma s_constr__a_s {s s' sigma} :
  s' = s_constr s sigma ->
  Alpha [] s s'.
Admitted.

Lemma s_constr__nc_s {s s' sigma} :
  s' = s_constr s sigma ->
  NC s' sigma.
Admitted.

Lemma s_constr__gu {s s' sigma} :
  s' = s_constr s sigma ->
  GU s'.
Admitted.

(* The fundamental theorem for named variables. *)
Corollary type_L (E : list (string * type)) s T : has_type E s T -> L T (subs (id_subst E) s).
Proof.
  intros Htype.
  assert (HEL: EL E (id_subst E)) by apply id_subst__EL.
  remember (s_constr s (id_subst E)) as s'.
  eapply alpha_preserves_typing with (t := s') in Htype; eauto.
  eapply soundness in Htype; eauto.
  - rewrite id_subst__id in Htype; [|apply id_subst_is_IdSubst]. 
    rewrite id_subst__id; [|apply id_subst_is_IdSubst].
    eapply α_preserves_L_R with (s := s'); eauto.
    eapply alpha_sym. eapply alpha_sym_nil. eapply s_constr__a_s; eauto.
  - eapply s_constr__gu; eauto.
  - apply id_subst__nc_uhm. eapply s_constr__nc_s; eauto.
  - eapply s_constr__nc_s; eauto.
  - apply id_subst__ParSeq. apply id_subst_is_IdSubst.
  - eapply s_constr__a_s; eauto.
Qed.



Theorem SN_naive E s T : has_type E s T -> SN_na s.
  intros.
  eapply type_L in H.
  rewrite id_subst__id in H; [|apply id_subst_is_IdSubst].
  eapply L_sn; eauto.
Qed.