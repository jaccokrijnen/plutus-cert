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

(* todo, current implementation is not correct, there is 
  no relation between binders in s and t. *)
Fixpoint to_GU (s : term) := 
  match s with
  | tmvar x => tmvar x
  | tmlam x A s => tmlam x A (to_GU s)
  | tmapp s t => tmapp (to_GU s) (to_GU t)
  end.

Lemma to_GU__alpha s : Alpha [] s (to_GU s).
Admitted.

Inductive GU : term -> Set :=
| GU_var x : GU (tmvar x)
(* in app, if s and t do not share GU_vars: *)
| GU_app s t : 
    GU s -> 
    GU t -> 
    (* Intersection of bound type variables of s and t is empty *)
    forall (H_btv_btv_empty : forall x, In x (btv t) -> ~ In x (btv s)),
    (* Intersection of bound type variables of s and free type variables of t is empty *)
    forall (H_btv_ftv_empty : forall x, In x (btv s) -> ~ In x (ftv t)),
    (* Intersection of free type variables of s and bound type variables of t is empty *)
    forall (H_ftv_btv_empty : forall x, In x (btv t) -> ~ In x (ftv s)),
    GU (tmapp s t)
| GU_lam x A s : 
    GU s -> 
    ~ In x (btv s) ->
    GU (tmlam x A s).

Lemma to_GU__GU s : GU (to_GU s).
Admitted.

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

Lemma step_gu_naive_preserves_alpha {s} {s'} {t} ren :
  Alpha ren s t -> step_gu_naive s s' -> {t' & prod (step_gu_naive t t') (Alpha ren s' t')}.
Proof.
Admitted.

Theorem α_preserves_SN_R s s' R :
  Alpha R s s' -> SN_na s -> SN_na s'.
Proof.
  intros Hα Hsn.
  generalize dependent s'.
  generalize dependent R.
  induction Hsn. intros R s' Hα.
  apply SNI.
  intros y1 Hstep.
  assert ({y1_α & prod (step_gu_naive x y1_α) (R ⊢ y1 ~ y1_α)}) as [y1_α [Hstep' Hα'] ].
  {
    (* eapply step_gu_naive_preserves_alpha; auto.
    - eapply alpha_sym in Hα. exact Hα. apply alpha_sym_nil.
    - assumption. *)
    admit.
  }
  eapply H.
  - exact Hstep'.
  - eapply @alpha_sym with (ren := R) (ren' := sym_alpha_ctx R). admit.  exact Hα'.
Admitted.

(* TODO: Can probably be simplified.
  Both s and s' are alpha equiv to the same GU s_GU. From this they step to the same thing
*)
Theorem α_preserves_SN s s' :
  Alpha [] s s' -> SN_na s -> SN_na s'.
Proof.
  intros Hα Hsn.
  generalize dependent s'.
  induction Hsn. intros s' Hα.
  apply SNI.
  intros y1 Hstep.
  assert ({y1_α & prod (step_gu_naive x y1_α) (nil ⊢ y1 ~ y1_α)}) as [y1_α [Hstep' Hα'] ].
  {
    eapply step_gu_naive_preserves_alpha; auto.
    - eapply alpha_sym in Hα. exact Hα. apply alpha_sym_nil.
    - assumption.
  }
  eapply H.
  - exact Hstep'.
  - eapply alpha_sym. apply alpha_sym_nil. exact Hα'.
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

Lemma gu_app_l s t :
  GU (tmapp s t) -> GU s.
Admitted.

Lemma gu_app_r s t :
  GU (tmapp s t) -> GU t.
Admitted.

Lemma gu_lam x A s :
  GU (tmlam x A s) -> GU s.
  Admitted.

Lemma assume_first_arg a b :
  (a -> b) -> b.
Proof.
Admitted.


(* I want to be in a position where the binders are chosen thus that I can do substitueT
  without checking if we are tyring to substitute a binder:
    i.e. no checks in substituteT 
    Then we ahve the property:
    subsT x t (tmlam y T s) = tmlam y T (subsT x t s) even if x = y (because that cannot happen anymore)
      Then also NC can go into the lambda
    this can be put into the NC property?
    *)
  (* Maybe we can leave out the R by switching to a renaming approach? *)
Lemma commute_sub_naive R x s t (sigma sigma' : list (string * term)) xtsAlpha:
  Alpha R (sub x t s) xtsAlpha ->
  αCtxSub R sigma sigma' -> (* TODO: Vars in R not in sigma?*)

  (* these two just say: x not in key or ftv sigma*)
  ~ In x (map fst sigma) ->
  (forall ftvs, In ftvs (map snd sigma) -> ~ In x (ftv ftvs)) -> 
  NC xtsAlpha sigma' ->
  NC s [(x, t)] ->
  NC s sigma ->
  NC (subs sigma s) [(x, subs sigma t)] ->
  (* s.t. substituteTs sigma xtsAlpha does not capture 
    e.g. suppose sigma:= [y := x]
    and xtsAlpha = λx. y.
    then substituting would capture.
    But we can always choose an alpha equivalent xtsAlpha with 
    different binder names not occuring in the rhs of sigma
  *)
  R ⊢ (sub x (subs sigma t) (subs sigma s))
      ~ (subs sigma' xtsAlpha).

    (* sub x (subs sigma t) (subs sigma s) ~ subs sigma (sub x t s)
    
    Barendreght variable convention source says:
    - x may not occur as key in sigma.
    - 
    *)
Proof.
  intros.
  generalize dependent xtsAlpha.
  generalize dependent R.
  induction s; intros.
  - (* We need to have that x does not occur in lhs or rhs of sigma! We have control over x
    when calling this function, so we should be good.*)
    destr_eqb_eq x s.
    + simpl in H. rewrite String.eqb_refl in H.
      destruct (in_dec String.string_dec s (map fst sigma)).
      * (* We know x= s not in keys or values of sigma. hence x=s cannot be in map fst sigma *)
        admit.
      * assert (subs sigma (tmvar s) = tmvar s) by admit.
        rewrite H7.
        simpl.
        rewrite String.eqb_refl.
        (* subs preserves alpha? *)
        admit.
    + simpl in H. 
      rewrite <- String.eqb_neq in H7.
      rewrite H7 in H.
      inversion H; subst.
      destruct (in_dec String.string_dec s (map fst sigma)).
      * assert ({T & (In (s, T) sigma) * (subs sigma (tmvar s) = T)}%type) by admit.
        destruct H8 as [T [Hin Hsubs] ].
        rewrite Hsubs.
        (* T is in rhs sigma, hence x cannot be in T *)
        assert (sub x (subs sigma t) T = T) by admit.
        rewrite H8.
        (* alpha preserves blablabla (possibly we can enforce that x, y not in R. ? Should not be necessary, but it can be true if that makes it easier)*)
        admit.
      * assert (subs sigma (tmvar s) = tmvar s) by admit.
        rewrite H8.
        simpl.
        rewrite H7.
        (* s not in sigma, then y not in sigma' by alpha *)



    (* we lookup s in sigma.
      Case (s, T) in sigma:
        Goal: sub x (subs sigma t) T ~ subs sigma xtsAlpha
        We know:    subs sigma (tmvar s) = T.
      
      Case s not in sigma:
        Goal: sub x (subs sigma t) (tmvar s) ~ subs sigma xtsAlpha
    *)
    admit.
  - 
    (* simpl in H. *)
    inversion H; subst.
    autorewrite with subs_db in *.
    (* simpl sub. *)
    constructor.
    eapply IHs; try eapply nc_lam; eauto.
    admit.
  - simpl in H.
    inversion H; subst.
    autorewrite with subs_db in *.
    constructor. fold sub.
    + eapply IHs1; eauto; eapply nc_app_l; eauto.
    + eapply IHs2; eauto; eapply nc_app_r; eauto.
Admitted.

(* SEE ALPHA_SUB.v for proof for substituteT, that is prolly easily ported *)
Lemma substituteT_preserves_alpha_test R U U' T T' X X':
  (forall Y, In Y (btv T) -> ~ In Y (ftv U)) -> (* this is why we can do substituteT without worrying about capture*)
  (* We could prevent this maybe by just renaming to globally unique in every lemma*)
  Alpha R U U' ->
  Alpha R T T' ->
  AlphaVar R X X' ->
  Alpha R (sub X U T) (sub X' U' T').
Proof.
Admitted.

(* TODO: MORE CONDITIONS: no shadowing/capture *)
Lemma subs_preserves_alpha R sigma T T' :
  false -> (* adding this so we don't forget this is a prototype*)
  Alpha R T T' ->
  Alpha R (subs sigma T) (subs sigma T').
Proof.
Admitted.

Lemma subs_preserves_alpha_σ sigma sigma' s :
  NC s sigma ->
  NC s sigma' ->
  αCtxSub [] sigma sigma' ->
  Alpha [] (subs sigma s) (subs sigma' s).
Proof.
  intros.
  induction s.
  - (* s in sigma => s in sigma', and rhs of sigma,sigma' are alpha*) 
    admit.
  - (* NC decomposes, so we can use IHs
      By NC (tmlam s t s0) sigma we can pull subs inwards
    *)
    autorewrite with subs_db.
    constructor.
    (* then some arg that we can remove id renamings*)
Admitted.

(* Problem: this is not true.
  after step_gu_naie, t does not have to be globally unique and hence the substitution will capture
  simplest solution: assume that step_gu_naive does globally uniquing before and after (and implement that later).

  We should have a GU property on sigma, but since sigma is never changed,
  this will not complicate the induction hypothesis or anything, it
  will just restrict the applicability of the lemma, which is fine.
*)
Lemma step_subst_sigma sigma {s t t' } :
  step_naive s t -> 
  GU s ->
  NC s sigma -> (* no free vars in sigma are binders in s'*)
  Alpha [] t t' -> 
  GU t' ->
  NC t' sigma ->
  {aT : term & 
  (step_gu_naive (subs sigma s) aT) * (Alpha [] aT (subs sigma t'))}%type.
Proof.
  intros. rename H0 into Hstep. generalize dependent t'. induction H; intros.
  - (* The difficult case. The whole reason we need to do global uniqueness every step
    *)
    
    autorewrite with subs_db. 
    assert ({
      subSigS & {
        subSigT & 
          Alpha [] subSigS (subs sigma s) *
          Alpha [] subSigT (subs sigma t) *
          GU (tmapp (tmlam x A (subSigS)) subSigT)
        }
      }%type
    ) by admit.
    destruct H as [subSigS [subSigT [HsubSigS ] ] ].
    destruct HsubSigS as [HsubSigSAlpha HsubSigTAlpha].

    exists (sub x subSigT subSigS).
    split.
    + admit.
    + 
    eapply @alpha_trans with (t := sub x (subs sigma t) (subs sigma s)); try constructor.
    eapply substituteT_preserves_alpha_test.
    { (* by gu I think *) admit.  } eauto. eauto. constructor.
    eapply commute_sub_naive; eauto.
    * admit.
    * admit.
    * (* when do we have capture? 
      If substituting sigma into t' would cause capture
      This can only happen if t' has binder y e.g.
      and then sigma contains a y.
      But that cannot happen by no_binders t' sigma
      *)
      admit.
    * (* by GU_Vars *)
      admit.
    * (* by no_binders tmapp (tmlam x A s) t) sigma*)
      admit.
     (* That seems more difficult.
        t has no binders in s or sigma
        sigma has no binders in t or s
        free_vars (subs sigma t) <= free_vars t + free_vars sigma
        we only have capture if there is a binder in subs sigma s that is
        in those free_vars.
        binders (subs sigma s) <= binders s + binders sigma

        if y is a binder in s, then it is not free in t by GU_vars
        if y is a binder in s, then it is not in the free_vars of sigma. by no_binders

        if y is a binder in sigma, then it is not in free_vars sigma (by no shadowing somewhere?)
        if y is a binder in sigma, then it is not in t by no_binders I think
      *)
      
    
     




    (* I think we can make assumptions about GU on sigma or something. Then 
      we rewrite to


      tmapp (tmlam x A (subsTs2 sig s)) (subsTs2 sig t0)
      ALPHA
      tmapp (tmlam x A subAlphaS      ) (subAlphat0)
      ->
      subT x subAlphat0 subAlphaS
      ALPHA
      subT x (subsTs2 sig t0) (subsTs2 sig s)    ~   aT

      Magic: x and sig do not interfere: sig has no x in keys or values, 
      and also sig and (subsTs2 sig t0) do not interfere

      hence:

      subT x t0 (subsTs2 sig s)  ~  subsTs2 sig (subT x t0 s)
      ALPHA
      subTs2 sig t.

      We could choose (tmapp (tmlam x A s) t0) in such a way s.t. no binder occurs in sigma
      However, if sigma contains say a "y".
      And t0 contains a free "y". Then we cannot change that t0 to not have the free "y"
    
    *)
    
  
   (* Assume s and t are globally unique 
    Induction on step_gu_naive.
    Four cases:
    - step_beta: s = tmapp (tmlam x A s1) s2 ->  t_ = subsT x s2 s1, then t = gu t
    *)
    * admit.
    - 

      assert (GU s1) by admit.
      specialize (IHstep_naive H0).
      apply assume_first_arg in IHstep_naive.
      inversion H2; subst.
      specialize (IHstep_naive s3 H8).
      apply assume_first_arg in IHstep_naive.
      apply assume_first_arg in IHstep_naive.
      
      destruct IHstep_naive as [sigS1 [HstepS1 HalphaS1] ]. 
      autorewrite with subs_db.
      assert ({sigS1alpha : term & {sigtalpha : term & 
        (Alpha [] sigS1 sigS1alpha) * 
        (Alpha [] (subs sigma t) sigtalpha) *
        GU (tmapp sigS1alpha sigtalpha)
      } }%type).
      {
        (* This is not hard to see:
          We perform "to_global_unique" on tmapp (sigS1 (substituteTs sigma t))
          This will yield something alpha equiv to it which is GU_Vars and can be decomposed
        
        but how to tell coq?*)
        admit.
      }
      destruct H6 as [sigS1alpha [sigtalpha [ HsigS1alpha ] ] ].
      destruct HsigS1alpha as [HsigS1alpha HsigtAlpha].
      exists (tmapp sigS1alpha sigtalpha).
      (*
        So, is this the case? The alpha one is true by construction.
        for step_gu_naive, we need some unfolding lemmas. The only thing it does is first making stuff
        unique, but keeping alpha equivalence.

        We know that

        substituteTs2 sigma s0 -> sigS1 ~ substituteTs2 sigma s2 ~ sigS1alpha

      Ok. I assume that the other 2 cases are analogous.
      *)
      admit.
    - admit.
    - inversion H; subst.
      inversion H3; subst.
      apply assume_first_arg in IHHstep.
      apply assume_first_arg in IHHstep.
      specialize (IHHstep s4).
      apply assume_first_arg in IHHstep.
      apply assume_first_arg in IHHstep.
      apply assume_first_arg in IHHstep.
      specialize (IHHstep s0).
      apply assume_first_arg in IHHstep.
      autorewrite with subs_db.
      destruct IHHstep as [subSigmaS1_ [Hsteps1 Halpha] ].
      (* we know no x in sigma and no binders x in s1*)
      assert ({subSigmaS1 & 
        Alpha [] subSigmaS1 (subs sigma s1) * 
        GU (tmlam x A subSigmaS1)
      }%type).
      {
        admit.
      }


  
Admitted.

(* We construct s in such a way that
  - Alpha [] to original
  - GU
  - NC with respect to X and T.

  We can achieve this since we only rename binders:
  - We can always generate a alpha GU term by only changing binders
  - We can then again change some binders so that they dont capture ftvs in X or T,
    this preserves GU and Alpha.
*)
Definition to_GU' (X : string) (T : term) (s : term) := s.

Definition sub_gu X T s := sub X T (to_GU' X T s).

Lemma sn_subst X T s : NC s ((X, T)::nil) -> SN_na (sub X T s) -> SN_na s.
Proof.
  intros nc.
  apply: (sn_preimage_α (h := sub_gu X T)) => x y. 
  unfold sub_gu.
  intros.
  assert (H_to_GU'_a: Alpha [] x (to_GU' X T x)).
  {
    (* by construction.*)
    admit.
  }
  apply (step_gu_naive_preserves_alpha H_to_GU'_a) in H.
  destruct H as [t' [Hstep H_a] ].
  (* to_GU' is created such that we have GU s and NC s ((X, T))*)
  repeat rewrite <- single_subs_is_sub.
  eapply step_subst_sigma; eauto.
  - (* by construction *)
    admit.
  - (* by construction *)
    admit.
  - (* t' ~ y,  and y ~ to_GU' X T y   by construction *)
    admit.
  - (* by construction *)
    admit.
  - (* by construction *)
    admit.
Admitted.

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
    intros t Ht.
    assert ({t0 & Alpha R t0 t}) as [t0 Halphat0] by admit.
    specialize (H0 t0).
    specialize (IHA1 (sym_alpha_ctx R) t0 t).
    assert (sym_alpha_ctx R ⊢ t ~ t0) by admit.
    specialize (IHA1 H1 Ht).
    assert (R ⊢ (tmapp s t0) ~ (tmapp s' t)).
    {
      apply alpha_app; assumption.
    }
    
    specialize (IHA2 R (tmapp s' t) (tmapp s t0) H2 (H0 IHA1)).
    assumption.
Admitted.

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
        eapply α_preserves_L.
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
        apply α_preserves_L with (s' := t2) in la; eauto.
      * assert (step_gu_naive t t0).
        {
          apply gu_app_r in H0.
          econstructor; eauto.    
        }
        specialize (ih3 t0 H).
        apply (p_cl ih1 la) in H.
        specialize (ih3 H).
        eapply α_preserves_L; eauto.
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
Definition red_gu_na := @star step_gu_naive.

Corollary L_cl_star T s t :
  L T s -> red_gu_na s t -> L T t.
Proof.
  intros Ls red_st. induction red_st.
  - assumption.
  - apply L_cl with y; assumption.
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

(* NOTE: Proof in alpha_typing*)
Lemma alpha_preserves_typing s t A Gamma :
  Alpha nil s t -> Gamma |-* s : A -> Gamma |-* t : A.
Admitted.


Lemma red_beta_gu_na x s t1 t2 :
  step_gu_naive t1 t2 ->
  { α & prod 
      (red_gu_na (substituteT x t1 s) α)
      (nil ⊢ α ~ (substituteT x t2 s))
  }.
Proof.
  intros Hstep.
  eapply red_beta'; auto; 
    solve [try apply alpha_refl; try apply alphavar_refl; constructor].
Admitted.

(* Closure under beta expansion. *)
Lemma beta_expansion A B x s s' t :
  Alpha [] s' s ->
  NC s' [(x, t)] -> (* this really is the right assumption. no free variable in t is a binder in s', because these binders could be added to the environment through beta reduction and then capture*)
  SN_na t -> L A (sub x t s') -> (* Key: s' is GU now *)
  L A (tmapp (tmlam x B s) t).
Proof with eauto.
  move=> alphass' guvars snt h. have sns := sn_subst (L_sn h).
  assert (SN_na s).
  {
    eapply α_preserves_SN; eauto.
  } 
  clear sns.
  generalize dependent h.
  generalize dependent s'.
  induction H. intros.
  (* generalize dependent s.

  (* TODO: How to get that second IH? *)

  induction sns. intros. *)
  apply: L_nc => // u st. 
  (* assert ({u' & Alpha [] u u' * step_naive (tmapp (tmlam x B s) t) u'}%type) as st' by admit.
  destruct st' as [u' [au' st'] ]. *)
  assert (step_naive (tmapp (tmlam x B s') t) u) as st' by admit.
    
  inv st' => //.
  (* - apply α_preserves_L with (s := sub x t s); auto. eapply alpha_sym. econstructor. auto. *)
  - inv H3.
    assert (Hprr: step_gu_naive x0 s0) by admit.
    specialize (H s0 Hprr).
    assert({s'0_nc & Alpha [] s'0_nc s0 * NC s'0_nc [(x, t)]}%type) by admit.
    destruct H0 as [s'0_nc [Hreds0_nc Hno_caps0] ].
    specialize (H s'0_nc Hreds0_nc Hno_caps0).

    (* inversion au'; subst. inversion H3; subst.  *)
    (* assert (step_gu_naive s s0) by admit. assumes NC also says something about uniqueness in term *)
    apply H => //.
    (* s steps naively to s0. Could make it non-unique, but it could not have caused new binders like x and t*)
    (* assert ({s0' & Alpha [] s0 s0' * NC s0' [(x, t)]}%type) as [s0' [Hreds0' Hno_caps0'] ].
    {
      admit.
    } *)

    assert ({α & (step_gu_naive (sub x t s') α) * (nil ⊢ α ~ sub x t s'0_nc)}%type) 
      as [alpha [Hred Halpha] ].
      {
        eapply (@step_subst_sigma ((x, t)::nil)).
        - apply alpha_refl. constructor.
        - eauto. 
        - admit.
        - assumption.
        - eapply alpha_sym; eauto. constructor.
        - admit.
        - eauto.
      }
    
     
    
    apply (L_cl h) in Hred.
    apply α_preserves_L with (s := alpha); assumption.
  - (* presumably analogous to above? *)
Admitted.

Lemma beta_expansion_subst X t sigma s A B :
  NC (subs sigma s) [(X, t)] -> (* so the substitution makes sense after "breaking"  it open*)
  SN_na t -> L A (subs ((X, t)::sigma) s) -> L A (tmapp (subs sigma (tmlam X B s)) t).
Proof.
  intros nc snt H.
  simpl in H.
  autorewrite with subs_db.
  eapply beta_expansion in H; eauto.
  apply alpha_refl. constructor.
Qed.


(* I devised this to make soundness var case easier, but is not getting easier
  so maybe I try to switch to paralell substs anyway.
*)
Inductive ParSeq : list (string * term) -> Set :=
| ParSeq_nil : ParSeq []
| ParSeq_cons x t sigma :
    ParSeq sigma -> 
    ~ In x (List.concat (map ftv (map snd sigma))) -> 
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



(* The fundamental theorem. *)
Theorem soundness Gamma s A :
  has_type Gamma s A -> 
  GU s -> (* So that we know GU_vars (tmlam x A s) -> ~ In x (btv s), and btv s ∩ ftv s = ∅, important for dealing with vars in `t` that roll out of LR*)
  forall sigma, 
    NC s sigma -> (* so we get "nice" substitutions *)
    ParSeq sigma -> (* So parallel and sequential substitions are identical *)
    EL Gamma sigma -> (* So that terms in a substitution are already L *)
  L A (subs sigma s).
Proof with eauto using L_sn. 
  elim=> {Gamma s A} [Gamma X A ih gu sigma nc blabla HEL |Gamma X A s B _ ih gu sigma nc blabla EL|Gamma s t A B _ ih1 _ ih2 gu sigma nc blabla HEL].
  - rewrite psubs_to_subs; eauto.
    unfold EL in HEL.
    specialize (HEL X A ih).
    destruct HEL as [t [HlookupSigma LAt] ].
    simpl.
    rewrite HlookupSigma.
    assumption.
  - unfold L. fold L.
    intros.

    specialize (ih (gu_lam gu)).

    (* Choose t' so that we do not have capture but can still use IH through L_α*)

      (* We need to transform sigma a little first ALSO to be able to use beta expansion: *)
          (* no ftv in t' (or X) is bound in the result (subs sigma'' s'')
              that is the case if it is not bound in s'' and not in sigma'',
              over which we have control.
              We already altered t' so that no ftv in t' is bound in s!
              By GU_vars (tmlam X A s) we know x not bound in s.
          *)
    assert (H_nicet: {t' & { R & { sigma' & Alpha R t t' 
          * Alpha R s s 
          * αCtxSub [] sigma sigma'
          * NC (subs sigma' s) ((X, t')::nil)
          * NC s ((X, t')::sigma')}%type }%type }%type).
    {
      (* Alpha R s s says: no element of R occurs in lhs or rhs of s*)
      admit.
    }
    destruct H_nicet as [t' [ R [ sigma' [ [ [ [Ha_t' Ha_s] Hctx ] Hnc_sub ] Hnc_t'] ] ] ].
    specialize (ih ((X, t')::sigma') Hnc_t').

    (* blabla preservet under alpha [] *)
    assert (blablajeej: ParSeq ((X, t')::sigma')) by admit.
    specialize (ih blablajeej).

    assert (L_t': L A t').
    {
      eapply α_preserves_L_R; eauto.
    }
    assert (H_EL_sigma': SN_STLC_named_naive.EL ((X, A)::Gamma) ((X, t')::sigma')).
    {
      (* We only renamed binders in sigma', so should not change a thing?
        We can prevent this by instantiating the IH with sigma, and then doing an alpha argument later
        That has disadvantages too in having to prove some NC things again.
      *)
      admit.
    }
    specialize (ih H_EL_sigma').
(* **** ih is now fully applied ********************** *)

    eapply beta_expansion_subst in ih; eauto. 
      2: { apply L_sn in H. eapply α_preserves_SN_R; eauto. }

    eapply α_preserves_L_R with (s' := tmapp (subs sigma (tmlam X A s)) t) in ih. eauto. constructor.
    2: {eapply @alpha_sym with (ren := R); eauto.
    apply sym_alpha_ctx_is_sym. }

    (* Now, first we prove that it is true without the alpha context*)
    assert (Alpha [] (subs sigma' (tmlam X A s)) (subs sigma (tmlam X A s))).
    {
      eapply subs_preserves_alpha_σ; eauto.
      - (* by NC (tmlam X A s) sigma 
            => X not in ftv sigma
            => X not in ftv sigma'   (alpha [] preserves ftvs)*)
        admit.
      - (* symmetry *) admit.
    }
    (* Then by Alpha R s s and αCtxSym R sigma sigma  and αCtxSym R sigma' sigma'
      we know that the alpha context doesnt do anything and can be removed

      I am not sure how to make that argument precise yet, and how much work it is.
    *)
    admit.

  - specialize (ih1 (gu_app_l gu) _ (nc_app_l nc) blabla HEL).
    specialize (ih2 (gu_app_r gu) _ (nc_app_r nc) blabla HEL).
    autorewrite with subs_db.
    unfold L in ih1. fold L in ih1.
    specialize (ih1 (subs sigma t) ih2).
    assumption.
Admitted.


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
  - admit.
    
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

(* The fundamental theorem for named variables. *)
Corollary type_L (E : list (string * type)) s T : has_type E s T -> L T (subs (id_subst E) s).
Proof.
  intros Htype.
  assert (HEL: EL E (id_subst E)) by apply id_subst__EL.
  assert ({s' & nil ⊢ s ~ s' * GU s' * NC s' (id_subst E)}).
  {
    (* easy, this can be achieved by only renaming some binders in s*)
    admit.
  }
  destruct H as [s' [ [Halpha Hgu] Hnc ] ].
  eapply alpha_preserves_typing with (t := s') in Htype; eauto.
  eapply soundness in Htype; eauto.
  - rewrite id_subst__id in Htype; [|apply id_subst_is_IdSubst]. 
    rewrite id_subst__id; [|apply id_subst_is_IdSubst].
    eapply α_preserves_L with (s := s'); eauto.
    eapply alpha_sym. eapply alpha_sym_nil. assumption.
  - apply id_subst__ParSeq. apply id_subst_is_IdSubst.
Admitted.



Theorem SN_naive E s T : has_type E s T -> SN_na s.
  intros.
  eapply type_L in H.
  rewrite id_subst__id in H; [|apply id_subst_is_IdSubst].
  eapply L_sn; eauto.
Qed.