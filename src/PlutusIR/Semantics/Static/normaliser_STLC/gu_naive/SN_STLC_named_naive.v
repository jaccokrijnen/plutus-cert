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

Create HintDb α_eq_db.
Hint Constructors Alpha : α_eq_db.
Hint Resolve alpha_refl : α_eq_db.
Hint Resolve alpha_sym : α_eq_db.
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

Lemma step_naive_preserves_alpha2 s t s' R:
  GU s -> GU s' -> Alpha R s s' -> step_naive s t -> {t' & step_naive s' t' * Alpha R t t'}%type.
Admitted.


Lemma step_naive_preserves_alpha s t s' t':
  GU s -> GU s' -> Alpha [] s s' -> step_naive s t -> step_naive s' t' -> Alpha [] t t'.
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


(* May need parseq assumption *)
(* SEE ALPHA_SUB.v for proof for substituteT, that is prolly easily ported *)
Lemma subs_preserves_alpha_σ_R R sigma sigma' s s' :
  NC s sigma ->
  NC s' sigma' ->
  Alpha R s s' ->
  αCtxSub R sigma sigma' ->
  Alpha R (subs sigma s) (subs sigma' s').
Proof.
  intros.
  generalize dependent R.
  generalize dependent s'.
  generalize dependent sigma.
  generalize dependent sigma'.
  induction s; intros; inv H1.
  - (* we have sequential substs here. *)
    (* seems doable with inductino over the length of sigma, but maybe we can add the ParSeq 
      Without ParSeq, we find s in sigma, then we find y in the same place. We get 
      subs sigma2 T ~ subs sigma' T' ? By alphaCtxSub R sigma sigma' we have that R ⊢ T ~ T',
      and hence we need to use this lemma with a smaller sigma.

      Maybe we can sneak it into αCtxSub
    *)
    admit.
  - autorewrite with subs_db.
    constructor.
    eapply IHs; eauto.
    * exact (nc_lam H).
    * exact (nc_lam H0).
    * (* NC (tmlam s t s0) sigma => s not free in sigma
         NC (tmlam y t s2) sigma => y not free in sigma'
         Then it is like adding a "vacuous renaming" to the alpha context*)
      admit.
  - autorewrite with subs_db.
    constructor.
    + eapply IHs1; eauto.
      * exact (nc_app_l H).
      * exact (nc_app_l H0).
    + eapply IHs2; eauto.
      * exact (nc_app_r H).
      * exact (nc_app_r H0).
Admitted.

Definition subs' sigma s := subs sigma (to_GU s). (* something like that*)

Lemma subs_vac_var sigma x :
  ~ In x (map fst sigma) ->
  subs sigma (tmvar x) = (tmvar x).
Proof.
  intros.
  induction sigma.
  - reflexivity.
  - admit.
Admitted.

Lemma gu_applam_to_nc s t x A :
  GU (tmapp (tmlam x A s) t) -> NC s [(x, t)].
Admitted.

(* NOT TRUE, BUT THIS MAY HELP A LOT EVERYWHERE AND MAY BE EASY TO ADD*)
Lemma nc_to_gu_axiom s sigma :
  NC s sigma -> GU s.
Proof.
Admitted.

Lemma nc_ftv_env s sigma :
  NC s sigma -> forall x, In x (btv s) -> ~ In x (ftv_keys_env sigma).
Admitted.

Create HintDb gu_nc_db.
Hint Resolve gu_app_r : gu_nc_db.
Hint Resolve gu_app_l : gu_nc_db.
Hint Resolve gu_lam : gu_nc_db.
Hint Resolve nc_app_r : gu_nc_db.
Hint Resolve nc_app_l : gu_nc_db.
Hint Resolve nc_lam : gu_nc_db.
Hint Resolve gu_applam_to_nc : gu_nc_db.
Hint Resolve nc_ftv_env : gu_nc_db.


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
      * assert (subs sigma (tmvar s) = tmvar s) by now apply subs_vac_var. (* DONE: s not in sigma*)
        rewrite H8.
        simpl.
        rewrite String.eqb_refl.
        eapply subs_preserves_alpha_σ_R; eauto.
    + simpl in H. 
      rewrite <- String.eqb_neq in H8.
      rewrite H8 in H.
      inversion H; subst.
      destruct (in_dec String.string_dec s (map fst sigma)).
      (* by s in keys, ther emust be a value. Hmm. But these are sequential substs...

      *)
      * assert (sub x (subs sigma t) (subs sigma (tmvar s)) = subs sigma (tmvar s)). {
          (* by some difficult argument, we know x notin ftv of map snd sigma
            By NC (subs sigma (tmvar s)) [(x, subs sigma t)], x not in btv of subs sigma (tmvar s)
          *)
          admit.
        }
        rewrite H9.
        eapply subs_preserves_alpha_σ_R; eauto.
      * assert (subs sigma (tmvar s) = tmvar s) by now apply subs_vac_var. (* DONE : s not in fst sigma *)
        rewrite H9.
        simpl.
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
Admitted.

(* 
*)
Lemma step_subst_sigma R sigma {s t t' } :
  step_naive s t -> 
  (* GU s -> *)   (* We could return them, but we don't want to. Current idea: have GU in NC *)
  NC s sigma -> (* no free vars in sigma are binders in s'*)
  Alpha R t t' -> 
  αCtxSub R sigma sigma ->
  (* GU t' -> *)
  NC t' sigma ->
  {aT : term & 
  (step_gu_naive (subs sigma s) aT) * (Alpha R aT (subs sigma t'))}%type.
Proof.
  intros. rename H into Hstep. generalize dependent t'. generalize dependent R. induction Hstep; intros.
  - 
    (* The difficult case. The whole reason we need to do global uniqueness every step
      *)
      
      autorewrite with subs_db. 
      assert ({
        sigma' & {
          s' & 
            Alpha [] s s' *
            αCtxSub [] sigma sigma' *
            Alpha [] (subs sigma' s') (subs sigma s) * 
            Alpha [] (subs sigma' t) (subs sigma t) * (* what if x free in t???? it cannot by GU (tmapp (tmlam x A s) t)*)
            GU (tmapp (tmlam x A (subs sigma' s')) (subs sigma' t))
          }
        }%type
      ) by admit.
      destruct H as [sigma' [s' [ [ [ [Ha_s Hctx] Hsubs ] Hsubt ] HGU ] ] ].

      exists (sub x (subs sigma' t) (subs sigma' s')).
      split.
      + eapply step_gu_naive_intro with (s' := (tmapp (tmlam x A (subs sigma' s')) (subs sigma' t))).
        * constructor. 
          -- constructor. (* extend alpha_id trivial*) admit.
          -- eapply @alpha_sym. constructor. eauto.
        * eauto.
        * apply step_beta.
      + 
        eapply commute_sub_naive; eauto.
        * (* by alpha trans and sub_preserves. 
            We need NC s' [(x, t)]  <-- Idk if we have that, but we can add it as a condition on the constructino of s'
          *) admit.
        * (* alpha ctx trans *) admit.
        * (* by nc and alpha preserves ftvs *) admit.
        * (* by nc and alpha preserves ftvs *) admit.
        * (* by nc and gu, can be forced by construction since we already have NC s [(x, t)] (by only changing binders we can get it)
          *)
          admit.
        * (* Can be forced by construction, since we alrady have NC s sigma *)
          admit.
        * (* Can be so constructed, because we already have NC t sigma, actually, we already have it, I think NC is preserved under alpha [] of subs *)
          admit.
        * (* By GU construction, the whole reason we are creating this term *)
          admit.
  - inversion H1; subst.
    
    
    specialize (IHHstep (nc_app_l H0) R H2 s3 H6 (nc_app_l H3)) as [sigS1 [HstepS1 HalphaS1] ].
    autorewrite with subs_db.

    inv HstepS1.

    assert ({sigS1alpha : term & {sigtalpha : term & 
      (Alpha [] s' sigS1alpha) * 
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
    destruct H7 as [sigS1alpha [sigtalpha [ [HsigS1alpha Ha_t] HGU_sigS1alpha ] ] ].

    (* like lam case, we then alpha step *)
    assert ({s''step & Alpha [] sigS1 s''step * step_naive sigS1alpha s''step}%type).
    {
        (* somethign like that, but not exactly, sicne there we need to specify a t'*)
      admit.
    }
    destruct H7 as [s''step [Halpha_s'' Hstep_s'' ] ].

    exists (tmapp s''step sigtalpha).
    split.
    + econstructor; auto.
      * constructor.
        -- eapply @alpha_trans. constructor. eauto. eauto.
        -- eauto.
      * eauto.
      * constructor. eauto.
    + eapply @alpha_trans with (ren := nil) (ren' := R). admit. (* AlphaTrans [] R R forall R*)
      * constructor. eapply alpha_sym. constructor. eauto. eapply alpha_sym. constructor. eauto.
      * constructor. eauto. (* TODO: we need alpha ctx to use subs preserves alpha! *)
        eapply subs_preserves_alpha_σ_R; eauto.
        -- exact (nc_app_r H0).
        -- exact (nc_app_r H3).
  - admit.
  - inv H2.
    autorewrite with subs_db.
    assert (HctxSub: αCtxSub ((x,y)::R) sigma sigma) by admit.
    specialize (IHHstep (gu_lam H0) (nc_lam H1) ((x, y)::R) HctxSub s3 H10 (gu_lam H4) (nc_lam H5)).
    destruct IHHstep as [subSigmaS2 [Hsteps1 Halpha] ].

    inversion Hsteps1; subst.

    (* Same term, but rename (possibly occuring) x binders to something else, so that we get GU with the wrapping tmlam x still
      This should be seen as a composability argument. GU composes up to alpha
    *)
    assert ({s'' & Alpha [] s' s'' * GU (tmlam x A s'')}%type) by admit.
    destruct H7 as [s'' [ Halpha_s' HGU_lam ] ].


    (* alpha preserves step_naive, so that we can use this new s'' from above*)
    assert ({s''step & Alpha [] subSigmaS2 s''step * step_naive s'' s''step}%type).
    {
        eremember (step_naive_preserves_alpha H2 (gu_lam HGU_lam) Halpha_s' H6) as Hstep2.
        (* somethign like that, but not exactly, sicne there we need to specify a t'*)
      admit.
    }
    destruct H7 as [s''step [Halpha_s'' Hstep_s'' ] ].
    exists (tmlam x A s''step).
    split.
    + econstructor; auto. 
      2: exact HGU_lam.
      * constructor. (* trivial alpha trans, followed by identity alpha ctx *) admit.
      * constructor. assumption.
    + constructor.
      eapply @alpha_trans with (ren := nil) (ren' := ((x, y)::R)).
      * (* trans with empty lhs is trivial *) admit.
      * eapply alpha_sym. constructor. eauto.
Admitted.

Lemma step_gu_subst_sigma { sigma s t } :
  step_gu_naive s t -> 
  { s' : term & 
    {t' : term &
    {aT : term & 
    (step_gu_naive (subs sigma s') aT) * (Alpha [] aT (subs sigma t'))
    }
    * Alpha [] t t' * NC t' sigma}
    * Alpha [] s s' * NC s' sigma
  }%type.
Proof.
  intros.
  inversion H; subst.
  assert ({s'_nc & Alpha [] s s'_nc * GU s'_nc * NC s'_nc sigma * 
    {t'_nc & step_naive s'_nc t'_nc * Alpha [] t t'_nc
    * {t'_nc_gu & GU t'_nc_gu & NC t'_nc_gu sigma * Alpha [] t t'_nc_gu}
    }}%type) as [s'_nc [ [ [Halpha_s' HGU_s'] HNC_s'] [t_nc [ [Hstep_t_nc Ha_t_nc] [t'_nc_gu t'_nc_gu_GU [t'_nc_gu_NC t'_nc_gu_A ] ]  ] ]  ]  ] by admit.
  exists s'_nc.
  split; [split|]; eauto.
  - exists t'_nc_gu. split; try split; eauto.
    + eapply step_subst_sigma; eauto.
      * eapply alpha_trans. constructor. eapply alpha_sym. constructor. eauto. eauto.
      * eapply alpha_ctx_ren_nil.
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
  eapply step_subst_sigma with (t := t'); eauto.
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

Definition R_extender (s s' t : term) : list (string * string) :=
  let ftvs_t := ftv t in
  let ftvs_s' := ftv s' in
  let ftvs_s := ftv s in
  (* problematic ones are: ftvs in t that are also in rhs of R
    but not if they are also in the lhs of R, or if they are ftv in s. Then never a problem:
    R ⊢ s ~ s' is already proving that that is not a problem.

    We can maybe play it safe. Only problematic ones are ftvs_t - ftvs_s.

    Adding for any of those a translation (even if not necessary) to the end of R, 
    will not have an influence on s
  *)

  (* We first add identity substs for everything in s, and then that makes sure the fresh ones (second map)
    only renames the problematic ones
  *)
  map (fun x => (x, x)) (ftv s) ++
  map (fun x => (fresh18 ((ftv s) ++ (ftv s') ++ (ftv t)), x)) (ftv t).

(* Too much indirection! 
  Nice is about fresh vars in rhs of R, while R_extender creates them on LHS.
*)
Lemma R_extender_Nice R s s' t' :
  Nice (sym_alpha_ctx (R ++ R_extender s s' t')) t'.
Proof.
Admitted.

Lemma some_constructive_arg {R s s'} t' :
  Alpha R s s' -> {t & Alpha (R ++ R_extender s s' t') t t' * Alpha (R ++ R_extender s s' t') s s'}%type.
Proof.
  intros.
  remember (R_extender s s' t') as R'.
  exists (mren (sym_alpha_ctx (R ++ R')) t').
  split.
  - eapply @alpha_sym with (ren := sym_alpha_ctx (R ++ R')). auto with α_eq_db.
    eapply alpha_mren_specal.
    subst.
    eapply R_extender_Nice.

  - eapply @alpha_extend_vacuous_right; auto.
    + (* by construction *) admit.
    + (* by construction *) admit.
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
    intros t Ht.

    destruct (some_constructive_arg t H) as [t0 [Ha_t0 Ha_s] ].
    
    eapply (IHA2 (R ++ (R_extender s s' t)) _ (tmapp s t0)).
    constructor; eauto.
    eapply H0. eapply (IHA1 (sym_alpha_ctx (R ++ (R_extender s s' t))) t0 t); eauto with α_eq_db.
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
  - eapply α_preserves_L; eauto. eapply alpha_refl. constructor.
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

(* TODO, no idea how hard this is
  Probaly need to make more generic with R
*)
Lemma red_beta x s t1 t2 : 
  step_gu_naive t1 t2 ->
  NC s ((x, t1)::nil) ->
  NC s ((x, t2)::nil) -> (* step does not introduce new free vars, so should be true!*)
  { a & prod 
    ( red_gu_na (sub x t1 s) a) 
    ( nil ⊢ a ~ sub x t2 s) }. 
Proof. 
  intros Hstep.
  induction s.
  - admit.
  - admit.
  - intros.
    specialize (IHs1 (nc_app_l H) (nc_app_l H0)) as [g1 [Hred_g1 Ha_g1] ].
    specialize (IHs2 (nc_app_r H) (nc_app_r H0)) as [g2 [Hred_g2 Ha_g2] ].
    (* subtle again.
      from red_gu_na (sub x t1 s1) g1 we know
      - exists U s.t. GU U and nil ⊢ U ~ sub x t1 s1
      - then step_naive U U2   and  red_beta U2 g1
    *)

    induction Hred_g1; try eapply IHHred_g1; eauto. (* why dont we get a nice term IH for the second case *)
    
    induction Hred_g2; try eapply IHHred_g2; eauto.
    repeat rewrite <- single_subs_is_sub.
    repeat rewrite <- single_subs_is_sub in *.
    autorewrite with subs_db.
    intros.

    
Admitted.

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
      (* LRS says we should be able to swap the two. But then ren_lrs ⊢ s y0
      should imply ((s, y)::ren) s y0, which cannot be
    *)
      admit.
    + exfalso.
      (* same reasoning, but now with first arg of pair.*)
      admit.
    + eapply @alpha_swap with (ren' := ((x, y)::Rt)) in H.
      inversion H; subst.
      inversion H10; subst; try contradiction.
      apply alpha_var.
      assumption.
      apply lrs_sym. auto.

  - constructor.
    eapply IHs; eauto...
    + (* aha! s not free in t0 by NC. So we can remove it! *) admit.
    + (* x <> s by NC (tmlam s t s0) [(x, ...)] *) admit.
  - constructor; eauto with gu_nc_db.
Admitted.

(* Unfolding step_gu_naive, not used, may be used in beta_expansion'? *)
Lemma step_gu_naive_unfold {s t s' t' x x' A }:
  step_gu_naive (tmapp (tmlam x A s) t) (tmapp (tmlam x' A s') t') ->
  Alpha [] t t' ->
(* by this last alpha argument, we force that we have a step_app_l
  maybe we can also encode this in another way.
*)

  {s'_alpha & Alpha [(x, x')] s'_alpha s' * step_gu_naive s s'_alpha}%type.
Proof.
  intros.
  inversion H; subst. inversion H1; subst. inversion H7; subst.
  assert (y = x') by admit. (* By step_naive, it cannot chagne binders*)
  subst.
  exists (rename x' x s'). (* x not free in s'. Then it would also have been free in s (step cannot introduce free vars)*)
  split.
  - admit.
  - apply step_gu_naive_intro with (s' := (rename x' x s0)).
    + admit.
    + (* what if x a binder in s0?? *)
      admit.
    + (* some step naive alpha preserves thing?*)

Admitted.

(* Closure under beta expansion. *)
Lemma beta_expansion' A B x y s s' t :
  Alpha [(y, x)] s' s -> (* this allows us to not have to "rename free vars in t" manually*)
  NC s [(x, t)] -> (* this really is the right assumption. no free variable in t is a binder in s', because these binders could be added to the environment through beta reduction and then capture*)
  SN_na t -> L A (sub x t s) ->
  L A (tmapp (tmlam y B s') t).
Proof with eauto with α_eq_db gu_nc_db.
  move=> Ha_s' nc snt h. have sns := sn_subst nc (L_sn h).
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
  - eapply α_preserves_L; eauto.
    rewrite <- single_subs_is_sub.
    eapply alpha_rename_binder_stronger...
    + eapply @alpha_trans with (ren := (x, y)::nil) (ren' := (y, y0)::nil)...
    + constructor. constructor.
     
  - inv H5.

    (* an unfolding alpha lemma for step_gu_naive *)
    destruct (step_gu_naive_unfold st H8) as [s5' [Ha_s5' Hstep_s5'] ].
    eapply α_preserves_L_R with (s := tmapp (tmlam y B s5') x1) (R := nil)...
    specialize (H s5' Hstep_s5' x1).
    clear Ha_s5'. clear H7. clear st. clear s5.
    inv Hstep_s5'.
    assert (HSN_x1: SN_na x1) by now constructor.

    (* TODO: instead of to_GU, assume gu of s0 here by NC?*)
    assert ({s'_a &  step_naive s0 s'_a * Alpha [(y, x)] s5' s'_a}%type).
    {
      eapply step_naive_preserves_alpha2 with (s := s') (s' := s0) (t := s5')...
      exact (nc_to_gu_axiom Hnc).
      eapply @alpha_trans with (ren := (y, y)::nil) (ren' := (y, x)::nil) (t := x0)...
    }
    destruct H4 as [s'_a [ Hstep_s'_a Ha_s'_a ] ].
    specialize (H HSN_x1 s'_a Ha_s'_a).

    assert (NC s'_a [(x, x1)]).
    {
      (* step_naive s0 s'_a, and step_naive does not introduce new bound var names*)
      admit.
    }

    eapply H; eauto.
    assert ({α & (step_gu_naive (sub x x1 s0) α) * (nil ⊢ α ~ sub x x1 s'_a)}%type) 
      as [alpha [Hred Halpha] ].
      {
        repeat rewrite <- single_subs_is_sub.
        eapply (@step_subst_sigma)...
      }
    eapply α_preserves_L with (s := alpha); auto.
    eapply L_cl with (s := (sub x x1 s0)); auto.

  - eapply α_preserves_L with (s := (tmapp (tmlam y B x0) t0))...
    eapply H10.
    + econstructor...
    + (* NC s0 [(x, x1)] and  x1 -gu-> t0, which cannot introduce free vars, so NC s0 [(x, t0)]*) 
      admit.
    +  
      assert ({ a & prod 
    ( red_gu_na (sub x x1 s0) a) 
    ( nil ⊢ a ~ sub x t0 s0) }).
      { (* this has a lot of repetition with the above *)
        apply red_beta...
        - econstructor...
        - (* step does not introduce ftvs *) admit.
      }
      destruct H0 as [a [Hred_a Ha_a] ].
      eapply (L_cl_star) in h.
      * eapply α_preserves_L; eauto.
      * assumption.
Admitted.

Lemma beta_expansion_subst X t sigma s A B :
  NC (subs sigma s) [(X, t)] -> (* so the substitution makes sense after "breaking"  it open*)
  SN_na t -> L A (subs ((X, t)::sigma) s) -> L A (tmapp (subs sigma (tmlam X B s)) t).
Proof.
  intros nc snt H.
  simpl in H.
  autorewrite with subs_db.
  eapply beta_expansion' in H; eauto. 
  (* This needs to be done in a lemma about allowing identity alpha contexts *)
  assert (forall A, Alpha [] (tmlam X A (subs sigma s)) (tmlam X A (subs sigma s))).
  {
    intros. apply alpha_refl. constructor.
  }
  specialize (H0 A).
  inv H0. assumption.
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
      2: { 
        apply L_sn in H. eapply α_preserves_SN_R; eauto. 
      }

    eapply α_preserves_L_R with (s' := tmapp (subs sigma (tmlam X A s)) t) in ih; eauto. constructor.
    2: {eapply @alpha_sym with (ren := R); eauto.
    apply sym_alpha_ctx_is_sym. }
(* Then by Alpha R s s and αCtxSym R sigma sigma  and αCtxSym R sigma' sigma'
      we know that the alpha context doesnt do anything and can be removed

      I am not sure how to make that argument precise yet, and how much work it is.
    *)
    eapply @alpha_trans with (ren' := (sym_alpha_ctx R)) (t := subs sigma (tmlam X A s)) (ren := nil).
    + (* alpha trans id*) admit.
    + eapply subs_preserves_alpha_σ_R; eauto.    
      *  (* by NC (tmlam X A s) sigma 
              => X not in ftv sigma (by nc (tmlam x ...) sigma)
              => X not in ftv sigma'   (alpha [] preserves ftvs)*)
          admit.
      * eapply alpha_refl. constructor.
      * (* alpha ctx sym *) admit.
    + (* we can remove the alpha_ctx*)
      autorewrite with subs_db.
      (* maybe this is simply: subs preserves alpha! we have R sigma sigma, R s s, then R (subs sigma s) (subs sigma s)*)
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