From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Arith.

From PlutusCert Require Import STLC step_naive util alpha.alpha variables alpha_freshness alpha_ctx_sub.



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
Hint Constructors LegalRenSwap : α_eq_db.
Hint Unfold LegalRenSwaps : α_eq_db.

Create HintDb α_eq_db_trans.
Hint Resolve id_left_trans : α_eq_db_trans.
Hint Resolve id_right_trans : α_eq_db_trans.
Hint Resolve alpha_extend_ids : α_eq_db_trans.
Hint Resolve ctx_id_left_is_id : α_eq_db_trans.
Hint Resolve ctx_id_right_is_id : α_eq_db_trans.

(* So sub is also rewritten when rewriting subs *)
Hint Extern 1 => simpl sub : subs_db.

Inductive GU : term -> Set :=
| GU_var x : GU (tmvar x)
(* in app, if s and t do not share GU_vars: *)
| GU_app {B} s t : 
    GU s -> 
    GU t -> 
    forall (H_btv_btv_empty : forall x, In x (btv t) -> ~ In x (tv s)),
    forall (H_btv_ftv_empty : forall x, In x (btv s) -> ~ In x (tv t)),
    GU (@tmbin B s t)
| GU_lam {B} x A s : 
    GU s -> 
    ~ In x (btv s) ->
    GU (@tmabs B x A s)
| GU_builtin d :
    GU (tmbuiltin d).

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

Lemma nc_smaller {s sigma x t} : NC s ((x, t)::sigma) -> NC s sigma.
Proof.
  intros.
  inversion H; subst.
  auto.
Qed.

(* why doesnt sigma grow???
  NC: forall btv in s, not in sigma
  we remove a binder, thenw e should still have that all remaining btvs are not in the original sigma.
*)
Lemma nc_lam {B x s A sigma} : 
  NC (@tmabs B x A s) sigma -> NC s sigma.
Proof.
  induction sigma; [constructor|]; intros Hnc.
  inversion Hnc; subst.
  constructor.
  + eapply IHsigma. auto.
  + intros y H_btvs.
    eapply btv_c_lam in H_btvs; eauto.
Qed.

Lemma nc_app_l {B s t sigma} :
  NC (@tmbin B s t) sigma -> NC s sigma.
Proof.
  induction sigma; [constructor|]; intros Hnc.
  inversion Hnc; subst.
  constructor.
  + eapply IHsigma. auto.
  + intros y H_btvs.
    eapply btv_c_appl in H_btvs; eauto.
Qed.

Lemma nc_app_r {B s t sigma} :
  NC (@tmbin B s t) sigma -> NC t sigma.
Proof.
  induction sigma; [constructor|]; intros Hnc.
  inversion Hnc; subst.
  constructor.
  + eapply IHsigma. auto.
  + intros y H_btvs.
    eapply btv_c_appr in H_btvs; eauto.
Qed.

(* No free vars are changed *)
Lemma alpha_preserves_nc_ctx s x t t':
   Alpha [] t t' -> NC s ((x, t)::nil) -> NC s ((x, t')::nil).
Proof.
  intros Ha_t Hnc_t.
  inversion Hnc_t; subst.
  constructor. auto.
  intros y Hbtv.
  specialize (H4 y Hbtv).
  destruct H4 as [Hynotx Hftv_t].
  split; auto.
  eapply alpha_preserves_no_ftv; eauto.
  constructor.
Qed.

Lemma gu_app_l {B s t} :
  GU (@tmbin B s t) -> GU s.
Proof.
  inversion 1; auto.
Qed.

Lemma gu_app_r {B s t} :
  GU (@tmbin B s t) -> GU t.
Proof.
  inversion 1; auto.
Qed.

Lemma gu_lam {B x A s} :
  GU (@tmabs B x A s) -> GU s.
Proof.
  inversion 1; auto.
Qed.

Lemma gu_app_st__gu_app_ts {B} s1 s2 :
  GU (@tmbin B s1 s2) -> GU (@tmbin B s2 s1).
Proof.
  intros.
  inversion H; subst.
  constructor; auto.
Qed.

Lemma gu_applam_to_nc {BA} {BL} s t x A :
  GU (@tmbin BA (@tmabs BL x A s) t) -> NC s [(x, t)].
Proof.
  intros Hgu.
  inversion Hgu as [ | ? ? ? Hgu_lam Hgu_t Hgu_P1 Hgu_P2 | | ]; subst.
  repeat constructor.
  - intros Hcontra; subst.
    inversion Hgu_lam; subst.
    contradiction.
  - intros Hcontra; apply extend_ftv_to_tv in Hcontra; revert Hcontra.
    apply Hgu_P2.
    apply btv_c_lam; auto.
Qed.

(* The fundamental NC property*)
Lemma nc_ftv_env s sigma :
  NC s sigma -> forall x, In x (btv s) -> ~ In x (ftv_keys_env sigma).
Proof.
  intros Hnc x Hin_btvs.
  induction Hnc.
  - simpl. auto.
  - simpl.
    specialize (p x Hin_btvs) as [Hnotx Hnott].
    apply de_morgan2.
    split; auto.
    apply not_in_app.
    split; auto.
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

Lemma gu_ftv_then_no_btv s x :
  GU s -> In x (ftv s) -> ~ In x (btv s).
Proof.
  intros Hgu Hins.
  induction Hgu.
  - simpl in Hins. auto.
  - simpl in Hins.
    apply in_app_iff in Hins as [Hins | Hins].
    + simpl.
      apply not_in_app.
      split.
      * auto.
      * intros Hcontra.
        apply H_btv_btv_empty in Hcontra.
        apply extend_ftv_to_tv in Hins.
        contradiction.
    + simpl.
      apply not_in_app.
      split.
      * intros Hcontra.
        apply H_btv_ftv_empty in Hcontra.
        apply extend_ftv_to_tv in Hins.
        contradiction.
      * auto.
  - simpl.
    apply de_morgan2.
    split.
    + intros Hcontra.
      subst.
      apply ftv_lam_no_binder in Hins. 
      auto.
    + apply IHHgu.
      apply ftv_lam_helper in Hins.
      auto.
  - inversion Hins.
Qed.


Lemma step_naive_preserves_nc_ctx s t1 t2 x :
  step_naive t1 t2 -> NC s ((x, t1)::nil) -> NC s ((x, t2)::nil).
Proof.
  intros Hstep Hnc.
  inversion Hnc; subst.
  constructor.
  - constructor.
  - intros y Hbtv.
    specialize (H4 y Hbtv).
    destruct H4 as [Hynotx Hftv_t].
    split; auto.
    eapply step_naive_preserves_no_ftv. eauto. auto.
Qed.


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
    What about ftv in t that are also ftv in s? they are not renamed and thus in t'.
     Can they be btv in sigma? No by the first argument

*)

(* Property that allows to add binder names (a, b, c,...) to alpha context R, and keeping the property that
    R ⊢ s ~ s, and R ⊢ sigma ~ sigma
   - binders in sigma are not free in s
   - binders in sigma are not free in sigma
   - binders in s are not free in sigma, exactly NC s sigma: so moved out of this
*)
(* Binders Unique, in the sense that they do not occur in ftvs sigma or tvs s*)
Definition BU sigma s := ((forall x, In x (btv_env sigma) -> ~ In x (tv s)) 
  * (forall x, In x (btv_env sigma) -> ~ In x (ftv_keys_env sigma)))%type.

Lemma BU_smaller {sigma s x t} : BU ((x, t)::sigma) s -> BU sigma s.
Proof.
  intros.
  unfold BU.
  split; unfold BU in H; destruct H as [ BU1 BU2]; intros.
  - eapply BU1.
    simpl. apply in_app_iff. right. assumption.
  - assert (~ In x0 (ftv_keys_env ((x, t)::sigma))).
    {
      eapply BU2.
      simpl. apply in_app_iff. right. assumption.
    }
    simpl in H0.
    intuition.
Qed.


Lemma BU_appl {B s t sigma} :
  BU sigma (@tmbin B s t) -> BU sigma s.
Proof.
  intros.
  unfold BU in H.
  destruct H as [ BU1 BU2].
  unfold BU.
  split; intros.
  - specialize (BU1 x H).
    apply not_tv_dc_appl in BU1. auto.
  - specialize (BU2 x H). auto.
Qed.

Lemma BU_appr {B s t sigma} :
  BU sigma (@tmbin B s t) -> BU sigma t.
Proof.
  intros HBU.
  unfold BU in HBU.
  destruct HBU as [ BU1 BU2].
  unfold BU.
  split; intros.
  - specialize (BU1 x H).
    apply not_tv_dc_appr in BU1. auto.
  - specialize (BU2 x H). auto.
Qed.

(* x not in btv s, hence we can add it freely as ftv to sigma*)
Lemma BU_lam_id {B x A s sigma} :
  GU (@tmabs B x A s) ->
  (* cannot combine BU3 and BU1: free vars in t can still be free vars in s*)
  BU sigma (@tmabs B x A s) -> BU ((x, tmvar x)::sigma) s.
Proof.
  intros Hgu HBU.
  unfold BU in HBU.
  destruct HBU as [ BU1 BU2].
  unfold BU.
  split; intros.
  - eapply not_tv_dc_lam.
    eapply BU1. auto.
  - simpl in H.
    simpl.
    apply de_morgan2.
    split; [|apply de_morgan2; split].
    all: try solve [intros Hcontra; subst; apply BU1 in H; simpl in H; intuition].
    now apply BU2.
Qed.
