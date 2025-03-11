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

From PlutusCert Require Import STLC_named util alpha freshness alpha_ctx_sub.



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
Lemma nc_lam {x A s sigma} :
  NC (tmlam x A s) sigma -> NC s sigma.
Admitted.

Lemma nc_app_l {s t sigma} :
  NC (tmapp s t) sigma -> NC s sigma.
Admitted.

Lemma nc_app_r {s t sigma} :
  NC (tmapp s t) sigma -> NC t sigma.
Admitted.

(* No free vars are changed *)
Lemma alpha_preserves_nc_ctx s x t t':
   Alpha [] t t' -> NC s ((x, t)::nil) -> NC s ((x, t')::nil).
Admitted.

Lemma step_naive_pererves_nc_ctx s t t1 t2 x :
  step_naive t1 t2 -> NC s ((x, t1)::nil) -> NC t ((x, t2)::nil).
Admitted.

Lemma gu_app_l {s t} :
  GU (tmapp s t) -> GU s.
Admitted.

Lemma gu_app_r {s t} :
  GU (tmapp s t) -> GU t.
Admitted.

Lemma gu_lam {x A s} :
  GU (tmlam x A s) -> GU s.
  Admitted.

Lemma gu_applam_to_nc s t x A :
  GU (tmapp (tmlam x A s) t) -> NC s [(x, t)].
Admitted.

Lemma nc_ftv_env s sigma :
  NC s sigma -> forall x, In x (btv s) -> ~ In x (ftv_keys_env sigma).
Admitted.



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

Fixpoint btv_env (sigma : list (string * term)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => (btv t) ++ (btv_env sigma')
  end.

  Definition set_diff (l1 l2 : list string) : list string :=
  filter (fun x => negb (existsb (String.eqb x) l2)) l1.

Fixpoint fresh18 (l : list string) : string :=
  match l with
    | nil => "fr"
    | x :: xs => x ++ fresh18 xs
  end.


Definition Uhm sigma s := ((forall x, In x (btv_env sigma) -> ~ In x (tv s)) 
  * (forall x, In x (btv_env sigma) -> ~ In x (ftv_keys_env sigma))
  * (forall x, In x (btv s) -> ~ In x (ftv_keys_env sigma)))%type.

Lemma uhm_smaller {sigma s x t} : Uhm ((x, t)::sigma) s -> Uhm sigma s.
Proof.
  intros.
  unfold Uhm.
  split; [split|]; unfold Uhm in H; destruct H as [ [uhm1 uhm2] uhm3]; intros.
  - eapply uhm1.
    simpl. apply in_app_iff. right. assumption.
  - assert (~ In x0 (ftv_keys_env ((x, t)::sigma))).
    {
      eapply uhm2.
      simpl. apply in_app_iff. right. assumption.
    }
    simpl in H0.
    intuition.
  - assert (~ In x0 (ftv_keys_env ((x, t)::sigma))).
    {
      eapply uhm3.
      auto.
    }
    simpl in H0.
    intuition.
Qed.


Lemma Uhm_appl {s t sigma} :
  Uhm sigma (tmapp s t) -> Uhm sigma s.
Proof.
  intros.
  unfold Uhm in H.
  destruct H as [ [uhm1 uhm2] uhm3].
  unfold Uhm.
  split; [split|]; intros.
  - specialize (uhm1 x H).
    apply not_tv_dc_appl in uhm1. auto.
  - specialize (uhm2 x H). auto.
  - specialize (uhm3 x).
    assert (In x (btv (tmapp s t))).
    { apply btv_c_appl. auto. }
    specialize (uhm3 H0).
    auto.
Qed.

Lemma Uhm_appr {s t sigma} :
  Uhm sigma (tmapp s t) -> Uhm sigma t.
Proof.
Admitted.

Lemma Uhm_lam {x A s sigma t} :
(* we changed Uhm. Maybe we need more conditions! *)
  (* by GU s we have x not in btv s.*)

  (forall y, In y (btv t) -> ~ In y (tv s)) -> (* uhm1*)
    (forall y, In y (btv t) -> ~ In y (ftv_keys_env sigma)) -> (* uhm2*)
  (forall y, In y (btv s) -> ~ In y (ftv t)) ->  (* uhm3*)

  (~ In x (btv t)) -> (* uhm6*)
  GU t -> (* uhm7 *)
  (forall y, In y (btv_env sigma) -> ~ In y (ftv t)) -> (* uhm8 *)
  (~ In x (btv s)) -> (* uhm9 *)

  (* cannot combine uhm3 and uhm1: free vars in t can still be free vars in s*)
  Uhm sigma (tmlam x A s) -> Uhm ((x, t)::sigma) s.
Proof.
  intros uhm1' uhm2' uhm3' uhm6' uhm7' uhm8' uhm9' HUhm.
  unfold Uhm.
  split; [split|]; intros;
      (* ~ In tv decomposes through tmlam.
        And we have control over binder names in t'? Yeah why not. 
          They were not a problem yet before though...
        Where do we need the GU sigma then? I think for the alphaCtxSub sigma sigma: 
          renaming stuff that is binder in sigma is vacuous alpha subst, but if it is also ftv, 
          then no longer. But if it is GU (elementwise for value side), then that canot happen
        That still allows the identity substitutions!
      *)
  unfold Uhm in HUhm; destruct HUhm as [ [uhm1 uhm2] uhm3].
  - (* x0 not in tv s.
      Case x0 in btv t:
        - then by uhm1' notin tv s
      Case x0 in btv_env sigma:
        - then by uhm1 and not_tv_dc_lam.
    *)

    admit.
  - (* suppose x0 in btv t
        - then by uhm2' not in ftv_keys_env sigma
        - then also not in tv s
        - what if x = x0?

          suppose x in btv env sigma. then x not in tv (tmlam x A s). Contradiction.
          Hence x not in btv_env sigma.
          Hence x in btv t.

       suppose x0 in btv_env sigma 
        - then not in tv (tmlam x A s)   -> x0 <> x
        - not in ftv_keys_env sigma
    *)
    destr_eqb_eq x0 x.
    + exfalso.
      simpl in H.
      apply in_app_iff in H.
      destruct H.
      * apply uhm6' in H. (* uhm6' *)
        auto.
      * specialize (uhm1 x H).
        contradiction uhm1.
        simpl. left. reflexivity.
    + simpl in H. apply in_app_iff in H.
      destruct H.
      * (* in btv t, then not in ftv of t by GU t (uhm7').
          and
          by uhm2' not in ftv keys env sigma.
        *)
        admit.
      * (*
          x: by x0 <> x.
          t: by uhm8'
          sigma: by uhm2
        *)
        admit.
  - destr_eqb_eq x0 x.
    + contradiction. (* by uhm9'*)
    + (*
        x : by x0 <> x
        t : by uhm3'
        sigma: By uhm3
    *)
Admitted.


(* defined for arbitrary substitution, while below we only need it for identity substituiosn
  maybe we can then reuse this in other parts of the code. 
  
  this is simply to_GU', but with more subsitutions.
  *)
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
