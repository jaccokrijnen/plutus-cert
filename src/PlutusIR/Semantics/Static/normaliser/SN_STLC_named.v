(** * Strong Normalization of System F *)

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import STLC_named STLC_named_typing ARS.


(** **** Capms lemmas *)
(*

TODO: alternatief
Jacco:
Het is misschien wat makkelijker om Equations te gebruiken in ipv Program Fixpoint, equations is wat uitgebreider en meer onderhouden (https://github.com/mattam82/Coq-Equations?tab=readme-ov-file#documentation)
GitHub - mattam82/Coq-Equations: A function definition package for Coq
A function definition package for Coq. Contribute to mattam82/Coq-Equations development by creating an account on GitHub.
 
die genereert de unfold lemmas sowieso
 
al die lemmas komen dan in een hintdb genaamd capms, die je dan met autorewrite with capms kan gebruiken.
 
dat is dan je alternatief voor wat je bij een niet-recursieve functie zou doen met simpl
 *)
Lemma capms_var sigma X t:
  lookup X sigma = Some t -> capms sigma (tmvar X) = t.
Proof. 
  rewrite capms_equation_1. 
  by move=> ->. (* TODO: this is copilot stuff, I dont understand that*)
Qed.

Lemma capms_lam X B sigma s :
  capms sigma (tmlam X B s) = 
    tmlam (fresh2 sigma s) B (capms sigma (rename X (fresh2 sigma s) s)).
Proof.
  rewrite capms_equation_2.
  reflexivity.
Qed.

(** **** Notations *)
(* Notation for substitution *)
Notation "'[' x ':=' s ']' t" := (capms [(x, s)] t) (at level 20).

Notation "sigma [[ t ]]" := (capms sigma t) (at level 20).

(** **** One-Step Reduction *)

(* Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope prop_scope with PROP.
Open Scope prop_scope. *)

Inductive step : term -> term -> Prop :=
| step_beta (x : string) (A : type) (s t : term) :
    step (tmapp (tmlam x A s) t) ([x := t] s)
| step_appL s1 s2 t :
    step s1 s2 -> step (tmapp s1 t) (tmapp s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (tmapp s t1) (tmapp s t2)
| step_abs x A s1 s2 :
    step s1 s2 -> step (tmlam x A s1) (tmlam x A s2).

Lemma step_ebeta x A s t u : 
  u = ([x := t] s) -> step (tmapp (tmlam x A s) t) u.
Proof. move->. exact: step_beta. Qed.

(* Note: Study: After replacing a variable with something in sigma
  we can still do the same step as we previously could by red s t, hence: true
  Not true in non-deterministic setting.
*)
Lemma step_subst sigma s t :
  step s t -> step (sigma [[ s ]]) (sigma [[ t ]]).
Proof.
  (* move=> st. elim: st sigma => {s t}; asimpl; eauto using step.
  move=> A s t sigma. apply: step_ebeta. by autosubst.
Qed. *)
Admitted.

(** **** Many-Step Reduction *)

Definition red := star step.

(* Definition sred sigma tau :=
  forall x : var, red (sigma x) (tau x). *)

Lemma red_app s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (tmapp s1 t1) (tmapp s2 t2).
Proof.
  move=> A B. apply: (star_trans (tmapp s2 t1)).
  - apply: (star_hom (tmapp^~ t1)) A => x y. exact: step_appL.
  - apply: star_hom B => x y. exact: step_appR.
Qed.

Lemma red_abs x A s1 s2 : 
  red s1 s2 -> red (tmlam x A s1) (tmlam x A s2).
Proof. apply: star_hom => x' y'. exact: step_abs. Qed.

Lemma red_subst sigma s t : 
  red s t -> red (sigma [[s]]) (sigma [[t]]).
Proof. apply: star_hom => x' y'. exact: step_subst. Qed.

(* Lemma sred_up sigma tau : 
  sred sigma tau -> sred (up sigma) (up tau).
Proof. move=> A [|n] //=. asimpl. apply/red_subst/A. Qed. *)

Global Hint Resolve red_app red_abs 
(* sred_hup  *)
: red_congr.

(* Lemma red_compat sigma tau s :
  sred sigma tau -> red ([x := sigma] s) ([x := tau] s).
Proof.
  elim: s sigma tau; intros; asimpl; eauto with red_congr.
Qed. *)

(* NOTE: A little pen and paper study strongly suggests that this is still true for named. *)
Lemma red_beta x s t1 t2 : step t1 t2 -> red ([x := t1] s) ([x := t2] s).
Proof. 
  (* move=> h. apply: red_compat => -[|n]/=; [exact: star1|exact: starR].  *)
Admitted.

(* Strong Normalization *)

Notation SN := (sn step).

Lemma sn_closed t s : SN (tmapp s t) -> SN s.
Proof. apply: (sn_preimage (h := tmapp^~t)) => x y. exact: step_appL. Qed.

Lemma sn_subst sigma s : SN (sigma [[s]]) -> SN s.
Proof. apply: sn_preimage => x' y'. exact: step_subst. Qed.

(* The Reducibility Candidates/Logical Predicate*)

Definition cand := term -> Prop.

Definition neutral (s : term) : bool :=
  match s with
    | tmlam _ _ _ => false
    | _ => true
  end.

Record reducible (P : cand) : Prop := {
  p_sn : forall s, P s -> SN s;
  p_cl : forall s t, P s -> step s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step s t -> P t) -> P s
}.

Fixpoint L (T : type) : cand :=
  match T with
    | tp_base => SN 
    | tp_arrow A B => fun s => forall t, L A t -> L B (tmapp s t)
  end.

(* TODO: Compare with Inductive instantiation from normalisation in
  PLF: that has a cleaner definition, but restraints the order*)
Definition EL (Gamma : list (string * type)) 
          (sigma : list (string * term)) : Prop :=
  forall x T, lookup x Gamma = Some T ->
    exists t, lookup x sigma = Some t /\ L T t.

(* is true! *)
Lemma extend_EL (Gamma : list (string * type)) (sigma : list (string * term)) x T t :
  EL Gamma sigma -> L T t -> EL ((x, T) :: Gamma) ((x, t) :: sigma).
Proof.
Admitted.

(* Facts about reducible sets. *)

Lemma reducible_sn : reducible SN.
Proof. constructor; eauto using ARS.sn. by move=> s t [f] /f. Qed.
Global Hint Resolve reducible_sn : core.

Lemma reducible_var P x : reducible P -> P (tmvar x).
Proof. move/p_nc. apply=> // t st. inversion st. Qed.

Lemma L_reducible A :
  reducible (L A).
Proof with eauto using step.
  elim: A => /=[|A ih1 B ih2].
  - apply reducible_sn.
  - constructor.
    + move=> s h. apply: (@sn_closed (tmvar "x")). apply: (p_sn (P := L B))...
      eapply h. eapply reducible_var; eauto.
    + move=> s t h st u la. apply: (p_cl _ (s := tmapp s u))...
    + move=> s ns h t la.
      have snt := p_sn ih1 la.
      elim: snt la => {} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      (* Note: Case L B ([x := t] s0. By using Autosubst's "inv" instead of normal inversion, this goal vanishes. Why? *) (* Todo: Think, this case doesn't happen in db variant*)
      * apply: ih3 => //. exact: (p_cl ih1) la _.
Qed.

Corollary L_sn A s : L A s -> SN s.
Proof. intros Las. assert (reducible (L A)) by apply (L_reducible A).
   apply (p_sn H). assumption.
Qed.

Corollary L_cl T s t : L T s -> step s t -> L T t.
Proof.
  intros Hstep Hst.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_cl H Hstep); assumption.
Qed.

Corollary L_nc T s :
  neutral s -> (forall t, step s t -> L T t) -> L T s.
Proof. 
  intros Hneut Hstep.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_nc H); assumption.
Qed.

Corollary L_var T x : L T (tmvar x).
Proof.
  apply L_nc; first by []. intros t st. inversion st.
Qed. 

Corollary L_cl_star T s t :
  L T s -> red s t -> L T t.
Proof.
  intros Ls red_st. induction red_st.
  - assumption.
  - apply L_cl with y; assumption.
Qed.

(* Closure under beta expansion. *)
Lemma beta_expansion A B x s t :
  SN t -> L A ([x := t] s) ->
  L A (tmapp (tmlam x B s) t).
Proof with eauto.
  move=> snt h. have sns := sn_subst (L_sn h).
  elim: sns t snt h => {} s sns ih1 t. elim=> {} t snt ih2 h.
  apply: L_nc => // u st. inv st => //.
  - inv H2. apply: ih1 => //. apply: L_cl h _. exact: step_subst.
  - apply: ih2 => //. apply: L_cl_star h _. exact: red_beta.
Qed.

(* Ask Richard's pen and paper notes*)
Lemma capmsRename x x' t sigma s :
  ((x', t)::sigma) [[rename x x' s]] = ((x, t)::sigma) [[s]].
Proof. Admitted.

Definition notKeyIn X (sigma : list (string * term)) : Prop :=
  ~ exists t, lookup X sigma = Some t.

Definition varNotIn X (sigma : list (string * term)) : Prop :=
  notKeyIn X sigma /\ (* X does not appear in the free type variables of any of the values  of tau*)
  ~ In X (List.flat_map (compose ftv snd) sigma).

(* Would also work for bigger substs, but not necessary*)
Lemma composeCapms X t sigma s :
  varNotIn X sigma -> [X := t] (sigma [[s]]) = ((X, t) :: sigma) [[s]].
Proof.
Admitted.

(* Definitionally, 
  fresh2 creates a fresh variable that is not in 
    any of the keys or values of sigma *)
Lemma freshLemma sigma s :
  varNotIn (fresh2 sigma s) sigma.
Proof. Admitted.

Lemma beta_expansion_subst X t sigma s A B :
  SN t -> L A (((X, t)::sigma) [[s]]) -> L A (tmapp (sigma [[tmlam X B s]]) t).
Proof.
  intros snt H.
  remember (fresh2 sigma s) as X'.
  assert (L A ([X' := t] (sigma [[(rename X X' s)]])) -> L A (tmapp (tmlam X' B (sigma [[rename X X' s]])) t)).
  {
    apply beta_expansion; assumption.
  }

  (* Now we use H to show the assumption of H0 holds. Then we rewrite the conclusion into the goal*)
  assert (HsigIntoLam: tmapp (tmlam X' B (sigma [[rename X X' s]])) t = tmapp (sigma [[tmlam X B s]]) t).
  {
    rewrite capms_lam.
    rewrite HeqX'.
    reflexivity.
  }
  rewrite <- HsigIntoLam.
  apply H0.
  rewrite composeCapms.
  - rewrite capmsRename.
    assumption.
  - rewrite -> HeqX'.
    apply freshLemma.
Qed.

(* The fundamental theorem. *)
Theorem soundness Gamma s A :
  has_type Gamma s A -> forall sigma,
    EL Gamma sigma -> L A (sigma [[s]]).
Proof with eauto using L_sn. 
  elim=> {Gamma s A} [Gamma X A |Gamma X A s B _ ih sigma EL|Gamma s t A B _ ih1 _ ih2 sigma HEL].
  - intros HlookupGamma sigma HEL.
    unfold EL in HEL.
    specialize (HEL X A HlookupGamma).
    destruct HEL as [t [HlookupSigma LAt] ].
    apply capms_var in HlookupSigma.
    rewrite HlookupSigma.
    assumption.
  - move=> t h.
    specialize (ih ((X, t)::sigma) (extend_EL EL h)).
    apply: beta_expansion_subst...
  - specialize (ih1 _ HEL). specialize (ih2 _ HEL).
    unfold L in ih1. fold L in ih1. specialize (ih1 (sigma [[t]]) ih2).
    rewrite capms_equation_3.
    assumption.
Qed.

Corollary type_L E s T : has_type E s T -> L T s.
Proof.
  move=> ty. move: (@soundness E s T ty) => h.
  admit. (* TODO: Create some sort of identity subsittution*)
Admitted.

Corollary strong_normalization E s T : has_type E s T -> SN s.
Proof.
  move=>/type_L/L_sn. apply.
Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Ssr")) *)
(* End: *)