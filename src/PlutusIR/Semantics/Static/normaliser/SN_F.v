(** * Strong Normalization of System F *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
From PlutusCert Require Import AutosubstSsr ARS normaliser.Context.
From PlutusCert Require Import STLC_DB STLC_DB_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** **** Definitions *)


(** **** Substitution Lemmas *)

(* Global Instance Rename_type : Rename type. derive. Defined. *)

(*Global Instance Subst_type : Subst type. derive. Defined.

Global Instance SubstLemmas_type : SubstLemmas type. derive. Qed.

Global Instance HSubst_term : HSubst type term. derive. Defined. *)

Global Instance Ids_term : Ids term. derive. Defined.
Global Instance Rename_term : Rename term. derive. Defined.
Global Instance Subst_term : Subst term. derive. Defined.

(* Global Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed.
Global Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed. *)

Global Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(** **** One-Step Reduction *)

Inductive step : term -> term -> Prop :=
| step_beta (A : type) (s t : term) :
    step (tmapp (tmlam A s) t) s.[t/]
| step_appL s1 s2 t :
    step s1 s2 -> step (tmapp s1 t) (tmapp s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (tmapp s t1) (tmapp s t2)
| step_abs A s1 s2 :
    step s1 s2 -> step (tmlam A s1) (tmlam A s2).

Lemma step_ebeta A s t u : u = s.[t/] -> step (tmapp (tmlam A s) t) u.
Proof. move->. exact: step_beta. Qed.

Lemma step_subst sigma s t :
  step s t -> step s.[sigma] t.[sigma].
Proof.
  move=> st. elim: st sigma => {s t}; asimpl; eauto using step.
  move=> A s t sigma. apply: step_ebeta. by autosubst.
Qed.

(* Lemma step_hsubst theta s t : step s t -> step s.|[theta] t.|[theta].
Proof. move=> h. apply (step_substf theta ids) in h. by asimpl in h. Qed. *)

(** **** Many-Step Reduction *)

Definition red := star step.

Definition sred sigma tau :=
  forall x : var, red (sigma x) (tau x).

Lemma red_app s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (tmapp s1 t1) (tmapp s2 t2).
Proof.
  move=> A B. apply: (star_trans (tmapp s2 t1)).
  - apply: (star_hom (tmapp^~ t1)) A => x y. exact: step_appL.
  - apply: star_hom B => x y. exact: step_appR.
Qed.

Lemma red_abs A s1 s2 : red s1 s2 -> red (tmlam A s1) (tmlam A s2).
Proof. apply: star_hom => x y. exact: step_abs. Qed.

Lemma red_subst sigma s t : red s t -> red s.[sigma] t.[sigma].
Proof. apply: star_hom => x y. exact: step_subst. Qed.

Lemma sred_up sigma tau : sred sigma tau -> sred (up sigma) (up tau).
Proof. move=> A [|n] //=. asimpl. apply/red_subst/A. Qed.

(* Lemma sred_hup sigma tau theta :
  sred sigma tau -> sred (sigma >>| theta) (tau >>| theta).
Proof. move=> A n /=. apply/red_hsubst/A. Qed. *)

Global Hint Resolve red_app red_abs sred_up 
(* sred_hup  *)
: red_congr.

Lemma red_compat sigma tau s :
  sred sigma tau -> red s.[sigma] s.[tau].
Proof.
  elim: s sigma tau; intros; asimpl; eauto with red_congr.
Qed.

Lemma red_beta s t1 t2 : step t1 t2 -> red s.[t1/] s.[t2/].
Proof. move=> h. apply: red_compat => -[|n]/=; [exact: star1|exact: starR]. Qed.

(* Strong Normalization *)

Notation SN := (sn step).

Lemma sn_closed t s : SN (tmapp s t) -> SN s.
Proof. apply: (sn_preimage (h := tmapp^~t)) => x y. exact: step_appL. Qed.

Lemma sn_subst sigma s : SN s.[sigma] -> SN s.
Proof. apply: sn_preimage => x y. exact: step_subst. Qed.

(* The Reducibility Candidates/Logical Predicate*)

Definition cand := term -> Prop.

Definition neutral (s : term) : bool :=
  match s with
    | tmlam _ _ => false
    | _ => true
  end.

Record reducible (P : cand) : Prop := {
  p_sn : forall s, P s -> SN s;
  p_cl : forall s t, P s -> step s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step s t -> P t) -> P s
}.

Fixpoint L (T : type) : cand :=
  match T with
    | tp_base => SN (** Added base kind! *)
    | tp_arrow A B => fun s => forall t, L A t -> L B (tmapp s t)
  end.

Global Instance Ids_type : Ids type. unfold Ids. exact (fun s => tp_base). Defined.
Notation "Gamma `_ i" := (normaliser.Context.get Gamma i) (at level 3).

Definition EL E (sigma : var -> term) : Prop :=
  forall x, x < size E -> L E`_x (sigma x).
(* 
Definition admissible (rho : nat -> cand) :=
  forall x, reducible (rho x). *)

(* Facts about reducible sets. *)

Lemma reducible_sn : reducible SN.
Proof. constructor; eauto using ARS.sn. by move=> s t [f] /f. Qed.
Global Hint Resolve reducible_sn : core.

Lemma reducible_var P x : reducible P -> P (tmvar x).
Proof. move/p_nc. apply=> // t st. inv st. Qed.

(* Lemma ad_cons P rho :
  reducible P -> admissible rho -> admissible (P .: rho).
Proof. by move=> H1 H2 [|i] //=. Qed. *)

Lemma L_reducible A :
  reducible (L A).
Proof with eauto using step.
  elim: A => /=[|A ih1 B ih2].
  - apply reducible_sn.
  - constructor.
    + move=> s h. apply: (@sn_closed (tmvar 0)). apply: (p_sn (P := L B))...
      eapply h. eapply reducible_var; eauto.
    + move=> s t h st u la. apply: (p_cl _ (s := tmapp s u))...
    + move=> s ns h t la.
      have snt := p_sn ih1 la.
      elim: snt la => {} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      apply: ih3 => //. exact: (p_cl ih1) la _.
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

Lemma beta_expansion A B s t :
  SN t -> L A s.[t/] ->
  L A (tmapp (tmlam B s) t).
Proof with eauto.
  move=> snt h. have sns := sn_subst (L_sn h).
  elim: sns t snt h => {} s sns ih1 t. elim=> {} t snt ih2 h.
  apply: L_nc => // u st. inv st => //.
  - inv H2. apply: ih1 => //. apply: L_cl h _. exact: step_subst.
  - apply: ih2 => //. apply: L_cl_star h _. exact: red_beta.
Qed.

(* The fundamental theorem. *)

Theorem soundness Gamma s A :
  has_type_db Gamma s A -> forall sigma,
    EL Gamma sigma -> L A s.[sigma].
Proof with eauto using L_sn.
  elim=> {Gamma s A} [|Gamma A B s _ ih sigma EL|Gamma A B s t _ ih1 _ ih2 sigma HEL]
    ;asimpl...    
  - move=> t h.
    apply: beta_expansion... asimpl. apply: ih... by case.
  - specialize (ih1 _ HEL). specialize (ih2 _ HEL).
    unfold L in ih1. fold L in ih1. apply ih1. apply ih2.
Qed.

Corollary type_L E s T : has_type_db E s T -> L T s.
Proof.
  move=> ty. move: (@soundness E s T ty) => h.
  specialize (h ids). asimpl in h. apply: h => x B. exact: L_var.
Qed.

Corollary strong_normalization E s T : has_type_db E s T -> SN s.
Proof.
  move=>/type_L/L_sn. apply.
Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Ssr")) *)
(* End: *)