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

(* See Barendregt 1984*)

(* Ask Richard's pen and paper notes*)
Lemma capmsRename x x' t sigma s :
  ((x', t)::sigma) [[rename x x' s]] = ((x, t)::sigma) [[s]].
Proof. 
  
Admitted.

Definition notKeyIn X (sigma : list (string * term)) : Prop :=
  ~ exists t, lookup X sigma = Some t.

Definition varNotIn X (sigma : list (string * term)) : Prop :=
  notKeyIn X sigma /\ (* X does not appear in the free type variables of any of the values  of tau*)
  ~ In X (List.flat_map (compose ftv snd) sigma).

(* Definitionally, 
  fresh2 creates a fresh variable that is not in 
    any of the keys or values of sigma *)
Lemma freshLemma sigma s :
  varNotIn (fresh2 sigma s) sigma.
Proof. Admitted.

(* TODO: why cant i use list syntax?*)
Lemma composeCapms' X t X' t' s :
  varNotIn X [(X', t')] -> [X := t] ([X' := t'] s) = ((X, t):: cons (X', t') nil) [[s]].
Proof.
  intros HnotIn.
  (* Induction on s?*)
Admitted.

(* Would also work for bigger substs, but not necessary*)
Lemma composeCapms X t sigma s :
  varNotIn X sigma -> [X := t] (sigma [[s]]) = ((X, t) :: sigma) [[s]].
Proof.
Admitted.

(*
  But what if sigma contains x.
  Then RHS will replace this by sigma(x)
  while LHS will replace it by t.
*)
Lemma commute_subst s t sigma x :
  sigma [[ [x := t] s]] = ((x, sigma [[t]])::sigma) [[s]].
Proof.
Admitted.


(* Note: Study: After replacing a variable with something in sigma
  we can still do the same step as we previously could by red s t, hence: true
  Not true in non-deterministic setting.
*)

Lemma step_subst s t : 
  step s t -> forall sigma, step (sigma [[ s ]]) (sigma [[ t ]]).
Proof.
  move => h.
  induction h; intros sigma.
  - rewrite capms_equation_3.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 sigma s) as x'.
    apply step_ebeta.
    rewrite -> composeCapms.
    + rewrite -> capmsRename.
      rewrite commute_subst.
      reflexivity.
    + rewrite Heqx'.
      apply freshLemma.
  - rewrite capms_equation_3.
    rewrite capms_equation_3.
    apply step_appL.
    specialize (IHh sigma).
    assumption.
  - rewrite capms_equation_3.
    rewrite capms_equation_3.
    apply step_appR.
    specialize (IHh sigma).
    assumption.
  - rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 sigma s1) as x_s1.
    remember (fresh2 sigma s2) as x_s2.
    assert (H_xeq: x_s1 = x_s2). {
      (* Problem: Fresh variables get out of sync.
      or maybe not: the ftv in s1 and s2 are the same.
      Stepping does not remove free vars, ftv s1 = ftv s2!
      So fresh2 sigma s1 =?= fresh2 sigma s2:
      I think so, if we have a good fresh2 function
      *)
      admit.
    }
    rewrite H_xeq.
    rename x_s2 into x'.
    apply step_abs.
    assert (sigma [[rename x x' s1]] = ((x, tmvar x')::sigma) [[s1]]).
    {
      (* This is not exactly true, since rename does not create fresh vars and stuff
        But it is "kind of true" , lol.

        So I guess we have to change capms to not unnecessarily rename?
        I would rather not ;) Maybe we can strengthen IHh to include this case.
        Or we change rename to do fresh?
      *)
      admit.
    }
    assert (sigma [[rename x x' s2]] = ((x, tmvar x')::sigma) [[s2]]) by admit.
    specialize (IHh ((x, tmvar x')::sigma)).
    rewrite -> H.
    rewrite -> H0.
    apply IHh.
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
Proof. apply: star_hom => x' y'. intros Hstep. exact: step_subst. Qed.

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
(* NOTE: At first I would expect that it would step on the right hand side (instead of multistep=red)
    but it doesnt because of the following example:
    Let t1 = (\x.x)w and t2 = w (which steps by step_beta)
    Let s = \y. (\z. x) x
    Then [x := t1] s = \y. (\z. t1) t1 = \y. (\z. (\x.x) w) ((\x.x) w)
    And [x := t2] s = \y. (\z. t2) t2 = \y. (\z. w) w

    there is no single step from the first to the second, since we have to perform
    step_beta in two different places.
    *)

(* Should we add the assumption that we are always substing in fresh stuff? *)
(* Fresh with respect to what? *)
Fixpoint mren (rho : list (string * string)) (T : term) : term :=
  match T with
  | tmvar Y => match lookup Y rho with
              | Some Z => tmvar Z
              | None => tmvar Y
              end
  | tmlam Y K1 T_body => let rho' := drop Y rho in (* What if Y in rhs of rho*)
                        tmlam Y K1 (mren rho' T_body)
  | tmapp T1 T2 => tmapp (mren rho T1) (mren rho T2)
end.

Lemma ren_id s : mren nil s = s.
Proof. Admitted.

Lemma red_beta_ren x s t1 t2 rho : step t1 t2 -> red ([x := t1] (mren rho s)) ([x := t2] (mren rho s)).
Proof.
  elim: s rho t1 t2 => [Y|Y K1 T_body IH|T1 IH1 T2 IH2] rho t1 t2 Hstep.
  - unfold mren.
    destruct (lookup Y rho) eqn: Hlookup.
    all: rewrite capms_equation_1.
    all: rewrite capms_equation_1.
    all: simpl.
    (* TODO: The two cases below are identical except for s vs Y*)
    + destruct (string_dec x s).
      * rewrite e.
        unfold lookup.
        rewrite eqb_refl.
        apply star1.
        assumption.
      * unfold lookup.
        destruct (x =? s).
        -- apply star1.
           assumption.
        -- apply starR.
    + destruct (string_dec x Y).
      * rewrite e.
        unfold lookup.
        rewrite eqb_refl.
        apply star1.
        assumption.
      * unfold lookup.
        destruct (x =? Y).
        -- apply star1.
           assumption.
        -- apply starR.
  - simpl.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 [(x, t1)] (mren (drop Y rho) T_body)) as x'.
    remember (fresh2 [(x, t2)] (mren (drop Y rho) T_body)) as x2.
    assert (H_xeq: x' = x2). {
      (* by reduction does not change ftv *)
      admit.
    }
    rewrite <- H_xeq.
    remember (drop Y rho) as rho'.
    apply red_abs.
    assert (rename Y x' (mren rho' T_body) = mren ((Y, x')::rho') T_body).
    {
      (* Only true if Y not in rhs of rho'?
      I think it shouldnt be by some freshness criterium, but even if it is, we can
      do something else. *)
      admit.
    }
    rewrite H.
    apply IH.
    assumption.
  - rewrite capms_equation_3.
    rewrite capms_equation_3.
    apply red_app.
    + apply IH1.
      assumption.
    + apply IH2.
      assumption.
Admitted.

Lemma red_beta x s t1 t2 : step t1 t2 -> red ([x := t1] s) ([x := t2] s).
Proof. 
  move=> h. 
  (* apply red_beta_ren with empty rho*)
  apply red_beta_ren with (rho := nil) (x := x) (s := s) in h.
  rewrite ren_id in h.
  assumption.
Qed.

(* Strong Normalization *)

Notation SN := (sn step).

Lemma sn_closed t s : SN (tmapp s t) -> SN s.
Proof. apply: (sn_preimage (h := tmapp^~t)) => x y. exact: step_appL. Qed.

Lemma sn_subst sigma s : SN (sigma [[s]]) -> SN s.
Proof. apply: sn_preimage => x' y'. intros Hstep. exact: step_subst. Qed.

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