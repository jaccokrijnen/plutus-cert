
From Equations Require Import Equations.
Require Import Coq.Lists.List.
Local Open Scope list_scope.

Require Import Lia.

Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Ascii.

From PlutusCert Require Import port_plut util Util.List. (* I don't understand why we need this for ftv defintion*)

Inductive BType := L | F. (* Lam or Forall*)

(** Types *)
Inductive term :=
  | tmvar : string -> term
  | tmlam : BType -> string -> type -> term -> term
  | tmapp : term -> term -> term
.

(** Substitutions *)
Function ftv (T : term) : list string :=
    match T with
    | tmvar X =>
        [X]
    | tmlam B X K1 T' =>
        remove string_dec X (ftv T')
    | tmapp T1 T2 =>
        ftv T1 ++ ftv T2
    end.

Fixpoint btv (T : term) : list string :=
    match T with
    | tmvar X =>
        []
    | tmlam B X K1 T' =>
      X :: btv T'
    | tmapp T1 T2 =>
        btv T1 ++ btv T2
    end.

(* Bound and free type variables *)
Fixpoint tv (s : term) : list string :=
  match s with
  | tmvar x => x::nil
  | tmlam B x A s => x :: tv s
  | tmapp s t => tv s ++ tv t
  end.

(** * Capture-avoiding substitution of types *)

Fixpoint tv_keys_env (sigma : list (string * term)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => x :: (tv t) ++ (tv_keys_env sigma')
  end.

Definition fresh2 (sigma : list (string * term)) (T : term) : string :=
  "a" (* new*)
  ++ String.concat EmptyString (
    tv_keys_env sigma ++ tv T
  ).

Definition fresh (X : string) (U T : term) : string :=
  "a" ++ X ++ (String.concat EmptyString (ftv U)) ++ (String.concat EmptyString (ftv T)).

Lemma fresh__X : forall X U T,
    X <> fresh X U T.
Proof with eauto.
  intros. intros Hcon.
  induction X; induction (ftv U); induction (ftv T).
  all: simpl in Hcon.
  all: inversion Hcon; subst...
Qed.

Lemma fresh__S : forall X U T,
    ~ In (fresh X U T) (ftv U).
Proof. Abort.

Lemma fresh__T : forall X U T,
    ~ In (fresh X U T) (ftv T).
Proof. Abort.

Fixpoint rename (X Y : string) (T : term) :=
  match T with
  | tmvar Z =>
      if X =? Z then tmvar Y else tmvar Z
  | tmlam B Z K T0 =>
      if X =? Z then tmlam B Z K T0
      else tmlam B Z K (rename X Y T0)
  | tmapp T1 T2 =>
      tmapp (rename X Y T1) (rename X Y T2)
  end.

(* Size of a term *)

Fixpoint size (T : term) : nat :=
  match T with
  | tmvar Y => 1
  | tmlam B bX K T0 => 1 + size T0
  | tmapp T1 T2 => 1 + size T1 + size T2
  end.


Lemma rename_preserves_size : forall T X Y,
    size T = size (rename X Y T).
Proof.
  unfold rename.
  induction T; intros; simpl; eauto.
  - destruct (X =? s); eauto.
  - destruct (X =? s); simpl; eauto.
Qed.

Equations? substituteTCA (X : string) (U T : term) : term by wf (size T) :=
  substituteTCA X U (tmvar Y) =>
      if X =? Y then U else tmvar Y ;
  substituteTCA X U (@tmlam B Y K T) =>
      if X =? Y
        then
          @tmlam B Y K T
        else
          if existsb (String.eqb Y) (ftv U)
            then
              let Y' := fresh2 ((Y, tmvar Y)::(X, U)::nil) T in
              let T' := rename Y Y' T in
              @tmlam B Y' K (substituteTCA X U T')
            else
              @tmlam B Y K (substituteTCA X U T) ;
  substituteTCA X U (tmapp T1 T2) =>
      tmapp (substituteTCA X U T1) (substituteTCA X U T2)
  .
Proof.
  all: try solve
    [ lia
    || replace T' with (rename Y Y' T); eauto; rewrite <- rename_preserves_size; eauto
    ].
Qed.


Inductive step_nd : term -> term -> Type :=
| step_beta_d (B : BType) (x : string) (A : type) (s t : term) :
  (* This allows for more steps then should be allowed.
      e.g. tmapp (forall B x A s) t) will now beta reduce.

      But that is no problem! As long as step_nd allows all steps that step_plut allows.
  *)
    step_nd (tmapp (@tmlam B x A s) t) (substituteTCA x t s) (* capture avoiding conservative substitutions *)
| step_appL_d s1 s2 t :
    step_nd s1 s2 -> step_nd (tmapp s1 t) (tmapp s2 t)
| step_appR_d s t1 t2 :
    step_nd t1 t2 -> step_nd (tmapp s t1) (tmapp s t2)
| step_abs_d B x A s1 s2 :
    step_nd s1 s2 -> step_nd (@tmlam B x A s1) (@tmlam B x A s2).

Set Implicit Arguments.

(** Substitutions *)

(* from plut to annotated stlc*)
Fixpoint f (t : term_plut) : term :=
  match t with
  | plutvar x => tmvar x
  | plutlam x A t => @tmlam L x A (f t)
  | plutforall x A t => @tmlam F x A (f t)
  | plutapp t1 t2 => tmapp (f t1) (f t2)
  end.

Require Import Coq.Program.Equality.

Lemma f_preserves_rename s fr T :
  rename s fr (f T) = f (port_plut.rename s fr T).
Proof.
  induction T.
  - simpl.
    destr_eqb_eq s s0.
    + simpl. auto.
    + simpl. auto.
  - simpl.
    destr_eqb_eq s s0.
    + simpl. auto.
    + simpl. f_equal. auto.
  - simpl.
    destr_eqb_eq s s0.
    + simpl. auto.
    + simpl. f_equal; auto.
  - simpl.
    f_equal; auto.
Qed.

Lemma f_preserves_ftv T :
  ftv (f T) = port_plut.ftv T.
Proof.
  induction T; simpl; try f_equal; auto.
Qed.

Lemma f_preserves_tv T :
  tv (f T) = port_plut.tv T.
Proof.
  induction T; simpl; try f_equal; auto.
Qed.

Lemma f_preserves_fresh2 x y s s' T :
  fresh2 ((x, f s)::(y, f s')::nil) (f T) = port_plut.fresh2 ((x, s)::(y, s')::nil) T.
Proof.
  simpl.
  unfold fresh2.
  unfold port_plut.fresh2.
  rewrite f_preserves_tv.
  assert (Htv_keys_env: (tv_keys_env
  [(x, f s); (y, f s')] = port_plut.tv_keys_env [(x, s); (y, s')])).
  {
    unfold tv_keys_env.
    unfold port_plut.tv_keys_env.
    f_equal.
    rewrite f_preserves_tv.
    f_equal.
    rewrite f_preserves_tv.
    f_equal.
  }
  rewrite Htv_keys_env.
  reflexivity.
Qed.

Require Import Coq.Arith.Wf_nat.

Lemma f_preserves_substituteTCA X U T :
  (f (port_plut.substituteTCA X U T)) = (substituteTCA X (f U) (f T)).
Proof.
  remember (f T) as fT.
  remember (size fT) as n.
  generalize dependent fT.
  generalize dependent T.
  induction n using lt_wf_ind.
  intros.
  dependent induction fT; subst.
  + induction T; subst; inversion HeqfT; subst.
    autorewrite with substituteTCA.
    destr_eqb_eq X s0; auto.
  + induction T; subst; inversion HeqfT; subst.
    * autorewrite with substituteTCA.
      destr_eqb_eq X s0; eauto.
      rewrite <- (f_preserves_ftv).
      destruct (existsb (String.eqb s0) (ftv (f U))) eqn:Heq.
      -- 
          simpl.
          remember (fresh2 _ _) as fr.
          remember (port_plut.fresh2 _ _) as fr'.
          assert (Hfr_pres: fr' = fr).
          {
            subst.
            symmetry.
            assert (Hfpluvar: f (plutvar s0) = tmvar s0) by auto.
            rewrite <- Hfpluvar.
            rewrite f_preserves_fresh2.
            reflexivity.
          }
          rewrite Hfr_pres.
          f_equal.
          ++ eapply H; eauto.
            ** rewrite <- rename_preserves_size.
               simpl.
               lia.
            ** apply f_preserves_rename.
      -- simpl.
          f_equal.
          eapply H; eauto. simpl. lia.



      (* TODO: EXACTLY IDENTICAL TO ABOVE*)
      * autorewrite with substituteTCA.
      destr_eqb_eq X s0; eauto.
      rewrite <- (f_preserves_ftv).
      destruct (existsb (String.eqb s0) (ftv (f U))) eqn:Heq.
      -- 
          simpl.
          remember (fresh2 _ _) as fr.
          remember (port_plut.fresh2 _ _) as fr'.
          assert (Hfr_pres: fr' = fr).
          {
            subst.
            symmetry.
            assert (Hfpluvar: f (plutvar s0) = tmvar s0) by auto.
            rewrite <- Hfpluvar.
            rewrite f_preserves_fresh2.
            reflexivity.
          }
          rewrite Hfr_pres.
          f_equal.
          ++ eapply H; eauto.
            ** rewrite <- rename_preserves_size.
               simpl.
               lia.
            ** apply f_preserves_rename.
      -- simpl.
          f_equal.
          eapply H; eauto. simpl. lia.

        (* END TODO*)

  + induction T; subst; inversion HeqfT; subst.
    
    autorewrite with substituteTCA.
    simpl.
    f_equal; eauto.
    * eapply H; auto. simpl. lia.
    * eapply H; auto. simpl. lia.
Qed.

        
Theorem f_preserves_step s s' :
  step_plut s s' -> step_nd (f s) (f s').
Proof.
  intros H.
  induction H; simpl; eauto.
  - rewrite f_preserves_substituteTCA.
    constructor.
  - constructor. assumption.
  - constructor. assumption.
  - constructor. assumption.
  - constructor. assumption.
Qed.

Inductive sn {X : Type} {e : X -> X -> Type } x : Type :=
| SNI : (forall y, e x y -> sn y) -> sn x.

Lemma sn_preimage2 {e2 : term_plut -> term_plut -> Type} {e : term -> term -> Type} (h : term_plut -> term) (x : term_plut) :
  (forall x y, e2 x y -> e (h x) (h y)) -> @sn term e (h x) -> @sn term_plut e2 x.
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
  
  specialize (X (h y)).
  rewrite <- eqn in C.
  eapply X.
  - assumption.
  - exact A.
  - reflexivity.
Qed.

(* todo: well kinded assumption.
  So we need to convert that from the step_plut one.
  if s is plut_well_kinded, then (f s) is nd_well_kinded
 *)
Theorem sn_step_nd : forall s, @sn term step_nd s.
Admitted.

Theorem sn_step_plut : forall s, @sn term step_nd (f s) -> @sn term_plut step_plut s.
Proof.
  intros s.
  eapply @sn_preimage2 with (h := f) (e2 := step_plut) (e := step_nd).
  apply f_preserves_step.
Qed.

Corollary sn_step_plut2 : forall s, @sn term_plut step_plut s.
Proof.
  intros s.
  eapply sn_preimage2 with (h := f).
  apply f_preserves_step.
  apply sn_step_nd.
Qed.