From PlutusCert Require Import STLC_named.
From PlutusCert Require Import Normalisation_STLC_named.
From PlutusCert Require Import SN_F.
From PlutusCert Require Import ARS.
From PlutusCert Require Import named_DB_iso.
From Autosubst Require Import Autosubst.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
From Equations Require Import Equations.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.

Module N := STLC_named.

(* Monad maybe*)
(* Define the bind function for option type *)
Definition bind {A B : Type} (xx : option A) (f : A -> option B) : option B :=
  match xx with
  | None => None
  | Some a => f a
  end.

(* Define an infix operator for bind *)
Infix ">>=" := bind (at level 50, left associativity).

Fixpoint namestep (t : term) : option term :=
    match t with
    | tmvar X => None
    | tmapp s t => 
        if is_normal s then
            if is_normal t then
                match s with
                | tmlam X A s' => Some (substituteTCA X t s')
                | _ => None
                end
            else namestep t >>= fun t' => Some (tmapp s t')
        else namestep s >>= fun s' => Some (tmapp s' t)
    | tmlam X A s => (* step' s >>= _ does the normality check for us implicitly*)
        namestep s >>= fun s' => Some (tmlam X A s')
    end.

  (* toDB instead of toDB': bad proof smell
  Exercise to make the problem clear:
  revAcc : List A -> List A -> List A
    revAcc [] acc = acc
    revAcc (x :: xs) acc = revAcc xs (x :: acc)

    reverse : List A -> List A
    reverse xs = revAcc xs []

    Proving something about reverse often is problematic, you need to prove something over revAcc.

  
  *)

(* Adding unused free variables to the "toDeBruijn" conversion 
    preserves stepping
    This does cause some renaming???
    *)
Lemma weaken_fv : forall t t' s fv fv',
  step (toDB' t fv) (toDB' t' fv') ->
  step (toDB' t (s:: (List.remove String.string_dec s fv))) (toDB' t' (s:: List.remove String.string_dec s fv')).
Proof.
Admitted.

Lemma weaken_fv' : forall t t' ss fv fv',
  step (toDB' t fv) (toDB' t' fv') ->
  step (toDB' t (ss ++ fv)) (toDB' t' (ss ++ fv')).
Proof.
Admitted.

Lemma weaken_fv'' : forall t t' ss fv fv',
  step (toDB' t fv) (toDB' t' fv') ->
  step (toDB' t (fv ++ ss)) (toDB' t' (fv' ++ ss)).
Proof.
Admitted.

Lemma step_preserves_freevars : forall t t' fv_t,
  N.ftv t = fv_t -> namestep t = Some t' -> N.ftv t' = fv_t.
Proof.
Admitted.

(* ftv in substTCA x t s never contains "x" (unless t contains "x"???)*)
Eval compute in (toDB' (N.tmlam "x" tp_base (N.tmvar "z")) ("x"::"y"::["z"])).
Eval compute in (toDB' (N.tmlam "w" tp_base (N.tmvar "x")) ("x"::["y"])).
Eval compute in ((D.tmlam D.tp_base (D.tmvar 1)).[D.tmvar 0/]).
Eval compute in ((D.tmlam D.tp_base (D.tmvar 1)).[(toDB' (N.tmapp (tmvar "y") (tmvar "z")) ["y";"z"])/]).
Eval compute in ((D.tmlam D.tp_base (D.tmapp (D.tmvar 1) (D.tmvar 8))).[(D.tmvar 12)/]).


Lemma uhm2 :
  substituteTCA "x" (N.tmvar "z") (N.tmlam "y" (N.tp_base) (N.tmapp (N.tmvar "x") (N.tmvar "w"))) = N.tmvar "g".

Lemma uhm :
  (D.tmlam D.tp_base (D.tmapp (D.tmvar 1) (D.tmvar 8))).[(D.tmvar 12)/] = D.tmvar 1.
Proof.
  simpl.
  unfold up.
  
  
  
  (* unfold ">>>". *)
  unfold ".:".
  unfold ">>>".
  
  simpl.
  

Lemma toDB'subst : forall x t s,
  toDB' (substituteTCA x t s) (N.ftv (substituteTCA x t s)) = 
    (toDB' s (x :: List.remove string_dec x (N.ftv (substituteTCA x t s)))).[(toDB' t (N.ftv (substituteTCA x t s)))/].
Proof.
  intros x t s.
  remember (N.ftv (substituteTCA x t s)) as fvs.
  induction s.
  - rewrite substituteTCA_equation_1.
    destruct (x =? s) eqn:Hx; admit.
   
Admitted.

(* If a named STLC term steps, then its corresponding DeBruijn term steps*)
Lemma namestep_implies_step_nd : forall t t',
  namestep t = Some t' -> 
  SN_F.step (toDB' t (N.ftv t)) (toDB' t' (N.ftv t')).
Proof. 
    (* intros t t' Hns.
    generalize dependent t'.
    induction t.
    - intros t' Hns. discriminate Hns.
    - intros t' Hns. 
      inversion Hns.
      unfold bind in H0.
      destruct (namestep t0) eqn:Hstep in H0; try discriminate.
      specialize (IHt t1 Hstep).
      inversion H0.
      simpl.
      apply SN_F.step_abs.
      apply weaken_fv with (s := s) in IHt.
      assumption.
    - intros t' Hns.
      inversion Hns.
      destruct (is_normal t1) eqn:Hnorm1.
      + destruct (is_normal t2) eqn:Hnorm2.
        * destruct t1 eqn:Ht1; try discriminate.
          inversion Hnorm1.
          inversion H0.
          subst...
          simpl.
          remember (List.app (List.remove String.string_dec s (N.ftv t0)) 
(N.ftv t2)) as fvs.
          remember (toDB' t0 (s :: fvs)) as t0'.
          remember (toDB' t2 fvs) as t2'.
          assert (N.ftv (substituteTCA s t2 t0) = fvs).
          {
            admit.
          }
          rewrite -> H.
          assert (toDB' (substituteTCA s t2 t0) fvs = t0'.[t2'/]).
          {
            rewrite -> Heqt0'.
            rewrite -> Heqt2'.
            rewrite <- H.
            apply toDB'subst.
          }
          rewrite -> H2.
          apply SN_F.step_beta.
        * unfold bind in H0.
          destruct (namestep t2) eqn:Hstep in H0; try discriminate.
          inversion H0.
          subst...
          simpl.
          assert (N.ftv t = N.ftv t2).
          {
            apply step_preserves_freevars with (t := t2); [reflexivity|assumption].
          }
          rewrite -> H.
          apply SN_F.step_appR.
          specialize (IHt2 t Hstep).
          rewrite -> H in IHt2.
          apply weaken_fv' with (ss := N.ftv t1) in IHt2.
          assumption.

      + unfold bind in H0.
        destruct (namestep t1) eqn:Hstep in H0; try discriminate.
        inversion H0.
        subst...
        simpl.
        assert (N.ftv t = N.ftv t1).
          {
            apply step_preserves_freevars with (t := t1); [reflexivity|assumption].
          }
        rewrite -> H.
        apply SN_F.step_appL.
        specialize (IHt1 t Hstep).
        rewrite -> H in IHt1.
        apply weaken_fv'' with (ss := N.ftv t2) in IHt1.
        assumption. *)
Admitted.
    
    
    

Definition step_with_proof (t : N.term) : option {t' : N.term | SN_F.step (toDB' t (N.ftv t)) (toDB' t' (N.ftv t'))} :=
  match namestep t with
  | None => fun _ => None
  | Some t' => fun Heq => (* Doing this function syntax thing to be able to use the equality hypothesis *)
      let H_step := namestep_implies_step_nd t t' Heq in
      Some (exist _ t' H_step)
  end eq_refl.

Fixpoint normalizer' (t : N.term) (H_sn : SN (toDB' t (N.ftv t))) : (forall t, option {t' | SN_F.step (toDB' t (N.ftv t)) (toDB' t' (N.ftv t'))}) -> N.term :=
    fun stepper => match stepper t with
    | None => t
    | Some (exist _ t' H_step) => match H_sn with
        | SNI f => normalizer' t' (f (toDB' t' (N.ftv t')) H_step) stepper
        end
end.

(* Step t according to step' until we reach a value, i.e. normalise it*)
Definition normalizer (t : N.term) (H_sn : SN (toDB' t (N.ftv t))) : N.term :=
    normalizer' t H_sn step_with_proof.