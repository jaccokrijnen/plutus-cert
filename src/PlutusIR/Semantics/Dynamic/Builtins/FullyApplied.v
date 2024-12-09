From Coq Require Import
  Strings.String
.
From PlutusCert Require Import
  PlutusIR
  Values
  Static.Builtins.Signatures
.
Import PlutusNotations.
From Equations Require Import Equations.

(* built-in function that is applied to 0 or more values/types of which the (type) arguments match
   the signature *)
Inductive applied_builtin : DefaultFun -> builtin_sig -> term -> Prop :=
  | BA_Builtin : forall f,
      applied_builtin f (to_sig f) (Builtin f)
  | BA_Apply : forall f sig t v T,
      result v ->
      ~ is_error v ->
      applied_builtin f (BS_Fun T sig) t ->
      applied_builtin f sig (Apply t v)
  | BA_TyInst : forall f t T X K sig,
      applied_builtin f (BS_Forall X K sig) t ->
      applied_builtin f sig (TyInst t T)
  .

Equations applied_args : term -> nat :=
  applied_args (Apply s t) := 1 + applied_args s;
  applied_args (TyInst s T) := 1 + applied_args s;
  applied_args _ := 0
.

Lemma applied_builtin__functional f f' s s' t : applied_builtin f s t -> applied_builtin f' s' t -> f = f' /\ s = s'.
Proof.
  revert f f' s s'.
  induction t.
  all: try solve [intros ? ? ? ?; inversion 1].
  - clear IHt2.
    intros ? ? ? ? H H'.
    inversion H; subst.
    inversion H'; subst.
    specialize (IHt1 _ _ _ _ H6 H9) as [H_f H_s].
    inversion H_s.
    subst.
    split; reflexivity.
  -
    intros ? ? ? ? H H'.
    inversion H; subst.
    inversion H'; subst.
    split; reflexivity.
  -
    intros ? ? ? ? H H'.
    inversion H; subst.
    inversion H'; subst.
    specialize (IHt _ _ _ _ H3 H4) as [H_f H_s].
    inversion H_s.
    subst.
    split; reflexivity.
Defined.

Corollary applied_builtin__functional_sig f f' s s' t : applied_builtin f s t -> applied_builtin f' s' t -> s = s'.
Proof.
  intros.
  eapply proj2.
  eauto using applied_builtin__functional.
Defined.

Ltac contradiction_exists :=
  match goal with
  | H  : { _ & {_ & applied_builtin _ _ ?t}} -> False
  , H' : applied_builtin _ _ ?t
  |- _ => apply H; eexists; eexists; apply H'
  end.

Ltac contradict_diff_sigs :=
  match goal with
  | H1 : applied_builtin ?f ?s ?t
  , H2 : applied_builtin ?f' ?s' ?t
  |- _ => assert (H_absurd : s = s') by eauto using applied_builtin__functional_sig; inversion H_absurd
  end.

Ltac fully_strategy := try solve
  [ right;
    let H := fresh "H" in
    destruct 1 as [ ? [? H] ];
    inversion H;
    (contradiction || contradiction_exists || contradict_diff_sigs)
  ]
.


Lemma applied_builtin_dec t :
   {f & {s & applied_builtin f s t}}  +
  ({f & {s & applied_builtin f s t}} -> False).
Proof with fully_strategy.
  induction t...
  - destruct IHt1 as [[ f [ s H' ]] | ], (result_dec t2), (is_error_dec t2)...
    destruct s eqn:H_s...
    left.
    eauto using applied_builtin.
  - left.
    eauto using applied_builtin.
  - destruct IHt as [[ f [ s H' ]] | ]...
    destruct s eqn:H_s...
    left.
    eauto using applied_builtin.
Defined.

Fixpoint result_ty (s : builtin_sig) : ty :=
  match s with
  | BS_Forall _ _ s => result_ty s
  | BS_Fun _ s => result_ty s
  | BS_Result t => t
  end
.


Definition fully_applied t := exists f, applied_builtin f (BS_Result (result_ty (to_sig f))) t.
Definition partially_applied t :=
  (exists f T sig, applied_builtin f (BS_Fun T sig) t) \/
  (exists f X K sig, applied_builtin f (BS_Forall X K sig) t)
.

Lemma fully_applied_dec t : {fully_applied t} + {~fully_applied t}.
Proof.
  destruct (applied_builtin_dec t) as [ H | H ] .
  - destruct H as [ f [ s H_app ]].
    destruct (builtin_sig_eq_dec s (BS_Result (result_ty (to_sig f)))).
    + subst. left. unfold fully_applied. eauto.
    + right. unfold fully_applied. intro H.
      destruct H as [ ? Hb ].
      match goal with
      | H1 : applied_builtin ?f ?s ?t
      , H2 : applied_builtin ?f' ?s' ?t
      |- _ => assert (H_absurd : f = f' /\ s = s') by eauto using applied_builtin__functional
      end.
      destruct H_absurd.
      subst.
      contradiction.
  - right.
    destruct 1 as [ f Happ ].
    apply H.
    eauto.
Defined.

Lemma fully__partially t:
  fully_applied t ->
  ~ partially_applied t.
Admitted.

Lemma not_fully__partially f sig t :
  applied_builtin f sig t ->
  ~ fully_applied t ->
  partially_applied t
.
Admitted.

Lemma partially_applied_dec t : {partially_applied t} + {~partially_applied t}.
  destruct (applied_builtin_dec t) as [ H | H ] .
  - destruct (fully_applied_dec t).
    + eauto using fully__partially.
    + left.
      destruct H as [ f [ s H_app ]].
      eauto using not_fully__partially.
  - right.
    inversion 1.
    + admit.
    + admit.
Admitted.

