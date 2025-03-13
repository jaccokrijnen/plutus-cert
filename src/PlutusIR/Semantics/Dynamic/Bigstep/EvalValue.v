Require Import PlutusCert.PlutusIR.

Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Lists.List.
Require Import Lia.


Definition Q f t :=
  args_len t < arity f ->
  t =[0]=> t
.

Lemma eval_value__Constr T i vs :
  Forall value vs ->
  Forall (fun t => t =[ 0 ]=> t) vs ->
  Constr T i vs =[ 0 ]=> Constr T i vs
.
Proof.
Admitted.

Lemma eval_value :
  forall v, value v -> v =[0]=> v.
Proof with (autounfold; (eauto || (try lia))).
  apply value__multind with (Q := Q).
  all: intros.
  all: try solve [constructor; eauto].
  - auto using eval_value__Constr.
  - unfold Q in *. auto.
  - (* Apply *)
    unfold Q in *.
    intros H_arity.
    assert (split : 0 = 0 + 0) by auto.
    rewrite split.
    eapply E_Apply_Builtin_Partial...
    apply H2. unfold args_len in *; lia.
  - (* TyInst *)
    unfold Q in *.
    intros H_arity.
    eapply E_TyInst_Builtin_Partial...
    unfold args_len in *.
    apply H0; lia.
Qed.

Lemma eval_result :
  forall v, result v -> v =[0]=> v.
Proof.
  intros v r.
  destruct r; eauto using eval, eval_value.
Qed.
