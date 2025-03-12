Require Import PlutusCert.PlutusIR.

Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Lia.

Lemma eval_result :
  forall v, result v -> v =[0]=> v.
Proof with (autounfold; (eauto || (try lia))).
  apply result__ind.
  all: intros.
  all: try solve [constructor; eauto].
  (* Constr*)
  - induction vs.
    + constructor.
    + inversion H. inversion H0. subst.
      eapply E_Constr_cons with (k_t := 0) (k_ts := 0)...
Qed.

Lemma eval_result' :
  forall v, result' v -> v =[0]=> v.
Admitted.

Corollary eval_result__result : forall v,
    result v ->
    v =[0]=> v.
Proof. apply eval_result. Qed.

Corollary eval_result'__result' : forall v,
    result' v ->
    v =[0]=> v.
Admitted.
