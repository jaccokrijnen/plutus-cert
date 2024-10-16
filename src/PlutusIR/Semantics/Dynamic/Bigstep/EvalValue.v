Require Import PlutusCert.PlutusIR.

Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Lia.

Lemma eval_value :
  forall v, value v -> v =[0]=> v.
Proof with (autounfold; (eauto || (try lia))).
  apply value__ind.
  all: intros.
  all: try solve [constructor; eauto].
  (* Constr*)
  - induction vs.
    + constructor.
    + inversion H. inversion H0. subst.
      eapply E_Constr_cons with (k_t := 0) (k_ts := 0)...
Qed.

Corollary eval_value__value : forall v,
    value v ->
    v =[0]=> v.
Proof. apply eval_value. Qed.
