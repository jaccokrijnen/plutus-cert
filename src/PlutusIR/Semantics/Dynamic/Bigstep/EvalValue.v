Require Import PlutusCert.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Lia.

Lemma eval_value : 
  (forall v, value v -> v =[0]=> v) /\
  (forall n v, neutral_value n v -> v =[0]=> v).
Proof with (autounfold; (eauto || (try lia))).
  apply value__multind.
  all: intros.
  all: try solve [constructor; eauto].
  - inversion H; subst...
  - inversion H2; subst.
    all: econstructor...
    all: econstructor...
    all: econstructor...
    all: eapply neutral_value__monotone...
  - inversion H; subst.
    all: econstructor...
    all: econstructor...
    all: econstructor...
    all: eapply neutral_value__monotone...
Qed.

Corollary eval_value__value : forall v,
    value v ->
    v =[0]=> v.
Proof. apply eval_value. Qed.

Corollary eval_value__neutral_value : forall n v,
  neutral_value n v ->
  v =[0]=> v.
Proof. apply eval_value. Qed.