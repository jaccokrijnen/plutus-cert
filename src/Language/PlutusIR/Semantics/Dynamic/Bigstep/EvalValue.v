Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.
Require Import PlutusCert.Util.

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
    2,3 : eapply neutral_value__monotone...
    apply lt_nat_lt.
    apply lt_nat_lt in H4...
  - inversion H; subst.
    all: econstructor...
    all: econstructor...
    all: econstructor...
    2,3: eapply neutral_value__monotone...
    apply lt_nat_lt.
    apply lt_nat_lt in H1...
Qed.

Corollary eval_value__value : forall v,
    value v ->
    v =[0]=> v.
Proof. apply eval_value. Qed.

Corollary eval_value__neutral_value : forall n v,
  neutral_value n v ->
  v =[0]=> v.
Proof. apply eval_value. Qed.
