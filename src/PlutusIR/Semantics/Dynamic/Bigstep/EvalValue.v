Require Import PlutusCert.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Lia.

Lemma eval_value : forall v, value v -> v =[0]=> v.
Proof with (autounfold; (eauto || (try lia))).
  apply value__ind.
  all: intros.
  all: try solve [constructor; eauto].
Qed.
