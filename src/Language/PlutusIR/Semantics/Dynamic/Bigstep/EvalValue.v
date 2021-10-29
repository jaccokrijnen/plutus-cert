Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Lia.

Definition P_value (v : Term) := v =[0]=> v.
Definition P_neutral_value (n : nat) (nv : Term) := nv =[0]=> nv.
#[export] Hint Unfold P_value P_neutral_value : core.

Lemma eval_value : 
  (forall v, value v -> P_value v) /\
  (forall n v, neutral_value n v -> P_neutral_value n v).
Proof with (autounfold; (eauto || (try lia))).
  apply value__multind.
  all: intros.
  all: autounfold.
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