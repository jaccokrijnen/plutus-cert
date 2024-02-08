Require Import PlutusCert.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.
From PlutusCert Require Import Util.Tactics.


Lemma compute_defaultfun__to_value : forall t v,
    compute_defaultfun t = Datatypes.Some v ->
    value v.
Proof with (try discriminate).
  intros.
  destruct t...
  simpl in H.

  all: destruct_match_hypo...
  all: try destruct_match_hypo...
  all: try destruct_match_hypo...
  2: {
    repeat destruct_match_hypo...
    inversion H; subst.
    constructor.
  }
  all: repeat
    destruct_match_hypo.
  all: try (inversion H; subst)...
  all: autounfold.
  all: try solve [constructor].
Qed.

Lemma eval_to_value :
    (forall t v k, t =[k]=> v -> value v) /\
    (forall t v k, t =[k]=>nr v -> value v) /\
    (forall bs0 t v k, t =[k]=>r v WITH bs0 -> value v).
Proof with (eauto with hintdb__eval_no_error).
  apply eval__multind.
  all: intros.
  all: eauto using compute_defaultfun__to_value.
  - (* E_IWrap *)
    inversion H0...
Qed.

Corollary eval_to_value__eval : forall t v k,
    t =[k]=> v ->
    value v.
Proof. apply eval_to_value. Qed.

Corollary eval_to_value__eval_bindings_nonrec : forall t v k,
    t =[k]=>nr v ->
    value v.
Proof. apply eval_to_value. Qed.

Corollary eval_to_value__eval_bindings_rec : forall bs0 t v k,
    t =[k]=>r v WITH bs0 ->
    value v.
Proof. apply eval_to_value. Qed.
