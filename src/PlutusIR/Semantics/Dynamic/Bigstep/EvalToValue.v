Require Import PlutusCert.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.


Lemma compute_defaultfun__to_value : forall t v,
    fully_applied t ->
    compute_defaultfun t = Datatypes.Some v ->
    value v.
Proof with (try discriminate).
  intros.
  destruct t...
  simpl in H0.
  all: destruct t1...
  all: try destruct t1_1...
  all: try destruct t1_1_1...
  2: {
    destruct t1_1_1...
    destruct d...
    destruct t1_1_2...
    destruct s...
    destruct u...
    destruct v0...
    inversion H; subst.
    inversion H6; subst.
    inversion H9; subst.
    destruct u.
    all: inversion H0; subst.
    all: eauto.
  }
  all: try destruct d...
  all: try destruct t1_1_2...
  all: try destruct s...
  all: try destruct u...
  all: try destruct v0...
  all: try destruct t1_2...
  all: try destruct s...
  all: try destruct u0...
  all: try destruct v0...
  all: try destruct t2...
  all: try destruct s...
  all: try destruct u1...
  all: try destruct v0...
  all: try (inversion H0; subst)...
  all: autounfold.
  all: try solve [constructor].
  all: try destruct u...
  all: try (inversion H0; subst)...
  all: autounfold.
  all: try constructor.
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
    subst.
    inversion H1.
  - (* E_NeutralBuiltin *)
    destruct f...
    all: constructor...
    all: constructor...
    all: try solve [intros Hcon; inversion Hcon].
    all: unfold arity...
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
