Require Import PlutusCert.PlutusIR.

Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.


Lemma compute_defaultfun__result : forall t v,
    fully_applied t ->
    compute_defaultfun t = Datatypes.Some v ->
    result v.
Proof with (try discriminate).
  intros.
  destruct t...
  (* TODO: redo for new built-ins *)
  admit.
  (*
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
  *)
Admitted.


Lemma compute_defaultfun__result' : forall t v,
    fully_applied t ->
    compute_defaultfun t = Datatypes.Some v ->
    result' v.
Admitted.


Lemma eval_builtin_partial__result :
  forall t r, t =η=> r -> result r
.
Admitted.

Lemma eval_to_result :
    (forall t v k, t =[k]=> v -> result v) /\
    (forall t v k, t =[k]=>nr v -> result v) /\
    (forall bs0 t v k, t =[k]=>r v WITH bs0 -> result v).
Proof with (eauto with hintdb__eval_no_error).
  apply eval__multind.
  all: intros.
  all: eauto using compute_defaultfun__result...
  - (* E_IWrap *)
    inversion H0...
  - (* Constr*)
    inversion H2.
    + apply R_Constr.
      constructor...
  - (* Builtin Apply Partial *)
    eauto using eval_builtin_partial__result. 
  - (* Builtin TyInst Partial*)
    eauto using eval_builtin_partial__result. 
  - (* Builtin TyInst Partial*)
    eauto using eval_builtin_partial__result. 
Qed.

Lemma eval_to_result' :
    (forall t v k, t =[k]=> v -> result' v) /\
    (forall t v k, t =[k]=>nr v -> result' v) /\
    (forall bs0 t v k, t =[k]=>r v WITH bs0 -> result' v).
Admitted.

Corollary eval_to_result__eval : forall t v k,
    t =[k]=> v ->
    result v.
Proof. apply eval_to_result. Qed.

Corollary eval_to_result'__eval : forall t v k,
    t =[k]=> v ->
    result' v.
Proof. apply eval_to_result'. Qed.

Corollary eval_to_result__eval_bindings_nonrec : forall t v k,
    t =[k]=>nr v ->
    result v.
Proof. apply eval_to_result. Qed.


Corollary eval_to_result'__eval_bindings_nonrec : forall t v k,
    t =[k]=>nr v ->
    result' v.
Proof. apply eval_to_result'. Qed.

Corollary eval_to_result__eval_bindings_rec : forall bs0 t v k,
    t =[k]=>r v WITH bs0 ->
    result v.
Proof. apply eval_to_result. Qed.

Corollary eval_to_result'__eval_bindings_rec : forall bs0 t v k,
    t =[k]=>r v WITH bs0 ->
    result' v.
Proof. apply eval_to_result'. Qed.
