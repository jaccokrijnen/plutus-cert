Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.

From Coq Require Import Lia.


Lemma compute_defaultfun__to_value : forall t v,
    compute_defaultfun t = Datatypes.Some v ->
    value v.
Proof with (try discriminate).
  intros.
  destruct t...
  simpl in H.
  destruct d...
  all: destruct l...
  all: destruct t...
  all: destruct s...
  all: destruct u...
  all: destruct v0...
  all: destruct l...
  all: try destruct t...
  all: try destruct s...
  all: try destruct u0...
  all: try destruct v0...
  all: try destruct l...
  all: try solve [inversion H; subst; constructor].
  destruct t...
  destruct s...
  destruct u1...
  destruct v0...
  destruct l...
  inversion H. subst.
  constructor.
Qed.

Definition P_eval (t v : Term) (k : nat) := value v.
Definition P_eval_bindings_nonrec (t v : Term) (k : nat) := value v.
Definition P_eval_bindings_rec (bs0 : list Binding) (t v : Term) (k : nat) := value v.
#[export] Hint Unfold P_eval P_eval_bindings_nonrec P_eval_bindings_rec : core.

Lemma eval_to_value : forall t v k,
    t =[k]=> v -> value v.
Proof.
  eapply eval__ind with (P := P_eval) (P0 := P_eval_bindings_nonrec) (P1 := P_eval_bindings_rec); 
    intros; autounfold.
  - assumption.
  - assumption.
  - apply V_TyAbs.
  - apply V_LamAbs.
  - assumption.
  - apply V_Constant.
  - apply V_ExtBuiltin.    
    destruct f.
    all: simpl; eauto.
  - apply V_ExtBuiltin. 
    assumption.
  - eapply compute_defaultfun__to_value. 
    eassumption.
  - assumption.
  - apply V_If. 
  - apply V_IfTyInst.
  - apply V_IfCondition.
  - apply V_IfThenBranch.
  - assumption.
  - assumption.
  - assumption.
  - apply V_Error.
  - apply V_IWrap. apply H0.
  - inversion H0; subst. assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.