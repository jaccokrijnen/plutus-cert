Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Def.

Lemma eval_preserves_termination : forall t v,
    terminates t ->
    t ==> v ->
    terminates v.
Proof. intros. exists v. apply eval_value. eapply eval_to_value. apply H0. Qed.

Lemma eval_preserves_R_left : forall k T t1 v1 t2,
    terminates t1 ->
    t1 ==> v1 ->
    R k T t1 t2 ->
    R k T v1 t2.
Proof. Abort.

Lemma eval_preserves_R_right : forall k T t1 t2 v2,
    terminates t1 ->
    t2 ==> v2 ->
    R k T t1 t2 ->
    R k T t1 v2.
Proof. Abort.

Lemma eval_preserves_R : forall k T t1 v1 t2 v2,
    terminates t1 ->
    t1 ==> v1 ->
    t2 ==> v2 ->
    R k T t1 t2 ->
    R k T v1 v2.
Proof.
  intros k T t1 v1 t2 v2 Hterm1 Hev1 Hev2 R.
  (*
  apply eval_preserves_R_left with t1; auto.
  apply eval_preserves_R_right with t2; auto.
  *)
Abort.

Lemma eval_preserved_R_left : forall k T t1 v1 t2,
    emptyContext |-+ t1 : T ->
    terminates t1 ->
    t1 ==> v1 ->
    R k T v1 t2 ->
    R k T t1 t2.
Proof. Abort.

Lemma eval_preserved_R_right : forall k T t1 t2 v2,
    emptyContext |-+ t2 : T ->
    terminates t1 ->
    t2 ==> v2 ->
    R k T t1 v2 ->
    R k T t1 t2.
Proof. Abort.

Lemma eval_preserved_R : forall k T t1 t2 v1 v2,
    emptyContext |-+ t1 : T ->
    emptyContext |-+ t2 : T ->
    terminates t1 ->
    t1 ==> v1 ->
    t2 ==> v2 ->
    R k T v1 v2 ->
    R k T t1 t2.
Proof.
  intros k T t1 t2 v1 v2 Htyp_t1 Htyp_t2 Hterm1 Hev1 Hev2 R.
  (*
  apply eval_preserved_R_left with v1; auto.
  apply eval_preserved_R_right with v2; auto.
  apply eval_preserves_termination with t1; auto.
  *)
Abort.