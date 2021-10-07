Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Constant.

Require Import Arith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Lemma compose_map : forall {A B C : Type} (f : A -> B) (g : B -> C),
    map (compose g f) = compose (map g) (map f).
Proof.
  intros.
  apply functional_extensionality.
  induction x.
  - reflexivity.
  - simpl.
    unfold compose.
    simpl.
    f_equal.
    apply IHx.
Qed.

Lemma msubst_ExtBuiltin : forall ss f args,
    msubst_term ss (ExtBuiltin f args) = ExtBuiltin f (map (msubst_term ss) args).
Proof. 
  induction ss; intros.
  - simpl. rewrite map_id. reflexivity.
  - destruct a. simpl.
    replace (fun t0 => msubst_term ss <{ [t / s] t0 }>) with (compose (msubst_term ss) (substitute s t)).
    + rewrite compose_map.
      eapply IHss.
    + unfold compose.
      reflexivity.
Qed.

Lemma msubstA_ExtBuiltin : forall ss f args,
    msubstA_term ss (ExtBuiltin f args) = ExtBuiltin f (map (msubstA_term ss) args).
Proof. 
  induction ss; intros.
  - simpl. rewrite map_id. reflexivity.
  - destruct a. simpl.
    replace (fun t0 => msubstA_term ss <{ [[t / s] t0 }>) with (compose (msubstA_term ss) (substituteA s t)).
    + rewrite compose_map.
      eapply IHss.
    + unfold compose.
      reflexivity.
Qed.

Lemma msubstT_TyFun : forall ss T1 T2,
    msubstT ss (Ty_Fun T1 T2) = Ty_Fun (msubstT ss T1) (msubstT ss T2).
Proof.
  induction ss.
  - reflexivity.
  - intros.
    simpl.
    destruct a.
    apply IHss.
Qed.

Lemma compatibility_ExtBuiltin: forall Delta Gamma f args args' Targs Tr,
    Datatypes.length args <= arity f ->
    (Targs, Tr) = splitTy (lookupBuiltinTy f) ->
    (forall p : Term * Ty, List.In p (List.combine args Targs) -> LR_logically_approximate Delta Gamma (fst p) (fst p) (snd p)) ->
    LR_logically_approximate Delta Gamma (ExtBuiltin f args) (ExtBuiltin f args') (combineTy (List.skipn (Datatypes.length args) Targs) Tr).
Proof with eauto_LR.
  intros Delta Gamma f args args'.
  unfold LR_logically_approximate.
Admitted.