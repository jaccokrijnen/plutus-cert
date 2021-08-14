Require Import PlutusCert.Language.PlutusIR.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Import NamedTerm.

Definition P ctx t1 T := forall t2, CNR_Term t1 t2 -> ctx |-+ t2 : T.

Theorem CNR_Term__preserves_typing : forall ctx t1 T,
    ctx |-+ t1 : T ->
    P ctx t1 T.
Proof.
  eapply has_type_rec.
  - unfold P. intros. inversion X. subst. Axiom cheat : forall P, P. apply cheat. apply cheat.
  - intros. apply cheat.
  - intros. subst. unfold P. intros. inversion X. subst. inversion X0. subst. apply T_Var. auto.
Abort.

