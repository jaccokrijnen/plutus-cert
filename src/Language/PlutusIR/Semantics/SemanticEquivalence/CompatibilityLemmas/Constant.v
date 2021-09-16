Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Def.

Require Import Arith.


Lemma RC_compatibility_Constant : forall k u a,
    RC k (Ty_Builtin (Some (TypeIn u))) (Constant (Some (ValueOf u a))) (Constant (Some (ValueOf u a))).
Proof.
  intros k u a.

  split. { apply T_Constant. } 
  split. { apply T_Constant. }

  intros j Hlt__j e_f Hev__e.

  exists e_f, j. split; auto.

  intros. subst.
  inversion Hev__e. subst.
  reflexivity.
Qed.