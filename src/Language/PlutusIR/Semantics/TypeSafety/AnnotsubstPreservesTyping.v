Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.

Theorem annotsubst_preserves_typing : forall Gamma X K U T t t',
  extendK X K Gamma |-+ t : T ->
  emptyContext |-* U : K ->
  annotsubst X U t t' ->
  Gamma |-+ t' : (beta_reduce (substituteT X U T)).
Proof. Admitted.