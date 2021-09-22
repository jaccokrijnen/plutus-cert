(** ** Definition of big-step semantics *)
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Values.

(** ** Theorems and lemmas about the big-step semantics *)
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.Congruence.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.Deterministic.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.EvalToValue.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.EvalValue.

(** ** Theorems and lemmas about substitution *)
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.Total.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.Vacuous.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.PreservesValue.