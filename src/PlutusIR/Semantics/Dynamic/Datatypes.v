From PlutusCert Require Import
  PlutusIR
.

Import NamedTerm.

Axiom dt_to_ty : DTDecl -> Ty.
Axiom match_to_term : DTDecl -> Term.
Axiom constr_to_term : constructor -> Term.

Axiom constr_to_subst : constructor -> String.string * Term.

