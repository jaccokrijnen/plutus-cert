From PlutusCert Require Import Language.
From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import Semantics.Dynamic.Bigstep.

Import NamedTerm.

Definition PIRLang : Language :=
  {|
    expr  := Term
  ; bigstep := fun t t' => exists n, eval t t' n
  ; app   := Apply
  ; const := fun i => Constant (Some' (ValueOf DefaultUniInteger i))
  |}
.
