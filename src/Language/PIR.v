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


From PlutusCert Require Import RelationalModel.

Require Import Lists.List.
Import ListNotations.

Lemma LR_forward t t' ty :
  LR_logically_approximate [] [] t t' ty ->
  forward PIRLang PIRLang t t'.
Proof.
  intros H_LR.
  destruct H_LR as [H_ty_t H_ty_t' .

bigstep L (app L p (const L n)) (const L r).


eval (Apply t Constant (Some' (ValueOf DefaultUniInteger i))) v i ->
eval (Apply t ())
