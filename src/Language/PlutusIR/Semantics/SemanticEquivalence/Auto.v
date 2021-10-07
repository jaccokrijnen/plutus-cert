Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

From Coq Require Import Lia.

Ltac multisubst_preserves_typing :=
  match goal with
  | |- 
      emptyContext |-+ (msubst_term ?env (msubstA_term (msyn1 ?rho) ?e)) : (msubstT (msyn1 ?rho) ?T)
    => 
      replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty);
        [ eapply msubst_preserves_typing_1; eauto;
          eapply msubstA_preserves_typing_1; eauto;
          eauto with typing
        | rewrite mupd_empty; reflexivity
        ]
  | |- 
      emptyContext |-+ (msubst_term ?env (msubstA_term (msyn2 ?rho) ?e)) : (msubstT (msyn2 ?rho) ?T)
    => 
      replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty);
        [ eapply msubst_preserves_typing_2; eauto;
          eapply msubstA_preserves_typing_2; eauto;
          eauto with typing
        | rewrite mupd_empty; reflexivity
        ]
  end.
  
Ltac eauto_LR :=
  try solve [eauto with typing || lia || multisubst_preserves_typing].