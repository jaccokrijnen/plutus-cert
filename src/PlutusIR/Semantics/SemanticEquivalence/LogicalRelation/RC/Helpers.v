Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

From Coq Require Import Lia.



Lemma RC_lt_obsolete : forall k T rho e e',
  (0 < k -> RC k T rho e e') ->
  RC k T rho e e'.
Proof.
  intros.
  autorewrite with RC.
  intros j Hlt__j.
  assert (0 < k) by lia.
  apply H in H0.
  autorewrite with RC in H0.
  eapply H0.
  assumption.
Qed.


(* Run an C(e, e') by looking in the context for an evaluation of e, and use that
* amount of steps
* binds the resulting
*    r' : result
*    j' : nat
*    H_eval' : eval e' ... 
*    H_res' : V(r, r')
*)
Ltac run_C H_RC r' j' H_eval' H_res':=
  match type of H_RC with
  | C ?k ?T ?ρ ?e1 ?e2 =>
    match goal with
    | H_ev : e1 =[ ?i ]=> ?v1 |- _ =>
        let H_RC' := fresh "H" in
        let H_ev'  := fresh "H_ev" in
        assert (H_RC' := H_RC); assert (H_ev' := H_ev);

        autorewrite with R in H_RC';
        apply H_RC' in H_ev' as [r' [j' [H_eval' H_res']]];
        clear H_RC'
    | _ =>
      fail 1 "Could not find required hypothesis of type eval"
    end
  end
.

(*
  Simplifies an assumption

    V k T ρ r r' \/ (is_error r /\ is_error r')

  to

    V k T ρ r r'

  by searching for ~is_error r or ~is_error r'
*)
Ltac no_err H HR :=
  destruct H as [HR | [H_err H_err'] ];
  try solve [inversion H_err; inversion H_err'];
  try solve [contradiction]
.
