Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Util.List.



Theorem substituteTCA_preserves_kinding : forall T Delta X K U L,
    ((X, L) :: Delta) |-* T : K ->
    Delta |-* U : L ->
    Delta |-* (substituteTCA X U T) : K.
Proof with eauto with typing.
  induction T.
  all: intros Delta X K U L Hkind__T HHkind__U.
  all: autorewrite with substituteTCA.
  all: simpl.
  all: inversion Hkind__T; subst...
  - (* Ty_Var *)
    rename t into Y.
    destruct (X =? Y)%string eqn:Heqb.
    + (* X = Y *)
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite lookup_eq in H1.
      congruence.
    + (* X <> Y *)
      apply eqb_neq in Heqb as Hneq.
      rewrite lookup_neq in H1...
(* ADMIT: I had no time to finish this. Requires proofs about renamings. *)
Admitted.
