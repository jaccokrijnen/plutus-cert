Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
From PlutusCert Require Import Kinding.Kinding Static.TypeSubstitution.

Require Import Coq.Strings.String.

(* See PR92 *)
Theorem substituteTCA_preserves_kinding : forall T Delta X K U L,
    ((X, L) :: Delta) |-* T : K ->
    Delta |-* U : L ->
    Delta |-* (substituteTCA X U T) : K.
Proof with eauto with typing.
  induction T.
  all: intros Delta X K U L Hkind__T HHkind__U.
  all: autorewrite with substituteTCA.
  all: simpl.
  all: inversion Hkind__T; subst.
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
      rewrite lookup_neq in H1.
      constructor. auto.
      auto.
  - (* Ty_Forall *)
    admit.
  - (* TY_IFIX*)
    admit.
  - (* Ty_lam*)
  admit.

    
(* ADMIT: I had no time to finish this. Requires proofs about renamings. *)
Admitted.
