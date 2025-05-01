Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
From PlutusCert Require Import 
  Kinding.Kinding 
  util
  Weakening
  Static.TypeSubstitution.

From Coq Require Import Lia.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Wf_nat.

(* See alpha_typing.v for a proof of this for STLC. This proof will be analogous*)
Theorem substituteTCA_preserves_kinding : forall T Delta X K U L,
    ((X, L) :: Delta) |-* T : K ->
    Delta |-* U : L ->
    Delta |-* (substituteTCA X U T) : K.
Proof with eauto with typing.
  intros T.
  remember (size T) as n.
  generalize dependent T.
  induction n using lt_wf_ind.

  induction T.
  all: intros Hsize Delta X K U L Hkind__T HHkind__U.
  all: autorewrite with substituteTCA.
  all: simpl.
  all: inversion Hkind__T; subst.
  - (* Ty_Var *)
    rename t into Y.
    destruct (X =? Y)%string eqn:Heqb.
    + (* X = Y *)
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite lookup_eq in H2.
      congruence.
    + (* X <> Y *)
      apply eqb_neq in Heqb as Hneq.
      rewrite lookup_neq in H2.
      constructor. auto.
      auto.
  - (* Ty_Fun *)
    constructor.
    + eapply H; eauto.
      simpl. lia.
    + eapply H; eauto.
      simpl. lia.
  - (* TY_IFIX*)
    econstructor.
    + eapply H; eauto.
      simpl. lia.
    + eapply H; eauto.
      simpl. lia.
  - (* Ty_Forall*)
    (* ADMIT: Identical to Ty_Lam *)
    admit.
  - (* Ty_Builtin *)
    constructor.
    assumption.
  - (* Ty_Lam *)
    destr_eqb_eq X b.
    + constructor.
      eapply Kinding.weakening with (Delta := ((b, k) :: (b, L) :: Delta)).
      * (* ADMIT: (b, L) is shadowed, so inclusion *) admit.
      * assumption.
    + destruct (existsb (eqb b) (ftv U)) eqn:Hexi.
      * remember (fresh _ _ _) as fr.
        constructor.
        eapply H; eauto.
        -- rewrite <- rename_preserves_size.
           simpl.
           lia.
        -- (* ADMIT: kinding swap *)
           admit.
        -- (* ADMIT: Vacuous context extension by fr notin ftv U.*)
           admit.
      * constructor.
        eapply H; eauto.
        -- simpl. lia.
        -- (* ADMIT: kinding swap *)
           admit.
        -- (* ADMIT: Vacuous context extension by b notin ftv U.*)
        admit.
    - (* Ty_App *)
      econstructor.
      + eapply H; eauto.
        simpl. lia.
      + eapply H; eauto.
        simpl. lia.
    - (* Ty_SOP *)
      (* ADMIT: Ty_SOP Unimplemented *)
      admit.
      
(* ADMIT: I had no time to finish this. Requires proofs about renamings. *)
Admitted.
