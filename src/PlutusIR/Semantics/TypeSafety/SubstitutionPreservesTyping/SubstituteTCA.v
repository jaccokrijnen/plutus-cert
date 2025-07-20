Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
From PlutusCert Require Import 
  Kinding.Kinding 
  util
  Free
  Weakening
  Static.TypeSubstitution.

From Coq Require Import Lia.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Wf_nat.

Require Import Coq.Program.Equality.

(* Appending an entry to a kinding context with a name that does not occur is vacuous *)
Lemma kinding_weakening_fresh : forall X T L K Δ,
  ~ In X (ftv T) ->
  Δ |-* T : K -> ((X, L) :: Δ) |-* T : K.
Proof.
  intros.
  generalize dependent Δ.
  generalize dependent K.
  generalize dependent L.
  induction T; intros; inversion H0; subst.
  - (* Ty_Var *)
    rename t into Y.
    destruct (X =? Y)%string eqn:Heqb.
    + (* X = Y *)
      simpl in H.
      contradiction H.
      left.
      symmetry.
      apply eqb_eq; auto.
    + (* X <> Y *)
      constructor.
      simpl.
      rewrite Heqb.
      assumption.
  - (* Ty_Fun *)
    constructor.
    + eapply IHT1; auto.
      simpl in H.
      apply not_in_app in H.
      destruct H; auto.
    + eapply IHT2; auto.
      simpl in H.
      apply not_in_app in H.
      destruct H; auto.
  - (* Ty_IFix *)
    econstructor.
    + eapply IHT2; eauto.
      simpl in H.
      apply not_in_app in H.
      destruct H; auto.
    + eapply IHT1; auto.
      simpl in H.
      apply not_in_app in H.
      destruct H; auto.
  - (* Ty_Forall *)
    rename b into Z.
    rename k into K1.
    destruct (X =? Z)%string eqn:Heqb.
    + (* X = Z *)
      apply eqb_eq in Heqb. symmetry in Heqb. subst.
      constructor.
      inversion H0; subst.
      eapply Kinding.weakening with (Delta := ((X, K1)::Δ)).
      eapply inclusion_shadow_right; eauto.
      auto.
    + (* X <> Z *)
      constructor.
      eapply Kinding.weakening with (Delta := ((X, L)::(Z, K1)::Δ)).
      { eapply inclusion_swap; auto.
        apply eqb_neq in Heqb; auto. }
      eapply IHT.
      * simpl in H.
        apply not_in_remove in H.
        destruct H; auto.
        subst.
        apply eqb_neq in Heqb; auto.
      * assumption.
  - (* Ty_Builtin *)
    constructor.
    assumption.
  - (* Ty_Lam *)
    rename b into Z.
    rename k into K1.
    destruct (X =? Z)%string eqn:Heqb.
    + (* X = Z *)
      apply eqb_eq in Heqb. symmetry in Heqb. subst.
      constructor.
      inversion H0; subst.
      eapply Kinding.weakening with (Delta := ((X, K1)::Δ)).
      eapply inclusion_shadow_right; eauto.
      auto.
    + (* X <> Z *)
      constructor.
      eapply Kinding.weakening with (Delta := ((X, L)::(Z, K1)::Δ)).
      { eapply inclusion_swap; auto.
        apply eqb_neq in Heqb; auto. }
      eapply IHT.
      * simpl in H.
        apply not_in_remove in H.
        destruct H; auto.
        subst.
        apply eqb_neq in Heqb; auto.
      * assumption.
  - (* Ty_App *)
    econstructor.
    + eapply IHT1; eauto.
      simpl in H.
      apply not_in_app in H.
      destruct H; auto.
    + eapply IHT2; auto.
      simpl in H.
      apply not_in_app in H.
      destruct H; auto.
  - (* Ty_SOP *)
    (* ADMIT: Ty_SOP: Unimplemented *)
Admitted.

(* Renaming (without causing capture) preserves kinding *)
(* Note: Not strictly necessary to work with tv,
    but easier to prove than with ftv *)
Lemma rename_preserves_kinding X Y K L Δ T:
  ~ In Y (tv T) ->
  ((X, L) :: Δ) |-* T : K -> 
  ((Y, L) :: Δ) |-* (rename X Y T) : K.
Proof.
  intros Hfresh Hkind.
  generalize dependent Δ.
  generalize dependent K.
  generalize dependent L.
  induction T; intros; inversion Hkind; subst.
  - (* K_Var *)
    rename t into Z.
    destruct (X =? Z)%string eqn:Heqb.
    + (* X = Z *)
      apply eqb_eq in Heqb as Heq.
      subst.
      inversion Hkind; subst.
      rewrite lookup_eq in H1.
      unfold rename.
      unfold substituteT.
      rewrite String.eqb_refl.
      constructor.
      rewrite lookup_eq.
      assumption.
    + (* X <> Z *)
      unfold rename.
      unfold substituteT.
      rewrite Heqb.
      apply eqb_neq in Heqb as Hneq.
      inversion Hkind; subst.
      rewrite lookup_neq in H1; auto.
      unfold rename.
      unfold substituteT.
      constructor. auto.
      rewrite lookup_neq; auto.
      simpl in Hfresh. intuition.
  - (* K_Fun *)
    unfold rename.
    simpl.
    constructor.
    + unfold rename in IHT1.
      eapply IHT1; auto.
      simpl in Hfresh; auto with *.
    + unfold rename in IHT2.
      eapply IHT2; auto.
      simpl in Hfresh; auto with *.
  - (* K_IFix *)
    unfold rename.
    simpl.
    econstructor.
    + unfold rename in IHT2.
      eapply IHT2; eauto.
      simpl in Hfresh; auto with *.
    + unfold rename in IHT1.
      eapply IHT1; eauto.
      simpl in Hfresh; auto with *.
  - (* Ty_Forall *)
    rename b into Z.
    rename k into K1.
    destruct (X =? Z)%string eqn:Heqb.
    + (* X = Z *)
      apply eqb_eq in Heqb. symmetry in Heqb. subst.
      unfold rename; simpl; rewrite String.eqb_refl.
      constructor.
      destr_eqb_eq X Y.
      * (* Y = X *)
        assumption.
      * eapply Kinding.weakening.
        eapply inclusion_swap; auto.
        apply kinding_weakening_fresh; auto.
        {          
          apply weaken_not_tv_to_not_ftv.
          simpl in Hfresh; intuition.
        }
        simpl in Hfresh; intuition.
        eapply Kinding.weakening in H4; eauto.
        apply inclusion_shadow_left.
    + (* X <> Z *)
      unfold rename; simpl; rewrite Heqb.
      constructor.
      destr_eqb_eq Z Y.
      * contradiction Hfresh.
        simpl. left. reflexivity.
      * unfold rename in IHT.
        eapply Kinding.weakening with (Delta := ((Y, L) :: (Z, K1) :: Δ)).
        eapply inclusion_swap; auto.
        eapply IHT; auto.
        {          
          simpl in Hfresh; intuition.
        }
        simpl in Hfresh; intuition.
        eapply Kinding.weakening.
        eapply inclusion_swap; eauto.
        apply eqb_neq in Heqb; auto.
        assumption.
  - (* Ty_Builtin *)
    constructor.
    assumption.
  - (* Ty_Lam *)
    rename b into Z.
    rename k into K1.
    destruct (X =? Z)%string eqn:Heqb.
    + (* X = Z *)
      apply eqb_eq in Heqb. symmetry in Heqb. subst.
      unfold rename; simpl; rewrite String.eqb_refl.
      constructor.
      destr_eqb_eq X Y.
      * (* Y = X *)
        assumption.
      * eapply Kinding.weakening.
        eapply inclusion_swap; auto.
        apply kinding_weakening_fresh; auto.
        {          
          apply weaken_not_tv_to_not_ftv.
          simpl in Hfresh; intuition.
        }
        simpl in Hfresh; intuition.
        eapply Kinding.weakening in H4; eauto.
        apply inclusion_shadow_left.
    + (* X <> Z *)
      unfold rename; simpl. rewrite Heqb.
      constructor.
      destr_eqb_eq Z Y.
      * contradiction Hfresh.
        simpl. left. reflexivity.
      * unfold rename in IHT.
        eapply Kinding.weakening with (Delta := ((Y, L) :: (Z, K1) :: Δ)).
        eapply inclusion_swap; auto.
        eapply IHT; auto.
        {          
          simpl in Hfresh; intuition.
        }
        simpl in Hfresh; intuition.
        eapply Kinding.weakening.
        eapply inclusion_swap; eauto.
        apply eqb_neq in Heqb; auto.
        assumption.
  - (* Ty_App *)
    unfold rename.
    simpl.
    econstructor.
    + unfold rename in IHT1.
      eapply IHT1; eauto.
      simpl in Hfresh; auto with *.
    + unfold rename in IHT2.
      eapply IHT2; eauto.
      simpl in Hfresh; auto with *.
  - (* Ty_SOP *)
    (* ADMIT: Ty_SOP: Unimplemented *)
Admitted.

Lemma substituteTCA_preserves_kinding__SOP : forall Ts Δ X K U L,
    ((X, L) :: Δ) |-* (Ty_SOP Ts) : K ->
    Δ |-* U : L ->
    Δ |-* (substituteTCA X U (Ty_SOP Ts)) : K.
Admitted.

(* Capture-avoiding substitutions preserve kinding *)
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
    destr_eqb_eq X b.
    + constructor.
      eapply Kinding.weakening with (Delta := ((b, k) :: (b, L) :: Delta)).
      * eapply inclusion_shadow_left.
      * assumption.
    + destruct (existsb (eqb b) (ftv U)) eqn:Hexi.
      * remember (fresh _ _ _) as fr.
        constructor.
        eapply H; eauto.
        -- rewrite <- rename_preserves_size.
           simpl.
           lia.
        -- eapply Kinding.weakening with (Delta := ((fr, k) :: (X, L):: Delta)); eauto.
           ++ eapply inclusion_swap; auto.
              subst.
              symmetry.
              apply fresh__X.
           ++ eapply rename_preserves_kinding; eauto.
              subst.
              apply fresh__T.
        -- apply kinding_weakening_fresh; auto.
           subst.
           apply weaken_not_tv_to_not_ftv.
           apply fresh__S.
      * constructor.
        eapply H; eauto.
        -- simpl. lia.
        -- eapply Kinding.weakening with (Delta := ((b, k) :: (X, L):: Delta)); eauto.
           apply inclusion_swap; auto.
        -- apply kinding_weakening_fresh; auto.
           apply not_in_existsb in Hexi; auto.
  - (* Ty_Builtin *)
    constructor.
    assumption.
  - (* Ty_Lam *)
    destr_eqb_eq X b.
    + constructor.
      eapply Kinding.weakening with (Delta := ((b, k) :: (b, L) :: Delta)).
      * eapply inclusion_shadow_left.
      * assumption.
    + destruct (existsb (eqb b) (ftv U)) eqn:Hexi.
      * remember (fresh _ _ _) as fr.
        constructor.
        eapply H; eauto.
        -- rewrite <- rename_preserves_size.
           simpl.
           lia.
        -- eapply Kinding.weakening with (Delta := ((fr, k) :: (X, L):: Delta)); eauto.
           ++ eapply inclusion_swap; auto.
              subst.
              symmetry.
              apply fresh__X.
           ++ eapply rename_preserves_kinding; eauto.
              subst.
              apply fresh__T.
        -- apply kinding_weakening_fresh; auto.
           subst.
           apply weaken_not_tv_to_not_ftv.
           apply fresh__S.
      * constructor.
        eapply H; eauto.
        -- simpl. lia.
        -- eapply Kinding.weakening with (Delta := ((b, k) :: (X, L):: Delta)); eauto.
           apply inclusion_swap; auto.
        -- apply kinding_weakening_fresh; auto.
           apply not_in_existsb in Hexi; auto.
    - (* Ty_App *)
      econstructor.
      + eapply H; eauto.
        simpl. lia.
      + eapply H; eauto.
        simpl. lia.
    - (* Ty_SOP *)
      (* ADMIT: Ty_SOP Unimplemented *)
      specialize (substituteTCA_preserves_kinding__SOP _ _ _ _ U _ Hkind__T) as H_admitted.
      autorewrite with substituteTCA in H_admitted.
      auto.
Defined.
