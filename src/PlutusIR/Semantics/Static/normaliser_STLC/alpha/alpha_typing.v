Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
From PlutusCert Require Import freshness util alpha.alpha STLC_named STLC_named_typing Util.List alpha_freshness alpha_rename.
Local Open Scope string_scope.
Local Open Scope list_scope.

From PlutusCert Require PlutusIRSOP.

(* Alpha equivalence of types *)

(* Contextual alpha equivalence: kinding contexts that match alpha contexts*)
Inductive CAlpha : list (string * string) -> list (string * PlutusIRSOP.kind) -> list (string * PlutusIRSOP.kind) -> Prop :=
  | calpha_nil D : CAlpha [] D D (* Non-empty kinding enviornments because id renamings are like no renamings. TODO: think whether we want to allow that or want to enforce that id renamings are in the alpha enviornment always*)
  | calpha_cons x y K sigma Gamma Gamma' :
    CAlpha sigma Gamma Gamma' ->
    CAlpha ((x, y)::sigma) ((x, K)::Gamma) ((y, K)::Gamma').
  (* | calpha_id x K sigma Gamma Gamma' :
    CAlpha sigma Gamma Gamma' ->
    CAlpha sigma ((x, K)::Gamma) ((x, K)::Gamma'). *)

Set Printing Implicit.

(* Exercise and possibly useful *)
Lemma alpha_preserves_typing sigma s t A Gamma Gamma' :
  Alpha sigma s t -> CAlpha sigma Gamma Gamma' -> STLC_named_typing.has_kind Gamma s A -> STLC_named_typing.has_kind Gamma' t A.
Proof.
  intros HAlpha Htype.
  generalize dependent A.
  generalize dependent Gamma.
  generalize dependent Gamma'.
  induction HAlpha.
  - intros Gamma' Gamma HCAlpha A HType.
    inversion HType.
    apply K_Var; subst...
    generalize dependent Gamma.
    generalize dependent Gamma'.
    induction a; subst...
    + intros.
      inversion HCAlpha; subst...
      assumption.
    + intros Gamma' Gamma HCAlpha HType Hlookup.
      inversion HCAlpha; subst...
      inversion Hlookup.
      simpl.
      repeat rewrite Coq.Strings.String.eqb_refl.
      reflexivity.
    + intros Gamma' Gamma HCAlpha HType Hlookup.
      inversion HCAlpha; subst...
      simpl.
      destruct (y =? w) eqn:yw.
      * apply String.eqb_eq in yw.
        contradiction.
      * specialize (IHa Gamma'0 Gamma0 H4).
        unfold lookup in Hlookup.
        destruct (x =? z) eqn:xz.
        -- apply String.eqb_eq in xz.
           contradiction.
        -- fold (lookup z Gamma0) in Hlookup.
          assert (Gamma0 |-* (tmvar z) : A).
          {
            (* Strengthening typing*)
            apply K_Var.
            assumption.
          }
           specialize (IHa H Hlookup).
           assumption.
  - intros Gamma' Gamma HCAlpha A0 HType.
    inversion HType; subst;
    specialize (IHHAlpha ((y, A)::Gamma') ((x, A)::Gamma)
      (calpha_cons x y A sigma Gamma Gamma' HCAlpha) _ H5); constructor; auto.
  - intros Gamma' Gamma HCAlpha A HType. 
    inversion HType; subst; econstructor; eauto.
  - intros.
    inversion H; subst.
    constructor. auto.
Qed.

























(* TODO, Kind of old code below*)











(* FROM deadcode/DSP/lemmas.v*)
  Lemma strengthen_Γ_cons Γ t T x Tx :
    ~ In x (ftv t) ->
    ((x, Tx) :: Γ) |-* t : T ->
    Γ |-* t : T.
Proof.
  (* PIR PROOF is still incomplete*)
Admitted.

(* TODO: NAIVE NOT WORKING INDUCTION HYPOTHESIS*)
Theorem substituteTCA_preserves_kinding : forall T Delta X K U L,
    ((X, L) :: Delta) |-* T : K ->
    Delta |-* U : L ->
    Delta |-* (substituteTCA X U T) : K.
Proof with eauto.
  (* induction T.
  all: intros Delta X K U L Hkind__T HHkind__U.
  all: autorewrite with substituteTCA.
  all: simpl.
  all: inversion Hkind__T; subst...
  - (* Ty_Var *)
    rename s into Y.
    destruct (X =? Y)%string eqn:Heqb.
    + (* X = Y *)
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite lookup_eq in H1.
      congruence.
    + (* X <> Y *)
      apply eqb_neq in Heqb as Hneq.
      rewrite lookup_neq in H1...
      now constructor.
  - (* Ty_Lam *)
    rename s into Y.
    destruct (X =? Y)%string eqn:Heqb.
    + (* X = Y *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply K_Lam.
      assert (((Y, t)::(Y, L):: Delta) |-* T : K2 -> ((Y, t)::Delta) |-* T : K2).
      {
        (* weaken duplicates *)
        admit.
      }
      auto.
    + destruct (in_dec string_dec Y (ftv U)).
      * (* Y in FV(U) *)

        (* DIFFICULT CASE THAT REQUIRES ALPHA RENAMING*)
        assert (existsb (eqb Y) (ftv U) = true) by admit. (* trivial *)
        rewrite H.
        apply K_Lam.
        remember (fresh2 _ T) as Y'.
        specialize (IHT ((Y', t)::Delta) X K2 U L).

        admit.
      * (* Y not in FV(U) *)
        assert (existsb (eqb Y) (ftv U) = false).
        { (* Follows from Y notin ftv U*)
          admit.
        }
        rewrite H.
        apply K_Lam.
        eapply IHT.
        -- (* X is not Y, so we can probably switch those around in the environment *)
          admit.
        -- (* Y not in U, so we can remove (Y, t) from the context *)
          admit.
  - (* Ty_App *)
    admit. *)
Admitted.

(* TODO: See also Theorems/Weakening for already existing PIR version
*)
Lemma weakening : forall T T2 K X Δ,
      ~ In X (ftv T) ->
      Δ |-* T : K ->
      ((X, T2)::Δ) |-* T : K.
Proof.
 (* PIR PROOF DONE IN WEAKENING THEOREMS FILE*)
Admitted.

Lemma substituteTCA_vacuous : forall R X U T T',
    Alpha R T T' ->
    ~ In X (ftv T) ->
    Alpha R (substituteTCA X U T) T'.
Proof.
  intros.
  generalize dependent T.
  generalize dependent R.
  induction T'; intros.
  all: inversion H; subst.
  all: autorewrite with substituteTCA.
  - apply not_in_ftv_var in H0.
    rewrite <- String.eqb_neq in H0.
    now rewrite H0.
  - destr_eqb_eq X x; [now constructor|].
    assert (~ In X (ftv s1)) by now apply ftv_lam_negative in H0.
    destruct (existsb (eqb x) (ftv U)) eqn:sinU.
    + simpl.
      remember (fresh2 _ s1) as Y.
      constructor.
      eapply IHT'.
      * eapply alpha_trans_rename_left; eauto.
      * apply ftv_not_in_rename; auto.
        eapply fresh2_over_key_sigma in HeqY. symmetry. eauto.
        apply in_eq.
    + constructor; auto.
  - constructor.
    + eapply IHT'1; eauto. 
      now apply not_ftv_app_not_left in H0.
    + eapply IHT'2; eauto.
      now apply not_ftv_app_not_right in H0.
  - auto.
Qed.

Corollary substituteTCA_vacuous_specialized X U T:  
  ~ In X (ftv T) ->
  Alpha nil (substituteTCA X U T) T.
Proof.
  eapply substituteTCA_vacuous; try apply alpha_ids; auto; repeat constructor.
Qed.

Lemma swap_kinding_context : forall T X Y K1 K2 K3 Δ,
    X <> Y -> 
    ((X, K1) :: (Y, K2) :: Δ) |-* T : K3 ->
    ((Y, K2) :: (X, K1) :: Δ) |-* T : K3.
Proof.

(* NOTE: See context_invariance for finished proof on PIR *)
Admitted.

Theorem substituteTCA_preserves_kinding_alpha_ren : forall T Delta Delta' ren T' X X' K U' L,
    Alpha ren T T' ->
    AlphaVar ren X X' ->
    CAlpha ren Delta Delta' ->
    ((X, L) :: Delta) |-* T : K ->
    Delta' |-* U' : L ->
    Delta' |-* (substituteTCA X' U' T') : K.
Proof with eauto.
  (* induction T.
  all: intros Delta Delta' ren T' X X' K U' L HalphaT HalphaX HalphaC Hkind__T HHkind__U.
  all: autorewrite with substituteTCA.
  all: simpl.
  all: inversion Hkind__T; subst...
  - (* Ty_Var *)
    inversion HalphaT; subst.
    destruct (in_dec String.string_dec X' (ftv (tmvar y))).
    {
      autorewrite with substituteTCA.
      assert (In X (ftv (tmvar s))).
      {
        eapply alpha_preserves_ftv in i; eauto.
        - eapply alpha_sym; eauto.
          eapply sym_alpha_ctx_is_sym; eauto.
        - eapply alphavar_sym; eauto.
          eapply sym_alpha_ctx_is_sym; eauto.
      }
      apply ftv_var in i; subst.
      apply ftv_var in H; subst.
      rewrite String.eqb_refl.
      inversion H1.
      rewrite String.eqb_refl in H0.
      inversion H0; subst; auto. 
    }
    {
      eapply alpha_preserves_typing; eauto.
      - eapply alpha_sym; try eapply sym_alpha_ctx_left_is_sym; eauto.
        eapply substituteTCA_vacuous; eauto.
        eapply alpha_sym; try eapply sym_alpha_ctx_is_sym; eauto.
      - eapply strengthen_Γ_cons; eauto.
        eapply alpha_preserves_no_ftv in n; eauto.
        + eapply alpha_sym; try eapply sym_alpha_ctx_is_sym; eauto.
        + eapply alphavar_sym in HalphaX; [| apply sym_alpha_ctx_is_sym]; eauto.
    }
  - (* Ty_Lam *)
    inversion HalphaT; subst.
    destruct (in_dec String.string_dec X' (ftv (tmlam y t s2))).
    {
    autorewrite with substituteTCA.
    destruct (X' =? y)%string eqn:Heqb.
    + (* X = Y *)
      apply eqb_eq in Heqb as Heq; subst.
      apply ftv_lam_no_binder in i.
      contradiction.
    + (* X <> Y *)
      assert (HinT: In X (ftv (tmlam s t T))).
      {
        eapply alpha_preserves_ftv in i; eauto.
        - eapply alpha_sym; try eapply sym_alpha_ctx_is_sym; eauto.
        - eapply alphavar_sym; try eapply sym_alpha_ctx_is_sym; eauto.
      }
      remember HinT as HinT_copy. clear HeqHinT_copy.
      apply ftv_lam_in_no_binder in HinT.
      apply ftv_lam_helper in HinT_copy as HinT_body.
      destruct (existsb (eqb y) (ftv U')) eqn:yInU'.
      * (* Y in FV(U) *)
        remember (fresh2 _ s2) as Y'.
        simpl.
        apply K_Lam.
        specialize (IHT ((s, t)::Delta) ((Y', t)::Delta') ((s, Y')::ren) (rename y Y' s2) X X' K2 U' L).

        eapply IHT.
        -- eapply alpha_trans_rename_right. eauto. eauto.
        -- apply alpha_var_diff; auto.
           eapply fresh2_over_key_sigma in HeqY'; eauto. eapply in_cons. eapply in_eq.
        -- constructor. auto.
        -- now eapply swap_kinding_context.
        -- eapply weakening in HHkind__U; eauto.
           eapply fresh2_over_tv_value_sigma in HeqY'.
           ++ intros Hcontra.
              apply extend_ftv_to_tv in Hcontra.
              revert Hcontra.
              eauto.
           ++ eapply in_cons. eapply in_eq.           
      * apply K_Lam.
        eapply IHT.
        -- exact H5.
        -- apply alpha_var_diff; eauto.
           intros Hcontra.
           subst.
           rewrite String.eqb_refl in Heqb.
           discriminate.
        -- constructor. eauto.
        -- eapply swap_kinding_context; eauto.
        -- eapply weakening in HHkind__U; eauto.
           now apply not_existsb_not_in.
    }
    {
      eapply alpha_preserves_typing; eauto.
      - eapply alpha_sym; try eapply sym_alpha_ctx_left_is_sym; eauto.
        eapply substituteTCA_vacuous; eauto.
        eapply alpha_sym in HalphaT; eauto; try eapply sym_alpha_ctx_is_sym; eauto.
      - eapply strengthen_Γ_cons; eauto.
        eapply alpha_preserves_no_ftv in n; eauto.
        + eapply alpha_sym; try apply sym_alpha_ctx_is_sym; eauto.
        + eapply alphavar_sym in HalphaX; [| apply sym_alpha_ctx_is_sym]; eauto.
    }
  - (* Ty_App *)
    inversion HalphaT; subst.
    autorewrite with substituteTCA.
    eapply K_App.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto. *)
Admitted.

Corollary substituteTCA_preserves_kinding_specialised : forall T Delta X K U L,
    ((X, L) :: Delta) |-* T : K ->
    Delta |-* U : L ->
    Delta |-* (substituteTCA X U T) : K.
Proof with eauto.
  intros.
  destruct (in_dec String.string_dec X (ftv T)).
  - eapply substituteTCA_preserves_kinding_alpha_ren; eauto; try constructor.
    + apply alpha_ids. constructor.
  - remember n as n'; clear Heqn'.
    eapply strengthen_Γ_cons in H; eauto.
    eapply alpha_preserves_typing; eauto.
    + eapply alpha_sym; try constructor.
      now eapply substituteTCA_vacuous_specialized.
    + constructor.
Qed.