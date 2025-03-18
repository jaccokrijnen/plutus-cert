
From Equations Require Import Equations.
Require Import Coq.Lists.List.
Local Open Scope list_scope.

Require Import Lia.

Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Ascii.

From PlutusCert Require Import SN_STLC_named_naive SN_STLC_named2 util Util.List STLC_named STLC_named_typing plutus_kinding_set. (* I don't understand why we need this for ftv defintion*)
From PlutusCert Require PlutusIR Static.TypeSubstitution Normalisation.Type_reduction.


(** Substitutions *)

(* from plut to annotated stlc*)
Fixpoint f (t : PlutusIR.ty) : term :=
  match t with
  | PlutusIR.Ty_Var x => tmvar x
  | PlutusIR.Ty_Lam x A t => @tmlam Lam x A (f t)
  | PlutusIR.Ty_Forall x A t => @tmlam ForAll x A (f t)
  | PlutusIR.Ty_Fun t1 t2 => @tmapp Fun (f t1) (f t2)
  | PlutusIR.Ty_App t1 t2 => @tmapp App (f t1) (f t2)
  | PlutusIR.Ty_IFix f1 t1 => @tmapp IFix (f f1) (f t1)
  | PlutusIR.Ty_Builtin d => tmbuiltin d
  end.

Require Import Coq.Program.Equality.

Set Printing Implicit.

Lemma f_preserves_rename s fr T :
  rename s fr (f T) = f (TypeSubstitution.rename s fr T).
Proof.
  induction T.
  - simpl.
    destr_eqb_eq s t.
    + simpl. auto. unfold TypeSubstitution.rename. simpl. rewrite String.eqb_refl. simpl.
      unfold rename. simpl. rewrite String.eqb_refl. simpl. auto.
    + unfold rename. unfold TypeSubstitution.rename. simpl. rewrite <- String.eqb_neq in H. rewrite H. simpl. auto.
  - simpl. unfold rename. simpl. f_equal. auto. auto.
  - simpl. unfold rename. simpl. f_equal. auto. auto.
  - unfold rename. simpl.
    unfold TypeSubstitution.rename.
    simpl.
    destr_eqb_eq s b.
    + rewrite mren_id.
      simpl. auto.
    + simpl. f_equal. auto.
  - simpl. unfold rename. simpl. auto.
  - unfold rename. simpl.
    unfold TypeSubstitution.rename.
    simpl.
    destr_eqb_eq s b.
    + rewrite mren_id.
      simpl. auto.
    + simpl. f_equal. auto.
  - simpl. unfold rename. simpl. f_equal. auto. auto.
Qed.

Lemma f_preserves_ftv T :
  ftv (f T) = TypeSubstitution.ftv T.
Proof.
  induction T; simpl; try f_equal; auto.
Qed.

(* TODO: This tv definition should be somewhere else! *)
Fixpoint plutusTv (t : PlutusIR.ty) : list string :=
  match t with
  | PlutusIR.Ty_Var x => [x]
  | PlutusIR.Ty_Lam x A t => x :: (plutusTv t)
  | PlutusIR.Ty_Forall x A t => x :: (plutusTv t)
  | PlutusIR.Ty_Fun t1 t2 => plutusTv t1 ++ plutusTv t2
  | PlutusIR.Ty_App t1 t2 => plutusTv t1 ++ plutusTv t2
  | PlutusIR.Ty_IFix f1 t1 => plutusTv f1 ++ plutusTv t1
  | PlutusIR.Ty_Builtin d => []
  end.

Lemma f_preserves_tv T :
  tv (f T) = plutusTv T.
Proof.
  induction T; simpl; try f_equal; auto.
Qed.

(* Not true currently
Little research:
Removing the first (x, fs) will be easy.
Hence the only difference is ftv vs tv.

*)
Lemma f_preserves_fresh2 x y s s' T :
  fresh2 ((x, f s)::(y, f s')::nil) (f T) = TypeSubstitution.fresh y s' T.
Proof.
  (* simpl.
  unfold fresh2.
  unfold port_plut.fresh2.
  rewrite f_preserves_tv.
  assert (Htv_keys_env: (tv_keys_env
  [(x, f s); (y, f s')] = port_plut.tv_keys_env [(x, s); (y, s')])).
  {
    unfold tv_keys_env.
    unfold port_plut.tv_keys_env.
    f_equal.
    rewrite f_preserves_tv.
    f_equal.
    rewrite f_preserves_tv.
    f_equal.
  }
  rewrite Htv_keys_env.
  reflexivity. *)
Admitted.

Require Import Coq.Arith.Wf_nat.

Lemma f_preserves_substituteTCA X U T :
  (f (TypeSubstitution.substituteTCA X U T)) = (substituteTCA X (f U) (f T)).
Proof.
  remember (f T) as fT.
  remember (size fT) as n.
  generalize dependent fT.
  generalize dependent T.
  induction n using lt_wf_ind.
  intros.
  dependent induction fT; subst.
  + induction T; subst; inversion HeqfT; subst.
    autorewrite with substituteTCA.
    destr_eqb_eq X t; auto.
  + induction T; subst; inversion HeqfT; subst.
    
    {
      autorewrite with substituteTCA.
      destr_eqb_eq X b; eauto.
      rewrite <- (f_preserves_ftv).
      destruct (existsb (String.eqb b) (ftv (f U))) eqn:Heq.
      -- 
          simpl.
          remember (fresh2 _ _) as fr.
          remember (TypeSubstitution.fresh _ _ _) as fr'.
          assert (Hfr_pres: fr' = fr).
          {
            (* Not currently true, but probably possible to change on both sides*)
            subst.
            symmetry.
            assert (tmvar b = f (PlutusIR.Ty_Var b)).
            {
              simpl.
              auto.
            }
            rewrite H1.
            eapply f_preserves_fresh2.
          }
          rewrite Hfr_pres.
          f_equal.
          ++ eapply H; eauto.
            ** rewrite <- rename_preserves_size.
               simpl.
               lia.
            ** apply f_preserves_rename.
      -- simpl.
         f_equal.
          eapply H; eauto. simpl. lia.
    }


(* TODO: EXACTLY IDENTICAL TO ABOVE*)

     {
      autorewrite with substituteTCA.
      destr_eqb_eq X b; eauto.
      rewrite <- (f_preserves_ftv).
      destruct (existsb (String.eqb b) (ftv (f U))) eqn:Heq.
      -- 
          simpl.
          remember (fresh2 _ _) as fr.
          remember (TypeSubstitution.fresh _ _ _) as fr'.
          assert (Hfr_pres: fr' = fr).
          {
            (* Not currently true, but probably possible to change on both sides*)
            subst.
            symmetry.
            assert (tmvar b = f (PlutusIR.Ty_Var b)).
            {
              simpl.
              auto.
            }
            rewrite H1.
            eapply f_preserves_fresh2.
          }
          rewrite Hfr_pres.
          f_equal.
          ++ eapply H; eauto.
            ** rewrite <- rename_preserves_size.
               simpl.
               lia.
            ** apply f_preserves_rename.
      -- simpl.
         f_equal.
          eapply H; eauto. simpl. lia.
    }
         
    
  + induction T; subst; inversion HeqfT; subst.
    all: autorewrite with substituteTCA; simpl; f_equal; eauto; eapply H; auto; simpl; lia. 
  + assert (T = PlutusIR.Ty_Builtin d).
    {
      destruct T; auto; inversion HeqfT. auto.
    }
    subst.
    autorewrite with substituteTCA.
    simpl. auto.
Qed.
        
Theorem f_preserves_step s s' :
  Type_reduction.step s s' -> step_nd (f s) (f s').
Proof.
  intros H.
  induction H; simpl; eauto; try solve [constructor; eauto].
  - rewrite f_preserves_substituteTCA.
    constructor.
Qed.

Set Printing Implicit.

Require Import Coq.Program.Equality.

Theorem f_preserves_kind Δ s K :
  plutus_kinding_set.has_kind Δ s K -> STLC_named_typing.has_kind Δ (f s) K.
Proof.
  intros.
  induction H; simpl; eauto.
  - constructor.
    auto.
  - constructor.
    + eauto.
    + eauto.
  - eapply STLC_named_typing.K_IFix; eauto.
  - constructor.
    auto.
  - constructor.
    exact h.
  - constructor.
    auto.
  - eapply STLC_named_typing.K_App; eauto.
Qed.  


(*
Jacco: Dit is blijkbaar een forward simulation
*)
Lemma sn_preimage2 {e2 : PlutusIR.ty -> PlutusIR.ty -> Type} {e : term -> term -> Type} (h : PlutusIR.ty -> term) (x : PlutusIR.ty) :
  (forall x y, e2 x y -> e (h x) (h y)) -> @sn term e (h x) -> @sn PlutusIR.ty e2 x.
Proof.
  intros A B.
  remember (h x) as v. (* this allows us to keep B : sn v as an hypothesis*)
  generalize dependent h.
  generalize dependent x.
  induction B.
  intros x0 h A eqn.
  apply SNI.
  intros y C.
  apply A in C.
  
  specialize (X (h y)).
  rewrite <- eqn in C.
  eapply X.
  - assumption.
  - exact A.
  - reflexivity.
Qed.

Theorem sn_step_plut : forall s, @sn term step_nd (f s) -> @sn PlutusIR.ty Type_reduction.step s.
Proof.
  intros s.
  eapply @sn_preimage2 with (h := f) (e2 := Type_reduction.step) (e := step_nd).
  apply f_preserves_step.
Qed.

Corollary plutus_ty_strong_normalization s Δ K : plutus_kinding_set.has_kind Δ s K -> @sn PlutusIR.ty Type_reduction.step s.
Proof.
  intros Hwk.
  eapply sn_preimage2. 
  - apply f_preserves_step.
  - eapply strong_normalization with (E := Δ) (T := K).
    eapply f_preserves_kind.
    auto.
Qed.

Print Assumptions plutus_ty_strong_normalization.
