
(* Progress of the reduction relation used in the normaliser *)
From PlutusCert Require Import PlutusIR Normalisation.Normalisation Kinding.Kinding Type_reduction
Kinding.Checker.
Require Import Coq.Lists.List.
Import ListNotations.

Axiom step_dec_SOP : forall l,
  normal_Ty (Ty_SOP l).

(* Need kinding because of e.g.
  T = Ty_App (Ty_Fun Int Int) Int.
  This is not normal (Ty_Fun is not neutral), and it also does not step (Ty_Fun not a Ty_lam)
*)
Definition step_dec (T : ty) : forall Δ K, has_kind Δ T K -> {T' & step T T'} + normal_Ty T.
Proof.
  induction T; intros.
  - right.
    repeat constructor.
  - apply kind_checking_complete in H.
    inversion H.
    repeat destruct_match.
    apply kind_checking_sound in Heqo.
    apply kind_checking_sound in Heqo0.
    edestruct IHT1; eauto.
    + left. 
      destruct s as [t1' Ht1].
      exists (Ty_Fun t1' T2).
      now constructor.
    + edestruct IHT2; eauto.
      * left.
        destruct s as [t2' Ht2].
        exists (Ty_Fun T1 t2').
        now constructor.
  
  - apply kind_checking_complete in H.
    inversion H.
    repeat destruct_match.
    apply kind_checking_sound in Heqo.
    apply kind_checking_sound in Heqo0.
    edestruct IHT1; eauto.
    + left.
      destruct s as [t1' Ht1].
      exists (Ty_IFix t1' T2).
      now constructor.
    + edestruct IHT2; eauto.
      left.
      destruct s as [t2' Ht2].
      exists (Ty_IFix T1 t2').
      now constructor.
  - apply kind_checking_complete in H. (* Note: Move to kind_checker world to fix not being able to `inversion` on `has_kind`*)
    inversion H.
    repeat destruct_match.
    apply kind_checking_sound in Heqo.
    destruct (IHT ((b, k) :: Δ) Kind_Base Heqo).
    + left.
      destruct s as [t1' Ht1].
      exists (Ty_Forall b k t1').
      now constructor.
    + right.
      apply NO_TyForall; assumption.
  - right. apply NO_TyBuiltin. 
  - apply kind_checking_complete in H. (* Note: Move to kind_checker world to fix not being able to `inversion` on `has_kind`*)
    inversion H.
    repeat destruct_match.
    apply kind_checking_sound in Heqo.
    destruct (IHT ((b, k) :: Δ) k0 Heqo).
    + left.
      destruct s as [t1' Ht1].
      exists (Ty_Lam b k t1').
      now constructor.
    + right.
      apply NO_TyLam; assumption.
  - remember H as H_copy; clear HeqH_copy.
    apply kind_checking_complete in H. (* Note: Move to kind_checker world to fix not being able to `inversion` on `has_kind`*)
    inversion H.
    repeat destruct_match.
    apply kind_checking_sound in Heqo.
    destruct (IHT1 Δ (Kind_Arrow k0_1 k0_2) Heqo).
    + left.
      destruct s as [t1' Ht1].
      exists (Ty_App t1' T2).
      now constructor.
    + apply kind_checking_complete in H_copy. (* Note: Move to kind_checker world to fix not being able to `inversion` on `has_kind`*)
      inversion H.
      repeat destruct_match.
      apply kind_checking_sound in Heqo2.
      destruct (IHT2 Δ k2 Heqo2).
      * left.
        destruct s as [t2' Ht2].
        exists (Ty_App T1 t2').
        now constructor.
      * 
        {
        induction T1.
        - right. constructor. constructor.
          + inversion n. assumption.
          + assumption.
        - (* This does not step *)
          (* but this is also never a normal ty since Ty_Fun is never neutral*)
          exfalso.
          (* it must be ill-kinded *)
          inversion Heqo.
        - exfalso. 
          inversion Heqo.
        - exfalso.
          inversion Heqo.
        - exfalso. 
          inversion Heqo.
        - left. 
          exists (substituteTCA b T2 T1).
          constructor.
          + inversion n. assumption. inversion H0.
          + assumption.
        - right. constructor. constructor.
          + inversion n. assumption.
          + assumption.
        - apply Checker.prop_to_type in Heqo. inversion Heqo.
        }
  - right. apply step_dec_SOP. (* TODO: Different induction prniciple! *)
Defined.

