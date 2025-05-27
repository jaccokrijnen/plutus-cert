From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import Semantics.Dynamic.Substitution.
From PlutusCert Require Import Semantics.Dynamic.AnnotationSubstitution.
From PlutusCert Require Import Multisubstitution.Congruence.
From PlutusCert Require Import Util.List.


Require Import Utf8_core.
Require Import Lists.List.
Require Import Strings.String.


(* Lemmas that prove that substitution will not change the set of bound variables *)

Section Bvb.

  (* Substitution does not change bound variables of a binding *)
  Definition bvb_subst_b x t b :
    bvb (subst_b x t b) = bvb b
    := match b with
        | TermBind s (VarDecl y T) tb => eq_refl
        | _ => eq_refl
      end.

  (* Substitution does not change bound variables *)
  Definition bvb_msubst_b γ b :
    bvb (msubst_b γ b) = bvb b.
  Proof.
    revert b.
    induction γ as [ | [x t] γ] .
    - intros b. reflexivity.
    - intros b.
      simpl.
      rewrite IHγ.
      rewrite bvb_subst_b.
      reflexivity.
  Qed.

End Bvb.


Section Bvbs.

  Lemma msubst_bnr_nil γ :
    msubst_bnr γ nil = nil.
  Proof with auto.
    induction γ.
    - reflexivity.
    - destruct a...
  Qed.


  (* Substitution does not change bound variables *)
  Lemma bvbs_msubst_bnr γ bs :
    bvbs (msubst_bnr γ bs) = bvbs bs.
  Proof with auto.
    revert γ.
    induction bs as [ | b bs].
    all: intros γ.
    - rewrite msubst_bnr_nil.
      reflexivity.
    - rewrite @bvbs_cons.
      rewrite msubst_bnr_cons.
      rewrite @bvbs_cons.
      rewrite bvb_msubst_b.
      rewrite IHbs with (γ := List.mdrop (bvb b) γ).
      reflexivity.
  Qed.

  Lemma bvbs_msubstA_bnr : ∀ ρ bs ,
    bvbs (msubstA_bnr ρ bs) = bvbs bs .
    (* TODO: should be similar to bvbs_msubst_bnr *)
  Admitted.

End Bvbs.


Section ExistsBvbs.

  Import ListNotations.

  Lemma In_NameIn x xs :
    In x xs <-> NameIn x xs.
  Proof with eauto using NameIn.
    split.
    {
      intros H_In.
      induction xs.
      - inversion H_In.
      - destruct H_In.
        + subst. auto using NameIn.
        + destruct (string_dec a x); subst...
    }

    {
      intros H_NameIn.
      induction H_NameIn.
      - apply or_introl...
      - apply or_intror...
    }

  Qed.

  Lemma map_bvc__bv_constructors cs :
    map bvc cs = bv_constructors cs.
  Admitted.

  Lemma existsb_appears_bound_in x bs r t :
    existsb (eqb x) (bvbs bs) = true ->
    appears_bound_in_tm x (Let r bs t).
  Proof.
    intros H_ex.
    simpl in H_ex.
    apply existsb_exists in H_ex.
    destruct H_ex as [ x' [H_In H_eq]].
    apply eqb_eq in H_eq.
    apply eq_sym in H_eq.
    subst.

    induction bs as [ | b bs].
    - contradiction.
    - rewrite @bvbs_cons in H_In.
      apply in_app_or in H_In.
      destruct H_In.
      + destruct b.
        * simpl in H.
          destruct v.
          apply in_singleton_eq in H.
          subst.
          apply ABI_Tm_Let_TermBind1.
        * simpl in H.
          destruct t0.
          contradiction H.
        * simpl in H.
          destruct d as [ [X K] YKs mfunc cs].
          apply in_inv in H.
          rewrite <- in_rev in H.
          apply ABI_Tm_Let_DatatypeBind.
          rewrite In_NameIn in *.
          destruct H.
          ** subst. eauto using NameIn.
          ** destruct (string_dec x mfunc).
            *** subst. eauto using NameIn.
            *** rewrite map_bvc__bv_constructors in H.
                eauto using NameIn.
      + auto.
  Qed.

End ExistsBvbs.
