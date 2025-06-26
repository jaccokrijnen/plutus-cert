
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From PlutusCert Require Import 
    Normalization.BigStep 
    Normalization.Normalizer_sound_complete
    Normalization.Normalizer
    PlutusIR 
    Static.Typing.Typing
    Util.List
    Equality
    Kinding.Checker
    Util
    SubstituteTCA
    UniqueTypes
    Typing.Binders_Wellkinded
    BaseKindedness
    Typing.Typechecker.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.

From Coq Require Import Program.Equality.

Require Import Coq.Strings.String.
Open Scope string_scope.

(* Soundness of no duplication*)
Lemma no_dup_fun_sound : forall xs, no_dup_fun xs = true -> NoDup xs.
Proof.
(* ADMITTED: Time constraints *)
Admitted.

(* Completeness of no duplication *)
Lemma no_dup_fun_complete : forall xs, NoDup xs -> no_dup_fun xs = true.
Proof.
(* ADMITTED: Time constraints *)
Admitted.

(* Soudness of well-formedness of constructors *)
Lemma constructor_well_formed_sound : 
  forall Δ c T, constructor_well_formed_check Δ c T = true -> Δ |-ok_c c : T.
Proof. 
  intros.
  destruct c.
  inversion H.
  remember (splitTy t).
  destruct p as [targs tr'].
  apply andb_true_iff in H1.
  destruct H1.
  apply Ty_eqb_eq in H0.
  subst.
  eapply W_Con; eauto.
  simpl in H1.
  intros.
  eapply forallb_forall in H1; eauto.
  unfold is_KindBase in H1.
  repeat destruct_match.
  subst.
  now apply kind_checking_sound in Heqo.
Qed.

(* Completeness of well-formedness of constructors *)
Lemma constructor_well_formed_complete : 
  forall Δ c T, Δ |-ok_c c : T -> constructor_well_formed_check Δ c T = true.
Proof.
  intros.
  destruct c.
  inversion H.
  subst.
  simpl.
  destruct (splitTy t) as [targs' T'].
  inversion H2.
  subst.
  apply andb_true_iff.
  split.
  - apply Ty_eqb_refl.
  - apply forallb_forall.
    intros.
    unfold is_KindBase.
    specialize (H4 x H0).
    apply kind_checking_complete in H4.
    rewrite H4.
    reflexivity.
Qed.

(* Recursively inserting deltas and then removing them is the identity*)
Lemma insert_remove_deltas_id (xs : list (string * ty)) Δ :
  xs = remove_deltas (insert_deltas_rec xs Δ).
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    destruct a as [x T].
    unfold remove_deltas. fold (@remove_deltas string).
    f_equal.
    assumption.
Qed.

(* Non-recursively inserting deltas based on list of binders, then removing them is the same as using binds_Gamma, up to flattening *)
Lemma insert_remove_deltas_nr_id bs Δ :
  flatten (map binds_Gamma bs) = remove_deltas (insert_deltas_bind_Gamma_nr bs Δ).
Proof.
  generalize dependent Δ.
  induction bs; intros.
  - reflexivity.
  - simpl.
    rewrite flatten_cons.
    rewrite remove_deltas_app.

    rewrite <- insert_remove_deltas_id.
    f_equal; auto.
Qed.

(* Type checking is sound *)
(* Mutually defined with soudness of binders and list of binders *)
Theorem type_checking_sound : 
 forall Δ Γ t ty, type_check Δ Γ t = Some ty -> (Δ ,, Γ |-+ t : ty).
Proof with (try apply kind_checking_sound; try eapply normalizer_sound; eauto).
  intros Δ Γ t ty.
  revert Δ Γ ty.
  eapply term_rect' with 
    (P := fun t => forall Δ Γ ty, type_check Δ Γ t = Some ty -> Δ,, Γ |-+ t : ty)
    (Q := fun b => forall Δ Γ rec, binding_well_formed_check type_check Δ Γ rec b = true -> binding_well_formed Δ Γ rec b)
    (R := fun bs => forall Δ Γ, bindings_well_formed_rec_check (binding_well_formed_check type_check Δ Γ Rec) bs = true -> bindings_well_formed_rec Δ Γ bs)
    (S := fun bs => forall Δ Γ, bindings_well_formed_nonrec_check (binding_well_formed_check type_check) Δ Γ bs = true -> bindings_well_formed_nonrec Δ Γ bs).
    repeat destruct_match.
  - (* Case: Let Rec*)
    intros bs t0.
    intros P.
    intros Ptype Δ Γ T Htc.
    inversion Htc.
    unfold bind in H0.
    repeat destruct_match.
    inversion H0; subst.
    apply andb_true_iff in Heqb. destruct Heqb.
    eapply T_LetRec; auto.
    + apply no_dup_fun_sound. auto.
    + apply no_dup_fun_sound. auto.
    + eapply map_normalizer_sound in Heqo.
      rewrite <- insert_remove_deltas_id in Heqo.
      eauto.
    + apply (map_normalizer_sound) in Heqo; eauto.
    + eapply Ptype; eauto.
    + now apply kind_checking_sound in Heqo1.
  - (* Case Let NONRec *)
    intros bs t0.
    intros P.
    intros Q.
    intros.
      inversion H.
      unfold bind in H1.
      destruct_match.
      repeat destruct_match.
      inversion H1; subst.
      eapply T_Let with (Δ' := (flatten (map binds_Delta bs) ++ Δ)%list); auto.      
      * apply (map_normalizer_sound) in Heqo. 
        rewrite <- insert_remove_deltas_nr_id in Heqo.
        exact Heqo.
      * eapply Q. auto.
      * apply kind_checking_sound in Heqo1.  auto.
  - intros. 
    inversion H; subst.
    unfold bind in H1.
    repeat destruct_match; subst.
    remember H1 as H1_copy; clear HeqH1_copy.
    apply T_Var with (T := t0); auto.
    eapply kind_checking_sound in Heqo0; auto.
    now apply normalizer_sound in H1_copy.
  - intros. 
    inversion H0.
    unfold bind in H0.
    repeat destruct_match.
    inversion H2.
    subst.
    eapply T_TyAbs...
  - intros.
    inversion H0.
    unfold bind in H2.
    repeat destruct_match.
    inversion H2.
    subst.
    apply T_LamAbs...
  - intros.
    inversion H1.
    repeat destruct_match.
    inversion H3; subst.
    eapply T_Apply with (T1n := t3_1).
    + eapply H; eauto.
    + eapply H0; eauto.
      apply Ty_eqb_eq in Heqb.
      now subst.
  - intros.
    inversion H.
    unfold bind in H1.
    repeat destruct_match.
    inversion H1; subst.
    apply T_Constant.
  - intros.
    inversion H.
    unfold bind in H1.
    repeat destruct_match.
    inversion H1; subst.
    apply normalizer_sound in Heqo.
    now apply T_Builtin with (T := lookupBuiltinTy d).
  - intros. inversion H0. unfold bind in H2. repeat destruct_match.
    inversion H2. subst.
    apply Kind_eqb_eq in Heqb0.
    subst.
    apply T_TyInst with (X := b) (K2 := k0) (T1n := t3) (T2n := t4); eauto.
    + apply kind_checking_sound. auto.
    + apply normalizer_sound in Heqo1. auto.
    + apply normalizer_sound in Heqo2. auto.
  - intros.
    unfold type_check in H.
    
    
    unfold bind in H.
    repeat destruct_match.
    inversion H.
    subst.
    apply T_Error.
    + now apply kind_checking_sound.
    + apply normalizer_sound in Heqo. 
      assumption.
  - intros.
    inversion H0.
    unfold bind in H2.
    repeat destruct_match.
    inversion H2.
    subst.
    apply Ty_eqb_eq in Heqb0.
    rewrite andb_true_iff in Heqb.
    destruct Heqb as [Heqb1 Heqb2].
    apply Kind_eqb_eq in Heqb1.
    apply Kind_eqb_eq in Heqb2.
    subst.
    apply T_IWrap with (K := k1_5) (T0n := t6)...
  - intros.
    inversion H0.
    unfold bind in H2.
    repeat destruct_match.
    inversion H2. subst.
    apply T_Unwrap with (Fn := t2_1) (Tn := t2_2) (K := k)...
  - intros.
    inversion H.
  - intros.
    inversion H0.
  - intros.
    inversion H0.
    repeat destruct_match.
    subst.
    apply W_Term with (Tn := t3).
    + apply kind_checking_sound in Heqo.
      assumption.
    + now apply normalizer_sound in Heqo1.
    + apply Ty_eqb_eq in H2.
      subst.
      eapply H; eauto.
  - intros.
    inversion H.
    repeat destruct_match.
    apply W_Type.
    apply kind_checking_sound in Heqo.
    apply Kind_eqb_eq in H1.
    subst.
    assumption.
  - (* W_Data *)
    intros.
    inversion H.
    repeat destruct_match; subst.
    + (* NonRec *)
      apply andb_true_iff in Heqb0 as [Hdup1 Hdup2].
      
      repeat destruct_match; subst.
      eapply W_Data.
      * eauto.
      * reflexivity.
      * reflexivity.
      * constructor.
        -- auto.
        -- apply no_dup_fun_sound; auto.
      * apply no_dup_fun_sound. auto.
      * reflexivity.
      * reflexivity.
      * eauto.
      * intros.
        simpl.
        eauto.
        assert (constructor_well_formed_check (rev (map fromDecl l) ++ (drop_Δ' Δ [tvdecl_name t0])) c (Ty_Apps (Ty_Var (tvdecl_name t0)) (map Ty_Var (map tvdecl_name l))) = true).
        { 
            eapply (forallb_forall) in Heqb1.
          - exact Heqb1.
          - assumption.
        }
        apply constructor_well_formed_sound.
        auto.
      * eapply kind_checking_sound; eauto.
    + apply andb_true_iff in Heqb0 as [Hdup1 Hdup2].
      repeat destruct_match; subst.
      eapply W_Data; eauto.
      * constructor; auto.
        apply no_dup_fun_sound; auto.
      * apply no_dup_fun_sound; auto.
      * intros.
        simpl.
        assert (constructor_well_formed_check (rev (map fromDecl l) ++ Δ) c (Ty_Apps (Ty_Var (tvdecl_name t0)) (map Ty_Var (map tvdecl_name l))) = true).
        { eapply (forallb_forall) in Heqb1.
          - exact Heqb1.
          - assumption.
        }
        now apply constructor_well_formed_sound.
      * eapply kind_checking_sound; eauto.
  - intros.
    apply W_ConsB_Rec.
    + apply H.
      inversion H1.
      apply andb_true_iff in H3.
      destruct H3.
      rewrite H2.
      rewrite H3.
      auto.
    + eapply H0.
      inversion H1.
      apply andb_true_iff in H3.
      destruct H3.
      rewrite H2.
      rewrite H3.
      auto.
  - intros.
    apply W_NilB_Rec.
  - intros.
    inversion H1.
    destruct_match.
    apply andb_true_iff in H3.
    destruct H3.
    eapply W_ConsB_NonRec.
    + apply H.
      assumption.
    + apply map_normalizer_sound in Heqo.
      eauto.
      rewrite <- insert_remove_deltas_id in Heqo.
      exact Heqo.
    + eapply H0.
      intuition.
  - intros.
    apply W_NilB_NonRec.
Qed.

(* Type checking is complete *)
Theorem type_checking_complete : forall Δ Γ t ty,
    (Δ ,, Γ |-+ t : ty) -> type_check Δ Γ t = Some ty.
Proof.
  intros.
  apply has_type_mut_ind with         
        (P := fun Δ Γ t T _ => type_check Δ Γ t = Some T)
        (P0 := fun Δ Γ l _ => bindings_well_formed_rec_check (binding_well_formed_check type_check Δ Γ Rec) l = true) 
        (P1 := fun Δ Γ l _ => bindings_well_formed_nonrec_check (binding_well_formed_check type_check) Δ Γ l = true )
        (P2 := fun Δ Γ rec b  _ => binding_well_formed_check type_check Δ Γ rec b = true) 
        ; simpl; auto; intros.
  - (*Case T_Var *)
    rewrite e. simpl. 
    eapply kind_checking_complete in h.
    rewrite h.
    eapply normalizer_complete; eauto.
    eapply kind_checking_sound; eauto.
  - (* Case: T_LamAbs *)
    eapply (normalizer_complete h) in n.
    rewrite n. simpl.
    apply kind_checking_complete in h; rewrite h.
    rewrite H0; auto.
  - (* Case: T_Apply *)
    rewrite H0.
    rewrite H1.
    now rewrite -> Ty_eqb_refl.
  - (* Case: T_TyAbs *) 
    rewrite H0; auto.
  - (* Case: T_Inst *)
    rewrite H0.
    apply (normalizer_complete h0) in n; rewrite n; simpl.
    apply kind_checking_complete in h0; rewrite h0.
    rewrite -> Kind_eqb_refl.
    
    assert (Δ0 |-* (substituteTCA X T2n T1n) : Kind_Base) as Hwk_subst.
    {
      assert (((X, K2)::Δ0) |-* T1n : Kind_Base).
      {
        apply has_type__basekinded in h.
        inversion h; subst.
        assumption.
      }
      eapply substituteTCA_preserves_kinding; eauto.
      eapply normalizer_preserves_kinding; eauto.
      eapply kind_checking_sound; eauto.
    }
    unfold bind.
    now apply (normalizer_complete Hwk_subst) in n0; rewrite n0; simpl.
  - (* Case T_IWrap *)
    apply (normalizer_complete h) in n; rewrite n; simpl.
    apply (normalizer_complete h0) in n0; rewrite n0; simpl.

    assert (Δ0 |-* (unwrapIFix Fn K Tn) : Kind_Base).
    {
      eapply unwrapIFix__well_kinded; eauto.
      - eapply normalizer_preserves_kinding; eauto.
      - eapply normalizer_preserves_kinding; eauto.
    }

    apply kind_checking_complete in h; rewrite h.
    apply kind_checking_complete in h0; rewrite h0.
    (* apply kind_checking_complete in H1. *)
    apply (normalizer_complete H1) in n1; rewrite n1; simpl.

    rewrite H0.
    rewrite Kind_eqb_refl; simpl.
    now rewrite Ty_eqb_refl.
  - (* Case: T_Unwrap*)
    rewrite H0.

    assert (Δ0 |-* (unwrapIFix Fn K Tn) : Kind_Base).
    {
      eapply unwrapIFix__well_kinded; eauto.
      apply has_type__basekinded in h.
      inversion h; subst.
      apply (unique_kinds Δ0 Tn K0 K H4) in h0; subst.
      assumption.
    }

    apply kind_checking_complete in h0; rewrite h0.
    unfold bind.
    apply (normalizer_complete H1) in n; rewrite n.
    reflexivity.
  - (* Case: T_Builtin*)
    subst.
    eapply normalizer_complete in n.
    rewrite n. simpl. reflexivity.
    apply lookupBuiltinTy__well_kinded. 
  - (* Case: T_Error *)
    unfold bind.
    apply (normalizer_complete h) in n; rewrite n.
    apply kind_checking_complete in h; rewrite h.
    reflexivity.
  - (* Case: T_Let (NonRec)*)
    intros. simpl. subst.
    unfold bind.

    apply bs_nr_wf__map_wk in b.
    assert (map_normalizer (insert_deltas_bind_Gamma_nr bs Δ0) = Some bsGn).
    {
      assert (flatten (map binds_Gamma bs) = remove_deltas (insert_deltas_bind_Gamma_nr bs Δ0)).
      { 
        apply insert_remove_deltas_nr_id.
      }
      rewrite H2 in m.
      apply (map_normalizer_complete b) in m.
      assumption.
    }
    unfold bind.
    rewrite H2.
    rewrite H0.
    rewrite H1.
    
    apply kind_checking_complete in h0; rewrite h0; auto.
  - (* Case: T_LetRec *)
    destruct (no_dup_fun (btvbs bs) &&
no_dup_fun (bvbs bs)) eqn:no_dup_eqn.
    {
      intros. simpl. subst.
      apply bs_r_wf__map_wk in b.
      - assert ( (* insert then remove deltas is id*)
        (flatten (map binds_Gamma bs)) = remove_deltas (insert_deltas_rec (flatten (map binds_Gamma bs)) (flatten (map binds_Delta bs) ++
    Δ0))).
        {
          apply insert_remove_deltas_id.
        }
        rewrite H2 in m.
        apply (map_normalizer_complete b) in m.
        unfold bind.
        rewrite m.
        rewrite H0.
        rewrite H1.
        
        apply kind_checking_complete in h0; rewrite h0; reflexivity.
    }
    apply andb_false_iff in no_dup_eqn. exfalso.
    
    destruct no_dup_eqn.
    + apply no_dup_fun_complete in n. rewrite n in H2. discriminate H2.
    + apply no_dup_fun_complete in n0. rewrite n0 in H2. discriminate H2.
  - (* Case: ? *)
    intros. simpl. rewrite H0. auto.
  - (* Case: ? *)

    
    assert (binds_Gamma b = remove_deltas (insert_deltas_rec (binds_Gamma b) (binds_Delta b ++ Δ0))).
    {
      apply insert_remove_deltas_id.
    }
    rewrite H2 in m.
    apply (map_normalizer_complete) in m.
    + unfold bind.
      rewrite m.
      apply andb_true_iff.
      split.
      * auto.
      * eapply H1.
    + apply b_nr_wf__map_wk in b0; auto.

  - intros. simpl. rewrite H0.
    apply (normalizer_complete h) in n; rewrite n.
    rewrite Ty_eqb_refl.
    apply kind_checking_complete in h; rewrite h.
    auto.
  - intros. simpl. apply kind_checking_complete in h; rewrite h. auto. apply Kind_eqb_eq. reflexivity.
  - (* W_Data *)
    destruct dtd.
    destruct rec.
    {
      inversion e; subst.
      destruct (in_dec string_dec (tvdecl_name XK) (map tvdecl_name YKs)) as [i | ni] eqn:Hindec.
      {
        exfalso.
        inversion n; subst.
        contradiction.
      }


      simpl.
      destruct (no_dup_fun (map tvdecl_name YKs) &&
        no_dup_fun (map vdecl_name cs)) eqn:no_dup.
    + inversion e; subst.
      apply no_dup_fun_complete in n.
      simpl in n.
      destruct_match.
      subst.
      clear e. clear n. clear n0. clear no_dup.
      induction cs; intros.
      -- simpl. 
         apply kind_checking_complete in y.
         simpl in y.
         rewrite y. reflexivity.
      -- assert (forallb
          (fun c0 : vdecl =>
        constructor_well_formed_check
          (rev (map fromDecl YKs) ++ drop_Δ' Δ0 [tvdecl_name XK]) c0
          (Ty_Apps (Ty_Var (tvdecl_name XK)) (map Ty_Var (map tvdecl_name YKs))))
          (a :: cs) = true).
          {
            eapply andb_true_intro. split.
            eapply constructor_well_formed_complete.
            eapply c. apply in_eq.
            assert ((if
                      forallb (fun c0 : vdecl =>
                      constructor_well_formed_check (rev (map fromDecl YKs) ++ drop_Δ' Δ0 [tvdecl_name XK]) c0 (Ty_Apps (Ty_Var (tvdecl_name XK))
                        (map Ty_Var (map tvdecl_name YKs))))                        cs then
                      match kind_check (fromDecl XK :: rev (map fromDecl YKs) ++ drop_Δ' Δ0 [tvdecl_name XK])
                        (Ty_Apps (Ty_Var (tvdecl_name XK)) (map Ty_Var (map tvdecl_name YKs)))
                      with | Some Kind_Base => true | _ => false end else false) = true).
                      {
                        eapply IHcs.
                        intros.
                        eapply c. apply in_cons. auto.
                        auto.
                      }
        destruct_match.
        auto.
          }
        rewrite H0.
        eapply kind_checking_complete in y.
        simpl in y.
        rewrite y.
        reflexivity.
    + exfalso.
      subst.
      inversion e; subst.
      apply andb_false_iff in no_dup.
      destruct no_dup as [DupTV | DUPV].
      * apply no_dup_fun_complete in n. simpl in n. destruct_match. rewrite n in DupTV. inversion DupTV.
      * apply no_dup_fun_complete in n0. rewrite n0 in DUPV. inversion DUPV.
    }
    {
      inversion e; subst.
      destruct (in_dec string_dec (tvdecl_name XK) (map tvdecl_name YKs)) eqn:Hindec.
      {
        exfalso.
        inversion n; subst.
        contradiction.
      }


      simpl.
      destruct (no_dup_fun (map tvdecl_name YKs) &&
        no_dup_fun (map vdecl_name cs)) eqn:no_dup.
    + inversion e; subst.
      apply no_dup_fun_complete in n.
      simpl in n.
      destruct_match.
      subst.
      clear e. clear n. clear n0. clear no_dup.
      induction cs; intros.
      -- simpl. eapply kind_checking_complete in y. simpl in y. rewrite y. reflexivity.
      -- assert (forallb
              (fun c0 : vdecl =>
            constructor_well_formed_check (rev (map fromDecl YKs) ++ Δ0) c0
              (Ty_Apps (Ty_Var (tvdecl_name XK)) (map Ty_Var (map tvdecl_name YKs))))
              (a :: cs) = true).
          {
            eapply andb_true_intro. split.
            eapply constructor_well_formed_complete.
            eapply c. apply in_eq.
            assert ((if
                      forallb (fun c0 : vdecl =>
                      constructor_well_formed_check (rev (map fromDecl YKs) ++ Δ0) c0 (Ty_Apps (Ty_Var (tvdecl_name XK))
                        (map Ty_Var (map tvdecl_name YKs))))                        cs then
                      match kind_check (rev (map fromDecl YKs) ++ Δ0)
                        (Ty_Apps (Ty_Var (tvdecl_name XK)) (map Ty_Var (map tvdecl_name YKs)))
                      with | Some Kind_Base => true | _ => false end else false) = true).
                      {
                        eapply IHcs.
                        intros.
                        eapply c. apply in_cons. auto.
                        auto.
                      }
        destruct_match.
        auto.
          }
        rewrite H0.
        eapply kind_checking_complete in y.
        simpl in y.
        rewrite y.
        reflexivity.
    + exfalso.
      subst.
      inversion e; subst.
      apply andb_false_iff in no_dup.
      destruct no_dup as [DupTV | DUPV].
      * apply no_dup_fun_complete in n.  simpl in n. destruct_match. rewrite n in DupTV. inversion DupTV.
      * apply no_dup_fun_complete in n0. rewrite n0 in DUPV. inversion DUPV.
    }
Qed.
