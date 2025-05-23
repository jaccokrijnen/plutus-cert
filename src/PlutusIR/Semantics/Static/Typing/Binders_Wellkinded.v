(* Note: This is maybe useful for Basekindedness proof*)

Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
From PlutusCert Require Import Analysis.BoundVars.
From PlutusCert Require Import Analysis.FreeVars.

Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Typing.Typing.
Require Export PlutusCert.PlutusIR.Semantics.Static.Typing.drop_context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.Normalisation.Normalisation.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Static.Builtins.Signatures.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Export PlutusCert.PlutusIR.Analysis.FreeVars.
Require Export PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
From PlutusCert Require Import Weakening.


From PlutusCert Require Import util.

Import Coq.Lists.List.
Import ListNotations.
Import Coq.Strings.String.
Local Open Scope string_scope.

Open Scope list_scope.

Opaque dtdecl_freshR.

Local Open Scope list_scope.


Lemma K_TyForalls_constructor : forall Δ T YKs,
      (rev (map fromDecl YKs) ++ Δ) |-* T : Kind_Base ->
      Δ |-* (Ty_Foralls YKs T) : Kind_Base.
Proof.
  intros.
  generalize dependent Δ.
  induction YKs; intros.
  - simpl. auto.
  - simpl. constructor.
    apply IHYKs.
    assert (Hr_rev: (rev
        (map fromDecl (a :: YKs)) ++
      Δ) = (rev (map fromDecl YKs) ++
      (getTyname a, getKind a) :: Δ)).
    {
      simpl. unfold fromDecl. fold fromDecl. destruct a. simpl. intuition.
    } 
    rewrite <- Hr_rev.
    auto.
Qed.

Definition notFun T1 := match T1 with | Ty_Fun _ _ => False | _ => True end.

Lemma TyApps_replaceReturnTy' T1 T2s T3 : 
  notFun T1 -> (replaceRetTy (Ty_Apps T1 T2s) T3) = T3.
Proof.
  intros.
  unfold Ty_Apps.
  rewrite <- fold_left_rev_right.
  generalize dependent T1.
  induction T2s; intros.
  - simpl. unfold notFun in H. destruct T1; intuition.
  - simpl. rewrite fold_right_app.
    eapply IHT2s. simpl. auto.
Qed.

Lemma TyApps_replaceReturnTy x T2s T3 : 
  (replaceRetTy (Ty_Apps (Ty_Var x) T2s) T3) = T3.
Proof.
  now apply TyApps_replaceReturnTy'.
Qed.

Lemma ni_map_tv_decl__ni_rev_map_fromdecl x YKs :
  ~ In x (map tvdecl_name YKs) -> ~ In x (map fst (rev (map fromDecl YKs))).
Proof.
  induction YKs; intros.
  - simpl. auto.
  - simpl.
    intros Hcontra.
    rewrite map_app in Hcontra.
    apply in_app_or in Hcontra as [Hcontra | Hcontra].
    + apply IHYKs in Hcontra; auto. apply not_in_cons in H as [_ H]; auto.
    + destruct a as [a1 a2].
      simpl in Hcontra.
      simpl in H.
      apply de_morgan2 in H as [H _].
      destruct Hcontra; auto.
Qed.

(* Proved in PR90 in SubstituteTCA.v*)
Lemma kinding_weakening_fresh : forall X T L K Δ,
  ~ In X (ftv T) ->
  Δ |-* T : K -> ((X, L) :: Δ) |-* T : K.
Proof.
Admitted.

Fixpoint insert_deltas_rec (xs : list (string * ty)) (Δ : list (string * kind)) := 
match xs with
  | nil => nil
  | (X, T):: xs' => (X, T, Δ) :: insert_deltas_rec xs' Δ
end.

Lemma insert_deltas_rec_app xs ys Δ :
  insert_deltas_rec (xs ++ ys) Δ = insert_deltas_rec xs Δ ++ insert_deltas_rec ys Δ.
Proof.
  induction xs.
  - reflexivity.
  - simpl. rewrite IHxs. 
    destruct a.
    reflexivity.
Qed.

Lemma b_r_wf__wk Δ Γ b :
  Δ ,, Γ |-ok_b Rec # b -> forall T _x, In (_x, T) (binds_Gamma b) -> (Δ |-* T : Kind_Base ).
Proof.
  intros Hb_wf T _x Hin_b.
  inversion Hb_wf as [| |? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hc_wf Hc_wk];  subst.
  all: try solve [simpl in Hin_b; inversion Hin_b; try inversion H2; subst; auto].
  (* Datatype binds *)
  clear Hb_wf.
  unfold binds_Gamma in Hin_b.
  destruct Hin_b as [Hm_bind | Hc_bind].
  - (*Case: match bind*)
    simpl in Hm_bind.
    inversion Hm_bind; subst.
    clear Hm_bind.
    destruct XK as [x x_k].
    
    apply K_TyForalls_constructor.
    simpl.
    remember (dtdecl_freshR (Datatype (TyVarDecl x x_k) YKs _x cs)) as fr.
      
    constructor; auto.
    constructor.

    (* We prove the lemma for all strings that are fresh, (not this specific one)
      because for that we can do induction. (equality of fresh vars stopped us before from using the IH.) *)
    assert (Hif_fresh: forall fr', 
      (~ In fr' ((map getTyname YKs) ++ x :: flat_map (fun c => Ty.ftv (vdecl_ty c)) cs))
      -> ((fr', Kind_Base) :: (rev (map fromDecl YKs)) ++ Δ) |-* (fold_right Ty_Fun (Ty_Var fr')
            (map (fun c : vdecl => replaceRetTy (vdecl_ty c) (Ty_Var fr')) cs)) : Kind_Base).
    {
      clear Heqfr.
      clear fr.
      intros.
      generalize dependent fr'.

      simpl in Hc_wf.

      induction cs; intros.
      - simpl. constructor. simpl. rewrite String.eqb_refl. auto.
      - simpl.
      
        assert (Hfr': fr' ∉ ((map getTyname YKs) ++ 
          x :: flat_map (fun c : vdecl => Ty.ftv (vdecl_ty c)) (cs))).
        {
          intros Hcontra.
          eapply not_in_app in H as [H11 H].
          apply in_app_iff in Hcontra as [Hcontra | Hcontra]; try contradiction; clear H11.
          apply not_in_cons in H as [H11 H].
          destruct Hcontra as [Hcontra | Hcontra]; subst; try contradiction; clear H11.
          simpl in H.
          apply not_in_app in H as [_ H].
          contradiction.
        }

        assert (Hc_wf_smaller: (forall c : vdecl,
            c ∈ cs ->
            rev (map fromDecl YKs) ++ Δ
            |-ok_c c
            : (Ty_Apps (Ty_Var x)
              (map Ty_Var
              (map tvdecl_name YKs))))).
        {
          intros.
          eapply Hc_wf. apply in_cons. auto.
        }
        assert (Hno_dup_smaller: NoDup (map vdecl_name cs)) by now inversion H3; auto.
         
        specialize (IHcs Hno_dup_smaller Hc_wk Hc_wf_smaller fr' Hfr').
        clear Hno_dup_smaller Hc_wf_smaller.
        simpl.
        constructor; eauto. (* RHS of Fun with IH*)
        
        specialize (Hc_wf a).
        assert (In a (a :: cs)) by now apply in_eq.
        specialize (Hc_wf H0).
        inversion Hc_wf; subst.
        simpl.
        apply splitTy__inversion in H1.
        subst.
        clear H0 Hfr' IHcs H2 H3 Hc_wk Hc_wf.
        induction Targs.
        + simpl.
          rewrite TyApps_replaceReturnTy.
          constructor.
          simpl. rewrite String.eqb_refl. auto.
        + simpl.
          constructor.
          * apply kinding_weakening_fresh.
            -- simpl in H.
               apply not_in_app in H as [_ H].
               apply not_in_cons in H as [_ H].
               apply not_in_app in H as [H _].
               apply not_in_app in H as [H _].
               assumption.
            -- apply H4.
               apply in_eq.
          * apply IHTargs.
            -- clear IHTargs.
               simpl in H.
               simpl.
               eapply not_in_app in H as [H11 H].
               intros Hcontra.
               apply in_app_iff in Hcontra as [Hcontra | Hcontra]; try contradiction; clear H11.
               apply not_in_cons in H as [H11 H].
               destruct Hcontra as [Hcontra | Hcontra]; subst; try contradiction; clear H11.
               apply not_in_app in H as [H H11].
               apply in_app_iff in Hcontra as [Hcontra | Hcontra]; try contradiction; clear H11.
               apply not_in_app in H as [_ H].
               contradiction.
            -- intros. apply H4. apply in_cons. auto. 
    }
    eapply Hif_fresh; subst.
    apply dtdecl_freshR__fresh.      
  - (*Case: constr bind*)
    unfold constrBinds in Hc_bind.
    rewrite <- in_rev in Hc_bind.
    apply in_map_iff in Hc_bind as [c [HconstrBind Hxincs]].
    specialize (Hc_wf c Hxincs).
    
    unfold constrBind in HconstrBind.
    destruct_match; subst. simpl in HconstrBind.
    inversion HconstrBind; subst.
    
    inversion Hc_wf; subst.
    apply splitTy__inversion in H1; simpl.
    apply K_TyForalls_constructor; subst.
    clear Hxincs Hc_wf HconstrBind.
    induction Targs; auto.
    constructor.
    * eapply H5.
      apply in_eq.
    * eapply IHTargs.
      intros.
      apply H5.
      apply in_cons; assumption.
Qed.

Lemma b_nr_wf__wk Δ Γ b:
  Δ ,, Γ |-ok_b NonRec # b -> forall T _x, In (_x, T) (binds_Gamma b) 
    -> ((binds_Delta b ++ Δ) |-* T : Kind_Base ).
Proof.
  intros Hb_wf T _x Hin_b.
  inversion Hb_wf as [| |? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hc_wf Hc_wk];  subst.
  all: try solve [simpl in Hin_b; inversion Hin_b; try inversion H2; subst; auto].
  (* Datatype binds*)
  clear Hb_wf.
  unfold binds_Gamma in Hin_b.
  destruct Hin_b as [Hm_bind | Hc_bind].
  - (*Case: match bind*)
    simpl in Hm_bind.
    inversion Hm_bind; subst.
    clear Hm_bind.
    destruct XK as [x x_k].
    apply K_TyForalls_constructor.
    simpl.
    remember (dtdecl_freshR (Datatype (TyVarDecl x x_k) YKs _x cs)) as fr.
    
    simpl in Hc_wf.
    constructor.
    {
      simpl in Hc_wk.
      eapply Kinding.weakening; eauto.
      apply append_permute__inclusion2.
      - apply drop_Δ'__inclusion.
      - simpl in H2.
        inversion H2; subst.
        now apply ni_map_tv_decl__ni_rev_map_fromdecl.
    } 
    constructor.

    assert ( forall fr', (~ In fr' ((map getTyname YKs) ++ x :: flat_map (fun c => Ty.ftv (vdecl_ty c)) cs))
      -> ((fr', Kind_Base) :: (rev (map fromDecl YKs)) ++ (x, x_k)::Δ) |-* (fold_right Ty_Fun (Ty_Var fr')
          (map (fun c : vdecl => replaceRetTy (vdecl_ty c) (Ty_Var fr')) cs)) : Kind_Base).
      {
        clear Heqfr.
        clear fr.
        intros.
        generalize dependent fr'.
        simpl in Hc_wf.

        induction cs; intros.
        - simpl. constructor. simpl. rewrite String.eqb_refl. auto.
        - assert (Hfr_smaller: fr' ∉ ((map getTyname YKs) ++ x :: flat_map (fun c : vdecl => Ty.ftv (vdecl_ty c)) (cs))).
          {
            intros Hcontra.
            eapply not_in_app in H as [H11 H].
            apply in_app_iff in Hcontra as [Hcontra | Hcontra]; try contradiction; clear H11.
            apply not_in_cons in H as [H11 H].
            destruct Hcontra as [Hcontra | Hcontra]; subst; try contradiction; clear H11.
            simpl in H.
            apply not_in_app in H as [_ H].
            contradiction.
          }

          assert (Hc_wf_smaller: (forall c : vdecl, c ∈ cs -> rev (map fromDecl YKs) ++ (drop_Δ' Δ [x])
              |-ok_c c : (Ty_Apps (Ty_Var x) (map Ty_Var (map tvdecl_name YKs))))).
          {
            intros.
            eapply Hc_wf. apply in_cons. auto.
          }
          assert (Hno_dup_smaller: NoDup (map vdecl_name cs)) by now inversion H3.
          specialize (IHcs Hno_dup_smaller Hc_wk Hc_wf_smaller fr' Hfr_smaller).
          clear Hno_dup_smaller Hc_wf_smaller.
          simpl.
          constructor; eauto. (* RHS of Fun with IH*)
          specialize (Hc_wf a).
          assert (In a (a :: cs)) by now apply in_eq.
          specialize (Hc_wf H0).
          inversion Hc_wf; subst.
          simpl.
          apply splitTy__inversion in H1.
          subst.
          clear H0 H2 H3 Hc_wk Hc_wf.
          induction Targs.
          + simpl.
            rewrite TyApps_replaceReturnTy.
            constructor.
            simpl. rewrite String.eqb_refl. auto.
          + simpl.
            constructor.
            * apply kinding_weakening_fresh.
              -- simpl in H.
                 apply not_in_app in H as [_ H].
                 apply not_in_cons in H as [_ H].
                 apply not_in_app in H as [H _].
                 apply not_in_app in H as [H _].
                 assumption.
              -- eapply Kinding.weakening.
                 2: eapply H4; apply in_eq.
                 apply inclusion_append; auto.
                 apply inclusion_no_shadow.
                 ++ eapply drop_Δ'__inclusion.
                 ++ apply dropped_not_in_drop_Δ'.
                    apply in_eq.
            * apply IHTargs.
              -- clear IHTargs.
                 simpl in H.
                 simpl.
                 eapply not_in_app in H as [H11 H].
                 intros Hcontra.
                 apply in_app_iff in Hcontra as [Hcontra | Hcontra]; try contradiction; clear H11.
                 apply not_in_cons in H as [H11 H].
                 destruct Hcontra as [Hcontra | Hcontra]; subst; try contradiction; clear H11.
                 apply not_in_app in H as [H H11].
                 apply in_app_iff in Hcontra as [Hcontra | Hcontra]; try contradiction; clear H11.
                 apply not_in_app in H as [_ H].
                 contradiction.
              -- intros. apply H4. apply in_cons. auto.
      }
      eapply H; subst.
      apply dtdecl_freshR__fresh.
  - (*Case: constr bind*)
    unfold constrBinds in Hc_bind.
    rewrite <- in_rev in Hc_bind.
    apply in_map_iff in Hc_bind.
    destruct Hc_bind as [c [HconstrBind Hxincs]].
    specialize (Hc_wf c Hxincs).
    
    unfold constrBind in HconstrBind.
    destruct_match; subst. simpl in HconstrBind.
  
    inversion HconstrBind; subst.
    
    inversion Hc_wf; subst.
    remember (Datatype XK YKs matchFunc cs) as d.

    apply splitTy__inversion in H1; simpl.

    apply K_TyForalls_constructor.
    destruct d.
    destruct t0.
    destruct XK as [x x_k].
    inversion Heqd; subst.
    clear Hxincs Hc_wf HconstrBind.
    induction Targs; auto.
    * simpl.
      simpl in Hc_wk.
      eapply Kinding.weakening; eauto.
      simpl.
      apply append_permute__inclusion2.
      -- apply drop_Δ'__inclusion.
      -- simpl in H2.
         inversion H2; subst.
         now apply ni_map_tv_decl__ni_rev_map_fromdecl.
    * simpl.
      constructor.
      -- eapply Kinding.weakening.
         2: eapply H5; apply in_eq.
         apply inclusion_append; auto; simpl.
         apply inclusion_no_shadow.
         ++ eapply drop_Δ'__inclusion.
         ++ apply dropped_not_in_drop_Δ'.
            apply in_eq.
      -- eapply IHTargs.
         intros.
         apply H5.
         apply in_cons; assumption.
Qed.

(* Insert_deltas_rec because only one binder: have the same Delta *)
Lemma b_nr_wf__map_wk Δ Γ b :
  Δ ,, Γ |-ok_b NonRec # b -> 
    map_wk (insert_deltas_rec (binds_Gamma b) (binds_Delta b ++ Δ)).
Proof.
  intros.

  assert ((forall x T, In (x, T) (binds_Gamma b) -> (binds_Delta b ++ Δ) |-* T : Kind_Base)).
  {
    intros.
    eapply b_nr_wf__wk; eauto.
  }
  induction (binds_Gamma b); intros.
  - simpl.
    constructor.
  - simpl.
    destruct a as [a1 a2].
    remember H0 as H1_copy.
    clear HeqH1_copy.
    specialize (H0 a1 a2).
    assert (In (a1, a2) ((a1, a2) :: l)) by apply in_eq.
    specialize (H0 H1).

    eapply MW_cons; auto.
    + eapply IHl; intros.
      eapply H1_copy; apply in_cons. eauto.
    + eauto.
Qed.

Lemma b_r_wf__map_wk Δ Γ b :
  Δ ,, Γ |-ok_b Rec # b ->
    map_wk (insert_deltas_rec (binds_Gamma b) (Δ)).
Proof.
 intros.

  assert ((forall x T, In (x, T) (binds_Gamma b) -> Δ |-* T : Kind_Base)).
  {
    intros.
    eapply b_r_wf__wk; eauto.
  }
  induction (binds_Gamma b); intros.
  - simpl.
    constructor.
  - simpl.
    destruct a as [a1 a2].
    remember H0 as H1_copy.
    clear HeqH1_copy.
    specialize (H0 a1 a2).
    assert (In (a1, a2) ((a1, a2) :: l)) by apply in_eq.
    specialize (H0 H1).

    eapply MW_cons; auto.
    + eapply IHl; intros.
      eapply H1_copy; apply in_cons. eauto.
    + eauto.
Qed.

Lemma bs_r_wf__map_wk (Δ : list (string * kind)) Γ bs :
  Δ ,, Γ |-oks_r bs  -> map_wk (insert_deltas_rec (flatten (map (binds_Gamma) bs)) Δ).
Proof.
  intros H.
  induction H.
  - constructor.
  - simpl.
    rewrite flatten_cons.
    rewrite insert_deltas_rec_app.
    apply map_wk_app.
    all: apply b_r_wf__map_wk in H; eauto.
Qed.

Fixpoint insert_deltas_bind_Gamma_nr (bs : list binding) (Δ : list (binderTyname * kind)) : 
      list (binderName * ty * list (binderTyname * kind)) :=
  match bs with
  | [] => []
  | (b :: bs') => (insert_deltas_bind_Gamma_nr bs' (binds_Delta b ++ Δ)) ++ (insert_deltas_rec (binds_Gamma b) (binds_Delta b ++ Δ))
  (* we do it in reverse to match the "flatten" from the definition of T_Let*)
  end.

Lemma bs_nr_wf__map_wk Δ Γ bs :
  Δ ,, Γ |-oks_nr bs -> map_wk (insert_deltas_bind_Gamma_nr bs Δ). 
Proof.
  intros H.
  induction H.
  - constructor.
  - simpl.
    apply map_wk_app.
    + eapply IHbindings_well_formed_nonrec; eauto.
    + eapply b_nr_wf__map_wk; eauto.
Qed.
