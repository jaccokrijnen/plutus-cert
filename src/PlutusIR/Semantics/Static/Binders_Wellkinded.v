(* Note: This is maybe useful for Basekindedness proof*)

Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
From PlutusCert Require Import Analysis.BoundVars.
From PlutusCert Require Import Analysis.FreeVars.

Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Typing.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.Normalisation.Normalisation.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Static.Builtins.Signatures.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Export PlutusCert.PlutusIR.Analysis.FreeVars.

From PlutusCert Require Import util.


Import Coq.Lists.List.
Import ListNotations.
Import Coq.Strings.String.
Local Open Scope string_scope.

Open Scope list_scope.

Opaque dtdecl_freshR.

Lemma b_r_wf__wk Δ Γ b :
  Δ ,, Γ |-ok_b Rec # b -> forall T _x, In (_x, T) (binds_Gamma b) -> (Δ |-* T : Kind_Base ).
Proof.
  intros Hb_wf T _x Hin_b.
  inversion Hb_wf as [| | ];  subst.
  - inversion Hin_b.
    + inversion H2; subst.
      auto.
    + inversion H2.
  - simpl in Hin_b.
    inversion Hin_b.
  - 
    clear Hb_wf.
    unfold binds_Gamma in Hin_b.
    destruct Hin_b as [Hm_bind | Hc_bind].
    + 
     (*Case: match bind*)

      (* Idea, we prove the lemma for all strings that are fresh, (not this specific one)
          because for that we can do induction. (equality of fresh vars stopped us before from using the IH.)
       *)
      simpl in Hm_bind.
      inversion Hm_bind; subst.
      clear Hm_bind.
      destruct XK as [x x_k].
      
        apply K_TyForalls_constructor.
        simpl.


        remember (dtdecl_freshR (Datatype (TyVarDecl x x_k) YKs _x cs)) as fr.
        
        simpl in H7.
        constructor; auto.

        assert (Hif_fresh:
          forall fr',
          (~ In fr' ((map getTyname YKs) ++ x :: 
              flat_map (fun c => Ty.ftv (vdecl_ty c)) cs))
          -> ((fr', Kind_Base) :: (rev (map fromDecl YKs)) ++ Δ)
                |-* (fold_right Ty_Fun (Ty_Var fr')
                (map (fun c : vdecl => replaceRetTy (vdecl_ty c) (Ty_Var fr')) cs))
              : Kind_Base)
          .
          {
            clear Heqfr.
            clear fr.
            intros.
            generalize dependent fr'.

            simpl in H7.

            induction cs; intros.
            - simpl. constructor. simpl. rewrite String.eqb_refl. auto.
            - assert (fr'
                ∉ ((map getTyname YKs) ++ x
                :: flat_map
                  (fun c : vdecl => Ty.ftv (vdecl_ty c))
                  (cs))) by admit. (* ADMIT: ~ in and smaller list*)

              assert (Hc_wf_smaller: (forall c : vdecl,
                  c ∈ cs ->
                  rev (map fromDecl YKs) ++ Δ
                  |-ok_c c
                  : (Ty_Apps (Ty_Var x)
                    (map Ty_Var
                    (map tvdecl_name YKs))))).
              {
                intros.
                eapply H7. apply in_cons. auto.
              }
              assert (Hno_dup_smaller: NoDup (map vdecl_name cs)) by admit. (* ADMIT: NoDup subset*)
              specialize (IHcs Hno_dup_smaller H8 Hc_wf_smaller fr' H0).
              clear Hno_dup_smaller Hc_wf_smaller.
              simpl.
              constructor; eauto. (* RHS of Fun with IH*)
              specialize (H7 a).
              assert (In a (a :: cs)) by now apply in_eq.
              specialize (H7 H1).
              inversion H7; subst.
              simpl.
              assert (T = fold_right Ty_Fun (Ty_Apps (Ty_Var x)
  (map Ty_Var (map tvdecl_name YKs))) Targs).
              {
                (* ADMIT: Definition of splitTy *)
                admit.
              }
              rewrite H6.
              rewrite H6 in H.
              clear H4.
              clear H6.
              induction Targs.
              + {
                simpl.
                rewrite TyApps_replaceReturnTy.
                constructor.
                simpl. rewrite String.eqb_refl. auto.
              }
              + simpl.
                constructor.
                * (* ADMIT: fr' not in a by H *) admit.
                * apply IHTargs.
                  -- (* ADMIT: freshness smaller Targs *) admit.
                  -- intros. apply H5. apply in_cons. auto.
          }
          constructor.
              
          eapply Hif_fresh.
         (* ADMIT: By freshness dtdecl_freshR definition*)
          admit.

        
    + (*Case: constr bind*)
      unfold constrBinds in Hc_bind.
      rewrite <- in_rev in Hc_bind.
      apply in_map_iff in Hc_bind.
      destruct Hc_bind as [c [HconstrBind Hxincs]].
      specialize (H7 c Hxincs).
      
      unfold constrBind in HconstrBind.
      destruct_match; subst. simpl in HconstrBind.
      (* unfold constrTy in HconstrBind. *)
      inversion HconstrBind; subst.
      
      remember (Datatype XK YKs matchFunc cs) as d.
      destruct XK as [x x_k].
      

                (* Rec *)
        inversion H7; subst.

        remember ((Datatype (TyVarDecl x x_k)
          YKs matchFunc
          cs)) as d.

          (* First cleanup extending this to multiple targs above*)
        assert (exists targ1, t = Ty_Fun targ1 (constrLastTyExpected d)) by admit.
        destruct H as [Htarg H]; subst.

        apply K_TyForalls_constructor.
        
        constructor.
        * eapply H5.
          unfold splitTy in H1.
          simpl in H1.
          inversion H1.
          subst.
          apply in_eq.
        * simpl.
          simpl in H8.
          auto.
Admitted.

Lemma b_nr_wf__wk Δ Γ b:
  Δ ,, Γ |-ok_b NonRec # b -> forall T _x, In (_x, T) (binds_Gamma b) 
    -> ((binds_Delta b ++ Δ) |-* T : Kind_Base ).
Proof.
    intros Hb_wf T _x Hin_b.
  inversion Hb_wf as [| | ];  subst.
  - inversion Hin_b.
    + inversion H2; subst.
      
      auto.
    + inversion H2.
  - simpl in Hin_b.
    inversion Hin_b.
  - 
    clear Hb_wf.
    unfold binds_Gamma in Hin_b.
    destruct Hin_b as [Hm_bind | Hc_bind].
    + 
     (*Case: match bind*)

      (* Idea, we prove the lemma for all strings that are fresh, (not this specific one)
          because for that we can do induction. (equality of fresh vars stopped us before from using the IH.)
       *)

      simpl in Hm_bind.
      inversion Hm_bind; subst.
      clear Hm_bind.
      destruct XK as [x x_k].
      
        apply K_TyForalls_constructor.
        simpl.


        remember (dtdecl_freshR (Datatype (TyVarDecl x x_k) YKs _x cs)) as fr.
        
        simpl in H7.
        constructor.
        {
          simpl in H8.
          (* ADMIT: By rearrange H7, allowd by NoDUP*)
          admit.
        } 

        assert (
          forall fr',
          (~ In fr' ((map getTyname YKs) ++ x :: 
              flat_map (fun c => Ty.ftv (vdecl_ty c)) cs))
          -> ((fr', Kind_Base) :: (rev (map fromDecl YKs)) ++ (x, x_k)::Δ)
                |-* (fold_right Ty_Fun (Ty_Var fr')
                (map (fun c : vdecl => replaceRetTy (vdecl_ty c) (Ty_Var fr')) cs))
              : Kind_Base)
          .
          {
            clear Heqfr.
            clear fr.
            intros.
            generalize dependent fr'.

            simpl in H7.

            induction cs; intros.
            - simpl. constructor. simpl. rewrite String.eqb_refl. auto.
            - assert (Hfr_smaller: fr'
                ∉ ((map getTyname YKs) ++ x
                :: flat_map
                  (fun c : vdecl => Ty.ftv (vdecl_ty c))
                  (cs))) by admit. (* ADMIT: By freshness smaller *)
    
              assert (Hc_wf_smaller: (forall c : vdecl,
                  c ∈ cs ->
                  rev (map fromDecl YKs) ++ (drop_Δ' Δ [x])
                  |-ok_c c
                  : (Ty_Apps (Ty_Var x)
                    (map Ty_Var
                    (map tvdecl_name YKs))))).
              {
                intros.
                eapply H7. apply in_cons. auto.
              }
              assert (Hno_dup_smaller: NoDup (map vdecl_name cs)) by admit. (* ADMIT: NoDUP Smaller*)
              specialize (IHcs Hno_dup_smaller H8 Hc_wf_smaller fr' Hfr_smaller).
              clear Hno_dup_smaller Hc_wf_smaller.
              simpl.
              constructor; eauto. (* RHS of Fun with IH*)
              specialize (H7 a).
              assert (In a (a :: cs)) by now apply in_eq.
              specialize (H7 H0).
              inversion H7; subst.
              simpl.
              assert (Hrew_fold: T = fold_right Ty_Fun (Ty_Apps (Ty_Var x)
  (map Ty_Var (map tvdecl_name YKs))) Targs).
              {
                (* ADMIT: Definition of splitTy *)
                admit.
              }
              rewrite Hrew_fold.
              rewrite Hrew_fold in H.
              clear H1; clear Hrew_fold. (* Should not be part of induction. *)
              induction Targs.
              + {
                simpl.
                rewrite TyApps_replaceReturnTy.
                constructor.
                simpl. rewrite String.eqb_refl. auto.
              }
              + simpl.
                constructor.
                * specialize (H4 a).
                   (* ADMIT: fr' not in a by H, then by H4 with weakening (because X also not in Delta)*) admit.
                * apply IHTargs.
                  -- (* ADMIT: freshness smaller Targs*) admit.
                  -- intros. apply H4. apply in_cons. auto.
          }


          constructor.
          eapply H.
          (* ADMIT: By freshness dtdecl_freshR definition*)
          admit.
        
    + (*Case: constr bind*)
      unfold constrBinds in Hc_bind.
      rewrite <- in_rev in Hc_bind.
      apply in_map_iff in Hc_bind.
      destruct Hc_bind as [c [HconstrBind Hxincs]].
      specialize (H7 c Hxincs).
      
      unfold constrBind in HconstrBind.
      destruct_match; subst. simpl in HconstrBind.
      (* unfold constrTy in HconstrBind. *)
      inversion HconstrBind; subst.
      
      remember (Datatype XK YKs matchFunc cs) as d.
      destruct XK as [x x_k].
      

                (* Rec *)
        inversion H7; subst.

        remember ((Datatype (TyVarDecl x x_k)
          YKs matchFunc
          cs)) as d.

          (* First cleanup extending this to multiple targs above*)
          (* ADMIT: Proving for case where we have single targ, easily extended*)
        assert (exists targ1, t = Ty_Fun targ1 (constrLastTyExpected d)) by admit.
        destruct H as [Htarg H]; subst.

        apply K_TyForalls_constructor.
        
        constructor.
        * simpl.
          simpl in H5.
          specialize (H5 Htarg).
          (* ADMIT: x, xk not in YKs or (drop_Δ' Δ [x]), hence we can weaken*)
          admit.
        * simpl.
          simpl in H7.
          simpl in H8.
          (* ADMIT: Weakening and rearrange with NODUP from H8.*)
          admit.
Admitted.

Require Import Coq.Program.Equality.

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

Fixpoint insert_deltas_bind_Gamma_nr (bs : list binding) (Δ : list (binderTyname * kind)) : list (binderName * ty * list (binderTyname * kind)) :=
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
