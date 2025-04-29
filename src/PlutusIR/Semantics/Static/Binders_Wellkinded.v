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


Lemma b_wf__wk_r Δ Γ b :
  Δ ,, Γ |-ok_b Rec # b -> forall T _x, In (_x, T) (binds_Gamma b) -> (exists K, Δ |-* T : K ).
Proof.
  intros Hb_wf T _x Hin_b.
  inversion Hb_wf as [| | ];  subst.
  - inversion Hin_b.
    + inversion H2; subst.
      exists Kind_Base.
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
      exists Kind_Base.
      destruct XK as [x x_k].
      
        apply K_TyForalls_constructor.
        simpl.


        remember (dtdecl_freshR (Datatype (TyVarDecl x x_k) YKs _x cs)) as fr.
        
        simpl in H7.
        constructor; auto.

        assert (
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
                  (cs))) by admit.

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
              assert (Hno_dup_smaller: NoDup (map vdecl_name cs)) by admit.
              specialize (IHcs Hno_dup_smaller Hc_wf_smaller fr' H0).
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
                * (* fr' not in a by H *) admit.
                * apply IHTargs.
                  -- (* freshness *) admit.
                  -- intros. apply H5. apply in_cons. auto.
          }
    (*           
          constructor.
          eapply H.
         (* By freshness definition*)
          admit.

        
    + (*Case: constr bind*)
      unfold constrBinds in Hc_bind.
      rewrite <- in_rev in Hc_bind.
      apply in_map_iff in Hc_bind.
      destruct Hc_bind as [c [HconstrBind Hxincs]].
      specialize (H6 c Hxincs).
      
      unfold constrBind in HconstrBind.
      destruct_match; subst. simpl in HconstrBind.
      (* unfold constrTy in HconstrBind. *)
      inversion HconstrBind; subst.
      exists Kind_Base. (* Ty_Forall always has Kind_Base, so also Ty_Foralls *)
      
      remember (Datatype XK YKs matchFunc cs) as d.
      destruct XK as [x x_k].
      

                (* Rec *)
        inversion H6; subst.

        remember ((Datatype (TyVarDecl x x_k)
          YKs matchFunc
          cs)) as d.

          (* First cleanup extending this to multiple targs above*)
        assert (exists targ1, t = Ty_Fun targ1 (constrLastTyExpected d)) by admit.
        destruct H as [Htarg H]; subst.

        apply K_TyForalls_constructor.
        
        constructor.
        * inversion H6; subst.
          simpl.
          eapply H9.
          unfold splitTy in H4.
          simpl in H4.
          inversion H4.
          subst.
          apply in_eq.
        * simpl.
          simpl in H7.
          auto. *)
Admitted.

Lemma b_wf__wk_nr Δ Γ b:
  Δ ,, Γ |-ok_b NonRec # b -> forall T _x, In (_x, T) (binds_Gamma b) 
    -> (exists K, (binds_Delta b ++ Δ) |-* T : K ).
Proof.
    (* intros Hb_wf H_nd T _x Hin_b.
  inversion Hb_wf as [| | ];  subst.
  - inversion Hin_b.
    + inversion H2; subst.
      exists Kind_Base.
      
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
      exists Kind_Base.
      destruct XK as [x x_k].
      
        apply K_TyForalls_constructor.
        simpl.


        remember (dtdecl_freshR (Datatype (TyVarDecl x x_k) YKs _x cs)) as fr.
        
        simpl in H7.
        constructor.
        {
          (* By rearrange H7*)
          admit.
        } 

        assert (
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
            clear H_nd.
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
                  (cs))) by admit.
    (* 
              assert (Hc_wf_smaller: (forall c : vdecl,
                  c ∈ cs ->
                  rev (map fromDecl YKs) ++ Δ
                  |-ok_c c
                  : (Ty_Apps (Ty_Var x)
                    (map Ty_Var
                    (map tvdecl_name YKs))))).
              {
                intros.
                eapply H. apply in_cons. auto.
              }
              assert (Hno_dup_smaller: NoDup (map vdecl_name cs)) by admit.
              specialize (IHcs Hno_dup_smaller Hc_wf_smaller fr' H0).
              clear Hno_dup_smaller Hc_wf_smaller.
              simpl.
              constructor; eauto. (* RHS of Fun with IH*)
              specialize (H6 a).
              assert (In a (a :: cs)) by now apply in_eq.
              specialize (H6 H1).
              inversion H6; subst.
              simpl.
              assert (T = fold_right Ty_Fun (Ty_Apps (Ty_Var x)
  (map Ty_Var (map tvdecl_name YKs))) Targs).
              {
                admit.
              }
              rewrite H8.
              rewrite H8 in H.
              clear H4.
              clear H8.
              induction Targs.
              + {
                simpl.
                rewrite TyApps_replaceReturnTy.
                constructor.
                simpl. rewrite String.eqb_refl. auto.
              }
              + simpl.
                constructor.
                * (* fr' not in a by H *) admit.
                * apply IHTargs.
                  -- (* freshness *) admit.
                  -- intros. apply H5. apply in_cons. auto.
          }


          constructor.

          (* NOT TRUE: But we can safely add the x, it doesn shadow by H_ns*)
          assert (Hrewrite_noshadow: ((fr, Kind_Base)
    :: rev (map fromDecl YKs) ++
    (x, x_k) :: Δ) 
                = (fr, Kind_Base) :: rev (map fromDecl YKs) ++ Δ) by admit.

          (* rewrite Hrewrite_noshadow. I dont understand why I cannot rewrite *)
          assert (((fr, Kind_Base) :: rev (map fromDecl YKs) ++ Δ)
              |-* (fold_right Ty_Fun (Ty_Var fr)
                (map
                (fun c : vdecl =>
              replaceRetTy (vdecl_ty c) (Ty_Var fr))
                cs))
              : Kind_Base).
              {

                        eapply H.
                        (* By freshness definition*)
                        admit.
              }
              
          admit.
        
    + (*Case: constr bind*)
      unfold constrBinds in Hc_bind.
      rewrite <- in_rev in Hc_bind.
      apply in_map_iff in Hc_bind.
      destruct Hc_bind as [c [HconstrBind Hxincs]].
      specialize (H6 c Hxincs).
      
      unfold constrBind in HconstrBind.
      destruct_match; subst. simpl in HconstrBind.
      (* unfold constrTy in HconstrBind. *)
      inversion HconstrBind; subst.
      exists Kind_Base. (* Ty_Forall always has Kind_Base, so also Ty_Foralls *)
      
      remember (Datatype XK YKs matchFunc cs) as d.
      destruct XK as [x x_k].
      

                (* Rec *)
        inversion H6; subst.

        remember ((Datatype (TyVarDecl x x_k)
          YKs matchFunc
          cs)) as d.

          (* First cleanup extending this to multiple targs above*)
        assert (exists targ1, t = Ty_Fun targ1 (constrLastTyExpected d)) by admit.
        destruct H as [Htarg H]; subst.

        apply K_TyForalls_constructor.
        
        constructor.
        * simpl.
          inversion H6; subst.
          simpl.
          (* x, xk not in YKs or Delta, hence we can weaken*)
          admit.
        * simpl.
          simpl in H7.
          By rearrange H7 *) *)
Admitted.

Require Import Coq.Program.Equality.

(* Insert_deltas_rec because only one binder: have the same Delta *)
Lemma b_wf__map_wk_nr Δ Γ b :
  Δ ,, Γ |-ok_b NonRec # b -> 
    map_wk (insert_deltas_rec (binds_Gamma b) (binds_Delta b ++ Δ)).
Proof.
  (* intros.

  assert ((forall x T, In (x, T) (binds_Gamma b) -> exists K, (binds_Delta b ++ Δ) |-* T : K)).
  {
    intros.
    eapply b_wf__wk_nr; eauto.
  }
  induction (binds_Gamma b); intros.
  - simpl.
    constructor.
  - simpl.
    destruct a as [a1 a2].
    remember H1 as H1_copy.
    clear HeqH1_copy.
    specialize (H1 a1 a2).
    assert (In (a1, a2) ((a1, a2) :: l)) by apply in_eq.
    specialize (H1 H2).
    destruct H1 as [K H1].

    eapply MW_cons; auto.
    + eapply IHl; intros.
      eapply H1_copy; apply in_cons. eauto.
    + eauto. *)
Admitted.

Lemma b_wf__map_wk_r Δ Γ b :
  Δ ,, Γ |-ok_b Rec # b ->
    map_wk (insert_deltas_rec (binds_Gamma b) (Δ)).
Proof.
 (* intros.

  assert ((forall x T, In (x, T) (binds_Gamma b) -> exists K, (Δ) |-* T : K)).
  {
    intros.
    eapply b_wf__wk_r; eauto.
  }
  induction (binds_Gamma b); intros.
  - simpl.
    constructor.
  - simpl.
    destruct a as [a1 a2].
    remember H1 as H1_copy.
    clear HeqH1_copy.
    specialize (H1 a1 a2).
    assert (In (a1, a2) ((a1, a2) :: l)) by apply in_eq.
    specialize (H1 H2).
    destruct H1 as [K H1].

    eapply MW_cons; auto.
    + eapply IHl; intros.
      eapply H1_copy; apply in_cons. eauto.
    + eauto. *)
Admitted.

Lemma bs_wf_r__map_wk (Δ : list (string * kind)) Γ bs :
  Δ ,, Γ |-oks_r bs  -> map_wk (insert_deltas_rec (flatten (map (binds_Gamma) bs)) Δ).
Proof.
  (* intros H H_ns.
  induction H.
  - constructor.
  - simpl.
    rewrite flatten_cons.
    (* rewrite insert_deltas_rec_app.
    apply map_wk_app.
    + apply b_wf__map_wk_r in H; eauto.
    + apply b_wf__map_wk_r in H; eauto. *) *)
Admitted.

Fixpoint insert_deltas_bind_Gamma_nr (bs : list binding) (Δ : list (binderTyname * kind)) : list (binderName * ty * list (binderTyname * kind)) :=
  match bs with
  | [] => []
  | (b :: bs') => (insert_deltas_bind_Gamma_nr bs' (binds_Delta b ++ Δ)) ++ (insert_deltas_rec (binds_Gamma b) (binds_Delta b ++ Δ))
  (* we do it in reverse to match the "flatten" from the definition of T_Let*)
  end.

Lemma bs_wf_nr__map_wk Δ Γ bs :
  Δ ,, Γ |-oks_nr bs -> map_wk (insert_deltas_bind_Gamma_nr bs Δ). (* Hmm, should we have nonrec insertion here?*)
Proof.
  (* intros H H_ns.
  induction H.
  - constructor.
  - simpl.
    apply map_wk_app.
    + eapply IHbindings_well_formed_nonrec; eauto.
      assert (map fst (binds_Delta b) = btvb b).
      {
        clear.
        induction b.
        - simpl. destruct v. auto.
        - simpl. destruct t. auto.
        - simpl. destruct d. destruct t. auto.
      }
      (* so just rearranged from H_ns, so yes!*)
      admit.
    + eapply b_wf__map_wk_nr.
      * eauto.
      * intros. (* subset preserves NoDup*) admit. *)
Admitted.
