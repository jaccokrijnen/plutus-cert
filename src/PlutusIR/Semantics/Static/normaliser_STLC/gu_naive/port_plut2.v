
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

From PlutusCert Require Import SN_STLC_named_naive SN_STLC_named2 util Util.List STLC_named STLC_named_typing. (* I don't understand why we need this for ftv defintion*)
From PlutusCert Require Import PlutusIR plutus_util Checker.


(** Substitutions *)

(* from plut to annotated stlc*)
Fixpoint f (t : ty) : STLC_named.term :=
  match t with
  | Ty_Var x => tmvar x
  | Ty_Lam x A t => @tmlam Lam x A (f t)
  | Ty_Forall x A t => @tmlam ForAll x A (f t)
  | Ty_Fun t1 t2 => @tmapp Fun (f t1) (f t2)
  | Ty_App t1 t2 => @tmapp App (f t1) (f t2)
  | Ty_IFix f1 t1 => @tmapp IFix (f f1) (f t1)
  | Ty_SOP Tss => 
  (* Two fold rights instead of concat/map to help termination checking*)
      fold_right (fun Ts acc => 
        (fold_right (fun T acc2 => @tmapp Fun (f T) acc2) acc Ts))
        (tmbuiltin PlutusIR.DefaultUniInteger) Tss
  
      (* Instead of checking for the length, we just start with something of Base Kind*)

  | Ty_Builtin d => tmbuiltin d
  end.

Compute (f (Ty_SOP [[PlutusIR.Ty_Var "a"; PlutusIR.Ty_Var "b"]; [PlutusIR.Ty_Var "c"]])).

(*
  The following lemmas are used to prove that the translation preserves the properties of the original terms. *)

Require Import Coq.Program.Equality.

Set Printing Implicit.

From PlutusCert Require Static.TypeSubstitution.

Lemma f_preserves_rename s fr T :
  rename s fr (f T) = f (TypeSubstitution.rename s fr T).
Proof.
  unfold rename; unfold TypeSubstitution.rename.
  apply PlutusIR.ty__ind with (P := fun T => mren [(s, fr)] (f T) = f (TypeSubstitution.substituteT s (PlutusIR.Ty_Var fr) T)); intros.
  all: try solve [simpl; f_equal; auto]. (* all cases without binders or lists *)
  all: try solve [simpl; destr_eqb_eq s X; try rewrite mren_id; simpl; f_equal; auto]. (* all cases with binders/vars *)
  induction H; auto.
  induction H; auto.
  simpl in IHForallP22. simpl. simpl. rewrite H. f_equal.
  apply IHForallP.
Qed.

Lemma f_preserves_ftv T :
  ftv (f T) = TypeSubstitution.ftv T.
Proof.
  apply PlutusIR.ty__ind with (P := fun T => ftv (f T) = TypeSubstitution.ftv T); intros.
  all: try solve [simpl; f_equal; auto]. 
  induction H; auto; simpl.
  induction H; auto; simpl.
  rewrite <- app_assoc.
  f_equal; auto.
Qed.

Require Import Coq.Arith.Wf_nat.

Lemma f_preserves_tv T :
  tv (f T) = TypeSubstitution.plutusTv T.
Proof.
  (* With custom induction principle*)
  apply PlutusIR.ty__ind with (P := fun T => tv (f T) = TypeSubstitution.plutusTv T); intros.
  all: try solve [simpl; f_equal; auto]. 
  induction H; auto; subst.
  induction H; auto; subst; simpl.
  rewrite <- app_assoc.
  f_equal; auto.
Qed.


Lemma f_preserves_fresh2 y s' T :
  fresh2 ((y, f s')::nil) (f T) = TypeSubstitution.fresh y s' T.
Proof.
  simpl.
  unfold fresh2.
  unfold TypeSubstitution.fresh.
  rewrite f_preserves_tv.
  assert (Htv_keys_env: (tv_keys_env
    [(y, f s')] = (y :: (TypeSubstitution.plutusTv s')))).
  {
    unfold tv_keys_env.
    f_equal.
    rewrite f_preserves_tv.
    rewrite app_nil_r.
    reflexivity.
  }
  rewrite Htv_keys_env.
  f_equal.
  rewrite string_concat_app.
  rewrite string_concat_cons.
  rewrite string_app_assoc.
  auto.
Qed.

From PlutusCert Require Type_reduction.

Lemma f_preserves_substituteTCA X U T :
  (f (TypeSubstitution.substituteTCA X U T)) = (substituteTCA X (f U) (f T)).
Proof.
  remember (f T) as fT.
  remember (size (f T)) as n.
  generalize dependent fT.
  generalize dependent T.
  induction n using lt_wf_ind.
  intros.
  induction fT; subst.
  + induction T; subst; inversion HeqfT; subst.
    autorewrite with substituteTCA.
    destr_eqb_eq X t; auto.
    (* With the current f definition, we have a not so nice inversino procedure?
      Now we need to invert again I guess.
    *)
    exfalso.
    simpl in HeqfT.
    induction l.
    * inversion HeqfT.
    * induction a.
      -- simpl in HeqfT. eapply IHl; auto.
      -- eapply IHa; inversion HeqfT; auto.
    (* The fold_left in H1 will become a long Fun STLC_named.term, so never equal to tmvar*)
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
            eapply f_preserves_fresh2.
          }
          rewrite Hfr_pres.
          f_equal.
          ++ eapply H; eauto.
            ** rewrite <- f_preserves_rename. 
              rewrite <- rename_preserves_size.
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
            eapply f_preserves_fresh2.
          }
          rewrite Hfr_pres.
          f_equal.
          ++ eapply H; eauto.
            ** rewrite <- f_preserves_rename.
               rewrite <- rename_preserves_size.
               simpl.
               lia.
            ** apply f_preserves_rename.
      -- simpl.
         f_equal.
          eapply H; eauto. simpl. lia.
    }

    (* Again a new case because of Ty_SOP*)
    induction l; simpl in H1; inversion H1.
    induction a; simpl in H2; inversion H2.
    assert (f
      (TypeSubstitution.substituteTCA X U
      (PlutusIR.Ty_SOP ([] :: l))) = f
      (TypeSubstitution.substituteTCA X U
      (PlutusIR.Ty_SOP (l)))).
    {
      autorewrite with substituteTCA. simpl. reflexivity.
    }
    rewrite H0.
    eapply IHl; intros; eauto.
    rewrite <- H0.
    eapply IHfT.
    assert (f (Ty_SOP l) = f (Ty_SOP ([] :: l))).
    {
      autorewrite with substituteTCA.
      simpl.
      auto.
    }
    rewrite <- H4.
    auto.
  + induction T; subst; inversion HeqfT; subst.
    * autorewrite with substituteTCA; simpl; f_equal; eauto; eapply H; auto; simpl; lia. 
    * autorewrite with substituteTCA; simpl; f_equal; eauto; eapply H; auto; simpl; lia. 
    * autorewrite with substituteTCA; simpl; f_equal; eauto; eapply H; auto; simpl; lia. 
    * (* The interesting SOP case*)
       induction l; subst.
       -- inversion HeqfT. 
       -- induction a; subst.
          ++ simpl.
             assert (f
            (TypeSubstitution.substituteTCA X U
            (PlutusIR.Ty_SOP ([] :: l))) = f
            (TypeSubstitution.substituteTCA X U
            (PlutusIR.Ty_SOP (l)))).
            {
              autorewrite with substituteTCA.
              simpl.
              auto.
            }
            rewrite H0.
            eapply IHl; intros; eauto.
            subst. 
            rewrite <- H0.
            eapply IHfT1.
            assert (f (Ty_SOP l) = f (Ty_SOP ([] :: l))).
            {
              autorewrite with substituteTCA.
              simpl.
              auto.
            }
            rewrite <- H2. reflexivity.
            rewrite <- H0.
            eapply IHfT2.
                        assert (f (Ty_SOP l) = f (Ty_SOP ([] :: l))).
            {
              autorewrite with substituteTCA.
              simpl.
              auto.
            }
            rewrite <- H2. 
            assumption.

          ++ autorewrite with substituteTCA.
             simpl.
             inversion HeqfT; subst.
             f_equal.
             ** eauto.
                eapply H; eauto; simpl. lia.
             ** assert (@fold_right STLC_named.term PlutusIR.ty
                  (fun (T : PlutusIR.ty) (acc2 : STLC_named.term) =>
                @tmapp Fun (f T) acc2)
                  (@fold_right STLC_named.term (list PlutusIR.ty)
                  (fun (Ts : list PlutusIR.ty) (acc : STLC_named.term) =>
                @fold_right STLC_named.term PlutusIR.ty
                  (fun (T : PlutusIR.ty) (acc2 : STLC_named.term) =>
                @tmapp Fun (f T) acc2)
                  acc
                  Ts)
                  (tmbuiltin PlutusIR.DefaultUniInteger)
                  (@TypeSubstitution.map' (list PlutusIR.ty)
                  (list PlutusIR.ty) l
                  (fun (y : list PlutusIR.ty) (_ : y ∈ l) =>
                @TypeSubstitution.map' PlutusIR.ty
                  PlutusIR.ty y
                  (fun (T : PlutusIR.ty) (_ : T ∈ y) =>
                TypeSubstitution.substituteTCA X U T))))
                  (@TypeSubstitution.map' PlutusIR.ty PlutusIR.ty
                  a0
                  (fun (y : PlutusIR.ty) (_ : y ∈ a0) =>
                TypeSubstitution.substituteTCA X U y)) = f (TypeSubstitution.substituteTCA X U (PlutusIR.Ty_SOP (a0::l)))).
    {
      autorewrite with substituteTCA.
      simpl.
      auto.
    }
    rewrite H0.
             
        assert  (@fold_right STLC_named.term PlutusIR.ty
            (fun (T : PlutusIR.ty) (acc2 : STLC_named.term) =>
          @tmapp Fun (f T) acc2)
            (@fold_right STLC_named.term (list PlutusIR.ty)
            (fun (Ts : list PlutusIR.ty) (acc : STLC_named.term) =>
          @fold_right STLC_named.term PlutusIR.ty
            (fun (T : PlutusIR.ty) (acc2 : STLC_named.term) =>
          @tmapp Fun (f T) acc2)
            acc
            Ts)
            (tmbuiltin PlutusIR.DefaultUniInteger)
            l)
            a0
         = f ((PlutusIR.Ty_SOP (a0::l)))).
         {
            simpl. auto.
         }
         rewrite H2.
         eapply H; eauto.
         clear.
         simpl.
         lia.
  + induction T; subst; inversion HeqfT; subst.
    * subst.
      autorewrite with substituteTCA.
      simpl. auto.
    * (* todo: inversion stuff, should be possible to automate, or at least to do that not in this function *)
      induction l; subst; inversion HeqfT.
      - autorewrite with substituteTCA. simpl. auto.
      - induction a; subst; inversion H2.
        
        assert (f
          (TypeSubstitution.substituteTCA X U
          (PlutusIR.Ty_SOP ([] :: l))) = f
          (TypeSubstitution.substituteTCA X U
          (PlutusIR.Ty_SOP (l)))).
        {
          autorewrite with substituteTCA.
          simpl.
          auto.
        }
        rewrite H0.
        eapply IHl; intros; auto.
        eapply H; eauto.
Qed.



        
Theorem f_preserves_step s s' :
  Type_reduction.step s s' -> step_nd (f s) (f s').
Proof.
  intros H.
  induction H; simpl; eauto; try solve [constructor; eauto].
  - rewrite f_preserves_substituteTCA.
    constructor.
  - induction f0. 
    + simpl. induction f1.
      * simpl. constructor. auto.
      * simpl. constructor. auto.
    + simpl. 
      induction x.
      * simpl. auto.
      * simpl. constructor. apply IHx.
        inversion f0; subst. auto.
Qed.

Set Printing Implicit.

Require Import Coq.Program.Equality.

Theorem f_preserves_kind Δ s K :
  Kinding.has_kind Δ s K -> STLC_named_typing.has_kind Δ (f s) K.
Proof.
  intros.
  apply Checker.prop_to_type in H.
  induction H using Kinding.has_kind_set__ind
    with (P := fun Δ s K => STLC_named_typing.has_kind Δ (f s) K)
         (P0 := fun Δ Tss => plutus_util.ForallSet2 (fun T => STLC_named_typing.has_kind Δ (f T) PlutusIR.Kind_Base) Tss)
         (P1 := fun Δ Tss => plutus_util.ForallSet (fun T => STLC_named_typing.has_kind Δ (f T) PlutusIR.Kind_Base) Tss).
  all: try solve [econstructor; eauto].
  simpl.
  induction Tss.
  - repeat constructor; induction IHhas_kind; subst; auto.
  - induction IHhas_kind_set; subst. simpl. constructor. constructor.
    induction f0.
    + auto. simpl. eapply IHIHhas_kind_set. inversion H; subst. auto.
    + simpl. constructor.
      * auto.
      * apply IHf0. clear IHf0. clear IHTss. clear IHIHhas_kind_set.
        inversion H; subst.
        inversion H3; subst.
        constructor; auto.
Qed.


(*
Jacco: Dit is blijkbaar een forward simulation
*)
Lemma sn_preimage2 {e2 : PlutusIR.ty -> PlutusIR.ty -> Type} {e : STLC_named.term -> STLC_named.term -> Type} (h : PlutusIR.ty -> STLC_named.term) (x : PlutusIR.ty) :
  (forall x y, e2 x y -> e (h x) (h y)) -> @sn STLC_named.term e (h x) -> @sn PlutusIR.ty e2 x.
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

Theorem sn_step_plut : forall s, @sn STLC_named.term step_nd (f s) -> @sn PlutusIR.ty Type_reduction.step s.
Proof.
  intros s.
  eapply @sn_preimage2 with (h := f) (e2 := Type_reduction.step) (e := step_nd).
  apply f_preserves_step.
Qed.

Corollary plutus_ty_strong_normalization s Δ K : Kinding.has_kind Δ s K -> @sn PlutusIR.ty Type_reduction.step s.
Proof.
  intros Hwk.
  apply f_preserves_kind in Hwk.
  apply strong_normalization in Hwk.
  apply sn_step_plut.
  auto.
Qed.

Print Assumptions plutus_ty_strong_normalization.