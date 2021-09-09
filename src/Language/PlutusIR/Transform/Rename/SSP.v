Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Transform.Rename.
Require Import PlutusCert.Language.PlutusIR.Analysis.FreeVars.

Require Import Coq.Logic.FunctionalExtensionality.

(*
Require Import Coq.Lists.List.
Import ListNotations.
*)

Require Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.ContextInvariance.

Definition rename_result := @rename_result name.
Definition environment := list (name * rename_result).
Definition lookupRR : environment -> name -> option rename_result := lookupRR eqb.
Definition lookupV : environment -> rename_result -> option name := lookupV eqb.
Definition Rename : environment -> Term -> Term -> Type := Rename eqb.
Definition RenameBindingsNonRec : environment -> environment -> list Binding -> list Binding -> Type := RenameBindingsNonRec eqb.
Definition RenameBindingsRec : environment -> environment -> list Binding -> list Binding -> Type := RenameBindingsRec eqb.
Definition RenameBinding : environment -> environment -> Binding -> Binding -> Type := RenameBinding eqb.
Definition Rename_dtdecl : environment -> environment -> DTDecl -> DTDecl -> Type := Rename_dtdecl eqb.
Definition Rename_var_bind : environment -> name * rename_result -> name -> name -> Type := @Rename_var_bind name tyname eqb.
Definition Rename_constrs : environment -> environment -> list constructor -> list constructor -> Type := Rename_constrs eqb.
Definition Rename_constr : environment -> name * rename_result -> constructor -> constructor -> Type := Rename_constr eqb.


Fixpoint RenameContext (env : environment) (Gamma : Context) : Context :=
  match env with
  | nil => Gamma
  | (x, RenamedTo u) :: env' => 
      match lookupT Gamma x with
      | None => 
          RenameContext env' Gamma
      | Datatypes.Some T => 
          u |T-> T ; RenameContext env' (deleteT x Gamma)
      end
  | (x, Unchanged) :: env' => 
      match lookupT Gamma x with
      | None => 
          RenameContext env' Gamma
      | Datatypes.Some T => 
          x |T-> T ; RenameContext env' (deleteT x Gamma)
      end
  end.

Lemma deleteT_ignores_kinds : forall Gamma x,
    snd (deleteT x Gamma) = snd Gamma.
Proof. intros. unfold deleteT. reflexivity. Qed.

Lemma RenameContext_ignores_kinds : forall env Gamma,
    snd (RenameContext env Gamma) = snd Gamma.
Proof.
  induction env.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    destruct a.
    destruct r.
    + destruct (lookupT Gamma s).
      * simpl.
        rewrite IHenv.
        rewrite deleteT_ignores_kinds.
        reflexivity.
      * apply IHenv.
    + destruct (lookupT Gamma s).
      * simpl.
        rewrite IHenv.
        rewrite deleteT_ignores_kinds.
        reflexivity.
      * apply IHenv.
Qed.

Inductive coincides (freevars: list name) : environment -> Context -> Context -> Prop :=
  | COI_nil :
      coincides freevars nil emptyContext emptyContext
  | COI_cons_RenamedTo : forall env Gamma Gamma' x w T,
      coincides freevars env Gamma Gamma' ->
      w <> x ->
      ~(List.In w freevars) ->
      ~(List.In (RenamedTo w) (List.map snd env)) ->
      coincides freevars ((x, RenamedTo w) :: env) (x |T-> T; Gamma) (w |T-> T; Gamma')
  | COI_cons_Unchanged : forall env Gamma Gamma' x T,
      coincides freevars env Gamma Gamma' ->
      coincides freevars ((x, Unchanged) :: env) (x |T-> T; Gamma) (x |T-> T; Gamma')
.

Lemma p : forall fv1 fv2 env Gamma Gamma',
    coincides (fv1 ++ fv2) env Gamma Gamma' ->
    coincides fv2 env Gamma Gamma'.
Proof.
  intros.
  induction H.
  - apply COI_nil.
  - apply COI_cons_RenamedTo; auto.
    intros Hcon.
    apply H1.
    apply List.in_or_app.
    right.
    apply Hcon.
  - apply COI_cons_Unchanged; auto.
Qed.

Lemma p2 : forall fv1 fv2 env Gamma Gamma',
    coincides (fv1 ++ fv2) env Gamma Gamma' ->
    coincides fv1 env Gamma Gamma'.
Proof.
  intros.
  induction H.
  - apply COI_nil.
  - apply COI_cons_RenamedTo; auto.
    intros Hcon.
    apply H1.
    apply List.in_or_app.
    left.
    apply Hcon.
  - apply COI_cons_Unchanged; auto.
Qed.

Lemma p3 : forall fv x env Gamma Gamma',
    coincides fv env Gamma Gamma' ->
    coincides (delete_all eqb x fv) env Gamma Gamma'.
Proof. Admitted.

Lemma b : forall env x w,
    lookupRR env x = Datatypes.Some (RenamedTo w) ->
    List.In (RenamedTo w) (List.map snd env).
Proof.
  induction env.
  - intros.
    inversion H.
  - intros.
    simpl.
    destruct a.
    destruct (s =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      simpl in H.
      rewrite eqb_refl in H.
      inversion H. subst.
      left.
      reflexivity.
    + simpl in H.
      rewrite Heqb in H.
      right.
      eapply IHenv; eauto.
Qed.

Lemma e' : forall freevars env Gamma Gamma' x w T,
    coincides freevars env Gamma Gamma'->
    List.In x freevars ->
    lookupRR env x = Datatypes.Some (RenamedTo w) ->
    lookupT Gamma x = Datatypes.Some T ->
    lookupT Gamma' w = Datatypes.Some T.
Proof.
  intros freevars env Gamma Gamma' x w T V.
  generalize dependent x.
  generalize dependent T.
  generalize dependent w.
  induction V.
  - intros.
    inversion H0.
  - intros. 
    destruct (x =? x0) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      simpl in H3.
      rewrite eqb_refl in H3.
      inversion H3. subst.
      rewrite lookupT_eq.
      rewrite lookupT_eq in H4.
      assumption.
    + apply eqb_neq in Heqb as Hneq.
      rewrite lookupT_neq in H4; auto.
      simpl in H3.
      rewrite Heqb in H3.
      destruct (w =? w0) eqn:Heqb'.
      * apply eqb_eq in Heqb'.
        subst.
        apply b in H3.
        apply H1 in H3.
        destruct H3.
      * apply eqb_neq in Heqb' as Hneq'.
        rewrite lookupT_neq; eauto.
  - intros.
    destruct (x =? x0) eqn:Heqb.
    + simpl in H0.
      rewrite Heqb in H0.
      inversion H0.
    + apply eqb_neq in Heqb as Hneq.
      simpl in H0.
      rewrite Heqb in H0.
      rewrite lookupT_neq in H1; auto.
      destruct (x =? w) eqn:Heqb'.
      * apply eqb_eq in Heqb' as Heq'.
        subst.
        rewrite lookupT_eq.
        apply b in H0.
        apply skip.
      * apply eqb_neq in Heqb' as Hneq'.
        eapply IHV in H0 as H10; eauto.
        rewrite lookupT_neq; auto.
Qed.

Lemma e: forall freevars env Gamma Gamma' x T,
  coincides freevars env Gamma Gamma'->
  List.In x freevars ->
  lookupRR env x = Datatypes.Some Unchanged ->
  lookupT Gamma x = Datatypes.Some T ->
  lookupT Gamma' x = Datatypes.Some T.
Proof.
  intros freevars env Gamma Gamma' x T V.
  generalize dependent x.
  generalize dependent T.
  induction V.
  - intros.
    inversion H0.
  - intros. 
    destruct (x =? x0) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      simpl in H3.
      rewrite Heqb in H3.
      inversion H3.
    + apply eqb_neq in Heqb as Hneq.
      simpl in H3.
      rewrite Heqb in H3.
      rewrite lookupT_neq in H4; auto.
      destruct (w =? x0) eqn:Heqb'.
      * apply eqb_eq in Heqb' as Heq'.
        subst.
        apply H0 in H2.
        destruct H2.
      * apply eqb_neq in Heqb' as Hneq'.
        rewrite lookupT_neq; auto.
  - intros.
    destruct (x =? x0) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      rewrite lookupT_eq.
      rewrite lookupT_eq in H1.
      assumption.
    + apply eqb_neq in Heqb as Hneq.
      rewrite lookupT_neq; auto.
      apply IHV.
      * assumption.
      * simpl in H0.
        rewrite Heqb in H0.
        assumption.
      * rewrite lookupT_neq in H1; auto.
Qed.


Lemma renaming_exhaustive : forall env x w t1 t2,
    lookupRR env x = Datatypes.Some (RenamedTo w) ->
    Rename env t1 t2 ->
    ~(appears_free_in x t2).
Proof. Admitted.


(* Predicate for the [has_type] datatype *)
Definition P_ht Gamma t1 T := 
  forall env Gamma' t2, 
    coincides (free_vars eqb t1) env Gamma Gamma' ->
    Rename env t1 t2 -> 
    Gamma' |-+ t2 : T.

(* Predicate for the [constructor_well_formed] datatype *)
Definition P_cwf Gamma c := Gamma |-ok_c c.

(* Predicate for the [bindings_well_formed_nonrec] datatype *)
Definition P_bwfnr Gamma bs1 :=
    forall env env' bs2,
      RenameBindingsNonRec env env' bs1 bs2 ->
      (RenameContext env Gamma) |-oks_nr bs2.

(* Predicate for the [bindings_well_formed_rec] datatype *)
Definition P_bwfr Gamma bs1 :=
  forall env env' bs2,
    RenameBindingsRec env env' bs1 bs2 ->
    (RenameContext env Gamma) |-oks_r bs2.

(* Predicate for the [binding_well_formed] datatype *)
Definition P_bwf Gamma b1 := 
  forall env env' b2,
      RenameBinding env env' b1 b2 ->
      (RenameContext env Gamma) |-ok b2.

Axiom skip : forall P, P.


Theorem Rename__SSP : forall Gamma t1 T,
    Gamma |-+ t1 : T ->
    P_ht Gamma t1 T.
Proof.
  apply has_type__ind with 
    (P := P_ht) 
    (P0 := P_cwf) 
    (P1 := P_bwfnr) 
    (P2 := P_bwfr) 
    (P3 := P_bwf).
  - (* T_Let *)
    apply skip.
  - (* T_LetRec *)
    apply skip.

  - (* T_Var *)
    intros Gamma x T Hlookup.
    unfold P_ht.
    intros env Gamma' t' V Hrename.

    inversion Hrename.
    + subst.
      apply T_Var.
      eapply e'; eauto.
      simpl.
      left.
      reflexivity.

    + (* RenameVarEq *) 
      subst.
      apply T_Var.
      eapply e; eauto.
      simpl.
      left.
      reflexivity.


  - (* T_TyAbs *)
    apply skip.
  - (* T_LamAbs *)
    intros Gamma x T1 t0 T2 Htyp_t0 IH_t0 Hkind_T1. 
    unfold P_ht. 
    intros env Gamma' t' V Hrename.

    inversion Hrename.
    + (* RenameLamAbsRename *) 
      subst.
      rename t'0 into t0'.
      apply T_LamAbs.
      * unfold P_ht in IH_t0.
        eapply IH_t0; eauto.
        apply COI_cons_RenamedTo; auto. 
        unfold free_vars in V.
        fold (@free_vars name tyname eqb) in V.
        apply skip.
      * apply skip.
    + subst.
      rename t'0 into t0'.
      apply T_LamAbs.
      * unfold P_ht in IH_t0.
        eapply IH_t0; eauto.
        apply COI_cons_Unchanged; auto.

        (*eapply p3.
        eapply IH_t0 in X0 as X1; eauto.
        -- simpl in X1. 
           rewrite update_eq in X1. 
           rewrite deleteT_extendT_shadow in X1.
           assert (~(appears_free_in x t0')). {
             apply renaming_exhaustive with ((x, RenamedTo w) :: env) w t0.
             - simpl.
               rewrite eqb_refl.
               reflexivity.
             - auto. 
           }
           eapply context_invariance; eauto.
           ++ intros.
              destruct (w =? x0) eqn:Hwx0. 
              ** apply eqb_eq in Hwx0.
                 subst.
                 rewrite lookupT_eq.
                 rewrite lookupT_eq.
                 reflexivity.
              ** apply eqb_neq in Hwx0.
                 rewrite lookupT_neq; auto.
                 rewrite lookupT_neq; auto.
                 destruct (x =? x0) eqn:Hxx0.
                 --- apply eqb_eq in Hxx0.
                     subst.
                     apply H in H0.
                     destruct H0.
                 --- apply eqb_neq in Hxx0.
                     apply skip.
           ++ simpl.
              apply skip.
       -- apply skip.
      * apply skip.
    + apply skip.*)
    apply skip. * apply skip.         
         
  - (* T_Apply *)
    intros Gamma t1 t2 T1 T2 Htyp_t1 IH_t1 Htyp_t2 IH_t2.
    unfold P_ht.
    intros env Gamma' t' V Hrename.
    
    inversion Hrename. subst.
    apply T_Apply with T1.
    + eapply IH_t1; eauto.
      eauto using p2.
    + eapply IH_t2; eauto.
      eauto using p.
  - (* T_Constant *)
    intros Gamma u a. 
    unfold P_ht. 
    intros env Gamma' t' V Hrename.
    inversion Hrename. subst.
    apply T_Constant.
  - (* T_Builtin *)
    intros Gamma f.
    unfold P_ht.
    intros env Gamma' t' V Hrename.
    inversion Hrename. subst.
    apply T_Builtin.
  - (* T_TyInst *)
    intros Gamma t0 T2 T1 X K2 S Htyp_t0 IH_t0 Hkind_T2 Hbeta.
    unfold P_ht.
    intros env Gamma' t' V Hrename.
    inversion Hrename. subst.
    rename t'0 into t0'.
    apply T_TyInst with T1 X K2.
    + eapply IH_t0; eauto.
    + apply skip.
    + reflexivity.
  - (* T_Error *)
    intros Gamma T Hkind_T.
    unfold P_ht.
    intros env Gamma' t' V Hrename.
    inversion Hrename. subst.
    apply T_Error.
    apply skip.
  - (* T_IWrap *)
    intros Gamma F T M K S Hbeta Htyp_M IH_M Hkind_T HKind_F.
    unfold P_ht.
    intros env Gamma' t' V Hrename.
    inversion Hrename. subst.
    rename t'0 into M'.
    eapply T_IWrap.
    + reflexivity.
    + eapply IH_M; eauto.
    + apply skip.
    + apply skip.
  - (* T_Unwrap *)
    intros Gamma M F K T S Htyp_M IH_M Hkind_T Hbeta.
    unfold P_ht.
    intros env Gamma' t' V Hrename.
    inversion Hrename. subst.
    rename t'0 into M'.
    eapply T_Unwrap.
    + eapply IH_M; eauto.
    + apply skip.
    + reflexivity. 

  - (* W_Con *)
    intros Gamma x T ar Hkinds.
    unfold P_cwf.
    apply W_Con; auto.

  - (* W_NilB_NonRec *)
    intros Gamma.
    unfold P_bwfnr.
    intros env env' bs' Hrename.
    inversion Hrename. subst.
    apply W_NilB_NonRec.
  - (* W_ConsB_NonRec *)
    intros Gamma b bs Hwf_b IH_b Hwf_bs IH_bs.
    unfold P_bwfnr.
    intros env env' bs' Hrename.
    inversion Hrename. subst.
    apply W_ConsB_NonRec.
    + eapply IH_b.
      apply X.
    + apply skip.
  - (* W_NilB_Rec *)
    intros Gamma.
    unfold P_bwfr.
    intros env env' bs' Hrename.
    inversion Hrename. subst.
    apply W_NilB_Rec.
  - (* W_ConsB_Rec*)
    intros Gamma b bs Hwf_b IH_b Hwf_bs IH_bs.
    unfold P_bwfr.
    intros env env' bs' Hrename.
    inversion Hrename. subst.
    apply W_ConsB_Rec.
    + eapply IH_b.
      apply X.
    + apply skip.
           
  - (* W_Term *)
    intros Gamma s x T tb Hkind_T Htyp_tb IH_tb.
    unfold P_bwf.
    intros env env' b' Hrename.
    inversion Hrename. subst.
    rename t' into tb'.
    apply W_Term.
    + apply skip.
    + apply skip.
  - (* W_Type *)
    intros Gamma X K T Hkind_T.
    unfold P_bwf.
    intros env env' b' Hrename.
    inversion Hrename. subst.
    apply W_Type.
    apply skip.
  - (* W_Data *)
    intros Gamma X YKs cs matchf Gamma' HGamma' Hwf_cs IH_cs.
    unfold P_bwf.
    intros env env' b' Hrename.
    inversion Hrename. subst.
    inversion H2. subst.
    eapply W_Data.
    + reflexivity.
    + intros c Hin.
      apply skip.
Qed. 
