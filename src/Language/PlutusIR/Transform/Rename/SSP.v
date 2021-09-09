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
      RenameContext env' Gamma
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
    + apply IHenv.
Qed.

Lemma renaming_exhaustive : forall env x w t1 t2,
    lookupRR env x = Datatypes.Some (RenamedTo w) ->
    Rename env t1 t2 ->
    ~(appears_free_in x t2).
Proof. Admitted.


(* Predicate for the [has_type] datatype *)
Definition P_ht Gamma t1 T := 
  forall env t2, 
    (*
    (forall x y T', 
      lookupRR env x = Datatypes.Some (RenamedTo y) ->
      lookupT Gamma x = Datatypes.Some T' -> 
      lookupT (RenameContext env Gamma) y = Datatypes.Some T'
    ) -> *)
    Rename env t1 t2 -> 
    (RenameContext env Gamma) |-+ t2 : T.

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
    (*
    intros Gamma x T Hlookup.
    unfold P_ht. 
    intros env t2 Hnce X.
    
    inversion X.
    + (* RenameVar *)
      subst.
      apply T_Var.
      eapply Hnce; eauto.
    + (* RenameVarEq *)
      subst.
      apply T_Var.
      eapply Hnce.
      apply skip.*)
      apply skip.

  - (* T_TyAbs *)
    apply skip.
  - (* T_LamAbs *)
    (*
    intros Gamma x T1 t0 T2 Htyp_t0 IH_t0 Hkind_T1. 
    unfold P_ht. 
    intros env t2 Hnce X.

    inversion X.
    + (* RenameLamAbsRename *) 
      subst.
      rename t' into t0'.
      apply T_LamAbs.
      * unfold P_ht in IH_t0.
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
    apply skip.        
         
  - (* T_Apply *)
    intros Gamma t1 t2 T1 T2 Htyp_t1 IH_t1 Htyp_t2 IH_t2.
    unfold P_ht.
    intros env t' X.
    
    inversion X. subst.
    apply T_Apply with T1.
    + apply IH_t1.
      assumption.
    + apply IH_t2.
      assumption.
  - (* T_Constant *)
    intros Gamma u a. 
    unfold P_ht. 
    intros env t' X.
    inversion X. subst.
    apply T_Constant.
  - (* T_Builtin *)
    intros Gamma f.
    unfold P_ht.
    intros env t' X.
    inversion X. subst.
    apply T_Builtin.
  - (* T_TyInst *)
    intros Gamma t0 T2 T1 X K2 S Htyp_t0 IH_t0 Hkind_T2 Hbeta.
    unfold P_ht.
    intros env t' Hrename.
    inversion Hrename. subst.
    rename t'0 into t0'.
    apply T_TyInst with T1 X K2.
    + apply IH_t0.
      assumption. 
    + apply skip.
    + reflexivity.
  - (* T_Error *)
    intros Gamma T Hkind_T.
    unfold P_ht.
    intros env t' Hrename.
    inversion Hrename. subst.
    apply T_Error.
    apply skip.
  - (* T_IWrap *)
    intros Gamma F T M K S Hbeta Htyp_M IH_M Hkind_T HKind_F.
    unfold P_ht.
    intros env t' Hrename.
    inversion Hrename. subst.
    rename t'0 into M'.
    eapply T_IWrap.
    + reflexivity.
    + apply IH_M.
      assumption.
    + apply skip.
    + apply skip.
  - (* T_Unwrap *)
    intros Gamma M F K T S Htyp_M IH_M Hkind_T Hbeta.
    unfold P_ht.
    intros env t' Hrename.
    inversion Hrename. subst.
    rename t'0 into M'.
    eapply T_Unwrap.
    + apply IH_M.
      assumption.
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
