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

Compute (
  lookupT 
  (RenameContext (("a", RenamedTo "b") :: ("a" , RenamedTo "c") :: nil) ("a" |T-> Ty_Var "B"; "a" |T-> Ty_Var "C"; emptyContext))
  "c"
).

Definition non_capturing_environment (t : Term) (env : environment) : Prop :=
  forall x rr, 
    List.In x (free_vars eqb t) ->
    lookupRR env x = Datatypes.Some rr /\ lookupV env rr = Datatypes.Some x.

Lemma e : forall env t y r,
    non_capturing_environment t ((y, r) :: env) ->
    non_capturing_environment t env.
Proof.
  intros.
  unfold non_capturing_environment.
  intros.
  unfold non_capturing_environment in H.
  apply H with x rr in H0.
  destruct H0.
  inversion H0.
  inversion H1.
  destruct (x =? y) eqn:Hxy; destruct (rename_result_eqb eqb rr r) eqn:Hrrr.
  - inversion H3. subst.
    inversion H4. subst.
Abort.

(* Predicate for the [has_type] datatype *)
Definition P_ht Gamma t1 T := 
  forall env t2, 
    (forall x y T', 
      lookupRR env x = Datatypes.Some (RenamedTo y) ->
      lookupT Gamma x = Datatypes.Some T' -> 
      lookupT (RenameContext env Gamma) y = Datatypes.Some T'
    ) ->
    Rename env t1 t2 -> 
    (RenameContext env Gamma) |-+ t2 : T.

(* Predicate for the [constructor_well_formed] datatype *)
Definition P_cwf Gamma c := Gamma |-ok_c c.

(* Predicate for the [bindings_well_formed_nonrec] datatype *)
Definition P_bwfnr Gamma bs1 :=
    forall env env' bs2,
      Gamma |-oks_nr bs1 ->
      RenameBindingsNonRec env env' bs1 bs2 ->
      Gamma |-oks_nr bs2.

(* Predicate for the [bindings_well_formed_rec] datatype *)
Definition P_bwfr Gamma bs1 :=
  forall env env' bs2,
    Gamma |-oks_nr bs1 ->
    RenameBindingsRec env env' bs1 bs2 ->
    Gamma |-oks_nr bs2.

(* Predicate for the [binding_well_formed] datatype *)
Definition P_bwf Gamma b1 := 
  forall env env' b2,
      Gamma |-ok b1 ->
      RenameBinding env env' b1 b2 ->
      Gamma |-ok b2.

Axiom skip : forall P, P.


Lemma e0e0 : forall env x w T Gamma t T0,
    ~(List.In x (free_vars eqb t)) ->
    (RenameContext ((x, RenamedTo w) :: env) (x |T-> T0; Gamma)) |-+ t : T ->
    (w |T-> T0; RenameContext env Gamma) |-+ t : T.
Proof.
  induction env.
  - intros.
    simpl in H0.
    rewrite update_eq in H0.
    destruct (w =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      rewrite deleteT_eq in H0.
      simpl.
      apply skip.
    + apply eqb_neq in Heqb as Hneq.
      apply skip.
  - intros.
Admitted.

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
    intros Gamma bs t T Gamma' Heq Htyp_bs IH_bs Htyp_t IH_t.
    unfold P_ht.
    intros env t2 X.
    subst.

    apply skip.
  - (* T_LetRec *)
    apply skip.

  - (* T_Var *)
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
      apply skip.
      apply skip.

  - (* T_TyAbs *)
    apply skip.
  - (* T_LamAbs *)
    intros Gamma x T1 t0 T2 Htyp_t0 IH_t0 Hkind_T1. 
    unfold P_ht. 
    intros env t2 Hnce X.

    inversion X.
    + (* RenameLamAbsRename *) 
      subst.
      rename t' into t0'.
      apply T_LamAbs.
      * unfold P_ht in IH_t0.
        eapply IH_t0 in X0; eauto.
        apply skip. apply skip.
      * apply skip.
    + apply skip.
         
  - (* T_Apply *)
    apply skip.
  - (* T_Constant *)
    apply skip.
  - (* T_Builtin *)
    apply skip.
  - (* T_TyInst *)
    apply skip.
  - (* T_Error *)
    apply skip.
  - (* T_IWrap *)
    apply skip.
  - (* T_Unwrap *)
    apply skip.

  - (* W_Con *)
    apply skip.

  - (* W_NilB_NonRec *)
    apply skip.
  - (* W_ConsB_NonRec *)
    apply skip.
  - (* W_NilB_Rec *)
    apply skip.
  - (* W_ConsB_Rec*)
    apply skip.
           
  - (* W_Term *)
    apply skip.
  - (* W_Type *)
    apply skip.
  - (* W_Data *)
    apply skip.
Qed. 
