Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.

Import Coq.Strings.String.
Local Open Scope string_scope.

Definition inclusion (ctx1 ctx2 : Context) : Prop :=
  (forall x T, lookupT ctx1 x = Coq.Init.Datatypes.Some T -> lookupT ctx2 x = Coq.Init.Datatypes.Some T) /\
  (forall X K, lookupK ctx1 X = Coq.Init.Datatypes.Some K -> lookupK ctx2 X = Coq.Init.Datatypes.Some K).

Lemma inclusion_empty : forall ctx2,
    inclusion empty ctx2.
Proof.
  intros.
  unfold inclusion.
  simpl.
  split; intros; inversion H.
Qed.

Lemma inclusion_extendT : forall (ctx1 ctx2 : Context) (y : binderName) (T : Ty),
    inclusion ctx1 ctx2 ->
    inclusion (extendT y T ctx1) (extendT y T ctx2).
Proof.
  unfold inclusion.
  intros.
  split.
  - intros.
    unfold lookupT.
    simpl.
    unfold lookupT in H0.
    simpl in H0.
    destruct (x =? y) eqn:Hxy.
    + assumption.
    + fold lookupK.
      fold lookupK in H0.
      apply H.
      assumption.
  - intros. 
    simpl.
    apply H.
    assumption.
Qed.

Lemma inclusion_extendK : forall (ctx1 ctx2 : Context) (y : binderTyname) (K : Kind),
    inclusion ctx1 ctx2 ->
    inclusion (extendK y K ctx1) (extendK y K ctx2).
Proof.
  unfold inclusion.
  intros.
  split.
  - intros.
    simpl.
    apply H.
    assumption.
  - intros.
    unfold lookupK.
    simpl.
    unfold lookupK in H0.
    simpl in H0.
    destruct (X =? y) eqn:Hxy.
    + assumption.
    + fold lookupK.
      fold lookupK in H0.
      apply H.
      assumption.
Qed.

Lemma inclusion_append : forall (ctx1 ctx2 ctx' : Context),
    inclusion ctx1 ctx2 ->
    inclusion (Named.append ctx' ctx1) (Named.append ctx' ctx2).
Proof.
  intros.
  induction ctx'.
  - simpl.
    assumption.
  - unfold Named.append.
    simpl.
    split.
    + destruct a; destruct p.
      * intros x T. 
        unfold lookupT.
        fold lookupT.
        destruct (x =? s) eqn:Hxy.
        -- auto.
        -- intros.
           apply IHctx'.
           assumption.
      * intros x T.
        apply IHctx'.
    + destruct a; destruct p.
      * intros xT.
        apply IHctx'.
      * intros x T.
        unfold lookupK.
        fold lookupK.
        destruct (x =? s) eqn:Hxy.
        -- auto.
        -- intros.
           apply IHctx'.
           assumption.
Qed.
      
Lemma weakening__has_kind : forall ctx ctx' T K,
    inclusion ctx ctx' ->
    ctx |-* T : K ->
    ctx' |-* T : K.
Proof.
  intros ctx ctx' T K H HT.
  generalize dependent ctx'.
  induction HT; intros; eauto using inclusion_extendK with typing.
  - apply K_Var.
    apply H0.
    apply H.
Qed.


Definition P_has_type ctx t T : Prop :=
  forall ctx',
    inclusion ctx ctx' ->
    ctx' |-+ t : T.

Definition P_constructor_well_formed ctx c : Prop :=
  forall ctx',
    inclusion ctx ctx' ->
    ctx' |-ok_c c.

Definition P_bindings_well_formed_nonrec ctx bs : Prop :=
  forall ctx',
    inclusion ctx ctx' ->
    ctx' |-oks_nr bs.

Definition P_bindings_well_formed_rec ctx bs : Prop :=
  forall ctx',
    inclusion ctx ctx' ->
    ctx' |-oks_r bs.

Definition P_binding_well_formed ctx b : Prop :=
  forall ctx',
    inclusion ctx ctx' ->
    ctx' |-ok b.

Lemma weakening : 
  (forall ctx t T, ctx |-+ t : T -> P_has_type ctx t T) /\
  (forall ctx bs, ctx |-oks_nr bs -> P_bindings_well_formed_nonrec ctx bs) /\
  (forall ctx bs, ctx |-oks_r bs -> P_bindings_well_formed_rec ctx bs) /\
  (forall ctx b, ctx |-ok b -> P_binding_well_formed ctx b).
Proof.
  apply has_type__multind with 
    (P := P_has_type) 
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).
  - (* T_Let *)
    intros. unfold P_has_type. intros.
    eapply T_Let.
    + reflexivity.
    + apply H1.
      assumption.
    + apply H3.
      subst.
      apply inclusion_append.
      assumption.
  - (* T_LetRec *)
    intros. unfold P_has_type. intros.
    eapply T_LetRec.
    + reflexivity.
    + apply H1.
      subst.
      apply inclusion_append.
      assumption.
    + apply H3.
      subst.
      apply inclusion_append.
      assumption.
  - (* T_Var *)
    intros. unfold P_has_type. intros.
    apply T_Var.
    apply H0.
    assumption.
  - (* T_TyAbs *)
    intros. unfold P_has_type. intros.
    apply T_TyAbs.
    apply H0.
    apply inclusion_extendK.
    assumption.
  - (* T_LamAbs *)
    intros. unfold P_has_type. intros.
    apply T_LamAbs.
    + apply H0.
      apply inclusion_extendT.
      assumption.
    + apply weakening__has_kind with ctx.
      * assumption.
      * assumption.
  - (* T_Apply *)
    intros. unfold P_has_type. intros.
    apply T_Apply with T1.
    + apply H0.
      assumption.
    + apply H2.
      assumption.
  - (* T_Constant *)
    intros. unfold P_has_type. intros.
    apply T_Constant.
  - (* T_Builtin *)
    intros. unfold P_has_type. intros.
    apply T_Builtin.
  - (* T_TyInst *)
    intros. unfold P_has_type. intros.
    apply T_TyInst with (T1 := T1) (X := X) (K2 := K2).
    + apply H0.
      assumption.
    + apply weakening__has_kind with ctx.
      * assumption.
      * assumption.
    + assumption.
  - (* T_Error *)
    intros. unfold P_has_type. intros.
    apply T_Error.
    apply weakening__has_kind with ctx.
    + assumption.
    + assumption.
  - (* T_IWrap *)
    intros. unfold P_has_type. intros.
    apply T_IWrap with X K S.
    + assumption.
    + apply H1.
      assumption.
    + apply weakening__has_kind with ctx.
      * assumption.
      * assumption.
    + apply weakening__has_kind with ctx. 
      * assumption.
      * assumption.
  - (* T_Unwrap *)
    intros. unfold P_has_type. intros.
    apply T_Unwrap with F X K T.
    + apply H0.
      assumption.
    + apply weakening__has_kind with ctx.
      * assumption.
      * assumption.
    + assumption.

  - (* W_Con *)
    intros. unfold P_constructor_well_formed. intros.
    apply W_Con.
    intros.
    apply weakening__has_kind with ctx.
    + assumption.
    + apply H.
      assumption.
  
  - (* W_NilB_NonRec *)
    intros. unfold P_bindings_well_formed_nonrec. intros.
    apply W_NilB_NonRec.
  - (* W_ConsB_NonRec *)
    intros. unfold P_bindings_well_formed_nonrec. intros.
    apply W_ConsB_NonRec.
    + apply H0.
      assumption.
    + apply H2.
      apply inclusion_append.
      assumption.
  
  - (* W_NilB_Rec *)  
    intros. unfold P_bindings_well_formed_rec. intros.
    apply W_NilB_Rec.
  - (* W_ConsB_Rec *)
    intros. unfold P_bindings_well_formed_rec. intros.
    apply W_ConsB_Rec.
    + apply H0.
      assumption.
    + apply H2.
      assumption.
  
  - (* W_Term *)
    intros. unfold P_binding_well_formed. intros.
    apply W_Term.
    + apply weakening__has_kind with ctx.
      * assumption.
      * assumption.
    + apply H1.
      assumption.
  - (* W_Type *)
    intros. unfold P_binding_well_formed. intros.
    apply W_Type.
    apply weakening__has_kind with ctx.
    + assumption.
    + assumption.
  - (* W_Data *)
    intros. unfold P_binding_well_formed. intros.
    eapply W_Data.
    + reflexivity.
    + intros.
      apply H1.
      * assumption.
      * subst.
        apply inclusion_append.
        assumption.
Qed.