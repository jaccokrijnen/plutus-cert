Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Rules.

Import Coq.Strings.String.
Local Open Scope string_scope.
      
Lemma weakening__has_kind : forall Delta Delta' T K,
    inclusion Delta Delta' ->
    Delta |-* T : K ->
    Delta' |-* T : K.
Proof.
  intros Delta Delta' T K H HT.
  generalize dependent Delta'.
  induction HT; intros; eauto using inclusion_update with typing.
Qed.

Lemma weakening_empty__has_kind : forall Delta T K,
    empty |-* T : K ->
    Delta |-* T : K.
Proof.
  intros.
  eapply weakening__has_kind; eauto using inclusion_empty.
Qed.


Definition P_has_type Delta Gamma t T : Prop :=
  forall Delta' Gamma',
    inclusion Delta Delta' ->
    inclusion Gamma Gamma' ->
    Delta' ,, Gamma' |-+ t : T.

Definition P_constructor_well_formed Delta c : Prop :=
  forall Delta',
    inclusion Delta Delta' ->
    Delta' |-ok_c c.

Definition P_bindings_well_formed_nonrec Delta Gamma bs : Prop :=
  forall Delta' Gamma',
    inclusion Delta Delta' ->
    inclusion Gamma Gamma' ->
    Delta' ,, Gamma' |-oks_nr bs.

Definition P_bindings_well_formed_rec Delta Gamma bs : Prop :=
  forall Delta' Gamma',
    inclusion Delta Delta' ->
    inclusion Gamma Gamma' ->
    Delta' ,, Gamma' |-oks_r bs.

Definition P_binding_well_formed Delta Gamma b : Prop :=
  forall Delta' Gamma',
    inclusion Delta Delta' ->
    inclusion Gamma Gamma' ->
    Delta' ,, Gamma' |-ok b.

#[export] Hint Unfold
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed 
  : core.

Lemma weakening : 
  (forall Delta Gamma t T, Delta ,, Gamma |-+ t : T -> P_has_type Delta Gamma t T) /\
  (forall Delta Gamma bs, Delta ,, Gamma |-oks_nr bs -> P_bindings_well_formed_nonrec Delta Gamma bs) /\
  (forall Delta Gamma bs, Delta ,, Gamma |-oks_r bs -> P_bindings_well_formed_rec Delta Gamma bs) /\
  (forall Delta Gamma b, Delta ,, Gamma |-ok b -> P_binding_well_formed Delta Gamma b).
Proof with eauto using weakening__has_kind, inclusion_update with typing.
  apply has_type__multind with 
    (P := P_has_type) 
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).
  all: intros; autounfold; intros...
  - (* T_Let *)
    subst.
    eapply T_Let...
    + apply H5.
      * apply inclusion_mupdate.
        assumption.
      * apply inclusion_mupdate.
        assumption.
  - (* T_LetRec *)
    subst.
    eapply T_LetRec...
    + apply H3.
      * apply inclusion_mupdate.
        assumption.
      * apply inclusion_mupdate.
        assumption.
    + apply H5.
      * apply inclusion_mupdate.
        assumption.
      * apply inclusion_mupdate.
        assumption.
  - (* T_ExtBuiltin *)
    eapply T_ExtBuiltin; eauto.
    intros.
    eapply H2; eauto.
  - (* W_ConsB_NonRec *)
    eapply W_ConsB_NonRec...
    + apply H3.
      apply inclusion_mupdate.
      assumption.
      apply inclusion_mupdate.
      assumption.
  - (* W_Data *)
    eapply W_Data.
    + reflexivity.
    + reflexivity.
    + intros.
      apply H2.
      * assumption.
      * subst.
        apply inclusion_mupdate.
        assumption.
Qed.

Lemma weakening_empty : forall Delta Gamma t T,
    empty ,, empty |-+ t : T ->
    Delta ,, Gamma |-+ t : T.
Proof.
  intros Delta Gamma t T Ht.
  apply weakening in Ht.
  unfold P_has_type in Ht.
  apply Ht.
  - apply inclusion_empty.
  - apply inclusion_empty.
Qed.