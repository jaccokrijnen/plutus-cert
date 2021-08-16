Require Import PlutusCert.Language.PlutusIR.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require PlutusCert.Language.PlutusIR.Semantics.Static.
Require PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.DeBruijn.
Require PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.

Require Import PlutusCert.Language.PlutusIR.Conversion.

Module DB.

Import PlutusCert.Language.PlutusIR.Semantics.Static.
Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.DeBruijn.
Import DeBruijnTerm.
Import ConvertInductive.

Definition P ctx t1 T := 
  forall t2 t1' t2' vars, 
    CNR_Term t1' t2' -> 
    ConvertTerm vars t1' t1 ->
    ConvertTerm vars t2' t2 ->
    ctx |-+ t2 : T.

Definition Q ctx c := ctx |-ok_c c.

Definition R ctx b1 := 
  forall b2 b1' b2' vars,
    Congruence.Cong_Binding CNR_Term b1' b2' ->
    ConvertBinding vars b1' b1 ->
    ConvertBinding vars b2' b2 ->
    ctx |-ok b2.

Axiom skip : forall P, P.

Theorem CNR_Term__preserves_typing : forall ctx t1 T,
    ctx |-+ t1 : T ->
    P ctx t1 T.
Proof.
  apply has_type_rec with (P := P) (P0 := Q) (P1 := R).
  - intros.  
    unfold P.
    intros.
    inversion H4. subst.
    inversion X; subst.
    + apply skip.
    + inversion X0. subst. apply skip.
  - intros.
    unfold P.
    intros.
    inversion H5. subst.
    rename bs0 into bs1'. rename t0 into t1'. rename bs into bs1. rename t into t1.
    inversion X. subst.
    inversion X0. subst.
    rename bs' into bs2'. rename t' into t2'.
    inversion H6. subst.
    rename bs' into bs2. rename t0' into t2.
    eapply T_LetRec.
    + auto.
    + reflexivity.
    + intros.
      unfold R in H2.
Abort.

End DB.



Module Named.

Import PlutusCert.Language.PlutusIR.Semantics.Static.
Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Import NamedTerm.

Definition P_term ctx t1 T := 
  forall t2, 
    CNR_Term t1 t2 -> 
    ctx |-+ t2 : T.

Definition P_constructor ctx c := ctx |-ok_c c.

Definition P_bindings ctx bs1 :=
    forall bs2,
      (ctx |-oks bs1 ->
      Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
      ctx |-oks bs2) /\
      (Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
      map binds bs1 = map binds bs2).

Definition P_binding ctx b1 := 
  forall b2,
    Congruence.Cong_Binding CNR_Term b1 b2 ->
    ctx |-ok b2.

Axiom skip : forall P, P.

Theorem CNR_Term__preserves_typing : forall ctx t1 T,
    ctx |-+ t1 : T ->
    P_term ctx t1 T.
Proof.
  apply has_type_rec with (P := P_term) (P0 := P_constructor) (P1 := P_bindings) (P2 := P_binding).
  - intros.  
    unfold P_term.
    intros.
    inversion X; subst.
    + apply skip.
    + inversion X0. subst. 
      apply T_Let.
      * assumption.
      * apply H1. assumption. assumption.
      * unfold P_bindings in H1. edestruct H1 as [_ Heq]. apply Heq in X1. rewrite <- X1. apply H3. assumption. 
  - intros.
    unfold P_term.
    intros.
    inversion X. subst.
    inversion X0. subst.
    eapply T_LetRec.
    + auto.
    + reflexivity.
    + unfold P_bindings in H2.
      edestruct H2 as [IHH Heq].
      apply Heq in X1 as Hsu.
      rewrite <- Hsu.
      apply IHH. auto. auto.
    + unfold P_bindings in H2.
      edestruct H2 as [_ Heq].
      apply Heq in X1 as Hsu.
      rewrite <- Hsu.
      apply H4.
      assumption.
  - 
Abort.