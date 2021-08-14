Require Import PlutusCert.Language.PlutusIR.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.DeBruijn.
Import DeBruijnTerm.
Require Import PlutusCert.Language.PlutusIR.Conversion.
Import ConvertFunc.

Definition P ctx t1 T := 
  forall t2 t1' t2', 
    CNR_Term t1' t2' -> 
    to t1' = Coq.Init.Datatypes.Some t1 -> 
    to t2' = Coq.Init.Datatypes.Some t2 -> 
    ctx |-+ t2 : T.

Theorem CNR_Term__preserves_typing : forall ctx t1 T,
    ctx |-+ t1 : T ->
    P ctx t1 T.
Proof.
  eapply has_type_rec.
  - intros. 
    unfold P. unfold to. intros.
    destruct t1'; autorewrite with term_to' in H1.
    + destruct r.
      * simpl in H1. autorewrite with term_to' in H1.
        destruct (bindings_to' [] l).
        -- rewrite app_nil_r in H1.
           destruct (term_to' (vars_bound_by_bindings l) t1').
           ++ inversion H1. subst.
              inversion X. subst.
              ** autorewrite with term_to' in H2. simpl in H2.
Abort.

