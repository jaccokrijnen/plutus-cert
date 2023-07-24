Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.TypeSubstitution.

Require Import PlutusCert.Util.List.

Require Import Lists.List.
Import ListNotations.

Require Import Coq.Logic.FunctionalExtensionality.

Definition gsubst (a : tyname) (T' : Ty ) (Gamma : list (string * Ty)) :=
  map (fun '(x, T) => (x, substituteT a T' T)) Gamma.

Lemma gsubst_empty : forall X U,
    gsubst X U [] = [].
Proof.
  intros X U.
  unfold gsubst.
  simpl.
  reflexivity.
Qed.

Lemma gsubst__substituteT Gamma x X U T :
    lookup x Gamma = Datatypes.Some T ->
    lookup x (gsubst X U Gamma) = Datatypes.Some (substituteT X U T).
Proof with auto.
  induction Gamma.
  all: intros H; unfold gsubst.
  - inversion H.
  - destruct a.
    destruct (string_dec x s).
    + subst s.
      simpl.
      rewrite eqb_refl.
      rewrite lookup_eq in H.
      congruence.
    + rewrite lookup_neq in H...
      apply eqb_neq in n.
      rewrite eqb_sym in n.
      simpl.
      rewrite n...
Qed.

Lemma gsubst_absorbs_substituteT : forall x X U T Gamma,
    ((x, (substituteT X U T)) :: gsubst X U Gamma) = gsubst X U ((x, T) :: Gamma).
Proof.
  reflexivity.
Qed.

(** ** Predicates *)
Definition P_Term (t : Term) :=
  forall Delta Gamma X K U T Tn,
    ((X, K) :: Delta) ,, Gamma |-+ t : T ->
    [] |-* U : K ->
    normalise (substituteT X U T) Tn ->
    Delta ,, (gsubst X U Gamma) |-+ <{ [[U / X] t }> : Tn.
    
Definition P_Binding (b : Binding) : Prop :=
  forall Delta Gamma X K U,
    ((X, K) :: Delta) ,, Gamma |-ok_b b ->
    [] |-* U : K ->
    Delta ,, (gsubst X U Gamma) |-ok_b <{ [[U / X][b] b }>.

#[export] Hint Unfold
  P_Term
  P_Binding
  : core.

Theorem substituteA_preserves_typing : 
  forall t, P_Term t.
Proof with (eauto using substituteT_preserves_kinding with typing). 
  apply Term__ind with P_Binding.
  all: intros.
  all: unfold P_Term.
  all: try (intros Delta Gamma X K U T Tn Htyp__t Hkind__U Hnorm__Tn).
  all: unfold P_Binding.
  all: try (intros Delta Gamma X K U Htyp__b Hkind__U).
  all: try (inversion Htyp__t; subst).
(* ADMIT: I had no time to finish this. Should follow from uniqueness property, amongst others. *)
Admitted.
