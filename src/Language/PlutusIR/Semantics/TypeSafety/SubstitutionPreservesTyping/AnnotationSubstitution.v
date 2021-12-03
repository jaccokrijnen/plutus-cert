Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.TypeSubstitution.

Require Import PlutusCert.Util.Map.Mupdate.

Require Import Coq.Logic.FunctionalExtensionality.

Definition gsubst (a : tyname) (T' : Ty ) (Gamma : partial_map Ty) :=
  fun x =>
    match Gamma x with
    | None => None
    | Datatypes.Some T => Datatypes.Some (substituteT a T' T)
    end.

Lemma gsubst_empty : forall X U,
    gsubst X U empty = empty.
Proof.
  intros X U.
  unfold gsubst.
  simpl.
  reflexivity.
Qed.

Lemma gsubst__substituteT : forall Gamma x X U T,
    Gamma x = Datatypes.Some T ->
    (gsubst X U Gamma) x = Datatypes.Some (substituteT X U T).
Proof.
  intros.
  unfold gsubst.
  rewrite H.
  reflexivity.
Qed.

Lemma gsubst_absorbs_substituteT : forall x X U T Gamma,
    (x |-> (substituteT X U T); gsubst X U Gamma) = gsubst X U (x |-> T; Gamma).
Proof.
  intros.
  simpl.
  f_equal.
  apply functional_extensionality.
  intros.
  destruct (x =? x0)%string eqn:Heqb.
  - (* x = x0 *)
    apply eqb_eq in Heqb as Heq.
    subst.
    unfold gsubst.
    rewrite update_eq.
    rewrite update_eq.
    reflexivity.
  - (* x <> x0 *)
    apply eqb_neq in Heqb as Hneq.
    unfold gsubst.
    rewrite update_neq; auto.
    rewrite update_neq; auto.
Qed.

(** ** Predicates *)
Definition P_Term (t : Term) :=
  forall Delta Gamma X K U T Tn,
    (X |-> K; Delta) ,, Gamma |-+ t : T ->
    empty |-* U : K ->
    normalise (substituteT X U T) Tn ->
    Delta ,, (gsubst X U Gamma) |-+ <{ [[U / X] t }> : Tn.
    
Definition P_Binding (b : Binding) : Prop :=
  forall Delta Gamma X K U,
    (X |-> K; Delta) ,, Gamma |-ok_b b ->
    empty |-* U : K ->
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