Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.


Fixpoint map_msubstT_rho_syn1 (rho : tymapping) (xts : tass) : tass :=
  match xts with
  | nil => nil
  | (x,T) :: xts' => (x, msubstT_rho_syn1 rho T) :: map_msubstT_rho_syn1 rho xts'
  end.

Fixpoint map_msubstT_rho_syn2 (rho : tymapping) (xts : tass) : tass :=
  match xts with
  | nil => nil
  | (x,T) :: xts' => (x, msubstT_rho_syn2 rho T) :: map_msubstT_rho_syn2 rho xts'
  end.

Definition substituteT_context (a : tyname) (S : Ty) (Gamma : partial_map Ty) :=
   fun x => 
    match Gamma x with
    | None => None
    | Datatypes.Some T => 
        Datatypes.Some (substituteT a S T)
    end.



(** ** Lemma C.6 *)

(** *** Predicates *)

Definition P_Term (e : Term) :=
  forall a Gamma Delta T2 T1 K e_s,
    (Gamma, a |-> K ; Delta) |-+ e : T2 ->
    (Gamma, Delta) |-* T1 : K ->
    annotsubst a T1 e e_s ->
    (substituteT_context a T1 Gamma, Delta) |-+ e_s : (substituteT a T1 T2).

Definition P_Binding (b : Binding) : Prop :=
  forall ctx x U v b',
    extendT x U ctx |-ok b ->
    emptyContext |-+ v : U ->
    substitute_binding x v b b' ->
    ctx |-ok b' /\ binds b = binds b'.
#[export] Hint Unfold P_Binding : core.

Definition P_Bindings_NonRec (bs : list Binding) : Prop :=
  forall ctx x U v bs',
    extendT x U ctx |-oks_nr bs ->
    emptyContext |-+ v : U ->
    Util.ForallP P_Binding bs ->
    substitute_bindings_nonrec x v bs bs' ->
    ctx |-oks_nr bs' /\ List.map binds bs = List.map binds bs'.

Definition P_Bindings_Rec (bs : list Binding) : Prop :=
  forall ctx x U v bs',
    extendT x U ctx |-oks_r bs ->
    emptyContext |-+ v : U ->
    Util.ForallP P_Binding bs ->
    substitute_bindings_rec x v bs bs' ->
    ctx |-oks_r bs' /\ List.map binds bs = List.map binds bs'.

Lemma P_Bindings_NonRec__holds_definitionally : forall bs, P_Bindings_NonRec bs.
Proof.
Abort.

Lemma P_Bindings_Rec__holds_definitionally : forall bs, P_Bindings_Rec bs.
Proof.
Abort.

Axiom skip : forall P, P.

Lemma type_substitution : forall e,
    P_Term e.
Proof.
  apply Term__ind with P_Binding.
  - apply skip.
  - apply skip.
  - (* T_TyAbs *)
    intros bX K t IH__t.
    unfold P_Term.
    intros a Gamma Delta T2 T1 K0 e_s Htyp Hkind__T1 Has__e_s.
    inversion Htyp. subst.
    inversion Has__e_s.
    + subst.
      simpl.
      rewrite eqb_refl.
      apply T_TyAbs.
      unfold P_Term in IH__t.
      apply annotsubst_preserves_typing.
      eapply IH__t.
      unfold extendK in H4. fold extendK in H4.
      eapply IH__t.
      simpl.


 Admitted.
