From Coq Require Import
  List
  Strings.String
.
From PlutusCert Require Import
  Language.PlutusIR
  SemanticEquivalence.LogicalRelation
  Semantics.Static

  Transform.DeadBindings
  Analysis.FreeVars
  Analysis.UniqueBinders

  Substitution
  Dynamic.AnnotationSubstitution
  Dynamic.Bigstep
  Static
  TypeSafety.TypeLanguage.Preservation
  Multisubstitution.Congruence

  Util.Tactics

  SemanticEquivalence.LogicalRelation
  SemanticEquivalence.Auto
  LetNonRec.DSP
.

Import NamedTerm.
Import ListNotations.
Import UniqueBinders.Term.

Lemma eval_let_subst ss r bs t v :
  Let r bs t ==> v ->
  <{ /[ ss /] {Let r bs t} }> ==> t.
Admitted.


Definition disjoint {A} (xs ys : list A) : Prop := 
  Forall (fun v => ~ In v ys) xs.

Lemma compat_dc_delete_nil Δ Γ T t t' :
  Δ |-* T : Kind_Base ->

  LR_logically_approximate Δ Γ           t  t' T ->
  LR_logically_approximate Δ Γ (Let NonRec [] t) t' T.
Proof.
apply compatibility_LetNonRec_Nil__desugar.
Qed.

Lemma compatibility_dc_delete_let Δ Γ t t' T Tn r bs Δ' Γ' bsn :
  Δ |-* T : Kind_Base ->
  normalise T Tn ->
  Δ ,, Γ |-+ (Let r bs t) : Tn ->

  unique (Let r bs t) ->
  disjoint (fv t') (bound_vars_bindings bs) ->
  Forall safe_binding bs ->

  (* Extended environments *)
  Δ' = mupdate Δ (ty_binds_bindings bs) ->
  map_normalise (binds_bindings bs) bsn ->
  Γ' = mupdate Γ bsn ->


  LR_logically_approximate Δ' Γ'   t            t' Tn ->
  LR_logically_approximate Δ  Γ    (Let r bs t) t' Tn.
Proof with auto.
intros Tn_k T_Tn H_Let_Tn.
intros let_uniq bvs_not_in_t' bs_safe.
intros H_Δ' H_bsn H_Γ'.
intros H_approx_t_t'.

unfold LR_logically_approximate.
repeat split.
1,2: admit.


(* Different representations of envronments *)
rename
  Γ into _Γ,
  Γ' into _Γ',
  Δ into _Δ,
  Δ' into _Δ'.

intros k ρ γ γ' Γ Δ H_eq_Δ_ck H_eq_Γ_ck.

intros H_good_ρ H_γ_γ'.
autorewrite with RC.

unfold LR_logically_approximate in H_approx_t_t'.
destruct_hypos.
intros j H_j_k e_f H_Let_eval.

Check forall r bs, <{ (Let r bs t) }> = t.

assert (eval_let_as_substs : forall γ ρ r bs t j e_f,
  <{ [γ / ρ] (Let r bs t) }>
  =[ j ]=> e_f).


Admitted.

Theorem dead_code_Term_DSP : forall Δ Γ,



Definition P_has_type Δ Γ t T : Prop :=
  forall t',
    dead_code t t' ->
    LR_logically_approximate Δ Γ t t' T.

Definition P_constructor_well_formed Delta c Tr : Prop := Delta |-ok_c c : Tr.

Definition P_bindings_well_formed_nonrec Delta Gamma bs : Prop := 
  True.

Definition P_bindings_well_formed_rec Delta Gamma bs1 : Prop := Delta ,, Gamma |-oks_r bs1.

Definition P_binding_well_formed Delta Gamma b : Prop := 
  True.




