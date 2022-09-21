From Coq Require Import
  List
  Strings.String
  Lia
.
From PlutusCert Require Import
  Language.PlutusIR
  SemanticEquivalence.LogicalRelation
  Semantics.Static

  Transform.DeadBindings
  Analysis.FreeVars
  Analysis.UniqueBinders

  Substitution
  AnnotationSubstitution
  Dynamic
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

Lemma compat_nil Δ Γ T t t' :
  Δ |-* T : Kind_Base -> (* May not be necessary, see #7 *)
  LR_logically_approximate Δ Γ           t  t' T ->
  LR_logically_approximate Δ Γ (Let NonRec [] t) t' T.
Proof.
  apply compatibility_LetNonRec_Nil__desugar.
Qed.

(*
Lemma unique_typed_disjoint r bs t t' Δ Γ τ:
  dead_syn t t' ->
  unique (Let r bs t) ->
  Forall (fun '(x, _) => ~ Term.appears_bound_in x t) Γ ->
  Forall (fun '(α, _) => ~ Annotation.appears_bound_in α t) Δ ->
  Δ ,, Γ |-+ t' : τ -> (* TODO: replace with well-scoped *)
  disjoint (fv t') (bound_vars_bindings bs) .
*)

Lemma subst_not_in_fv x t' t : ~ (In x (fv t)) -> <{ [t' / x] t }> = t.
Admitted.

(* Substituting type annotations will not change free term variables*)
Lemma fv_msubstA_fv γ t : fv <{ /[[ γ /] t }> = fv t.
Admitted.

Lemma msubst_not_in_fv x t' γ t : ~ (In x (fv t)) -> <{ /[(x, t') :: γ /] t }> = <{ /[γ/] t }>.
Admitted.

Lemma msubstA_LetNonRec ss bs t : <{ /[[ ss /] {Let NonRec bs t} }>
  = Let NonRec <{ /[[ ss /][bnr] bs }> <{/[[ ss /] t}>.
Admitted.

Lemma msubst_LetNonRec ss bs t : <{ /[ ss /] {Let NonRec bs t} }>
  = Let NonRec <{ /[ ss /][bnr] bs }> <{/[ ss /] t}>.
Admitted.

Lemma msubst_bs_cons ss b bs : <{ /[ ss /][bnr] {b :: bs} }>
  = <{ /[ ss /][b]b }> :: <{ /[ ss /][bnr]bs }>.
Admitted.

Lemma msubstA_bs_cons ss b bs : <{ /[[ ss /][bnr] {b :: bs} }>
  = <{ /[[ ss /][b]b }> :: <{ /[[ ss /][bnr]bs }>.
Admitted.

Lemma msubst_TermBind ss s x t : msubst_binding ss (TermBind s x t)
  = TermBind s x (msubst_term ss t).
Admitted.

Lemma msubstA_TermBind ss s x t : msubstA_binding ss (TermBind s x t)
  = TermBind s x (msubstA_term ss t).
Admitted.

Lemma compose_subst_msubst : forall x tx γ t,
  substitute x tx (msubst_term γ t) = msubst_term ((x, tx) :: γ) t.
Admitted.

Lemma compose_subst_msubst_bindings_nonrec : forall x tx γ bs,
  <{ [ tx / x ][bnr] (/[ γ /][bnr] bs) }> = <{ /[ (x, tx) :: γ /][bnr] bs }>.
Admitted.

Lemma compat_TermBind pm_Δ pm_Γ t t' Tn b bs tb tb' x Tb Tbn :
  pm_Δ |-* Tb : Kind_Base ->
  normalise Tb Tbn ->

  disjoint (bvb b) (fv t') ->
  disjoint (bvbs bs) (fv t') ->
  Forall safe_binding bs ->

  forall pm_Δb pm_Γb,
    b = TermBind Strict (VarDecl x Tb) tb ->
    pm_Δb = pm_Δ ->
    pm_Γb = (x |-> Tbn; pm_Γ) ->
    LR_logically_approximate pm_Δb pm_Γb (Let NonRec bs t) t' Tn ->
    LR_logically_approximate pm_Δ  pm_Γ  tb tb' Tbn -> (* Probably not using this IH *)
    LR_logically_approximate pm_Δ  pm_Γ  (Let NonRec (b :: bs) t) t' Tn.
Proof.
  intros H_Tb_kind H_Tbn.
  intros H_disjoint_b H_disjoint H_safe.
  intros pm_Δb pm_Γb.
  intros H_Eqb H_Δb H_Γb.
  intros H_IH_let_bs H_IH_tb.

  subst b.
  unfold LR_logically_approximate.
  repeat split.

  (* typing*)
  1, 2: admit.

    intros k ρ γ γ' Γ Δ.
    intros H_pm_Δ_Δ H_pm_Γ_Γ.
    intros H_Δ_ρ H_Γ_γ_γ'.

    apply RV_to_RC.
    autorewrite with RC.

    intros j H_lt_j_k e_f.

    intros H_let_terminates.
    simpl in H_let_terminates.

    rewrite msubstA_LetNonRec in H_let_terminates.
    rewrite msubst_LetNonRec in H_let_terminates.
    inversion H_let_terminates. subst bs0 t0 v j0.
    clear H_let_terminates.
    rename H3 into H_b_bs_terminate.
    rewrite msubstA_bs_cons in H_b_bs_terminate.
    rewrite msubst_bs_cons in H_b_bs_terminate.
    rewrite msubstA_TermBind, msubst_TermBind in H_b_bs_terminate.
    inversion H_b_bs_terminate. subst s x0 T t1 bs0 t0 v2.

    (* Error case*)
    2: admit.

    rename H9 into H_bs_terminate.

    simpl in H_bs_terminate.
    destruct
      (* binder x should not occur as let-bound variable in bs *)
      (existsb (eqb x) (bvbs <{ /[ γ /][bnr] (/[[ msyn1 ρ /][bnr] bs) }>)).
      - admit. (* should be impossible by uniqueness *)
      -
        (* combine single substitution with multi-sibstitution *)
        rewrite compose_subst_msubst
              , compose_subst_msubst_bindings_nonrec in H_bs_terminate.
        remember ((x, v1) :: γ) as γₓ.
        remember ((x, v1) :: γ') as γ'ₓ.

        unfold LR_logically_approximate in H_IH_let_bs.
        repeat apply proj2 in H_IH_let_bs.

        assert (H_γₓ_γ'ₓ : RG ρ k ((x, Tbn) :: Γ) γₓ γ'ₓ).
        {
         subst. eapply RG_cons.
              all: try assumption.
              + assert (value v1).
                eauto using eval_to_value__eval.
              unfold RV.
              admit.
              + admit.
        }
        assert ( H_RC_ :
             RC k Tn ρ
               <{ /[ γₓ /] (/[[ msyn1 ρ /] {Let NonRec bs t}) }>
               <{ /[ γ'ₓ /] (/[[ msyn2 ρ /] t') }>).
          { apply H_IH_let_bs with   (ct := (x, Tbn) :: Γ) (ck := Δ).
            - subst. reflexivity.
            - subst. reflexivity.
            - assumption.
              (* RG ρ k ((x, Tbn) :: Γ) γₓ γ'ₓ *)
            - assumption.
          }

        (* push substitutions through*)
        rewrite msubstA_LetNonRec, msubst_LetNonRec in H_RC_.

        apply RC_to_RV with  (j := j2) (e_f := e_f)in H_RC_.
        2: lia.
        2: {
          apply E_Let.
          assumption.
        }

        assert (H_RV_monotone : forall {k k' ρ e1 e2}, k' < k -> RV k Tn ρ e1 e2 -> RV k' Tn ρ e1 e2).
        { admit. }

        assert (H_RC_monotone : forall k k' ρ e1 e2, forall H : (k' < k), RC k Tn ρ e1 e2 -> RC k' Tn ρ e1 e2).
        { admit. }

        destruct H_RC_ as [e'_f [j' [H_t'_terminates RV_e_f_e'_f]]].
        eexists.
        eexists.
        split.

        + simpl in H_disjoint_b. 
          unfold disjoint in H_disjoint_b. 
          apply Forall_inv in H_disjoint_b.
          rewrite Heqγ'ₓ in H_t'_terminates.
          rewrite msubst_not_in_fv in H_t'_terminates.

          apply H_t'_terminates.
          rewrite fv_msubstA_fv.
          assumption.
        + eapply RV_monotone.
          * eassumption.
          * eassumption.
          * lia.
Admitted.



    (*
    γ(ρ(Let (b::bs) t)) ⇓ e_f
    Let (γρb::γρbs) (γρt) ⇓ e_f
    [v/x](Let γρbs γρt) ⇓ e_f
    Let ([v/x]γρbs) ([v/x]γρt) ⇓ e_f
    by IH: [v/x]γt' ⇓ e_f'
    since x ∉ t': γt' ⇓ e_f'


    *)

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




