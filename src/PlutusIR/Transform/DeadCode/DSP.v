Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

Require Import PlutusCert.PlutusIR.Transform.DeadCode2.
Require Import PlutusCert.PlutusIR.Transform.DeadCode.SSP.
Require Import PlutusCert.PlutusIR.Transform.DeadCode.DSP.Lemmas.
Require Import PlutusCert.PlutusIR.Transform.DeadCode.DSP.TermBind.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Misc.Axiom.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Import PlutusCert.PlutusIR.Analysis.UniqueBinders.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.

Import UniqueBinders.Term.

Import PlutusNotations.




(** ** Predicates *)

Definition P_has_type Δ Γ t T : Prop :=
  forall
    t'
    (H_dc : dc t t'),
    Δ ,, Γ |- t ≤ t' : T.

Definition P_constructor_well_formed Δ c Tr : Prop := Δ |-ok_c c : Tr.

Definition P_bindings_well_formed_nonrec Δ Γ bs : Prop :=

  (* dc_compat case *)
  (
    forall bs',
      Compat.Compat_Bindings dc bs bs' ->
      forall Δ_t Γ_t bsGn t t' Tn,
        Δ_t = flatten (List.map binds_Delta bs) ++ Δ  ->
        map_normalise (flatten (List.map binds_Gamma bs)) bsGn ->
        Γ_t = bsGn ++ Γ ->
        Δ |-* Tn : Kind_Base ->
        Δ_t ,, Γ_t |- t ≤ t' : Tn ->
        Δ   ,, Γ   |- (Let NonRec bs t) ≤ (Let NonRec bs' t') : Tn
  ) /\
  (
      forall Δ' Γ' b bs' bsGn t Tn,
        bs = b :: bs' ->
        map_normalise (rev (binds_Gamma b)) bsGn ->
        Γ' = bsGn ++ Γ ->
        Δ' = (rev (binds_Delta b)) ++ Δ ->
        Δ |-* Tn : Kind_Base ->
        P_has_type Δ' Γ' (Let NonRec bs' t) Tn
  ).

Definition P_bindings_well_formed_rec Δ Γ bs1 : Prop := Δ ,, Γ |-oks_r bs1.

Definition P_binding_well_formed Δ Γ b : Prop :=
  (
    forall
      b'
      (H_compat : Compat.Compat_Binding dc b b'),
      forall Δ_t Γ_t bsGn t t' Tn bs bs',
        Δ_t = binds_Delta b ++ Δ ->
        map_normalise (binds_Gamma b) bsGn ->
        Γ_t = bsGn ++ Γ ->
        Δ |-* Tn : Kind_Base ->
        Δ_t ,, Γ_t |- (Let NonRec bs t) ≤ (Let NonRec bs' t') : Tn ->
        Δ   ,, Γ   |- (Let NonRec (b :: bs) t) ≤ (Let NonRec (b' :: bs') t') : Tn
  ).

#[export] Hint Unfold
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed : core.

(** ** The main theorem *)

Theorem dc__DSP : forall Δ Γ e T,
    Δ ,, Γ |-+ e : T ->
    P_has_type Δ Γ e T.
Proof with (eauto_LR || eauto with DSP_compatibility_lemmas).
  apply has_type__ind with
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).
  all : intros; autounfold; intros; subst.


  (* P_has_type, compatibility cases *)
  all: try (
    inversion H_dc;
    match goal with
      | H : Compat.Compat dc _ _ |- _ =>
          inversion H;
          eauto with DSP_compatibility_lemmas typing
    end
    ).

  (* P_constructor_well_formed *)
  all: try eauto with typing.

  (* P_binding_well_formed *)
  all: try (
    match goal with
      | H : Compat.Compat_Binding dc _ _ |- _ =>
          inversion H;
          eauto with DSP_compatibility_lemmas typing
    end
    ).

  (* P_has_type, T_Let *)
  - inversion H_dc; subst.

    (* dc_compat *)
    + inversion H_compat; subst.
      destruct H3 as [H_bs _].
      subst...

    (* dc_delete_binding *)
    +
      destruct H3 as [_ H_bbs].

      assert (bsGn_b : list (string * Ty)). admit.
      assert (H_norm_b : map_normalise (rev (binds_Gamma b)) bsGn_b). admit.
      remember (rev (binds_Delta b) ++ Δ) as Δ'.
      remember (bsGn_b ++ Γ) as Γ'.

      (* Construct the right Induction Hypothesis *)
      assert (H : P_has_type Δ' Γ'  (Let NonRec bs0 t) Tn). {
        eauto.
      }

      (* Use IH *)
      assert (H_approx_bs : Δ',, Γ' |- (Let NonRec (bs0) t) ≤ t' : Tn). {
        debug eauto.
      }

      assert (H_unique : unique (Let NonRec (b :: bs0) t)).
        admit. (* Precondition of translation relation, add to P_... *)

      destruct b as [ [] [x Tb] tb | | ].

      (* TermBind NonStrict *)
      * admit. (* Add non-strict semantics *)

      (* TermBind Strict *)
      *
        (* Set up all premises for elim_TermBind__approximate *)

        simpl in H_norm_b.
        inversion H_norm_b; subst.
        rename Tn0 into Tbn.
        inversion H9; subst.

        remember (TermBind Strict (VarDecl x Tb) tb) as b.

        assert (pure_binding Δ Γ b). {
          subst b.
          simpl.
          assert (pure_open Δ Γ tb Tbn). {
          inversion H_pure.
          eauto using is_pure_nil_pure_open.
          }
          eauto.
        }

        assert (Δ ,, Γ |-ok_b b ). {
          inversion H2.
          auto.
        }

        assert (H_ty_tb : Δ ,, Γ |-+ tb : Tbn). {
          clear - H2 H10 Heqb.
          inversion H2; subst.
          inversion H1; subst.
          assert (Tn = Tbn) by eauto using normalisation__deterministic.
          subst.
          assumption.
        }

        assert (H_Tb_wf : Δ |-* Tb : Kind_Base). {
          clear - H2 H10 Heqb.
          inversion H2; subst.
          inversion H1; subst.
          assumption.
        }

        assert (H_Γ_b_normal : exists Γn_b, map_normalise (binds_Gamma b) Γn_b). {
          admit. (* By H0 *)
        }
        destruct H_Γ_b_normal.

        simpl in H_approx_bs.

        subst b.

        (* Use elim_TermBind lemma *)
        eauto using elim_TermBind_NonRec__approximate.

      (* TypeBind *)
      * admit. (* Lemma similar to compat_TermBind *)

      (* DatatypeBind *)
      * admit. (* Add Datatype semantics, lemma similar to compat_TermBind *)


    (* dc_keep_binding *)
    + admit.

    (* dc_delete_let_nil *)
    + admit.

    (* dc_compat_let_nil_nil *)
    + admit.

  (* W_NilB_NonRec *)
  - split.
    + intros.
      inversion X;subst.
      eauto with DSP_compatibility_lemmas.
    + intros.
      inversion H.

  (* W_ConsB_NonRec *)
  - split.
    + intros.
      inversion X. subst.
      admit.
    + intros. subst.
    (* TODO, change P_bindings_well_formed_nonrec ? *)

Admitted.
