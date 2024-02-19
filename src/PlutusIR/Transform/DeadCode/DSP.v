Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

Require Import PlutusCert.PlutusIR.Transform.DeadCode2.
Require Import PlutusCert.PlutusIR.Transform.DeadCode.SSP.
Require Import PlutusCert.PlutusIR.Transform.DeadCode.DSP.TermBind.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Misc.Axiom.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Import PlutusCert.PlutusIR.Analysis.Purity.
Require Import PlutusCert.PlutusIR.Analysis.UniqueBinders.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.

Import UniqueBinders.

Import PlutusNotations.


(** ** The main theorem *)

Definition P_dc t t' :=
    forall Δ Γ T,
    Δ ,, Γ |-+ t : T ->
    LR_logically_approximate Δ Γ t t' T.


(* Add as general lemma in Static.Typing *)
Lemma let_nonrec_inv : forall {Δ Γ b bs t T},
  Δ ,, Γ |-+ (Let NonRec (b :: bs) t) : T ->
  exists Γ_b,
  map_normalise (binds_Gamma b) Γ_b /\
  (((binds_Delta b) ++ Δ) ,, (Γ_b ++ Γ) |-+ (Let NonRec bs t) : T)
.
Admitted.

Notation "'[' γ ; ρ ']' t" := (msubst γ (msubstA ρ t)) (at level 10).
Notation "'[' γ ; ρ ']_bnr' t" := (msubst_bnr γ (msubstA_bnr ρ t)) (at level 10).
Notation "'[' γ ; ρ ']_b' t" := (msubst_b γ (msubstA_b ρ t)) (at level 10).

Lemma elim_nonrec_approx : forall Δ Γ b bs t T t' Γ_b,
  disjoint (bvb b) (fv t') ->
  disjoint (btvb b) (ftv t') ->
  map_normalise (binds_Gamma b) Γ_b ->
  binds_Delta b ++ Δ,, Γ_b ++ Γ |- (Let NonRec       bs  t) ≤ t' : T ->
  Δ                 ,, Γ        |- (Let NonRec (b :: bs) t) ≤ t' : T.
Proof.
  intros.
  unfold LR_logically_approximate.
  repeat split.
  1,2:  admit. (* Typing *)

  setoid_rewrite RV_RC.
  intros.


  (* Push substitutions in *)
  rewrite msubstA_LetNonRec
        , msubst_LetNonRec
        , msubstA_BindingsNonRec_cons
        , msubst_bnr_cons
  in H5.
  inversion H5; subst. clear H5.
  destruct b.

  - destruct v.

    (* Push subistutitions further in *)
    rewrite msubstA_TermBind
          , msubst_TermBind
    in H10.
    inversion H10; subst. clear H10.


    + (* E_Let_TermBind *)
      Set Diffs "on".

      rewrite btvbs_cons in H16.
      unfold btvb in H16.
      rewrite app_nil_l in H16.
      (* Pull substitutions out *)
      rewrite <- msubst_LetNonRec in H16.
      rewrite <- msubstA_LetNonRec in H16.

      (* Simplify disjoint assumptions *)
      simpl in H0, H.
      unfold disjoint in *.
      apply Forall_inv in H.
      clear H0.
      simpl in H2.
      admit.

      
    + (* E_Error_Let_Termbind*)
      admit.

  - (* TypeBind *)
    admit.

  - (* DatatypeBind *)
    admit.
Admitted.

Lemma has_type_NonRec_nil : forall Δ Γ t T,
  Δ,, Γ |-+ (Let NonRec nil t) : T ->
  Δ,, Γ |-+ t : T.
Admitted.


Theorem dc__approx : forall t t',
    dc t t' ->
    P_dc t t'.
Proof.
  apply dc__ind with (P := P_dc).

  - (* dc_compat *)
    admit.
    (* TODO: compatibility lemmas *)

  - (* dc_delete_binding *)
    intros.
    unfold P_dc.
    intros.
    pose proof (let_nonrec_inv H0) as [ Γ_b [H_norm H_ty_bs]].
    unfold P_dc in H.
    apply H in H_ty_bs.
    destruct H_unused as [ H1 H2 ].
    eauto using elim_nonrec_approx.

  - (* dc_keep_binding *)
    intros.
    admit.
    (* TODO: compatibility lemma *)

  - (* dc_delete_nil *)
    intros.
    unfold P_dc in *.
    intros Δ Γ T H_ty.
    apply has_type_NonRec_nil in H_ty.
    eauto using compat_nil.

  - (* dc_compat_let_nil_nil *)
    intros.
    (* TODO: compatibility lemmas *)
    admit.
Admitted.

Definition P_dc_rev t t' :=
    forall Δ Γ T,
    Δ ,, Γ |-+ t : T ->
    LR_logically_approximate Δ Γ t' t T.

Lemma elim_nonrec_approx_rev : forall Δ Γ b bs t T t' Γ_b,
  disjoint (bvb b) (fv t') ->
  disjoint (btvb b) (ftv t') ->
  pure_binding nil b ->
  map_normalise (binds_Gamma b) Γ_b ->
  binds_Delta b ++ Δ,, Γ_b ++ Γ |- t' ≤ (Let NonRec       bs  t)  : T ->
  Δ                 ,, Γ        |- t' ≤ (Let NonRec (b :: bs) t)  : T.
Admitted.

Theorem dc__approx_rev : forall t t',
    dc t t' ->
    P_dc_rev t t'.
Proof.
  apply dc__ind with (P := P_dc_rev).
  - (* dc_compat *)
    admit.
    (* TODO: compatibility lemmas *)
  - (* dc_delete_binding *)
    intros.
    unfold P_dc_rev in *.
    intros Δ Γ T H_ty.
    pose proof (let_nonrec_inv H_ty) as [ Γ_b [H_norm H_ty_bs]].
    admit.
  - admit.
  - admit.
  - admit.
Admitted.


(* TODO: remove this old proof structure, above dc__DSP is simpler
   by doing induction on the translation relation first *)
Require Import PlutusCert.PlutusIR.Transform.DeadCode.DSP.Lemmas.

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
  (* dc_delete_binding case *)
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




Theorem dc__DSP' : forall Δ Γ e T,
    Δ ,, Γ |-+ e : T ->
    P_has_type Δ Γ e T.
Proof with (eauto_LR || eauto with DSP_compatibility_lemmas).
  apply has_type__ind with
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).
  all : intros.


  (* P_has_type, compatibility cases *)
  all: try (
    autounfold; intros; subst;
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
    autounfold; intros; subst;
    match goal with
      | H : Compat.Compat_Binding dc _ _ |- _ =>
          inversion H;
          eauto with DSP_compatibility_lemmas typing
    end
    ).

  (* P_has_type, T_Let NonRec *)
  - unfold P_has_type. intros t' H_dc.
    inversion H_dc; subst.

    (* dc_compat *)
    + inversion H_compat; subst.
      destruct H3 as [H_bs _].
      subst...

    (* dc_delete_binding *)
    +
      destruct H3 as [_ H_bbs].

      assert (bsGn_b : list (string * Ty)).
        admit.
      assert (H_norm_b : map_normalise (rev (binds_Gamma b)) bsGn_b).
        admit.
      remember (rev (binds_Delta b) ++ Δ) as Δ'.
      remember (bsGn_b ++ Γ) as Γ'.

      (* Construct the right Induction Hypothesis *)
      assert (H : P_has_type Δ' Γ'  (Let NonRec bs0 t) Tn). {
        eauto.
      }

      (* Use IH *)
      assert (H_approx_bs : Δ',, Γ' |- (Let NonRec (bs0) t) ≤ t' : Tn). {
        eauto.
      }

      assert (H_unique : unique_tm (Let NonRec (b :: bs0) t)).
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

        destruct H_unused as [ H_unused1 H_unused2 ].

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

  (* W_LetRec *)
  - admit.


  (* W_NilB_NonRec *)
  - unfold P_bindings_well_formed_nonrec; intros.
    split.
    + intros.
      inversion H;subst.
      eauto with DSP_compatibility_lemmas.
    + intros.
      inversion H.

  (* W_ConsB_NonRec *)
  - split.
    + intros.
      inversion H4. subst.
      admit.
    + intros. subst.
    (* TODO, change P_bindings_well_formed_nonrec ? *)

Admitted.
