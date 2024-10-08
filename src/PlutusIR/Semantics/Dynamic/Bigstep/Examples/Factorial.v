Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Import PlutusNotations.


(* Build lazy if-then-else using thunking *)

Definition thunk t :=
  <{ λ "unit" :: unit, t }>
.

Definition force t :=
  <{ t ⋅ () }>
.

Definition lazy_if T b t1 t2 :=
force
  <{
    ifthenelse @ (unit → T) ⋅ b ⋅ {thunk t1} ⋅ {thunk t2}
  }>
.

Definition fact_term (n : Z) : term :=
  Let
    Rec
    [ TermBind
        Strict
        (VarDecl
          "fact"
          (Ty_Fun
            (Ty_Builtin DefaultUniInteger)
            (Ty_Builtin DefaultUniInteger)
          )
        )
        (LamAbs
          "x"
          (Ty_Builtin DefaultUniInteger)
          (lazy_if <{ ℤ }>
            <{ {Builtin EqualsInteger} ⋅ {Var "x"} ⋅ (Int 0) }>
            <{ Int 1 }>
            <{ {Var "x"} × ({Var "fact"} ⋅ ({Var "x"} - (Int 1)))}>
          )
        )
    ]
    (Apply
      (Var "fact")
      (Constant (ValueOf DefaultUniInteger n))
    ).

Ltac invert_contra := let Hcon := fresh "Hcon" in intros Hcon; inversion Hcon.
Ltac destruct_invert_contra := let Hcon := fresh "Hcon" in intros Hcon; destruct Hcon as [Hcon | Hcon]; try solve [inversion Hcon || destruct Hcon].
Ltac solve_substitute := repeat (econstructor || eauto || invert_contra || destruct_invert_contra).
Ltac solve_value_builtin := repeat econstructor.

Ltac invert_unsaturated :=
  match goal with
  | H : unsaturated_with ?n ?t |- False =>
      inversion H; clear H; subst; try invert_unsaturated
  | H : unsaturated ?t |- False =>
      inversion H; clear H; subst; try invert_unsaturated
  end.

Ltac decide_unsaturated :=
  match goal with
  | |- unsaturated_with ?n ?nv =>
      econstructor; eauto; try decide_unsaturated
  | |- ?f <> ?f' =>
      let Hcon := fresh "Hcon" in
      try solve [intros Hcon; inversion Hcon]
  end.

Lemma eval_ifthenelse_true : forall T t1 t2 t3 v2 v3 k1 k2 k3,
    t1 =[ k1 ]=> <{ true }> ->
    t2 =[ k2 ]=> v2 ->
    t3 =[ k3 ]=> v3 ->
    <{ ifthenelse @ T ⋅ t1 ⋅ t2 ⋅ t3 }> =[ k2 ]=> v2.
Admitted.

Lemma eval_ifthenelse_false : forall T t1 t2 t3 v2 v3 k1 k2 k3,
    t1 =[ k1 ]=> <{ false }> ->
    t2 =[ k2 ]=> v2 ->
    t3 =[ k3 ]=> v3 ->
    <{ ifthenelse @ T ⋅ t1 ⋅ t2 ⋅ t3 }> =[ k2 ]=> v3.
Admitted.

Example fact_term_evaluates : exists k,
  fact_term 2 =[k]=> Constant (ValueOf DefaultUniInteger 2).
Proof with (autounfold; simpl; eauto || (try reflexivity) || (try solve [intros Hcon; inversion Hcon])).
  unfold fact_term.
  eexists.
  apply E_LetRec.
  eapply E_LetRec_TermBind.
  simpl.
  eapply E_LetRec_Nil.
  eapply E_Apply... {
    eapply E_LetRec.
    eapply E_LetRec_TermBind.
    simpl.
    eapply E_LetRec_Nil...
    constructor.
  } {
    constructor.
    } {
    inversion 1.
    } {
    simpl.

    eapply E_Apply. {
      eapply eval_ifthenelse_false.
      - eapply E_NeutralApplyFull...
        eapply S_Apply...
        eapply S_Apply...
      - constructor.
      - constructor.
      } {
      constructor. } {
        inversion 1.
      }

      simpl.

      eapply E_NeutralApplyPartial...
      - intros.
        invert_unsaturated.
        simpl in H3.
        inversion H3.
        inversion H0.
        inversion H7.
      - constructor.
        constructor...
      - constructor...
      - eapply E_Apply.
        + eapply E_LetRec.
          constructor.
          simpl.
          eapply E_LetRec_Nil.
          constructor.
        + eapply E_NeutralApplyFull.
          * constructor...
            constructor...
          * reflexivity.
        + inversion 1.
        + simpl.
          eapply E_Apply.
          eapply eval_ifthenelse_false.
          { constructor...
            constructor...
            constructor...
          } {
            constructor.
          } {
            constructor.
          } {
            constructor.
          } {
            inversion 1.
          } {
            simpl.
            eapply E_NeutralApplyPartial.
            { intro.
              invert_unsaturated.
              inversion H3.
              inversion H0.
              inversion  H7.
            } {
              constructor...
              constructor...
            } {
              constructor...
            } {
              eapply E_Apply.
              { eapply E_LetRec.
                constructor.
                simpl.
                eapply E_LetRec_Nil.
                constructor.
            } {
              eapply E_NeutralApplyFull...
              constructor...
              constructor...
            } {
              inversion 1.
            } {
              simpl.
              eapply E_Apply.
              { eapply eval_ifthenelse_true...
              { eapply E_NeutralApplyFull...
                constructor...
                constructor...
              } {
                constructor...
              } {
                constructor...
              } }
              { constructor... }
              { inversion 1. }
              { constructor... } }
              }
              { inversion 1. }
              { eapply E_NeutralApplyFull...
                constructor...
                constructor...
              }
              }
        - inversion 1.
        - eapply E_NeutralApplyFull...
          constructor...
          constructor...
          }
Qed.
