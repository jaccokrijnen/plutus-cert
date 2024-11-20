From PlutusCert Require Import
  PlutusIR
  Bigstep
  Util
.

Import PlutusNotations.


Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.



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
        NonStrict
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
            <{ {Builtin EqualsInteger} ⋅ {Var "x"} ⋅ (CInt 0) }>
            <{ CInt 1 }>
            <{ {Var "x"} * ({Var "fact"} ⋅ ({Var "x"} - (CInt 1)))}>
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

Ltac finish :=
  match goal with

  (* fully_applied *)
    | |- ~ fully_applied ?t =>
           assert (H := sumboolOut (fully_applied_dec t));
           assumption
    | |- fully_applied ?t -> False =>
           assert (H := sumboolOut (fully_applied_dec t));
           assumption
    | |- fully_applied ?t =>
           assert (H := sumboolOut (fully_applied_dec t));
           assumption

  (* bindings_nonstrict *)
    | |- bindings_nonstrict ?bs ?bs' => auto using bindings_nonstrict

  (* is_error *)

    | |- ~ is_error ?v => inversion 1
  end.



Example fact_term_evaluates : exists k,
  fact_term 2 =[k]=> Constant (ValueOf DefaultUniInteger 2).
Proof with (simpl; auto; try solve [finish]).
  unfold fact_term.
  eexists.
  eapply E_LetRec...
  eapply E_LetRec_TermBind_NonStrict.
  simpl.
  eapply E_LetRec_Nil.
  eapply E_Apply...
  {
    eapply E_LetRec...
    eapply E_LetRec_TermBind_NonStrict.
    simpl.
    eapply E_LetRec_Nil...
    constructor.
  }
  { constructor. }
  { inversion 1. }
  {
    simpl.

    eapply E_Apply...
    {
      eapply eval_ifthenelse_false.
      - eapply E_Builtin_Apply...
      - constructor.
      - constructor.
      } {
      constructor. } {
        inversion 1.
      }

      simpl.

      eapply E_Apply...
      - eapply E_Apply...
        + apply E_Builtin_Eta with (f := MultiplyInteger)...
        + constructor.
        + inversion 1.
        + cbn. constructor.
      - eapply E_Apply...
        + eapply E_LetRec.
          { auto using bindings_nonstrict. }
          constructor.
          simpl.
          eapply E_LetRec_Nil.
          constructor.
        + eapply E_Builtin_Apply...
        + inversion 1.
        + simpl.
          eapply E_Apply...
          { eapply eval_ifthenelse_false.
            - constructor...
            - constructor...
            - constructor...
          }
          { constructor... }
          { finish.  }
          { simpl.
            eapply E_Apply...
            - eapply E_Apply...
              + apply E_Builtin_Eta with (f := MultiplyInteger).
              + constructor...
              + finish.
              + simpl.
                constructor...
            - eapply E_Apply...
              + econstructor...
                constructor.
                simpl.
                constructor.
                constructor.
              + constructor...
              + finish.
              + simpl.
                eapply E_Apply...
                * eapply eval_ifthenelse_true...
                  ** constructor...
                  ** constructor...
                  ** constructor...
                * constructor...
                * finish.
                * constructor...
            - finish.
            - constructor...
          }
          - finish.
          - constructor...
          }
Qed.
