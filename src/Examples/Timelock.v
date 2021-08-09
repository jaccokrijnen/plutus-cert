Require Coq.Strings.String.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import Ascii.
Require Import Omega.
From Equations Require Import Equations.
Set Implicit Arguments.
Set Printing Universes.

From PlutusCert Require Import Util.
From PlutusCert Require Import Language.PlutusIR.
From PlutusCert Require Import Language.PlutusIR.Folds.
From PlutusCert Require Import Language.PlutusIR.Analysis.FreeVars.
From PlutusCert Require Import Language.PlutusIR.Analysis.Size.
From PlutusCert Require Import Language.PlutusIR.Transform.Inline.
From PlutusCert Require Import Language.PlutusIR.Transform.Inline.DecideStepBool.
From PlutusCert Require Import Language.PlutusIR.Transform.Congruence.
From PlutusCert Require Import Language.PlutusIR.Transform.Universal.
From PlutusCert Require Import Language.PlutusIR.Transform.Compose.
From PlutusCert Require Import Language.PlutusIR.Transform.FloatLet.
From PlutusCert Require Import Language.PlutusIR.Transform.LetNonRec.
From PlutusCert Require Import Language.PlutusIR.Transform.Desugar.DecideBool.
(* From PlutusCert Require Import Language.PlutusIR.Transform.ScottEnc. *)
From PlutusCert Require Import Language.PlutusIR.Optimizer.DeadBindings.
From PlutusCert Require Import Examples.TimelockDumps.

Local Open Scope string_scope.

Ltac cong_tac  := apply DBE_Congruence; apply C_Let;
  [ constructor; [constructor|constructor]
  | ].


Lemma pir0_1 : pir_0_original = pir_1_renamed.
Proof. reflexivity. Qed.

Lemma pir1_2 : pir_1_renamed = pir_2_typechecked.
Proof. reflexivity. Qed.

(* Axiom pir2_3 : DBE_Term pir_2_typechecked pir_3_deadcode.*)
Lemma pir2_3 : DBE_Term pir_2_typechecked pir_3_deadcode.
Proof.
  unfold pir_2_typechecked, pir_3_deadcode.
  repeat (first [cong_tac | elim_let | term_cong]).
Qed.

Ltac skipLet :=
  eapply Inl_Let;
    [ reflexivity
    | eapply Inl_Binding_cons;
      [ constructor
      | constructor
      ]
    | simpl
    ].

(* Recognize inliner *)


(* Lemma pir_3_inlined : Term. *)
Lemma pir3_4 : compose [Inline nil; DBE_Term] pir_3_deadcode pir_4_inlined.
Proof.
  eapply ComposeCons.
  - unfold pir_3_deadcode.
    unfold Name, TyName.
    skipLet.
    skipLet.
    constructor. constructor. constructor. eapply C_TermBind. constructor. repeat constructor. constructor.
    skipLet.
    constructor.
    constructor.
    constructor.
    constructor.


    eapply Inl_Let ; [ reflexivity  | eapply Inl_Binding_cons; [ repeat constructor | constructor ] | ].
    constructor. constructor; [ | repeat constructor].
    constructor. constructor; [ repeat constructor | ].

    constructor. constructor.
    eapply Inl_Var.
      + simpl. tauto. (*unfold In as disjunctions *)
      + repeat constructor.
  -
  eapply ComposeCons ; [ | constructor].
  repeat (first [cong_tac | elim_let | term_cong]).
  Unshelve. (* Not sure why these were left-over*)
Defined.

(* eats memory and doesn't terminate
Eval cbv in is_inline nil pir_3_deadcode pir_4_inlined.
*)

(*
Definition pir3_inlined : {t & {t' & Inline nil t t'}}.
pose pir3_4 as pir3_4.
inversion pir3_4.
exists x. exists y. subst. assumption.
Defined.
  match pir3_4 return Term with
    | ComposeCons inline _ => inline
    | _ => Var "workaround" (* Otherwise Coq tries to do something clever but fails*)
  end.

Print pir3_inlined.
Eval cbv in term_size pir_3_deadcode
Eval cbv in term_size pir_3_deadcode
Eval cbv in is_inline (term_size pir_4_inlined) pir_4_inlined pir_5_thunkrec.
Eval cbv in is_inline (term_size pir_3_deadcode) pir_3_deadcode pir_3_deadcode.
*)
(*
why is this slow?

Eval compute in is_inline (term_size pir_3_inlined_keep) pir_3_inlined_keep pir_3_inlined_keep.
*)

(* it should recognize the identity transformation *)
Eval cbv in is_inline (term_size pir_4_inlined) pir_4_inlined pir_4_inlined.
Definition slow_subterm := (Let NonRec
                    [TermBind NonStrict
                       (VarDecl (Name "keep" (Unique 77)) tt)
                       (Var (Name "a" (Unique 3)))]
                    (Builtin SHA3)).
Eval lazy in (term_size slow_subterm).
Eval lazy in is_inline (term_size slow_subterm) slow_subterm slow_subterm.
(*Eval lazy in is_inline (term_size pir_3_inlined_keep)
  pir_3_deadcode
  pir_3_inlined_keep.*)

Lemma pir4_5 : pir_4_inlined = pir_5_thunkrec.
Proof. reflexivity. Qed.


Lemma pir5_6 : compose [LetMerge; LetReorder] pir_5_thunkrec pir_6_floatTerm.
Proof.
  unfold pir_5_thunkrec, pir_6_floatTerm.
  eapply ComposeCons.

  (* Prove merging of lets, i.e.
       let x = xt in
       let y = yt in
       ...
       in t
       =>
       let x = xt; y = yt; ... in t*)
  - eapply LM_Merge.
    reflexivity.

    (* relate all bound terms which are equal (Zip)*)
    repeat constructor.

    (* relate let-body (which are equal)*)
    repeat constructor.

  (* Prove the permutation is valid *)
  - eapply ComposeCons ; [ | apply ComposeNil ].
    eapply LR_Let;
      [ repeat constructor (* recursive in let body *)
      | repeat constructor (* recursive in bindings *)
      | ].

    (*build the permutation with swaps: 3-4 2-3 1-2 3-4*)
    eapply SwapsIn_cons.
      (* swap 3-4 *)
      refine (Swap_Pop (Swap_Pop (Swap_Top _))).
      apply BC_Symm. eapply BC_DatatypeL.
      repeat (apply Forall_cons; [notIn2|]). apply Forall_nil.

    eapply SwapsIn_cons.
      (* swap 2-3*)
      refine (Swap_Pop (Swap_Top _)).
      apply BC_Datatypes.

    eapply SwapsIn_cons.
      (* swap 1-2*)
      refine (Swap_Top _).
      apply BC_Datatypes.

    eapply SwapsIn_cons.
      (* swap 3-4*)
      refine (Swap_Pop (Swap_Pop (Swap_Top _))).
      eapply BC_DatatypeL.
      repeat (apply Forall_cons; [notIn2|]). apply Forall_nil.
    apply SwapsIn_nil.
Qed.



Definition pir6_plc0 : pir_6_floatTerm = plc_0_compileNS.
Proof. reflexivity. Qed.


(* TODO: get actual Scott rel working again*)
Definition Scott (s : Term) t := Universal s t.


Definition plc_0_1 : Scott plc_0_compileNS plc_1_compileTys.
Proof.
  constructor.
Qed.
(* Eval cbv in scottEncode' plc_0_compileNS.*)
(* Definition plc_0_1 : ScottEncode' plc_0_compileNS plc_1_compileTys := Uni.*)

(*
Definition plc_0_1 : ScottEncode' plc_0_compileNS plc_1_compileTys .
Proof. unfold ScottEncode'.
  apply folds_equal.
  cbv.
  reflexivity.
Qed.
*)

Definition plc_1_2 : plc_1_compileTys = plc_2_compileRecTerms.
Proof. reflexivity. Qed.

Definition plc_2_3 :
  DBE_Term plc_2_compileRecTerms plc_3_dbe.
Proof.
  unfold plc_2_compileRecTerms, plc_3_dbe.
  repeat (first [cong_tac | elim_let | term_cong]).
Qed.

Definition plc_3_4 :
  plc_3_dbe = plc_4_inlined.
Proof. reflexivity. Qed.

Compute Term_desugar plc_4_inlined plc_5_compileNonRecTerms.

Definition plc_4_5_true : Term_desugar plc_4_inlined plc_5_compileNonRecTerms = true.
Proof. reflexivity. Qed.

Compute (Term_desugar_sound _ _ (plc_4_5_true)).
Definition plc_4_5 :
  CNR_Term plc_4_inlined plc_5_compileNonRecTerms.
Proof.
  exact (Term_desugar_sound _ _ (plc_4_5_true)).
Qed.

(* doesn't run anymore after refactoring rules:
Definition plc_4_5 :
  CNR_Term plc_4_inlined plc_5_compileNonRecTerms.
  unfold plc_4_inlined, plc_5_compileNonRecTerms.
  repeat (first [eapply CNR_Let; repeat econstructor | constructor]).
Qed.
*)


Definition pir_0_6 : compose _ pir_2_typechecked plc_5_compileNonRecTerms:=
  ComposeCons pir0_1
    (ComposeCons pir1_2
    (ComposeCons pir2_3
    (ComposeCons pir3_4
    (ComposeCons pir4_5
    (ComposeCons pir5_6
    (ComposeCons pir6_plc0
    (ComposeCons plc_0_1
    (ComposeCons plc_1_2
    (ComposeCons plc_2_3
    (ComposeCons plc_3_4
    (ComposeCons plc_4_5
     ComposeNil
    ))))))))))).

(*
Hangs
Eval cbv in dbe_dec_Term pir2 pir3.
*)
