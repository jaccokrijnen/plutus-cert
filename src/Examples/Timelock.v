Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import Ascii.
From Equations Require Import Equations.

From PlutusCert Require Import
  Util
  PlutusIR.Transform
  PlutusIR.Analysis.Purity
  PlutusIR.Transform.LetNonRec.DecideBool
  Semantics.Dynamic
  Examples.TimelockDumps
.

Import NamedTerm.

Set Implicit Arguments.
Set Printing Universes.

Local Open Scope string_scope.

Ltac compat_tac  := (* apply DBE_Congruence; *) apply C_Let;
  [ constructor; [constructor|constructor]
  | ].


Lemma pir0_1 : pir_0_original = pir_1_renamed.
Admitted.

Lemma pir1_2 : pir_1_renamed = pir_2_typechecked.
Proof. reflexivity. Qed.


Create HintDb hint_dead_code.

(* safe_binding constraints *)
#[global]
Hint Constructors
  Forall
  (* safe_binding *)
  is_pure
  pure_binding
  value
: hint_dead_code.
#[global]
Hint Resolve
  (* use decision procedure*)
  dec_is_error_not_is_error
: hint_dead_code.

#[global]
Hint Resolve
  -> Nat.leb_le 0 : hint_dead_code
.

(* Compatibility *)
#[global]
Hint Constructors
  (* Compat *)
  Compat
  Compat_Binding
  Compat_Bindings
  : hint_dead_code.

#[global]
Hint Resolve
  elim_sym : hint_dead_code
.

(* Using reflection *)
Lemma pir2_3' : dead_code pir_2_typechecked pir_3_deadcode.
Proof.
Admitted.


Lemma pir2_3 : dead_code pir_2_typechecked pir_3_deadcode.

(* TODO: there was an intermediate rename term, this built before because we were comparing
        string names, instead of uniques *)
(*
Proof with auto 10 with hint_dead_code.
  split.
  2: admit. (* typing and unique *)
  apply elim_delete_let...

  unfold pir_3_deadcode.
  apply elim_cong, C_Let...
  do 2 (apply elim_delete_let; auto 10 with hint_dead_code).
  apply elim_cong, C_Let...
  do 11 (apply elim_delete_let; auto 10 with hint_dead_code).
  apply elim_cong, C_Let...
  do 16 (apply elim_delete_let; auto 10 with hint_dead_code).
  apply elim_cong, C_Let...
  apply elim_cong, Congruence.C_LamAbs...
  apply elim_cong, Congruence.C_LamAbs...
  apply elim_cong, C_Let...
  apply elim_delete_let...
 *)
Admitted.

(* TODO: Update with new definition of inline and dead_code *)
(*
Ltac skipLet :=
  eapply Inl_Let;
    [ reflexivity
    | eapply Inl_Binding_cons;
      [ constructor
      | constructor
      ]
    | simpl
    ].
    *)

(* Recognize inliner *)


(* TODO: Update with new definition of inline and dead_code *)
(* Lemma pir_3_inlined : Term. *)
Lemma pir3_4 : compose_prop [inline nil nil; dead_code] pir_3_deadcode pir_4_inlined.
Proof.
(*
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
  admit. (* TODO: fix this with new definition of DBE*)
  Unshelve. (* Not sure why these were left-over*)
*)
Admitted.

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

(*
Eval cbv in is_inline (term_size pir_4_inlined) pir_4_inlined pir_4_inlined.
Definition slow_subterm : Term := (Let NonRec
                    [TermBind NonStrict
                       (VarDecl (Name "keep" (Unique 77)) tt)
                       (Var (Name "a" (Unique 3)))]
                    (Builtin SHA3)).
Eval lazy in (term_size slow_subterm).
Eval lazy in is_inline (term_size slow_subterm) slow_subterm slow_subterm.
*)
(*Eval lazy in is_inline (term_size pir_3_inlined_keep)
  pir_3_deadcode
  pir_3_inlined_keep.*)

Lemma pir4_5 : pir_4_inlined = pir_5_thunkrec.
Proof. reflexivity. Qed.


(* TODO: Update proof with new definitions of FloatLet *)
Lemma pir5_6 : let_float pir_5_thunkrec pir_6_floatTerm.
Proof.
  unfold pir_5_thunkrec, pir_6_floatTerm.
Admitted.
  (*
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
*)



Definition pir6_plc0 : pir_6_floatTerm = plc_0_compileNS.
Proof. reflexivity. Qed.


Definition Scott (s t : Term) := True.
Definition DBE (s t : Term) := True.


Definition plc_0_1 : Scott plc_0_compileNS plc_1_compileTys.
Proof.
  constructor.
Qed.

Definition plc_1_2 : plc_1_compileTys = plc_2_compileRecTerms.
Proof. reflexivity. Qed.

Definition plc_2_3 :
  DBE plc_2_compileRecTerms plc_3_dbe.
Proof.
  unfold plc_2_compileRecTerms, plc_3_dbe.
  constructor.
Qed.

Definition plc_3_4 :
  plc_3_dbe = plc_4_inlined.
Proof. reflexivity. Qed.

(* Compute Term_desugar plc_4_inlined plc_5_compileNonRecTerms. *)

Definition plc_4_5_true : Term_desugar plc_4_inlined plc_5_compileNonRecTerms = true.
Proof. reflexivity. Qed.

Definition plc_4_5 :
  CNR_Term plc_4_inlined plc_5_compileNonRecTerms.
Proof.
  exact (Term_desugar_sound _ _ (plc_4_5_true)).
Qed.

(*
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
 *)
