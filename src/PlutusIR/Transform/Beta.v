From Coq Require Import
  Lists.List
  Strings.String.
Import ListNotations.
From PlutusCert Require Import
  PlutusIR
  Util
  Compat
  LetMergeNR
  FreeVars
  Util.List
  Util.Tactics
  Size
.


(*

This pass transforms beta redexes into let non-recs, so that the later inlining
pass has more opportunities for inlining.

Transforms repeated applications (not just repeated β-redexes), e.g.

(\x y z. t) t₁ t₂ t₃

=>

let nonrec x = t₁
           y = t₂
           z = t₃
in t

Has to avoid capture: e.g. t₂ may not have a free variable `x` as it would be captured
by the first binding

*)




Definition app_ctx := list term.

Function apps (t : term) (C : app_ctx) : term :=
  match C with
  | [] => t
  | s :: ss => apps (Apply t s) ss
  end.

Inductive betas : app_ctx -> term -> term -> Prop :=
  | beta_Compat s t :
     Compat (betas []) s t ->
     betas [] s t

  | beta_Apply C s t r :
     betas (t :: C) s           r ->
     betas C        (Apply s t) r

  | beta_LamAbs C x T t t' t0 t0' :
     betas C t t' ->
     betas [] t0 t0' ->
     (Forall (fun t => x ∉ Term.fv t) C) ->
     betas (t0 :: C)
      (LamAbs x T t)
      (Let NonRec [TermBind Strict (VarDecl x T) t0'] t')

  | beta_TyInst_TyAbs X K t T t' :
      betas [] t t' ->
      betas []
        (TyInst (TyAbs X K t) T)
        (Let NonRec [TypeBind (TyVarDecl X K) T] t')


  .

Lemma beta_refl : forall x, betas [] x x.
Proof.
  apply term__ind with (Q := fun b => Compat_Binding (betas []) b b).
  all: try auto using betas, Compat, Compat_Bindings, Compat_Binding.
  - intros.
    constructor.
    constructor.
    + induction bs.
      * auto using Compat_Bindings.
      * inversion H; auto using Compat_Bindings, Compat.
    + assumption.
  - admit. (* TODO add Constr to Compat *)
  - admit. (* TODO add Case to Compat *)
Admitted.

Definition spec s t := betas [] (split s) (split t).


Require Import
  Bool.Bool.
From PlutusCert Require Import
  Equality.

Inductive result (A : Set) :=
  | success
  | failure : A -> result A
.
Arguments success {_}.
Arguments failure {_} _.


Section DEC.

Definition app_ctx_dec := list (term * (term -> bool)).

Context
  (dec : app_ctx_dec -> term -> term -> bool)
  (C : app_ctx_dec)
  (t t' : term)
.

Definition dec_compat : bool :=
  match C, t, t' with
  | [], (Let r bs t), (Let r' bs' t')      =>
                                    recursivity_eqb r r'
                                    && (fix f bs bs' :=
                                        (match bs, bs' with
                                          | []       , []        => true
                                          | (b :: bs), (b' :: bs') =>
                                            (
                                              match b, b' with
                                                | (TermBind s v t), (TermBind s' v' t') => strictness_eqb s s' && VDecl_eqb v v' && dec [] t t'
                                                | (TypeBind v T), (TypeBind v' T') => TVDecl_eqb v v'  && Ty_eqb T T'
                                                | (DatatypeBind d), (DatatypeBind d') => DTDecl_eqb d d'
                                                | _, _                               => false
                                              end
                                            && f bs bs')%bool
                                          | _        , _         => false
                                        end)) bs bs'
                                    && dec [] t t'
  | [], (Var n), (Var n')                  => String.eqb n n'
  | [], (TyAbs n k t), (TyAbs n' k' t')    => String.eqb n n' && Kind_eqb k k' && dec [] t t'
  | [], (LamAbs n T t), (LamAbs n' T' t')  => String.eqb n n'&& Ty_eqb T T' && dec [] t t'
  | [], (Apply s t), (Apply s' t')         => dec [] s s' && dec [] t t'
  | [], (Constant c), (Constant c')        => constant_eqb c c'
  | [], (Builtin f), (Builtin f')          => func_eqb f f'
  | [], (TyInst t T), (TyInst t' T')       => Ty_eqb T T' && dec [] t t'
  | [], (Error T), (Error T')              => Ty_eqb T T'
  | [], (IWrap T1 T2 t), (IWrap T1' T2' t') => Ty_eqb T1 T1' && Ty_eqb T2 T2' && dec [] t t'
  | [], (Unwrap t), (Unwrap t')            => dec [] t t'
  | _, _, _                               => false
  end
  .

Definition dec_compat' : bool :=
  match C, t, t' with
  | [], t, t' => Compat.dec_compat (dec []) t t'
  | _, _, _ => false
  end
  .

Definition dec_Apply : bool :=
  match C, t, t' with
  | C, Apply s t, r => dec ((t, dec [] t) :: C) s r
  | _, _, _ => false
  end
.

Definition dec_TyAbs_TyInst : bool :=
  match C, t, t' with
  | []
  , TyInst (TyAbs X K t) T
  , Let NonRec [TypeBind (TyVarDecl X' K') T'] t'
  =>
      String.eqb X X' &&
      Kind_eqb K K' &&
      Ty_eqb T T' &&
      dec [] t t'
  | _, _, _ => false
  end.

Definition dec_LamAbs : bool :=
  match C, t, t' with
  | (t0, dec_t0) :: C
  , LamAbs x T t
  , Let NonRec [TermBind Strict (VarDecl x' T') t0'] t'
  =>
      String.eqb x x' &&
      Ty_eqb T T' &&
      dec_t0 t0' &&
      dec C t t' &&
      forallb (fun '(t, f) => negb (in_str x (Term.fv t))) C
  | _, _, _ => false
  end
.

End DEC.

Fixpoint dec (C : app_ctx_dec) (t t' : term) : bool :=
     dec_compat dec C t t'
  || dec_Apply dec C t t'
  || dec_LamAbs dec C t t'
  || dec_TyAbs_TyInst dec C t t'
.

Definition dec_unfold C t t' :
  dec C t t' =
     dec_compat dec C t t'
  || dec_Apply dec C t t'
  || dec_LamAbs dec C t t'
  || dec_TyAbs_TyInst dec C t t'
.
Proof.
  destruct C, t, t'; reflexivity.
Qed.



Section SOUND.

  (* Defines when an argument in the (extended) application context has a
     sound decision procedure
  *)
  Definition arg_sound '(t, dec_t) :=
    forall t', dec_t t' = true -> betas [] t t'.

  Lemma Forall_map_fst {A} (f : term -> Prop) (l : list (term * A)):
    Forall (fun '(t, _) => f t) l ->
    Forall (fun t => f t) (map fst l).
  Proof.
    induction l.
    - auto.
    - inversion 1; subst.
      destruct a.
      constructor; auto.
  Qed.


  (* TODO move to List.Util *)
  Lemma negb_iff b :
    negb b = true <-> b = false.
  Proof. destruct b; intuition. Qed.

  Lemma negb_in_str__NotIn x xs :
    negb (in_str x xs) = true ->
    x ∉ xs
  .
  Proof.
    induction xs.
    - simpl. auto.
    - intros.
      rewrite negb_iff in *.
      admit.
  Admitted.

  Context
    (dec : app_ctx_dec -> term -> term -> bool)
    (dec_sound : forall C s t,
      Forall arg_sound C ->
      dec C s t = true ->
      betas (map fst C) s t)
    (C : list (term * (term -> bool)))
    (C_sound : Forall arg_sound C)
    (t t' : term)
  .

  Lemma dec_sound_Apply : dec_Apply dec C t t' = true -> betas (map fst C) t t'.
  Proof.
    unfold dec_Apply.
    destruct t; try solve [inversion 1].
    clear t.
    rename t0_1 into s.
    rename t0_2 into t.
    intros H_dec.
    apply dec_sound in H_dec.
    - auto using betas.
    - constructor; try assumption.
      unfold arg_sound.
      intros.
      specialize (dec_sound []).
      apply dec_sound;auto.
  Defined.

  Lemma dec_sound_LamAbs : dec_LamAbs dec C t t' = true -> betas (map fst C) t t'.
  Proof.
    unfold dec_LamAbs.
    destruct C; try solve [inversion 1].
    destruct p.
    destruct t; try solve [inversion 1].
    destruct t'; try solve [inversion 1].
    destruct r; try solve [inversion 1].
    destruct l0; try solve [inversion 1].
    destruct b1; try solve [inversion 1].
    destruct s; try solve [inversion 1].
    destruct v; try solve [inversion 1].
    destruct l0; try solve [inversion 1].
    intros H_dec.
    repeat apply andb_and in H_dec as [H_dec ?].
    simpl.

    (* Todo, use apply that leaves equality goals *)
    rewrite string_eqb_eq in H_dec; subst b0.
    rewrite Ty_eqb_eq in H2; subst t1.

    apply beta_LamAbs.
    - eauto using Forall_inv_tail.
    - unfold arg_sound in C_sound. apply Forall_inv in C_sound.
      auto.
    -
      apply Forall_map_fst.
      rewrite forallb_forall in H.
      rewrite Forall_forall.
      intros.
      specialize (H x H2).
      destruct x.
      apply negb_in_str__NotIn.
      assumption.
  Defined.

  Lemma dec_sound_TyBeta :
    dec_TyAbs_TyInst dec C t t' = true ->
    betas (map fst C) t t'.
  Proof.
    unfold dec_TyAbs_TyInst.
    destruct t, C; try solve [inversion 1].
    destruct t0; try solve [inversion 1].
    destruct t'; try solve [inversion 1].
    destruct r; try solve [inversion 1].
    destruct l; try solve [inversion 1].
    destruct b0; try solve [inversion 1].
    destruct t3; try solve [inversion 1].
    destruct l; try solve [inversion 1].
    intros H_dec.
    destruct_hypos.
    rewrite String.eqb_eq in H.
    rewrite Kind_eqb_eq in H2.
    rewrite Ty_eqb_eq in H1.
    subst.
    simpl.
    apply beta_TyInst_TyAbs.
    specialize (dec_sound []).
    auto.
  Defined.


  Definition P_term t := forall C t',
    dec_compat dec C t t' = true ->
    betas (map fst C) t t'
  .

  Lemma dec_sound_compat :
    dec_compat dec C t t' = true ->
    betas (map fst C) t t'.
  Proof.
    specialize (dec_sound []). (* usable IH for auto due to map fst *)
    destruct C; try solve [inversion 1].
    destruct t, t'.
    all: try solve [unfold dec_compat; inversion 1].
    all: intros H_dec; simpl in H_dec; try discriminate H_dec.
    all: split_hypos.
    all: try (constructor; (eauto with compat reflection)).
    - (* Let *)
      apply c_Let; try solve [eauto with compat reflection].
      + revert dependent l0. induction l; intros l0 H_dec.
        * destruct l0; simpl.
          ** constructor.
          ** inversion H_dec.
        * destruct l0.
          ** inversion H_dec.
          ** constructor.
            *** 
                destruct a, b; destruct_hypos; try solve [inversion H1].
                destruct_hypos.
                ++ eauto with compat reflection.
                ++ eauto with compat reflection.
                ++ eauto with compat reflection.
            *** destruct_hypos.
              auto.
  Defined.

End SOUND.


(* Defines when an argument in the (extended) application context has a
   sound decision procedure
*)

Fixpoint dec_sound C t t' {struct t} :
  Forall arg_sound C ->
  dec C t t' = true ->
  betas (map fst C) t t'.
Proof.
  setoid_rewrite dec_unfold.
  setoid_rewrite orb_true_iff.
  setoid_rewrite orb_true_iff.
  setoid_rewrite orb_true_iff.
  intros C_sound H_dec.
  destruct H_dec as [[[H_dec | H_dec] | H_dec] | H_dec ].
  - apply dec_sound_compat in H_dec.
    destruct t; (* no need for induction since this is already a Fixpoint *)
    assumption.
    all: try assumption.
  - apply dec_sound_Apply in H_dec.
    destruct t; (* no need for induction since this is already a Fixpoint *)
    assumption.
    all: try assumption.
  - apply dec_sound_LamAbs in H_dec.
    destruct t; (* no need for induction since this is already a Fixpoint *)
    assumption.
    all: try assumption.
  - apply dec_sound_TyBeta in H_dec.
    destruct t; (* no need for induction since this is already a Fixpoint *)
    assumption.
    all: try assumption.
Defined. 

Module Example.


Open Scope string.

Definition ty_unit := (Ty_Builtin DefaultUniUnit).
Definition lam x t := LamAbs x ty_unit t.
Definition unit := (Constant (ValueOf DefaultUniUnit tt)).

Definition s :=
  Apply
    (Apply
      (lam "x"
        (lam "y" (Var "x"))
      )
      unit
    )
    unit
.

Definition s' :=
  Let NonRec
    [ TermBind Strict (VarDecl "x" ty_unit) unit;
      TermBind Strict (VarDecl "y" ty_unit) unit
    ]
    (Var "x")
.


Goal betas [] (split s) (split s').
  simpl.
  apply beta_Apply.
  apply beta_Apply.
  apply beta_LamAbs.
  apply beta_LamAbs;
  repeat constructor. (* Why does auto using betas, Compat not work? *)
  repeat constructor.
  constructor.
  simpl. intro. assumption.
  constructor.
Qed.

Goal dec [] (split s) (split s') = true.
Proof.
  reflexivity.
Qed.

Import PIRNotations.
Import ListNotations.
Open Scope pir_scope.

Definition u := (Λ "X" ★ unit) @ ty_unit.

Definition v :=
  let_
    [type ("X" :* ★) = ty_unit]
    unit
.

Goal betas [] u v.
  apply beta_TyInst_TyAbs.
  repeat constructor. (* Why does auto using betas, Compat not work? *)
Qed.

Goal dec [] u v = true.
simpl.
reflexivity.
Qed.

(* Multi type lets is not allowed *)
Definition w :=
  (Λ "X" ★ (λ "y" (Ty_Var "X") `"y")) @ ty_unit ⋅ unit.

Definition x :=
  let_
    [type "X" :* ★ = ty_unit]
    let_
      ["y" : (Ty_Var "X") = unit]
      `"y"
.

Unset Printing Notations.

Goal betas [] w x.
  unfold w, x.
  constructor.
  Fail constructor.
Abort.

Goal dec [] w x = false.
reflexivity.
Qed.


End Example.
