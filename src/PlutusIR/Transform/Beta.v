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

Context
  (dec : list (term * (term -> bool)) -> term -> term -> bool)
  (C : list (term * (term -> bool)))
  (t t' : term)
.

Definition dec_compat : bool :=
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

Fixpoint dec (C : list (term * (term -> bool))) (t t' : term) : bool :=
     dec_compat dec C t t'
  || dec_Apply dec C t t'
  || dec_LamAbs dec C t t'
  || dec_TyAbs_TyInst dec C t t'
.


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

  Lemma dec_sound_compat :
    dec_compat dec C t t' = true ->
    betas (map fst C) t t'.
  Proof.
    unfold dec_compat.
    destruct C; try solve [inversion 1].
    intros H.
    constructor.
    specialize (dec_sound []); simpl in dec_sound.
    eapply sound_dec_compat.
    - intros t0 t0'.
      specialize (dec_sound t0 t0' C_sound).
      eauto.
    - eauto.
  Defined.

End SOUND.


(* Defines when an argument in the (extended) application context has a
   sound decision procedure
*)

Lemma dec_sound C s t :
  Forall arg_sound C ->
  dec C s t = true ->
  betas (map fst C) s t.
Proof.
  intros H_C H_dec.
  induction s.
  - admit.
  - destruct t.
    + simpl in H_dec.
      apply orb_prop in H_dec.
      destruct H_dec.
      * unfold dec_LamAbs in H.
        destruct C. inversion H.
        destruct p; inversion H.
      * admit.
    + (* Var, Var case compatibility *)
      simpl in H_dec.
      repeat rewrite orb_true_iff in H_dec.
      repeat destruct H_dec as [H_dec | ?].
      * unfold dec_compat in H_dec; destruct C.
        ** unfold Compat.dec_compat in H_dec.
           rewrite string_eqb_eq in H_dec.
           subst n0.
           constructor.
           constructor.
        ** inversion H_dec.
      * inversion H.
      * unfold dec_LamAbs in H; simpl. destruct C; inversion H; destruct p;
      inversion H.
      * admit.
    + simpl in H_dec.
  (* Needs stronger IH for terms inside Let *)
  (* Perhaps there is a simpler IH possible that follows the function structure
     of dec
  *)
Abort.

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
