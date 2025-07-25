Set Implicit Arguments.
From PlutusCert Require Import PlutusIR.
From Coq Require Import
  Bool.Bool
  Utf8_core.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import
  Util.List
  Analysis.Equality
  .

Import ListNotations.

Section Term.

  Context (R : term -> term -> Prop).
  Context (RB : binding -> binding -> Prop).

  Definition compat_TermBind := ∀ s v t t',
    R t t' ->
    RB (TermBind s v t) (TermBind s v t').

  Definition compat_TypeBind := ∀ tvd T,
    RB (TypeBind tvd T) (TypeBind tvd T).

  Definition compat_DatatypeBind := ∀ dtd,
    RB (DatatypeBind dtd) (DatatypeBind dtd).


  (* TODO: we cannot have this, since Coq cannot generate nice induction schemes
   * for the nested recursion that exists between the relation and Forall2
   * so instead, we have a separate case for nil and cons.

   * The same applies to Constr and Case
   *)
  (*
  Definition compat_Let := ∀ r bs bs' t t',
    Forall2 RB bs bs' ->
    R t t' ->
    R (Let r bs t) (Let r bs' t').
  *)

  Definition compat_Let_nil := ∀ r t t',
    R t t' ->
    R (Let r [] t) (Let r [] t').

  Definition compat_Let_cons := ∀ r b b' bs bs' t t',
    RB b b' ->
    R (Let r bs t) (Let r bs' t') ->
    R (Let r (b :: bs) t) (Let r (b' :: bs') t').

  Definition compat_Var   := ∀ n, R (Var n) (Var n).

  Definition compat_TyAbs := ∀ X K t t',
    R t t' ->
    R (TyAbs X K t) (TyAbs X K t').

  Definition compat_LamAbs := ∀ x T t t',
    R t t' ->
    R (LamAbs x T t) (LamAbs x T t').

  Definition compat_Apply := ∀ s s' t t',
    R s s' ->
    R t t' ->
    R (Apply s t) (Apply s' t').

  Definition compat_Constant := ∀ v,
    R (Constant v) (Constant v).

  Definition compat_Builtin := ∀ f,
    R (Builtin f) (Builtin f).

  Definition compat_TyInst := ∀ t t' T,
    R t t' ->
    R (TyInst t T) (TyInst t' T).

  Definition compat_Error := ∀ T,
    R (Error T) (Error T).

  Definition compat_IWrap := ∀ T1 T2 t t',
    R t t' ->
    R (IWrap T1 T2 t) (IWrap T1 T2 t').

  Definition compat_Unwrap := ∀ t t',
    R t t' ->
    R (Unwrap t) (Unwrap t').

  (* TODO: add cons/nil cases for Constr and Case, so
     correct induction schemes are generated *)
  Definition compat_Constr := ∀ T i ts ts',
    Forall2 R ts ts' ->
    R (Constr T i ts) (Constr T i ts').


  Definition compat_Case := ∀ T (t t' : term) ts ts',
    R t t' ->
    Forall2 R ts ts' ->
    R (Case T t ts) (Case T t' ts').

End Term.


Section Compatibility.

  Context
    (R : term -> term -> Prop)
    (dec_R : term -> term -> bool)
  .

  Inductive Compat_Binding : binding -> binding -> Prop :=
    | C_TermBind     : ∀ s v t t',
        R t t' -> Compat_Binding (TermBind s v t) (TermBind s v t')

    | C_TypeBind     : ∀ d T,
        Compat_Binding (TypeBind d T) (TypeBind d T)

    | C_DatatypeBind : ∀ d,
        Compat_Binding (DatatypeBind d) (DatatypeBind d)
    .

  Inductive Compat_Bindings : list binding -> list binding -> Prop :=
    | Compat_Bindings_Cons : ∀ {b b' bs bs'},
        Compat_Binding b b' -> Compat_Bindings bs bs' -> Compat_Bindings (b :: bs) (b' :: bs')

    | Compat_Bindings_Nil :
        Compat_Bindings nil nil.

  Inductive Compat : term -> term -> Prop :=
    | C_Let : ∀ bs bs' r t t',
        Compat_Bindings bs bs' -> R t t' -> Compat (Let r bs t) (Let r bs' t')

    | C_Var : ∀ n,
        Compat (Var n) (Var n)

    | C_TyAbs : ∀ n k t t',
        R t t' -> Compat (TyAbs n k t) (TyAbs n k t')

    | C_LamAbs : ∀ n T t t' ,
        R t t' -> Compat (LamAbs n T t) (LamAbs n T t')

    | C_Apply : ∀ s s' t t' ,
        R s s' -> R t t' -> Compat (Apply s t) (Apply s' t')

    | C_Constant : ∀ v,
        Compat (Constant v) (Constant v)

    | C_Builtin : ∀ f,
        Compat (Builtin f) (Builtin f)

    | C_TyInst : ∀ t t' T,
        R t t' -> Compat (TyInst t T) (TyInst t' T)

    | C_Error : ∀ T,
        Compat (Error T) (Error T)

    | C_IWrap : ∀ T1 T2 t t',
        R t t' -> Compat (IWrap T1 T2 t) (IWrap T1 T2 t')

    | C_Unwrap : ∀ t t',
        R t t' -> Compat (Unwrap t) (Unwrap t')
  .

  Definition dec_binding  (b b' : binding) : bool :=
    match b, b' with
      | (TermBind s v t), (TermBind s' v' t') => strictness_eqb s s' && VDecl_eqb v v' && dec_R t t'
      | (TypeBind v T), (TypeBind v' T') => TVDecl_eqb v v'  && Ty_eqb T T'
      | (DatatypeBind d), (DatatypeBind d') => DTDecl_eqb d d'
      | _, _                               => false
    end
  .


  Definition dec (t t' : term) : bool :=
    match t, t' with
      | (Let r bs t), (Let r' bs' t')      => recursivity_eqb r r' && forall2b dec_binding bs bs' && dec_R t t'
      | (Var n), (Var n')                  => String.eqb n n'
      | (TyAbs n k t), (TyAbs n' k' t')    => String.eqb n n' && Kind_eqb k k' && dec_R t t'
      | (LamAbs n T t), (LamAbs n' T' t')  => String.eqb n n'&& Ty_eqb T T' && dec_R t t'
      | (Apply s t), (Apply s' t')         => dec_R s s' && dec_R t t'
      | (Constant c), (Constant c')        => constant_eqb c c'
      | (Builtin f), (Builtin f')          => func_eqb f f'
      | (TyInst t T), (TyInst t' T')       => Ty_eqb T T' && dec_R t t'
      | (Error T), (Error T')              => Ty_eqb T T'
      | (IWrap T1 T2 t), (IWrap T1' T2' t') => Ty_eqb T1 T1' && Ty_eqb T2 T2' && dec_R t t'
      | (Unwrap t), (Unwrap t')            => dec_R t t'
      | _, _                               => false
    end
    .

  Ltac split_hypos :=
    match goal with
    | H : (?x && ?y)%bool = true |- _ => apply andb_true_iff in H; destruct H; split_hypos
    | _ => idtac
    end.


  Lemma dec_Binding_Compat_Binding : ∀ b b',
      (∀ t t', dec_R t t' = true -> R t t') ->
      dec_binding b b' = true -> Compat_Binding b b'.
  Proof with eauto with reflection.
    intros b b' H_term_sound H_dec.
    destruct b, b'.
    all: simpl in H_dec; try discriminate H_dec.
    all: split_hypos.
    - assert (s = s0)...
      assert (v = v0)...
      subst.
      apply C_TermBind...
    - assert (t = t1)...
      assert (t0 = t2)...
      subst.
      apply C_TypeBind.
    - assert (d = d0)...
      subst.
      apply C_DatatypeBind.
  Defined.

  Lemma dec_Bindings_Compat_Bindings : ∀ bs bs',
      (∀ t t', dec_R t t' = true -> R t t') ->
      forall2b dec_binding bs bs' = true -> Compat_Bindings bs bs'.
  Proof with eauto.
    intros bs.
    induction bs.
    all: intros bs' H_term_sound H_dec.
    all: destruct bs'.
    all: simpl in H_dec.
    all: try discriminate H_dec.
    - apply Compat_Bindings_Nil.
    - split_hypos.
      apply Compat_Bindings_Cons.
      + apply dec_Binding_Compat_Binding...
      + eauto.
  Defined.

  Definition P_term t := forall t',
    (∀ t t', dec_R t t' = true -> R t t') ->
    dec t t' = true -> Compat t t'
  .
  Definition P_binding b := forall b',
    (∀ t t', dec_R t t' = true -> R t t') ->
    dec_binding b b' = true -> Compat_Binding b b'
  .

  Lemma sound_dec :
    forall t, P_term t.
  Proof with eauto with reflection.
    (* term__rect is definitely transparent *)
    apply term__rect with (P := P_term) (Q := P_binding).
    all:
      intros;
      unfold P_term;
      intros t' H_sound_R H_dec.
    all: destruct t'.
    all: simpl in H_dec.
    all: try discriminate H_dec.
    all: split_hypos.
    - apply H_sound_R in H1.
      apply recursivity_eqb_eq in H0.
      subst.
      eapply C_Let...
      apply dec_Bindings_Compat_Bindings...
    - apply String.eqb_eq in H_dec.
      subst.
      constructor.
    - assert (s = b)...
      assert (k = k0)...
      subst.
      eapply C_TyAbs...
    - assert (s = b)...
      assert (t = t1)...
      subst.
      apply C_LamAbs...
    - apply C_Apply...
    - assert (c = c0)...
      subst.
      apply C_Constant.
    - assert (d = d0)... subst.
      apply C_Builtin.
    - assert (t0 = t1)... subst.
      apply C_TyInst...
    - assert (t = t0)... subst.
      apply C_Error.
    - assert (t = t2)...
      assert (t0 = t3)...
      subst.
      apply C_IWrap...
    - apply C_Unwrap...
    - assert (s = s0)...
      assert (v = v0)...
      subst.
      apply C_TermBind...
    - assert (v = t)...
      assert (ty = t0)...
      subst.
      apply C_TypeBind...
    - assert (dtd = d)...
      subst.
      apply C_DatatypeBind.
  Defined.



(*
  Lemma sound_dec t t' :
    (∀ t t', dec_R t t' = true -> R t t') ->
    dec t t' = true -> Compat t t'.
  Proof with eauto with reflection.
    generalize t'.
    clear t'.
    intros t'.
    induction t.
    all: intros H_sound_R H_dec.
    all: destruct t'.
    all: simpl in H_dec.
    all: try discriminate H_dec.
    all: split_hypos.
    - apply H_sound_R in H0.
      apply recursivity_eqb_eq in H.
      subst.
      eapply C_Let...
      apply dec_Bindings_Compat_Bindings...
    - apply String.eqb_eq in H_dec.
      subst.
      constructor.
    - assert (b = b0)...
      assert (k = k0)...
      subst.
      eapply C_TyAbs...
    - assert (b = b0)...
      assert (t = t1)...
      subst.
      apply C_LamAbs...
    - apply C_Apply...
    - assert (c = c0)...
      subst.
      apply C_Constant.
    - assert (d = d0)... subst.
      apply C_Builtin.
    - assert (t0 = t1)... subst.
      apply C_TyInst...
    - assert (t = t0)... subst.
      apply C_Error.
    - assert (t = t2)...
      assert (t0 = t3)...
      subst.
      apply C_IWrap...
    - apply C_Unwrap...
  Defined.
*)
End Compatibility.


Section CompatConstrs.

Context {R : term -> term -> Prop}.

Definition c_TermBind : forall s s' v v' t t',
  s = s' ->
  v = v' ->
  R t t' -> Compat_Binding R (TermBind s v t) (TermBind s' v' t').
Proof.
intros; subst; auto using Compat_Binding.
Defined.


Definition c_TypeBind     : forall d d' T T',
  d = d' ->
  T = T' ->
  Compat_Binding R (TypeBind d T) (TypeBind d' T').
Proof.
intros; subst; auto using Compat_Binding.
Defined.

Definition c_DatatypeBind : forall d d',
  d = d' ->
  Compat_Binding R (DatatypeBind d) (DatatypeBind d').
Proof.
intros; subst; auto using Compat_Binding.
Defined.


Definition c_Let r r' bs bs' t t' :
  r = r' ->
  Compat_Bindings R bs bs'-> R t t' -> Compat R (Let r bs t) (Let r' bs' t').
Proof.
intros; subst; auto using Compat.
Defined.

Definition c_Var n n' :
  n = n' ->
  Compat R (Var n) (Var n').
Proof.
intros; subst; auto using Compat.
Defined.

Definition c_TyAbs : forall n n' k k' t t',
  n = n' ->
  k = k' ->
  R t t' -> Compat R (TyAbs n k t) (TyAbs n' k' t')
.
Proof.
intros; subst; auto using Compat.
Defined.

Definition c_LamAbs : forall n n' T T' t t' ,
  n = n' ->
  T = T' ->
  R t t' -> Compat R (LamAbs n T t) (LamAbs n' T' t').
Proof.
intros; subst; auto using Compat.
Defined.

Definition c_Apply : forall s s' t t' ,
  R s s' -> R t t' -> Compat R (Apply s t) (Apply s' t') := C_Apply R.

Definition c_Constant : forall v v',
  v = v' ->
  Compat R (Constant v) (Constant v').
Proof.
intros; subst; auto using Compat.
Defined.

Definition c_Builtin : forall f f',
  f = f' ->
  Compat R (Builtin f) (Builtin f').
Proof.
intros; subst; auto using Compat.
Defined.

Definition c_TyInst : forall t t' T T',
  T = T' ->
  R t t' -> Compat R (TyInst t T) (TyInst t' T').
Proof.
intros; subst; auto using Compat.
Defined.

Definition c_Error : forall T T',
  T = T' ->
  Compat R (Error T) (Error T').
Proof.
intros; subst; auto using Compat.
Defined.

Definition c_IWrap : forall T1 T1' T2 T2' t t',
  T1 = T1' ->
  T2 = T2' ->
  R t t' -> Compat R (IWrap T1 T2 t) (IWrap T1' T2' t').
Proof.
intros; subst; auto using Compat.
Defined.

Definition c_Unwrap : forall t t',
  R t t' -> Compat R (Unwrap t) (Unwrap t').
Proof.
intros; subst; auto using Compat.
Defined.



End CompatConstrs.

Create HintDb compat.

#[export] Hint Resolve
c_TermBind
c_TypeBind
c_DatatypeBind
c_Let
c_Var
c_TyAbs
c_LamAbs
c_Apply
c_Constant
c_Builtin
c_TyInst
c_Error
c_IWrap
c_Unwrap
: compat.
