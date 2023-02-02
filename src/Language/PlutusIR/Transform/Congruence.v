From PlutusCert Require Import
  Language.PlutusIR
  Language.PlutusIR.Analysis.Equality
  Util.List.

From Equations Require Import
  Equations.

From Coq Require Import
  Bool
  Strings.String
  Lists.List
  Utf8
  .

Generalizable All Variables.
Set Implicit Arguments.

Section Congruence.
  Import NamedTerm.

  Context
    (R : Term -> Term -> Type)
    (dec_R : Term -> Term -> bool)
  .

  Inductive Cong_Binding : Binding -> Binding -> Type :=
    | C_TermBind     : `{ R t t' -> Cong_Binding (TermBind s v t)
                                                 (TermBind s v t')}

    | C_TypeBind     : `{           Cong_Binding (TypeBind d T)
                                                 (TypeBind d T) }
    | C_DatatypeBind : `{           Cong_Binding (DatatypeBind d)
                                                   (DatatypeBind d) }
    .
  Inductive Cong_Bindings : list Binding -> list Binding -> Type :=
    | Cong_Bindings_Cons : forall {b b' bs bs'}, Cong_Binding b b' -> Cong_Bindings bs bs' -> Cong_Bindings (b :: bs) (b' :: bs')
    | Cong_Bindings_Nil  : Cong_Bindings nil nil.

  Inductive Cong : Term -> Term -> Type :=
    | C_Let      : `{ Cong_Bindings bs bs' -> R t t'    -> Cong (Let r bs t)
                                                                (Let r bs' t')}
    | C_Var      : `{                          Cong (Var n)
                                                    (Var n) }
    | C_TyAbs    : `{ R t t'                -> Cong (TyAbs n k t)
                                                    (TyAbs n k t') }
    | C_LamAbs   : `{ R t t' ->                Cong (LamAbs n T t)
                                                    (LamAbs n T t') }
    | C_Apply    : `{ R s s' -> R t t'      -> Cong (Apply s t)
                                                    (Apply s' t')}
    | C_Constant : `{                          Cong (Constant v)
                                                    (Constant v) }
    | C_Builtin  : `{                          Cong (Builtin f)
                                                    (Builtin f)}
    | C_TyInst   : `{ R t t'                -> Cong (TyInst t T)
                                                    (TyInst t' T)}
    | C_Error    : `{                          Cong (Error T)
                                                    (Error T)}
    | C_IWrap    : `{ R t t'                -> Cong (IWrap T1 T2 t)
                                                    (IWrap T1 T2 t') }
    | C_Unwrap   : `{ R t t'                -> Cong (Unwrap t)
                                                    (Unwrap t')}
  .

    Definition is_cong_binding  (b b' : Binding) : bool :=
      match b, b' with
        | (TermBind s v t), (TermBind s' v' t') => Strictness_eqb s s' && VDecl_eqb v v' && dec_R t t'
        | (TypeBind v T), (TypeBind v' T') => TVDecl_eqb v v'  && Ty_eqb T T'
        | (DatatypeBind d), (DatatypeBind d') => DTDecl_eqb d d'
        | _, _                               => false
      end
    .

    Definition is_cong (t t' : Term) : bool :=
      match t, t' with
        | (Let r bs t), (Let r' bs' t')      => Recursivity_eqb r r' && forall2b is_cong_binding bs bs' && dec_R t t'
        | (Var n), (Var n')                  => String.eqb n n'
        | (TyAbs n k t), (TyAbs n' k' t')    => String.eqb n n' && Kind_eqb k k' && dec_R t t'
        | (LamAbs n T t), (LamAbs n' T' t')  => String.eqb n n'&& Ty_eqb T T' && dec_R t t'
        | (Apply s t), (Apply s' t')         => dec_R s s' && dec_R t t'
        | (Constant v), (Constant v')        => some_valueOf_eqb v v'
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

    Axiom (String_eqb_eq       : ∀ x y, String.eqb x y = true -> x = y).
    Axiom (Recursivity_eqb_eq  : ∀ x y, Recursivity_eqb x y = true -> x = y).
    Axiom (Strictness_eqb_eq   : ∀ x y, Strictness_eqb x y = true -> x = y).
    Axiom (Kind_eqb_eq         : ∀ x y, Kind_eqb x y = true -> x = y).
    Axiom (Ty_eqb_eq           : ∀ x y, Ty_eqb x y = true -> x = y).
    Axiom (some_valueOf_eqb_eq : ∀ x y, some_valueOf_eqb x y = true -> x = y).
    Axiom (func_eqb_eq         : ∀ x y, func_eqb x y = true -> x = y).
    Axiom (VDecl_eqb_eq        : ∀ x y, VDecl_eqb x y = true -> x = y).
    Axiom (TVDecl_eqb_eq       : ∀ x y, TVDecl_eqb x y = true -> x = y).
    Axiom (DTDecl_eqb_eq       : ∀ x y, DTDecl_eqb x y = true -> x = y).

    Create HintDb Hints_soundness.
    Hint Resolve
      String_eqb_eq
      Recursivity_eqb_eq
      Strictness_eqb_eq
      Kind_eqb_eq
      Ty_eqb_eq
      some_valueOf_eqb_eq
      func_eqb_eq
      VDecl_eqb_eq
      TVDecl_eqb_eq
      DTDecl_eqb_eq
    : Hints_soundness.



    Lemma is_cong_Binding_Cong_Binding : ∀ b b',
        (∀ t t', dec_R t t' = true -> R t t') ->
        is_cong_binding b b' = true -> Cong_Binding b b'.
    Proof with eauto with Hints_soundness.
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
    Qed.

    Lemma is_cong_Bindings_Cong_Bindings : ∀ bs bs',
        (∀ t t', dec_R t t' = true -> R t t') ->
        forall2b is_cong_binding bs bs' = true -> Cong_Bindings bs bs'.
    Proof with eauto.
      intros bs.
      induction bs.
      all: intros bs' H_term_sound H_dec.
      all: destruct bs'.
      all: simpl in H_dec.
      all: try discriminate H_dec.
      - apply Cong_Bindings_Nil.
      - split_hypos.
        apply Cong_Bindings_Cons.
        + apply is_cong_Binding_Cong_Binding...
        + eauto.
    Qed.

    Lemma is_cong_Cong t t' :
      (∀ t t', dec_R t t' = true -> R t t') ->
      is_cong t t' = true -> Cong t t'.
    Proof with eauto with Hints_soundness.
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
        apply Recursivity_eqb_eq in H.
        subst.
        eapply C_Let...
        apply is_cong_Bindings_Cong_Bindings...
      - apply String.eqb_eq in H_dec.
        subst.
        constructor.
      - assert (b = s)...
        assert (k = k0)...
        subst.
        eapply C_TyAbs...
      - assert (b = s)...
        assert (t = t1)...
        subst.
        apply C_LamAbs...
      - apply C_Apply...
      - assert (s = s0)...
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
    Qed.




    (* Constructors with explicit equalities for indices *)
    Definition C_TermBind'     : forall t t' s s' v v' , s = s' -> v = v' -> R t t' -> Cong_Binding
                                    (TermBind s  v t)
                                    (TermBind s' v' t').
    Proof. intros. subst. apply C_TermBind. assumption. Qed.

    Definition C_TypeBind' : forall d d' ty ty',
      d = d' ->
      ty = ty' ->
      Cong_Binding (TypeBind d ty)
      (TypeBind d' ty').
    Proof. intros. subst. constructor. Qed.

    Definition C_DatatypeBind' : forall d d', d = d' -> Cong_Binding (DatatypeBind d)
                                                   (DatatypeBind d').
    Proof. intros. subst. constructor. Qed.

  Notation "'Nothing'" := None.
  Notation "'Just'"    := Datatypes.Some.

End Congruence.
