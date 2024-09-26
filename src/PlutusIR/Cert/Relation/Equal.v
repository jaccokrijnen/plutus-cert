Require Import
  Bool.Bool.

From PlutusCert Require Import
  PlutusIR
  Cert.Relation.Types
  Analysis.Equality

  Util.List
.

(* This is a notation, since a new definition cannot be used properly with
** rewrite.
*)
Notation beq_eq T eqb := (forall (x y : T), eqb x y = true <-> x = y).

Create HintDb reflect_eq.

(* This has to replace definitions in Analysis.Equality *)
Scheme Boolean Equality for ty.
Axiom ty_beq_eq : beq_eq ty ty_beq.
Hint Rewrite ty_beq_eq : reflect_eq.
Hint Resolve ty_beq_eq : reflect_eq.


Scheme Boolean Equality for recursivity.
Axiom recursivity_beq_eq : beq_eq recursivity recursivity_beq.
Hint Rewrite recursivity_beq_eq: reflect_eq.
Hint Resolve recursivity_beq_eq: reflect_eq.

Scheme Boolean Equality for kind.
Axiom kind_beq_eq : beq_eq kind kind_beq.
Hint Rewrite kind_beq_eq : reflect_eq.
Hint Resolve kind_beq_eq : reflect_eq.

Scheme Boolean Equality for DefaultFun.
Axiom DefaultFun_beq_eq : beq_eq DefaultFun DefaultFun_beq.
Hint Rewrite DefaultFun_beq_eq : reflect_eq.
Hint Resolve DefaultFun_beq_eq : reflect_eq.

Scheme Boolean Equality for strictness.
Axiom strictness_beq_eq : beq_eq strictness strictness_beq.
Hint Rewrite strictness_beq_eq : reflect_eq.
Hint Resolve strictness_beq_eq : reflect_eq.

Scheme Boolean Equality for tvdecl.
Axiom tvdecl_beq_eq : beq_eq tvdecl tvdecl_beq.
Hint Rewrite tvdecl_beq_eq : reflect_eq.
Hint Resolve tvdecl_beq_eq : reflect_eq.

Scheme Boolean Equality for vdecl.
Axiom vdecl_beq_eq : beq_eq vdecl vdecl_beq.
Hint Rewrite vdecl_beq_eq : reflect_eq.
Hint Resolve vdecl_beq_eq : reflect_eq.

Scheme Boolean Equality for DefaultUni.
Axiom DefaultUni_beq_eq : beq_eq DefaultUni DefaultUni_beq.
Hint Rewrite DefaultUni_beq_eq : reflect_eq.
Hint Resolve DefaultUni_beq_eq : reflect_eq.

(*
the Scheme command is limited, we need manual definitions below

e.g.

Scheme Boolean Equality for dtdecl

> Unsupported constructor with an argument whose type is a non-parametric
> inductive type. Type
> "list" is applied to an argument which is not a variable.

*)


Definition dtdecl_beq : dtdecl -> dtdecl -> bool := fun x y => match x, y with
  | Datatype tvd tvds n cs, Datatype tvd' tvds' n' cs' =>
    TVDecl_eqb tvd tvd' && forall2b TVDecl_eqb tvds tvds'
      && String.eqb n n' && forall2b VDecl_eqb cs cs'
    end
.
Axiom dtdecl_beq_eq : beq_eq dtdecl dtdecl_beq.
Hint Rewrite dtdecl_beq_eq : reflect_eq.
Hint Resolve dtdecl_beq_eq : reflect_eq.

Definition constant_beq : constant -> constant -> bool := fun x y => match x, y with
  | ValueOf T v, ValueOf T' v' =>
    match DefaultUni_dec T T' with
    | left H => uniType_eqb T' (eq_rect _ _ v _ H) v'
    | _      => false
    end
  end.
Axiom constant_beq_eq : beq_eq constant constant_beq.
Hint Rewrite constant_beq_eq : reflect_eq.
Hint Resolve constant_beq_eq : reflect_eq.

Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.
Definition string_beq_stub : string -> string -> bool := String.eqb.

Function term_beq (x y : term) {struct x} : bool := match x, y with
  | (Let r bs t), (Let r' bs' t')      => recursivity_beq r r' && forall2b binding_beq bs bs' && term_beq t t'
  | (TyInst t T), (TyInst t' T')       => ty_beq T T' && term_beq t t'
  | (Var n), (Var n')                  => string_beq_stub n n'
  | (TyAbs n k t), (TyAbs n' k' t')    => string_beq_stub n n' && kind_beq k k' && term_beq t t'
  | (LamAbs n T t), (LamAbs n' T' t')  => string_beq_stub n n'&& ty_beq T T' && term_beq t t'
  | (Apply s t), (Apply s' t')         => term_beq s s' && term_beq t t'
  | (Constant c), (Constant c')        => constant_beq c c'
  | (Builtin f), (Builtin f')          => DefaultFun_beq f f'
  | (Error T), (Error T')              => ty_beq T T'
  | (IWrap T1 T2 t), (IWrap T1' T2' t') => ty_beq T1 T1' && ty_beq T2 T2' && term_beq t t'
  | (Unwrap t), (Unwrap t')            => term_beq t t'
  | (Constr n ts), (Constr n' ts')     => Nat.eqb n n' && forall2b term_beq ts ts'
  | (Case t ts), (Case t' ts')         => term_beq t t' && forall2b term_beq ts ts'

  | (Let r bs t), _ => false
  | (TyInst t T), _ => false
  | (Var n), _ => false
  | (TyAbs n k t), _ => false
  | (LamAbs n T t), _ => false
  | (Apply s t), _ => false
  | (Constant c), _ => false
  | (Builtin f), _ => false
  | (Error T), _ => false
  | (IWrap T1 T2 t), _ => false
  | (Unwrap t), _ => false
  | (Constr n ts), _ => false
  | (Case t ts), _ => false
  end
with
   binding_beq  (b b' : binding) : bool :=
    match b, b' with
      | (TermBind s v t), (TermBind s' v' t') => strictness_beq s s' && vdecl_beq v v' && term_beq t t'
      | (TypeBind v T), (TypeBind v' T') => tvdecl_beq v v'  && ty_beq T T'
      | (DatatypeBind d), (DatatypeBind d') => dtdecl_beq d d'
      | (TermBind s v t), _ => false
      | (TypeBind v T), _ => false
      | (DatatypeBind d), _ => false
    end
  .

Definition P_term t := forall t', term_beq t t' = true <-> t = t'.
Definition P_binding b := forall b', binding_beq b b' = true <-> b = b'.
Definition P_bindings bs := forall bs', forall2b binding_beq bs bs' = true <-> bs = bs'.


(*
proof by reflection approach

1. Rewrite with ..._equation (either generated by Function or handwritten)
2. simplify .. && .. && .. = true to
      .. = true /\ .. = true /\ ...
3. Use tactic to replace known equivalences to
      PA        /\ PB       /\ ...
4. Use autorewrite with hint db and inductive hypotheses
*)

Axiom eq_Apply : forall s s' t t', s = s' /\ t = t' <-> Apply s t = Apply s' t'.
Axiom eq_Let : forall r r' bs bs' t t', r = r' /\ bs = bs' /\ t = t' <-> Let r bs t = Let r' bs' t'.
Axiom eq_Var : forall v v', v = v' <-> Var v = Var v'.
Axiom eq_TyAbs : forall v v' k k' t t', v = v' /\ k = k' /\ t = t' <-> TyAbs v k t = TyAbs v' k' t'.
Axiom eq_LamAbs : forall v v' ty ty' t t', v = v' /\ ty = ty' /\ t = t' <-> LamAbs v ty t = LamAbs v' ty' t'.
Axiom eq_Constant : forall c c', c = c' <-> Constant c = Constant c'.
Axiom eq_Builtin : forall f f', f = f' <-> Builtin f = Builtin f'.
Axiom eq_TyInst : forall t t' ty ty', t = t' /\ ty = ty' <-> TyInst t ty = TyInst t' ty'.
Axiom eq_Error : forall ty ty', ty = ty' <-> Error ty = Error ty'.
Axiom eq_IWrap : forall ty1 ty1' ty2 ty2' t t', ty1 = ty1' /\ ty2 = ty2' /\ t = t' <-> IWrap ty1 ty2 t = IWrap ty1' ty2' t'.
Axiom eq_Unwrap : forall t t', t = t' <-> Unwrap t = Unwrap t'.
Axiom eq_Constr : forall i i' ts ts', i = i' /\ ts = ts' <-> Constr i ts = Constr i' ts'.
Axiom eq_Case : forall t t' ts ts', t = t' /\ ts = ts' <-> Case t ts = Case t' ts'.

Create HintDb term_eq.
Hint Rewrite <-
eq_Apply
eq_Let
eq_Var
eq_TyAbs
eq_LamAbs
eq_Constant
eq_Builtin
eq_TyInst
eq_Error
eq_IWrap
eq_Unwrap
eq_Constr
eq_Case
: term_eq .


Axiom beq_eq__refl : forall T beq, beq_eq T beq -> forall x, beq x x = true.

Axiom beq_eq__forall2b : forall T f,
  beq_eq T f ->
  beq_eq (list T) (forall2b f).
Hint Resolve beq_eq__forall2b : reflect_eq.

From PlutusCert Require Import Util.Tactics.

Axiom and_iff : forall P P' Q Q', ((P /\ P') <-> (Q /\ Q')) <-> ((P <-> Q) /\ (P' <-> Q')).

(* Split conjunction of iffs *)
Ltac split_goal :=
  match goal with
    | |- _ /\ _ => split; [ | split_goal]
    | |- _ <-> _ => idtac
  end.

Lemma term_beq_eq : forall t, P_term t.
Proof.
apply term_rect' with (P := P_term) (Q := P_binding) (R := P_bindings).
  + intros.
    unfold P_term, P_binding in *.
    intro t'.
    destruct t'.
    - (* equal *)
      (* LHS *)
      rewrite term_beq_equation.
      repeat rewrite andb_true_iff .
      repeat rewrite and_assoc.
      (* RHS *)
      autorewrite with term_eq.

      repeat rewrite and_iff.
      split_goal; auto with reflect_eq.
    - simpl.
      split; inversion 1.

Admitted.

Definition rd_equal : rel_decidable :=
  {| rd_rel := (@eq term)
  ;  rd_decb := term_beq
  ;  rd_equiv := term_beq_eq
  |}
.
