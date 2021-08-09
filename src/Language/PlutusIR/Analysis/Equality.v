Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Lists.List.
Require Import Ascii.
Require Import Eqdep.
Set Implicit Arguments.

From PlutusCert Require Import Language.PlutusIR.

Definition EqDec := fun A : Type => forall x y : A, {x = y} + {x <> y}.


Create HintDb Eqs.
Hint Resolve Nat.eq_dec ascii_dec bool_dec string_dec list_eq_dec : Eqs.

Ltac solveEq :=
  intros;
  unfold EqDec;
  decide equality; auto with Eqs. (* debug auto with Eqs.*)

Definition unit_dec: EqDec unit. Proof. solveEq. Defined.
  Hint Resolve unit_dec : Eqs.

Definition Strictness_dec: EqDec Strictness. solveEq. Defined.
  Hint Resolve Strictness_dec : Eqs.

Definition Ty_dec: EqDec Ty. solveEq. Defined.
  Hint Resolve Ty_dec : Eqs.

Definition VDecl_dec: EqDec VDecl. Proof. solveEq. Defined.
  Hint Resolve VDecl_dec : Eqs.

Definition TVDecl_dec : EqDec TVDecl. Proof. solveEq. Defined.
  Hint Resolve TVDecl_dec : Eqs.

Definition constructor_dec : EqDec constructor. Proof. solveEq. Defined.
  Hint Resolve constructor_dec : Eqs.

Definition DTDecl_dec: EqDec DTDecl. Proof. solveEq. Defined.
  Hint Resolve DTDecl_dec : Eqs.

Definition Recursivity_dec : EqDec Recursivity. Proof. solveEq. Defined.
  Hint Resolve Recursivity_dec : Eqs.

Definition func_dec : EqDec func. Proof. solveEq. Defined.
  Hint Resolve func_dec: Eqs.

Definition Kind_dec : EqDec Kind. Proof. solveEq. Defined.
  Hint Resolve Kind_dec : Eqs.

Definition DefaultUni_dec : EqDec DefaultUni. solveEq. Defined.
  Hint Resolve DefaultUni_dec : Eqs.

Definition uniType_dec : forall t, EqDec (uniType t). intro t. destruct t; simpl; solveEq. Defined.
  Hint Resolve uniType_dec : Eqs.

Definition valueOf_dec : forall t, EqDec (valueOf t). solveEq. apply uniType_dec. Defined.
  Hint Resolve valueOf_dec : Eqs.

(* Somewhat cumbersome, cannot use "decide equality" tactic *)
Definition some_dec: forall (x y : some), {x = y} + {x <> y}.
Proof.
  intros x y.
  refine (
    match x, y with | @Some u  v, @Some u' v' =>
    match DefaultUni_dec u u' with
    | left eq   => _
    | right neq => _
    end end
  ).
  - subst. destruct (valueOf_dec v v').
    + apply left. congruence.
    + apply right. intros H.
      inversion H .
      inversion_sigma.
      unfold eq_rect in H2.
      assert (H3 : H0 = eq_refl). { apply UIP_refl. } (* I need UIP to reduce eq_rect and finish the proof, can this be done without? *)
      rewrite H3 in H2.
      contradiction.
  - apply right. intros H.
    inversion H. contradiction.
Defined.
  Hint Resolve some_dec : Eqs.

Lemma Term_dec : forall (x y : Term), {x = y} + {x <> y}
  with binding_dec: forall (x y : Binding), {x = y} + {x <> y}.
Proof.
  - solveEq.
  - solveEq.
Defined.



(* boolean equality
I define this separately from the dec_* functions to avoid carrying around
proof terms at run-time.
*)

(*
  TODO: do this cleanly with HasEqb/HasEqBool/HasEq
  https://coq.inria.fr/library/Coq.Structures.Equalities.html
*)

Create HintDb reflection.

(*
  Note [Hints and name-collision]
  ~~~~~~~~~~~~~~~~

  When adding Nat.eqb_eq to a hint database using "Hint Resolve ->", Coq
  generates a definition eqb_eq_l2r (note: not qualified by module name
  anymore). The same happens when adding String.eqb_eq, thus causing a naming
  conflict.
  Current work-around is to alias the imported functions.
*)
(* Note [Hints and name-collision] *)
Definition nat_eqb_eq := Nat.eqb_eq.
Definition string_eqb_eq := String.eqb_eq.
Hint Resolve ->
  andb_true_iff
  nat_eqb_eq
  string_eqb_eq
  Ascii.eqb_eq
  Bool.eqb_true_iff
: reflection.

Hint Resolve <-
  andb_true_iff
  nat_eqb_eq
  string_eqb_eq
  Ascii.eqb_eq
  Bool.eqb_true_iff
: reflection.
Definition andb_and : forall s t, s && t = true -> s = true /\ t = true.
Proof. auto with reflection. Qed.

Ltac rewrite_eqbs := repeat (
  match goal with
  | Hyp : _ |- _ => apply andb_and in Hyp
  end).

(* Destruct all /\ hypotheses*)
Ltac destruct_ands := repeat (
  match goal with
  | Hyp : ?l /\ ?r |- _ => destruct Hyp
  end).

Ltac bool_assumptions :=
  repeat (rewrite_eqbs; destruct_ands).

Ltac eqb_eq_tac :=
  intros x y;
  constructor; (* <-> *)

  (* -> case*)
  [ generalize y; clear y; induction x; intros y; (* get suitable IH *)
    destruct y;
    intros H;
    repeat (rewrite_eqbs; destruct_ands); (* unfolds the call and rewrites && into /\*)
    (f_equal || inversion H); (* Eliminate cases based on H, f_equal on same constructors*)
    eauto with reflection

  (* <- case *)
  | intros H;
    subst x;
    induction y;
    simpl;
    eauto with reflection
  ].


Definition Eqb x := x -> x -> bool.
Definition Eqb_eq := fun {a} (eqb : Eqb a) => forall (x y : a),
  eqb x y = true <-> x = y.

Definition unit_eqb: Eqb unit := fun x y => match x, y with
  | tt, tt => true
  end.
Definition unit_eqb_eq : Eqb_eq unit_eqb.
   Proof. eqb_eq_tac. Defined.

Hint Resolve -> unit_eqb_eq : reflection.
Hint Resolve <- unit_eqb_eq : reflection.




Definition Strictness_eqb: Eqb Strictness := fun x y =>
  match x, y with
  | NonStrict, NonStrict => true
  | Strict   , Strict    => true
  | _, _                 => false
  end.

Definition Strictness_eqb_eq : Eqb_eq Strictness_eqb.
Proof. eqb_eq_tac. Defined.
Hint Resolve -> Strictness_eqb_eq : reflection.
Hint Resolve <- Strictness_eqb_eq : reflection.

Definition TVDecl_eqb : Eqb TVDecl := fun x y => match x, y with
  | TyVarDecl ty k, TyVarDecl ty' k' => String.eqb ty ty' && unit_eqb k k'
  end.

Definition TVDecl_eqb_eq : Eqb_eq TVDecl_eqb.
Proof. eqb_eq_tac. Defined.
Hint Resolve -> TVDecl_eqb_eq : reflection.
Hint Resolve <- TVDecl_eqb_eq : reflection.




Definition Ty_eqb: Eqb Ty := unit_eqb.

Definition Ty_eqb_eq : Eqb_eq Ty_eqb.
Proof. eqb_eq_tac. Defined.

Hint Resolve -> Ty_eqb_eq : reflection.
Hint Resolve <- Ty_eqb_eq : reflection.

Definition VDecl_eqb: Eqb VDecl := String.eqb.
Definition VDecl_eqb_eq : Eqb_eq VDecl_eqb := String.eqb_eq.
Hint Resolve -> VDecl_eqb_eq : reflection.
Hint Resolve <- VDecl_eqb_eq : reflection.
(* reminder: String.eqb_eq is opaque, perhaps this will be an
issue later on*)



Definition constructor_eqb : Eqb constructor := fun x y => match x, y with
  | Constructor c n, Constructor c' n' => String.eqb c c' && Nat.eqb n n'
  end.

Definition constructor_eqb_eq : Eqb_eq constructor_eqb.
Proof. eqb_eq_tac. Qed.
Hint Resolve -> constructor_eqb_eq : reflection.
Hint Resolve <- constructor_eqb_eq : reflection.

Definition list_eqb a (eqb : Eqb a) : Eqb (list a) := fix f xs ys :=
  match xs, ys with
  | nil, nil             => true
  | cons x xs, cons y ys => eqb x y && f xs ys
  | _, _                 => false
  end.

Definition list_eqb_eq a (a_eqb : Eqb a) (a_eqb_eq : Eqb_eq a_eqb) : Eqb_eq (list_eqb a_eqb).
Proof.
  eqb_eq_tac.
  (* -> case for:  (x : a) = (y : a) *)
  - apply a_eqb_eq; assumption.
  (* <- case for: a_eqb ... && list_eqb ... = true *)
  - unfold Eqb, Eqb_eq in *.
    apply andb_true_iff_proj_r2l.
    constructor.
    + apply a_eqb_eq.
      reflexivity.
    + assumption.
Qed.

Hint Resolve -> list_eqb_eq : reflection.
Hint Resolve <- list_eqb_eq : reflection.

Definition DTDecl_eqb: Eqb DTDecl := fun x y => match x, y with
  | Datatype tvd tvds n cs, Datatype tvd' tvds' n' cs' =>
    TVDecl_eqb tvd tvd' && list_eqb TVDecl_eqb tvds tvds'
      && String.eqb n n' && list_eqb constructor_eqb cs cs'
    end.
Definition DTDecl_eqb_eq : Eqb_eq DTDecl_eqb.

Proof.
  eqb_eq_tac.
  - apply (list_eqb_eq TVDecl_eqb_eq).
    assumption.
  - apply (list_eqb_eq constructor_eqb_eq).
    assumption.
  - repeat (apply andb_true_iff_proj_r2l; constructor);
     auto with reflection.
    + apply (list_eqb_eq TVDecl_eqb_eq).
      reflexivity.
    + apply (list_eqb_eq constructor_eqb_eq).
      reflexivity.
Qed.
Hint Resolve -> DTDecl_eqb_eq : reflection.
Hint Resolve <- DTDecl_eqb_eq : reflection.



Definition Recursivity_eqb : Eqb Recursivity := fun x y => match x, y with
  | NonRec, NonRec => true
  | Rec, Rec => true
  | _, _ => false
  end.

Definition Recursivity_eqb_eq : Eqb_eq Recursivity_eqb.
Proof. eqb_eq_tac. Qed.
Hint Resolve -> Recursivity_eqb_eq : reflection.
Hint Resolve <- Recursivity_eqb_eq : reflection.

Definition func_eqb : Eqb func := fun x y => match x, y with
  | AddInteger , AddInteger => true
  | SubtractInteger , SubtractInteger => true
  | MultiplyInteger , MultiplyInteger => true
  | DivideInteger , DivideInteger => true
  | QuotientInteger , QuotientInteger => true
  | RemainderInteger , RemainderInteger => true
  | ModInteger , ModInteger => true
  | LessThanInteger , LessThanInteger => true
  | LessThanEqInteger , LessThanEqInteger => true
  | GreaterThanInteger , GreaterThanInteger => true
  | GreaterThanEqInteger , GreaterThanEqInteger => true
  | EqInteger , EqInteger => true
  | Concatenate , Concatenate => true
  | TakeByteString , TakeByteString => true
  | DropByteString , DropByteString => true
  | SHA2 , SHA2 => true
  | SHA3 , SHA3 => true
  | VerifySignature , VerifySignature => true
  | EqByteString , EqByteString => true
  | LtByteString , LtByteString => true
  | GtByteString , GtByteString => true
  | IfThenElse , IfThenElse => true
  | CharToString , CharToString => true
  | Append , Append => true
  | Trace , Trace => true
  | _, _ => false
  end.

Definition func_eqb_eq : Eqb_eq func_eqb.
Proof. eqb_eq_tac. Qed.
Hint Resolve -> func_eqb_eq : reflection.
Hint Resolve <- func_eqb_eq : reflection.

Definition Kind_eqb : Eqb Kind := unit_eqb.
Definition Kind_eqb_eq : Eqb_eq Kind_eqb.
Proof. eqb_eq_tac. Qed.
Hint Resolve -> Kind_eqb_eq : reflection.
Hint Resolve <- Kind_eqb_eq : reflection.


Definition DefaultUni_eqb : Eqb DefaultUni := fun x y => match x, y with
  | DefaultUniInteger , DefaultUniInteger => true
  | DefaultUniByteString , DefaultUniByteString => true
  | DefaultUniString , DefaultUniString => true
  | DefaultUniChar , DefaultUniChar => true
  | DefaultUniUnit , DefaultUniUnit => true
  | DefaultUniBool , DefaultUniBool => true
  | _, _ => false
  end.

Definition DefaultUni_eqb_eq : Eqb_eq DefaultUni_eqb.
Proof. eqb_eq_tac. Qed.
Hint Resolve -> DefaultUni_eqb_eq : reflection.
Hint Resolve <- DefaultUni_eqb_eq : reflection.

Definition uniType_eqb : forall t, Eqb (uniType t) := fun ty =>
  match ty return Eqb (uniType ty) with
  | DefaultUniInteger => Nat.eqb
  | DefaultUniChar    => Strings.Ascii.eqb
  | DefaultUniUnit    => unit_eqb
  | DefaultUniBool    => Bool.eqb
  | DefaultUniByteString => String.eqb
  | DefaultUniString    => String.eqb
  end.

Definition uniType_eqb_eq : forall t, Eqb_eq (uniType_eqb t).
Proof.
  intro t.
  destruct t;
  unfold Eqb_eq;
  auto using string_eqb_eq, unit_eqb_eq, Ascii.eqb_eq, Nat.eqb_eq, Bool.eqb_true_iff.
Qed.

Hint Resolve -> uniType_eqb_eq : reflection.
Hint Resolve <- uniType_eqb_eq : reflection.

Definition valueOf_eqb : forall t, Eqb (valueOf t) := fun ty x y => match x, y with
  | ValueOf _ x, ValueOf _ y => uniType_eqb ty x y
  end.

Definition valueOf_eqb_eq : forall t, Eqb_eq (@valueOf_eqb t).
Proof.
  intros t.
  destruct t;
  eqb_eq_tac.
Qed.
Hint Resolve -> valueOf_eqb_eq : reflection.
Hint Resolve <- valueOf_eqb_eq : reflection.

Definition some_eqb: Eqb some := fun x y => match x, y with
  | @Some t v, @Some t' v' =>
    match DefaultUni_dec t t' with
    | left H => valueOf_eqb (eq_rect _ valueOf v _ H) v'
    | _      => false
    end
  end.

Definition some_eqb_eq : Eqb_eq (some_eqb).
Proof.
  eqb_eq_tac.
  - destruct u, u0;
    simpl in *;
    f_equal;
    inversion H;
    auto with reflection.
  - destruct u;
    simpl;
    destruct v; simpl;
    auto with reflection.
Qed.
Hint Resolve -> some_eqb_eq : reflection.
Hint Resolve <- some_eqb_eq : reflection.

Fixpoint Term_eqb (x y : Term) {struct x} : bool := match x, y with
  | Let rec bs t, Let rec' bs' t' => Recursivity_eqb rec rec'
      && list_eqb Binding_eqb bs bs'
        && Term_eqb t t'
  | Var n, Var n' => String.eqb n n'
  | TyAbs n k t, TyAbs n' k' t' => String.eqb n n' && Kind_eqb k k' && Term_eqb t t'
  | LamAbs n ty t, LamAbs n' ty' t' => String.eqb n n' && Ty_eqb ty ty' && Term_eqb t t'
  | Apply s t, Apply s' t' => Term_eqb s s' && Term_eqb t t'
  | Constant c, Constant c' => some_eqb c c'
  | Builtin f, Builtin f' => func_eqb f f'
  | TyInst t ty, TyInst t' ty' => Term_eqb t t' && Ty_eqb ty ty'
  | Error ty , Error ty' => Ty_eqb ty ty'
  | IWrap ty1 ty2 t, IWrap ty1' ty2' t' => Ty_eqb ty1 ty1' && Ty_eqb ty2 ty2' && Term_eqb t t'
  | Unwrap t, Unwrap t' => Term_eqb t t'
  | _, _ => false
  end
with Binding_eqb (x y : Binding) {struct x} : bool := match x, y with
  | TermBind s vd t, TermBind s' vd' t' => Strictness_eqb s s' && VDecl_eqb vd vd' && Term_eqb t t'
  | TypeBind tvd ty, TypeBind tvd' ty' => TVDecl_eqb tvd tvd' && Ty_eqb ty ty'
  | DatatypeBind  dtd, DatatypeBind dtd' => DTDecl_eqb dtd dtd'
  | _, _ => false
  end
  .
