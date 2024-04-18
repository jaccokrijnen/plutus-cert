Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Lists.List.
Require Import Ascii.
Require Import Eqdep.

From PlutusCert Require Import
  PlutusIR
  Util.List
.

Import NamedTerm.
Set Implicit Arguments.

Definition EqDec := fun A : Type => forall x y : A, {x = y} + {x <> y}.


Create HintDb Eqs.
#[export] Hint Resolve Nat.eq_dec Z.eq_dec ascii_dec bool_dec string_dec list_eq_dec : Eqs.

Ltac solveEq :=
  intros;
  unfold EqDec;
  decide equality; auto with Eqs. (* debug auto with Eqs.*)

Definition unit_dec: EqDec unit. Proof. solveEq. Defined.
  #[export] Hint Resolve unit_dec : Eqs.

Definition Strictness_dec: EqDec Strictness. solveEq. Defined.
  #[export] Hint Resolve Strictness_dec : Eqs.

  Definition Recursivity_dec : EqDec Recursivity. Proof. solveEq. Defined.
  #[export] Hint Resolve Recursivity_dec : Eqs.

Definition func_dec : EqDec DefaultFun. Proof. solveEq. Defined.
  #[export] Hint Resolve func_dec: Eqs.

Definition DefaultUni_dec : EqDec DefaultUni. solveEq. Defined.
  #[export] Hint Resolve DefaultUni_dec : Eqs.

Definition uniType_dec : forall t, EqDec (uniType t). intro t. destruct t; simpl; solveEq; solveEq. Defined.
  #[export] Hint Resolve uniType_dec : Eqs.

Definition valueOf_dec : forall t, EqDec (valueOf t). solveEq. apply uniType_dec. Defined.
  #[export] Hint Resolve valueOf_dec : Eqs.

Definition typeIn_dec : forall t, EqDec (typeIn t). solveEq. Defined.
  #[export] Hint Resolve typeIn_dec : Eqs.


(* Somewhat cumbersome, cannot use "decide equality" tactic *)
Definition some_dec f (dec : forall (t : DefaultUni), EqDec (f t)) :
  forall (x y : @some f), {x = y} + {x <> y}.
Proof.
  intros x y.
  refine (
    match x, y with | @Some' _ u  v, @Some' _ u' v' =>
    match DefaultUni_dec u u' with
    | left eq   => _
    | right neq => _
    end end
  ).
  - subst.
    destruct (dec _ v v').
    + apply left. congruence.
    + apply right. intros H.
      injection H.
      intro H_sigma_eq.
      inversion_sigma.
      (* eq_rect can only be reduced by invoking UIP on H_sigma_eq1 *)
      assert (H_sigma_eq1 = eq_refl) by apply UIP_refl.
      subst H_sigma_eq1; simpl in H_sigma_eq2.
      tauto.
  - apply right. intros H.
    inversion H. contradiction.
Defined.

Definition some_valueOf_dec := @some_dec valueOf valueOf_dec.
#[export] Hint Resolve some_valueOf_dec : Eqs.

Definition some_typeIn_dec := @some_dec typeIn typeIn_dec.
#[export] Hint Resolve some_typeIn_dec : Eqs.

Definition Kind_dec : EqDec Kind. solveEq. Defined.
  #[export] Hint Resolve Kind_dec : Eqs.

Definition Ty_dec: EqDec Ty. solveEq. Defined.
  #[export] Hint Resolve Ty_dec : Eqs.

Definition VDecl_dec: EqDec VDecl. Proof. solveEq. Defined.
  #[export] Hint Resolve VDecl_dec : Eqs.

Definition TVDecl_dec : EqDec TVDecl. Proof. solveEq. Defined.
  #[export] Hint Resolve TVDecl_dec : Eqs.

Definition constructor_dec : EqDec constructor. Proof. solveEq. Defined.
  #[export] Hint Resolve constructor_dec : Eqs.

Definition DTDecl_dec: EqDec DTDecl. Proof. solveEq. Defined.
  #[export] Hint Resolve DTDecl_dec : Eqs.

Lemma Term_dec : forall (x y : Term), {x = y} + {x <> y}
  with binding_dec: forall (x y : Binding), {x = y} + {x <> y}.
Proof.
  - solveEq.
  - solveEq.
Defined.

Definition pass_dec {name : Set} (name_dec : EqDec name) (p1 p2 : pass name) :
  {p1 = p2} + {p1 <> p2}.
  Proof. solveEq. Defined.

Definition pair_dec {a b} (a_dec : EqDec a) (b_dec : EqDec b) : EqDec (a * b).
  Proof. solveEq. Defined.
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
  Note [#[export] Hints and name-collision]
  ~~~~~~~~~~~~~~~~

  When adding Nat.eqb_eq to a hint database using "#[export] Hint Resolve ->", Coq
  generates a definition eqb_eq_l2r (note: not qualified by module name
  anymore). The same happens when adding String.eqb_eq, thus causing a naming
  conflict.
  Current work-around is to alias the imported functions.
*)
(* Note [#[export] Hints and name-collision] *)
Definition Z_eqb_eq := Z.eqb_eq.
Definition nat_eqb_eq := Nat.eqb_eq.
Definition string_eqb_eq := String.eqb_eq.
#[export] Hint Resolve ->
  andb_true_iff
  nat_eqb_eq
  Z_eqb_eq
  string_eqb_eq
  Ascii.eqb_eq
  Bool.eqb_true_iff
: reflection.

#[export] Hint Resolve <-
  andb_true_iff
  nat_eqb_eq
  Z_eqb_eq
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
(*
Definition Eqb_eq := fun {a} (eqb : Eqb a) => forall (x y : a),
  eqb x y = true <-> x = y.
  *)

Definition unit_eqb: Eqb unit := fun x y => match x, y with
  | tt, tt => true
  end.
Definition unit_eqb_eq : forall u u', unit_eqb u u' = true <-> u = u'.
   Proof. eqb_eq_tac. Defined.

#[export] Hint Resolve -> unit_eqb_eq : reflection.
#[export] Hint Resolve <- unit_eqb_eq : reflection.


Definition Strictness_eqb: Eqb Strictness := fun x y =>
  match x, y with
  | NonStrict, NonStrict => true
  | Strict   , Strict    => true
  | _, _                 => false
  end.

Definition Strictness_eqb_eq : forall s s', Strictness_eqb s s' = true <-> s = s'.
Proof. eqb_eq_tac. Defined.
#[export] Hint Resolve -> Strictness_eqb_eq : reflection.
#[export] Hint Resolve <- Strictness_eqb_eq : reflection.

Definition Recursivity_eqb : Eqb Recursivity := fun x y => match x, y with
  | NonRec, NonRec => true
  | Rec, Rec => true
  | _, _ => false
  end.

Definition Recursivity_eqb_eq : forall r r', Recursivity_eqb r r' = true <-> r = r'.
Proof. eqb_eq_tac. Qed.
#[export] Hint Resolve -> Recursivity_eqb_eq : reflection.
#[export] Hint Resolve <- Recursivity_eqb_eq : reflection.

Definition func_eqb : Eqb DefaultFun := fun x y => match x, y with
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

Definition func_eqb_eq : forall f f', func_eqb f f' = true <-> f = f'.
Proof. eqb_eq_tac. Qed.
#[export] Hint Resolve -> func_eqb_eq : reflection.
#[export] Hint Resolve <- func_eqb_eq : reflection.

Definition DefaultUni_eqb : Eqb DefaultUni := fun x y => match x, y with
  | DefaultUniInteger , DefaultUniInteger => true
  | DefaultUniByteString , DefaultUniByteString => true
  | DefaultUniString , DefaultUniString => true
  | DefaultUniChar , DefaultUniChar => true
  | DefaultUniUnit , DefaultUniUnit => true
  | DefaultUniBool , DefaultUniBool => true
  | _, _ => false
  end.

Definition DefaultUni_eqb_eq : forall u u', DefaultUni_eqb u u' = true <-> u = u'.
Proof. eqb_eq_tac. Qed.
#[export] Hint Resolve -> DefaultUni_eqb_eq : reflection.
#[export] Hint Resolve <- DefaultUni_eqb_eq : reflection.

Definition uniType_eqb : forall t, Eqb (uniType t) := fun ty =>
  match ty return Eqb (uniType ty) with
  | DefaultUniInteger => Z.eqb
  | DefaultUniChar    => Strings.Ascii.eqb
  | DefaultUniUnit    => unit_eqb
  | DefaultUniBool    => Bool.eqb
  | DefaultUniByteString => String.eqb
  | DefaultUniString    => String.eqb
  end.

Definition uniType_eqb_eq : forall t ty ty', uniType_eqb t ty ty' = true <-> ty = ty'.
Proof.
  intro t.
  destruct t;
  auto using Z.eqb_eq, string_eqb_eq, unit_eqb_eq, Ascii.eqb_eq, Nat.eqb_eq, Bool.eqb_true_iff.
Qed.

#[export] Hint Resolve -> uniType_eqb_eq : reflection.
#[export] Hint Resolve <- uniType_eqb_eq : reflection.

Definition valueOf_eqb : forall t, Eqb (valueOf t) := fun ty x y => match x, y with
  | ValueOf _ x, ValueOf _ y => uniType_eqb ty x y
  end.

Definition valueOf_eqb_eq : forall t c c', @valueOf_eqb t c c' = true <-> c = c'.
Proof.
  intros t.
  destruct t;
  eqb_eq_tac.
Qed.
#[export] Hint Resolve -> valueOf_eqb_eq : reflection.
#[export] Hint Resolve <- valueOf_eqb_eq : reflection.

Definition some_valueOf_eqb: Eqb (@some valueOf) := fun x y => match x, y with
  | @Some' _ t v, @Some' _ t' v' =>
    match DefaultUni_dec t t' with
    | left H => valueOf_eqb (eq_rect _ valueOf v _ H) v'
    | _      => false
    end
  end.

Definition some_valueOf_eqb_eq : forall v v', some_valueOf_eqb v v' = true <-> v = v'.
Proof.
  eqb_eq_tac.
  - destruct u, u0;
    simpl in *;
    f_equal;
    inversion H;
    auto with reflection.
  - destruct u;
    simpl;
    destruct f; simpl;
    auto with reflection.
Qed.
#[export] Hint Resolve -> some_valueOf_eqb_eq : reflection.
#[export] Hint Resolve <- some_valueOf_eqb_eq : reflection.

Definition typeIn_eqb : forall t, Eqb (typeIn t) := fun ty x y => match x, y with
  | @TypeIn _, TypeIn _ => true
  end.

Definition typeIn_eqb_eq : forall t ty ty', @typeIn_eqb t ty ty' = true <-> ty = ty'.
Proof.
  intros t.
  destruct t;
  eqb_eq_tac.
Qed.
#[export] Hint Resolve -> typeIn_eqb_eq : reflection.
#[export] Hint Resolve <- typeIn_eqb_eq : reflection.

Definition some_typeIn_eqb : Eqb (@some typeIn) := fun x y => match x, y with
  | @Some' _ t v, @Some' _ t' v' =>
    match DefaultUni_dec t t' with
    | left H => typeIn_eqb (eq_rect _ typeIn v _ H) v'
    | _      => false
    end
  end.

Definition some_typeIn_eqb_eq : forall ty ty', some_typeIn_eqb ty ty' = true <-> ty = ty'.
Proof.
  eqb_eq_tac.
  - destruct u, u0;
    simpl in *;
    f_equal;
    inversion H;
    auto with reflection.
  - destruct u;
    simpl;
    destruct f; simpl;
    auto with reflection.
Qed.
#[export] Hint Resolve -> some_typeIn_eqb_eq : reflection.
#[export] Hint Resolve <- some_typeIn_eqb_eq : reflection.

Fixpoint Kind_eqb (x y : Kind) : bool := match x, y with
  | Kind_Base, Kind_Base => true
  | Kind_Arrow K1 K2, Kind_Arrow K3 K4 => Kind_eqb K1 K3 && Kind_eqb K2 K4
  | _, _ => false
  end.

Definition Kind_eqb_eq : forall k k', Kind_eqb k k' = true <-> k = k'.
Proof. eqb_eq_tac. Defined.

#[export] Hint Resolve -> Kind_eqb_eq : reflection.
#[export] Hint Resolve <- Kind_eqb_eq : reflection.

(* TODO: This is not correct yet. Because we have computation in types, we can not merely rely
  on syntactic equality checking. *)
Fixpoint Ty_eqb (x y : Ty) : bool := match x, y with
  | Ty_Var X, Ty_Var Y => String.eqb X Y
  | Ty_Fun T1 T2, Ty_Fun T3 T4 => Ty_eqb T1 T3 && Ty_eqb T2 T4
  | Ty_IFix T1 U1, Ty_IFix T2 U2 => Ty_eqb T1 T2 && Ty_eqb U1 U2
  | Ty_Forall X1 K1 T1, Ty_Forall X2 K2 T2 => String.eqb X1 X2 && Kind_eqb K1 K2 && Ty_eqb T1 T2
  | Ty_Builtin s1, Ty_Builtin s2 => some_typeIn_eqb s1 s2
  | Ty_Lam X1 K1 T1, Ty_Lam X2 K2 T2 => String.eqb X1 X2 && Kind_eqb K1 K2 && Ty_eqb T1 T2
  | Ty_App S1 T1, Ty_App S2 T2 => Ty_eqb S1 S2 && Ty_eqb T1 T2
  | _, _ => false
  end.

Definition Ty_eqb_eq : forall ty ty', Ty_eqb ty ty' = true <-> ty = ty'.
Proof. Local Open Scope string_scope. eqb_eq_tac; try (inversion H).
  - assert (b =? b = true) by eauto with reflection.
    assert (Kind_eqb k k = true) by eauto with reflection.
    rewrite H. rewrite H0. rewrite IHy. auto.
  - assert (b =? b = true) by eauto with reflection.
    assert (Kind_eqb k k = true) by eauto with reflection.
    rewrite H. rewrite H0. rewrite IHy. auto.
Defined.
#[export] Hint Resolve -> Ty_eqb_eq : reflection.
#[export] Hint Resolve <- Ty_eqb_eq : reflection.


Definition TVDecl_eqb : Eqb TVDecl := fun x y => match x, y with
  | TyVarDecl ty k, TyVarDecl ty' k' => String.eqb ty ty' && Kind_eqb k k'
  end.

Definition TVDecl_eqb_eq : forall tvd tvd', TVDecl_eqb tvd tvd' = true <-> tvd = tvd'.
Proof. eqb_eq_tac. Defined.
#[export] Hint Resolve -> TVDecl_eqb_eq : reflection.
#[export] Hint Resolve <- TVDecl_eqb_eq : reflection.


Definition VDecl_eqb: Eqb VDecl := fun x y => match x, y with
  | VarDecl x ty, VarDecl x' ty' => String.eqb x x' && Ty_eqb ty ty'
  end.
Definition VDecl_eqb_eq : forall vd vd', VDecl_eqb vd vd' = true <-> vd = vd'.
Proof. eqb_eq_tac. Defined.

#[export] Hint Resolve -> VDecl_eqb_eq : reflection.
#[export] Hint Resolve <- VDecl_eqb_eq : reflection.
(* reminder: String.eqb_eq is opaque, perhaps this will be an
issue later on*)



Definition constructor_eqb : Eqb constructor := fun x y => match x, y with
  | Constructor c n, Constructor c' n' => VDecl_eqb c c' && Nat.eqb n n'
  end.

Definition constructor_eqb_eq : forall c c', constructor_eqb c c' = true <-> c = c'.
Proof. eqb_eq_tac. Qed.
#[export] Hint Resolve -> constructor_eqb_eq : reflection.
#[export] Hint Resolve <- constructor_eqb_eq : reflection.

Definition list_eqb a (eqb : Eqb a) : Eqb (list a) := fix f xs ys :=
  match xs, ys with
  | nil, nil             => true
  | cons x xs, cons y ys => eqb x y && f xs ys
  | _, _                 => false
  end.

Lemma list_eqb_tl A eqb (x y : A) (xs ys : list A) : list_eqb eqb (x :: xs) (y :: ys) = true -> list_eqb eqb xs ys = true.
Proof.
  simpl. intros. rewrite andb_true_iff in H. intuition.
Qed.


(* Instead of requiring a general decidable equality eqb x x' <-> x = x', we require
   that the elements in the list xs have decidable equality. This makes mutual
   inductive proofs possible *)
Definition list_eqb_eq_Forall a (a_eqb : Eqb a) xs xs' (H_sound_xs : Forall (fun x => forall x', a_eqb x x' = true <-> x = x') xs) :
  list_eqb a_eqb xs xs' = true <-> xs = xs'.
Proof.
  revert xs'.
  induction xs.
  intros xs'.
  - simpl.
    destruct xs'; split; inversion 1; reflexivity.
  - simpl.
    destruct xs'; split; try solve [inversion 1].
    + intros H_eqb.
      rewrite andb_true_iff in H_eqb. destruct H_eqb.
      inversion_clear H_sound_xs.
      specialize (IHxs H2).
      rewrite H1 in H. subst.
      specialize (IHxs xs').
      destruct IHxs.
      f_equal.
      auto.
    + intros.
      inversion H; subst.
      rewrite andb_true_iff.
      inversion H_sound_xs; subst.
      rewrite H2.
      rewrite IHxs; auto.
Qed.

Arguments list_eqb_eq_Forall {a} _ _ _ _.

(* This is the more specific version that isn't suitable for mutual induction *)
Definition list_eqb_eq A (A_eqb : Eqb A) (H : forall x x', A_eqb x x' = true <-> x = x') : forall xs xs',
  list_eqb A_eqb xs xs' = true <-> xs = xs'.
Proof.
  intros.
  assert (H_sound_xs : Forall (fun x => forall x', A_eqb x x' = true <-> x = x') xs).
  { induction xs.
    + constructor.
    + constructor.
      * specialize (H a).
        assumption.
      * assumption.
  }
  apply list_eqb_eq_Forall. auto.
Qed.


#[export] Hint Resolve -> list_eqb_eq : reflection.
#[export] Hint Resolve <- list_eqb_eq : reflection.

Definition DTDecl_eqb: Eqb DTDecl := fun x y => match x, y with
  | Datatype tvd tvds n cs, Datatype tvd' tvds' n' cs' =>
    TVDecl_eqb tvd tvd' && list_eqb TVDecl_eqb tvds tvds'
      && String.eqb n n' && list_eqb constructor_eqb cs cs'
    end.
Definition DTDecl_eqb_eq : forall dtd dtd', DTDecl_eqb dtd dtd' = true <-> dtd = dtd'.
Proof.
  eqb_eq_tac.
  - apply (list_eqb_eq _ TVDecl_eqb_eq ).
    assumption.
  - apply (list_eqb_eq _ constructor_eqb_eq).
    assumption.
  - repeat (apply andb_true_iff_proj_r2l; constructor);
     auto with reflection.
    + apply (list_eqb_eq _ TVDecl_eqb_eq).
      reflexivity.
    + apply (list_eqb_eq _ constructor_eqb_eq).
      reflexivity.
Qed.
#[export] Hint Resolve -> DTDecl_eqb_eq : reflection.
#[export] Hint Resolve <- DTDecl_eqb_eq : reflection.







Fixpoint Term_eqb (x y : Term) {struct x} : bool := match x, y with
  | Let rec bs t, Let rec' bs' t' => Recursivity_eqb rec rec'
      && list_eqb Binding_eqb bs bs'
        && Term_eqb t t'
  | Let _ _ _, _ => false
  | Var n, Var n' => String.eqb n n'
  | Var _, _ => false
  | TyAbs n k t, TyAbs n' k' t' => String.eqb n n' && Kind_eqb k k' && Term_eqb t t'
  | TyAbs _ _ _, _ => false
  | LamAbs n ty t, LamAbs n' ty' t' => String.eqb n n' && Ty_eqb ty ty' && Term_eqb t t'
  | LamAbs _ _ _, _ => false
  | Apply s t, Apply s' t' => Term_eqb s s' && Term_eqb t t'
  | Apply _ _, _ => false
  | Constant c, Constant c' => some_valueOf_eqb c c'
  | Constant _, _ => false
  | Builtin f, Builtin f' => func_eqb f f'
  | Builtin _, _ => false
  | TyInst t ty, TyInst t' ty' => Term_eqb t t' && Ty_eqb ty ty'
  | TyInst _ _, _ => false
  | Error ty , Error ty' => Ty_eqb ty ty'
  | Error _, _ => false
  | IWrap ty1 ty2 t, IWrap ty1' ty2' t' => Ty_eqb ty1 ty1' && Ty_eqb ty2 ty2' && Term_eqb t t'
  | IWrap _ _ _, _ => false
  | Unwrap t, Unwrap t' => Term_eqb t t'
  | Unwrap _, _ => false
  | Constr n args, Constr n' args' => Nat.eqb n n' && forall2b Term_eqb args args'
  | Constr _ _ , _ => false
  | Case t ts, Case t' ts' => Term_eqb t t' && forall2b Term_eqb ts ts'
  | Case _ _, _ => false
  end
with Binding_eqb (x y : Binding) {struct x} : bool := match x, y with
  | TermBind s vd t, TermBind s' vd' t' => Strictness_eqb s s' && VDecl_eqb vd vd' && Term_eqb t t'
  | TermBind _ _ _, _ => false
  | TypeBind tvd ty, TypeBind tvd' ty' => TVDecl_eqb tvd tvd' && Ty_eqb ty ty'
  | TypeBind _ _, _ => false
  | DatatypeBind  dtd, DatatypeBind dtd' => DTDecl_eqb dtd dtd'
  | DatatypeBind _, _ => false
  end
  .
