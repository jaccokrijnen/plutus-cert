Require Import PlutusCert.Language.PlutusIR.
Import ZArith.BinInt.
Import Coq.Lists.List.
Import Coq.Strings.String.
Import Ascii.
Require Import Coq.Strings.BinaryString.
From Equations Require Import Equations.

Import NamedTerm.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * Substitution *)

(** ** Utilities *)
Definition term_var_bound_by_constructor (c : NamedTerm.constructor) : string :=
  match c with
  | Constructor (VarDecl x _) _ => x
  end.

Definition term_vars_bound_by_binding (b : NamedTerm.Binding) : list string :=
  match b with
  | TermBind _ (VarDecl x _) _ => cons x nil
  | TypeBind (TyVarDecl X _) _ => nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => matchFunc :: (rev (map term_var_bound_by_constructor cs))
  end.

Definition term_vars_bound_by_bindings (bs : list NamedTerm.Binding) : list string := List.concat (map term_vars_bound_by_binding bs).

(** ** Implementation of substitution on terms as inductive datatype *)
Inductive substitute : name -> Term -> Term -> Term -> Prop :=
  | S_Let1 : forall x s bs t0 bs',
      (exists v, In v (term_vars_bound_by_bindings bs) -> x = v) ->
      substitute_bindings_nonrec x s bs bs' ->
      substitute x s (Let NonRec bs t0) (Let NonRec bs' t0)
  | S_Let2 : forall x s bs t0 bs' t0',
      ~(exists v, In v (term_vars_bound_by_bindings bs) -> x = v) ->
      substitute_bindings_nonrec x s bs bs' ->
      substitute x s t0 t0' ->
      substitute x s (Let NonRec bs t0) (Let NonRec bs' t0')
  | S_LetRec1 : forall x s bs t0,
      (exists v, In v (term_vars_bound_by_bindings bs) -> x = v) ->
      substitute x s (Let Rec bs t0) (Let Rec bs t0)
  | S_LetRec2 : forall x s bs t0 bs' t0',
      ~(exists v, In v (term_vars_bound_by_bindings bs) -> x = v) ->
      substitute_bindings_rec x s bs bs' ->
      substitute x s t0 t0' ->
      substitute x s (Let Rec bs t0) (Let Rec bs' t0')
  | S_Var1 : forall x s,
      substitute x s (Var x) s
  | S_Var2 : forall x s y,
      x <> y ->
      substitute x s (Var y) (Var y)
  | S_TyAbs : forall x s bX K t0 t0',
      substitute x s t0 t0' ->
      substitute x s (TyAbs bX K t0) (TyAbs bX K t0')
  | S_LamAbs1 : forall x s T t0,
      substitute x s (LamAbs x T t0) (LamAbs x T t0)
  | S_LamAbs2 : forall x s bx T t0 t0',
      x <> bx ->
      substitute x s t0 t0' ->
      substitute x s (LamAbs bx T t0) (LamAbs bx T t0') 
  | S_Apply : forall x s t1 t2 t1' t2',
      substitute x s t1 t1' ->
      substitute x s t2 t2' ->
      substitute x s (Apply t1 t2) (Apply t1' t2')
  | S_Constant : forall x s u,
      substitute x s (Constant u) (Constant u)
  | S_Builtin : forall x s d,
      substitute x s (Builtin d) (Builtin d)
  | S_TyInst : forall x s t0 T t0',
      substitute x s t0 t0' ->
      substitute x s (TyInst t0 T) (TyInst t0' T)
  | S_Error : forall x s T,
      substitute x s (Error T) (Error T)
  | S_IWrap : forall x s F T t0 t0',
      substitute x s t0 t0' ->
      substitute x s (IWrap F T t0) (IWrap F T t0')
  | S_Unwrap : forall x s t0 t0',
      substitute x s t0 t0' ->
      substitute x s (Unwrap t0) (Unwrap t0') 
      
with substitute_bindings_nonrec : name -> Term -> list Binding -> list Binding -> Prop :=
  | S_NilB_NonRec : forall x s, 
      substitute_bindings_nonrec x s nil nil
  | S_ConsB_NonRec1 : forall x s b b' bs,
      (exists v, In v (term_vars_bound_by_binding b) -> x = v) ->
      substitute_binding x s b b' ->
      substitute_bindings_nonrec x s (b :: bs) (b' :: bs)
  | S_ConsB_NonRec2 : forall x s b b' bs bs',
      ~(exists v, In v (term_vars_bound_by_binding b) -> x = v) ->
      substitute_binding x s b b' ->
      substitute_bindings_nonrec x s bs bs' ->
      substitute_bindings_nonrec x s (b :: bs) (b' :: bs')

with substitute_bindings_rec : name -> Term -> list Binding -> list Binding -> Prop :=
  | S_NilB_Rec : forall x s,
      substitute_bindings_rec x s nil nil
  | S_ConsB_Rec : forall x s b b' bs bs',
      substitute_binding x s b b' ->
      substitute_bindings_rec x s bs bs' ->
      substitute_bindings_rec x s (b :: bs) (b' :: bs')

with substitute_binding : name -> Term -> Binding -> Binding -> Prop :=
  | S_TermBind : forall x s strictness bx T t t',
      substitute x s t t' ->
      substitute_binding x s (TermBind strictness (VarDecl bx T) t) (TermBind strictness (VarDecl bx T) t')
  | S_TypeBind : forall x s tvd T,
      substitute_binding x s (TypeBind tvd T) (TypeBind tvd T)
  | S_DatatypeBind : forall x s dtd,
      substitute_binding x s (DatatypeBind dtd) (DatatypeBind dtd).

Scheme substitute__ind := Minimality for substitute Sort Prop
  with substitute_bindings_nonrec__ind := Minimality for substitute_bindings_nonrec Sort Prop
  with substitute_bindings_rec__ind := Minimality for substitute_bindings_rec Sort Prop
  with substitute_binding__ind := Minimality for substitute_binding Sort Prop.

Combined Scheme substitute__mutind from 
  substitute__ind, 
  substitute_bindings_nonrec__ind, 
  substitute_bindings_rec__ind, 
  substitute_binding__ind.

(** ** Definition as a function (failed) *)
Reserved Notation "'[' x '|->' s ']' t" (at level 20).
Fail Equations substitute (x : name) (s t : Term) : Term := {
  substitute x s (Let NonRec bs t0) => 
    if existsb (String.eqb x) (vars_bound_by_bindings bs)
      then Let NonRec (substitute_bindings_nonrec x s bs) t0
      else Let NonRec (substitute_bindings_nonrec x s bs) ([x |-> s] t0) ;
  substitute x s (Let Rec bs t0) => 
    if existsb (String.eqb x) (vars_bound_by_bindings bs)
      then Let Rec bs t0
      else Let Rec bs (*(map (substitute_binding x s) bs)*) ([x |-> s]  t0) ;
  substitute x s (Var y) => 
    if String.eqb x y then s else Var y ;
  substitute x s (TyAbs bX K t0) => 
    TyAbs bX K ([x |-> s]  t0) ;
  substitute x s (LamAbs bx T t0) => 
    if String.eqb x bx
      then LamAbs bx T t0
      else LamAbs bx T ([x |-> s]  t0) ;
  substitute x s (Apply t1 t2) => 
    Apply ([x |-> s]  t1) ([x |-> s]  t2) ;
  substitute x s (Constant u) => 
    Constant u ;
  substitute x s (Builtin d) => 
    Builtin d ;
  substitute x s (TyInst t0 T) => 
    TyInst ([x |-> s]  t0) T ;
  substitute x s (Error T) => 
    Error T ;
  substitute x s (IWrap F T t0) => 
    IWrap F T ([x |-> s]  t0) ;
  substitute x s (Unwrap t0) => 
    Unwrap ([x |-> s]  t0) }
where "'[' x '|->' s ']' t" := (substitute x s t)

with substitute_bindings_nonrec : (x : name) (s : Term) (bs : list Binding) : list Binding := {
  substitute_bindings_nonrec x s nil =>
    nil ;
  substitute_bindings_nonrec x s (TermBind strictness (VarDecl bx T) t :: bs) =>
    if String.eqb x bx
      then TermBind strictness (VarDecl bx T) ([x |-> s] t) :: bs
      else TermBind strictness (VarDecl bx T) ([x |-> s] t) :: substitute_bindings_nonrec x s bs ;
  substitute_bindings_nonrec x s (TypeBind tvd T :: bs) =>
    if existsb (String.eqb x) (vars_bound_by_binding (TypeBind tvd T))
      then TypeBind tvd T :: bs
      else TypeBind tvd T :: substitute_bindings_nonrec x s bs ;
  substitute_bindings_nonrec x s (DatatypeBind dtd :: bs) =>
    if existsb (String.eqb x) (vars_bound_by_binding (DatatypeBind dtd))
      then DatatypeBind dtd :: bs
      else DatatypeBind dtd :: substitute_bindings_nonrec x s bs }.

(** * Big-step operational semantics *)

Definition arity (df : DefaultFun) : nat :=
  match df with
  | AddInteger => 2
  | SubtractInteger => 2
  | MultiplyInteger => 2
  | DivideInteger => 2
  | QuotientInteger => 2
  | RemainderInteger => 2
  | ModInteger => 2
  | LessThanInteger => 2
  | LessThanEqInteger => 2
  | GreaterThanInteger => 2
  | GreaterThanEqInteger => 2
  | EqInteger => 2
  | Concatenate => 2
  | TakeByteString => 2
  | DropByteString => 2
  | SHA2 => 1
  | SHA3 => 1
  | VerifySignature => 3
  | EqByteString => 2
  | LtByteString => 2
  | GtByteString => 2
  | IfThenElse => 4
  | CharToString => 1
  | Append => 2
  | Trace => 1
  end.

(** ** Values *)
Local Close Scope Z_scope.

Inductive value : Term -> Prop :=
  | V_TyAbs : forall bX K t0,
      (* TODO: Should the line below be included? *)
      value t0 ->
      value (TyAbs bX K t0)
  | V_LamAbs : forall bx T t0,
      value (LamAbs bx T t0)
  | V_Constant : forall u,
      value (Constant u)
  | V_Builtin : forall v,
      value_builtin v ->
      value v
  | V_Error : forall T,
      value (Error T)
  | V_IWrap : forall F T t0,
      (* TODO: Should the line below be included? *)
      value t0 ->
      value (IWrap F T t0)

with value_builtin : Term -> Prop :=
| V_Builtin0 : forall f,
    0 < arity f ->
    value_builtin (Builtin f)
| V_Builtin1 : forall f v1,
    1 < arity f ->
    value v1 ->
    value_builtin (Apply (Builtin f) v1)
| V_Builtin2 : forall f v1 v2,
    2 < arity f ->
    value v1 ->
    value v2 ->
    value_builtin (Apply (Apply (Builtin f) v1) v2)
| V_Builtin1_WithTyInst : forall f T,
    1 < arity f ->
    value_builtin (TyInst (Builtin f) T)
| V_Builtin2_WithTyInst : forall f T v1,
    2 < arity f ->
    value v1 ->
    value_builtin (Apply (TyInst (Builtin f) T) v1)
| V_Builtin3_WithTyInst : forall f T v1 v2,
    3 < arity f ->
    value v1 ->
    value v2 ->
    value_builtin (Apply (Apply (TyInst (Builtin f) T) v1) v2).

(** ** Meanings of built-in functions *)
Local Open Scope Z_scope.

Definition constInt (a : Z) : Term := Constant (Some (ValueOf DefaultUniInteger a)).
Definition constBool (a : bool) : Term := Constant (Some (ValueOf DefaultUniBool a)).
Definition constBS (a : string) : Term := Constant (Some (ValueOf DefaultUniByteString a)).
Definition constChar (a : ascii) : Term := Constant (Some (ValueOf DefaultUniChar a)).
Definition constString (a : string) : Term := Constant (Some (ValueOf DefaultUniString a)).
Definition constUnit (a : unit) : Term := Constant (Some (ValueOf DefaultUniUnit a)).

Definition take (x : Z) (s : string) : string := substring 0 (Z.to_nat x) s.
Definition drop (x : Z) (s : string) : string := substring (Z.to_nat x) (length s) s.

Inductive eval_defaultfun : Term -> Term -> Prop :=
  (** Binary operators on integers *)
  | E_Builtin_AddInteger : forall x y,
      eval_defaultfun (Apply (Apply (Builtin AddInteger) (constInt x)) (constInt y)) (constInt (x + y))
  | E_Builtin_SubtractInteger : forall x y, 
      eval_defaultfun (Apply (Apply (Builtin SubtractInteger) (constInt x)) (constInt y)) (constInt (x - y))
  | E_Builtin_MultiplyInteger : forall x y,
      eval_defaultfun  (Apply (Apply (Builtin MultiplyInteger) (constInt x)) (constInt y)) (constInt (x * y))
  | E_Builtin_DivideInteger : forall x y,
      eval_defaultfun  (Apply (Apply (Builtin DivideInteger) (constInt x)) (constInt y)) (constInt (x / y))
  | E_Builtin_QuotientInteger : forall x y,
      eval_defaultfun  (Apply (Apply (Builtin QuotientInteger) (constInt x)) (constInt y)) (constInt (x ÷ y))
  | E_Builtin_RemainderInteger : forall x y,
      eval_defaultfun (Apply (Apply (Builtin RemainderInteger) (constInt x)) (constInt y)) (constInt (Z.rem x y))
  | E_Builtin_ModInteger : forall x y,
      eval_defaultfun  (Apply (Apply (Builtin ModInteger) (constInt x)) (constInt y)) (constInt (x mod y))
  (** Binary predicates on integers *)
  | E_Builtin_LessThanInteger : forall x y,
      eval_defaultfun (Apply (Apply (Builtin LessThanInteger) (constInt x)) (constInt y)) (constBool (x <? y))
  | E_Builtin_LessThanEqInteger : forall x y,
      eval_defaultfun (Apply (Apply (Builtin LessThanEqInteger) (constInt x)) (constInt y)) (constBool (x <=? y))
  | E_Builtin_GreaterThanInteger : forall x y,
      eval_defaultfun (Apply (Apply (Builtin GreaterThanInteger) (constInt x)) (constInt y)) (constBool (x >? y))
  | E_Builtin_GreaterThanEqInteger : forall x y,
      eval_defaultfun (Apply (Apply (Builtin GreaterThanEqInteger) (constInt x)) (constInt y)) (constBool (x >=? y))
  | E_Builtin_EqInteger : forall x y,
      eval_defaultfun (Apply (Apply (Builtin EqInteger) (constInt x)) (constInt y)) (constBool (x =? y))
  (** Bytestring operations *)
  | E_Builtin_Concatenate : forall bs1 bs2,
      eval_defaultfun (Apply (Apply (Builtin Concatenate) (constBS bs1)) (constBS bs2)) (constBS (bs1 ++ bs2))
  | E_Builtin_TakeByteString : forall x bs,
      eval_defaultfun (Apply (Apply (Builtin TakeByteString) (constInt x)) (constBS bs)) (constBS (take x bs))
  | E_Builtin_DropByteString : forall x bs,
      eval_defaultfun (Apply (Apply (Builtin DropByteString) (constInt x)) (constBS bs)) (constBS (drop x bs))
  (** Bytestring hashing
      
      Note: We model hashing by identity. Comparing hashes now becomes a straightforward equality check.
      We believe modelling hash function as such is sufficient, because the dynamic semantics is not meant to 
      be used as a basis for a real-world evaluator.
  *)
  | E_Builtin_SHA2 : forall bs,
      eval_defaultfun (Apply (Builtin SHA2) (constBS bs)) (constBS bs)
  | E_Builtin_SHA3 : forall bs,
      eval_defaultfun (Apply (Builtin SHA3) (constBS bs)) (constBS bs)
  (** Signature verification *)
  | E_Builtin_VerifySignature : forall publicKey message signature,
      (* TODO: Obviously, this should evaluate to true. However, how can we model the verification of signatures? 

         Implementation of signature verification:
         https://input-output-hk.github.io/ouroboros-network/cardano-crypto/Crypto-ECC-Ed25519Donna.html
      *)
      eval_defaultfun (Apply (Apply (Apply (Builtin VerifySignature) (constBS publicKey)) (constBS message)) (constBS signature)) (constBool true)
  (** Binary predicates on bytestrings *)
  | E_Builtin_EqByteString : forall bs1 bs2,
      eval_defaultfun (Apply (Apply (Builtin EqByteString) (constBS bs1)) (constBS bs2)) (constBool (bs1 =? bs2)%string)
  | E_Builtin_LtByteString : forall bs1 bs2,
      eval_defaultfun (Apply (Apply (Builtin LtByteString) (constBS bs1)) (constBS bs2)) (constBool (to_Z bs1 <? to_Z bs2))
  | E_Builtin_GtByteString : forall bs1 bs2,
      eval_defaultfun (Apply (Apply (Builtin GtByteString) (constBS bs1)) (constBS bs2)) (constBool (to_Z bs1 >? to_Z bs2))
  (** If-Then-Else *)
  | E_Builtin_IfThenElse : forall cond t f T,
      eval_defaultfun (Apply (Apply (Apply (TyInst (Builtin IfThenElse) T) (constBool cond)) t) f) (if cond then t else f)
  (** String operations *)
  | E_Builtin_CharToString : forall ch,
      eval_defaultfun (Apply (Builtin CharToString) (constChar ch)) (constString (String ch EmptyString))
  | E_Builtin_Append : forall s1 s2,
      eval_defaultfun (Apply (Apply (Builtin Append) (constString s1)) (constString s2)) (constString (s1 ++ s2))
  | E_Builtin_Trace : forall s,
      eval_defaultfun (Apply (Builtin Trace) (constString s)) (constUnit tt)
.

(** ** Implementation of big-step semantics as an inductive datatype *)
Reserved Notation "t '==>' v"(at level 40).
Inductive eval : Term -> Term -> Prop :=
  | E_Let : forall bs t v,
      eval_bindings_nonrec (Let NonRec bs t) v ->
      (Let NonRec bs t) ==> v
  | E_LetRec : forall bs t,
      (Let Rec bs t) ==> (Let Rec bs t) (* TODO *)
  (* | E_Var : should never occur *)
  | E_TyAbs : forall X K t v,
      t ==> v ->
      TyAbs X K t ==> TyAbs X K v
  | E_LamAbs : forall x T t,
      LamAbs x T t ==> LamAbs x T t
  | E_Apply : forall t1 t2 x T t0 t0' v2 v0,
      t1 ==> LamAbs x T t0 ->
      t2 ==> v2 ->
      substitute x v2 t0 t0' ->
      t0' ==> v0 ->
      Apply t1 t2 ==> v0
  | E_Constant : forall a,
      Constant a ==> Constant a
  (* Builtins *)
  | E_Builtin : forall f,
      Builtin f ==> Builtin f
  | E_ApplyBuiltin1 : forall t1 t2 v1 v2,
      t1 ==> v1 ->
      value_builtin v1 ->
      t2 ==> v2 ->
      value_builtin (Apply v1 v2) ->
      Apply t1 t2 ==> Apply v1 v2
  | E_ApplyBuiltin2 : forall t1 t2 v1 v2 v0,
      t1 ==> v1 ->
      value_builtin v1 ->
      t2 ==> v2 ->
      ~(value_builtin (Apply v1 v2)) ->
      eval_defaultfun (Apply v1 v2) v0 ->
      Apply t1 t2 ==> v0
  | E_TyInstBuiltin1 : forall t1 T,
      t1 ==> Builtin IfThenElse ->
      TyInst t1 T ==> TyInst (Builtin IfThenElse) T
  (* Type instantiation *)
  | E_TyInst : forall t1 T2 X K v0,
      t1 ==> TyAbs X K v0 ->
      (* TODO: should the type argument be substituted for the type variable?
      substituteT_in_term X T2 v0 v0' ->
      *)
      TyInst t1 T2 ==> v0
  (* Errors and their propagation *)
  | E_Error : forall T,
      Error T ==> Error T
  (* Wrap and unwrap *)
  | E_IWrap : forall F T t0 v0,
      t0 ==> v0 ->
      IWrap F T t0 ==> IWrap F T v0
  | E_Unwrap : forall t0 F T v0,
      t0 ==> IWrap F T v0 ->
      Unwrap t0 ==> v0
  (* TODO: Should there be a rule for type reduction? *)

  (* TODO: Errors propagate *)

with eval_bindings_nonrec : Term -> Term -> Prop :=
  | E_NilB_NonRec : forall t v,
      t ==> v ->
      eval_bindings_nonrec (Let NonRec nil t) v
  | E_ConsB_NonRec : forall s x T tb bs t vb bs' t' v,
      tb ==> vb ->
      substitute_bindings_nonrec x vb bs bs' ->
      substitute x vb t t' ->
      eval_bindings_nonrec (Let NonRec bs' t') v ->
      eval_bindings_nonrec (Let NonRec ((TermBind s (VarDecl x T) tb) :: bs) t) v

where "t '==>' v" := (eval t v).

Scheme eval__ind := Minimality for eval Sort Prop
  with eval_bindings_nonrec__ind := Minimality for eval_bindings_nonrec Sort Prop.


(** ** Examples for derivations of [eval] *)

Definition Ty_int : Ty := Ty_Builtin (Some (TypeIn DefaultUniInteger)).
Definition int_to_int : Ty := Ty_Fun Ty_int Ty_int.

Example test_addInteger : 
  Apply (LamAbs "x+" int_to_int (Apply (Var "x+") (constInt 17))) (Apply (Builtin AddInteger) (constInt 3))
  ==> constInt 20.
Proof.
  eapply E_Apply.
  - apply E_LamAbs.
  - eapply E_ApplyBuiltin1.
    + apply E_Builtin.
    + apply V_Builtin0.
      simpl.
      apply le_S.
      apply le_n.
    + apply E_Constant.
    + apply V_Builtin1.
      * simpl.
        apply le_n.
      * apply V_Constant.
  - apply S_Apply.
    + apply S_Var1.
    + apply S_Constant.
  - eapply E_ApplyBuiltin2.
    + eapply E_ApplyBuiltin1.
      * apply E_Builtin.
      * apply V_Builtin0.
        simpl.
        apply le_S.
        apply le_n.
      * apply E_Constant.
      * apply V_Builtin1.
        -- simpl.
           apply le_n.
        -- apply V_Constant.
    + apply V_Builtin1.
      -- apply le_n.
      -- apply V_Constant.
    + apply E_Constant.
    + intros Hcon.
      inversion Hcon. subst.
      simpl in H2.
      apply PeanoNat.Nat.lt_irrefl in H2.
      inversion H2. 
    + apply E_Builtin_AddInteger.
Qed.

Definition int_and_int_to_int : Ty := Ty_Fun Ty_int (Ty_Fun Ty_int Ty_int).


Example test_ifThenElse :
  Apply (LamAbs "ite_c" int_and_int_to_int (Apply (Apply (Var "ite_c") (constInt 17)) (constInt 3))) (Apply (TyInst (Apply (LamAbs "x" Ty_int (Builtin IfThenElse)) (constInt 666)) (Ty_Builtin (Some (TypeIn DefaultUniInteger)))) (Constant (Some (ValueOf DefaultUniBool true)))) ==> constInt 17.
Proof.
  eapply E_Apply.
  - apply E_LamAbs.
  - eapply E_ApplyBuiltin1.
    + eapply E_TyInstBuiltin1. 
      eapply E_Apply.
      * apply E_LamAbs.
      * apply E_Constant.
      * apply S_Builtin.
      * apply E_Builtin.
    + apply V_Builtin1_WithTyInst.
      simpl. apply le_S. apply le_S. apply le_n.
    + apply E_Constant.
    + apply V_Builtin2_WithTyInst.
      * simpl. apply le_S. apply le_n.
      * apply V_Constant.
  - apply S_Apply.
    + apply S_Apply.
      * apply S_Var1.
      * apply S_Constant.
    + apply S_Constant.
  - eapply E_ApplyBuiltin2.
    + apply E_ApplyBuiltin1.
      * apply E_ApplyBuiltin1.
        -- apply E_TyInstBuiltin1.
           apply E_Builtin.
        -- apply V_Builtin1_WithTyInst.
           simpl. apply le_S. apply le_S. apply le_n.
        -- apply E_Constant.
        -- apply V_Builtin2_WithTyInst.
           ++ simpl. apply le_S. apply le_n.
           ++ apply V_Constant.
      * apply V_Builtin2_WithTyInst.
        -- simpl. apply le_S. apply le_n.
        -- apply V_Constant.
      * apply E_Constant.
      * apply V_Builtin3_WithTyInst.
        -- simpl. apply le_n.
        -- apply V_Constant.
        -- apply V_Constant.
    + apply V_Builtin3_WithTyInst.
      * simpl. apply le_n.
      * apply V_Constant.
      * apply V_Constant.
    + apply E_Constant.
    + intros Hcon.
      inversion Hcon.
    + apply E_Builtin_IfThenElse.
Qed. 