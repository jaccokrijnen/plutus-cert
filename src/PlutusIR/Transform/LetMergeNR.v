From PlutusCert Require Import
  PlutusIR.
Require Import Lists.List.
Import ListNotations.

(*

Transforms a term into one where all subsequent non-recursive lets are merged.
Convenient for passes that transform lets "modulo" let merging.

merge (let x = 3 in let y = 5; data A = B in x)
=
let x = 3; y = 5; data A = B in x

*)

(* Apply merge in the term of the binding *)
Definition merge_binding (merge : term -> term) (b : binding) : binding :=
  match b with
    | TermBind s vd t => TermBind s vd (merge t)
    | DatatypeBind dtd => DatatypeBind dtd
    | TypeBind tvd ty => TypeBind tvd ty
  end
  .

(* Merge subsequent non-recursive lets *)
Function merge (t : term) : term :=
  match t with
  | Let NonRec bs t =>
    match merge t with
    | Let NonRec bs' t' => Let NonRec (map (merge_binding merge) bs ++ bs') t'
    | t' => Let NonRec bs t'
    end
  | Let Rec bs t => Let Rec (map (merge_binding merge) bs) (merge t)
  | Var x => Var x
  | TyAbs X K t => TyAbs X K (merge t)
  | LamAbs x T t => LamAbs x T (merge t)
  | Apply s t => Apply (merge s) (merge t)
  | Constant c => Constant c
  | Builtin f => Builtin f
  | TyInst t T => TyInst (merge t) T
  | Error T => Error T
  | IWrap F T t => IWrap F T (merge t)
  | Unwrap t => Unwrap (merge t)
  | Constr T n ts => Constr T n (map merge ts)
  | Case T t ts => Case T (merge t) (map merge ts)
  end
.


(* Apply split in the term of the binding *)
Definition split_binding (split : term -> term) (b : binding) : binding :=
  match b with
    | TermBind s vd t => TermBind s vd (split t)
    | DatatypeBind dtd => DatatypeBind dtd
    | TypeBind tvd ty => TypeBind tvd ty
  end
  .


(* Split non-recursive let groups into one per binding *)
Fixpoint split (t : term) : term :=
  match t with
  | Let NonRec bs t =>
      (fix go bs :=
        match bs with
        | [] => t
        | b :: bs => Let NonRec [b] (go bs)
        end) bs
  | Let Rec bs t => Let Rec (map (split_binding split) bs) (split t)
  | Var x => Var x
  | TyAbs X K t => TyAbs X K (split t)
  | LamAbs x T t => LamAbs x T (split t)
  | Apply s t => Apply (split s) (split t)
  | Constant c => Constant c
  | Builtin f => Builtin f
  | TyInst t T => TyInst (split t) T
  | Error T => Error T
  | IWrap F T t => IWrap F T (split t)
  | Unwrap t => Unwrap (split t)
  | Constr T n ts => Constr T n (map split ts)
  | Case T t ts => Case T (split t) (map split ts)
  end
.

Section EXAMPLES.

Import Strings.String.
Open Scope string_scope.


Definition b1 := TermBind Strict (VarDecl "x" ty_unit) unitVal.
Definition b2 := TermBind NonStrict (VarDecl "y" ty_unit) unitVal.
Definition t := Var "x".

Example ex :
  merge (Let NonRec [b1] (Let NonRec [b2] t)) =
  Let NonRec [merge_binding merge b1; merge_binding merge b2] t.
Proof.
  reflexivity.
Qed.

Example split_merge :
  split (merge (Let NonRec [b1] (Let NonRec [b2] t))) =
  Let NonRec [b1] (Let NonRec [b2] t).
Proof.
  reflexivity.
Qed.


End EXAMPLES.
