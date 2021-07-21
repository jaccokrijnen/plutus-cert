From Coq Require Import
  String
  List
  Bool
  Program.

From PlutusCert Require Import
  Util
  Language.PlutusIR
  Language.PlutusIR.Analysis.Equality
  Language.PlutusIR.Transform.Congruence
  Language.PlutusIR.Transform.Let
  Language.PlutusIR.Transform.Inline.


Definition Bindings_desugar' :=
  fun (Term_desugar : Term -> Term -> bool) =>
    (fix Bindings_desugar'
            (bs : list Binding) (t : Term) {struct bs} := match bs with
            | nil       => Just t
            | cons b bs => match b, t with
              | TermBind Strict v rhs, Apply (LamAbs v' _ body') rhs' =>
                if (String.eqb v v' && Term_desugar rhs rhs')
                  then Bindings_desugar' bs body'
                  else None
                (* Notation scope analysis fails, not sure why....*)
              | _, _ => None
              end
            end).

(*
  Returns true if the inline transformation was correct
*)
Fixpoint dec_inline (env : list (string * Term)) (x y : Term) {struct x} : bool := match x, y with
  | Var n          , t                  =>

  | Let rec bs t   , Let rec' bs' t'    => Recursivity_eqb rec rec' && list_eqb (dec_inline_Binding env) bs bs' && dec_inline env t t'
  | TyAbs n k t    , TyAbs n' k' t'     => String.eqb n n' && Kind_eqb k k' && dec_inline env t t'
  | LamAbs n ty t  , LamAbs n' ty' t'   => String.eqb n n' && Ty_eqb ty ty' && dec_inline env t t'
  | Apply s t      , Apply s' t'        => dec_inline env s s' && dec_inline env t t'
  | Constant c     , Constant c'        => some_eqb c c'
  | Builtin f      , Builtin f'         => func_eqb f f'
  | TyInst t ty    , TyInst t' ty'      => dec_inline env t t' && Ty_eqb ty ty'
  | Error ty       , Error ty'          => Ty_eqb ty ty'
  | IWrap ty1 ty2 t, IWrap ty1' ty2' t' => Ty_eqb ty1 ty1' && Ty_eqb ty2 ty2' && dec_inline env t t'
  | Unwrap t       , Unwrap t'          => dec_inline env t t'

  | _, _ => false
  end
with dec_inline_Binding (env : list (string * Term)) (b b' : Binding) : bool := match b, b' with
  | TermBind s vdecl t, TermBind s' vdecl' t' => Strictness_eqb s s' && VDecl_eqb vdecl vdecl' && dec_inline env t t'
  | TypeBind tvdecl ty, TypeBind tvdecl' ty'  => TVDecl_eqb tvdecl tvdecl' && Ty_eqb ty ty'
  | DatatypeBind dtd  , DatatypeBind dtd'     => DTDecl_eqb dtd dtd'
  | _, _ => false
  end
.

(* See comment of Bindings_desugar' *)
Definition Bindings_desugar
     : list Binding -> Term -> option Term := Bindings_desugar' Term_desugar.


