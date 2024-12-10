From PlutusCert Require Import Language.GHC.Core.AST.

Require Import Strings.String.
Require Import Lists.List.

Require Import Utf8_core.

Fixpoint occurs (x : string) (bs : list (string * Expr string)) : bool :=
  match bs with
    | nil => false
    | (y, _) :: bs' => if eqb x y then true else occurs x bs'
  end
.

Fixpoint subst x (t1 t2 : Expr string) : Expr string :=
  match t2 with
  | Var y   =>
      if String.eqb x y
        then t1
        else Var y
  | App s t => App (subst x t1 s) (subst x t1 t)
  | Lam y t => if String.eqb x y then Lam y t else Lam y (subst x t1 t)
  | Lit l => Lit l
  | Let (NonRec y tb) t =>
      if String.eqb x y
        then t2
        else Let (NonRec y (subst x t1 tb)) (subst x t1 t)

  | Let (Rec bs) t =>
      if occurs x bs
        then t2
        else Let (Rec (map (fun '(y,tb) => (y, subst x t1 tb)) bs)) t

  (* TODO: Ignore non-stlc fragment as long as there is no big-step semantics *)
  | _ => t2
 (*
  | Case      : Expr b -> b -> TType -> list (AltCon * list b * Expr b) -> Expr b
  | EType     : TType -> Expr b    (* Renamed from Type *)

  | Cast      : Expr b -> Coercion -> Expr b
  | Tick      : Tickish Id -> Expr b -> Expr b
  | ECoercion : Coercion -> Expr b (* Renamed from Coercion *)
  *)
  end
.

Inductive eval : Expr string -> Expr string -> Prop :=
  | E_Lam : ∀ x t, eval (Lam x t) (Lam x t)

  | E_App : ∀ tf b tx vx x v,
      eval tf (Lam x b) ->
      eval tx vx ->
      eval (subst x vx b) v ->
      eval (App tf tx) v

  | E_Lit_LitInt : ∀ l,
      eval (Lit l) (Lit l)
.


From PlutusCert Require Import Language.
Definition CoreLang : Language :=
{|
  expr  := Expr string
; bigstep := eval
; app   := @App string
; const := fun n => Lit (LitNumber tt n tt)
|}
.
