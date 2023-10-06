Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Ascii.
Require Import Omega.
From Equations Require Import Equations.

Require Import FunInd.

Set Implicit Arguments.

From PlutusCert Require Import
  PlutusIR
  PlutusIR.Folds
  Analysis.BoundVars
  Util
  Util.List
.


Module Ty.


  Section FreeVars.
  Context
    {tyvar : Set}
    (tyvar_dec : forall x y : tyvar, {x = y} + {x <> y})
    .

  Function ftv (T : ty tyvar tyvar) : list tyvar :=
    match T with
    | Ty_Var X =>
        [X]
    | Ty_Fun T1 T2 =>
        ftv T1 ++ ftv T2
    | Ty_IFix F T =>
        ftv F ++ ftv T
    | Ty_Forall X K T' =>
        remove tyvar_dec X (ftv T')
    | Ty_Builtin u =>
        []
    | Ty_Lam X K1 T' =>
        remove tyvar_dec X (ftv T')
    | Ty_App T1 T2 =>
        ftv T1 ++ ftv T2
    end.
  End FreeVars.

End Ty.


Module Term.
  Section FreeVars.

  (* Parametrized for _named_ binders (not de Bruijn) *)
  Context
    {var tyvar : Set}
    (var_dec : forall x y : var, {x = y} + {x <> y})
    (tyvar_dec : forall x y : tyvar, {x = y} + {x <> y})
    .

  Definition binding' := binding var tyvar var tyvar.

  Section Bindings.

    (* It becomes a parameter to both fvbs and the generated
       fvbs_equation *)
    Context (fvb : Recursivity -> binding' -> list var).

    Function fvbs  rec (bs : list binding') : list var :=
    match bs with
      | nil     => []
      | b :: bs =>
         match rec with
           | Rec    =>
               remove_many var_dec (bvbs (b :: bs)) (fvb Rec b)
               ++ remove_many var_dec (bvbs (b :: bs)) (fvbs Rec bs)
           | NonRec =>
               fvb NonRec b
               ++ remove_many var_dec (bvb b) (fvbs NonRec bs)
         end
    end.

  End Bindings.

  Function fv (t : term var tyvar var tyvar) : list var :=
   match t with
     | Let rec bs t => fvbs fvb rec bs ++ remove_many var_dec (bvbs bs) (fv t)
     | (LamAbs n ty t)   => remove var_dec n (fv t)
     | (Var n)           => [n]
     | (TyAbs n k t)     => fv t
     | (Apply s t)       => fv s ++ fv t
     | (TyInst t ty)     => fv t
     | (IWrap ty1 ty2 t) => fv t
     | (Unwrap t)        => fv t
     | (Error ty)        => []
     | (Constant v)      => []
     | (Builtin f)       => []
     end

  with fvb rec (b : binding') : list var :=
    match b with
      | TermBind _ (VarDecl v _) t => match rec with
        | Rec    => remove var_dec v (fv t)
        | NonRec => fv t
        end
      | _        => []
    end
    .

  (* Write by hand, because somehow it isn't generated for fvb *)
  Lemma fvb_equation rec (b : binding') :
    fvb rec b =
    match b with
      | TermBind _ (VarDecl v _) t => match rec with
        | Rec    => remove var_dec v (fv t)
        | NonRec => fv t
        end
      | _        => []
    end
    .
  Proof.
    destruct b; destruct rec;
    reflexivity.
  Qed.


  Section Bindings.
  Context (ftvb : Recursivity -> binding' -> list tyvar).

  Function ftvbs rec bs : list tyvar :=
    match bs with
      | nil => []
      | b :: bs => match rec with
        | Rec =>
             remove_many tyvar_dec (btvbs (b :: bs)) (ftvb Rec b)
          ++ remove_many tyvar_dec (btvbs (b :: bs)) (ftvbs NonRec bs)
        | NonRec =>
             ftvb NonRec b
          ++ remove_many tyvar_dec (btvb b) (ftvbs NonRec bs)
        end
    end.

  End Bindings.


  (*
  Lemma ftvbs_NonRec_cons ftvb b bs :
     ftvbs ftvb NonRec (b :: bs)
   = ftvb NonRec b ++ remove_many tyvar_dec (btvb b) (ftvbs ftvb NonRec bs).
  Proof.
    reflexivity.
  Qed.

  Lemma ftvbs_Rec_cons ftvb b bs :
     ftvbs ftvb Rec (b :: bs)
   = ftvb NonRec b ++ remove_many tyvar_dec (btvbs (b :: bs)) (ftvbs ftvb Rec bs).
  Proof.
    simpl.
    reflexivity.
  Qed.
  *)

  Definition ftvc (c : constr tyvar var tyvar) : list tyvar :=
    match c with
      | Constructor (VarDecl _ τ) _ => Ty.ftv tyvar_dec τ
    end.

  Function ftv (t : term var tyvar var tyvar) : list tyvar :=
   match t with
     | Let rec bs t => ftvbs ftvb rec bs ++ remove_many tyvar_dec (btvbs bs) (ftv t)
     | LamAbs n τ t    => Ty.ftv tyvar_dec τ ++ ftv t
     | Var n           => []
     | TyAbs α k t     => remove tyvar_dec α (ftv t)
     | Apply s t       => ftv s ++ ftv t
     | TyInst t τ      => Ty.ftv tyvar_dec τ ++ ftv t
     | IWrap τ1 τ2 t   => Ty.ftv tyvar_dec τ1 ++ Ty.ftv tyvar_dec τ2 ++ ftv t
     | Unwrap t        => ftv t
     | Error τ         => Ty.ftv tyvar_dec τ
     | Constant v      => []
     | Builtin f       => []
     end

  with ftvb rec (b : binding') : list tyvar :=
    match b with
      | TermBind s (VarDecl _ τ) t => Ty.ftv tyvar_dec τ ++ ftv t
      | TypeBind (TyVarDecl α k) τ  => Ty.ftv tyvar_dec τ
      | DatatypeBind (Datatype (TyVarDecl α _) params m cs) => concat (map ftvc cs)
    end
    .

  Lemma ftvb_equation rec b :  
    ftvb rec b =
    match b with
      | TermBind s (VarDecl _ τ) t => Ty.ftv tyvar_dec τ ++ ftv t
      | TypeBind (TyVarDecl α k) τ  => Ty.ftv tyvar_dec τ
      | DatatypeBind (Datatype (TyVarDecl α _) params m cs) => concat (map ftvc cs)
    end.
  Proof.
    destruct rec, b.
    all: reflexivity.
  Qed.

  End FreeVars.
End Term.
