From Coq Require Import
  ZArith.BinInt
  Strings.String (eqb)
  Lists.List
.

From PlutusCert Require Import
  PlutusIR
  FreeVars
  Analysis.BoundVars
  Equality
  Util
  Util.List
  UniqueBinders
  UniqueBinders.DecOpt
.

Require Import Init.Datatypes.


(* Import UniqueTerm. *)
Import ListNotations.

Section InlineOnly.

  (* The variables that were conditionally inlined as dumped by the compiler*)
  Context (elims : list name).

  (* Add a term-binding if it occurs in elims *)
  Definition bind_to_term_env (b : binding) : list (name * term)
   := match b with
    | TermBind str (VarDecl v ty) t => if elem String.eqb v elims then [(v, t)] else []
    | TypeBind v ty   => []
    | DatatypeBind dt => []
    end.

  (* Add a term-binding if it occurs in elims *)
  Definition bind_to_ty_env (b : binding) : list (tyname * ty)
   := match b with
    | TermBind str (VarDecl v ty) t => []
    | TypeBind (TyVarDecl v k) ty   => if elem String.eqb v elims then [(v, ty)] else []
    | DatatypeBind dt => []
    end.

  Definition binds_to_term_env (bs : list binding) : list (name * term) :=
    concat (map bind_to_term_env bs).

  Definition binds_to_ty_env (bs : list binding) : list (tyname * ty) :=
    concat (map bind_to_ty_env bs).

  (* Unconditionally inline the variables in elims, by
     collecting let-bound definitions with those names
   *)

  Definition inline_uncond_ty (Δ : list (tyname * ty)) : ty -> ty :=
    ty_transform
      (fun τ => match τ with
        | Ty_Var _ => Some (fun v => match lookup' String.eqb v Δ with | Some t => t | None => Ty_Var v end)
        | _        => None
      end
      ).

  Fixpoint inline_uncond (Γ : list (name * term)) (Δ : list (name * ty)) (t : term) : term
    := match t with

        (* Non-recursive bindings require linear scoping, inlined fixpoint for totality checker *)
        | Let NonRec bs t_body =>
            Let NonRec
              ((fix f bs := fun Γ Δ => match bs with
                | []        => []
                | (b :: bs) => inline_uncond_binding Γ Δ b :: f bs (bind_to_term_env b ++ Γ) (bind_to_ty_env b ++ Δ)
              end) bs Γ Δ)
              (inline_uncond (binds_to_term_env bs ++ Γ) (binds_to_ty_env bs ++ Δ) t_body)

        (* recursive bindings won't be inlined, so never extend Γ or Δ *)
        | Let Rec bs t_body => Let Rec (map (inline_uncond_binding Γ Δ) bs) (inline_uncond Γ Δ t_body)

        (* β redex case for TyInst *)
        | TyInst (TyAbs v k t) τ => TyInst (inline_uncond Γ ((v, τ) :: Δ) t) (inline_uncond_ty Δ τ)

        | Var x             =>
          match lookup' String.eqb x Γ with
          | None   => Var x
          | Some t => t
          end
        | TyAbs v k t       => TyAbs v k (inline_uncond Γ Δ t)
        | LamAbs v τ t      => LamAbs v (inline_uncond_ty Δ τ) (inline_uncond Γ Δ t)
        | Apply t1 t2       => Apply (inline_uncond Γ Δ t1) (inline_uncond Γ Δ t2)
        | Constant c        => Constant c
        | Builtin f         => Builtin f
        | TyInst t τ        => TyInst (inline_uncond Γ Δ t) (inline_uncond_ty Δ τ)
        | Error τ           => Error (inline_uncond_ty Δ τ)
        | IWrap τ1 τ2 t     => IWrap (inline_uncond_ty Δ τ1) (inline_uncond_ty Δ τ2) (inline_uncond Γ Δ t)
        | Unwrap t          => Unwrap (inline_uncond Γ Δ t)
        | Constr i T ts     => Constr i (inline_uncond_ty Δ T) (map (inline_uncond Γ Δ) ts)
        | Case T t ts       => Case (inline_uncond_ty Δ T) (inline_uncond Γ Δ t) (map (inline_uncond Γ Δ) ts)
      end

   with inline_uncond_binding (Γ : list (name * term)) (Δ : list (tyname * ty)) (b : binding) : binding
   := match b with
    | TermBind str (VarDecl v τ) t => TermBind str (VarDecl v (inline_uncond_ty Δ τ)) (inline_uncond Γ Δ t)
    | TypeBind v τ                 => TypeBind v (inline_uncond_ty Δ τ)
    | DatatypeBind dt              => DatatypeBind dt
    end
  .

  Fixpoint inline_deadcode (t : term) : term :=
    match t with
      | Let rec bs t_body => mk_let rec (concat (map inline_deadcode_binding bs)) (inline_deadcode t_body)
      | TyInst (TyAbs v k t) ty => if elem String.eqb v elims then inline_deadcode t else TyInst (TyAbs v k (inline_deadcode t)) ty

      | Var x             => Var x
      | TyAbs v k t       => TyAbs v k (inline_deadcode t)
      | LamAbs v ty t     => LamAbs v ty (inline_deadcode t)
      | Apply t1 t2       => Apply (inline_deadcode t1) (inline_deadcode t2)
      | Constant c        => Constant c
      | Builtin f         => Builtin f
      | TyInst t ty       => TyInst (inline_deadcode t) ty
      | Error ty          => Error ty
      | IWrap ty1 ty2 t   => IWrap ty1 ty2 (inline_deadcode t)
      | Unwrap t          => Unwrap (inline_deadcode t)
      | Constr i T ts     => Constr i T (map inline_deadcode ts)
      | Case T t ts       => Case T (inline_deadcode t) (map (inline_deadcode) ts)
    end

   with inline_deadcode_binding (b : binding) : list binding
   := match b with
    | TermBind str (VarDecl v ty) t => if elem String.eqb v elims then [] else [TermBind str (VarDecl v ty) (inline_deadcode t)]
    | TypeBind (TyVarDecl v k) ty   => if elem String.eqb v elims then [] else [TypeBind (TyVarDecl v k) ty]
    | DatatypeBind dt               => [DatatypeBind dt]
    end
  .

  (* Will the let node be replaced by its body? This happens
     when all bindings have been eliminated *)
  Definition let_group_eliminated
    (elims : list name) (bs : list binding) : bool :=
    forallb
      (fun v => elem String.eqb v elims)
      (bvbs bs)
  .


  (* Constructs the final term, but without dead-code performed
     Note: this does result in inlined terms that are α-renamed compared to their
     binding site *)
  Fixpoint inlined_intermediate (elims : list name) (t : term) (t' : term) : option term
    := match t, t' with
        (* We can traverse the ASTs in parallel, except when a complete
           Let node was removed (because all of its bindings were eliminated) *)
        | Let rec bs t_body, t' =>
            if let_group_eliminated elims bs
              then
                Let rec bs <$> inlined_intermediate elims t_body t'
              else
                match t' with
                 | Let _ bs' t_body'  =>
                     Let rec <$> sequence_options (map (fun b => inlined_intermediate_binding elims b bs') bs)
                             <*> inlined_intermediate elims t_body t_body'

                 | _                  => None
                 end

        | Var x, t     => pure t (* it must be inlined *)

        | TyAbs v k t, TyAbs _ _ t' => TyAbs v k <$> inlined_intermediate elims t t'
        | TyAbs _ _ _, _ => None
        | LamAbs v ty t, LamAbs _ _ t' => LamAbs v ty <$> inlined_intermediate elims t t'
        | LamAbs _ _ _, _ => None
        | Apply t1 t2, Apply t1' t2' => Apply <$> inlined_intermediate elims t1 t1' <*> inlined_intermediate elims t2 t2'
        | Apply _ _, _ => None
        | Constant c, Constant _ => pure (Constant c)
        | Constant _, _ => None
        | Builtin f, Builtin _ => pure (Builtin f)
        | Builtin _, _ => None
        | TyInst t ty, TyInst t' _ => TyInst <$> inlined_intermediate elims t t' <*> pure ty
        | TyInst _ _, _ => None
        | Error ty, Error _ => pure (Error ty)
        | Error _, _ => None
        | IWrap ty1 ty2 t, IWrap _ _ t' => IWrap ty1 ty2 <$> inlined_intermediate elims t t'
        | IWrap _ _ _ , _ => None
        | Unwrap t, Unwrap t' => Unwrap <$> inlined_intermediate elims t t'
        | Unwrap _, _ => None
        | Constr i T ts, Constr _ _ ts' => Constr i T <$> sequence_options (zip_with (inlined_intermediate elims) ts ts')
        | Constr _ _ _, _ => None
        | Case T t ts, Case _ t' ts' => Case T <$> inlined_intermediate elims t t' <*> sequence_options (zip_with (inlined_intermediate elims) ts ts')
        | Case _ _ _, _ => None
      end
  with inlined_intermediate_binding (elims : list name) (b : binding) (bs_post : list binding) : option binding
   := match b with
    | TermBind str (VarDecl v ty) t =>
        let b_post := find
              (fun b' => match b with
                | TermBind _ (VarDecl v' _) _ => String.eqb v v'
                | _ => false
                end) bs_post
        in match b_post with
          | Some (TermBind _ _ t') =>
              TermBind str (VarDecl v ty) <$> inlined_intermediate elims t t'
          | _ => None
          end
    | TypeBind v ty => pure (TypeBind v ty)
    | DatatypeBind dt => pure (DatatypeBind dt)
    end
  .


End InlineOnly.

