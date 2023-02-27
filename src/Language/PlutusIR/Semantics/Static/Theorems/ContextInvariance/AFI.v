From PlutusCert Require Import
  Util.In
  Language.PlutusIR
  Language.PlutusIR.Analysis.BoundVars
  Language.PlutusIR.Semantics.Static.Typing.

Import NamedTerm.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Inductive appears_free_in_ty (X : tyname) : Ty -> Prop :=
  | AFI_TyVar :
      appears_free_in_ty X (Ty_Var X)
  | AFI_TyFun1 : forall T1 T2,
      appears_free_in_ty X T1 ->
      appears_free_in_ty X (Ty_Fun T1 T2)
  | AFI_TyFun2 : forall T1 T2,
      appears_free_in_ty X T2 ->
      appears_free_in_ty X (Ty_Fun T1 T2)
  | AFI_TyIFix1 : forall F T,
      appears_free_in_ty X F ->
      appears_free_in_ty X (Ty_IFix F T)
  | AFI_TyIFix2 : forall F T,
      appears_free_in_ty X T ->
      appears_free_in_ty X (Ty_IFix F T)
  | AFI_TyForall : forall bX K T,
      X <> bX ->
      appears_free_in_ty X T ->
      appears_free_in_ty X (Ty_Forall bX K T)
  | AFI_TyLam : forall bX K T,
      X <> bX ->
      appears_free_in_ty X T ->
      appears_free_in_ty X (Ty_Lam bX K T)
  | AFI_TyApp1 : forall T1 T2,
      appears_free_in_ty X T1 ->
      appears_free_in_ty X (Ty_App T1 T2)
  | AFI_TyApp2 : forall T1 T2,
      appears_free_in_ty X T2 ->
      appears_free_in_ty X (Ty_App T1 T2)
.



Definition closed_ty (T : Ty) :=
  forall X, ~(appears_free_in_ty X T).


Definition bvb' (b : Binding) := bvb b.
Definition bvbs' (bs : list Binding) := bvbs bs.

Inductive appears_free_in_tm : name -> Term -> Prop :=
  | AFIT_Let : forall x r bs t,
      ~ (NameIn x (bvbs' bs)) ->
      appears_free_in_tm x t ->
      appears_free_in_tm x (Let r bs t)
  | AFIT_LetNonRec : forall x bs t,
      appears_free_in_tm__bindings_nonrec x bs ->
      appears_free_in_tm x (Let NonRec bs t)
  | AFIT_LetRec : forall x bs t,
      ~ NameIn x (bvbs' bs) ->
      appears_free_in_tm__bindings_rec x bs ->
      appears_free_in_tm x (Let Rec bs t)
  | AFIT_Var : forall x,
      appears_free_in_tm x (Var x)
  | AFIT_TyAbs : forall x bX K t0,
      appears_free_in_tm x t0 ->
      appears_free_in_tm x (TyAbs bX K t0)
  | AFIT_LamAbs : forall x bx T t0,
      x <> bx ->
      appears_free_in_tm x t0 ->
      appears_free_in_tm x (LamAbs bx T t0)
  | AFIT_Apply1 : forall x t1 t2,
      appears_free_in_tm x t1 ->
      appears_free_in_tm x (Apply t1 t2)
  | AFIT_Apply2 : forall x t1 t2,
      appears_free_in_tm x t2 ->
      appears_free_in_tm x (Apply t1 t2)
  | AFIT_TyInst : forall x t0 T,
      appears_free_in_tm x t0 ->
      appears_free_in_tm x (TyInst t0 T)
  | AFIT_IWrap : forall x F T t0,
      appears_free_in_tm x t0 ->
      appears_free_in_tm x (IWrap F T t0)
  | AFIT_Unwrap : forall x t0,
      appears_free_in_tm x t0 ->
      appears_free_in_tm x (Unwrap t0)

with appears_free_in_tm__bindings_nonrec : name -> list Binding -> Prop :=
  | AFIT_ConsB1_NonRec : forall x b bs,
      appears_free_in_tm__binding x b ->
      appears_free_in_tm__bindings_nonrec x (b :: bs)
  | AFIT_ConsB2_NonRec : forall x b bs,
      ~ NameIn x (bvb' b) ->
      appears_free_in_tm__bindings_nonrec x bs ->
      appears_free_in_tm__bindings_nonrec x (b :: bs)

with appears_free_in_tm__bindings_rec : name -> list Binding -> Prop :=       
  | AFIT_ConsB1_Rec : forall x b bs,
      appears_free_in_tm__binding x b ->
      appears_free_in_tm__bindings_rec x (b :: bs)
  | AFIT_ConsB2_Rec : forall x b bs,
      appears_free_in_tm__bindings_rec x bs ->
      appears_free_in_tm__bindings_rec x (b :: bs)

with appears_free_in_tm__binding : name -> Binding -> Prop :=
  | AFIT_TermBind : forall x s vd t0,
      appears_free_in_tm x t0 ->
      appears_free_in_tm__binding x (TermBind s vd t0)
  .


Definition closed_tm (t : Term) :=
  forall x, ~(appears_free_in_tm x t).



Definition map_fst_rev_map_fromDecl ZKs := (map fst (rev (map fromDecl ZKs))).
Definition btvb' (b : Binding) := btvb b.
Definition btvbs' (bs : list Binding) := btvbs bs.


Inductive appears_free_in_ann (X : tyname) : Term -> Prop :=
  | AFIA_Let : forall r bs t,
      ~ NameIn X (btvbs' bs) ->
      appears_free_in_ann X t ->
      appears_free_in_ann X (Let r bs t)
  | AFIA_LetNonRec : forall bs t,
      appears_free_in_ann__bindings_nonrec X bs ->
      appears_free_in_ann X (Let NonRec bs t)
  | AFIA_LetRec : forall bs t,
      ~ NameIn X (btvbs' bs) ->
      appears_free_in_ann__bindings_rec X bs ->
      appears_free_in_ann X (Let Rec bs t)
  | AFIA_TyAbs : forall bX K t0,
      X <> bX ->
      appears_free_in_ann X t0 ->
      appears_free_in_ann X (TyAbs bX K t0)
  | AFIA_LamAbs1 : forall bx T t0,
      appears_free_in_ty X T ->
      appears_free_in_ann X (LamAbs bx T t0)
  | AFIA_LamAbs2 : forall bx T t0,
      appears_free_in_ann X t0 ->
      appears_free_in_ann X (LamAbs bx T t0)
  | AFIA_Apply1 : forall t1 t2,
      appears_free_in_ann X t1 ->
      appears_free_in_ann X (Apply t1 t2)
  | AFIA_Apply2 : forall t1 t2,
      appears_free_in_ann X t2 ->
      appears_free_in_ann X (Apply t1 t2)
  | AFIA_TyInst1 : forall t0 T,
      appears_free_in_ty X T ->
      appears_free_in_ann X (TyInst t0 T)
  | AFIA_TyInst2 : forall t0 T,
      appears_free_in_ann X t0 ->
      appears_free_in_ann X (TyInst t0 T)
  | AFIA_IWrap1 : forall F T t0,
      appears_free_in_ty X F ->
      appears_free_in_ann X (IWrap F T t0)
  | AFIA_IWrap2 : forall F T t0,
      appears_free_in_ty X T ->
      appears_free_in_ann X (IWrap F T t0)
  | AFIA_IWrap3 : forall F T t0,
      appears_free_in_ann X t0 ->
      appears_free_in_ann X (IWrap F T t0)
  | AFIA_Unwrap : forall t0,
      appears_free_in_ann X t0 ->
      appears_free_in_ann X (Unwrap t0)

with appears_free_in_ann__constructor (X : tyname) : constructor -> Prop :=
  | AFIA_Constructor : forall x T ar Targs Tr,
      (Targs, Tr) = splitTy T ->
      (exists U, In U Targs /\ appears_free_in_ty X U) ->
      appears_free_in_ann__constructor X (Constructor (VarDecl x T) ar)

with appears_free_in_ann__bindings_nonrec (X : tyname) : list Binding -> Prop :=
  | AFIA_ConsB1_NonRec : forall b bs,
      appears_free_in_ann__binding X b ->
      appears_free_in_ann__bindings_nonrec X (b :: bs)
  | AFIA_ConsB2_NonRec : forall b bs,
      ~ NameIn X (btvb' b) ->
      appears_free_in_ann__bindings_nonrec X bs ->
      appears_free_in_ann__bindings_nonrec X (b :: bs)

with appears_free_in_ann__bindings_rec (X : tyname) : list Binding -> Prop :=
  | AFIA_ConsB1_Rec : forall b bs,
      appears_free_in_ann__binding X b ->
      appears_free_in_ann__bindings_rec X (b :: bs)
  | AFIA_ConsB2_Rec : forall b bs,
      appears_free_in_ann__bindings_rec X bs ->
      appears_free_in_ann__bindings_rec X (b :: bs)

with appears_free_in_ann__binding (X: tyname) : Binding -> Prop :=
  | AFIA_TermBind1 : forall s x T t0,
      appears_free_in_ty X T ->
      appears_free_in_ann__binding X (TermBind s (VarDecl x T) t0)
  | AFIA_TermBind2 : forall s x T t0,
      appears_free_in_ann X t0 ->
      appears_free_in_ann__binding X (TermBind s (VarDecl x T) t0)
  | AFI_TypeBind : forall Y K T,
      appears_free_in_ty X T ->
      appears_free_in_ann__binding X (TypeBind (TyVarDecl Y K) T)
  | AFI_DatatypeBind1 : forall Y K ZKs matchFunc c cs,
      ~ NameIn X (map_fst_rev_map_fromDecl ZKs) ->
      appears_free_in_ann__constructor X c ->
      appears_free_in_ann__binding X (DatatypeBind (Datatype (TyVarDecl Y K) ZKs matchFunc (c :: cs)))
  .


Definition closed_ann (t : Term) :=
  forall x, ~(appears_free_in_ann x t).


#[export] Hint Constructors 
  appears_free_in_ty
  : core.

#[export] Hint Constructors 
  appears_free_in_tm 
  appears_free_in_tm__bindings_nonrec
  appears_free_in_tm__bindings_rec
  appears_free_in_tm__binding 
  : core.

#[export] Hint Constructors 
  appears_free_in_ann 
  appears_free_in_ann__constructor
  appears_free_in_ann__bindings_nonrec
  appears_free_in_ann__bindings_rec
  appears_free_in_ann__binding : core. 

(** Full closedness of terms (and type annotations) *)
Definition closed (t : Term) :=
  (forall x, ~(appears_free_in_tm x t)) /\ (forall X, ~(appears_free_in_ann X t)).
