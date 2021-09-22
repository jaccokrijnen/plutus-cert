Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.



(** * Free (type) variables and closedness *)

(** ** Types *)
Inductive appears_free_in_Ty : tyname -> Ty -> Prop :=
  | AFI_TyVar : forall X,
      appears_free_in_Ty X (Ty_Var X)
  | AFI_TyFun1 : forall X T1 T2,
      appears_free_in_Ty X T1 ->
      appears_free_in_Ty X (Ty_Fun T1 T2)
  | AFI_TyFun2 : forall X T1 T2,
      appears_free_in_Ty X T2 ->
      appears_free_in_Ty X (Ty_Fun T1 T2)
  | AFI_TyIFix1 : forall X F T,
      appears_free_in_Ty X F ->
      appears_free_in_Ty X (Ty_IFix F T)
  | AFI_TyIFix2 : forall X F T,
      appears_free_in_Ty X T ->
      appears_free_in_Ty X (Ty_IFix F T)
  | AFI_TyForall : forall X bX K T,
      X <> bX ->
      appears_free_in_Ty X T ->
      appears_free_in_Ty X (Ty_Forall bX K T)
  | AFI_TyLam : forall X bX K T,
      X <> bX ->
      appears_free_in_Ty X T ->
      appears_free_in_Ty X (Ty_Lam bX K T)
  | AFI_TyApp1 : forall X T1 T2,
      appears_free_in_Ty X T1 ->
      appears_free_in_Ty X (Ty_App T1 T2)
  | AFI_TyApp2 : forall X T1 T2,
      appears_free_in_Ty X T2 ->
      appears_free_in_Ty X (Ty_App T1 T2)
  .

#[export] Hint Constructors 
  appears_free_in_Ty 
  : core.

Definition closed_Ty (T : Ty) :=
  forall X, ~(appears_free_in_Ty X T).



(** ** Terms *)

(** *** Utilities *)
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

(** *** AFI inductive datatype *)
Inductive appears_free_in_Term : name -> Term -> Prop :=
  | AFIT_Let : forall x r bs t,
      ~(In x (term_vars_bound_by_bindings bs)) ->
      appears_free_in_Term x t ->
      appears_free_in_Term x (Let r bs t)
  | AFIT_LetNonRec : forall x bs t,
      appears_free_in_Term__bindings_nonrec x bs ->
      appears_free_in_Term x (Let NonRec bs t)
  | AFIT_LetRec : forall x bs t,
      ~(In x (term_vars_bound_by_bindings bs)) ->
      appears_free_in_Term__bindings_rec x bs ->
      appears_free_in_Term x (Let Rec bs t)
  | AFIT_Var : forall x,
      appears_free_in_Term x (Var x)
  | AFIT_TyAbs : forall x bX K t0,
      appears_free_in_Term x t0 ->
      appears_free_in_Term x (TyAbs bX K t0)
  | AFIT_LamAbs : forall x bx T t0,
      x <> bx ->
      appears_free_in_Term x t0 ->
      appears_free_in_Term x (LamAbs bx T t0)
  | AFIT_Apply1 : forall x t1 t2,
      appears_free_in_Term x t1 ->
      appears_free_in_Term x (Apply t1 t2)
  | AFIT_Apply2 : forall x t1 t2,
      appears_free_in_Term x t2 ->
      appears_free_in_Term x (Apply t1 t2)
  | AFIT_TyInst : forall x t0 T,
      appears_free_in_Term x t0 ->
      appears_free_in_Term x (TyInst t0 T)
  | AFIT_IWrap : forall x F T t0,
      appears_free_in_Term x t0 ->
      appears_free_in_Term x (IWrap F T t0)
  | AFIT_Unwrap : forall x t0,
      appears_free_in_Term x t0 ->
      appears_free_in_Term x (Unwrap t0)

with appears_free_in_Term__bindings_nonrec : name -> list Binding -> Prop :=
  | AFIT_ConsB1_NonRec : forall x b bs,
      appears_free_in_Term__binding x b ->
      appears_free_in_Term__bindings_nonrec x (b :: bs)
  | AFIT_ConsB2_NonRec : forall x b bs,
      ~(In x (term_vars_bound_by_binding b)) ->
      appears_free_in_Term__bindings_nonrec x bs ->
      appears_free_in_Term__bindings_nonrec x (b :: bs)

with appears_free_in_Term__bindings_rec : name -> list Binding -> Prop :=
  | AFIT_ConsB1_Rec : forall x b bs,
      appears_free_in_Term__binding x b ->
      appears_free_in_Term__bindings_rec x (b :: bs)
  | AFIT_ConsB2_Rec : forall x b bs,
      appears_free_in_Term__bindings_rec x bs ->
      appears_free_in_Term__bindings_rec x (b :: bs)

with appears_free_in_Term__binding : name -> Binding -> Prop :=
  | AFIT_TermBind : forall x s vd t0,
      appears_free_in_Term x t0 ->
      appears_free_in_Term__binding x (TermBind s vd t0)
  .

#[export] Hint Constructors 
  appears_free_in_Term 
  appears_free_in_Term__bindings_nonrec
  appears_free_in_Term__bindings_rec
  appears_free_in_Term__binding 
  : core.

(** *** Closedness of Terms *)
Definition closed_Term (t : Term) :=
  forall x, ~(appears_free_in_Term x t).



(** ** Type annotations *)
Definition tyvars_bound_by_binding (b : NamedTerm.Binding) : list tyname :=
  match b with
  | TermBind _ (VarDecl x _) _ => nil
  | TypeBind (TyVarDecl X _) _ => cons X nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => cons X nil
  end.

Definition tyvars_bound_by_bindings (bs : list NamedTerm.Binding) : list tyname := List.concat (map tyvars_bound_by_binding bs).


(** *** AFIA inductive datatype *)
Inductive appears_free_in_Annotation (X : tyname) : Term -> Prop :=
  | AFIA_Let : forall r bs t,
      ~(In X (tyvars_bound_by_bindings bs)) ->
      appears_free_in_Annotation X t ->
      appears_free_in_Annotation X (Let r bs t)
  | AFIA_LetNonRec : forall bs t,
      appears_free_in_Annotation__bindings_nonrec X bs ->
      appears_free_in_Annotation X (Let NonRec bs t)
  | AFIA_LetRec : forall bs t,
      ~(In X (tyvars_bound_by_bindings bs)) ->
      appears_free_in_Annotation__bindings_rec X bs ->
      appears_free_in_Annotation X (Let Rec bs t)
  | AFIA_TyAbs : forall bX K t0,
      X <> bX ->
      appears_free_in_Annotation X t0 ->
      appears_free_in_Annotation X (TyAbs bX K t0)
  | AFIA_LamAbs1 : forall bx T t0,
      appears_free_in_Ty X T ->
      appears_free_in_Annotation X (LamAbs bx T t0)
  | AFIA_LamAbs2 : forall bx T t0,
      appears_free_in_Annotation X t0 ->
      appears_free_in_Annotation X (LamAbs bx T t0)
  | AFIA_Apply1 : forall t1 t2,
      appears_free_in_Annotation X t1 ->
      appears_free_in_Annotation X (Apply t1 t2)
  | AFIA_Apply2 : forall t1 t2,
      appears_free_in_Annotation X t2 ->
      appears_free_in_Annotation X (Apply t1 t2)
  | AFIA_TyInst1 : forall t0 T,
      appears_free_in_Ty X T ->
      appears_free_in_Annotation X (TyInst t0 T)
  | AFIA_TyInst2 : forall t0 T,
      appears_free_in_Annotation X t0 ->
      appears_free_in_Annotation X (TyInst t0 T)
  | AFIA_Error : forall T,
      appears_free_in_Ty X T ->
      appears_free_in_Annotation X (Error T)
  | AFIA_IWrap1 : forall F T t0,
      appears_free_in_Ty X F ->
      appears_free_in_Annotation X (IWrap F T t0)
  | AFIA_IWrap2 : forall F T t0,
      appears_free_in_Ty X T ->
      appears_free_in_Annotation X (IWrap F T t0)
  | AFIA_IWrap3 : forall F T t0,
      appears_free_in_Annotation X t0 ->
      appears_free_in_Annotation X (IWrap F T t0)
  | AFIA_Unwrap : forall t0,
      appears_free_in_Annotation X t0 ->
      appears_free_in_Annotation X (Unwrap t0)

with appears_free_in_Annotation__bindings_nonrec (X : tyname) : list Binding -> Prop :=
  | AFIA_ConsB1_NonRec : forall b bs,
      appears_free_in_Annotation__binding X b ->
      appears_free_in_Annotation__bindings_nonrec X (b :: bs)
  | AFIA_ConsB2_NonRec : forall b bs,
      ~(In X (tyvars_bound_by_binding b)) ->
      appears_free_in_Annotation__bindings_nonrec X bs ->
      appears_free_in_Annotation__bindings_nonrec X (b :: bs)

with appears_free_in_Annotation__bindings_rec (X : tyname) : list Binding -> Prop :=
  | AFIA_ConsB1_Rec : forall b bs,
      appears_free_in_Annotation__binding X b ->
      appears_free_in_Annotation__bindings_rec X (b :: bs)
  | AFIA_ConsB2_Rec : forall b bs,
      appears_free_in_Annotation__bindings_rec X bs ->
      appears_free_in_Annotation__bindings_rec X (b :: bs)

with appears_free_in_Annotation__binding (X: tyname) : Binding -> Prop :=
  (* TODO *) .


#[export] Hint Constructors 
  appears_free_in_Annotation 
  appears_free_in_Annotation__bindings_nonrec
  appears_free_in_Annotation__bindings_rec
  appears_free_in_Annotation__binding : core. 

(** *** Closedness of type annotations *)
Definition closed_Annotation (t : Term) :=
  forall x, ~(appears_free_in_Term x t).



(** * Full closedness of terms (and type annotations) *)
Definition closed (t : Term) :=
  (forall x, ~(appears_free_in_Term x t)) /\ (forall X, ~(appears_free_in_Annotation X t)).