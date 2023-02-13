From Coq Require Import
  Strings.String
  Lists.List
  Arith.PeanoNat
  Strings.Ascii
  Program.Basics
  .

Import ListNotations.
Local Open Scope string_scope.

From PlutusCert Require Import
  Util
  Util.List
  Language.PlutusIR
  Language.PlutusIR.Folds
  .

Import NamedTerm.


Inductive appears_bound_in_ty (X: tyname) : Ty -> Prop :=
  | ABI_Ty_TyFun1 : forall T1 T2,
      appears_bound_in_ty X T1 ->
      appears_bound_in_ty X (Ty_Fun T1 T2)
  | ABI_Ty_TyFun2 : forall T1 T2,
      appears_bound_in_ty X T2 ->
      appears_bound_in_ty X (Ty_Fun T1 T2)
  | ABI_Ty_TyIFix1 : forall F T,
      appears_bound_in_ty X F ->
      appears_bound_in_ty X (Ty_IFix F T)
  | ABI_Ty_TyIFix2 : forall F T,
      appears_bound_in_ty X T ->
      appears_bound_in_ty X (Ty_IFix F T)
  | ABI_Ty_TyForall1 : forall K T,
      appears_bound_in_ty X (Ty_Forall X K T)
  | ABI_Ty_TyForall2 : forall Y K T,
      X <> Y ->
      appears_bound_in_ty Y T ->
      appears_bound_in_ty X (Ty_Forall Y K T)
  | ABI_Ty_TyLam1 : forall K T,
      appears_bound_in_ty X (Ty_Lam X K T)
  | ABI_Ty_TyLam2 : forall Y K T,
      X <> Y ->
      appears_bound_in_ty Y T ->
      appears_bound_in_ty X (Ty_Lam Y K T)
  | ABI_Ty_TyApp1 : forall T1 T2,
      appears_bound_in_ty X T1 ->
      appears_bound_in_ty X (Ty_App T1 T2)
  | ABI_Ty_TyApp2 : forall T1 T2,  
      appears_bound_in_ty X T2 ->
      appears_bound_in_ty X (Ty_App T1 T2).


Fixpoint bv_constructors (cs : list constructor) : list string :=
  match cs with
  | [] => []
  | Constructor (VarDecl x _) _ :: cs' => x :: bv_constructors cs'
  end.

Inductive appears_bound_in_tm (x : name) : Term -> Prop :=
  | ABI_Tm_LamAbs1 : forall T t,
      appears_bound_in_tm x (LamAbs x T t)
  | ABI_Tm_LamAbs2 : forall y T t,
      x <> y ->
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (LamAbs y T t)
  | ABI_Tm_Apply1 : forall t1 t2,
      appears_bound_in_tm x t1 ->
      appears_bound_in_tm x (Apply t1 t2)
  | ABI_Tm_Apply2 : forall t1 t2,
      appears_bound_in_tm x t2 ->
      appears_bound_in_tm x (Apply t1 t2)
  | ABI_Tm_TyAbs : forall X K t,
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (TyAbs X K t)
  | ABI_Tm_TyInst : forall t T,
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (TyInst t T)
  | ABI_Tm_IWrap : forall F T t,
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (IWrap F T t)
  | ABI_Tm_Unwrap : forall t,
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (Unwrap t)
  | ABI_Tm_Let_Nil : forall recty t0,
      appears_bound_in_tm x t0 ->
      appears_bound_in_tm x (Let recty nil t0)
  | ABI_Tm_Let_Cons : forall recty b bs t0,
      appears_bound_in_tm x (Let recty bs t0) ->
      appears_bound_in_tm x (Let recty (b :: bs) t0)
  | ABI_Tm_Let_TermBind1 : forall recty stricty T t bs t0,
      appears_bound_in_tm x (Let recty (TermBind stricty (VarDecl x T) t :: bs) t0)
  | ABI_Tm_Let_TermBind2 : forall recty stricty y T t bs t0,
      x <> y ->
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (Let recty (TermBind stricty (VarDecl y T) t :: bs) t0)
  | ABI_Tm_Let_DatatypeBind : forall recty XK YKs mfunc cs t0 bs,
      NameIn x (mfunc :: bv_constructors cs) ->
      appears_bound_in_tm x (Let recty (DatatypeBind (Datatype XK YKs mfunc cs) :: bs) t0) 
      .


Inductive appears_bound_in_ann (X : tyname) : Term -> Prop :=
  | ABI_Ann_LamAbs1 : forall x T t,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (LamAbs x T t)
  | ABI_Ann_LamAbs : forall x T t,
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (LamAbs x T t)
  | ABI_Ann_Apply1 : forall t1 t2,
      appears_bound_in_ann X t1 ->
      appears_bound_in_ann X (Apply t1 t2)
  | ABI_Ann_Apply2 : forall t1 t2,
      appears_bound_in_ann X t2 ->
      appears_bound_in_ann X (Apply t1 t2)
  | ABI_Ann_TyAbs1 : forall K t,
      appears_bound_in_ann X (TyAbs X K t)
  | ABI_Ann_TyAbs2 : forall Y K t,
      X <> Y ->
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (TyAbs Y K t)
  | ABI_Ann_TyInst1 : forall t T,
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (TyInst t T)
  | ABI_Ann_TyInst2 : forall t T,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (TyInst t T)
  | ABI_Ann_IWrap1 : forall F T t,
      appears_bound_in_ty X F ->
      appears_bound_in_ann X (IWrap F T t)
  | ABI_Ann_IWrap2 : forall F T t,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (IWrap F T t)
  | ABI_Ann_IWrap3 : forall F T t,
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (IWrap F T t)
  | ABI_Ann_Unwrap : forall t,
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (Unwrap t)
  | ABI_Ann_Error : forall T,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (Error T)
  | ABI_Ann_Let_Nil : forall recty t0,
      appears_bound_in_ann X t0 ->
      appears_bound_in_ann X (Let recty nil t0)
  | ABI_Ann_Let_Cons : forall recty b bs t0,
      appears_bound_in_ann X (Let recty bs t0) ->
        appears_bound_in_ann X (Let recty (b :: bs) t0)
  | ABI_Ann_Let_TermBind1 : forall recty stricty x T t bs t0,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (Let recty (TermBind stricty (VarDecl x T) t :: bs) t0)
  | ABI_Ann_Let_TermBind2 : forall recty stricty y T t bs t0,
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (Let recty (TermBind stricty (VarDecl y T) t :: bs) t0)
  | ABI_Ann_Let_TypeBind1 : forall recty K T bs t0,
      appears_bound_in_ann X (Let recty (TypeBind (TyVarDecl X K) T :: bs) t0)
  | ABI_Ann_Let_TypeBind2 : forall recty Y K T bs t0,
      X <> Y ->
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (Let recty (TypeBind (TyVarDecl Y K) T :: bs) t0)
  | ABI_Ann_Let_DatatypeBind : forall recty K YKs mfunc cs t0 bs,
      appears_bound_in_ann X (Let recty (DatatypeBind (Datatype (TyVarDecl X K) YKs mfunc cs) :: bs) t0) 
  .


#[export] Hint Constructors 
  appears_bound_in_ty
  appears_bound_in_tm
  appears_bound_in_ann
  : core.


Section BoundVars.
  Context
    {var tyvar : Set}
    (var_eqb : var -> var -> bool)
    .

Definition term' := term var tyvar var tyvar.
Definition binding' := binding var tyvar var tyvar.
Definition constructor' := constr tyvar var tyvar.

(** Retrieve bound term variable bindings *)

Definition bvc (c : constructor') : var :=
  match c with
  | Constructor (VarDecl x _) _ => x
  end.

Definition bvb (b : binding') : list var :=
  match b with
  | TermBind _ (VarDecl x _) _ => cons x nil
  | TypeBind (TyVarDecl X _) _ => nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => matchFunc :: (rev (map bvc cs))
  end.

Definition bvbs (bs : list binding') : list var := List.concat (map bvb bs).


Fixpoint boundTerms_bindings (bs : list binding') : list (var * term var tyvar var tyvar) := match bs with
    | ((TermBind _ (VarDecl v _) t) :: bs) => (v, t) :: boundTerms_bindings bs
    | (_ :: bs) => boundTerms_bindings bs
    | nil       => nil
    end.

(** Retrieve bound type variable bindings *)

Definition btvb (b : binding') : list tyvar :=
  match b with
  | TermBind _ (VarDecl x _) _ => nil
  | TypeBind (TyVarDecl X _) _ => cons X nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => cons X nil
  end.

Definition btvbs (bs : list binding') : list tyvar := List.concat (map btvb bs).

Fixpoint bound_vars (t : term') : list var :=
 match t with
   | Let rec bs t => concat (map bound_vars_binding bs) ++ bound_vars t
   | (LamAbs n ty t)   => n :: (bound_vars t)
   | (Var n)           => []
   | (TyAbs n k t)     => bound_vars t
   | (Apply s t)       => bound_vars s ++ bound_vars t
   | (TyInst t ty)     => bound_vars t
   | (IWrap ty1 ty2 t) => bound_vars t
   | (Unwrap t)        => bound_vars t
   | (Error ty)        => []
   | (Constant v)      => []
   | (Builtin f)       => []
   end
with bound_vars_binding (b : binding') : list var := match b with
  | TermBind _ (VarDecl v _) t => [v] ++ bound_vars t
  | DatatypeBind (Datatype _ _ matchf constructors ) => [matchf] ++ map constructorName constructors
  | _                          => []
  end.

Definition bound_vars_bindings := @concat _ ∘ map bound_vars_binding.

End BoundVars.

Definition P_Term (t : Term) : Prop := Forall (fun v => appears_bound_in_tm v t) (bound_vars t).
Definition P_Binding (b : Binding) := Forall (fun v => forall t bs recty, appears_bound_in_tm v (Let recty (b :: bs) t)) (bound_vars_binding b).

Lemma bound_vars_appears_bound_in_tm : (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof with eauto using appears_bound_in_tm.
  apply Term__multind with (P := P_Term) (Q := P_Binding).
  all: unfold P_Term...
  - intros.
    unfold P_Term.
    apply Forall_app.
    split.
    + unfold P_Binding in H.
      induction bs.
      * constructor.
      * simpl. 
        apply Forall_app.
        split.
          ** apply ForallP_Forall in H.
             apply Forall_inv in H.
             eapply Forall_impl.
               2: { apply H. }
               auto.
          ** apply ForallP_Forall in H.
             apply Forall_inv_tail in H.
             apply ForallP_Forall in H.
             apply IHbs in H.
             eapply Forall_impl.
             intros b. apply ABI_Tm_Let_Cons.
             auto.

    + unfold P_Term in *.
      eapply Forall_impl with (P := fun v => appears_bound_in_tm v t)...
      eauto using appears_bound_in_tm.
      intros.
      induction bs...
      apply ForallP_Forall in H.
      apply Forall_inv_tail in H.
      apply ForallP_Forall in H...
  - intros.
    cbv.
    auto.
  - intros.
    eapply Forall_impl. 2: exact H.
    eauto.
  - intros.
    eapply Forall_cons...
    eapply Forall_impl with (P := fun a => appears_bound_in_tm a t0)...
    intros. 
      destruct (string_dec a s).
      * subst. apply ABI_Tm_LamAbs1.
      * apply ABI_Tm_LamAbs2...

  (* Common pattern: only need to prove an implication using a ABI_Tm rule *)
  Ltac tac rule :=
    intros; eapply Forall_impl; [intros a; apply rule | auto].

  - intros.
    apply Forall_app. split.
      + tac ABI_Tm_Apply1.
      + tac ABI_Tm_Apply2.
  - intros. cbv. auto.
  - intros. cbv. auto.
  - tac ABI_Tm_TyInst.
  - intros. cbv. auto.
  - tac ABI_Tm_IWrap.
  - tac ABI_Tm_Unwrap.
  - intros.
    unfold P_Binding.
    intros.
    cbv.
    destruct v.
    eapply Forall_cons.
      + intros...
      + intros. eapply Forall_impl with (P := fun v => appears_bound_in_tm v t)...
        intros. destruct (string_dec a s0); subst...
  - unfold P_Binding.
    intros.
    cbv...
  - unfold P_Binding.
    cbv.
    destruct dtd.
    apply Forall_cons.
    + intros.
      apply ABI_Tm_Let_DatatypeBind.
      constructor...
    + apply Forall_forall.
      intros.
      apply ABI_Tm_Let_DatatypeBind.
      apply NameIn_In_string_equal.
      apply in_cons.
      induction l0...
      destruct a.
      destruct v.
      induction H; subst; simpl...
Qed.

Inductive decide {a : Type} (P : a -> Type) (x : a) :=
  | dec_False : notT (P x) -> decide P x
  | dec_True  : P x        -> decide P x
  .

#[local]
Hint Constructors decide : core.

Definition dec_all a P (xs : list a) : ForallT (decide P) xs -> decide (ForallT P) xs.
Proof.
Admitted.
