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
  Language.PlutusIR.Folds.

Import NamedTerm.

From QuickChick Require Import QuickChick.


Inductive appears_bound_in_ty (X: tyname) : Ty -> Prop :=
  | ABIT_TyFun1 : forall T1 T2,
      appears_bound_in_ty X T1 ->
      appears_bound_in_ty X (Ty_Fun T1 T2)
  | ABIT_TyFun2 : forall T1 T2,
      appears_bound_in_ty X T2 ->
      appears_bound_in_ty X (Ty_Fun T1 T2)
  | ABIT_TyIFix1 : forall F T,
      appears_bound_in_ty X F ->
      appears_bound_in_ty X (Ty_IFix F T)
  | ABIT_TyIFix2 : forall F T,
      appears_bound_in_ty X T ->
      appears_bound_in_ty X (Ty_IFix F T)
  | ABIT_TyForall1 : forall K T,
      appears_bound_in_ty X (Ty_Forall X K T)
  | ABIT_TyForall2 : forall Y K T,
      X <> Y ->
      appears_bound_in_ty Y T ->
      appears_bound_in_ty X (Ty_Forall Y K T)
  | ABIT_TyLam1 : forall K T,
      appears_bound_in_ty X (Ty_Lam X K T)
  | ABIT_TyLam2 : forall Y K T,
      X <> Y ->
      appears_bound_in_ty Y T ->
      appears_bound_in_ty X (Ty_Lam Y K T)
  | ABIT_TyApp1 : forall T1 T2,
      appears_bound_in_ty X T1 ->
      appears_bound_in_ty X (Ty_App T1 T2)
  | ABIT_TyApp2 : forall T1 T2,  
      appears_bound_in_ty X T2 ->
      appears_bound_in_ty X (Ty_App T1 T2).

QCDerive DecOpt for (appears_bound_in_ty x ty).  

Instance appears_bound_in_ty_DecOpt_sound x ty: DecOptSoundPos (appears_bound_in_ty x ty).
Proof. derive_sound. Qed.

Instance appears_bound_in_ty_DecOpt_complete x ty: DecOptCompletePos (appears_bound_in_ty x ty).
Proof. derive_complete. Qed.

Instance appears_bound_in_ty_DecOpt_monotonicity x ty: DecOptSizeMonotonic (appears_bound_in_ty x ty).
Proof. derive_mon. Qed.



Inductive appears_bound_in_constrs (x : name) : list constructor -> Prop :=
  | ABIC_Here  : forall t n cs,
      appears_bound_in_constrs x ((Constructor (VarDecl x t) n) :: cs)
  | ABIC_There : forall c' cs,
      appears_bound_in_constrs x cs ->
      appears_bound_in_constrs x (c' :: cs).

QCDerive DecOpt for (appears_bound_in_constrs x ls).

Instance appears_bound_in_constrs_DecOpt_sound x ty: DecOptSoundPos (appears_bound_in_constrs x ty).
Proof. derive_sound. Qed.

Instance appears_bound_in_constrs_DecOpt_complete x ty: DecOptCompletePos (appears_bound_in_constrs x ty).
Proof. derive_complete. Qed.

Instance appears_bound_in_constrs_DecOpt_monotonicity x ty: DecOptSizeMonotonic (appears_bound_in_constrs x ty).
Proof. derive_mon. Qed.



(* QuickChick will fail to derive a checker for appears_bound_in if this application
 * occurs directly in the constructor. This is because QuickChick will try and match
 * 'bv_constructor' with the variables bound by the 'forall', which will fail.
 *
 * In short, only the function is allowed to be defined outside the constructor, and
 * any variables applied to the function should be bound as quantified variables.
 *)

Inductive appears_bound_in_tm (x : name) : Term -> Prop :=
  | ABITM_LamAbs1 : forall T t,
      appears_bound_in_tm x (LamAbs x T t)
  | ABITM_LamAbs2 : forall y T t,
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (LamAbs y T t)
  | ABITM_Apply1 : forall t1 t2,
      appears_bound_in_tm x t1 ->
      appears_bound_in_tm x (Apply t1 t2)
  | ABITM_Apply2 : forall t1 t2,
      appears_bound_in_tm x t2 ->
      appears_bound_in_tm x (Apply t1 t2)
  | ABITM_TyAbs : forall X K t,
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (TyAbs X K t)
  | ABITM_TyInst : forall t T,
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (TyInst t T)
  | ABITM_IWrap : forall F T t,
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (IWrap F T t)
  | ABITM_Unwrap : forall t,
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (Unwrap t)
  | ABITM_Let_Nil : forall recty t0,
      appears_bound_in_tm x t0 ->
      appears_bound_in_tm x (Let recty nil t0)
  | ABITM_Let_Cons : forall recty b bs t0,
      appears_bound_in_tm x (Let recty bs t0) ->
      appears_bound_in_tm x (Let recty (b :: bs) t0)
  | ABITM_Let_TermBind1 : forall recty stricty T t bs t0,
      appears_bound_in_tm x (Let recty (TermBind stricty (VarDecl x T) t :: bs) t0)
  | ABITM_Let_TermBind2 : forall recty stricty y T t bs t0,
      appears_bound_in_tm x t ->
      appears_bound_in_tm x (Let recty (TermBind stricty (VarDecl y T) t :: bs) t0)
  | ABITM_Let_DatatypeBindHere : forall recty XK YKs cs t0 bs,
      appears_bound_in_tm x (Let recty (DatatypeBind (Datatype XK YKs x cs) :: bs) t0)
  | ABITM_Let_DatatypeBindThere : forall recty XK YKs mfunc cs t0 bs,
      appears_bound_in_constrs x cs ->
      appears_bound_in_tm x (Let recty (DatatypeBind (Datatype XK YKs mfunc cs) :: bs) t0).
  

(* Necessary since 'In' has strings as arguments *)
(* TODO: move these elsewhere? In favour of deriving these once in a central place?*)
QCDerive EnumSized for ascii.
QCDerive EnumSized for string.

QCDerive DecOpt for (appears_bound_in_tm x tm).

(* TODO: finishes, but does not finalize a proof :( *)
Instance appears_bound_in_tm_DecOpt_sound x tm: DecOptSoundPos (appears_bound_in_tm x tm).
Proof. derive_sound. Qed.

Instance appears_bound_in_tm_DecOpt_complete x ty: DecOptCompletePos (appears_bound_in_tm x ty).
Proof. derive_complete. Qed.

Instance appears_bound_in_tm_DecOpt_monotonicity x ty: DecOptSizeMonotonic (appears_bound_in_tm x ty).
Proof. derive_mon. Qed.



Inductive appears_bound_in_ann (X : tyname) : Term -> Prop :=
  | ABIA_LamAbs1 : forall x T t,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (LamAbs x T t)
  | ABIA_LamAbs : forall x T t,
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (LamAbs x T t)
  | ABIA_Apply1 : forall t1 t2,
      appears_bound_in_ann X t1 ->
      appears_bound_in_ann X (Apply t1 t2)
  | ABIA_Apply2 : forall t1 t2,
      appears_bound_in_ann X t2 ->
      appears_bound_in_ann X (Apply t1 t2)
  | ABIA_TyAbs1 : forall K t,
      appears_bound_in_ann X (TyAbs X K t)
  | ABIA_TyAbs2 : forall Y K t,
      X <> Y ->
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (TyAbs Y K t)
  | ABIA_TyInst1 : forall t T,
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (TyInst t T)
  | ABIA_TyInst2 : forall t T,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (TyInst t T)
  | ABIA_IWrap1 : forall F T t,
      appears_bound_in_ty X F ->
      appears_bound_in_ann X (IWrap F T t)
  | ABIA_IWrap2 : forall F T t,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (IWrap F T t)
  | ABIA_IWrap3 : forall F T t,
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (IWrap F T t)
  | ABIA_Unwrap : forall t,
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (Unwrap t)
  | ABIA_Error : forall T,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (Error T)
  | ABIA_Let_Nil : forall recty t0,
      appears_bound_in_ann X t0 ->
      appears_bound_in_ann X (Let recty nil t0)
  | ABIA_Let_Cons : forall recty b bs t0,
      appears_bound_in_ann X (Let recty bs t0) ->
        appears_bound_in_ann X (Let recty (b :: bs) t0)
  | ABIA_Let_TermBind1 : forall recty stricty x T t bs t0,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (Let recty (TermBind stricty (VarDecl x T) t :: bs) t0)
  | ABIA_Let_TermBind2 : forall recty stricty y T t bs t0,
      appears_bound_in_ann X t ->
      appears_bound_in_ann X (Let recty (TermBind stricty (VarDecl y T) t :: bs) t0)
  | ABIA_Let_TypeBind1 : forall recty K T bs t0,
      appears_bound_in_ann X (Let recty (TypeBind (TyVarDecl X K) T :: bs) t0)
  | ABIA_Let_TypeBind2 : forall recty Y K T bs t0,
      appears_bound_in_ty X T ->
      appears_bound_in_ann X (Let recty (TypeBind (TyVarDecl Y K) T :: bs) t0)
  | ABIA_Let_DatatypeBind : forall recty K YKs mfunc cs t0 bs,
      appears_bound_in_ann X (Let recty (DatatypeBind (Datatype (TyVarDecl X K) YKs mfunc cs) :: bs) t0) 
      .

QCDerive DecOpt for (appears_bound_in_ann x tm).

Instance appears_bound_in_ann_decopt_sound x tm: DecOptSoundPos (appears_bound_in_ann x tm).
Proof. derive_sound. Qed.

Instance appears_bound_in_ann_DecOpt_complete x ty: DecOptCompletePos (appears_bound_in_ann x ty).
Proof. derive_complete. Qed.

Instance appears_bound_in_ann_DecOpt_monotonic x ty: DecOptSizeMonotonic (appears_bound_in_ann x ty).
Proof. derive_mon. Qed.

(* TODO: Does not terminate
Instance appears_bound_in_ann_decopt_complete x tm: DecOptCompletePos (appears_bound_in_ann x tm).
Proof. derive_complete. Qed.
*)


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
    | (b                :: bs) =>           boundTerms_bindings bs
    | nil               => nil
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
   | Let rec bs t => List.concat (map bound_vars_binding bs) ++ bound_vars t
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

Definition bound_vars_bindings := @List.concat _ ∘ map bound_vars_binding.

End BoundVars.

Definition P_Term (t : Term) : Prop := Forall (fun v => appears_bound_in_tm v t) (bound_vars t).
Definition P_Binding (b : Binding) := Forall (fun v => forall t bs recty, appears_bound_in_tm v (Let recty (b :: bs) t)) (bound_vars_binding b).

Lemma bound_vars_appears_bound_in : (forall t, P_Term t) /\ (forall b, P_Binding b).
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
             intros b. apply ABITM_Let_Cons.
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
    (*
    intros. 
      destruct (string_dec a s).
      * subst. apply ABITM_LamAbs1.
      * apply ABITM_LamAbs2...
     *)
  (* Common pattern: only need to prove an implication using a ABI rule *)
  Ltac tac rule :=
    intros; eapply Forall_impl; [intros a; apply rule | auto].
     
  - intros.
    apply Forall_app. split.
      + tac ABITM_Apply1.
      + tac ABITM_Apply2.
  - intros. cbv. auto.
  - intros. cbv. auto.
  - tac ABITM_TyInst.
  - intros. cbv. auto.
  - tac ABITM_IWrap.
  - tac ABITM_Unwrap.
  - intros.
    unfold P_Binding.
    intros.
    cbv.
    destruct v.
    eapply Forall_cons.
      + intros...
      + intros. eapply Forall_impl with (P := fun v => appears_bound_in_tm v t).
        1: { intros. apply ABITM_Let_TermBind2... }
        auto.
  - unfold P_Binding.
    intros.
    cbv...
  - unfold P_Binding.
    cbv.
    destruct dtd.
    apply Forall_cons.
    + intros.
      apply ABITM_Let_DatatypeBindHere.
    + apply Forall_forall.
      intros.
      apply ABITM_Let_DatatypeBindThere.
      induction l0; inversion H; induction a; induction v.
      * subst.
        apply ABIC_Here.
      * destruct H.
        -- subst. apply ABIC_Here.
        -- apply ABIC_There.
           apply IHl0.
           auto.
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
