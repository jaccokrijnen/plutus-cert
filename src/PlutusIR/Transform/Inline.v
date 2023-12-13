Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PeanoNat.

Import ListNotations.
From Equations Require Import Equations.
Require Import Program.
Require Import Lia.

From PlutusCert Require Import
  Util
  Util.List
  PlutusIR
  .

Import NamedTerm.

(*
Inlining considers:

  let nonrec Term bindings
  let Type bindings

The plutus compiler will _unconditionally_ inline, meaning that it will inline all occurences
and then remove the remaining dead binding.

We consider the more general case where some occurences may be inlined, but not others. As a consequence,
this pass does not consider binder elimination.

*)

(* Context of all let-bound term variables in scope *)

Inductive var_info :=
  | bound_LamAbs : var_info
  | bound_Constructor : var_info
  | bound_match : var_info
  | bound_TermBind : Term -> var_info
.

Inductive tyvar_info :=
  | bound_TypeBind : Ty -> tyvar_info
  | bound_TyAbs : tyvar_info

  | bound_Datatype_TyVar : tyvar_info
  | bound_Datatype : tyvar_info
  | bound_Forall : tyvar_info
  | bound_TyLam : tyvar_info
  .

Definition ctx := list (string * var_info).
Definition ty_ctx := list (string * tyvar_info).

Definition Binding_to_ctx (b : Binding) : ctx :=
  match b with
    | TermBind _ (VarDecl v _) t => [(v, bound_TermBind t)]
    | DatatypeBind (Datatype _ _ mfunc cs) => (mfunc, bound_match) :: map (fun '(Constructor (VarDecl x _) _) => (x, bound_Constructor)) cs
    | TypeBind _ _ => []
  end
.
Definition Binding_to_ty_ctx (b : Binding) : ty_ctx :=
  match b with
    | TypeBind (TyVarDecl α _) τ => [(α, bound_TypeBind τ)]
    | TermBind _ _ _ => []
    | DatatypeBind (Datatype (TyVarDecl x _) _ _ _) => [(x, bound_Datatype)]
  end
.

Definition Bindings_to_ctx (bs : list Binding) : ctx :=
  rev (concat (map Binding_to_ctx bs)).

Definition Bindings_to_ty_ctx (bs : list Binding) : ty_ctx :=
  rev (concat (map Binding_to_ty_ctx bs)).

Local Open Scope list_scope.

Inductive inline_Ty (Δ : ty_ctx) : Ty -> Ty -> Prop :=

   | inl_Ty_Var_1 : forall α τ τ',
      Lookup α (bound_TypeBind τ) Δ ->
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_Var α) τ

   | inl_Ty_Var_2 : forall α τ τ',
      Lookup α (bound_TypeBind τ) Δ -> (* See Note [Inlining and well-scopedness] *)
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_Var α) (Ty_Var α)

   | inl_Ty_Fun : forall σ τ σ' τ',
      inline_Ty Δ σ σ' ->
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_Fun σ τ) (Ty_Fun σ' τ')

   | inl_Ty_IFix : forall σ τ σ' τ',
      inline_Ty Δ σ σ' ->
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_IFix σ τ) (Ty_IFix σ' τ')

   | inl_Ty_Forall : forall α k τ τ',
      inline_Ty ((α, bound_Forall) :: Δ) τ τ' ->
      inline_Ty Δ (Ty_Forall α k τ) (Ty_Forall α k τ')

   | inl_Ty_Builtin : forall t,
      inline_Ty Δ (Ty_Builtin t) (Ty_Builtin t)

   | inl_Ty_Lam : forall α k τ τ',
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_Lam α k τ) (Ty_Lam α k τ')

   | Ty_App : forall σ τ σ' τ',
      inline_Ty Δ σ σ' ->
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_App σ τ) (Ty_App σ' τ')
   .

(*
This relation relates terms where inlining of let-bound variables may
have taken place. Note that the PIR inliner may also remove the let binding
when all of its occurrences have been inlined (dead code). This is not taken into account here.


Note [Inline and well-scopedness]
~~~
The constructors inl_Var_2 requires that the variable must appear in Γ. This
ensures that Δ and Γ always contain the free variables of the related terms.
The inline relation implies well-scopedness of both pre- and post-term.

This makes it easier to prove semantics preservation: we need to reuse that fact
that substitution on a closed term is the identity.

*)
Inductive inline (Δ : ty_ctx) (Γ : ctx) : Term -> Term -> Prop :=
  | inl_Var_1 : forall v t_v,
      Lookup v (bound_TermBind t_v) Γ ->
      inline Δ Γ (Var v) t_v

  | inl_Var_2 : forall v info,
      Lookup v info Γ -> (* See Note [Inline and well-scopedness] *)
      inline Δ Γ (Var v) (Var v)

  | inl_Let_Rec : forall Γ_bs Δ_bs bs bs' t t',
      Γ_bs = Bindings_to_ctx bs ->
      Δ_bs = Bindings_to_ty_ctx bs ->
      inline_Bindings_Rec (Δ_bs ++ Δ) (Γ_bs ++ Γ) (Let Rec bs t) (Let Rec bs' t') ->
      inline Δ Γ (Let Rec bs t) (Let Rec bs' t')

  | inl_Let_NonRec : forall bs bs' t t',
      inline_Bindings_NonRec Δ Γ (Let NonRec bs t) (Let NonRec bs' t') ->
      inline Δ Γ (Let NonRec bs t) (Let NonRec bs' t')

  (* Compatibility cases *)
  | inl_TyInst_compat   : forall t t' τ τ',
      inline Δ Γ t t' ->
      inline_Ty Δ τ τ' ->
      inline Δ Γ (TyInst t τ) (TyInst t' τ')
  | inl_TyAbs    : forall α k t t',
      inline ((α, bound_TyAbs) :: Δ) Γ t t' ->
      inline Δ Γ (TyAbs α k t) (TyAbs α k t')
  | inl_LamAbs   : forall x τ τ' t t',
      inline Δ ((x, bound_LamAbs) :: Γ) t t' ->
      inline_Ty Δ τ τ' ->
      inline Δ Γ (LamAbs x τ t) (LamAbs x τ' t')
  | inl_Apply    : forall s s' t t',
      inline Δ Γ s s' ->
      inline Δ Γ t t' ->
      inline Δ Γ (Apply s t) (Apply s' t')
  | inl_Constant : forall c,
      inline Δ Γ (Constant c) (Constant c)
  | inl_Builtin  : forall f,
      inline Δ Γ (Builtin f) (Builtin f)
  | inl_Error    : forall τ τ',
      inline Δ Γ (Error τ) (Error τ')
  | inl_IWrap    : forall σ σ' τ τ' t t',
      inline_Ty Δ τ τ' ->
      inline_Ty Δ σ σ' ->
      inline Δ Γ (IWrap σ τ t) (IWrap σ' τ' t')
  | inl_Unwrap   : forall t t',
      inline Δ Γ (Unwrap t) (Unwrap t')

  (* We closely follow the structure of eval so the semantic proof lines up
     more easily *)
  with inline_Bindings_NonRec (Δ : ty_ctx) (Γ : ctx) : Term -> Term -> Prop :=

  | inl_Binding_NonRec_cons : forall b b' bs bs' t t',
      inline_Binding Δ Γ b b' ->
      inline_Bindings_NonRec (Binding_to_ty_ctx b ++ Δ) (Binding_to_ctx b ++ Γ)
        (Let NonRec bs t)
        (Let NonRec bs' t') ->
      inline_Bindings_NonRec Δ Γ
        (Let NonRec (b :: bs) t)
        (Let NonRec (b' :: bs') t')

  | inl_Binding_NonRec_nil  : forall t t',
      inline Δ Γ t t' ->
      inline_Bindings_NonRec Δ Γ (Let NonRec [] t) (Let NonRec [] t')

  with inline_Bindings_Rec (Δ : ty_ctx) (Γ : ctx) : Term -> Term -> Prop :=

    | inl_Binding_Rec_cons : forall b b' bs bs' t t',
        inline_Binding Δ Γ b b' ->
        inline_Bindings_Rec Δ Γ (Let Rec bs t) (Let Rec bs' t') ->
        inline_Bindings_Rec Δ Γ (Let Rec (b :: bs) t) (Let Rec (b' :: bs') t')

    | inl_Binding_Rec_nil : forall t t',
        inline Δ Γ t t' ->
        inline_Bindings_Rec Δ Γ (Let Rec [] t) (Let Rec [] t')

with inline_Binding (Δ : ty_ctx) (Γ : ctx) : Binding -> Binding -> Prop :=

  | inl_TermBind  : forall s x τ τ' tb tb',
      inline Δ Γ tb tb' -> (* Δ and Γ need not be extended, in case of LetRec, x is already in Γ, otherwise it is not in scope *)
      inline_Binding Δ Γ
        (TermBind s (VarDecl x τ) tb)
        (TermBind s (VarDecl x τ') tb')

  | inl_DatatypeBind_NonRec : forall d,
      (* TODO: add bindings and inline_Ty premises, should probably distinguish
      * between Rec and NonRec binding *)
      inline_Binding Δ Γ (DatatypeBind d) (DatatypeBind d)

  | inl_TypeBind_NonRec : forall tvd τ τ',
      inline_Ty Δ τ τ' -> (* Cannot be recursive *)
      inline_Binding Δ Γ (TypeBind tvd τ) (TypeBind tvd τ')
.


From PlutusCert Require Import Bigstep.
Require Import Program.


(* Todo: move this to a subst helper module *)
Lemma subst_here x tx : subst x tx (Var x) = tx.
Proof.
Admitted.

Lemma Lookup_append {A B} (k : A) (v : B) xs xs':
  Lookup k v xs -> Lookup k v (xs ++ xs').
Admitted.

Lemma Lookup_extensional {A B} (k : A) (v v' : B) xs :
  Lookup k v xs -> Lookup k v' xs -> v = v'.
Admitted.


Module InlineWS.

  From PlutusCert Require Import WellScoped.

  (* Lowering contexts *)
  Definition lower {A} (xs : list (string * A)) :=
    map fst xs.

  Lemma inline_well_scoped_l Δ Γ t t' :
    inline Δ Γ t t' ->
    well_scoped (lower Δ) (lower Γ) t.
  Admitted.

  Lemma inline_closed_l t t' :
    inline [] [] t t' ->
    well_scoped [] [] t.
  Proof.
    apply inline_well_scoped_l with (Δ := []) (Γ := []).
  Qed.

  Lemma ws_subst_id Δ Γ x tx t :
    well_scoped Δ Γ t -> subst x tx t = t.
  Admitted.

  Lemma inline_closed_refl t :
    well_scoped [] [] t ->
    inline [] []  t t.
  Admitted.

  Lemma inline_refl Δ Γ t :
    well_scoped (lower Δ) (lower Γ) t ->
    inline Δ Γ t t.
  Admitted.

  Lemma inline_weaken Δ Γ t t' :
    inline [] [] t t' ->
    inline Δ Γ t t'.
  Admitted.

  Lemma inline_inv_var Δ Γ x t':
    inline Δ Γ (Var x) t' ->
    exists tx, Lookup x tx Γ.
  Proof.
    intros H_inl.
    inversion H_inl; eauto.
  Qed.

  Lemma inline_strengthen_var Δ Γ x t' :
    inline Δ Γ (Var x) t' ->
    exists info, inline [] [(x, info)] (Var x) t'.
  Proof.
    intros H_inl.
    inversion H_inl; subst.
    - exists (bound_TermBind t').
      econstructor.
      constructor.
    - exists info.
      eapply inl_Var_2.
      constructor.
  Qed.

End InlineWS.


Import InlineWS.

Lemma subst_preserves_inline_Let Δ_pre Γ_pre tx tx' t t' x :
  inline [] [] tx tx' -> (* substituting a closed term *)
  inline Δ_pre (Γ_pre ++ [(x, bound_TermBind tx)]) t t' -> (* into a term that has x as free variable *)
  inline Δ_pre Γ_pre (subst x tx t) (subst x tx' t').
Proof.
  induction t.
  all: intros H_inl_tx H_inl_t.
  - (* Let *) admit.
  - (* Var *)
    inversion H_inl_t; subst.
    + (* Var-1 *)
      destruct (string_dec x n).
      * (* n = x *)
        subst n.
        simpl.
        rewrite eqb_refl.
        assert (t' = tx) by admit. (* From lookup *)
        subst t'.
        rewrite (ws_subst_id (lower Δ_pre) (lower Γ_pre) x tx' _).
        ** eapply inline_refl.
           eauto using inline_well_scoped_l, inline_weaken.
        ** eauto using inline_well_scoped_l, inline_weaken.
      * (* n ≠ x *)

        simpl.
        rewrite <- eqb_neq in n0.
        rewrite n0.
        apply inline_strengthen_var in H_inl_t as [info inl_t].

Admitted.

Lemma subst_preserves_inline_Let Δ Γ Δ_pre Γ_pre tx tx' t t' x :
  inline Δ Γ tx tx' ->
  inline (Δ_pre ++ Δ) (Γ_pre ++ (x, bound_TermBind tx) :: Γ) t t' ->
  ~(exists y, Lookup x y Γ_pre) ->
        erewrite ws_subst_id; eauto.
  inline (Δ_pre ++ Δ) (Γ_pre ++ Γ) (subst x tx t) (subst x tx' t').
Proof.
  induction t.
  all: intros H_inl_tx H_inl_t H_no_shadow.
  - (* Let *) admit.
  - (* Var *)
    inversion H_inl_t; subst.
    + (* inl_Var_1 *)
      destruct (string_dec n x).
      * subst.
        rewrite subst_here.
        assert (t = tx). admit.
        subst.
        assert (bound_TermBind tx = bound_TermBind t) by
          eauto using Lookup_append, Lookup_extensional.
        inversion H; subst. clear H.
        
        apply f_equal in H. clear H.
        assert ().
        eapply inl_Var_1.
      eauto using inline.
      
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma substA_preserves_inline Δ Γ T T' info t t' α :
  inline_Ty Δ T T' ->
  inline ((α, info) :: Δ) Γ t t' ->
  inline Δ Γ (substA α T t) (substA α T' t').
Admitted.

Lemma inline_preserves_no_error Δ Γ t t':
  inline Δ Γ t t' ->
  ~(is_error t) ->
  ~(is_error t').
Admitted.

Lemma inline_all_bindings Δ Γ bs bs' t t':
  inline_Bindings_Rec Δ Γ (Let Rec bs t) (Let Rec bs' t') ->
  Forall2 (inline_Binding Δ Γ) bs bs'.
Admitted.

Definition P_Term t v (k : nat) := forall Δ Γ t',
  inline Δ Γ t t' ->
  exists k' v',
    eval t' v' k' /\ inline Δ Γ v v'.

Definition P_LetNonRec t v (k : nat) := forall Δ Γ t',
  inline Δ Γ t t' ->
  exists k' v',
    eval_bindings_nonrec t' v' k' /\ inline Δ Γ v v'.

Definition P_LetRec bs t v (k : nat) := forall Δ Γ t' bs',
  inline Δ Γ t t' ->
  Forall2 (inline_Binding (Bindings_to_ty_ctx bs ++ Δ) (Bindings_to_ctx bs ++ Γ)) bs bs' ->
  exists k' v',
    eval_bindings_rec bs' t' v' k' /\ inline Δ Γ v v'.

Lemma eval_inline :
  (forall t v k, eval t v k -> P_Term t v k) /\
  (forall t v k, eval_bindings_nonrec t v k -> P_LetNonRec t v k) /\
  (forall bs t v k, eval_bindings_rec bs t v k -> P_LetRec bs t v k).
Proof.
  apply eval__multind with (P := P_Term) (P0 := P_LetNonRec) (P1 := P_LetRec).
  - (* LamAbs *)
    unfold P_Term.
    intros.
    inversion H; subst.
    eauto using eval.
  - (* Apply *)
    unfold P_Term.
    intros.

    match goal with
    | H : inline _ _ _ _ |- _ => inversion H; subst
    end.

    edestruct H0 as [k1' [v1' [H_eval_t1' H_inl_v1]]]; eauto. clear H0.
    edestruct H2 as [k2' [v2' [H_eval_t2' H_inl_v2]]] ; eauto. clear H2.

    inversion H_inl_v1; subst.
    edestruct H5 as [k3' [v3' [H_eval_subst H_inl_v3']]]; clear H5.
    + eapply subst_preserves_inline; eauto.
    + repeat eexists.
      * eapply E_Apply; eauto.
        eauto using inline_preserves_no_error.
      * eauto.
  - (* TyAbs*)
    admit.
  - (* TyInst *)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (**)
    admit.
  - (* Let NonRec *)
    unfold P_Term, P_LetNonRec.
    intros.

    match goal with
    | H : inline _ _ _ _ |- _ => inversion H; subst
    end.

    edestruct H0 as [k' [v' [H_eval_t' H_inl_v]]]; eauto. clear H0.
    eauto using eval.
  - (* Let Rec*)
    unfold P_Term, P_LetRec.
    intros.

    match goal with
    | H : inline _ _ _ _ |- _ => inversion H; subst
    end.

    edestruct H0 as [k' [v' [H_eval_t' H_inl_v ]]]; eauto using inline_all_bindings. clear H0.
    eauto using eval.

  - (* Let NonRec [] *)
    admit.

  - (* Let NonRec TermBind *)
    unfold P_LetNonRec in *.
    intros.

    match goal with
    | H : inline _ _ _ _ |- _ => inversion H; clear H; subst
    end.

    inversion H8; subst.
    inversion H6; subst.

    edestruct H0; eauto.
    destruct H4 as [v' [H_eval_tb H_inl_v1]].
    edestruct H3.
    (*
      seems like something is wrong with H3, it shouldn't have the same Δ and Γ
    *)
    +
      eapply subst_preserves_inline.
      * eauto.
      * simpl in H11.
        eauto using inline.
    + destruct H4 as [v'0 [H_eval_bs H_inline_v2]].
      repeat eexists;
      eauto using eval_bindings_nonrec, inline_preserves_no_error.

  - (* Let NonRec TypeBind *)

    unfold P_LetNonRec in *.
    intros.

    match goal with
    | H : inline _ _ _ _ |- _ => inversion H; clear H; subst
    end.
    inversion H5; subst. clear H5.
    simpl in H8.
    inversion H3; subst.

    unfold P_Term in *.

    apply inl_Let_NonRec in H8.
      eapply substA_preserves_inline in H8; eauto.
      edestruct H0 as [ k' [ v' [H_eval H_inl] ] ]; eauto.
    repeat eexists.
    + econstructor. eauto.
    + eauto.

  - (* Let NonRec TermBind *)
    admit.
  - (* Let Rec [] *)
    admit.
  - (* Let Rec TermBind *)

    admit.
Qed.
