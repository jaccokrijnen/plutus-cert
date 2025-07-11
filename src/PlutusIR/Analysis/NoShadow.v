From PlutusCert Require Import
  PlutusIR
  Analysis.BoundVars
  Analysis.FreeVars
  Util.List
.

Require Import
  Strings.String
  Lists.List
.
Import Utf8_core.
Import ListNotations.

(*
Note [No Shadowing]
-------------------
A term has shadowing when it binds a variable that is already in scope. To avoid this,
we keep track of the variables in scope (ctx), and at every binding site, check if the
name was not already bound.

*)

(* A context is used to track the names of variables, so we can avoid shadowing *)
Definition ctx := list string.

Reserved Notation "Δ '|-*ns' T" (at level 40, T at level 0).
Inductive no_shadow_ty (Δ : ctx) : ty -> Prop :=
  | NS_Ty_Forall : forall X K T,
      X ∉ Δ ->
      (X :: Δ) |-*ns T ->
      Δ |-*ns (Ty_Forall X K T)
  | NS_Ty_Lam : forall X K1 T,
      X ∉ Δ ->
      (X :: Δ) |-*ns T ->
      Δ |-*ns (Ty_Lam X K1 T)

  | NS_Ty_Var : forall X,
      In X Δ ->
      Δ |-*ns (Ty_Var X)
  | NS_Ty_Fun : forall T1 T2,
      Δ |-*ns T1 ->
      Δ |-*ns T2 ->
      Δ |-*ns (Ty_Fun T1 T2)
  | NS_Ty_IFix  : forall F T,
      Δ |-*ns T ->
      Δ |-*ns F ->
      Δ |-*ns (Ty_IFix F T)
  | NS_Ty_Builtin : forall T,
      Δ |-*ns (Ty_Builtin T)
  | NS_Ty_App : forall T1 T2,
      Δ |-*ns T1 ->
      Δ |-*ns T2 ->
      Δ |-*ns (Ty_App T1 T2)
where "Δ '|-*ns' T " := (no_shadow_ty Δ T).

Reserved Notation "Δ ',,' Γ '|-+ns' t " (at level 101, t at level 0, no associativity).
Reserved Notation "Δ '|-ns_ok_c' c " (at level 101, c at level 0).
Reserved Notation "Δ ',,' Γ  '|-ns_oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-ns_oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-ns_ok_b' b" (at level 101, b at level 0, no associativity).

Inductive no_shadow : ctx -> ctx -> term -> Prop :=
  | NS_LamAbs : forall Δ Γ x T t,
      x ∉ Γ ->
      Δ |-*ns T ->
      Δ ,, (x :: Γ) |-+ns t ->
      Δ ,, Γ |-+ns (LamAbs x T t)
  | NS_TyAbs : forall Δ Γ X K t,
      X ∉ Δ ->
      (X :: Δ) ,, Γ |-+ns t ->
      Δ ,, Γ |-+ns (TyAbs X K t)

  | NS_Var : forall Δ Γ x,
      In x Γ ->
      Δ ,, Γ |-+ns (Var x)
  | NS_Apply : forall Δ Γ t1 t2,
      Δ ,, Γ |-+ns t1 ->
      Δ ,, Γ |-+ns t2 ->
      Δ ,, Γ |-+ns (Apply t1 t2)
  | NS_TyInst : forall Δ Γ t T,
      Δ ,, Γ |-+ns t ->
      Δ |-*ns T ->
      Δ ,, Γ |-+ns (TyInst t T)
  | NS_IWrap : forall Δ Γ F T M,
      Δ |-*ns F ->
      Δ |-*ns T ->
      Δ ,, Γ |-+ns M ->
      Δ ,, Γ |-+ns (IWrap F T M)
  | NS_Unwrap : forall Δ Γ M,
      Δ ,, Γ |-+ns M ->
      Δ ,, Γ |-+ns (Unwrap M)
  | NS_Constant : forall Δ Γ (c : constant),
      Δ ,, Γ |-+ns (Constant c)
  | NS_Builtin : forall Δ Γ f,
      Δ ,, Γ |-+ns (Builtin f)
  | NS_Error : forall Δ Γ S,
      Δ |-*ns S ->
      Δ ,, Γ |-+ns (Error S)

  | NS_Let : forall Δ Γ bs t Δ_bs Γ_bs,
      Δ_bs = rev (btvbs bs) ->
      Γ_bs = rev (bvbs bs) ->
      Δ ,, Γ |-ns_oks_nr bs ->
      (Δ_bs ++ Δ) ,, (Γ_bs ++ Γ) |-+ns t ->
      Δ ,, Γ |-+ns (Let NonRec bs t)

  | NS_LetRec : forall Δ Γ bs t Δ_bs Γ_bs,
      Δ_bs = rev (btvbs bs) ->
      Γ_bs = rev (bvbs bs) ->
      Forall (fun X => X ∉ Δ) Δ_bs ->
      Forall (fun x => x ∉ Γ) Δ_bs ->
      NoDup Δ_bs ->
      NoDup Γ_bs ->
      (Δ_bs ++ Δ) ,, (Γ_bs ++ Γ) |-ns_oks_r bs ->
      (Δ_bs ++ Δ) ,, (Γ_bs ++ Γ) |-+ns t ->
      Δ ,, Γ |-+ns (Let Rec bs t)


with ns_bindings_nonrec : ctx -> ctx -> list binding -> Prop :=

  | NS_NilB_NonRec : forall Δ Γ,
    Δ ,, Γ |-ns_oks_nr nil

  | NS_ConsB_NonRec : forall Δ Γ b bs,
      Forall (fun X => X ∉ Δ) (btvb b) ->
      Forall (fun x => x ∉ Δ) (bvb b) ->
      Δ ,, Γ |-ns_ok_b b ->
      (btvb b ++ Δ) ,, (bvb b ++ Γ) |-ns_oks_nr bs ->
      Δ ,, Γ |-ns_oks_nr (b :: bs)

with ns_bindings_rec : ctx -> ctx -> list binding -> Prop :=

  | NS_NilB_Rec : forall Δ Γ,
      Δ ,, Γ |-ns_oks_r nil
  | NS_ConsB_Rec : forall Δ Γ b bs,
      Δ ,, Γ |-ns_ok_b b ->
      Δ ,, Γ |-ns_oks_r bs ->
      Δ ,, Γ |-ns_oks_r (b :: bs)

with ns_binding : ctx -> ctx -> binding -> Prop :=
  | NS_TermBind : forall Δ Γ s x T t,
      Δ |-*ns T ->
      Δ ,, Γ |-+ns t ->
      Δ ,, Γ |-ns_ok_b (TermBind s (VarDecl x T) t)
  | NS_TypeBind : forall Δ Γ X K T,
      Δ |-*ns T ->
      Δ ,, Γ |-ns_ok_b (TypeBind (TyVarDecl X K) T)
  | NS_DataBind : forall Δ Γ X YKs cs matchFunc Δ',
      Δ' = rev (map tvdecl_name YKs) ++ Δ  ->
      (forall c, In c cs -> Δ' |-ns_ok_c c) ->
      Δ ,, Γ |-ns_ok_b (DatatypeBind (Datatype X YKs matchFunc cs))

with constructor_well_formed : ctx -> vdecl -> Prop :=
  | NS_Con : forall Δ x T,
      Δ |-*ns T ->
      Δ |-ns_ok_c (VarDecl x T)
  where "Δ '|-ns_ok_c' c" := (constructor_well_formed Δ c)
  and "Δ ',,' Γ '|-+ns' t" := (no_shadow Δ Γ t)
  and "Δ ',,' Γ '|-ns_oks_nr' bs" := (ns_bindings_nonrec Δ Γ bs)
  and "Δ ',,' Γ '|-ns_oks_r' bs" := (ns_bindings_rec Δ Γ bs)
  and "Δ ',,' Γ '|-ns_ok_b' b" := (ns_binding Δ Γ b)
.


Scheme no_shadow__ind := Minimality for no_shadow Sort Prop
  with ns_bindings_nonrec__ind := Minimality for ns_bindings_nonrec Sort Prop
  with ns_bindings_rec__ind := Minimality for ns_bindings_rec Sort Prop
  with ns_binding__ind := Minimality for ns_binding Sort Prop
.

Combined Scheme no_shadow__multind from
  no_shadow__ind,
  ns_bindings_nonrec__ind,
  ns_bindings_rec__ind,
  ns_binding__ind
.

Definition multind P_ns P_ns_nonrec P_ns_rec P_ns_bind :=
  (∀ Δ Γ t, no_shadow Δ Γ t -> P_ns Δ Γ t) /\
  (∀ Δ Γ bs, ns_bindings_nonrec Δ Γ bs -> P_ns_nonrec Δ Γ bs) /\
  (∀ Δ Γ bs, ns_bindings_rec Δ Γ bs -> P_ns_rec Δ Γ bs) /\
  (∀ Δ Γ b, ns_binding Δ Γ b -> P_ns_bind Δ Γ b)
.


Module Ty.

  Import FreeVars.Ty.
  Import BoundVars.Ty.

  (* TODO: move to Util.List *)
  Notation "xs ⊑ ys" := (incl xs ys) (at level 70, no associativity).

  (* TODO: move to Util.List *)
  Lemma remove_incl {A} xs ys f (x : A) :
    xs ⊑ (x :: ys) -> remove f x xs ⊑ ys.
  Proof.
  Admitted.

  Create HintDb incl.
  Hint Resolve remove_incl incl_nil_l incl_cons incl_app
    : incl.

  Lemma ns_ftv Δ T : no_shadow_ty Δ T -> ftv T ⊑ Δ.
  Proof.
    induction 1; rewrite ftv_equation; auto with incl.
  Qed.

  Create HintDb disjoint.
  Hint Resolve disjoint_cons_r disjoint_cons_l disjoint_nil_l disjoint_nil_r
    disjoint_app_r disjoint_app_l
    : disjoint.

  Hint Resolve disjoint_uncons_r disjoint_uncons_l | 10 (* higher cost to prevent useless identities *)
    : disjoint.

  Lemma ns_disjoint Δ T : no_shadow_ty Δ T -> disjoint Δ (btv T).
  Proof.
    induction 1; rewrite btv_equation; eauto with disjoint.
  Qed.

End Ty.


Module Term.

(* TODO: move to Util.List *)
Notation "xs ⊑ ys" := (incl xs ys) (at level 70, no associativity).


Definition ctx_bound__term (Δ Γ : ctx) t :=
  (∀ x, x ∈ Γ -> x ∉ bound_vars t) /\
  (∀ X, X ∈ Δ -> X ∉ btv t).

(* reused for let and letrec: bound_vars and btv make no distinction between recursive and non-recursive lets *)
Definition ctx_bound__let (Δ Γ : ctx) bs := 
  (∀ x, x ∈ Γ -> x ∉ concat (map bound_vars_binding bs)) /\
  (∀ X, X ∈ Δ -> X ∉ concat (map btv_binding bs)).

Definition ctx_bound__bind (Δ Γ : ctx) b := 
  (∀ x, x ∈ Γ -> x ∉ bound_vars_binding b) /\
  (∀ x, x ∈ Δ -> x ∉ btv_binding b).

Lemma no_shadow__ctx_bound : multind ctx_bound__term ctx_bound__let ctx_bound__let ctx_bound__bind.
  apply no_shadow__multind.
  - unfold ctx_bound__term. intros.
    split.
    + intros y H_y_in.
      destruct H2 as [IH1 _].
      specialize (IH1 y).
      assert (y ∉ bound_vars t) by intuition.
      assert (x <> y). { destruct (string_dec x y); try assumption. subst x. contradiction. }
      simpl.
      intuition.
      (* etc. *)
Admitted.


(*
(* Corollaries that play nice with auto *)
Corollary ns_ctx Δ Γ t :
  no_shadow Δ Γ t ->
  (∀ x, x ∈ Γ -> x ∉ bound_vars t) /\
  (∀ X, X ∈ Δ -> X ∉ btv t).
Proof.
  apply no_shadow__ctx_bound.
Qed.

Corollary ns_tctx Δ Γ t :
  no_shadow Δ Γ t ->
  (∀ x, x ∈ Γ -> x ∉ bound_vars t).
Proof.
  apply ns_ctx.
Qed.
*)


  Lemma ns_disjoint_ann Δ Γ t : no_shadow Δ Γ t -> disjoint Δ (btv t).
  Proof.
  Admitted.


  Lemma ns_disjoint Δ Γ t : no_shadow Δ Γ t -> disjoint Γ (bound_vars t).
  Proof.
  Admitted.

End Term.

