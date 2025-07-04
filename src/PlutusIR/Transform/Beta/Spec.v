From Coq Require Import
  Lists.List
  Strings.String.
Import ListNotations.
From PlutusCert Require Import
  PlutusIR
  Util
  Compat
  LetMergeNR
  FreeVars
  Util.List
  Util.Tactics
  Size
.


(*

This pass transforms beta redexes into let non-recs, so that the later inlining
pass has more opportunities for inlining.

Transforms repeated applications (not just repeated β-redexes), e.g.

(\x y z. t) t₁ t₂ t₃

=>

let nonrec x = t₁
           y = t₂
           z = t₃
in t

Has to avoid capture: e.g. t₂ may not have a free variable `x` as it would be captured
by the first binding

*)




Definition app_ctx := list term.

Inductive betas : app_ctx -> term -> term -> Prop :=
  | beta_Compat s t :
     Compat (betas []) s t ->
     betas [] s t

  | beta_Apply C s t r :
     betas (t :: C) s           r ->
     betas C        (Apply s t) r

  | beta_LamAbs C x T t t' t0 t0' :
     betas C t t' ->
     betas [] t0 t0' ->
     (Forall (fun t => x ∉ Term.fv t) C) ->
     betas (t0 :: C)
      (LamAbs x T t)
      (Let NonRec [TermBind Strict (VarDecl x T) t0'] t')

  | beta_TyInst_TyAbs X K t T t' :
      betas [] t t' ->
      betas []
        (TyInst (TyAbs X K t) T)
        (Let NonRec [TypeBind (TyVarDecl X K) T] t')
  .

Lemma beta_refl : forall x, betas [] x x.
Proof.
  apply term__ind with (Q := fun b => Compat_Binding (betas []) b b).
  all: try auto using betas, Compat, Compat_Bindings, Compat_Binding.
  - intros.
    constructor.
    constructor.
    + induction bs.
      * auto using Compat_Bindings.
      * inversion H; auto using Compat_Bindings, Compat.
    + assumption.
  - admit. (* TODO add Constr to Compat *)
  - admit. (* TODO add Case to Compat *)
Admitted.

Definition spec s t := betas [] (split s) (split t).


