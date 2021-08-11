Require Import PlutusCert.Language.PlutusIR.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope context_scope.

(*
Theorem CNR_Binding__preserves_wellformedness : forall b f_b bs,
    ctx |-ok (TermBind Strict (VarDecl v ty) t_bound) ->
    CNR_Binding b f_b ->
    appendContext (binds bs) ctx |-+ (f_b t_bound) : T.


with CNR_Binding : Binding -> (Term -> Term) -> Type :=
  | CNR_Desugar : forall {v t_bound t_bound' ty},
      CNR_Term t_bound t_bound' ->
      CNR_Binding
        (TermBind Strict (VarDecl v ty) t_bound)
        (fun t_bs => Apply (LamAbs v ty t_bs) t_bound')
  .

Theorem CNR_Bindings__preserves_typing : forall bs ctx t_body T t_body' f_bs,
    (forall b : Binding, In b bs -> binding_well_formed ctx b) ->
    appendContexts (fold_right appendContexts Nil (map binds bs)) ctx |-+ t_body : T ->
    CNR_Term t_body t_body' ->
    (forall t2 : Term, CNR_Term t_body t2 -> appendContexts (fold_right appendContexts Nil (map binds bs)) ctx |-+ t2 : T) ->
    CNR_Bindings bs f_bs ->
    ctx |-+ (fold_right apply t_body' f_bs) : T.
Proof.
  intros.
  generalize dependent ctx.
  generalize dependent t_body.
  generalize dependent T.
  generalize dependent t_body'.
  induction X0.
  - intros.
    simpl.
    apply H1.
    apply X.
  - intros.
    simpl.
    simpl in H1.
    inversion c. subst.
    *)

    

Theorem CNR_Term__preserves_typing : forall t1 t2 T ctx,
    ctx |-+ t1 : T ->
    CNR_Term t1 t2 ->
    ctx |-+ t2 : T.
Proof.
  intros t1 t2 T ctx Ht1.
  generalize dependent t2.
  induction Ht1. 
  - intros t2 H_CNR.
    inversion H_CNR.
    + subst.
Abort.
      (*
      inversion X0.
      * subst.
        simpl.
        simpl in IHHt1.
        apply IHHt1.
        apply X.
      * subst.
        simpl.
      *)

(** *** Weakening of kinding *)
Lemma weakening__has_kind : forall ctx ctx' T K,
    (forall e, In e ctx -> In e ctx') ->
    ctx |-* T : K ->
    ctx' |-* T : K.
Proof. Admitted.

Lemma weakening__binding_well_formed : forall ctx ctx' b,
    (forall e, In e ctx -> In e ctx') ->
    ctx |-ok b ->
    ctx' |-ok b.
Proof. Admitted.

Lemma CNR_Bindings__preserves_typing : forall bs ctx t_body T f_bs t_body',
    (concat_rev_ctx (Lists.List.map binds bs) ++ ctx) |-+ t_body' : T ->
    ctx |-+ (Let NonRec bs t_body) : T ->
    CNR_Bindings bs f_bs ->
    ctx |-+ (Lists.List.fold_right apply t_body' f_bs) : T.
Proof.
  intros.
  generalize dependent t_body.
  generalize dependent t_body'.
  generalize dependent T.
  generalize dependent ctx.
  induction X.
  - simpl. intros. 
    inversion H0.
    + subst.
      assumption.
    + subst.
      assumption.
  - intros.
    inversion H0.
    + subst.
      inversion c.
      subst.
      simpl.
      apply T_Apply with ty.
      * apply T_LamAbs.
        -- eapply IHX.
            ++ unfold concat_rev_ctx in H.
               simpl in H.
               rewrite concat_app in H.
               simpl in H.
               rewrite <- app_assoc in H.
               simpl in H.
               apply H.
            ++ apply T_Let.
               ** apply weakening__has_kind with ctx.
                  --- intros.
                      destruct e; right; auto.
                  --- auto. 
               ** intros.
                  apply weakening__binding_well_formed with ctx.
                  --- intros. apply in_cons. apply H2.
                  --- apply H5.
                      apply in_cons. 
                      apply H1.
               ** simpl in H.
                  unfold concat_rev_ctx in H.
                  simpl in H.
                  rewrite concat_app in H.
                  simpl in H.
                  rewrite <- app_assoc in H.
                  simpl in H.
                  apply H.
        -- remember (H5 (TermBind Strict (VarDecl v ty) t_bound)).
           clear Heqb.
           assert (In (TermBind Strict (VarDecl v ty) t_bound) (TermBind Strict (VarDecl v ty) t_bound :: bs)). {
             simpl. left. auto.
           }
           apply b in H1.
           inversion H1. subst.
           apply H8.
      * remember (H5 (TermBind Strict (VarDecl v ty) t_bound)).
        clear Heqb.
        assert (In (TermBind Strict (VarDecl v ty) t_bound) (TermBind Strict (VarDecl v ty) t_bound :: bs)). {
          simpl. left. auto.
        }
        apply b in H1.
        inversion H1. subst.
Abort.
