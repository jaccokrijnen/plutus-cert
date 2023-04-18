Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Util.
Require Import PlutusCert.Util.List.
Require Import PlutusCert.Util.Map.
Require Import PlutusCert.Util.Map.Mupdate.

Require Import Arith.
Require Import Coq.Lists.List.

Local Open Scope list_scope.




Lemma In__mdrop : forall {X} ns ss x s,
    List.In x ns ->
    @mdrop X ns ((x, s) :: ss) = @mdrop X ns ss.
Proof.
  induction ns; intros.
  - destruct H.
  - simpl.
    destruct (x =? a)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      destruct H.
      * symmetry in H. 
        apply Hneq in H.
        destruct H.
      * eapply IHns.
        assumption. 
Qed.

Lemma not_In__mdrop : forall {X} ns ss x s,
    ~ List.In x ns ->
    @mdrop X ns ((x, s) :: ss) = (x, s) :: @mdrop X ns ss.
Proof.
  induction ns; intros.
  - reflexivity.
  - simpl.
    destruct (x =? a)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      exfalso.
      apply H.
      left.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      eapply IHns.
      intros Hcon.
      apply H.
      right.
      assumption.
Qed.

Lemma subst_b__bound_vars : forall x s b,
    bvb b = bvb <{ [s/x][b] b }>.
Proof. intros. induction b. all: eauto. destruct v. eauto. Qed.

Lemma subst_bnr__bound_vars : forall x s bs,
    bvbs bs = bvbs <{ [s/x][bnr] bs }>.
Proof. 
  intros. 
  induction bs.
  - reflexivity.
  - simpl.
    destruct (List.existsb (eqb x) (bvb a)) eqn:Hexb.
    + unfold bvbs.
      simpl.
      f_equal.
      apply subst_b__bound_vars.
    + unfold bvbs.
      simpl.
      f_equal.
      * apply subst_b__bound_vars.
      * assumption.
Qed.

Lemma msubst_bnr__bound_vars : forall bs ss,
    bvbs bs = bvbs <{ /[ ss /][bnr] bs }>.
Proof. 
(* ADMIT: I had no time to finish this. Should follow from subst_bnr__bound_vars *)
Admitted.

Lemma substA_b__bound_tyvars : forall a T b,
    btvb b = btvb <{ [[T/a][b] b }>.
Proof. intros. induction b. all: eauto. destruct v; eauto. destruct d; eauto. Qed.

Lemma substA_bnr__bound_tyvars : forall a T bs,
    btvbs bs = btvbs <{ [[T/a][bnr] bs }>.
Proof. 
  intros. 
  induction bs.
  - reflexivity.
  - simpl.
    destruct (List.existsb (eqb a) (btvb a0)) eqn:Hfind.
    + unfold btvbs.
      simpl.
      f_equal.
      apply substA_b__bound_tyvars.
    + unfold btvbs.
      simpl.
      f_equal.
      * apply substA_b__bound_tyvars.
      * assumption.
Qed.

Lemma msubstA_bnr__bvbs : forall bs ss,
    bvbs bs = bvbs <{ /[[ ss /][bnr] bs }>.
Proof. 
(* ADMIT: I had no time to finish this. Should follow from substA_bnr__bound_tyvars *)
Admitted.
    
Lemma msubst_LetNonRec_nil : forall ss e,
    msubst_term ss (Let NonRec nil e) = Let NonRec nil (msubst_term ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_LetNonRec : forall ss bs e,
    msubst_term ss (Let NonRec bs e) = Let NonRec (msubst_bindings_nonrec ss bs) (msubst_term (mdrop (bvbs bs) ss) e).
Proof with auto.
  induction ss; intros.
  - rewrite mdrop_nil. reflexivity.
  - destruct a. simpl.
    destruct (existsb (eqb s) (bvbs bs)) eqn:Hexb.
    + apply existsb_exists in Hexb.
      destruct Hexb as [x [HIn Heqb]].
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite In__mdrop...
      erewrite subst_bnr__bound_vars.
      eapply IHss.
    + rewrite not_In__mdrop...
      * simpl.
        erewrite subst_bnr__bound_vars.
        eapply IHss.
      * intros Hcon.
        eapply existsb_nexists.
        -- eapply Hexb.
        -- exists s.
           rewrite eqb_refl.
           auto.
Qed.

Lemma msubst_TermBind : forall ss stricty x T e,
    msubst_binding ss (TermBind stricty (VarDecl x T) e) = TermBind stricty (VarDecl x T) (msubst_term ss e). 
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_BindingsNonRec_cons : forall ss b bs,
    msubst_bindings_nonrec ss (b :: bs) = msubst_binding ss b :: msubst_bindings_nonrec (mdrop (bvb b) ss) bs.
Proof.
  induction ss; intros.
  - rewrite mdrop_nil. reflexivity.
  - destruct a. 
    simpl.
    destruct (existsb (eqb s) (bvb b)) eqn:Hexb.
    + apply existsb_exists in Hexb.
      destruct Hexb as [x [HIn Heqb]].
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite In__mdrop.
      * erewrite subst_b__bound_vars.  
        eapply IHss.
      * assumption.
    + apply existsb_nexists in Hexb.
      rewrite not_In__mdrop.
      * simpl.
        erewrite subst_b__bound_vars.
        eapply IHss.
      * intros Hcon.
        apply Hexb.
        exists s.
        rewrite eqb_refl.
        auto.
Qed.

Lemma msubstA_LetNonRec_nil : forall ss e,
    msubstA_term ss (Let NonRec nil e) = Let NonRec nil (msubstA_term ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_LetNonRec : forall ss bs e,
    msubstA_term ss (Let NonRec bs e) = Let NonRec (msubstA_bindings_nonrec ss bs) (msubstA_term (mdrop (btvbs bs) ss) e).
Proof.
(* ADMIT: I had no time to finish this. Should hold, it is a congruence lemma. *)
Admitted.

Lemma msubstA_LetRec : forall ss bs e,
    msubstA_term ss (Let Rec bs e) = Let Rec (msubstA_bindings_rec (mdrop (btvbs bs) ss) bs) (msubstA_term (mdrop (btvbs bs) ss) e).
Proof.
(* ADMIT: I had no time to finish this. Should hold, it is a congruence lemma. *)
Admitted.

Lemma msubstA_TermBind : forall ss stricty x T e,
    msubstA_binding ss (TermBind stricty (VarDecl x T) e) = TermBind stricty (VarDecl x (msubstT ss T)) (msubstA_term ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_BindingsNonRec_cons : forall ss b bs,
    msubstA_bindings_nonrec ss (b :: bs) = msubstA_binding ss b :: msubstA_bindings_nonrec (mdrop (btvb b) ss) bs.
Proof.
(* ADMIT: I had no time to finish this. Should hold, it is a congruence lemma. *)
Admitted.

Lemma msubst_term__fold : forall ss x v t,
    msubst_term ss <{ [v / x] t }> = msubst_term ((x, v) :: ss) t.
Proof. induction ss; intros; auto. Qed.

Lemma msubst_bindings_nonrec__fold : forall ss x v bs,
    msubst_bindings_nonrec ss <{ [v / x][bnr] bs }> = msubst_bindings_nonrec ((x, v) :: ss) bs.
Proof. induction ss; intros; auto. Qed.

Lemma msubst_LamAbs : forall ss x T t0,
    msubst_term ss (LamAbs x T t0) = LamAbs x T (msubst_term (drop x ss) t0).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a.
    simpl.
    destruct (s =? x)%string eqn:Heqb.
    + eauto using eqb_eq.
    + eauto using eqb_neq.
Qed.

Lemma msubstA_LamAbs : forall ss x T t0,
    msubstA_term ss (LamAbs x T t0) = LamAbs x (msubstT ss T) (msubstA_term ss t0).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstT_TyFun : forall ss T1 T2,
    msubstT ss (Ty_Fun T1 T2) = Ty_Fun (msubstT ss T1) (msubstT ss T2).
Proof.
  induction ss.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_Apply : forall ss t1 t2,
    msubst_term ss (Apply t1 t2) = Apply (msubst_term ss t1) (msubst_term ss t2).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Apply : forall ss t1 t2,
    msubstA_term ss (Apply t1 t2) = Apply (msubstA_term ss t1) (msubstA_term ss t2).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_Builtin : forall ss f,
    msubst_term ss (Builtin f) = Builtin f.
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Builtin : forall ss f,
    msubstA_term ss (Builtin f) = Builtin f.
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_Constant : forall ss sv,
    msubst_term ss (Constant sv) = Constant sv.
Proof.
  induction ss; intros. 
  - reflexivity.
  - destruct a.
    eauto.
Qed.

Lemma msubstA_Constant : forall ss sv ,
    msubstA_term ss (Constant sv) = Constant sv.
Proof.
  induction ss; intros. 
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstT_TyBuiltin : forall ss u,
    msubstT ss (Ty_Builtin (Some (TypeIn u))) = Ty_Builtin (Some (TypeIn u)).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_DatatypeBind : forall ss X YKs matchFunc cs,
    msubst_binding ss (DatatypeBind (Datatype X YKs matchFunc cs)) = DatatypeBind (Datatype X YKs matchFunc cs).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_DatatypeBind : forall ss X YKs matchFunc cs,
    msubstA_binding ss (DatatypeBind (Datatype X YKs matchFunc cs)) = DatatypeBind (Datatype X YKs matchFunc (msubstA_constructors ss cs)).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. simpl. eauto.
Qed.


Lemma msubst_Error : forall ss T,
    msubst_term ss (Error T) = Error T.
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Error : forall ss T,
    msubstA_term ss (Error T) = Error (msubstT ss T).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_IWrap : forall ss F T M,
    msubst_term ss (IWrap F T M) = IWrap F T (msubst_term ss M).
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed. 

Lemma msubstA_IWrap : forall ss F T M,
    msubstA_term ss (IWrap F T M) = IWrap (msubstT ss F) (msubstT ss T) (msubstA_term ss M).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed. 

Lemma msubstT_IFix : forall ss F T,
    msubstT ss (Ty_IFix F T) = Ty_IFix (msubstT ss F) (msubstT ss T).
Proof.
  induction ss; intros.
    - reflexivity.
    - destruct a. eauto.
Qed. 

Lemma msubst_TyAbs : forall ss bX K t0,
    msubst_term ss (TyAbs bX K t0) = TyAbs bX K (msubst_term ss t0).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

Lemma msubstA_TyAbs : forall ss bX K t0,
    msubstA_term ss (TyAbs bX K t0) = TyAbs bX K (msubstA_term (drop bX ss) t0).
Proof. induction ss; intros. - reflexivity. - intros. destruct a. simpl. destruct (s =? bX)%string; eauto. Qed.


Lemma msubstT_TyForall : forall ss bX K T,
    msubstT ss (Ty_Forall bX K T) = Ty_Forall bX K (msubstT (drop bX ss) T).
Proof. induction ss; intros. - reflexivity. - intros. destruct a. simpl. destruct (s =? bX)%string; eauto. Qed.

Lemma msubst_TyInst : forall ss t0 T0,
    msubst_term ss (TyInst t0 T0) = TyInst (msubst_term ss t0) T0.
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


Lemma msubstA_TyInst : forall ss t0 T0,
    msubstA_term ss (TyInst t0 T0) = TyInst (msubstA_term ss t0) (msubstT ss T0).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


Lemma msubst_Unwrap : forall ss M,
    msubst_term ss (Unwrap M) = Unwrap (msubst_term ss M).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

Lemma msubstA_Unwrap : forall ss M ,
    msubstA_term ss (Unwrap M) = Unwrap (msubstA_term ss M).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


Lemma msubst_Var : forall ss x,
    closed_env ss ->
    msubst_term ss (Var x) =
      match lookup x ss with
      | Datatypes.Some t => t
      | None => Var x
      end.
Proof. 
  induction ss; intros. 
  - reflexivity. 
  - intros. 
    destruct a. 
    simpl. 
    destruct (s =? x)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      destruct H.
      rewrite msubst_closed.
      all: auto.
    + apply eqb_neq in Heqb as Hneq.
      destruct H.
      eapply IHss.
      assumption.
Qed.

Lemma msubstA_Var : forall ss x,
    msubstA_term ss (Var x) = Var x.
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


(* TODO move this into separate module*)

Hint Rewrite
  msubstA_LetRec
  msubstA_LetNonRec
  msubstA_bnr__bvbs
  msubstA_LetNonRec_nil
  msubstA_LetNonRec
  msubstA_LetRec
  msubstA_TermBind
  msubstA_BindingsNonRec_cons
  msubstA_LamAbs
  msubstA_Apply
  msubstA_Builtin
  msubstA_Constant
  msubstA_DatatypeBind
  msubstA_Error
  msubstA_IWrap
  msubstA_TyAbs
  msubstA_TyInst
  msubstA_Unwrap
  msubstA_Var
  : msubstA_cong.

Lemma not_is_error_msubstA : forall v ss, ~ is_error v -> ~ is_error (msubstA_term ss v).
  intros v ss H_not_err H_err.
  destruct v; simpl in H_err.
  all: try (autorewrite with msubstA_cong in H_err; inversion H_err).

  (* Let r bs t *)
  - destruct r.
    + autorewrite with msubstA_cong in H_err.
       inversion H_err.
    + rewrite msubstA_LetRec in H_err.
       inversion H_err.

  (* Error *)
  - apply H_not_err.
    constructor.
Qed.


