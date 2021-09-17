Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.ContextInvariance.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Def.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Termination.

Require Import Coq.Logic.Decidable.
Require Import Coq.Lists.List.
Require Import Arith.

(** ** Multisubstitutions, multi-extensions, and instantiations *)

Definition env := list (name * Term).

Inductive msubst : env -> Term -> Term -> Prop :=
  | msubst_nil : forall t,
      msubst nil t t
  | msubst_cons : forall x s ss t t' t'',
      substitute x s t t' ->
      msubst ss t' t'' ->
      msubst ((x, s) :: ss) t t''
  .

Definition tass := list (name * Ty).

Fixpoint mupdate (Gamma : Context) (xts : tass) :=
  match xts with
  | nil => Gamma
  | ((x, v) :: xts') => extendT x v (mupdate Gamma xts')
  end. 

Fixpoint lookup {X:Type} (k : string) (l : list (name * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if String.eqb j k then Datatypes.Some x else lookup k l'
  end.

Fixpoint drop {X:Type} (n:string) (nxs:list (string * X)) : list (string * X) :=
  match nxs with
  | nil => nil
  | (n',x) :: nxs' => if String.eqb n' n then drop n nxs' else (n',x) :: (drop n nxs')
  end.

Inductive instantiation : nat -> tass -> env -> env -> Prop :=
  | V_nil : forall k,
      instantiation k nil nil nil
  | V_cons : forall x k T v1 v2 c e1 e2,
      value v1 ->
      value v2 ->
      RC k T v1 v2 ->
      instantiation k c e1 e2 ->
      instantiation k ((x, T) :: c) ((x, v1) :: e1) ((x, v2) :: e2)
  . 

(** ** More substitution facts *)

Definition P_Term (t : Term) :=
  forall x,
    ~(appears_free_in x t) ->
    forall s t', 
      substitute x s t t' ->
      t' = t.

Definition P_Binding (b : Binding) :=
  forall x,
    ~(appears_free_in_binding x b) ->
    forall s b',
      substitute_binding x s b b' ->
      b' = b.

Definition P_Bindings_NonRec (bs : list Binding) :=
  Util.ForallT P_Binding bs ->
  forall x,
    ~(appears_free_in_bindings_nonrec x bs) ->
    forall s bs',
      substitute_bindings_nonrec x s bs bs' ->
      bs' = bs.

Lemma P_Bindings_NonRec__holds_definitionally : forall bs, P_Bindings_NonRec bs.
Proof.
  induction bs.
  - unfold P_Bindings_NonRec. intros.
    inversion H0. subst.
    reflexivity.
  - unfold P_Bindings_NonRec. intros.
    inversion H0.
    + subst.
      f_equal.
      apply Util.ForallT_hd in X.
      unfold P_Binding in X.
      apply X with x s.
      * intros Hcon.
        apply H.
        apply AFI_ConsB1_NonRec.
        assumption.
      * assumption.
    + subst.
      f_equal.
      * apply Util.ForallT_hd in X.
        unfold P_Binding in X.
        apply X with x s.
        -- intros Hcon.
           apply H.
           apply AFI_ConsB1_NonRec.
           assumption.
        -- assumption.
      * unfold P_Bindings_NonRec in IHbs.
        apply IHbs with x s.
        -- apply Util.ForallT_tl in X.
           assumption.
        -- intros Hcon.
           apply H.
           apply AFI_ConsB2_NonRec.
           ++ assumption.
           ++ assumption.
        -- assumption.
Qed.

Definition P_Bindings_Rec (bs : list Binding) :=
  Util.ForallT P_Binding bs ->
  forall x,
    ~(appears_free_in_bindings_rec x bs) ->
    forall s bs',
      substitute_bindings_rec x s bs bs' ->
      bs' = bs.

Lemma P_Bindings_Rec__holds_definitionally : forall bs, P_Bindings_Rec bs.
Proof.
  induction bs.
  - unfold P_Bindings_Rec. intros.
    inversion H0. subst.
    reflexivity.
  - unfold P_Bindings_Rec. intros.
    inversion H0.
    subst.
    f_equal.
    + apply Util.ForallT_hd in X.
      unfold P_Binding in X.
      apply X with x s.
      * intros Hcon.
        apply H.
        apply AFI_ConsB1_Rec.
        assumption.
      * assumption.
    + unfold P_Bindings_Rec in IHbs.
      apply IHbs with x s.
      * apply Util.ForallT_tl in X.
        assumption.
      * intros Hcon.
        apply H.
        apply AFI_ConsB2_Rec.
        assumption.
      * assumption.
Qed.

Lemma vacuous_substitution : forall t, P_Term t.
Proof.
  apply Term_rect' with (P := P_Term) (Q := P_Binding).
  - (* Let *)
    intros. unfold P_Term. intros.
    inversion H1; subst.
    + (* S_Let1 *)
      f_equal.
      assert (P_Bindings_NonRec bs) by apply P_Bindings_NonRec__holds_definitionally.
      unfold P_Bindings_NonRec in H2.
      apply H2 with x s.
      * assumption.
      * intros Hcon.
        apply H0.
        apply AFI_LetNonRec.
        assumption.
      * assumption.
    + (* S_Let2 *)
      f_equal.
      * assert (P_Bindings_NonRec bs) by apply P_Bindings_NonRec__holds_definitionally.
        unfold P_Bindings_NonRec in H2.
        apply H2 with x s.
        -- assumption.
        -- intros Hcon.
           apply H0.
           apply AFI_LetNonRec.
           assumption.
        -- assumption.
      * unfold P_Term in H.
        apply H with x s.
        -- intros Hcon.
           apply H0.
           apply AFI_Let.
           ++ assumption.
           ++ assumption.
        -- assumption.
    + (* S_LetRec1 *)
      reflexivity.
    + (* S_LetRec2 *)
      f_equal.
      * assert (P_Bindings_Rec bs) by apply P_Bindings_Rec__holds_definitionally.
        unfold P_Bindings_Rec in H2.
        apply H2 with x s.
        -- assumption.
        -- intros Hcon.
           apply H0.
           apply AFI_LetRec.
           ++ assumption.
           ++ assumption.
        -- assumption.
      * unfold P_Term in H.
        apply H with x s.
        -- intros Hcon.
           apply H0.
           apply AFI_Let.
           ++ assumption.
           ++ assumption.
        -- assumption.
  - (* Var *)
    intros. unfold P_Term. intros.
    inversion H0.
    + (* S_Var1 *)
      subst.
      assert (appears_free_in s (Var s)) by constructor.
      apply H in H1.
      destruct H1.
    + (* S_Var2 *)
      reflexivity.
  - (* TyAbs *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s0.
    + intros Hcon.
      apply H0.
      apply AFI_TyAbs.
      assumption.
    + assumption.
  - (* LamAbs *)
    intros. unfold P_Term. intros.
    inversion H1.
    + (* S_LamAbs1 *)
      reflexivity.
    + (* S_LamAbs2 *)
      subst.
      f_equal.
      unfold P_Term in H.
      apply H with x s0.
      * intros Hcon.
        apply H0.
        apply AFI_LamAbs.
        -- assumption.
        -- assumption.
      * assumption.
  - (* Apply *)
    intros. unfold P_Term. intros.
    inversion H2. subst.
    f_equal.
    + unfold P_Term in H. 
      apply H with x s.
      * intros Hcon.
        apply H1.
        apply AFI_Apply1.
        assumption.
      * assumption.
    + unfold P_Term in H0.
      apply H0 with x s.
      * intros Hcon.
        apply H1.
        apply AFI_Apply2.
        assumption.
      * assumption.
  - (* Constant *)
    intros. unfold P_Term. intros.
    inversion H0. subst.
    reflexivity.
  - (* Builtin *)
    intros. unfold P_Term. intros.
    inversion H0. subst.
    reflexivity.
  - (* TyInst *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s.
    + intros Hcon.
      apply H0.
      apply AFI_TyInst.
      assumption.
    + assumption.
  - (* Error *)
    intros. unfold P_Term. intros.
    inversion H0. subst.
    reflexivity.
  - (* IWrap *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s.
    + intros Hcon.
      apply H0.
      apply AFI_IWrap.
      assumption.
    + assumption.
  - (* Unwrap *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s.
    + intros Hcon.
      apply H0.
      apply AFI_Unwrap.
      assumption.
    + assumption.

  - (* TermBind *)
    intros. unfold P_Binding. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s0.
    + intros Hcon.
      apply H0.
      apply AFI_TermBind.
      assumption.
    + assumption.
  - (* TypeBind *)
    intros. unfold P_Binding. intros.
    inversion H0. subst.
    reflexivity.
  - (* DatatypeBind *)
    intros. unfold P_Binding. intros.
    inversion H0. subst.
    reflexivity.
Qed.

Lemma subst_closed : forall t,
    closed t -> 
    forall x s t',
      substitute x s t t' ->
      t' = t.
Proof. Admitted.

Lemma subst_not_afi : forall t x v,
    closed v ->
    forall t',
      substitute x v t t' ->
      ~(appears_free_in x t').
Proof. Admitted.

Lemma duplicate_subst : forall x t v s,
    closed v ->
    forall t' t'',
      substitute x v t t' ->
      substitute x s t' t'' ->
      t'' = t'.
Proof. Admitted.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v ->
    closed v1 ->
    forall t1 t2 t3 t4,
      substitute x v t t1 ->
      substitute x1 v1 t1 t2 ->
      substitute x1 v1 t t3 ->
      substitute x v t3 t4 ->
      t2 = t4.
Proof. Admitted.



(** ** Properties of multi-substitutions *)

Lemma msubst_closed : forall t,
    closed t ->
    forall ss t',
      msubst ss t t' ->
      t' = t.
Proof. Admitted.

Fixpoint closed_env (env : env) :=
  match env with
  | nil => True
  | (x,t) :: env' => closed t /\ closed_env env'
  end.

Fixpoint value_env (env : env) :=
  match env with
  | nil => True
  | (x,t) :: env' => value t /\ value_env env'
  end.

Lemma subst_msubst : forall env x v t,
    closed v ->
    closed_env env ->
    forall t1 t2 t3 t4,
      substitute x v t t1 ->
      msubst env t1 t2 ->
      msubst (drop x env) t t3 ->
      substitute x v t3 t4 ->
      t2 = t4.
Proof. Admitted.

Lemma msubst_Var : forall ss x,
    closed_env ss ->
    value_env ss ->
    forall t',
      msubst ss (Var x) t' ->
        match lookup x ss with
        | Datatypes.Some t => t' = t /\ value t 
        | None=> t' = Var x
        end.
Proof. 
  induction ss; intros.
  - inversion H1. subst.
    reflexivity.
  - inversion H1. subst.
    simpl.
    inversion H4; subst.
    + rewrite String.eqb_refl.
      split.
      * eapply msubst_closed; eauto.
        inversion H; auto.
      * destruct H0. 
        assumption. 
    + apply String.eqb_neq in H6.
      rewrite H6.
      apply IHss; eauto.
      inversion H; auto.
      inversion H0; auto.
Qed.

Lemma msubst_LamAbs : forall ss x T t0 t',
    closed_env ss ->
    msubst ss (LamAbs x T t0) t' ->
    exists t0', msubst (drop x ss) t0 t0' /\ t' = LamAbs x T t0'.
Proof.
  induction ss.
  - intros. 
    inversion H0. subst.
    exists t0.
    split. 
    + apply msubst_nil.
    + reflexivity. 
  - intros.
    inversion H0. subst.
    rename t'0 into t''.
    destruct H.
    inversion H3.
    + subst.
      simpl.
      rewrite eqb_refl.
      eapply IHss; eauto.
    + subst.
      simpl.
      apply eqb_neq in H10.
      rewrite H10.
      edestruct IHss as [t0'' Hms0']; eauto.
      eexists.
      split.
      -- eapply msubst_cons.
         ++ apply H11.
         ++ apply Hms0'.
      -- destruct Hms0'.
         subst.
         reflexivity.
Qed.

Lemma msubst_Apply : forall ss t1 t2 t',
    msubst ss (Apply t1 t2) t' ->
    exists t1' t2', msubst ss t1 t1' /\ msubst ss t2 t2' /\ t' = (Apply t1' t2').
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists t1, t2.
    eauto using msubst_nil, msubst_cons. 
  - inversion H. subst.
    rename t'0 into t''.
    inversion H2. subst.
    apply IHss in H5.
    destruct H5 as [t1'' [t2'' [H9 [H10 H11]]]].
    exists t1'', t2''.
    split. {
      apply msubst_cons with t1'.
      + assumption.
      + apply H9.
    }
    split. {
      apply msubst_cons with t2'.
      + assumption.
      + apply H10.
    }
    assumption.
Qed.

Lemma msubst_Constant : forall ss sv t',
  msubst ss (Constant sv) t' ->
  t' = Constant sv.
Proof.
  induction ss; intros.
  - inversion H. subst. reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    eauto.
Qed.

Lemma msubst_IWrap : forall ss F T M t',
    msubst ss (IWrap F T M) t' ->
    exists M', msubst ss M M' /\ t' = IWrap F T M'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists M. split. constructor. reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    rename t0' into M'.
    eapply IHss in H5.
    destruct H5 as [M'' [H0 H1]].
    subst.
    exists M''.
    split.
    + eapply msubst_cons; eauto.
    + reflexivity.
Qed.

Lemma msubst_Unwrap : forall ss M t',
    msubst ss (Unwrap M) t' ->
    exists M', msubst ss M M' /\ t' = Unwrap M'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists M. split. constructor. reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    rename t0' into M'.
    eapply IHss in H5.
    destruct H5 as [M'' [H0 H1]].
    subst.
    exists M''.
    split.
    + eapply msubst_cons; eauto.
    + reflexivity.
Qed.

(** ** Properties of multi-extensions *)

Lemma mupdate_lookup : forall (c : tass) (x : name),
    lookup x c = lookupT (mupdate emptyContext c) x.
Proof. Admitted.

Lemma mupdate_drop : forall (c : tass) Gamma x x',
      lookupT (mupdate Gamma (drop x c)) x' 
    = if String.eqb x x' 
        then lookupT Gamma x' 
        else lookupT (mupdate Gamma c) x'.
Proof. Admitted.

(** ** Properties of Instantiations *)

Lemma instantiation_domains_match : forall c e1 e2 k,
    instantiation k c e1 e2 ->
    forall x T,
      lookup x c = Datatypes.Some T ->
      exists v1 v2,
        lookup x e1 = Datatypes.Some v1 /\
        lookup x e2 = Datatypes.Some v2.
Proof.
  intros k c e1 e2 V. 
  induction V; intros x0 T0 C.
  - discriminate.
  - simpl.
    simpl in C.
    destruct (x =? x0) eqn:Heqb.
    + exists v1, v2. auto.
    + apply IHV with T0.
      assumption.
Qed.

Lemma instantiation_env_closed : forall k c e1 e2,
    instantiation k c e1 e2 ->
    closed_env e1 /\ closed_env e2.
Proof.
  intros k c e1 e2 V.
  induction V; intros.
  - split; reflexivity.
  - split.
    + simpl.
      split.
      * apply typable_empty__closed with T.
        apply RC_typable_empty_1 with k v2.
        assumption.
      * apply IHV.
    + simpl.
      split.
      * apply typable_empty__closed with T.
        apply RC_typable_empty_2 with k v1.
        assumption.
      * apply IHV.
Qed.

Corollary instantiation_env_closed_1 : forall k c e1 e2,
    instantiation k c e1 e2 ->
    closed_env e1.
Proof. intros. destruct (instantiation_env_closed _ _ _ _ H). assumption. Qed.

Corollary instantiation_env_closed_2 : forall k c e1 e2,
    instantiation k c e1 e2 ->
    closed_env e2.
Proof. intros. destruct (instantiation_env_closed _ _ _ _ H). assumption. Qed.

Lemma instantiation_env_values : forall k c e1 e2,
    instantiation k c e1 e2 ->
    value_env e1 /\ value_env e2.
Proof.
  intros k c e1 e2 V.
  induction V; intros.
  - split; reflexivity.
  - split.
    + simpl.
      split.
      * assumption.
      * apply IHV.
    + simpl.
      split.
      * assumption.
      * apply IHV.
Qed.

Lemma instantiation_env_values_1 : forall k c e1 e2,
    instantiation k c e1 e2 ->
    value_env e1.
Proof. intros. destruct (instantiation_env_values _ _ _ _ H). assumption. Qed.

Lemma instantiation_env_values_2 : forall k c e1 e2,
    instantiation k c e1 e2 ->
    value_env e2.
Proof. intros. destruct (instantiation_env_values _ _ _ _ H). assumption. Qed.

Lemma instantiation_R : forall k c e1 e2,
    instantiation k c e1 e2 ->
    forall x T v1 v2,
      lookup x c = Datatypes.Some T ->
      lookup x e1 = Datatypes.Some v1 ->
      lookup x e2 = Datatypes.Some v2 ->
      RC k T v1 v2.
Proof.
  intros k c e1 e2 V.
  induction V; intros x' T' v1' v2' G E1 E2.
  - destruct x'; discriminate.
  - inversion G. subst.
    inversion E1. subst.
    inversion E2. subst.
    destruct (x =? x').
    + inversion H3. subst.
      inversion H4. subst.
      inversion H5. subst.
      assumption. 
    + apply IHV with x'; assumption.
Qed.

Lemma instantiation_drop : forall k c e1 e2,
    instantiation k c e1 e2 ->
    forall x,
      instantiation k (drop x c) (drop x e1) (drop x e2).
Proof.
  intros k c e1 e2 V.
  induction V.
  - intros. simpl. apply V_nil.
  - intros. simpl.
    destruct (x =? x0).
    + apply IHV.
    + apply V_cons.
      * assumption.
      * assumption.
      * assumption.
      * apply IHV.
Qed.

(** ** Congruence lemmas on [eval] *)

(** ** Multi-substitutions preserve typing *)

Lemma msubst_preserves_typing_1 : forall k c e1 e2,
    instantiation k c e1 e2 ->
    forall Gamma t t' S,
      (mupdate Gamma c) |-+ t : S ->
      msubst e1 t t' ->
      Gamma |-+ t': S. 
Proof.
  intros k c e1 e2 V.
  induction V.
  - intros.
    simpl in H.
    inversion H0. subst.
    assumption.
  - intros.
    simpl in H2.
    inversion H3. subst.
    apply IHV with t'0.
    + eapply substitution_preserves_typing.
      * apply H2.
      * apply RC_typable_empty_1 with k v2.
        apply H1.
      * apply H9.
    + apply H10.
Qed. 

Lemma msubst_preserves_typing_2 : forall k c e1 e2,
    instantiation k c e1 e2 ->
    forall Gamma t t' S,
      (mupdate Gamma c) |-+ t : S ->
      msubst e2 t t' ->
      Gamma |-+ t': S. 
Proof.
  intros k c e1 e2 V.
  induction V.
  - intros.
    simpl in H.
    inversion H0. subst.
    assumption.
  - intros.
    simpl in H2.
    inversion H3. subst.
    apply IHV with t'0.
    + eapply substitution_preserves_typing.
      * apply H2.
      * apply RC_typable_empty_2 with k v1.
        apply H1.
      * apply H9.
    + apply H10.
Qed. 

(** ** The [R] Lemma *)

Definition P_has_type Gamma t1 T := 
  forall k c e1 e2,
    Gamma = mupdate emptyContext c ->
    Gamma |-+ t1 : T ->
    Gamma |-+ t1 : T ->
    instantiation k c e1 e2 ->
    forall t2 t3,
      msubst e1 t1 t2 ->
      msubst e2 t1 t3 ->
      RC k T t2 t3.

Definition P_constructor_well_formed Gamma c := Gamma |-ok_c c.

Definition P_bindings_well_formed_nonrec Gamma bs1 := Gamma |-oks_nr bs1.

Definition P_bindings_well_formed_rec Gamma bs1 := Gamma |-oks_r bs1.

Definition P_binding_well_formed Gamma b1 := Gamma |-ok b1.

Axiom skip : forall P, P.

 (*forall c e1 e2 t1 t2 T,
    (mupdate emptyContext c) |-+ t1 : T ->
    (mupdate emptyContext c) |-+ t2 : T ->
    instantiation c e1 e2 ->
    CNR_Term t1 t2 ->
    forall t1' t2',
      msubst e1 t1 t1' ->
      msubst e2 t2 t2' ->
      R T t1' t2'.*)

Lemma msubst_R : forall Gamma t1 T,
    Gamma |-+ t1 : T ->
    P_has_type Gamma t1 T.
Proof.
  apply has_type__ind with 
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).
  - intros. unfold P_has_type. intros. subst.
    apply skip.
  - intros. unfold P_has_type. intros. subst.
    apply skip.

  - (* T_Var *)
    intros. 
    unfold P_has_type. 
    intros k c e1 e2 Heq Htyp_t1 _ V v2 v3 Hms_v2 Hms_v3.
    subst.

    assert (forall x, lookupT (mupdate emptyContext c) x = lookup x c). {
      intros. rewrite mupdate_lookup. auto.
    }
    rewrite H0 in H.
    destruct (instantiation_domains_match _ _ _ _ V _ _ H) as [v2' [v3' [Hlu_v2' Hlu_v3']]].
    destruct (instantiation_env_closed _ _ _ _ V) as [He1 He2].
    destruct (instantiation_env_values _ _ _ _ V) as [Hvals_e1 Hvals_e2].

    eapply instantiation_R.
    + eassumption.
    + eassumption.
    + apply msubst_Var in Hms_v2; eauto.
      rewrite Hlu_v2' in Hms_v2.
      destruct Hms_v2. subst.
      assumption.
    + apply msubst_Var in Hms_v3; eauto.
      rewrite Hlu_v3' in Hms_v3.
      destruct Hms_v3. subst.
      assumption.

  - (* T_Forall *)
    intros Gamma X K t0_1 T Htyp_t IH. 
    unfold P_has_type. 
    intros c e1 e2 ixs Heq Htyp_t1 _ V v2 v3 Hms_v2 Hms_v3.
    subst.

    apply skip.

  - (* T_LamAbs *)
    intros Gamma x T1 t0_1 T2 Htyp__t0_1 IH Hkin_T1.
    unfold P_has_type.
    intros k c e1 e2 Heq Htyp_t1 _ V v2 v3 Hms_v2 Hms_v3.
    subst.

    assert (Hcls1 : closed_env e1) by (eapply instantiation_env_closed_1; eauto).
    assert (Hcls2 : closed_env e2) by (eapply instantiation_env_closed_2; eauto).
    destruct (msubst_LamAbs _ _ _ _ _ Hcls1 Hms_v2) as [t0_2 [Hms__t0_2 Heq1]].
    destruct (msubst_LamAbs _ _ _ _ _ Hcls2 Hms_v3) as [t0_3 [Hms__t0_3 Heq2]].
    subst.
    clear Hcls1 Hcls2.

    assert (emptyContext |-+ (LamAbs x T1 t0_2) : (Ty_Fun T1 T2)) by eauto using msubst_preserves_typing_1.
    assert (emptyContext |-+ (LamAbs x T1 t0_3) : (Ty_Fun T1 T2)) by eauto using msubst_preserves_typing_2.

    unfold P_has_type in IH.

    autorewrite with RC.
    split; auto. split; auto.
    intros j Hlt__j e_f Hev__e_f.
    inversion Hev__e_f. subst.
    exists (LamAbs x T1 t0_3).
    exists 0.
    split. {
      eapply eval_value. apply V_LamAbs.
    }
    intros.
    inversion H1. subst.
    inversion H2. subst.

    assert (msubst ((x', v) :: drop x' e1) t0_1 e_body'). { apply skip. }
    assert (msubst ((x', v') :: drop x' e2) t0_1 e'_body'). { apply skip. }

    eapply IH; eauto.
    + assert (x' |T-> T1; mupdate emptyContext c = mupdate emptyContext ((x', T1) :: drop x' c)). {
        apply skip.
      }
      apply H10.
    + apply V_cons; eauto.
      eapply instantiation_drop.
      apply skip.

  - (* T_Apply *)
    intros Gamma t1 t2 T1 T2 Htyp_t1 IH_t1 Htyp_t2 IH_t2.
    unfold P_has_type.
    intros k c e1 e2 Heq Htyp _ V t3 t4 Hms_t3 Hms_t4.
    subst.
    
    destruct (msubst_Apply _ _ _ _ Hms_t3) as [t3_1 [t3_2 [Hms_t3_1 [Hms_t3_2 Heq_t3]]]].
    subst.
    destruct (msubst_Apply _ _ _ _ Hms_t4) as [t4_1 [t4_2 [Hms_t4_1 [Hms_t4_2 Heq_t4]]]].
    subst.

    assert (emptyContext |-+ (Apply t3_1 t3_2) : T2) by eauto using msubst_preserves_typing_1.
    assert (emptyContext |-+ (Apply t4_1 t4_2) : T2) by eauto using msubst_preserves_typing_2.

    assert (R1: RC k (Ty_Fun T1 T2) t3_1 t4_1) by (eapply IH_t1; eauto; apply skip).
    assert (R2: RC k T1 t3_2 t4_2) by (eapply IH_t2; eauto; apply skip).

    eapply RC_compatibility_Apply; eauto.
  
  - (* T_Constant *)
    intros Gamma u a.
    unfold P_has_type.
    intros k c e1 e2 Heq Htyp_t1 _ V t2 t3 Hmsubst_t2 Hmsubst_t3.

    apply msubst_Constant in Hmsubst_t2 as Heq2.
    apply msubst_Constant in Hmsubst_t3 as Heq3.
    subst.

    apply RC_compatibility_Constant.
    
  - (* T_Builtin*)
    apply skip.

  - (* T_TyInst *)
    apply skip.

  - (* T_Error *)
    apply skip.

  - (* T_IWrap *)
    intros Gamma F T M K S Hbr Htyp_M IH_M Hkind_T Hkind_F.
    unfold P_has_type.
    intros k c e1 e2 Heq Htyp _ V t2 t3 Hmsubst_t2 Hmsubst_t3.

    unfold P_has_type in IH_M.

    assert (exists M', msubst e1 M M' /\ t2 = IWrap F T M')
      by eauto using msubst_IWrap.
    destruct H as [M' [Hmsubst_M' Heq_t2]].
    subst.

    assert (exists M'', msubst e2 M M'' /\ t3 = IWrap F T M'')
      by eauto using msubst_IWrap.
    destruct H as [M'' [Hmsubst_M'' Heq_t3]].
    subst.

    assert (emptyContext |-+ (IWrap F T M') : (Ty_IFix F T)) by eauto using msubst_preserves_typing_1.
    assert (emptyContext |-+ (IWrap F T M'') : (Ty_IFix F T)) by eauto using msubst_preserves_typing_2.

    assert (RC k (beta_reduce (unwrapIFix F K T)) M' M''). {
      eapply IH_M; eauto.
    }

    eapply RC_compatibility_IWrap; eauto.
    + inversion H. subst. auto. apply skip. (* TODO *)
    + inversion H0. subst. auto. apply skip. (* TODO *)

  - (* T_Unwrap *)
    intros Gamma M F K T S Htyp_M IH_M Hkind_T Hbr.
    unfold P_has_type.
    intros k c e1 e2 Heq Htyp _ V t2 t3 Hmsubst_t2 Hmsubst_t3.

    unfold P_has_type in IH_M.

    assert (exists M', msubst e1 M M' /\ t2 = Unwrap M')
      by eauto using msubst_Unwrap.
    destruct H as [M' [Hmsubst_M' Heq_t2]].
    subst.

    assert (exists M'', msubst e2 M M'' /\ t3 = Unwrap M'')
      by eauto using msubst_Unwrap.
    destruct H as [M'' [Hmsubst_M'' Heq_t3]].
    subst.

    assert (emptyContext |-+ (Unwrap M') : (beta_reduce (unwrapIFix F K T))) 
      by eauto using msubst_preserves_typing_1.
    assert (emptyContext |-+ (Unwrap M'') : (beta_reduce (unwrapIFix F K T)))
      by eauto using msubst_preserves_typing_2.

    assert (RC k (Ty_IFix F T) M' M''). {
      eapply IH_M; eauto.
    }

    eapply RC_compatibility_Unwrap; eauto.
    + inversion H. subst. apply skip. (* TODO *)

  - 

Abort.