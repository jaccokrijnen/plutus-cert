Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

Notation beta_reduce := (beta_reduce).

Definition terminates := fun t => exists v, t ==> v.

(* Note: The cases for Ty_Forall and and Ty_IFix make use of
   type substitution and beta reduction. However, Coq can then not
   guess the decreasing argument of fix anymore. *)
Fixpoint R (k : nat) (T : Ty) (t1 t2 : Term) {struct k} : Prop :=
  emptyContext |-+ t1 : T /\
  emptyContext |-+ t2 : T /\
  forall v1,
    t1 ==> v1 ->
    exists v2,
      t2 ==> v2 /\
        match T with
        | Ty_Forall X K T0 => 
            match k with 
            | 0 => 
                False
            | S k' =>
                forall t0_1 t0_2 T',
                  v1 = TyAbs X K t0_1 ->
                  v2 = TyAbs X K t0_2 ->
                  forall H : emptyContext |-* T' : K,
                  R k' (beta_reduce (substituteT X T' T0)) (TyInst v1 T') (TyInst v2 T')
            end
        | Ty_Fun T1 T2 => 
            match k with
            | 0 =>
                False
            | S k' =>
                forall s1 s2,
                  R k' T1 s1 s2 ->
                  R k' T2 (Apply v1 s1) (Apply v2 s2)
            end
        | Ty_Builtin st => 
            v1 = v2
        | Ty_IFix F T0 => 
            match k with
            | 0 =>
                False
            | S k' =>
                forall X K,
                  emptyContext |-* T : K ->
                  R k' (beta_reduce (unwrapIFix F X K T0)) (Unwrap v1) (Unwrap v2)
            end
        |_ => False
        end.

Lemma R_typable_empty : forall k T t1 t2,
    R k T t1 t2 ->
    emptyContext |-+ t1 : T /\ emptyContext |-+ t2 : T.
Proof. intros. destruct k, T; destruct H as [Ht1 [Ht2 _]]; auto. Qed.

Lemma R_typable_empty_1 : forall k T t1 t2,
    R k T t1 t2 ->
    emptyContext |-+ t1 : T.
Proof. intros. destruct (R_typable_empty _ _ _ _ H). assumption. Qed.

Lemma R_typable_empty_2 : forall k T t1 t2,
    R k T t1 t2 ->
    emptyContext |-+ t2 : T.
Proof. intros. destruct (R_typable_empty _ _ _ _ H). assumption. Qed.

Lemma R_evaluable : forall k T t1 t2,
    terminates t1 ->
    R k T t1 t2 ->
    exists v1 v2, t1 ==> v1 /\ t2 ==> v2.
Proof. intros. destruct H. destruct k, T; destruct H0 as [_ [_ [v1 [Hev2 _]]]]; eauto. Qed.

Lemma R_evaluable_1 : forall k T t1 t2,
    terminates t1 ->
    R k T t1 t2 ->
    exists v1, t1 ==> v1.
Proof. intros. destruct (R_evaluable _ _ _ _ H H0) as [v1 [_ [Hev1 _]]]. eauto. Qed.

Lemma R_evaluable_2 : forall k T t1 t2,
    terminates t1 ->
    R k T t1 t2 ->
    exists v2, t2 ==> v2.
Proof. intros. destruct (R_evaluable _ _ _ _ H H0) as [_ [v2 [_ Hev2]]]. eauto. Qed.

Lemma R_syntactic_equality : forall k st t1 t2,
    terminates t1 ->
    R k (Ty_Builtin st) t1 t2 ->
    exists v1 v2,
      t1 ==> v1 /\
      t2 ==> v2 /\
      v1 = v2.
Proof. intros. destruct H. destruct k; destruct H0 as [_ [_ [v2 [Hev2 Heq]]]]; eauto. Qed.

Lemma R_functional_extensionality : forall k' T1 T2 t1 t2,
    terminates t1 ->
    R (S k') (Ty_Fun T1 T2) t1 t2 ->
    exists v1 v2,
      t1 ==> v1 /\
      t2 ==> v2 /\
      (forall s1 s2,
        R k' T1 s1 s2 ->
        R k' T2 (Apply v1 s1) (Apply v2 s2)).
Proof. intros. destruct H. destruct H0 as [_ [_ [v2 [Hev2 Hfe]]]]; eauto. Qed.

Lemma R_impossible_type : forall k t1 t2,
    terminates t1 ->
    (forall a, ~(R k (Ty_Var a) t1 t2)) /\
    (forall bX K T, ~(R k (Ty_Lam bX K T) t1 t2)) /\
    (forall T1 T2, ~(R k (Ty_App T1 T2) t1 t2)).
Proof.
  intros. destruct H. 
  split; try split; try solve [intros; intro Hcon; destruct k; destruct Hcon as [_ [_ [_ [_ Hfalse]]]]; eauto].
Qed.

Lemma R_impossible_k : forall t1 t2,
    terminates t1 ->
    (forall T1 T2, ~(R 0 (Ty_Fun T1 T2) t1 t2)) /\
    (forall X K T0, ~(R 0 (Ty_Forall X K T0) t1 t2)).
Proof.
  intros. destruct H.
  split; intros; try solve [intros Hcon; destruct Hcon as [_ [_ [_ [_ Hfls]]]]; eauto].
Qed.

Lemma R_nontermination : forall k T t1 t2,
    ~(terminates t1) ->
    emptyContext |-+ t1 : T ->
    emptyContext |-+ t2 : T ->
    R k T t1 t2.
Proof. intros. destruct k; destruct T; try solve [split; eauto; split; eauto; intros v1 Hcon; exfalso; apply H; exists v1; auto]. Qed.

Axiom skip: forall P, P.

Lemma R_monotone : forall k1 k2 T t1 t2,
  terminates t1 ->
  R k1 T t1 t2 ->
  k1 < k2 ->
  R k2 T t1 t2.
Proof.
  intros k1 k2 T.
  generalize dependent k2.
  generalize dependent k1.
  induction T; intros.
  - apply R_impossible_type in H0; eauto. destruct H0.
  - destruct k1; destruct k2.
    + apply PeanoNat.Nat.nlt_0_r in H1. destruct H1.
    + apply R_impossible_k in H0. destruct H0. assumption.
    + apply PeanoNat.Nat.nlt_0_r in H1. destruct H1.
    + destruct (R_typable_empty _ _ _ _ H0).
      split; auto.
      split; auto.
      destruct (R_functional_extensionality _ _ _ _ _ H H0) as [v1 [v2 [Hev1 [Hev2 Hfe]]]].
      intros.
      exists v2.
      split; auto.
      assert (v0 = v1) by (eapply eval__deterministic; eauto).
      subst.
      intros.
      apply skip.
  - destruct k1; destruct k2; destruct (R_typable_empty _ _ _ _ H0); eauto.
Abort.