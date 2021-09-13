Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

Require Import Arith.


Definition terminates := fun t k => exists v j, j < k /\ t =[j]=> v.

Lemma e : forall i j k,
  i < k ->
  j < k - i ->
  j < k.
Proof. Admitted.


(* Note: The cases for Ty_Forall and and Ty_IFix make use of
   type substitution and beta reduction. However, Coq can then not
   guess the decreasing argument of fix anymore. *)
Equations? R (k : nat ) (T : Ty) (t1 t2 : Term) : Prop by wf k :=
  R k T t1 t2 =>
  emptyContext |-+ t1 : T /\
  emptyContext |-+ t2 : T /\
  forall v1 j1,
    forall (Hj1 : j1 < k),
    t1 =[j1]=> v1 ->
    exists v2 j2,
      t2 =[j2]=> v2 /\
        match T with
        | Ty_Forall X K T0 => 
            forall t0_1 t0_2 T' j,
              forall (Hj : j < k - j1),
              v1 = TyAbs X K t0_1 ->
              v2 = TyAbs X K t0_2 ->
              emptyContext |-* T' : K ->
              R j (beta_reduce (substituteT X T' T0)) v1 v2
        | Ty_Fun T1 T2 => 
            forall s1 s2 j,
              forall (Hj : j < k - j1),
              R j T1 s1 s2 ->
              R j T2 (Apply v1 s1) (Apply v2 s2)
        | Ty_Builtin st => 
            v1 = v2
        | Ty_IFix F T0 => 
            forall X K j,
              forall (Hj : j < k - j1),
              emptyContext |-* T0 : K ->
              R j (beta_reduce (unwrapIFix F X K T0)) v1 v2
        | _ => False (* Ty_Lam, Ty_Abs and Ty_Var should not occur *)
        end.
Proof. all: try solve [eapply e; eauto]. Qed.

Lemma monotonicity : forall k T v1 v2 j,
  value v1 ->
  value v2 ->
  j <= k ->
  R k T v1 v2 ->
  R j T v1 v2.
Proof.
  destruct T.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
    destruct H7.
    destruct H7.
    exists x.
    exists x0.
    split; auto.

    intros.
    eapply H8.
    + apply skip. 
    + assumption.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
    destruct H7.
    destruct H7.
    exists x.
    exists x0.
    split; auto.

    intros.
    eapply H8.
    + apply skip. 
    + assumption.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
    destruct H7.
    destruct H7.
    exists x.
    exists x0.
    split; auto.

    intros.
    eapply H8.
    + apply skip. 
    + eassumption.
    + eassumption.
    + eassumption.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
Qed.

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
    terminates t1 k ->
    R k T t1 t2 ->
    exists v1 v2 j1 j2, t1 =[j1]=> v1 /\ t2 =[j2]=> v2.
Proof. intros. destruct H. destruct H. destruct H. autorewrite with R in H0.
  destruct T; destruct H0 as [_ [_ [v2 [j2 [Hev2 _]]]]]; eauto; 
    try solve [eexists; eexists; eexists; eexists; eauto].
Qed.

Lemma R_evaluable_1 : forall k T t1 t2,
    terminates t1 k ->
    R k T t1 t2 ->
    exists v1 j1, t1 =[j1]=> v1.
Proof. intros. destruct (R_evaluable _ _ _ _ H H0) as [v1 [_ [j1 [_ [Hev1 _]]]]]; eauto. Qed.

Lemma R_evaluable_2 : forall k T t1 t2,
    terminates t1 k ->
    R k T t1 t2 ->
    exists v2 j2, t2 =[j2]=> v2.
Proof. intros. destruct (R_evaluable _ _ _ _ H H0) as [_ [v2 [_ [j2 [_ Hev2]]]]]; eauto. Qed.

Lemma R_syntactic_equality : forall k st t1 t2,
    terminates t1 k ->
    R k (Ty_Builtin st) t1 t2 ->
    exists v1 v2 j1 j2,
      t1 =[j1]=> v1 /\
      t2 =[j2]=> v2 /\
      v1 = v2.
Proof. 
  intros. destruct H. destruct H. destruct H. destruct H0 as [_ [_ [v2 [j2 [Hev2 Heq]]]]]; eauto.
  eexists. eexists. eexists. eexists. eauto. 
Qed.

Lemma R_functional_extensionality : forall k T1 T2 t1 t2,
    terminates t1 k ->
    R k (Ty_Fun T1 T2) t1 t2 ->
    exists v1 v2 j1 j2,
      t1 =[j1]=> v1 /\
      t2 =[j2]=> v2 /\
      (forall s1 s2 j,
        j < k - j1 ->
        R j T1 s1 s2 ->
        R j T2 (Apply v1 s1) (Apply v2 s2)).
Proof. 
  intros. destruct H. destruct H. destruct H.
  autorewrite with R in H0.
  destruct H0.
  destruct H2.
  edestruct H3; eauto.
  destruct H4.
  destruct H4.
  exists x.
  exists x1.
  exists x0.
  exists x2.
  split; eauto.
Qed.

Lemma R_impossible_type : forall k t1 t2,
    terminates t1 k ->
    (forall a, ~(R k (Ty_Var a) t1 t2)) /\
    (forall bX K T, ~(R k (Ty_Lam bX K T) t1 t2)) /\
    (forall T1 T2, ~(R k (Ty_App T1 T2) t1 t2)).
Proof.
  intros. destruct H. destruct H. destruct H. 
  split; try split; try solve [intros; intro Hcon; destruct k; destruct Hcon as [_ [_ [_ [_ [_ Hfls]]]]]; eauto].
Qed.

Lemma R_impossible_k : forall t1 t2,
    terminates t1 0 ->
    (forall T1 T2, ~(R 0 (Ty_Fun T1 T2) t1 t2)) /\
    (forall X K T0, ~(R 0 (Ty_Forall X K T0) t1 t2)).
Proof.
  intros. destruct H.
  destruct H.
  destruct H.
  apply PeanoNat.Nat.nlt_0_r in H.
  destruct H.
Qed.

Lemma R_nontermination : forall k T t1 t2,
    ~(terminates t1) ->
    emptyContext |-+ t1 : T ->
    emptyContext |-+ t2 : T ->
    R k T t1 t2.
Proof. intros. destruct k; destruct T; try solve [split; eauto; split; eauto; intros v1 Hcon; exfalso; apply H; exists v1; auto]. Qed.

(* TODO: Possible fixes for R require a proof of well-founded recursion. I've tried out some things
   below, but I have not founda solution yet. *)
(* https://coq.inria.fr/refman/addendum/program.html *)
(* http://adam.chlipala.net/cpdt/html/Cpdt.GeneralRec.html *)

Fixpoint countBindingLocations (T : Ty) : nat := 
  match T with
  | Ty_Var X => 0
  | Ty_Fun T1 T2 => countBindingLocations T1 + countBindingLocations T2
  | Ty_IFix F T0 => countBindingLocations F + countBindingLocations T0
  | Ty_Forall X K T0 => 1 + countBindingLocations T0
  | Ty_Builtin st => 0
  | Ty_Lam X K T0 => 1 + countBindingLocations T0       
  | Ty_App T1 T2 => countBindingLocations T1 + countBindingLocations T2  
  end.

Program Fixpoint R'' (T : Ty) (t1 t2 : Term) {measure (countBindingLocations T)} : Prop :=
  emptyContext |-+ t1 : T /\
  emptyContext |-+ t2 : T /\
  exists v1 v2,
    t1 ==> v1 /\
    t2 ==> v2 /\
    match T with
    | Ty_Forall X K T0 => 
        forall t0 T',
          v1 = TyAbs X K t0 ->
          v2 = TyAbs X K t0 ->
          emptyContext |-* T' : K ->
          R'' (Named.beta_reduce (substituteT X T' T0)) (TyInst v1 T') (TyInst v2 T')
    | Ty_Fun T1 T2 => 
        forall s1 s2,
          R'' T1 s1 s2 ->
          R'' T2 (Apply v1 s1) (Apply v2 s2)
    | Ty_Builtin st => 
        v1 = v2
    | Ty_IFix F T0 => 
        forall X K,
          emptyContext |-* T : K ->
          R'' (Named.beta_reduce (unwrapIFix F X K T0)) (Unwrap v1) (Unwrap v2)
    |_ => False
    end.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

(* WF by countBindingLocations and size? *)
Equations R' (T : Ty) (t1 t2 : Term) : Prop by wf (countBindingLocations T) :=
  R' T t1 t2 =>
    emptyContext |-+ t1 : T /\
    emptyContext |-+ t2 : T /\
    exists v1 v2,
      t1 ==> v1 /\
      t2 ==> v2 /\
      match T with
      | Ty_Forall X K T0 => 
          forall t0 T',
            v1 = TyAbs X K t0 ->
            v2 = TyAbs X K t0 ->
            emptyContext |-* T' : K ->
            R' (Named.beta_reduce (substituteT X T' T0)) (TyInst v1 T') (TyInst v2 T')
      | Ty_Fun T1 T2 => 
          forall s1 s2,
            R' T1 s1 s2 ->
            R' T2 (Apply v1 s1) (Apply v2 s2)
      | Ty_Builtin st => 
          v1 = v2
      | Ty_IFix F T0 => 
          forall X K,
            emptyContext |-* T : K ->
            R' (Named.beta_reduce (unwrapIFix F X K T0)) (Unwrap v1) (Unwrap v2)
      |_ => False
      end.
      

Fail Inductive R : Ty -> Term -> Term -> Prop :=
  | R_ : forall t1 t2 T,
      (emptyContext |-+ t1 : T /\
      emptyContext |-+ t2 : T /\
      exists v1 v2,
        t1 ==> v1 /\
        t2 ==> v2 /\
        R2 T v1 v2) ->
      R T t1 t2
      
with R2 : Ty -> Term -> Term -> Prop :=
  | R2_TyForall : forall X K T0,
      forall v1 v2 t0 T' S,
        v1 = TyAbs X K t0 ->
        v2 = TyAbs X K t0 ->
        emptyContext |-+ t0 : T0 ->
        emptyContext |-* T' : K ->
        substituteT X T' T0 =b S ->
        R S (TyInst v1 T') (TyInst v2 T') ->
        R2 (Ty_Forall X K T0) v1 v2
  | R2_TyFun : forall T1 T2 v1 v2,
      (forall s1 s2,
        R T1 s1 s2 ->
        R T2 (Apply v1 s1) (Apply v2 s2)) ->
      R2 (Ty_Fun T1 T2) v1 v2.
