Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

Require Import Arith.


Definition terminates_excl := fun t j v k => t =[j]=> v /\ j < k.
Definition terminates_incl := fun t j v k => t =[j]=> v /\ j <= k.

Lemma e : forall i j k,
i < k ->
j < k - i ->
j < k.
Proof. Admitted.

(*
(* Note: The cases for Ty_Forall and and Ty_IFix make use of
   type substitution and beta reduction. However, Coq can then not
   guess the decreasing argument of fix anymore. *)
Equations? R (k : nat ) (T : Ty) (t1 t2 : Term) : Prop by wf k :=
  R k T t1 t2 =>
    emptyContext |-+ t1 : T /\
    emptyContext |-+ t2 : T /\
    forall v1 j1,
      forall (Hlt_j1 : j1 < k),
      t1 =[j1]=> v1 ->
      exists v2 j2,
        t2 =[j2]=> v2 /\
          match T with
          | Ty_Forall X K T0 => 
              forall t0_1 t0_2 T' k',
                forall (Hlt_k' : k' < k - j1),
                v1 = TyAbs X K t0_1 ->
                v2 = TyAbs X K t0_2 ->
                emptyContext |-* T' : K ->
                R k' (beta_reduce (substituteT X T' T0)) v1 v2
          | Ty_Fun T1 T2 => 
              forall s1 s2 k',
                forall (Hlt_k' : k' < k - j1),
                R k' T1 s1 s2 ->
                R k' T2 (Apply v1 s1) (Apply v2 s2)
          | Ty_Builtin st => 
              v1 = v2
          | Ty_IFix F T0 => 
              forall K k',
                forall (Hlt_k' : k' < k - j1),
                emptyContext |-* T0 : K ->
                R k' (beta_reduce (unwrapIFix F K T0)) v1 v2
          | _ => False (* Ty_Lam, Ty_Abs and Ty_Var should not occur *)
          end.
Proof. all: try solve [eapply e; eauto]. Qed.
*)

Equations? R (k : nat ) (T : Ty) (t1 t2 : Term) : Prop by wf k :=
  R k T t1 t2 =>
    emptyContext |-+ t1 : T /\
    emptyContext |-+ t2 : T /\
    match T with
    | Ty_Forall X K T0 => 
        forall v1 j1,
          forall (Hlt_j1 : j1 < k),
          t1 =[j1]=> v1 ->
          exists v2 j2,
            t2 =[j2]=> v2 /\
            forall t0_1 t0_2 T' k',
              forall (Hlt_k' : k' < k - j1),
              v1 = TyAbs X K t0_1 ->
              v2 = TyAbs X K t0_2 ->
              emptyContext |-* T' : K ->
              R k' (beta_reduce (substituteT X T' T0)) v1 v2
    | Ty_Fun T1 T2 => 
        forall v1 j1,
          forall (Hlt_j1 : j1 < k),
          t1 =[j1]=> v1 ->
          exists v2 j2,
            t2 =[j2]=> v2 /\
            forall s1 s2 k' x1_0 x2_0 T1_0 T2_0 t1_0 t2_0 t1_0' t2_0',
              forall (Hlt_k' : k' < k - j1),
              v1 = LamAbs x1_0 T1_0 t1_0 ->
              v2 = LamAbs x2_0 T2_0 t2_0 ->
              R k' T1 s1 s2 ->
              substitute x1_0 s1 t1_0 t1_0' ->
              substitute x2_0 s2 t2_0 t2_0' ->
              R k' T2 t1_0' t2_0'
    | Ty_Builtin st => 
        forall v1 j1,
          forall (Hlt_j1 : j1 < k),
          t1 =[j1]=> v1 ->
          exists v2 j2,
            t2 =[j2]=> v2 /\
            v1 = v2
    | Ty_IFix F T0 => 
        forall v1 j1,
          forall (Hlt_j1 : j1 < k),
          t1 =[j1]=> v1 ->
          exists v2 j2,
            t2 =[j2]=> v2 /\
            forall K k',
              forall (Hlt_k' : k' < k - j1),
              emptyContext |-* T0 : K ->
              R k' (beta_reduce (unwrapIFix F K T0)) v1 v2
    | _ => False (* Ty_Lam, Ty_Lam and Ty_Var should not occur *)
    end.
Proof. all: try solve [eapply e; eauto]. Qed.

Definition possible_type (T : Ty) : Prop :=
  match T with
  | Ty_Forall _ _ _ => True
  | Ty_Fun _ _ => True
  | Ty_Builtin _  => True
  | Ty_IFix _ _ => True
  | _ => False
  end.

Definition impossible_type (T : Ty) : Prop := ~ possible_type T.

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

Lemma R_evaluable : forall k T t1 j1 v1 t2,
    terminates_excl t1 j1 v1 k ->
    possible_type T ->
    R k T t1 t2 ->
    exists v2 j2, j1 < k /\ t1 =[j1]=> v1 /\ t2 =[j2]=> v2.
Proof. intros. destruct H. autorewrite with R in H1.
  destruct T; inversion H0; destruct H1 as [_ [_ [v2 [j2 [Hev2 _]]]]]; eauto; 
    try solve [eexists; eexists; eexists; eexists; eauto].
Qed.

Lemma R_evaluable_1 : forall k T t1 j1 v1 t2,
    terminates_excl t1 j1 v1 k ->
    possible_type T ->
    R k T t1 t2 ->
    j1 < k /\ t1 =[j1]=> v1.
Proof. intros. destruct H. eauto. Qed.

Lemma R_evaluable_2 : forall k T t1 j1 v1 t2,
    terminates_excl t1 j1 v1 k ->
    possible_type T ->
    R k T t1 t2 ->
    exists v2 j2, t2 =[j2]=> v2.
Proof. intros. destruct (R_evaluable _ _ _ _ _ _ H H0 H1) as [v2 [j2 [_ [_ Hev2]]]]; eauto. Qed.

Lemma R_syntactic_equality : forall k st t1 j1 v1 t2,
    terminates_excl t1 j1 v1 k ->
    R k (Ty_Builtin st) t1 t2 ->
    exists v2 j2,
      t2 =[j2]=> v2 /\
      v1 = v2.
Proof. intros. destruct H. destruct H0 as [_ [_ [v2 [j2 [Hev2 Heq]]]]]; eauto. Qed.

Lemma R_functional_extensionality : forall k T1 T2 t1 j1 v1 t2,
    terminates_excl t1 j1 v1 k ->
    R k (Ty_Fun T1 T2) t1 t2 ->
    exists v2 j2,
      t2 =[j2]=> v2 /\
      (forall s1 s2 k' x1_0 x2_0 T1_0 T2_0 t1_0 t2_0 t1_0' t2_0',
        k' < k - j1 ->
        v1 = LamAbs x1_0 T1_0 t1_0 ->
        v2 = LamAbs x2_0 T2_0 t2_0 ->
        R k' T1 s1 s2 ->
        substitute x1_0 s1 t1_0 t1_0' ->
        substitute x2_0 s2 t2_0 t2_0' ->
        R k' T2 t1_0' t2_0').
Proof. 
  intros k T1 T2 t1 j1 v1 t2 Hterm R. 
  destruct Hterm.
  autorewrite with R in R.
  destruct R as [_ [_ [v2 [j2 [Hev_t2 Hfe]]]]]; eauto.
Qed.

Lemma R_unwrap : forall k F T t1 j1 v1 t2,
    terminates_excl t1 j1 v1 k ->
    R k (Ty_IFix F T) t1 t2 ->
    exists v2 j2,
      t2 =[j2]=> v2 /\
      (forall K k',
        k' < k - j1 ->
        emptyContext |-* T : K ->
        R k' (beta_reduce (unwrapIFix F K T)) v1 v2).
Proof.
  intros k F T t1 j1 v1 t2 Hterm R.
  destruct Hterm. 
  autorewrite with R in R.
  destruct R as [_ [_ [v2 [j2 [Hev_t2 Hunwrap]]]]]; eauto.
Qed.

Lemma R_instantiational_extensionality : forall k X K T t1 j1 v1 t2,
    terminates_excl t1 j1 v1 k ->
    R k (Ty_Forall X K T) t1 t2 ->
    exists v2 j2,
      t2 =[j2]=> v2 /\
      (forall t0_1 t0_2 T' k',
        k' < k - j1 ->
        v1 = TyAbs X K t0_1 ->
        v2 = TyAbs X K t0_2 ->
        emptyContext |-* T' : K ->
        R k' (beta_reduce (substituteT X T' T)) v1 v2).
Proof.
  intros k X K T t1 j1 v1 t2 Hterm R. 
  destruct Hterm.
  autorewrite with R in R.
  destruct R as [_ [_ [v2 [j2 [Hev_t2 Hie]]]]]; eauto.
Qed.


Lemma R_impossible_type : forall k t1 t2,
    (forall a, ~(R k (Ty_Var a) t1 t2)) /\
    (forall bX K T, ~(R k (Ty_Lam bX K T) t1 t2)) /\
    (forall T1 T2, ~(R k (Ty_App T1 T2) t1 t2)).
Proof. intros. split; try split; try solve [intros; intro Hcon; destruct k; destruct Hcon as [_ [_ Hfls]]; eauto]. Qed.

Lemma R_nontermination : forall k T t1 t2,
    ~(exists j1 v1, terminates_excl t1 j1 v1 k) ->
    possible_type T ->
    emptyContext |-+ t1 : T ->
    emptyContext |-+ t2 : T ->
    R k T t1 t2.
Proof. intros. unfold terminates_excl in H. destruct T; try solve [split; auto; split; auto; intros; exfalso; apply H; eauto]. Qed.