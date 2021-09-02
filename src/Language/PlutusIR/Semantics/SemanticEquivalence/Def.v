Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

Notation beta_reduce := (beta_reduce tyname binderTyname substituteT).

(* Note: The cases for Ty_Forall and and Ty_IFix make use of
   type substitution and beta reduction. However, Coq can then not
   guess the decreasing argument of fix anymore. *)
Fixpoint R (T : Ty) (ctx_K : partial_map Kind) (t1 t2 : Term) : Prop :=
  (empty, ctx_K) |-+ t1 : T /\
  (empty, ctx_K) |-+ t2 : T /\
  exists v1 v2,
    t1 ==> v1 /\
    t2 ==> v2 /\
    match T with
    | Ty_Forall X K T0 => 
        forall t0_1 t0_2,
          v1 = TyAbs X K t0_1 ->
          v2 = TyAbs X K t0_2 ->
          R T0 (X |-> K ; ctx_K) t0_1 t0_2
    | Ty_Fun T1 T2 => 
        forall s1 s2,
          R T1 ctx_K s1 s2 ->
          R T2 ctx_K (Apply v1 s1) (Apply v2 s2)
    | Ty_Builtin st => 
        v1 = v2
    | Ty_IFix F T0 => 
        (*
        forall X K,
          empty |-* T : K ->
          R (beta_reduce (unwrapIFix F X K T0)) (Unwrap v1) (Unwrap v2)
        *)
        True
    |_ => False
    end.

Lemma R_typable_emptyT : forall T ctxK t1 t2,
    R T ctxK t1 t2 ->
    (empty, ctxK) |-+ t1 : T /\ (empty, ctxK) |-+ t2 : T.
Proof. intros. destruct T; destruct H as [Ht1 [Ht2 _]]; auto. Qed.

Lemma R_typable_emptyT_1 : forall T ctxK t1 t2,
    R T ctxK t1 t2 ->
    (empty, ctxK) |-+ t1 : T.
Proof. intros. destruct (R_typable_emptyT _ _ _ _ H). assumption. Qed.

Lemma R_typable_emptyT_2 : forall T ctxK t1 t2,
    R T ctxK t1 t2 ->
    (empty, ctxK) |-+ t2 : T.
Proof. intros. destruct (R_typable_emptyT _ _ _ _ H). assumption. Qed.

Lemma R_evaluable : forall T ctxK t1 t2,
    R T ctxK t1 t2 ->
    exists v1 v2, t1 ==> v1 /\ t2 ==> v2.
Proof. intros. destruct T; destruct H as [_ [_ [v1 [v2 [Hev1 [Hev2 _]]]]]]; eauto. Qed.

Lemma R_evaluable_1 : forall T ctxK t1 t2,
    R T ctxK t1 t2 ->
    exists v1, t1 ==> v1.
Proof. intros. destruct (R_evaluable _ _ _ _ H) as [v1 [_ [Hev1 _]]]. eauto. Qed.

Lemma R_evaluable_2 : forall T ctxK t1 t2,
    R ctxK T t1 t2 ->
    exists v2, t2 ==> v2.
Proof. intros. destruct (R_evaluable _ _ _ _ H) as [_ [v2 [_ Hev2]]]. eauto. Qed.

Lemma R_syntactic_equality : forall st ctxK t1 t2,
    R (Ty_Builtin st) ctxK t1 t2 ->
    exists v1 v2,
      t1 ==> v1 /\
      t2 ==> v2 /\
      v1 = v2.
Proof. intros. destruct H as [_ [_ [v1 [v2 [Hev1 [Hev2 Heq]]]]]]. eauto. Qed.

Lemma R_functional_extensionality : forall T1 T2 ctxK t1 t2,
  R (Ty_Fun T1 T2) ctxK t1 t2 ->
  exists v1 v2,
    t1 ==> v1 /\
    t2 ==> v2 /\
    (forall s1 s2,
      R T1 ctxK s1 s2 ->
      R T2 ctxK (Apply v1 s1) (Apply v2 s2)).
Proof. intros. destruct H as [_ [_ [v1 [v2 [Hev1 [Hev2 Hfe]]]]]]. eauto. Qed.

Lemma R_falsity : forall ctxK t1 t2,
  (forall a, ~(R (Ty_Var a) ctxK t1 t2)) /\
  (forall bX K T, ~(R (Ty_Lam bX K T) ctxK t1 t2)) /\
  (forall T1 T2, ~(R (Ty_App T1 T2) ctxK t1 t2)).
Proof. 
  split.
  - intros. intro Hcon. destruct Hcon as [_ [_ [_ [_ [_ [_ Hfalse]]]]]]. destruct Hfalse.
  - split.
    + intros. intro Hcon. edestruct Hcon as [_ [_ [_ [_ [_ [_ Hfalse]]]]]]. destruct Hfalse.
    + intros. intro Hcon. edestruct Hcon as [_ [_ [_ [_ [_ [_ Hfalse]]]]]]. destruct Hfalse.
Qed.

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
