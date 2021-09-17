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

(* Relational interpretations of values *)
Section RV.

  Context (RC : forall (k j : nat), Ty -> Term -> Term -> j < k -> Prop).

  Definition RV_TyVar (k : nat) (a : tyname) (v1 v2 : Term) : Prop :=
    False.

  Definition RV_TyLam (k : nat) (bX : binderTyname) (K : Kind) (T : Ty) (v1 v2 : Term) : Prop :=
    False.

  Definition RV_TyApp (k : nat) (T1 T2 : Ty) (v1 v2 : Term) : Prop :=
    False.

  Definition RV_TyBuiltin (k : nat) (st : @some typeIn) (v1 v2 : Term) : Prop :=
    forall sv sv',
      (* Determine the shape of v1 and v2 *)
      v1 = Constant sv ->
      v2 = Constant sv' ->
      (* Syntactic equality *)
      v1 = v2.

  Definition RV_TyFun (k : nat) (T1 T2 : Ty) (v1 v2 : Term) : Prop :=
    forall x T e x' T' e',
      (* Determine the shape of v1 and v2 *)
      v1 = LamAbs x T e ->
      v2 = LamAbs x' T' e' ->
      (* Extensional equivalence *)
      forall j (Hlt_j : j < k) v v' e_subst e'_subst,
        RC k j T1 v v' Hlt_j ->
        substitute x v e e_subst ->
        substitute x' v' e' e'_subst ->
        RC k j T2 e_subst e'_subst Hlt_j.


  Definition RV_TyIFix (k : nat) (F T : Ty) (v1 v2 : Term) : Prop :=
    forall v v',
      (* Determine the shape of v1 and v2 *)
      v1 = IWrap F T v ->
      v2 = IWrap F T v' ->
      (* Uwrap *)
      forall j (Hlt_j : j < k) K,
        emptyContext |-* T : K ->
        RC k j (beta_reduce (unwrapIFix F K T)) v v' Hlt_j.

  Definition RV_TyForall (k : nat) (bX : binderTyname) (K : Kind) (T : Ty) (v1 v2 : Term) : Prop :=
    forall e e',
      (* Determine the shape of v1 and v2 *)
      v1 = TyAbs bX K e ->
      v2 = TyAbs bX K e' ->
      (* Instantiational equivalence *)
      forall j (Hlt_j : j < k) T2,
        RC k j (beta_reduce (substituteT bX T2 T)) e e' Hlt_j.

  Definition RV (k : nat) (T : Ty) (v1 v2 : Term) : Prop :=
    match T with
    | Ty_Var a => RV_TyVar k a v1 v2
    | Ty_Lam bX K T => RV_TyLam k bX K T v1 v2
    | Ty_App T1 T2 => RV_TyApp k T1 T2 v1 v2
    | Ty_Builtin st => RV_TyBuiltin k st v1 v2
    | Ty_Fun T1 T2 => RV_TyFun k T1 T2 v1 v2
    | Ty_IFix F T => RV_TyIFix k F T v1 v2
    | Ty_Forall bX K T => RV_TyForall k bX K T v1 v2
    end.
End RV.


(** RV = Relational interpretation for values, RC = Relation interpretation for computations *)
Equations? RC (k : nat) (T : Ty) (e e' : Term) : Prop by wf k :=
  RC k T e e' =>
    (* RC *)
    emptyContext |-+ e : T /\
    emptyContext |-+ e' : T /\
    forall j (Hlt_j : j < k) e_f,
      e =[j]=> e_f ->
      exists e'_f j', e' =[j']=> e'_f /\
      
      (* RV *)
      match T with

        (* RV for type variable *)
        | Ty_Var a =>  
            False

        (* RV for type lambda *)
        | Ty_Lam bX K T =>
            False

        (* RV for type application *)
        | Ty_App T1 T2 => 
            False

        (* RV for built-in types *)
        | Ty_Builtin st => 
            forall v v' sv sv',
              (* Determine the shape of e_f and e'_f *)
              e_f = v ->
              e'_f = v' ->
              v = Constant sv ->
              v' = Constant sv' ->
              (* Syntactic equality *)
              v = v'

        (* RV for function types *)
        | Ty_Fun T1 T2 =>
            forall x e_body x' e'_body,
              (* Determine the shape of e_f and e'_f *)
              e_f = LamAbs x T1 e_body ->
              e'_f = LamAbs x' T1 e'_body ->
              (* Extensional equivalence *)
              forall i (Hlt_i : i < k - j) v v' e_body' e'_body',
                RC i T1 v v' ->
                value v ->
                value v' ->
                substitute x v e_body e_body' ->
                substitute x' v' e'_body e'_body' ->
                RC i T2 e_body' e'_body'

        (* RV for recursive types *)
        | Ty_IFix F T =>
            forall v v',
              (* Determine the shape of e_f and e_f' *)
              IWrap F T v = e_f ->
              IWrap F T v' = e'_f ->
              (* Uwrap *)
              forall i (Hlt_i : i < k - j) K,
                emptyContext |-* T : K ->
                RC i (beta_reduce (unwrapIFix F K T)) v v'

        (* RV for universal types *)
        | Ty_Forall bX K T => 
            forall e_body e'_body,
              (* Determine the shape of e_f and e_f' *)
              e_f = TyAbs bX K e_body ->
              e'_f = TyAbs bX K e'_body ->
              (* Instantiational equivalence *)
              forall i (Hlt_i : i < k - j) T2,
                RC i (beta_reduce (substituteT bX T2 T)) e_body e'_body
      end.
Proof. all: try (eapply e; eauto). Qed.
      
      
      
      

(*
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
*)

Definition possible_type (T : Ty) : Prop :=
  match T with
  | Ty_Forall _ _ _ => True
  | Ty_Fun _ _ => True
  | Ty_Builtin _  => True
  | Ty_IFix _ _ => True
  | _ => False
  end.

Definition impossible_type (T : Ty) : Prop := ~ possible_type T.

Lemma RC_typable_empty : forall k T e e',
    RC k T e e' ->
    emptyContext |-+ e : T /\ emptyContext |-+ e' : T.
Proof. intros. destruct k, T; destruct H as [He [He' _]]; auto. Qed.

Lemma RC_typable_empty_1 : forall k T e e',
    RC k T e e' ->
    emptyContext |-+ e : T.
Proof. intros. destruct (RC_typable_empty _ _ _ _ H). assumption. Qed.

Lemma RC_typable_empty_2 : forall k T e e',
    RC k T e e' ->
    emptyContext |-+ e' : T.
Proof. intros. destruct (RC_typable_empty _ _ _ _ H). assumption. Qed.

Lemma RC_evaluable : forall k T e j e_f e',
    terminates_excl e j e_f k ->
    RC k T e e' ->
    exists e'_f j', j < k /\ e =[j]=> e_f /\ e' =[j']=> e'_f.
Proof. intros. destruct H. autorewrite with RC in H1.
  destruct T; destruct H0 as [_ [_ [e'_f [j' [Hev_e' _]]]]]; eauto.
  Unshelve. all: eauto.
Qed.

Lemma RC_evaluable_1 : forall k T e j e_f e',
    terminates_excl e j e_f k ->
    RC k T e e' ->
    j < k /\ e =[j]=> e_f.
Proof. intros. destruct H. eauto. Qed.

Lemma RC_evaluable_2 : forall k T e j e_f e',
    terminates_excl e j e_f k ->
    RC k T e e' ->
    exists e'_f j', e' =[j']=> e'_f.
Proof. intros. destruct (RC_evaluable _ _ _ _ _ _ H H0) as [e'_f [j' [_ [_ Hev_e']]]]; eauto. Qed.

Lemma RC_syntactic_equality : forall k st e j e_f e',
    terminates_excl e j e_f k ->
    RC k (Ty_Builtin st) e e' ->

    (exists e'_f j',
      e' =[j']=> e'_f /\

      forall v v' sv sv',
        (* Determine the shape of e_f and e'_f *)
        e_f = v ->
        e'_f = v' ->
        v = Constant sv ->
        v' = Constant sv' ->
        (* Syntactic equality *)
        v = v').
Proof. intros. destruct H. destruct H0 as [_ [_ [e'_f [j' [Hev_e' Heq]]]]]; eauto. Qed.

Lemma RC_functional_extensionality : forall k T1 T2 e j e_f e',
    terminates_excl e j e_f k ->
    RC k (Ty_Fun T1 T2) e e' ->

    exists e'_f j',
      e' =[j']=> e'_f /\

      (forall x e_body x' e'_body,
        (* Determine the shape of e_f and e'_f *)
        e_f = LamAbs x T1 e_body ->
        e'_f = LamAbs x' T1 e'_body ->
        (* Extensional equivalence *)
        forall i (Hlt_i : i < k - j) v v' e_body' e'_body',
          RC i T1 v v' ->
          value v ->
          value v' ->
          substitute x v e_body e_body' ->
          substitute x' v' e'_body e'_body' ->
          RC i T2 e_body' e'_body').
Proof. 
  intros k T1 T2 t1 j1 v1 t2 Hterm RC. 
  destruct Hterm.
  autorewrite with RC in RC.
  destruct RC as [_ [_ [e'_f [j' [Hev_e' Hfe]]]]]; eauto.
Qed.

Lemma RC_unwrap : forall k F T e j e_f e',
    terminates_excl e j e_f k ->
    RC k (Ty_IFix F T) e e' ->

    exists e'_f j',
      e' =[j']=> e'_f /\

      (forall v v',
        (* Determine the shape of e_f and e_f' *)
        IWrap F T v = e_f ->
        IWrap F T v' = e'_f ->
        (* Uwrap *)
        forall i (Hlt_i : i < k - j) K,
          emptyContext |-* T : K ->
          RC i (beta_reduce (unwrapIFix F K T)) v v').
Proof.
  intros k F T t1 j1 v1 t2 Hterm RC.
  destruct Hterm. 
  autorewrite with RC in RC.
  destruct RC as [_ [_ [e'_f [j' [Hev_e' Hunwrap]]]]]; eauto.
Qed.

Lemma RC_instantiational_extensionality : forall k bX K T e j e_f e',
    terminates_excl e j e_f k ->
    RC k (Ty_Forall bX K T) e e' ->

    exists e'_f j',
      e' =[j']=> e'_f /\

      (forall e_body e'_body,
        (* Determine the shape of e_f and e_f' *)
        e_f = TyAbs bX K e_body ->
        e'_f = TyAbs bX K e'_body ->
        (* Instantiational equivalence *)
        forall i (Hlt_i : i < k - j) T2,
          RC i (beta_reduce (substituteT bX T2 T)) e_body e'_body).
Proof.
  intros k X K T t1 j1 v1 t2 Hterm RC. 
  destruct Hterm.
  autorewrite with RC in RC.
  destruct RC as [_ [_ [e'_f [j' [Hev_e' Hie]]]]]; eauto.
Qed.


Lemma RC_impossible_type : forall k e j e_f e',
    terminates_excl e j e_f k ->

    (forall a, ~(RC k (Ty_Var a) e e')) /\
    (forall bX K T, ~(RC k (Ty_Lam bX K T) e e')) /\
    (forall T1 T2, ~(RC k (Ty_App T1 T2) e e')).
Proof. intros. destruct H. split; try split; try solve [intros; intro Hcon; destruct Hcon as [_ [_ [_ [_ [_ Hfls]]]]]; eauto]. Qed.

Lemma RC_nontermination : forall k T e e',
    ~(exists e_f j, terminates_excl e j e_f k) ->
    emptyContext |-+ e : T ->
    emptyContext |-+ e' : T ->
    RC k T e e'.
Proof. intros. unfold terminates_excl in H. destruct T; try solve [split; auto; split; auto; intros; exfalso; apply H; eauto]. Qed.