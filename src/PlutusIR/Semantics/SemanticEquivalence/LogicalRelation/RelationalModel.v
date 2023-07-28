Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.
Require Import PlutusCert.Util.List.

Import PlutusNotations.

From Coq Require Import Lia.

Require Import Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

Local Open Scope list_scope.
Local Open Scope string_scope.

Definition Rel (T T' : Ty) (Chi : nat -> Term -> Term -> Prop) : Prop :=
  forall j v v',
    Chi j v v' -> 0 < j ->
      value v /\ value v' /\
      (exists Tn, normalise T Tn /\ ([] ,, [] |-+ v : Tn)) /\
      (exists Tn', normalise T' Tn' /\ ([] ,, [] |-+ v' : Tn')) /\
      forall i,
        i <= j ->
        Chi i v v'.

(** Relation interpational of types as computations and values.

    RV = Relational interpretation for values
    RC = Relation interpretation for computations
*)
Equations? RC (k : nat) (T : Ty) (rho : tymapping) (e e' : Term) : Prop by wf k :=
  RC k T rho e e' =>
    (* RC *)
    forall j (Hlt_j : j < k) e_f,
      e =[j]=> e_f ->
      exists e'_f j', e' =[j']=> e'_f /\

      (* RV *)
      (exists Tn, normalise (msubstT (msyn1 rho) T) Tn /\ ([] ,, [] |-+ e_f : Tn)) /\
      (exists Tn', normalise (msubstT (msyn2 rho) T) Tn' /\  ([] ,, [] |-+ e'_f : Tn')) /\

      (
        (
          ~ is_error e_f /\
          ~ is_error e'_f /\
          (
            match T with

            (* RV for type variable *)
            | Ty_Var a =>
                forall Chi,
                  sem rho a = Datatypes.Some Chi ->
                  Chi (k - j) e_f e'_f

            (* RV for type lambda *)
            | Ty_Lam X K T0 =>
                False

            (* RV for type application *)
            | Ty_App T1 T2 =>
                False

            (* RV for built-in types *)
            | Ty_Builtin st =>
                exists sv sv',
                  (* Determine the shape of e_f and e'_f *)
                  e_f = Constant sv /\
                  e'_f = Constant sv' /\
                  (* Syntactic equality *)
                  e_f = e'_f

            (* RV for function types *)
            | Ty_Fun T1n T2n =>
                (* Determine the shape of e_f and e'_f *)
                exists x e_body e'_body T1 T1',
                  LamAbs x T1 e_body = e_f /\
                  LamAbs x T1' e'_body = e'_f /\
                  (* Extensional equivalence *)
                  forall i (Hlt_i : i < k - j) v_0 v'_0,
                    ~ is_error v_0 /\ ~ is_error v'_0 ->
                    value v_0 /\ value v'_0 /\
                    RC i T1n rho v_0 v'_0 ->
                    RC i T2n rho <{ [v_0 / x] e_body }> <{ [v'_0 / x] e'_body }>

            (* RV for recursive types *)
            | Ty_IFix Fn Tn =>
                exists v_0 v'_0 F F' T T',
                  (* Determine the shape of e_f and e'_f *)
                  e_f = IWrap F T v_0 /\
                  e'_f = IWrap F' T' v'_0 /\
                  (* Unwrap *)
                  forall i (Hlt_i : i < k - j) K T0n,
                    [] |-* (msubstT (msyn1 rho) Tn) : K ->
                    [] |-* (msubstT (msyn2 rho) Tn) : K ->
                    normalise (unwrapIFix Fn K Tn) T0n ->
                    RC i T0n rho v_0 v'_0

            (* RV for universal types *)
            | Ty_Forall X K Tn =>
                exists e_body e'_body,
                  (* Determine the shape of e_f and e_f' *)
                  e_f = TyAbs X K e_body /\
                  e'_f = TyAbs X K e'_body /\
                  (* Instantiational equivalence *)
                  forall T1 T2 Chi,
                    [] |-* T1 : K ->
                    [] |-* T2 : K ->
                    Rel T1 T2 Chi ->
                    forall i (Hlt_i : i < k - j),
                      RC i Tn ((X, (Chi, T1, T2)) :: rho) <{ [[T1 / X ] e_body }> <{ [[T2 / X ] e'_body }>
            end
          )
        ) \/ (
          is_error e_f /\
          is_error e'_f
        )
      ).
Proof. all: lia. Qed.

Definition RV (k : nat) (T : Ty) (rho : tymapping) (v v' : Term) : Prop :=
  value v /\ value v' /\ RC k T rho v v'.

(** Converting from RC to RV and vice versa *)

Lemma make_RC k T rho e e' :
  (forall j (Hlt_j : j < k) e_f,
    e =[j]=> e_f ->
    exists e'_f j', e' =[j']=> e'_f /\ RV (k - j) T rho e_f e'_f
  ) ->
  RC k T rho e e'.
Proof with auto.
  intros H.
  autorewrite with RC.
  intros.

  assert (
    exists (e'_f : Term) (j' : nat),
      e' =[ j' ]=> e'_f /\ RV (k - j) T rho e_f e'_f
      )...
  destruct H1 as [e'_f [j' [H_e'_runs H_RV_e_f_e'_f]]].
  exists e'_f, j'.
  split.
    - assumption.
    - unfold RV in H_RV_e_f_e'_f.
      destruct H_RV_e_f_e'_f as [H_val_e_f [H_val_e'_f H_RC]].
      autorewrite with RC in H_RC.
      assert (H_lt : 0 < k - j).
        { lia. }
      assert (H_eval := eval_value__value _ H_val_e_f).
      assert (H__ := H_RC 0 H_lt e_f H_eval); clear H_RC.
      destruct H__ as [e'f0 [j'' [H_eval_e'_f HH]]].

      (* Since j is e'_f is a value, we should know that e'f0 = e'_f*)
      assert (H_eval_e'_f_val := eval_value__value _ H_val_e'_f).
      assert (H_eqs := eval__deterministic _ _ _ H_eval_e'_f _ _ H_eval_e'_f_val).
      destruct H_eqs; subst.

      assert (H_kj0 : forall k j, k - j - 0 = k - j). lia.
      rewrite H_kj0 in HH.
      assumption.
Qed.

Lemma RC_to_RV : forall k T rho e e',
    RC k T rho e e' ->
    forall j (Hlt_j : j < k) e_f,
      e =[j]=> e_f ->
      exists e'_f j', e' =[j']=> e'_f /\
        RV (k - j) T rho e_f e'_f.
Proof.
  intros k T rho e e' HRC j Hlt__j e_f Hev__e_f.
  autorewrite with RC in HRC.
  apply HRC in Hev__e_f as temp; eauto.
  clear HRC.
  destruct temp as [e'_f [j' [Hev__e'_f [Htyp__e_f [Htyp__e'_f H]]]]].
  eexists. eexists.
  split. eauto.
  split. eauto using eval_value__value, eval_to_value__eval.
  split. eauto using eval_value__value, eval_to_value__eval.
  autorewrite with RC.
  intros.
  assert (e_f =[0]=> e_f). {
    eapply eval_value__value.
    eapply eval_to_value__eval.
    eauto.
  }
  assert (e_f0 = e_f /\ j0 = 0) by (eapply eval__deterministic; eauto).
  destruct H2. subst.
  eexists. eexists.
  split. eapply eval_value__value. eapply eval_to_value__eval. eauto.
  rewrite <- minus_n_O.
  eauto.
Qed.

Lemma RV_RC k T rho e e' :
  RC k T rho e e' <->
  (forall j (Hlt_j : j < k) e_f,
    e =[j]=> e_f ->
    exists e'_f j', e' =[j']=> e'_f /\ RV (k - j) T rho e_f e'_f
  ).
Proof.
constructor;
eauto using make_RC, RC_to_RV.
Qed.

Corollary RV_unfolded_to_RV : forall k T rho v v',
    value v /\ value v' /\ RC k T rho v v' ->
    RV k T rho v v'.
Proof. intros. auto. Qed.

Lemma RV_to_RC : forall k T rho v v',
  RV k T rho v v' ->
  RC k T rho v v'.
Proof. intros. apply H. Qed.

(** Kind assignments *)
Definition kass := list (name * Kind).

(** RD = Interpretation of kind contexts as type mappings *)
Inductive RD : kass -> tymapping -> Prop :=
  | RD_nil :
      RD nil nil
  | RD_cons : forall ck rho T1 T2 Chi X K,
      [] |-* T1 : K ->
      [] |-* T2 : K ->
      Rel T1 T2 Chi ->
      RD ck rho ->
      RD ((X, K) :: ck) ((X, (Chi, T1, T2)) :: rho).

(** Term environment *)
Definition env := list (name * Term).
(** Type assignments *)
Definition tass := list (name * Ty).

(** RG = Interpretation of type contexts as logically related term environments *)
Inductive RG (rho : tymapping) (k : nat) : tass -> env -> env -> Prop :=
  | RG_nil :
      RG rho k nil nil nil
  | RG_cons : forall x T v1 v2 c e1 e2,
      RV k T rho v1 v2 ->
      normal_Ty T ->
      ~ (is_error v1) ->
      RG rho k c e1 e2 ->
      RG rho k ((x, T) :: c) ((x, v1) :: e1) ((x, v2) :: e2).

Fixpoint closed_env (env : env) :=
  match env with
  | nil => True
  | (x,t) :: env' => closed t /\ closed_env env'
  end.

(** Logical relation: logical approximation

    If $\Gamma \vdash e : \tau$ and $\Gamma \vdash e' : \tau$, then we write
    $\Gamma \vdash e \leq e' : \tau$ to mean that
    for all $k \geq 0$, if $env$ and $env'$ are mappings from variables $x$ to closed
    values that are lated for $k$ steps at $\Gamma$, then $\gamma(e)$ and
    $\gamma(e')$ are related for $k$ steps as computations of type $\tau$.
*)
Definition LR_logically_approximate (Delta : list (string * Kind)) (Gamma : list (string * Ty)) (e e' : Term) (T : Ty) :=
    (Delta ,, Gamma |-+ e : T) /\
    (Delta ,, Gamma |-+ e' : T) /\
    forall k rho env env',
      RD Delta rho ->
      RG rho k Gamma env env' ->
      RC k T rho (msubst env (msubstA (msyn1 rho) e)) (msubst env' (msubstA (msyn2 rho) e')).

(** Logical relation: logical equivalence

    We say $e$ and $e'$ are logically equivalent, written
    $\Gamma \vdash e \tilde e' : \tau$, if they logically approximate one
    another.
*)

Definition LR_logically_equivalent (Delta : list (string * Kind)) (Gamma : list (string * Ty)) (e e' : Term) (T : Ty) :=
  LR_logically_approximate Delta Gamma e e' T /\ LR_logically_approximate Delta Gamma e' e T.



(*
Logical approximation of one-hole contexts
*)
Definition LR_logically_approximate_context Δ₁ Γ₁ C C' Δ Γ T T₁ :=
  forall e e',
    LR_logically_approximate Δ Γ e e' T ->
    LR_logically_approximate Δ₁ Γ₁ (context_apply C e) (context_apply C' e') T₁.
