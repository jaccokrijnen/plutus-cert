Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

From Coq Require Import Arith.

Local Open Scope list_scope.



(** Empty typability *)

Lemma RV_typable_empty : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    (exists Tn, normalise (msubstT (msyn1 rho) T) Tn /\ (empty ,, empty |-+ v : Tn)) /\
    (exists Tn', normalise (msubstT (msyn2 rho) T) Tn' /\  (empty ,, empty |-+ v' : Tn')).
Proof. 
  intros. 
  unfold RV in H. 
  destruct H as [Hval__v [Hval__v' HRC]].
  autorewrite with RC in HRC.
  apply eval_value in Hval__v as Hev__v.
  apply HRC in Hev__v; auto.
  clear HRC.
  destruct Hev__v as [e'_f [j' [Hev__e'_f [Htyp__v [Htyp__v' _]]]]].
  apply eval_value in Hval__v'.
  assert (e'_f = v' /\ j' = 0) by (eapply eval__deterministic; eauto).
  destruct H. subst.
  auto.
Qed.

Lemma RV_typable_empty_1 : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    (exists Tn, normalise (msubstT (msyn1 rho) T) Tn /\ (empty ,, empty |-+ v : Tn)).
Proof. intros. destruct (RV_typable_empty _ _ _ _ _ H H0) as [Htyp__v Htyp__v']. eauto. Qed.

Lemma RV_typable_empty_2 : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    (exists Tn', normalise (msubstT (msyn2 rho) T) Tn' /\ (empty ,, empty |-+ v' : Tn')).
Proof. intros. destruct (RV_typable_empty _ _ _ _ _ H H0) as [Htyp__v Htyp__v']. eauto. Qed.

(** Equivalnce of step-index implies equivalence of RV *)

Lemma RV_equiv : forall k k' T rho e e',
    RV k T rho e e' ->
    k = k' ->
    RV k' T rho e e'.
Proof. intros. subst. eauto. Qed.

(** Easy access to the RV conditions *)

Lemma RV_condition : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->

    ( 
      ~ is_error v /\
      ~ is_error v' /\
      (
        match T with

        (* RV for type variable *)
        | Ty_Var a =>
            forall Chi,
              sem rho a = Datatypes.Some Chi ->  
              Chi k v v'

        (* RV for type lambda *)
        | Ty_Lam bX K T =>
            False

        (* RV for type application *)
        | Ty_App T1 T2 => 
            False

        (* RV for built-in types *)
        | Ty_Builtin st => 
            exists sv sv',
              (* Determine the shape of v and v'*)
              v = Constant sv /\
              v' = Constant sv' /\
              (* Syntactic equality *)
              v = v'

        (* RV for function types *)
        | Ty_Fun T1 T2 =>
            (* Determine the shape of v and v' *)
            exists x e_body x' e'_body T1p,
              normalise T1p T1 /\   
              LamAbs x (msubstT (msyn1 rho) T1p) e_body = v /\
              LamAbs x' (msubstT (msyn2 rho) T1p) e'_body = v' /\
              (* Extensional equivalence *)
              forall i (Hlt_i : i < k) v_0 v'_0,
                value v_0 /\ value v'_0 /\ RC i T1 rho v_0 v'_0 ->
                RC i T2 rho <{ [v_0 / x] e_body }> <{ [v'_0 / x'] e'_body }>

        (* RV for recursive types *)
        | Ty_IFix F T =>
            exists v_0 v'_0 Fp Tp,
              (* Determine the shape of v and v' *)
              normalise Fp F /\ normalise Tp T /\
              v = IWrap (msubstT (msyn1 rho) Fp) (msubstT (msyn1 rho) Tp) v_0 /\
              v' = IWrap (msubstT (msyn2 rho) Fp) (msubstT (msyn2 rho) Tp) v'_0 /\
              (* Unwrap *)
              forall i (Hlt_i : i < k) K T0n,
                empty |-* (msubstT (msyn1 rho) T) : K ->
                empty |-* (msubstT (msyn2 rho) T) : K ->
                normalise (unwrapIFix F K T) T0n ->
                RC i T0n rho v_0 v'_0

        (* RV for universal types *)
        | Ty_Forall bX K T => 
            exists e_body e'_body,
              (* Determine the shape of v and v' *)
              v = TyAbs bX K e_body /\
              v' = TyAbs bX K e'_body /\
              (* Instantiational equivalence *)
              forall T1 T2 Chi,
                empty |-* T1 : K ->
                empty |-* T2 : K ->
                Rel T1 T2 Chi ->
                forall i (Hlt_i : i < k),
                  RC i T ((bX, (Chi, T1, T2)) :: rho) <{ [[T1 / bX ] e_body }> <{ [[T2 / bX ] e'_body }>
        end
      ) \/ (
        is_error v /\
        is_error v'
      )
    ).
Proof.
  intros.
  destruct H as [Hval__v [Hval__v' HRC]].
  apply eval_value__value in Hval__v as Hev__v.
  apply eval_value__value in Hval__v' as Hev__v'.
  autorewrite with RC in HRC.
  apply HRC in Hev__v as temp; eauto.
  clear HRC.
  destruct temp as [v'' [j'' [Hev__v'' [_ [_ condition]]]]].
  assert (v'' = v' /\ j'' = 0) by (eapply eval__deterministic; eauto).
  destruct H. subst.
  rewrite <- minus_n_O in condition.
  eauto. 
Qed.
  
Corollary RV_syntactic_equality : forall k st rho v v',
    RV k (Ty_Builtin st) rho v v' ->
    0 < k ->

    ( 
      ~ is_error v /\
      ~ is_error v' /\
      exists sv sv',
        (* Determine the shape of v and v' *)
        v = Constant sv /\
        v' = Constant sv' /\
        (* Syntactic equality *)
        v = v'
    ) \/ (
      is_error v /\
      is_error v'
    ).
Proof. intros. eapply RV_condition in H. all: eauto. Qed.

Corollary RV_functional_extensionality : forall k T1 T2 rho v v',
    RV k (Ty_Fun T1 T2) rho v v' ->
    0 < k ->

    ( 
      ~ is_error v /\
      ~ is_error v' /\
      (* Determine the shape of v and v' *)
      exists x e_body x' e'_body T1p,
        normalise T1p T1 /\   
        LamAbs x (msubstT (msyn1 rho) T1p) e_body = v /\
        LamAbs x' (msubstT (msyn2 rho) T1p) e'_body = v' /\
        (* Extensional equivalence *)
        forall i (Hlt_i : i < k) v_0 v'_0,
          value v_0 /\ value v'_0 /\ RC i T1 rho v_0 v'_0 ->
          RC i T2 rho <{ [v_0 / x] e_body }> <{ [v'_0 / x'] e'_body }>
    ) \/ (
      is_error v /\
      is_error v'
    ).
Proof. intros. eapply RV_condition in H. all: eauto. Qed.

Corollary RV_unwrap : forall k F T rho v v' ,
    RV k (Ty_IFix F T) rho v v' ->
    0 < k ->

    (
      ~ is_error v /\
      ~ is_error v' /\
      exists v_0 v'_0 Fp Tp,
        (* Determine the shape of v and v' *)
        normalise Fp F /\ normalise Tp T /\
        v = IWrap (msubstT (msyn1 rho) Fp) (msubstT (msyn1 rho) Tp) v_0 /\
        v' = IWrap (msubstT (msyn2 rho) Fp) (msubstT (msyn2 rho) Tp) v'_0 /\
        (* Unwrap *)
        forall i (Hlt_i : i < k) K T0n,
          empty |-* (msubstT (msyn1 rho) T) : K ->
          empty |-* (msubstT (msyn2 rho) T) : K ->
          normalise (unwrapIFix F K T) T0n ->
          RC i T0n rho v_0 v'_0
    ) \/ (
      is_error v /\
      is_error v'
    ).
Proof. intros. eapply RV_condition in H. all: eauto. Qed.

Corollary RV_instantiational_extensionality : forall k bX K T rho v v',
    RV k (Ty_Forall bX K T) rho v v' ->
    0 < k ->

    (
      ~ is_error v /\
      ~ is_error v' /\
      exists e_body e'_body,
        (* Determine the shape of v and v' *)
        v = TyAbs bX K e_body /\
        v' = TyAbs bX K e'_body /\
        (* Instantiational equivalence *)
        forall T1 T2 Chi,
          empty |-* T1 : K ->
          empty |-* T2 : K ->
          Rel T1 T2 Chi ->
          forall i (Hlt_i : i < k),
            RC i T ((bX, (Chi, T1, T2)) :: rho) <{ [[T1 / bX ] e_body }> <{ [[T2 / bX ] e'_body }>
    ) \/ (
      is_error v /\
      is_error v'
    ).
Proof. intros. eapply RV_condition in H. all: eauto. Qed.