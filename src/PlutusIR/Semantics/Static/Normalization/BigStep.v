Require Import PlutusCert.PlutusIR.
Require Import Strings.String.

Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.

From PlutusCert Require Import Util.

(** Type equality *)
Reserved Notation "T1 '=b' T2" (at level 40).
Inductive EqT : ty -> ty -> Prop :=
  (* Beta-reduction *)
  | Q_Beta : forall X K T1 T2 T1',
      substituteTCA X T2 T1 = T1' ->
      Ty_App (Ty_Lam X K T1) T2 =b T1'
  (* Reflexivity, Symmetry and Transitivity*)
  | Q_Refl : forall T,
      T =b T
  | Q_Symm : forall T S,
      T =b S ->
      S =b T
  | Q_Trans : forall S U T,
      S =b U ->
      U =b T ->
      S =b T
  (* Congruence *)
  | Q_Fun : forall S1 S2 T1 T2,
      S1 =b S2 ->
      T1 =b T2 ->
      Ty_Fun S1 T1 =b Ty_Fun S2 T2
  | Q_Forall : forall X K S T,
      S =b T ->
      Ty_Forall X K S =b Ty_Forall X K T
  | Q_Lam : forall X K S T,
      S =b T ->
      Ty_Lam X K S =b Ty_Lam X K T
  | Q_App : forall S1 S2 T1 T2,
      S1 =b S2 ->
      T1 =b T2 ->
      Ty_App S1 T1 =b Ty_App S2 T2
  | Q_IFix : forall F1 F2 T1 T2,
      F1 =b F2 ->
      T1 =b T2 ->
      Ty_IFix F1 T1 =b Ty_IFix F2 T2
where "T1 '=b' T2" := (EqT T1 T2).

#[export] Hint Constructors EqT : core.

(** Normal types *)
Inductive normal_Ty : ty -> Prop :=
  | NO_TyLam : forall bX K T,
      normal_Ty T ->
      normal_Ty (Ty_Lam bX K T)
  | NO_neutral : forall T,
      neutral_Ty T ->
      normal_Ty T
  | NO_TyFun : forall T1 T2,
      normal_Ty T1 ->
      normal_Ty T2 ->
      normal_Ty (Ty_Fun T1 T2)
  | NO_TyForall : forall bX K T,
      normal_Ty T ->
      normal_Ty (Ty_Forall bX K T)
  | NO_TyIFix : forall F T,
      normal_Ty F ->
      normal_Ty T ->
      normal_Ty (Ty_IFix F T)
  | NO_TyBuiltin : forall st,
      normal_Ty (Ty_Builtin st)
  | NO_TySOP : forall (Tss : (list (list ty))),
      ForallSet2 (fun T => normal_Ty T) Tss ->
      normal_Ty (Ty_SOP Tss)

with neutral_Ty : ty -> Prop :=
  | NE_TyVar : forall X,
      neutral_Ty (Ty_Var X)
  | NE_TyApp : forall T1 T2,
      neutral_Ty T1 ->
      normal_Ty T2 ->
      neutral_Ty (Ty_App T1 T2).

Scheme normal_Ty__ind := Minimality for normal_Ty Sort Prop
  with neutral_Ty__ind := Minimality for neutral_Ty Sort Prop.

Combined Scheme normal_Ty__multind from
  normal_Ty__ind,
  neutral_Ty__ind.

#[export] Hint Constructors normal_Ty neutral_Ty : core.

(** Type normalisation *)
Inductive normalise : ty -> ty -> Prop :=
  | N_BetaReduce : forall bX K T1 T2 T1n T2n T,
      normalise T1 (Ty_Lam bX K T1n) ->     (* TyApp (Lam bX Kind_Base (Ty_Var bX)) (Lam bY Kind_Base (Ty_Var bY)) -> Lam bY Kind_Base (Ty_Var bY) *)
      normalise T2 T2n ->
      normalise (substituteTCA bX T2n T1n) T ->
      normalise (Ty_App T1 T2) T
  | N_TyApp : forall T1 T2 T1n T2n,
      normalise T1 T1n ->
      neutral_Ty T1n ->
      normalise T2 T2n ->
      normalise (Ty_App T1 T2) (Ty_App T1n T2n)
  | N_TyFun : forall T1 T2 T1n T2n,
      normalise T1 T1n ->
      normalise T2 T2n ->
      normalise (Ty_Fun T1 T2) (Ty_Fun T1n T2n)
  | N_TyForall : forall bX K T0 T0n,
      normalise T0 T0n ->
      normalise (Ty_Forall bX K T0) (Ty_Forall bX K T0n)
  | N_TyLam : forall bX K T0 T0n,
      normalise T0 T0n ->
      normalise (Ty_Lam bX K T0) (Ty_Lam bX K T0n)
  | N_TyVar : forall X,
      normalise (Ty_Var X) (Ty_Var X)
  | N_TyIFix : forall F T Fn Tn,
      normalise F Fn ->
      normalise T Tn ->
      normalise (Ty_IFix F T) (Ty_IFix Fn Tn)
  | N_TyBuiltin : forall (st : DefaultUni),
      normalise (Ty_Builtin st) (Ty_Builtin st)
  | N_TySOP : forall (Tss Tss' : (list (list ty))),
      ForallSetPair2 normalise Tss Tss' ->
      normalise (Ty_SOP Tss) (Ty_SOP Tss')
  .

#[export] Hint Constructors normalise : core.



(** Properties of type normalisation *)
Lemma normalise_to_normal : forall T Tn,
    normalise T Tn ->
    normal_Ty Tn.
Proof.
  induction 1; eauto.
  apply NO_TySOP.
  (* ADMIT: TY_SOP *)
Admitted.

Lemma normalisation__deterministic : forall T Tn T'n,
    normalise T Tn ->
    normalise T T'n ->
    Tn = T'n.
Proof.
  intros.
  generalize dependent T'n.
  induction H; intros.
  - inversion H2.
    + subst.
      apply IHnormalise1 in H5. inversion H5. subst.
      apply IHnormalise2 in H6. subst.
      apply IHnormalise3; eauto.
    + subst.
      apply IHnormalise1 in H5.
      inversion H5. subst.
      inversion H6.
  - inversion H2.
    + subst.
      apply IHnormalise1 in H5.
      inversion H5. subst.
      inversion H0.
    + subst.
      f_equal; eauto.
  - inversion H1. subst.
    f_equal; eauto.
  - inversion H0. subst.
    f_equal; eauto.
  - inversion H0. subst.
    f_equal; eauto.
  - inversion H0. subst.
    f_equal; eauto.
  - inversion H1. subst.
    f_equal; eauto.
  - inversion H0. subst.
    eauto.
  - (* ADMIT: TY_SOP*)
Admitted.

Ltac invert_normalise :=
  match goal with
  | H : normalise ?T ?Tn |- _ => inversion H; subst; f_equal; eauto
  end.

Theorem normalisation__stable :
  (forall T, normal_Ty T -> (forall Tn, normalise T Tn -> T = Tn)) /\
  (forall T, neutral_Ty T -> (forall Tn, normalise T Tn -> T = Tn)).
Proof with eauto.
  eapply normal_Ty__multind; intros...
  all: try solve [invert_normalise].
  - (* ADMIT: TY_ SOP*) admit.
  - inversion H3.
    + subst.
      eapply H0 in H6.
      subst.
      inversion H.
    + subst.
      f_equal...
Admitted.

Corollary normalisation__stable__normal : forall T,
    normal_Ty T ->
    forall Tn,
      normalise T Tn -> T = Tn.
Proof. apply normalisation__stable. Qed.

Corollary normalisation__stable__neutral : forall T,
    neutral_Ty T ->
    forall Tn,
      normalise T Tn -> T = Tn.
Proof. apply normalisation__stable. Qed.

Lemma normalisation__stable' :
  (forall Tn, normal_Ty Tn -> normalise Tn Tn) /\
  (forall Tn, neutral_Ty Tn -> normalise Tn Tn).
Proof. apply normal_Ty__multind; eauto.
(* ADMIT: Ty_SOP *)
Admitted.

Corollary normalisation__stable'__normal : forall Tn,
    normal_Ty Tn ->
    normalise Tn Tn.
Proof. apply normalisation__stable'. Qed.

Corollary normalisation__stable'__neutral : forall Tn,
    neutral_Ty Tn ->
    normalise Tn Tn.
Proof. apply normalisation__stable'. Qed.

Theorem normalisation__sound : forall T Tn,
    normalise T Tn ->
    T =b Tn.
Proof with eauto. induction 1...
(* ADMIT: Ty_SOP *)
Admitted.

Lemma normalisation__complete : forall S T Sn,
    S =b T ->
    normalise S Sn ->
    normalise T Sn.
Proof. Abort.

(** Normalization of lists of types*)
(* Added well-kinded proofs as this is necessary for completeness of normalisation *)
Inductive map_normalise : list (string * ty) -> list (string * ty) -> Prop :=
  | MN_nil :
      map_normalise nil nil
  | MN_cons : forall X T Ts Tn Tsn,
      map_normalise Ts Tsn ->
      normalise T Tn ->
      map_normalise ((X, T) :: Ts) ((X, Tn) :: Tsn).


#[export] Hint Constructors map_normalise : core.

Require Import Coq.Lists.List.
Import ListNotations.

Lemma MN_snoc : forall X T Ts Tn Tsn,
  map_normalise Ts Tsn ->
  normalise T Tn ->
  map_normalise (Ts ++ [(X, T)]) (Tsn ++ [(X, Tn)])
.
Proof.
  induction Ts.
  - simpl.
    induction Tsn.
    + eauto using map_normalise.
    + intros H_problem.
      inversion H_problem.
  - intros.
    inversion H. subst.
    simpl.
    econstructor; eauto.
Qed.

Lemma MN_app Ts Tsn Ts' Tsn' :
  map_normalise Ts Tsn ->
  map_normalise Ts' Tsn' ->
  map_normalise (Ts ++ Ts') (Tsn ++ Tsn').
Proof.
  intros H1 H2.
  induction H1.
  - assumption.
  - simpl.
    constructor; auto.
Qed.


Lemma map_normalise__app : forall l1 l2 ln,
    map_normalise (l1 ++ l2) ln ->
    exists l1n l2n,
      map_normalise l1 l1n /\
      map_normalise l2 l2n /\
      ln = l1n ++ l2n.
Proof.
  induction l1; intros.
  - exists nil. exists ln. eauto.
  - inversion H. subst.
    eapply IHl1 in H2.
    destruct H2 as [l1n' [l2n' [Hmn1 [Hmn2 Heq]]]].
    subst.
    exists ((X, Tn) :: l1n').
    exists l2n'.
    eauto.
Qed.

Lemma map_normalise__deterministic : forall l ln ln',
    map_normalise l ln ->
    map_normalise l ln' ->
    ln = ln'.
Proof with eauto.
  induction l. all: intros.
  all: inversion H.
  all: inversion H0.
  all: subst.
  - reflexivity.
  - inversion H6. subst.
    f_equal.
    + f_equal.
      eauto using normalisation__deterministic.
    + eauto.
Qed.

Axiom norm : ty -> ty.
Axiom norm_normalise : forall ty, normalise ty (norm ty).

Axiom map_norm : list (string * ty) -> list (string * ty).
Axiom map_norm_map_normalise : forall Ts, map_normalise Ts (map_norm Ts).