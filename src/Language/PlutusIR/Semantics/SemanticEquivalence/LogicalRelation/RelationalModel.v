Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Util.Map.Mupdate.

From Coq Require Import Lia.
Require Import Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

(** ** Type mappings

    We denote a type mapping by rho. A type mapping maps
    type variables to a triplet of a step-indexed relation and two types.
*)
Definition tymapping := list (tyname * ((nat -> Term -> Term -> Prop) * Ty * Ty)).


(** Semantic substitution for the type variable a *)
Fixpoint sem (rho : tymapping) (a : tyname) : option (nat -> Term -> Term -> Prop) :=
  match rho with
  | nil => None
  | (a', (Chi, _ , _)) :: rho' => 
      if a =? a' then Datatypes.Some Chi else sem rho' a
  end.


(** (Left) syntactic substitution for the type variable a *)
Fixpoint syn1 (rho : tymapping) (a : tyname) : option Ty :=
  match rho with
  | nil => None
  | (a', (_, T1, _)) :: rho' => 
      if a =? a' then Datatypes.Some T1 else syn1 rho' a
  end.

(** (Right) syntactic substitution for the type variable a *)
Fixpoint syn2 (rho : tymapping) (a : tyname) : option Ty :=
  match rho with
  | nil => None
  | (a', (_, _, T2)) :: rho' => 
      if a =? a' then Datatypes.Some T2 else syn2 rho' a
  end.

(** (Left) syntactic substitutions in rho *)
Fixpoint msyn1 (rho : tymapping) : list (tyname * Ty) :=
  match rho with
  | nil => nil
  | (a', (_, T1, _)) :: rho' => 
      (a', T1) :: msyn1 rho'
  end.

(** (Right) syntactic substitutions in rho *)
Fixpoint msyn2 (rho : tymapping) : list (tyname * Ty) :=
  match rho with
  | nil => nil
  | (a', (_, _, T2)) :: rho' => 
      (a', T2) :: msyn2 rho'
  end.

Definition Rel 
    (T T' : Ty) 
    (Chi : nat -> Term -> Term -> Prop)
    : Prop :=
  forall j v v',
    Chi j v v' ->
    (* value v /\ value v' /\ *)
    empty ,, empty |-+ v : T /\
    (empty ,, empty |-+ v' : T') /\ 
    forall i,
      i <= j ->
      Chi i v v'.



(** ** Relation interpation for computations and values *)

(** RV = Relational interpretation for values, RC = Relation interpretation for computations *)
Equations? RC (k : nat) (T : Ty) (rho : tymapping) (e e' : Term) : Prop by wf k :=
  RC k T rho e e' =>
    (* RC *)

    forall j (Hlt_j : j < k) e_f,
      e =[j]=> e_f ->
      exists e'_f j', e' =[j']=> e'_f /\
      
      (* RV *)
      (empty ,, empty |-+ e_f : (msubstT (msyn1 rho) T)) /\
      (empty ,, empty |-+ e'_f : (msubstT (msyn2 rho) T)) /\
      match T with

        (* RV for type variable *)
        | Ty_Var a =>
            forall Chi,
            sem rho a = Datatypes.Some Chi ->  
            Chi (k - j) e_f e'_f

        (* RV for type lambda *)
        | Ty_Lam bX K T =>
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
        | Ty_Fun T1 T2 =>
            (
              (* Determine the shape of e_f and e'_f *)
              exists x e_body x' e'_body,   
                LamAbs x (msubstT (msyn1 rho) T1) e_body = e_f /\
                LamAbs x' (msubstT (msyn2 rho) T1) e'_body = e'_f /\
                (* Extensional equivalence *)
                forall i (Hlt_i : i < k - j) v_0 v'_0,
                  value v_0 /\ value v'_0 /\ RC i T1 rho v_0 v'_0 ->
                  RC i T2 rho <{ [v_0 / x] e_body }> <{ [v'_0 / x'] e'_body }>
            ) \/ (
              (* Determine the shape of e_f and e'_f*)
              exists f args f' args',
                ExtBuiltin f args = e_f /\
                ExtBuiltin f' args' = e'_f /\
                (* Extensional equivalence*)
                forall i (Hlt_i : i < k - j) v_0 v'_0,
                  value v_0 /\ value v'_0 /\ RC i T1 rho v_0 v'_0 ->
                  RC i T2 rho (ExtBuiltin f (v_0 :: args)) (ExtBuiltin f' (v'_0 :: args'))
            )

        (* RV for recursive types *)
        | Ty_IFix F T =>
            exists v_0 v'_0,
              (* Determine the shape of e_f and e_f' *)
              e_f = IWrap (msubstT (msyn1 rho) F) (msubstT (msyn1 rho) T) v_0 /\
              e'_f = IWrap (msubstT (msyn2 rho) F) (msubstT (msyn2 rho) T) v'_0 /\
              (* Uwrap *)
              forall i (Hlt_i : i < k - j) K S,
                empty |-* (msubstT (msyn2 rho) T) : K ->
                normalise (unwrapIFix F K T) S ->
                RC i S rho v_0 v'_0

        (* RV for universal types *)
        | Ty_Forall bX K T => 
            (
              exists e_body e'_body,
                (* Determine the shape of e_f and e_f' *)
                e_f = TyAbs bX K e_body /\
                e'_f = TyAbs bX K e'_body /\
                (* Instantiational equivalence *)
                forall T1 T2 Chi,
                  empty |-* T1 : K ->
                  empty |-* T2 : K ->
                  Rel T1 T2 Chi ->
                  forall i (Hlt_i : i < k - j),
                    RC i T ((bX, (Chi, T1, T2)) :: rho) <{ [[T1 / bX ] e_body }> <{ [[T2 / bX ] e'_body }>
            )
      end.
Proof. all: lia. Qed.

Definition RV (k : nat) (T : Ty) (rho : tymapping) (v v' : Term) : Prop :=
  value v /\ value v' /\ RC k T rho v v'.

(** ** Helper lemmas for RC *)

Lemma RV_typable_empty : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    empty ,, empty |-+ v : (msubstT (msyn1 rho) T) /\ (empty ,, empty |-+ v' : (msubstT (msyn2 rho) T)).
Proof. 
  intros. 
  unfold RV in H. 
  destruct H as [Hval__v [Hval__v' HRC]].
  autorewrite with RC in HRC.
  apply eval_value in Hval__v as Hev__v.
  unfold P_value in Hev__v.
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
    empty ,, empty |-+ v : (msubstT (msyn1 rho) T).
Proof. intros. destruct (RV_typable_empty _ _ _ _ _ H H0). eauto. Qed.

Lemma RV_typable_empty_2 : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->
    empty ,, empty |-+ v' : (msubstT (msyn2 rho) T).
Proof. intros. destruct (RV_typable_empty _ _ _ _ _ H H0). eauto. Qed.

Lemma RC_lt : forall k T rho e e',
  (0 < k -> RC k T rho e e') ->
  RC k T rho e e'.
Proof.
  intros.
  autorewrite with RC.
  intros j Hlt__j.
  assert (0 < k) by lia.
  apply H in H0.
  autorewrite with RC in H0.
  eapply H0.
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
  split. eauto using eval_value, eval_to_value.
  split. eauto using eval_value, eval_to_value.
  autorewrite with RC.
  intros.
  assert (e_f =[0]=> e_f). {
    eapply eval_value.
    eapply eval_to_value.
    eauto.
  }
  assert (e_f0 = e_f /\ j0 = 0) by (eapply eval__deterministic; eauto).
  destruct H2. subst.
  assert (forall i, i < k - 0 -> i < k - j) by apply skip.
  eexists. eexists.
  split. eapply eval_value. eapply eval_to_value. eauto.
  rewrite <- minus_n_O.
  eauto.
Qed.

Corollary RV_unfolded_to_RV : forall k T rho v v',
    value v /\ value v' /\ RC k T rho v v' ->
    RV k T rho v v'.
Proof. intros. auto. Qed.

Lemma RV_to_RC : forall k T rho v v',
  RV k T rho v v' ->
  RC k T rho v v'.
Proof. intros. apply H. Qed.

Lemma RV_condition : forall k T rho v v',
    RV k T rho v v' ->
    0 < k ->

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
              (* Determine the shape of e_f and e'_f *)
              v = Constant sv /\
              v' = Constant sv' /\
              (* Syntactic equality *)
              v = v'

        (* RV for function types *)
        | Ty_Fun T1 T2 =>
            (
              (* Determine the shape of e_f and e'_f *)
              exists x e_body x' e'_body,
                LamAbs x (msubstT (msyn1 rho) T1) e_body = v /\
                LamAbs x' (msubstT (msyn2 rho) T1) e'_body = v' /\
                (* Extensional equivalence *)
                forall i (Hlt_i : i < k) v_2 v'_2,
                  RV i T1 rho v_2 v'_2 ->
                  RC i T2 rho <{ [v_2 / x] e_body }> <{ [v'_2 / x'] e'_body }>
            ) \/ (
              (* Determine the shape of e_f and e'_f*)
              exists f args f' args',
                ExtBuiltin f args = v /\
                ExtBuiltin f' args' = v' /\
                (* Extensional equivalence*)
                forall i (Hlt_i : i < k) v_0 v'_0,
                  RV i T1 rho v_0 v'_0 ->
                  RC i T2 rho (ExtBuiltin f (v_0 :: args)) (ExtBuiltin f' (v'_0 :: args'))
            )

        (* RV for recursive types *)
        | Ty_IFix F T =>
            exists v_2 v'_2,
              (* Determine the shape of e_f and e_f' *)
              v = IWrap (msubstT (msyn1 rho) F) (msubstT (msyn1 rho) T) v_2 /\
              v' = IWrap (msubstT (msyn2 rho) F) (msubstT (msyn2 rho) T) v'_2 /\
              (* Uwrap *)
              forall i (Hlt_i : i < k) K S,
                empty |-* (msubstT (msyn2 rho) T) : K ->
                normalise (unwrapIFix F K T) S ->
                RC i S rho v_2 v'_2

        (* RV for universal types *)
        | Ty_Forall bX K T => 
            (
              exists e_body e'_body,
                (* Determine the shape of e_f and e_f' *)
                v = TyAbs bX K e_body /\
                v' = TyAbs bX K e'_body /\
                (* Instantiational equivalence *)
                forall T1 T2 Chi,
                  empty |-* T1 : K ->
                  empty |-* T2 : K ->
                  Rel T1 T2 Chi ->
                  forall i (Hlt_i : i < k),
                    RC i T ((bX, (Chi, T1, T2)) :: rho) <{ [[T1 / bX ] e_body }> <{ [[T2 / bX ] e'_body }>
            )
      end.
Proof.
  intros.
  destruct H as [Hval__v [Hval__v' HRC]].
  apply eval_value in Hval__v as Hev__v.
  unfold P_value in Hev__v.
  apply eval_value in Hval__v' as Hev__v'.
  unfold P_value in Hev__v'.
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

    exists sv sv',
      (* Determine the shape of e_f and e'_f *)
      v = Constant sv /\
      v' = Constant sv' /\
      (* Syntactic equality *)
      v = v'.
Proof. intros. eapply RV_condition in H. all: eauto. Qed.

Corollary RV_functional_extensionality : forall k T1 T2 rho v v',
    RV k (Ty_Fun T1 T2) rho v v' ->
    0 < k ->

    (
      exists x e_body x' e'_body,
        (* Determine the shape of e_f and e'_f *)
        LamAbs x (msubstT (msyn1 rho) T1) e_body = v /\
        LamAbs x' (msubstT (msyn2 rho) T1) e'_body = v' /\
        (* Extensional equivalence *)
        forall i (Hlt_i : i < k) v_2 v'_2,
          RV i T1 rho v_2 v'_2 ->
          RC i T2 rho <{ [v_2 / x] e_body }> <{ [v'_2 / x'] e'_body }>
    ) \/  (
      (* Determine the shape of e_f and e'_f*)
      exists f args f' args',
        ExtBuiltin f args = v /\
        ExtBuiltin f' args' = v' /\
        (* Extensional equivalence*)
        forall i (Hlt_i : i < k) v_0 v'_0,
          RV i T1 rho v_0 v'_0 ->
          RC i T2 rho (ExtBuiltin f (v_0 :: args)) (ExtBuiltin f' (v'_0 :: args'))
    ).
Proof. intros. eapply RV_condition in H. all: eauto. Qed.

Corollary RV_unwrap : forall k F T rho v v' ,
    RV k (Ty_IFix F T) rho v v' ->
    0 < k ->

    exists v_2 v'_2,
      (* Determine the shape of e_f and e_f' *)
      v = IWrap (msubstT (msyn1 rho) F) (msubstT (msyn1 rho) T) v_2 /\
      v' = IWrap (msubstT (msyn2 rho) F) (msubstT (msyn2 rho) T) v'_2 /\
      (* Uwrap *)
      forall i (Hlt_i : i < k) K S,
        empty |-* (msubstT (msyn2 rho) T) : K ->
        normalise (unwrapIFix F K T) S ->
        RC i S rho v_2 v'_2.
Proof. intros. eapply RV_condition in H. all: eauto. Qed.

Corollary RV_instantiational_extensionality : forall k bX K T rho v v',
    RV k (Ty_Forall bX K T) rho v v' ->
    0 < k ->

    exists e_body e'_body,
      (* Determine the shape of e_f and e_f' *)
      v = TyAbs bX K e_body /\
      v' = TyAbs bX K e'_body /\
      (* Instantiational equivalence *)
      forall T1 T2 Chi,
        empty |-* T1 : K ->
        empty |-* T2 : K ->
        Rel T1 T2 Chi ->
        forall i (Hlt_i : i < k),
          RC i T ((bX, (Chi, T1, T2)) :: rho) <{ [[T1 / bX ] e_body }> <{ [[T2 / bX ] e'_body }>.
Proof. intros. eapply RV_condition in H. all: eauto. Qed.


(** ** Multisubstitutions, multi-extensions, and instantiations *)

Definition kass := list (name * Kind).

Inductive RD : kass -> tymapping -> Prop :=
  | RD_nil :
      RD nil nil
  | RD_cons : forall ck rho T1 T2 Chi X K,
      empty |-* T1 : K ->
      empty |-* T2 : K ->
      (* Something about the fact that T1 and T2 should be reduced? *)
      Rel T1 T2 Chi ->
      RD ck rho ->
      RD ((X, K) :: ck) ((X, (Chi, T1, T2)) :: rho).

(** Instantiation *)
Definition env := list (name * Term).
Definition tass := list (name * Ty).

Inductive RG (rho : tymapping) (k : nat) : tass -> env -> env -> Prop :=
  | RG_nil :
      RG rho k nil nil nil
  | RG_cons : forall x T v1 v2 c e1 e2,
      RV k T rho (msubstA_term (msyn1 rho) v1) (msubstA_term (msyn2 rho) v2) ->
      RG rho k c e1 e2 ->
      RG rho k ((x, T) :: c) ((x, msubstA_term (msyn1 rho) v1) :: e1) ((x, msubstA_term (msyn2 rho) v2) :: e2).
  
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

Fixpoint mdrop {X:Type} (ns : list string) (nxs: list (string * X)) : list (string * X) :=
  match ns with
  | nil => nxs
  | n :: ns' =>
      mdrop ns' (drop n nxs) 
  end.

Lemma subst_closed : forall t,
    closed t -> 
    forall x s,
      <{ [s / x] t }> = t.
Proof.
  intros.
  eapply vacuous_substitution; eauto.
  unfold closed in H.
  apply H.
Qed.

Lemma substA_closed : forall t,
    closed t -> 
    forall X T,
      <{ [[T / X] t }> = t.
Proof.
  intros.
  eapply vacuous_substituteA; eauto.
  unfold closed in H.
  apply H.
Qed.

Lemma subst_not_afi : forall t x v,
    closed v ->
    ~(appears_free_in_Term x <{ [v / x] t }> ).
Proof.
  unfold closed, not.
  induction t; intros x v P A.
  - simpl in A. destruct r.
    + destruct (existsb (eqb x) (bvbs l)) eqn:Hexb.
      * inversion A.
        -- subst.
Admitted.

Lemma duplicate_subst : forall x t v v',
    closed v ->
    <{ [v' / x] ([v / x] t) }> = <{ [v / x] t }>.
Proof. 
  intros. eapply vacuous_substitution. apply subst_not_afi. assumption.
Qed.

Lemma duplicate__subst_bnr : forall x bs v v',
    closed v ->
    <{ [v' / x][bnr] ([v / x][bnr] bs) }> = <{ [v / x][bnr] bs }>.
Proof. intros. Admitted.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v ->
    closed v1 ->
    <{ [v1/x1]([v/x]t) }> = <{ [v/x]([v1/x1]t) }>.
Proof. Admitted.

Lemma swap__subst_bnr : forall bs x x1 v v1,
    x <> x1 ->
    closed v ->
    closed v1 ->
    <{ [v1/x1][bnr]([v/x][bnr] bs) }> = <{ [v/x][bnr]([v1/x1][bnr] bs) }>.
Proof. Admitted.



(** ** Properties of multi-substitutions *)

Lemma msubst_closed : forall t,
    closed t ->
    forall ss,
       msubst_term ss t = t.
Proof.
  induction ss.
  - reflexivity.
  - destruct a.
    simpl.
    rewrite subst_closed; assumption.
Qed.

Lemma msubstA_closed : forall t,
    closed t ->
    forall ss,
      msubstA_term ss t = t.
Proof.
  induction ss.
  - reflexivity.
  - destruct a.
    simpl.
    rewrite substA_closed; assumption.
Qed.

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
    msubst_term env <{ [v/x]t }> = <{ [v/x] {msubst_term (drop x env) t} }>.
Proof.
  induction env0; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (s =? x) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    subst.
    rewrite duplicate_subst; auto.
  - apply eqb_neq in Heqb as Hneq.
    rewrite swap_subst; eauto.
Qed.

Lemma subst_msubst' : forall env x v t,
    closed v ->
    closed_env env ->
    msubst_term (drop x env) <{ [v/x]t }> = <{ [v/x] {msubst_term (drop x env) t} }>.
Proof.
  induction env0; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (s =? x) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    subst.
    eauto.
  - apply eqb_neq in Heqb as Hneq.
    simpl.  
    rewrite swap_subst; eauto.
Qed.

Lemma subst_msubst'' : forall env x xs v t,
    closed v ->
    closed_env env ->
    ~ In x xs ->
    msubst_term (mdrop xs env) <{ [v/x]t }> = <{ [v/x] {msubst_term (mdrop xs env) t} }>.
Proof. Admitted.

Lemma subst_bnr__msubst_bnr : forall env x v bs,
    closed v ->
    closed_env env ->
    msubst_bindings_nonrec env <{ [v/x][bnr] bs }> = <{ [v/x][bnr] {msubst_bindings_nonrec (drop x env) bs} }>.
Proof.
  induction env0; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (s =? x) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    subst.
    rewrite duplicate__subst_bnr; auto.
  - apply eqb_neq in Heqb as Hneq.
    rewrite swap__subst_bnr; eauto.
Qed.

Lemma subst_bnr__msubst_bnr' : forall env x v bs,
    closed v ->
    closed_env env ->
    msubst_bindings_nonrec (drop x env) <{ [v/x][bnr] bs }> = <{ [v/x][bnr] {msubst_bindings_nonrec (drop x env) bs} }>.
Proof. Admitted.
Lemma substA_msubstA : forall envA X U t,
    closed_Ty U ->
    msubstA_term envA <{ [[U/X]t }> = <{ [[U/X] {msubstA_term (drop X envA) t} }>.
Proof. Admitted.

(** ** Properties of multi-extensions *)

Lemma mupdate_lookup : forall (c : tass) (x : name),
    lookup x c = (mupdate empty c) x.
Proof.
  induction c.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    destruct a.
    destruct (s =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      rewrite update_eq.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      rewrite update_neq; auto.
Qed.

Lemma mupdate_drop : forall (c : tass) x T,
    (x |-> T; mupdate empty c) = (x |-> T; mupdate empty (drop x c)).
Proof. 
  induction c; intros. 
  - auto.
  - destruct a.
    simpl.
    destruct (s =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      rewrite update_shadow.
      auto.
    + apply eqb_neq in Heqb as Hneq.
      rewrite update_permute; auto.
      simpl.
      assert ((x |-> T; s |-> t; mupdate empty (drop x c)) = (s |-> t; x |-> T; mupdate empty (drop x c))). {
        apply update_permute. auto. 
      }
      rewrite H.
      f_equal.
      auto.
Qed.

(*
Lemma mupdate_drop : forall (c : tass) Gamma x x',
      lookupT (mupdate Gamma (drop x c)) x' 
    = if String.eqb x x' 
        then lookupT Gamma x' 
        else lookupT (mupdate Gamma c) x'.
Proof. Admitted.
*)

Lemma mupdate_unfold : forall {X : Type} (c : list (string * X)) x (v : X),
    (x |-> v; mupdate empty c) = mupdate empty ((x, v) :: c).
Proof. intros. auto. Qed.

Lemma mdrop_nil : forall X ns,
    @mdrop X ns nil = nil.
Proof. induction ns; auto. Qed.

(** ** Properties of Instantiations *)

Lemma RD_rel : forall ck rho,
    RD ck rho ->
    forall X Chi T1 T2,
      sem rho X = Datatypes.Some Chi ->
      syn1 rho X = Datatypes.Some T1 ->
      syn2 rho X = Datatypes.Some T2 ->
      Rel T1 T2 Chi.
Proof.
  induction 1.
  - intros.
    unfold sem in H.
    inversion H.
  - intros.
    unfold sem in H3.
    unfold syn1 in H4.
    unfold syn2 in H5.
    destruct (X0 =? X) eqn:Heqb.
    + inversion H3. subst.
      inversion H4. subst.
      inversion H5. subst.
      assumption.
    + fold sem in H3.
      fold syn1 in H4.
      fold syn2 in H5.
      eapply IHRD; eauto.
Qed.

Lemma RD_sem_syn : forall ck rho,
    RD ck rho ->
    forall X Chi,
      sem rho X = Datatypes.Some Chi ->
      exists T1 T2, 
        syn1 rho X = Datatypes.Some T1 /\
        syn2 rho X = Datatypes.Some T2.
Proof.
  induction 1.
  - intros.
    unfold sem in H.
    inversion H.
  - intros.
    unfold sem in H3.
    simpl.
    destruct (X0 =? X) eqn:Heqb; eauto.
Qed.

Lemma RG_extend_rho : forall X Chi T1 T2 rho k c env env' ,
    RG rho k c env env' ->
    RG ((X, (Chi, T1, T2)) :: rho) k c env env'.
Proof. Admitted.

Lemma RG_domains_match : forall c e1 e2 k rho,
    RG rho k c e1 e2 ->
    forall x T,
      lookup x c = Datatypes.Some T ->
      exists v1 v2,
        lookup x e1 = Datatypes.Some v1 /\
        lookup x e2 = Datatypes.Some v2.
Proof.
  intros c e1 e2 k rho V. 
  induction V; intros x0 T0 C.
  - discriminate.
  - simpl.
    simpl in C.
    destruct (x =? x0) eqn:Heqb.
    + exists (msubstA_term (msyn1 rho) v1), (msubstA_term (msyn2 rho) v2). split; auto.
    + apply IHV with T0.
      assumption.
Qed.

Lemma RG_env_closed : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    closed_env e1 /\ closed_env e2.
Proof.
  intros rho k c e1 e2 V Hlt.
  induction V; intros.
  - split; reflexivity.
  - split.
    + simpl.
      split.
      * eapply typable_empty__closed.
        eapply RV_typable_empty_1 in H; eauto.
      * apply IHV.
    + simpl.
      split.
      * eapply typable_empty__closed.
        eapply RV_typable_empty_2 in H; eauto.
    * apply IHV.
Qed.

Corollary RG_env_closed_1 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    closed_env e1.
Proof. intros. destruct (RG_env_closed _ _ _ _ _ H H0). assumption. Qed.

Corollary RG_env_closed_2 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    closed_env e2.
Proof. intros. destruct (RG_env_closed _ _ _ _ _ H H0). assumption. Qed.

Lemma RG_env_values : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    value_env e1 /\ value_env e2.
Proof.
  intros rho k c e1 e2 V.
  induction V; intros.
  - split; reflexivity.
  - split.
    + simpl.
      split.
      * eapply H.
      * apply IHV. 
    + split.
      * eapply H.
      * apply IHV.  
Qed.

Lemma RG_env_values_1 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    value_env e1.
Proof. intros. destruct (RG_env_values _ _ _ _ _ H). assumption. Qed.

Lemma RG_env_values_2 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    value_env e2.
Proof. intros. destruct (RG_env_values _ _ _ _ _ H). assumption. Qed. 

Lemma RG_RV : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    forall x T v1 v2,
      lookup x c = Datatypes.Some T ->
      lookup x e1 = Datatypes.Some v1 ->
      lookup x e2 = Datatypes.Some v2 ->
      RV k T rho v1 v2.
Proof.
  intros rho k c e1 e2 V.
  induction V; intros x' T' v1' v2' G E1 E2.
  - destruct x'; discriminate.
  - inversion G. subst.
    inversion E1. subst.
    inversion E2. subst.
    destruct (x =? x').
    + inversion H1. subst.
      inversion H2. subst.
      inversion H3. subst.
      assumption. 
    + apply IHV with x'; assumption.
Qed.

Lemma RG_drop : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    forall x,
      RG rho k (drop x c) (drop x e1) (drop x e2).
Proof.
  intros rho k c e1 e2 V.
  induction V.
  - intros. simpl. apply RG_nil.
  - intros. simpl.
    destruct (x =? x0).
    + apply IHV.
    + eapply RG_cons.
      * eassumption.
      * apply IHV.
Qed.

(** ** Congruence lemmas on [eval] *)

(** ** Multi-substitutions preserve typing *)

Fixpoint mupd (xts : tass) (Gamma : Gamma) : Implementations.Gamma :=
  match xts with
  | nil => Gamma
  | ((a, T) :: xts') => mupd xts' (upd a T Gamma)
  end.

Lemma mupd_nil : forall Gamma,
    mupd nil Gamma = Gamma.
Proof. intros. apply Coq.Logic.FunctionalExtensionality.functional_extensionality. intros. unfold mupd. destruct (Gamma x); auto. Qed.

Lemma mupd_absorbs_msubstT : forall xts x T Gamma,
    mupd xts (x |-> T; Gamma) = (x |-> msubstT xts T; mupd xts Gamma).
Proof.
  induction xts.
  - auto.
  - intros.
    destruct a. 
    simpl.
    rewrite <- upd_absorbs_substituteT.
    eauto.
Qed.

Lemma mupd_empty : forall xts,
    mupd xts empty = empty.
Proof. induction xts; auto. simpl. destruct a. auto. Qed.

Lemma msubstA_preserves_typing_1 : forall rho ck,
    RD ck rho ->
    forall Delta Gamma t T,
      mupdate Delta ck ,, Gamma |-+ t : T ->
      Delta ,, mupd (msyn1 rho) Gamma |-+ (msubstA_term (msyn1 rho) t) : (msubstT (msyn1 rho) T). 
Proof.
  intros rho ck V.
  induction V.
  - intros.
    subst.
    simpl.
    assumption.
  - intros.
    subst.
    simpl.
    unfold mupd.
    simpl.
    eapply IHV; eauto.
    eapply substituteA_preserves_typing; eauto.
Qed.

Lemma msubstA_preserves_typing_2 : forall rho ck,
    RD ck rho ->
    forall Delta Gamma t T,
      mupdate Delta ck ,, Gamma |-+ t : T ->
      Delta ,, mupd (msyn2 rho) Gamma |-+ (msubstA_term (msyn2 rho) t) : (msubstT (msyn2 rho) T). 
Proof.
  intros rho ck V.
  induction V.
  - intros.
    subst.
    simpl.
    assumption.
  - intros.
    subst.
    simpl.
    unfold mupd.
    simpl.
    eapply IHV; eauto.
    eapply substituteA_preserves_typing; eauto.
Qed.

Lemma msubst_preserves_typing_1 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    forall Gamma T t,
      empty ,, (mupd (msyn1 rho) (mupdate Gamma c)) |-+ t : (msubstT (msyn1 rho) T) ->
      empty ,, (mupd (msyn1 rho) Gamma) |-+ (msubst_term e1 t) : (msubstT (msyn1  rho) T). 
Proof.
  intros rho k c e1 e2 V Hlt.
  induction V.
  - intros.
    simpl.
    assumption.
  - intros.
    eapply IHV.
    eapply substitution_preserves_typing.
    + simpl in H0.
      rewrite mupd_absorbs_msubstT in H0.
      eauto.
    + eapply RV_typable_empty_1 in H.
      eauto.
      eauto.
Qed. 

Lemma msubst_preserves_typing_2 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    forall Gamma T t,
      empty ,, (mupd (msyn2 rho) (mupdate Gamma c)) |-+ t : (msubstT (msyn2 rho) T) ->
      empty ,, (mupd (msyn2 rho) Gamma) |-+ (msubst_term e2 t) : (msubstT (msyn2 rho) T). 
Proof.
  intros rho k c e1 e2 V Hlt.
  induction V.
  - intros.
    simpl.
    assumption.
  - intros.
    eapply IHV.
    eapply substitution_preserves_typing.
    + simpl in H0.
      rewrite mupd_absorbs_msubstT in H0.
      eauto.
    + eapply RV_typable_empty_2 in H.
      eauto.
      eauto.
Qed. 

Lemma msubstT_preserves_kinding_1 : forall ck rho,
  RD ck rho ->
  forall Delta T K,
    (mupdate Delta ck) |-* T : K ->
    Delta |-* (msubstT (msyn1 rho) T) : K.
Proof.
  intros ck rho V.
  induction V; intros.
  - assumption.
  - simpl.
    eapply IHV.
    eapply substituteT_preserves_kinding.
    + apply H2.
    + assumption.
Qed.

Lemma msubstT_preserves_kinding_2 : forall ck rho,
  RD ck rho ->
  forall Delta T K,
    (mupdate Delta ck) |-* T : K ->
    Delta |-* (msubstT (msyn2 rho) T) : K.
Proof.
  intros ck rho V.
  induction V; intros.
  - assumption.
  - simpl.
    eapply IHV.
    eapply substituteT_preserves_kinding.
    + apply H2.
    + assumption.
Qed.


(** Logical relation: logical approximation

    If $\Gamma \vdash e : \tau$ and $\Gamma \vdash e' : \tau$, then we write
    $\Gamma \vdash e \leq e' : \tau$ to mean that
    for all $k \geq 0$, if $env$ and $env'$ are mappings from variables $x$ to closed 
    values that are lated for $k$ steps at $\Gamma$, then $\gamma(e)$ and
    $\gamma(e')$ are related for $k$ steps as computations of type $\tau$.
*)
Definition LR_logically_approximate (Delta : partial_map Kind) (Gamma : partial_map Ty) (e e' : Term) (T : Ty) :=
    Delta ,, Gamma |-+ e : T /\
    (Delta ,, Gamma |-+ e' : T) /\
    forall k rho env env' ct ck,
      Delta = mupdate empty ck -> 
      Gamma = mupdate empty ct ->
      RD ck rho ->
      RG rho k ct env env' ->
      RC k T rho (msubst_term env (msubstA_term (msyn1 rho) e)) (msubst_term env' (msubstA_term (msyn2 rho) e')).
      
(** Logical relation: logical equivalence 

    We say $e$ and $e'$ are logically equivalent, written 
    $\Gamma \vdash e \tilde e' : \tau$, if they logically approximate one
    another.
*)

Definition LR_logically_equivalent (Delta : partial_map Kind) (Gamma : partial_map Ty) (e e' : Term) (T : Ty) :=
  LR_logically_approximate Delta Gamma e e' T /\ LR_logically_approximate Delta Gamma e' e T.

Definition LR_logically_approximate_binding (Delta : Delta) (Gamma : Gamma) (b b' : Binding) :=
  Delta ,, Gamma |-ok b /\
  (Delta ,, Gamma |-ok b') /\
  match b, b' with
  | TermBind s (VarDecl x T) e, TermBind s' (VarDecl x' T') e' =>
      s' = s /\
      x' = x /\
      T' = T /\
      LR_logically_approximate Delta Gamma e e' T
  | TypeBind _ _, TypeBind _ _ => b = b'
  | DatatypeBind _, DatatypeBind _ => b = b'
  | _, _ => False
  end.