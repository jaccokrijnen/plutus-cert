Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.

Require Import Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Definition terminates_excl := fun t j v k => t =[j]=> v /\ j < k.
Definition terminates_incl := fun t j v k => t =[j]=> v /\ j <= k.


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
    value v /\ value v' /\
    emptyContext |-+ v : T /\
    emptyContext |-+ v' : T' /\ 
    forall i,
      i <= j ->
      Chi i v v'.



(** ** Relation interpation for computations and values *)

(** *** Fixpoint termination 

    This helper lemma is the key to proving that [RC] is terminating.
*)
Lemma RC_termination_helper : forall i j k,
    i < k ->
    j < k - i ->
    j < k.
Proof. Admitted.

(** RV = Relational interpretation for values, RC = Relation interpretation for computations *)
Equations? RC (k : nat) (T : Ty) (rho : tymapping) (e e' : Term) : Prop by wf k :=
  RC k T rho e e' =>
    (* RC *)
    emptyContext |-+ e : (msubstT (msyn1 rho) T) /\
    emptyContext |-+ e' : (msubstT (msyn2 rho) T) /\

    forall j (Hlt_j : j < k) e_f,
      e =[j]=> e_f ->
      exists e'_f j', e' =[j']=> e'_f /\
      
      (* RV *)
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
              e_f = LamAbs x (msubstT (msyn1 rho) T1) e_body ->
              e'_f = LamAbs x' (msubstT (msyn2 rho) T1) e'_body ->
              (* Extensional equivalence *)
              forall i (Hlt_i : i < k - j) v v' e_body' e'_body',
                value v /\ value v' /\ RC i T1 rho v v' ->
                substitute x v e_body e_body' ->
                substitute x' v' e'_body e'_body' ->
                RC i T2 rho e_body' e'_body'

        (* RV for recursive types *)
        | Ty_IFix F T =>
            forall v v',
              (* Determine the shape of e_f and e_f' *)
              IWrap F T v = e_f ->
              IWrap F T v' = e'_f ->
              (* Uwrap *)
              forall i (Hlt_i : i < k - j) K T',
                empty |-* T : K ->
                normalise (unwrapIFix F K T) T' ->
                RC i T' rho v v'

        (* RV for universal types *)
        | Ty_Forall bX K T => 
            forall e_body e'_body,
              (* Determine the shape of e_f and e_f' *)
              e_f = TyAbs bX K e_body ->
              e'_f = TyAbs bX K e'_body ->
              (* Instantiational equivalence *)
              forall T1 T2 Chi,
                Rel T1 T2 Chi ->
                forall i (Hlt_i : i < k - j),
                  RC i T ((bX, (Chi, T1, T2)) :: rho) e_body e'_body
      end.
Proof. all: eapply RC_termination_helper. all: eauto. Qed.
      
Definition RV (k : nat) (T : Ty) (rho : tymapping) (v v' : Term) : Prop :=
  value v /\ value v' /\ RC k T rho v v'.

Definition possible_type (T : Ty) : Prop :=
  match T with
  | Ty_Forall _ _ _ => True
  | Ty_Fun _ _ => True
  | Ty_Builtin _  => True
  | Ty_IFix _ _ => True
  | _ => False
  end.

Definition impossible_type (T : Ty) : Prop := ~ possible_type T.

(** ** Helper lemmas for RC *)

Lemma RC_typable_empty : forall k T rho e e',
    RC k T rho e e' ->
    emptyContext |-+ e : (msubstT (msyn1 rho) T) /\ emptyContext |-+ e' : (msubstT (msyn2 rho) T).
Proof. intros. destruct T; edestruct H as [He [He' _]]; eauto. Qed.

Lemma RC_typable_empty_1 : forall k T rho e e',
    RC k T rho e e' ->
    emptyContext |-+ e : (msubstT (msyn1 rho) T).
Proof. intros. destruct (RC_typable_empty _ _ _ _ _ H). eauto. Qed.

Lemma RC_typable_empty_2 : forall k T rho e e',
    RC k T rho e e' ->
    emptyContext |-+ e' : (msubstT (msyn2 rho) T).
Proof. intros. destruct (RC_typable_empty _ _ _ _ _ H). eauto. Qed.
(*
Lemma RC_evaluable : forall k T rho e j e_f e',
    terminates_excl e j e_f k ->
    RC k T rho e e' ->
    exists e'_f j', j < k /\ e =[j]=> e_f /\ e' =[j']=> e'_f.
Proof. intros. destruct H. autorewrite with RC in H1.
  destruct T; destruct H0 as [_ [_ [e'_f [j' [Hev_e' _]]]]]; eauto.
  Unshelve. all: eauto.
Qed.

Lemma RC_evaluable_1 : forall k T rho e j e_f e',
    terminates_excl e j e_f k ->
    RC k T rho e e' ->
    j < k /\ e =[j]=> e_f.
Proof. intros. destruct H. eauto. Qed.

Lemma RC_evaluable_2 : forall k rho T e j e_f e',
    terminates_excl e j e_f k ->
    RC k rho T e e' ->
    exists e'_f j', e' =[j']=> e'_f.
Proof. intros. destruct (RC_evaluable _ _ _ _ _ _ _ H H0) as [e'_f [j' [_ [_ Hev_e']]]]; eauto. Qed.

Lemma RC_syntactic_equality : forall k st rho e j e_f e',
    terminates_excl e j e_f k ->
    RC k (Ty_Builtin st) rho e e' ->

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

Lemma RC_functional_extensionality : forall k T1 T2 rho e j e_f e',
    terminates_excl e j e_f k ->
    RC k (Ty_Fun T1 T2) rho e e' ->

    exists e'_f j',
      e' =[j']=> e'_f /\

      (forall x e_body x' e'_body,
        (* Determine the shape of e_f and e'_f *)
        e_f = LamAbs x (msubstT (msyn1 rho) T1) e_body ->
        e'_f = LamAbs x' (msubstT (msyn2 rho) T1) e'_body ->
        (* Extensional equivalence *)
        forall i (Hlt_i : i < k - j) v v' e_body' e'_body',
          value v /\ value v' /\ RC i T1 rho v v' ->
          substitute x v e_body e_body' ->
          substitute x' v' e'_body e'_body' ->
          RC i T2 rho e_body' e'_body').
Proof. 
  intros k T1 T2 rho t1 j1 v1 t2 Hterm RC. 
  destruct Hterm.
  autorewrite with RC in RC.
  destruct RC as [_ [_ [e'_f [j' [Hev_e' Hfe]]]]]; eauto.
Qed.

Lemma RC_unwrap : forall k F T rho e j e_f e',
    terminates_excl e j e_f k ->
    RC k (Ty_IFix F T) rho e e' ->

    exists e'_f j',
      e' =[j']=> e'_f /\

      (forall v v',
        (* Determine the shape of e_f and e_f' *)
        IWrap F T v = e_f ->
        IWrap F T v' = e'_f ->
        (* Uwrap *)
        forall i (Hlt_i : i < k - j) K T',
          empty |-* T : K ->
          normalise (unwrapIFix F K T) T' ->
          RC i T' rho v v').
Proof.
  intros k F T rho t1 j1 v1 t2 Hterm RC.
  destruct Hterm. 
  autorewrite with RC in RC.
  destruct RC as [_ [_ [e'_f [j' [Hev_e' Hunwrap]]]]]; eauto.
Qed.

Lemma RC_instantiational_extensionality : forall k bX K T rho e j e_f e',
    terminates_excl e j e_f k ->
    RC k (Ty_Forall bX K T) rho e e' ->

    exists e'_f j',
      e' =[j']=> e'_f /\

      (forall e_body e'_body,
        (* Determine the shape of e_f and e_f' *)
        e_f = TyAbs bX K e_body ->
        e'_f = TyAbs bX K e'_body ->
        (* Instantiational equivalence *)
        forall T1 T2 Chi,
          Rel T1 T2 Chi ->
          forall i (Hlt_i : i < k - j),
            RC i T ((bX, (Chi, T1, T2)) :: rho) e_body e'_body).
Proof.
  intros k X K T rho t1 j1 v1 t2 Hterm RC. 
  destruct Hterm.
  autorewrite with RC in RC.
  destruct RC as [_ [_ [e'_f [j' [Hev_e' Hie]]]]]; eauto.
Qed.


Lemma RC_impossible_type : forall k rho e j e_f e',
    terminates_excl e j e_f k ->

    (forall bX K T, ~(RC k (Ty_Lam bX K T) rho e e')) /\
    (forall T1 T2, ~(RC k (Ty_App T1 T2) rho e e')).
Proof. intros. destruct H. split; try split; try solve [intros; intro Hcon; destruct Hcon as [_ [_ [_ [_ [_ Hfls]]]]]; eauto]. Qed.

(*
Lemma RC_nontermination : forall k T rho e e',
    ~(exists e_f j, terminates_excl e j e_f k) ->
    emptyContext |-+ e : (msubstT_rho_syn1 rho T) ->
    emptyContext |-+ e' : (msubstT_rho_syn2 rho T) ->
    RC k T rho e e'.
Proof. intros. unfold terminates_excl in H. destruct T; try solve [split; auto; split; auto; intros; exfalso; apply H; eauto]. Qed.
*)
*)


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
  | RG_cons : forall x T v1 v2 c e1 e2 v1_s v2_s,
      msubstA (msyn1 rho) v1 v1_s ->
      msubstA (msyn2 rho) v2 v2_s ->
      value v1_s ->
      value v2_s ->
      RC k T rho v1_s v2_s ->
      RG rho k c e1 e2 ->
      RG rho k ((x, T) :: c) ((x, v1_s) :: e1) ((x, v2_s) :: e2).

Fixpoint mupdate {X:Type} (m : partial_map X) (xts : list (string * X)) :=
  match xts with
  | nil => m
  | ((x, v) :: xts') => x |-> v ; (mupdate m xts')
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


Lemma subst_closed : forall t,
    closed t -> 
    forall x s t',
      substitute x s t t' ->
      t' = t.
Proof.
  intros.
  eapply vacuous_substitution; eauto.
  unfold closed in H.
  apply H.
Qed.

Lemma substA_closed : forall t,
    closed t -> 
    forall X T t',
      substituteA X T t t' ->
      t' = t.
Proof.
  intros.
  eapply vacuous_substituteA; eauto.
  unfold closed in H.
  apply H.
Qed.

Lemma subst_not_afi : forall t x v,
    closed v ->
    forall t',
      substitute x v t t' ->
      ~(appears_free_in_Term x t').
Proof. Abort.

Lemma duplicate_subst : forall x t v s,
    closed v ->
    forall t' t'',
      substitute x v t t' ->
      substitute x s t' t'' ->
      t'' = t'.
Proof. Abort.

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
Proof. Abort.



(** ** Properties of multi-substitutions *)

Lemma msubst_closed : forall t,
    closed t ->
    forall ss t',
      msubst ss t t' ->
      t' = t.
Proof.
  induction ss.
  - intros.
    inversion H0. 
    subst.
    reflexivity.
  - intros.
    inversion H0. 
    subst.
    assert (t'0 = t) by eauto using subst_closed.
    subst.
    apply IHss.
    assumption.
Qed.

Lemma msubstA_closed : forall t,
    closed t ->
    forall ss t',
      msubstA ss t t' ->
      t' = t.
Proof.
  induction ss.
  - intros.
    inversion H0. 
    subst.
    reflexivity.
  - intros.
    inversion H0. 
    subst.
    assert (t'0 = t) by eauto using substA_closed.
    subst.
    apply IHss.
    assumption.
Qed.

Inductive close_off_env (envA : list (tyname * Ty)) : env -> env -> Prop :=
  | CO_nil : 
      close_off_env envA nil nil
  | CO_cons : forall x t t' env env',
      msubstA envA t t' ->
      close_off_env envA env env' ->
      close_off_env envA ((x,t) :: env) ((x, t') :: env').

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

Lemma mupdate_unfold : forall c x (T : Ty),
    (x |-> T; mupdate empty c) = mupdate empty ((x, T) :: c).
Proof. intros. auto. Qed.

(** ** Properties of Instantiations *)

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
    + exists v1_s, v2_s. auto.
    + apply IHV with T0.
      assumption.
Qed.

Lemma RG_env_closed : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    closed_env e1 /\ closed_env e2.
Proof.
  intros rho k c e1 e2 V.
  induction V; intros.
  - split; reflexivity.
  - split.
    + simpl.
      split.
      * eapply typable_empty__closed.
        eapply RC_typable_empty_1 in H3; eauto.
      * apply IHV.
    + simpl.
      split.
      * eapply typable_empty__closed.
        eapply RC_typable_empty_2 in H3; eauto.
    * apply IHV.
Qed.

Corollary RG_env_closed_1 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    closed_env e1.
Proof. intros. destruct (RG_env_closed _ _ _ _ _ H). assumption. Qed.

Corollary RG_env_closed_2 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    closed_env e2.
Proof. intros. destruct (RG_env_closed _ _ _ _ _ H). assumption. Qed.

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
      * assumption.
      * apply IHV. 
    + simpl.
      split.
      * assumption.
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

Lemma RG_RC : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    forall x T v1 v2,
      lookup x c = Datatypes.Some T ->
      lookup x e1 = Datatypes.Some v1 ->
      lookup x e2 = Datatypes.Some v2 ->
      RC k T rho v1 v2.
Proof.
  intros rho k c e1 e2 V.
  induction V; intros x' T' v1' v2' G E1 E2.
  - destruct x'; discriminate.
  - inversion G. subst.
    inversion E1. subst.
    inversion E2. subst.
    destruct (x =? x').
    + inversion H5. subst.
      inversion H6. subst.
      inversion H7. subst.
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
      * eassumption.
      * assumption.
      * assumption.
      * assumption.
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
    forall Delta Gamma t t' T,
      (mupdate Delta ck, Gamma) |-+ t : T ->
      msubstA (msyn1 rho) t t' ->
      (Delta, mupd (msyn1 rho) Gamma) |-+ t': (msubstT (msyn1 rho) T). 
Proof.
  intros rho ck V.
  induction V.
  - intros.
    subst.
    inversion H0. subst.
    simpl.
    assumption.
  - intros.
    subst.
    inversion H3. subst.
    simpl.
    unfold mupd.
    simpl.
    eapply IHV; eauto.
    eapply substituteA_preserves_typing; eauto.
Qed.

Lemma msubstA_preserves_typing_2 : forall rho ck,
    RD ck rho ->
    forall Delta Gamma t t' T,
      (mupdate Delta ck, Gamma) |-+ t : T ->
      msubstA (msyn2 rho) t t' ->
      (Delta, mupd (msyn2 rho) Gamma) |-+ t': (msubstT (msyn2 rho) T). 
Proof.
  intros rho ck V.
  induction V.
  - intros.
    subst.
    inversion H0. subst.
    simpl.
    assumption.
  - intros.
    subst.
    inversion H3. subst.
    simpl.
    unfold mupd.
    simpl.
    eapply IHV; eauto.
    eapply substituteA_preserves_typing; eauto.
Qed.

Lemma msubst_preserves_typing_1 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    forall Gamma T t t',
      (empty, mupd (msyn1 rho) (mupdate Gamma c)) |-+ t : (msubstT (msyn1 rho) T) ->
      msubst e1 t t' ->
      (empty, mupd (msyn1 rho) Gamma) |-+ t': (msubstT (msyn1  rho) T). 
Proof.
  intros rho k c e1 e2 V.
  induction V.
  - intros.
    inversion H0. subst.
    assumption.
  - intros.
    inversion H5. subst.
    eapply IHV.
    + eapply substitution_preserves_typing.
      * simpl in H4.
        rewrite mupd_absorbs_msubstT in H4.
        eauto.
      * eapply RC_typable_empty_1 in H3.
        
        subst.
        eauto.
      * eassumption.
    + assumption.
Qed. 

Lemma msubst_preserves_typing_2 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    forall Gamma T t t',
      (empty, mupd (msyn2 rho) (mupdate Gamma c)) |-+ t : (msubstT (msyn2 rho) T) ->
      msubst e2 t t' ->
      (empty, mupd (msyn2 rho) Gamma) |-+ t': (msubstT (msyn2 rho) T). 
Proof.
  intros rho k c e1 e2 V.
  induction V.
  - intros.
    inversion H0. subst.
    assumption.
  - intros.
    inversion H5. subst.
    eapply IHV.
    + eapply substitution_preserves_typing.
      * simpl in H4.
        rewrite mupd_absorbs_msubstT in H4.
        eauto.
      * eapply RC_typable_empty_2 in H3.
        
        subst.
        eauto.
      * eassumption.
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
    (Delta, Gamma) |-+ e : T /\
    (Delta, Gamma) |-+ e' : T /\
    forall k rho env env' ct ck,
      Delta = mupdate empty ck -> Gamma = mupdate empty ct ->
      RD ck rho /\
      RG rho k ct env env' ->
      forall e_sa e'_sa e_s e'_s,
        msubstA (msyn1 rho) e e_sa ->
        msubstA (msyn2 rho) e e'_sa ->
        msubst env e_sa e_s ->
        msubst env' e'_sa e'_s ->
        RC k T rho e_s e'_s.
      
(** Logical relation: logical equivalence 

    We say $e$ and $e'$ are logically equivalent, written 
    $\Gamma \vdash e \tilde e' : \tau$, if they logically approximate one
    another.
*)

Definition LR_logically_equivalent (Delta : partial_map Kind) (Gamma : partial_map Ty) (e e' : Term) (T : Ty) :=
  LR_logically_approximate Delta Gamma e e' T /\ LR_logically_approximate Delta Gamma e' e T.