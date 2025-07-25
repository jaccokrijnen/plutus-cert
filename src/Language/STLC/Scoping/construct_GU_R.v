From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List Util.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

From PlutusCert Require Import
  alpha_vacuous
  construct_GU
  step_naive
  psubs
  util
  STLC GU_NC
  Alpha.alpha
  variables
  alpha_subs
  alpha_freshness.

Require Import Coq.Program.Equality.

(* Procedure that freshens all variables in to_freshen, not using names in used, and all being distinct *)
Definition freshen used to_freshen :=
  fold_right
    (fun x acc =>
      let fresh_var := fresh_to_GU_ (used ++ to_freshen) acc x in
      (x, fresh_var) :: acc) (* New element is added at the front in `fold_right` *)
    [] to_freshen.


(* Constructs an extended renaming context.
  Does: Rename ftvs in t (that are not in s) in construction of new t' *)
Definition a_R_constr R (s s' : term) t : list (string * string) :=
  let used := tv s ++ tv s' ++ tv t ++ (map fst R) ++ (map snd R) in
  let to_freshen := list_diff string_dec (ftv t) (ftv s) in
  let Rfr := freshen used to_freshen in
  Rfr ++ R.


(* If the new fresh variable is based on everything in original R, it will be genuinly "fresh"*)
Lemma R_Well_formedFresh x R R' used :
  R_Well_formed R ->
  (forall y, In y (map fst R ++ map snd R) -> (In y used) \/ (In y (map fst R' ++ map snd R'))) ->
  R_Well_formed ((x, fresh_to_GU_ used R' x)::R).
Proof.
  intros.
  unfold R_Well_formed in *.
  intros.
  destr_eqb_eq x0 x.
  - simpl in H1.
    rewrite String.eqb_refl in H1.
    inv H1.
    constructor.
  - inv H1.
    rewrite <- String.eqb_neq in H2.
    rewrite String.eqb_sym in H2.
    rewrite H2 in H4.
    remember H4 as H4_lookup.
    clear HeqH4_lookup.
    apply lookup_some_then_in_values in H4.
    assert (In y (map fst R ++ map snd R)).
    {
      apply in_app_iff. right. auto.
    }
    specialize (H0 y H1).
    apply alpha_var_diff; auto.
    + rewrite <- String.eqb_neq. auto.
    + destruct H0.
      * assert (~ In (fresh_to_GU_ used R' x) used) by apply fresh_to_GU__fresh_over_ftvs.
        intros Hcontra.
        subst.
        contradiction.
      * assert (~ In (fresh_to_GU_ used R' x) (map fst R' ++ map snd R')) by apply fresh_to_GU__fresh_over_binders.
        intros Hcontra.
        subst.
        contradiction.
Qed.

(* Analogous but for multiple renamings *)
Lemma R_Well_formedFreshMultiple used R l :
  R_Well_formed R -> R_Well_formed ((freshen (used ++ map fst R ++ map snd R) l ) ++ R).
Proof.
  unfold freshen.
  remember ((used ++ map fst R ++ map snd R) ++ l) as used'.
  (* I find this interesting. We are doing this to lose information, it is like we are weakening the induction hypothesis!*)
  assert ({l' &  (used ++ map fst R ++ map snd R) ++ l' = (used ++ map fst R ++ map snd R) ++ l}%type).
  {
    exists l. auto.
  }
  destruct H as [l' Heq].
  rewrite <- Heq in Heqused'.
  clear Heq.
  subst.

  induction l.
  - simpl. auto.
  - intros.
    unfold freshen.
    change (a :: l) with ([a] ++ l).
    rewrite fold_right_app.
    simpl.
    remember ((fold_right
        (fun (x : string) (acc : list (string * string)) =>
      _
      :: acc)
        []
        l)) as R''.
    unfold freshen in IHl.
    specialize (IHl H).
    change ((a, fresh_to_GU_ ((used ++ map fst R ++ map snd R) ++ (a :: l)) R'' a) :: R'' ++ R) with ((a, fresh_to_GU_ ((used ++ map fst R ++ map snd R) ++ (a :: l)) R'' a) :: (R'' ++ R)).

    eapply R_Well_formedFresh; auto.
    + intros.
      rewrite map_app in H0.
      apply in_app_iff in H0.
      rewrite map_app in H0.
      destruct H0.
      * apply in_app_iff in H0.
        destruct H0; intuition.
        left. apply in_app_iff. left. apply in_app_iff. right. intuition.
      * apply in_app_iff in H0.
        destruct H0; intuition.
        left. apply in_app_iff. intuition.
Qed.

(* If x is banned (by being in used), or x is in the generator list l, then it will not be in the freshened list *)
(* NOTE: We have to prove over in l and in used simultaneously, because things move from l to used*)
Lemma freshen2__fresh_not_generator {used l } {x : string } :
  (In x l \/ In x used) -> ~ In x (map snd (freshen used l)).
Proof.
  intros Hin.
  generalize dependent used.
  induction l; intros.
  - simpl in Hin. simpl. auto.
  - destruct Hin.
    + (* In x l case*)
      destruct H.
      *
      {
        subst.
        unfold freshen.
        simpl.
        apply de_morgan2.
        split.
        * assert (~ In (fresh_to_GU_ (used ++ x :: l)
    (fold_right
    (fun (x0 : string) (acc : list (string * string)) =>
  (x0, fresh_to_GU_ (used ++ x :: l) acc x0) :: acc)
    []
    l) x) (used ++ (x :: l))).
          {
            apply fresh_to_GU__fresh_over_ftvs.
          }
          apply not_in_app in H as [_ H].
          apply not_in_cons in H as [H _].
          auto.
        * assert (((used ++ [x]) ++ l) = (used ++ x :: l)).
        { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
          rewrite <- H.
          eapply IHl. (* Here we use IHL where we need the simultaneous induction prniciple over used.*)
          right.
          apply in_app_iff.
          right.
          apply in_eq.
    }
    * {
      simpl.
      apply de_morgan2.
      split.
      --
        (* x not in ftvs of fresh_to_GU, but also x in l, which is in ftvs/used *)
        assert (~ In (fresh_to_GU_ (used ++ a :: l)
            (fold_right (fun (x0 : string) (acc : list (string * string)) =>
            (x0, fresh_to_GU_ (used ++ a :: l) acc x0) :: acc) [] l) a )

            (used ++ a :: l)).
        {
          apply fresh_to_GU__fresh_over_ftvs.
        }
        intros Hcontra.
        apply not_in_app in H0 as [_ H0].
        apply not_in_cons in H0 as [_ H0].
        subst.
        contradiction.
      -- simpl in IHl.
          assert ( HChange: ((used ++ [a]) ++ l) = (used ++ a :: l)).
        { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
          rewrite <- HChange.
          eapply IHl.
          left. auto.
    }
  + (* In x used case *)
    simpl.
    apply de_morgan2.
    split.
    * remember ((fold_right _ _ _)) as fld.
      assert (~ In (fresh_to_GU_ (used ++ a :: l) fld a) (used ++ a :: l)).
      { apply fresh_to_GU__fresh_over_ftvs. }
      apply not_in_app in H0 as [H0 _].
      intros Hcontra.
      subst.
      contradiction.
    * unfold freshen in IHl.
      assert (HChange: ((used ++ [a]) ++ l) = (used ++ a :: l)).
      { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
      rewrite <- HChange.
      eapply IHl.
      right. apply in_app_iff. left. auto.
Qed.

(* If y is in the freshened list, then it cannot have been in the generator l*)
Lemma freshen2__fresh_generator {used l } {y : string } :
  In y (map snd (freshen used l)) -> ~ In y l.
Proof.
  intros Hin Hcontra.
  eapply or_introl in Hcontra.
  eapply @freshen2__fresh_not_generator with (used := used) in Hcontra.
  contradiction.
Qed.

(* If y is in the freshened list, then it cannot have been in the banned "used" context*)
Lemma freshen2__fresh_map_snd {used l } {y : string } :
  In y (map snd (freshen used l)) -> ~ In y used.
Proof.
  intros Hin Hcontra.
  eapply or_intror in Hcontra.
  eapply @freshen2__fresh_not_generator with (l := l) in Hcontra.
  contradiction.
Qed.

(* If x is a key in the list of fresh renamings, then x must be in the generator l*)
Lemma in_freshen2_then_in_generator used l x :
  In x (map fst (freshen used l)) -> In x l.
Proof.
  intros Hin.
  generalize dependent used.
  induction l; intros.
  - simpl in Hin. auto.
  - simpl in Hin.
    destruct Hin.
    + subst. simpl. auto.
    + unfold freshen in IHl.
      assert (Hchange: ((used ++ [a]) ++ l) = (used ++ a :: l)).
        { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
      rewrite <- Hchange in H.
      eapply IHl in H.
      simpl.
      right.
      auto.
Qed.

(* If x is in the gnerator, then x will be renamed by the fresh renamings*)
Lemma in_generator_then_in_freshen2 used l x :
  In x l -> In x (map fst (freshen used l)).
Proof.
  intros Hin.
  generalize dependent used.
  induction l; intros.
  - simpl in Hin. auto.
  - unfold freshen.
    simpl.
    destruct Hin.
    + subst. simpl. auto.
    + right.
      assert (Hchange: ((used ++ [a]) ++ l) = (used ++ a :: l)).
      { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
      rewrite <- Hchange.
      eapply IHl in H.
      unfold freshen in H.
      eauto.
Qed.

(* Strengthened statement: The constructed renaming context is well-formed for free type variables in t: if under R' we have left-sided lookup behaviour, then this is mirrored by right-sided lookup behaviour
Note: uses that R is used to relate s and s' to be able to case distinct on x in s or x not in s.
*)
Lemma a_R_constr_helper R R' s s' t x y :
  R' = @a_R_constr R s s' t ->

  In x (ftv t) ->
  lookup x R' = Some y ->
  Alpha R s s' ->
  AlphaVar R' x y.
Proof.
  intros.
  unfold a_R_constr in H.
  remember (freshen _ _) as Rfr.
  rewrite H in H1.
  apply lookup_app_or_extended in H1 as [H_in_fresh | [H_ni_fresh H_in_strip] ].
  - assert (AlphaVar Rfr x y).
    {
      assert (R_Well_formed (Rfr ++ nil)).
      {
        subst.
        assert ((tv s ++
            tv s' ++
            tv t ++ map fst R ++ map snd R) = (tv s ++
            tv s' ++
            tv t ++ map fst R ++ map snd R) ++ (@map (string * string) string fst []) ++ (@map (string * string) string snd [])).
        { simpl. rewrite app_nil_r. auto. }
        rewrite H.
        eapply R_Well_formedFreshMultiple.
        unfold R_Well_formed. intros. inversion H1.
      }
      unfold R_Well_formed in H1. repeat rewrite app_nil_r in H1.
      eapply H1; auto.
    }

    assert (lookup_r y (Rfr ++ R) = Some x).
    {
      apply lookup_r__app.
      apply av_lookup_implies_right in H1; auto.
    }
    rewrite H.
    eapply lookup_some_then_alphavar; eauto.
    + apply lookup_app_r; auto.

  -
    assert (AlphaVar R x y).
    {
      assert (In x (ftv s)).
      {
        apply lookup__not_in in H_ni_fresh.
        subst.
        assert (~ In x (list_diff string_dec (ftv t) (ftv s))).
        {
          intros Hcontra.
          eapply in_generator_then_in_freshen2 with (used := (tv s ++ tv s' ++ tv t ++ map fst R ++ map snd R)) in Hcontra.
          contradiction.
        }
        eapply list_diff_got_filtered; eauto.
      }
      clear HeqRfr H0 H H_ni_fresh.
      apply (alpha_preserves_ftv' H1) in H2 as [y' [H2_a H2_fr]].
      destruct (alphavar_models_lookup H2_a) as [[H2_a' _] | [[H2_a' _] _]].
      + rewrite H_in_strip in H2_a'. congruence.
      + rewrite H2_a' in H_in_strip. congruence.
    }
    assert (lookup x R' = Some y).
    {
      rewrite H.
      apply lookup_none_app; auto.

    }
    assert (lookup_r y R' = Some x).
    {
      assert (lookup_r y Rfr = None).
      {
        assert (In y (map snd R)).
        {
          apply lookup_In in H_in_strip.
          apply in_map_iff.
          exists ((x, y)). simpl. split; auto.
        }

        assert (In y ((tv s ++
            tv s' ++
            tv t ++
            map fst R ++
            map snd R))).
        {

          apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. auto.
        }
            remember ((tv s ++
              tv s' ++
              tv t ++
              map fst R ++
              map snd R)) as used.
        assert (~ In y (map snd Rfr)).
        {
          rewrite HeqRfr.
          intros Hcontra.
          eapply freshen2__fresh_map_snd in Hcontra.
          contradiction.
        }
        apply not_ex__lookup_r_none. auto.
      }
      rewrite H.
      eapply lookup_r__extend.
      + auto.
      + apply alphavar_models_lookup in H1.
        destruct H1.
        * destruct p. auto.
        * destruct p. destruct p. rewrite e0 in H_in_strip. inversion H_in_strip.
    }
    eapply lookup_some_then_alphavar; eauto.
Qed.

(* Using the construction for renaming contexts a_R_constr, we generate a globally unique type that has free variables renamed according to that renaming context
*)
Definition a_constr {R} {s s' : term} t : prod (list (string * string)) (term) :=
  let R' := @a_R_constr R s s' t in
  let used' := tv s ++ tv s' ++ tv t ++ (map fst R') ++ (map snd R') in
  (R', snd (to_GU_ used' R' t)).

(* In a_R_constr, α-equivalence of the original s and s' is preserved by the updated renaming context *)
Lemma a_R_constr_alpha_s R s s' t R' :
  R' = a_R_constr R s s' t ->
  Alpha R s s' ->
  Alpha R' s s'.
Proof.
  intros.
  unfold a_R_constr in H.
  remember (freshen _ _) as Rfr.
  rewrite H.
  eapply alpha_vacuous_R.
  - intros.
    remember ((tv s ++
        tv s' ++
        tv t ++
        map fst R ++
        map snd R)) as used.
    intros Hcontra.
    apply list_diff_not with (l1 := (ftv t)) in Hcontra.
    rewrite HeqRfr in H1.
    apply in_freshen2_then_in_generator in H1.
    contradiction.
  - intros.
    rewrite HeqRfr in H1.
    apply freshen2__fresh_map_snd in H1.
    apply not_in_app in H1 as [_ H1].
    apply not_in_app in H1 as [H1 _].
    intros Hcontra.
    apply extend_ftv_to_tv in Hcontra.
    contradiction.
  - auto.
Qed.

(* If x is not in R, it did not get renamed *)
Lemma alphavar_id_helper {R x y} :
  AlphaVar R x y ->
  ~ In x (map fst R) ->
  y = x.
Proof.
  intros Ha Hno.
  induction Ha; auto.
  - simpl in Hno. intuition.
  - eapply IHHa.
    simpl in Hno. intuition.
Qed.

(* If x free in s, and x does not get renamed.
  Then x must be free in s'.
  If it would then be renamed from s' (by being in snd R), we would break alpha-equivalence by uniquess of alpha-equivalence *)
Lemma alpha_contradiction_helper R s s' x :
  Alpha R s s' ->
  ~ In x (map fst R) ->
  In x (ftv s) ->
  ~ In x (map snd R).
Proof.
  intros.
  induction H.
  - apply ftv_var in H1; subst.
    assert (y = x0) by apply (alphavar_id_helper a H0).

    induction a.
    + auto.
    + simpl in H0. intuition.
    + subst.
      simpl.
      apply de_morgan2.
      split; auto.
      eapply IHa; eauto.
      simpl in H0. apply de_morgan2 in H0. destruct H0; auto.

  - assert (~ In x (map snd ((x0, y)::R))).
    {
      eapply IHAlpha.
      assert (x <> x0).
      {
        simpl in H1.
        apply in_remove in H1.
        intuition.
      }
      simpl. intuition.
      eapply ftv_lam_helper; eauto.
    }
    simpl in H2.
    apply de_morgan2 in H2.
    destruct H2 as [_ H2].
    auto.
  - simpl in H1.
    apply in_app_or in H1.
    destruct H1.
    + eapply IHAlpha1; eauto.
    + eapply IHAlpha2; eauto.
  - inversion H1.
Qed.

Lemma map_pair_helper {A : Type} (x : string) l (f : A) :
  In x l -> In x (map fst ((map (pair^~ f) l))).
Proof.
  intros.
  apply in_map_iff.
  exists (x, f).
  simpl.
  split.
  auto.
  apply in_map with (f := pair^~ f) in H.
  auto.
Qed.

(* a_constr construct an α-equivalent t' *)
Lemma a_constr__t_alpha {R s s' t R' t'} :
  (R', t') = @a_constr R s s' t ->
  Alpha R s s' ->
  Alpha R' t t'.
Proof.
  unfold a_constr.
  intros.
  inversion H.
  apply to_GU__alpha_'.
  - intros.
    eapply a_R_constr_helper.
    + eauto.
    + auto.
    + auto.
    + auto.
  - intros.
    rewrite <- H2.
    apply lookup_none_then_no_key in H4.

    assert (In x (ftv s)).
    {
      unfold a_R_constr in H3.
      remember (freshen _ _) as frMap.

      destruct (in_dec string_dec x (ftv s)).
      - auto.
      - exfalso.

         assert (In x  (list_diff string_dec
  (ftv t) (ftv s))).
        {
          apply list_diff_helper.
          auto. auto.
        }
        exfalso.

        assert (In x (map fst frMap)).
      {


        subst.
        remember (list_diff _ _ _) as l.
        eapply in_generator_then_in_freshen2.
        auto.
      }

      unfold a_R_constr in H4.
      rewrite <- HeqfrMap in H4.
      rewrite map_app in H4.
      apply not_in_app in H4. destruct H4 as [H4 _].
      contradiction.


    }


    assert (~ In x (map snd R')).
    {
      (* Then there exists x' s.t. (x', x) in (strip_R R)*)
      eapply alpha_contradiction_helper.
      eapply a_R_constr_alpha_s; eauto.
      subst. auto.
      auto.
    }

    apply alphavar_refl_weaken_vacuouss.
    + subst. auto.
    + subst. auto.
  - intros.
    apply in_or_app.
    intuition.
Qed.

(* specialization of a_R_constr__s*)
Lemma a_constr__s_alpha {R s s' t R' t'} :
  (R', t') = @a_constr R s s' t ->
  Alpha R s s' ->
  Alpha R' s s'.
Proof.
  intros.
  unfold a_constr in H.
  inversion H.
  eapply a_R_constr_alpha_s with (R' := R') (t := t) in H0; eauto.
  subst.
  eauto.
Qed.


(* Another construction R_constr that generates a renaming context that freshens all ftvs in t that are binders in s and sigma.
NOTE: This is used in the generalized fundamental theorem
*)
Definition R_constr (t : term) (s : term) (sigma : list (string * term)) (X : string) : prod (list (string * string)) (list (string * string)) :=
    let tvs := tv s ++ tv_keys_env sigma in
  let btvs := btv s ++ btv_env sigma in
  let tv_t := tv t in
  let used := tv_t ++ tvs ++ [X] in
  let R2 := map (fun x => (x, x)) (list_diff string_dec (ftv t) btvs) in
  let R1 := freshen (used ++ map fst R2 ++ map snd R2) btvs in (* Added map fst R2 ++ map snd R2 for easier proving*)
  (* we rename those ftvs in t that are binders in s and sigma*)
  (R1, R2).

(* All elements in the rhs of R are distinct *)
Inductive UniqueRhs : list (string * string) -> Prop :=
| uniqueRhs_nil : UniqueRhs nil
| uniqueRhs_cons : forall x y l,
    ~ In y (map snd l) ->
    UniqueRhs l ->
    UniqueRhs ((x, y) :: l).

(* All variables generated by freshen2 are distinct*)
Lemma freshen2__uniqueRHs {used l} :
  UniqueRhs (freshen used l).
Proof.
  generalize dependent used.
  induction l; intros.
  - unfold freshen. simpl. constructor.
  - unfold freshen.
    simpl.
    constructor.
    + remember (fold_right _ _ _) as fld.
      apply fresh_to_GU__fresh_over_snd_binders.
    + unfold freshen in IHl.
      assert (Hchange: ((used ++ [a]) ++ l) = (used ++ a :: l)).
      { rewrite <- app_assoc. rewrite <- app_comm_cons. auto. }
      rewrite <- Hchange.
      eapply IHl.
Qed.

(* If all rhs elements are distinct and we lookup x in l to get y,
  this is the only y in the rhs of l. Hence lookup_r y must return x.
  If it were to return x' <> x, then there must exist (x', y) breaking the uniqueness
*)
Lemma lookup_Some__uniqueRhs__lookup_r {l x y} :
  lookup x l = Some y ->
  UniqueRhs l ->
  lookup_r y l = Some x.
Proof.
  intros Hlu Hunique.
  induction l.
  - inversion Hlu.
  - destruct a as [a1 a2].
    destr_eqb_eq a1 x.
    + simpl in Hlu.
      rewrite String.eqb_refl in Hlu.
      inversion Hlu; subst.
      simpl.
      rewrite String.eqb_refl.
      f_equal.
    + simpl in Hlu.
      rewrite <- String.eqb_neq in H.
      rewrite H in Hlu.
      inversion Hunique; subst.
      specialize (IHl Hlu H4).
      simpl.
      destr_eqb_eq a2 y.
      * exfalso.
        apply lookup_r_then_in_map_snd in IHl.
        contradiction.
      * auto.
Qed.

(* Freshen creates unique rhs renaming contexts, hence we have similar bothsided lookup behaviour*)
Lemma freshen2_lookup__lookup_r {used l x x'} :
  lookup x (freshen used l) = Some x' ->
  lookup_r x' (freshen used l) = Some x.
Proof.
  intros Hlookup.
  eapply lookup_Some__uniqueRhs__lookup_r; auto.
  apply freshen2__uniqueRHs.
Qed.

(* Alpha models lookup *)
Lemma freshen2_alpha_lookup {used l x x'} :
  lookup x (freshen used l) = Some x' ->
  AlphaVar (freshen used l) x x'.
Proof.
  intros Hlookup.
  remember (freshen2_lookup__lookup_r Hlookup) as Hlookup'; clear HeqHlookup'.
  apply lookup_some_then_alphavar; eauto.
Qed.

(* By rhs of freshen is unique ( each rhs element gets uniqued/freshened)*)
Lemma freshen2_alpha {used l x} :
  In x l ->
  {x' & AlphaVar (freshen used l) x x' * (x <> x')}%type.
Proof.
  intros Hin.
  assert (Hex: {x' & lookup x (freshen used l) = Some x'}).
  {
    eapply in_generator_then_in_freshen2 in Hin.
    apply in_map_iff_sigma in Hin.
    destruct Hin as [x' H_inmap].

    apply in_map__exists_lookup in H_inmap.
    eauto.
  }
  destruct Hex as [x' Hax].
  exists x'.
  split.
  - apply freshen2_alpha_lookup; auto.
  - assert (In x' (map snd (freshen used l))).
    { apply lookup_some_then_in_values in Hax. auto. }
    eapply freshen2__fresh_generator in H.
    intros Hcontra.
    subst.
    contradiction.
Qed.

(* R_constr's second renaming context is an identity renaming*)
Lemma R_constr_R2_IdCtx {t s sigma X R1 R2} :
  (R1, R2) = R_constr t s sigma X ->
  IdCtx R2.
Proof.
  intros Hconstr.
  unfold R_constr in Hconstr.
  inversion Hconstr; clear Hconstr H0 H1.
  apply map_creates_IdCtx.
Qed.


Lemma R_constr__BU3 { R1 R2 t s sigma X} :
  (R1, R2) = R_constr t s sigma X ->
  forall x, In x (btv s ++ btv_env sigma) -> {X' & AlphaVar (R1 ++ R2) x X' * (x <> X') * (~ In x (map snd (R1 ++ R2)))}%type.
Proof.
  intros Hconstr x Hin_btvs.
  assert (Hconstr' : ((R1, R2) = R_constr t s sigma X)) by auto.
  unfold R_constr in Hconstr.
  remember (freshen _ _) as frs.
  remember  ((tv t ++ (tv s ++ tv_keys_env sigma) ++ [X]) ++
      map fst
        (map (fun x0 : string => (x0, x0))
        (list_diff string_dec (ftv t)
        (btv s ++ btv_env sigma))) ++
      map snd
        (map (fun x0 : string => (x0, x0))
        (list_diff string_dec (ftv t)
        (btv s ++ btv_env sigma)))) as used.
  assert (H: x
      ∈ (btv s ++
      btv_env sigma)) by auto.
  eapply freshen2_alpha in H as [x' [Ha_x' Hneq]].
  rewrite <- Heqfrs in Ha_x'.
  inversion Hconstr.
  rewrite <- H0 in *.
  rewrite <- H1 in *.
  exists x'.
  split; [split|]; eauto.
  - eapply alphavar_extend_ids_right; eauto.
    eapply R_constr_R2_IdCtx; eauto.
  - rewrite map_app.
    apply not_in_app.
    split.
    + intros Hcontra.
      rewrite Heqfrs in Hcontra.
      apply freshen2__fresh_map_snd in Hcontra.
      rewrite Heqused in Hcontra.
      apply in_app_iff in Hin_btvs.
      destruct Hin_btvs as [Hin_btvs | Hin_btv_sigma].
      * apply not_in_app in Hcontra as [Hcontra _].
        apply not_in_app in Hcontra as [_ Hcontra].
        apply not_in_app in Hcontra as [Hcontra _].
        apply not_in_app in Hcontra as [Hcontra _].
        apply extend_btv_to_tv in Hin_btvs.
        contradiction.
      * apply not_in_app in Hcontra as [Hcontra _].
        apply not_in_app in Hcontra as [_ Hcontra].
        apply not_in_app in Hcontra as [Hcontra _].
        apply not_in_app in Hcontra as [_ Hcontra].
        apply btv_env_extends_to_tv_env in Hin_btv_sigma.
        contradiction.
    + intros Hcontra.
      rewrite H1 in Hcontra.
      apply in_map_iff in Hcontra.
      destruct Hcontra as [x'' [Hx''_eq H_in_map]].
      destruct x'' as [x''0 x''1].
      simpl in Hx''_eq.
      rewrite <- Hx''_eq in *.


      assert (x''0 = x''1).
      { apply in_id_map_then_id in H_in_map; auto. }
      rewrite <- H in *.
      apply in_id_map_then_in_generator in H_in_map.
      eapply list_diff_not with (l1 := (ftv t)) in Hin_btvs.
      contradiction.
Qed.

Lemma R_constr_freshen_helper {t s sigma X R1 R2} :
  (R1, R2) = R_constr t s sigma X ->
  forall x, In x (map fst R1) -> sum (In x (btv s)) (In x (btv_env sigma)).
Proof.
  intros Hconstr x Hin.
  unfold R_constr in Hconstr.
  inversion Hconstr. clear H1 Hconstr.
  remember ((tv t ++
        tv s ++ tv_keys_env sigma) ++
        map fst
          (map
          (fun x0 : string =>
        (x0, x0))
          (list_diff string_dec
          (ftv t)
          (btv s ++ btv_env sigma))) ++
        map snd
          (map
          (fun x0 : string =>
        (x0, x0))
          (list_diff string_dec
          (ftv t)
          (btv s ++ btv_env sigma)))) as used.
  clear Heqused.
  subst.
  apply in_freshen2_then_in_generator in Hin.
  apply in_prop_to_set in Hin.
  apply in_app_or_set in Hin as [Hin | Hin].
  + left.
    apply in_set_to_prop. auto.
  + right.
    apply in_set_to_prop. auto.
Qed.

Lemma R_constr_freshen_fresh_over_sigma {t s sigma X R1 R2} :
  (R1, R2) = R_constr t s sigma X ->
  forall x, In x (map snd R1) -> (~ In x (ftv_keys_env sigma)).
Proof.
  intros Hconstr x Hin.
  unfold R_constr in Hconstr.
  inversion Hconstr. clear H1 Hconstr.
  subst.
  apply freshen2__fresh_map_snd in Hin.
  intros Hcontra.
  apply ftv_keys_env_extends_to_tv_env in Hcontra.
  apply not_in_app in Hin as [Hin _].
  apply not_in_app in Hin as [_ Hin].
  apply not_in_app in Hin as [Hin _].
  apply not_in_app in Hin as [_ Hin].
  contradiction.
Qed.



Definition t_constr (t : term) (s : term) (sigma : list (string * term)) (X : string) : prod term (list (string * string)) :=
  let tvs := tv s ++ tv_keys_env sigma in
  let tv_t := tv t in
  let used := tv_t ++ tvs ++ [X] in
  let (R1, R2) := R_constr t s sigma X in
  (snd (to_GU_ used (R1 ++ R2) t), R1 ++ R2).

Lemma t_constr__GU {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  GU t'.
Proof.
  intros.
  unfold t_constr in H.
  remember (R_constr t s sigma X) as p.
  destruct p as [R1 R2].
  inversion H.
  eapply to_GU__GU_; eauto.
  - intros.
    unfold R_constr in Heqp.
    destruct (in_dec string_dec x (btv s ++ btv_env sigma)).
    + inversion Heqp.
      rewrite <- H4.
      rewrite <- H5.

      (* eapply map_pair_helper in i. *)
      eapply in_generator_then_in_freshen2 in i.
      rewrite map_app. apply in_app_iff. left. rewrite H4. auto.
      unfold freshen in Heqp.
      eauto.



    + inversion Heqp.
      rewrite map_app. apply in_app_iff. right.
      apply in_map_iff.
      exists (x, x); intuition.
      apply id_map_helper.
      apply list_diff_helper; eauto.
  - intros.
    apply in_app_iff.
    left.
    auto.
Qed.

(* R is constructed so that all x in ftv t are either in R1 or R2*)
Lemma R_constr_contains_all_t_ftvs {t s sigma X R1 R2} :
  (R1, R2) = R_constr t s sigma X ->
  forall x, In x (ftv t) -> In x (map fst (R1 ++ R2)).
Proof.
  intros Hconstr.
  intros x Hftv.
  unfold R_constr in Hconstr.
  remember (((tv t ++ tv s ++ tv_keys_env sigma) ++
  map fst
    (map (fun x0 : string => (x0, x0))
    (list_diff string_dec (ftv t)
    (btv s ++ btv_env sigma))) ++
  map snd
    (map (fun x0 : string => (x0, x0))
  (list_diff string_dec (ftv t)
  (btv s ++ btv_env sigma))))) as used. clear Heqused.
  destruct (in_dec string_dec x (btv s ++ btv_env sigma)).
  + rewrite map_app.
    apply in_app_iff. left.
    eapply in_generator_then_in_freshen2 in i.
    inversion Hconstr.
    subst.
    eauto.
  + rewrite map_app.
    apply in_app_iff. right.
    inversion Hconstr.
    clear H0 Hconstr.
    subst.
    assert (In x  (list_diff string_dec (ftv t) (btv s ++ btv_env sigma))).
    {
      apply list_diff_helper.
      auto. auto.
    }
    apply in_map_iff.
    exists ((x, x)); split; auto.
    apply id_map_helper; auto.
Qed.

Lemma t_constr__a_t {t t' R s sigma X }:
  (t', R) = t_constr t s sigma X ->
  Alpha R t t'.
Proof.
  intros.
  unfold t_constr in H.
  remember (tv t ++ tv s ++ tv_keys_env sigma) as used.
  remember (R_constr t s sigma X) as R'.
  destruct R' as [R1 R2].
  inv H.
  apply to_GU__alpha_'.
  - remember (map (fun x : string => (x, x))
      (list_diff string_dec (ftv t)
      (btv s ++ btv_env sigma))) as Rid.
    unfold R_constr in HeqR'.
    inv HeqR'.
    intros.
    eapply R_Well_formedFreshMultiple; auto.
    eapply IdCtx__R_Well_formed.
    apply map_creates_IdCtx.
  - intros.
    remember HeqR' as HeqR''.
    unfold R_constr in HeqR'.
    eapply @R_constr_contains_all_t_ftvs with (R1 := R1) (R2 := R2) in H.
    apply lookup_none_then_no_key in H0.
    contradiction H0; eauto. eauto.
  - intros.
    subst.
    intuition.
Qed.



Lemma R_constr__a_s {R1 R2 t s sigma X} :
  GU s ->
  BU sigma s ->
  (R1, R2) = R_constr t s sigma X ->
  Alpha (R1 ++ R2) s s.
Proof.
  intros HGU H H0.
  apply alpha_vacuous_R.
  - intros.
    unfold BU in H.
    destruct H as [ BU1 _].
    intros Hcontra.
    remember Hcontra as Hcontra2; clear HeqHcontra2.
    apply extend_ftv_to_tv in Hcontra.
    apply BU1 in Hcontra; auto.
    unfold R_constr in H0.
    inv H0.
    apply in_freshen2_then_in_generator in H1.
    apply in_app_or in H1.
    destruct H1.
    * apply gu_ftv_then_no_btv in H. contradiction. auto. auto.
    * auto.
   - (* x' is specifically in R1, which only contains fresh vars (over s)*)
       unfold R_constr in H0.
      inv H0. intros.
      apply freshen2__fresh_map_snd in H0.
      rename H0 into H1.
      apply not_in_app in H1 as [H1 _].
      apply not_in_app in H1 as [_ H1].
      apply not_in_app in H1 as [H1 _].
      apply not_in_app in H1 as [H1 _].
      intros Hcontra.
      apply extend_ftv_to_tv in Hcontra.
      contradiction.
  - apply alpha_extend_ids.
    + unfold R_constr in H0.
      inv H0.
      apply map_creates_IdCtx.
    + eapply alpha_refl. constructor.
Qed.

(* here we probably need BU requirements*)
Lemma t_constr__a_s {t t' R s sigma X} :
  GU s ->
  BU sigma s ->
  (t', R) = t_constr t s sigma X ->
  Alpha R s s.
Proof.
  intros.
  unfold t_constr in H1.
  remember (R_constr t s sigma X) as p.
  destruct p as [R1 R2].
  inversion H1.
  eapply R_constr__a_s; eauto.
Qed.

Lemma R_constr__a_sigma {R1 R2 t s sigma X} :
  BU sigma s ->
  NC s sigma ->
  (R1, R2) = R_constr t s sigma X ->
  AlphaSubs (R1 ++ R2) sigma sigma.
Proof.
  intros HBU Hnc HReq.
  destruct HBU as [ BU1 BU2].
  apply AlphaSubs_sub_extend_ids_right.
  + eapply R_constr_R2_IdCtx; eauto.
  + apply AlphaSubs_vacuous_R.
    * intros.
      apply R_constr_freshen_helper with (x := x) in HReq; auto.
      destruct HReq as [H01 | H02]; auto.
      eapply nc_ftv_env in Hnc; eauto.
    * intros.
      apply R_constr_freshen_fresh_over_sigma with (x := x') in HReq; auto.
    * apply AlphaSubs_R_nil.
Qed.

Lemma t_constr__a_sigma {t t' R s sigma X} :
  BU sigma s ->
  NC s sigma ->
  (t', R) = t_constr t s sigma X ->
  AlphaSubs R sigma sigma.
Proof.
  unfold t_constr.
  destruct (R_constr t s sigma X) as [R1 R2] eqn:Rconstr.
  intros HBU Hnc Hconstr.
  inversion Hconstr. clear H0. clear Hconstr.
  eapply R_constr__a_sigma; eauto.
Qed.

Lemma t_constr__fresh_X_btv_t' {t t' R s sigma X} :
  (t', R) = t_constr t s sigma X ->
  ~ In X (btv t').
Proof.
  intros Hconstr Hbtv_t'.
  unfold t_constr in Hconstr.
  inversion Hconstr.
  clear H1 Hconstr.
  remember ((tv t ++ (tv s ++ tv_keys_env sigma) ++ [X])) as used.
  remember ((freshen _ _) ++ _) as binders; clear Heqbinders.
  remember ((to_GU_ used binders t)) as p.
  destruct p as [[used' binders'] t''].
  subst.
  eapply no_binder_used with (used := tv t ++ tv s ++ tv_keys_env sigma ++ [X]) in Hbtv_t'; eauto.
  - repeat apply not_in_app in Hbtv_t' as [_ Hbtv_t'].
    contradiction Hbtv_t'.
    apply in_eq.
  - repeat rewrite app_assoc in Heqp.
    repeat rewrite app_assoc.
    eauto.
Qed.

Lemma t_constr__BU1 {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv t') -> ~ In x (tv s).
Proof.
  intros Hconstr x Hbtv_t'.
  unfold t_constr in Hconstr.
  inversion Hconstr.
  clear H1 Hconstr.
  remember (tv t ++ (tv s ++ tv_keys_env sigma) ++ [X]) as used.
  remember ((freshen _ _) ++ _) as binders; clear Heqbinders.
  remember ((to_GU_ used binders t)) as p.
  destruct p as [[used' binders'] t''].
  subst.
  eapply no_binder_used with (used := tv t ++ tv s ++ tv_keys_env sigma ++ [X]) in Hbtv_t'; eauto.
  apply not_in_app in Hbtv_t' as [_ Hbtv_t'].
  apply not_in_app in Hbtv_t' as [Hbtv_t' _].
  auto; eauto. subst. eauto. simpl. eauto.
  repeat rewrite app_assoc in Heqp.
  repeat rewrite app_assoc.
  eauto.
Qed.

(* Very similar to above*)
Lemma t_constr__new_btv_not_sigma {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv t') -> ~ In x (ftv_keys_env sigma).
Proof.
  intros Hconstr x Hbtv_t'.
  unfold t_constr in Hconstr.
  inversion Hconstr.
  clear H1 Hconstr.
  remember (tv t ++ (tv s ++ tv_keys_env sigma) ++ [X]) as used.
  remember ((freshen _ _) ++ _) as binders; clear Heqbinders.
  remember ((to_GU_ used binders t)) as p.
  destruct p as [[used' binders'] t''].
  subst.
  eapply no_binder_used with (used := tv t ++ tv s ++ tv_keys_env sigma ++ [X]) in Hbtv_t'; eauto.
  apply not_in_app in Hbtv_t' as [_ Hbtv_t'].
  apply not_in_app in Hbtv_t' as [_ Hbtv_t'].
  apply not_in_app in Hbtv_t' as [Hbtv_t' _].
  auto.
  intros Hcontra.
  apply ftv_keys_env_extends_to_tv_env in Hcontra.
  contradiction.
  repeat rewrite app_assoc.
  repeat rewrite app_assoc in Heqp.
  simpl. eauto.
Qed.

(* Cumbersome, uninsightful helper lemma for reaching a contradiction *)
Lemma ftv_helper_constr {t t' R  X X'} :
  Alpha R t t' ->
  ~ In X (map snd R) ->
  X <> X' ->
  AlphaVar R X X' ->
  ~ In X (btv t') ->
  ~ In X' (btv t') ->
  ~ In X (ftv t').
Proof.
  intros.
  assert (Hbinderchange: {t'' & Alpha R t'' t' * ~ In X (btv t'')}%type).
  {
    exists (to_GU'' X t).
    split.
    - eapply @alpha_trans with (t := t) (R := ctx_id_left R) (R1 := R); eauto with α_eq_db.
      + apply id_left_trans.
      + apply alpha_extend_ids. apply ctx_id_left_is_id. eapply @alpha_sym. constructor. apply to_GU''__alpha.
    - apply to_GU''__btv.
  }
  destruct Hbinderchange as [t'' [Ha_t'' Hbtv_t''] ].
  clear H.
  (* By X not in rhs R, we should then have X in ftv t, but that doesnt work, because we have (X, X')
    I'm sure we must already have lemmas for this kind of contraddiction.
  *)
  generalize dependent t''.
  generalize dependent R.
  induction t'; intros.
  - inversion Ha_t''; subst.

    intros Hcontra.
    inversion Hcontra; eauto. subst. clear Hcontra.
    destr_eqb_eq x X.
    + assert (X = X').
      eapply alphavar_unique_right. eauto. eauto. contradiction.
    + assert (In (x, X) R).
      {
        clear H2.
        induction R.
        - inversion Ha_t''; subst. inversion H7; subst. contradiction.
        - simpl in H0.
          simpl.
          right.
          assert (a <> (x, X)).
          {
            intros Hcontra.
            assert (snd a = X).
            {
              destruct a.
              inversion Hcontra. subst. reflexivity.
            }
            subst.
            intuition.
          }
          eapply IHR.
          + intuition.
          + inversion H7; subst.
            * contradiction.
            * assumption.
          + inversion H7; subst; intuition.
      }
      contradiction H0.
      apply in_map_iff.
      exists (x, X). split; auto.
  - destr_eqb_eq X s.
    + intros Hcontra. simpl in Hcontra. apply in_remove in Hcontra. destruct Hcontra as [_ snots]. contradiction.
    +
      assert (~ In X (ftv t')).
      {
        inversion Ha_t''; subst.
        eapply IHt' with (t'' := s1) (R := ((x, s)::R)); eauto.
        - eapply not_btv_dc_lam; eauto.
        - eapply not_btv_dc_lam; eauto.
        - simpl.
          intuition.
        - constructor; auto.
          + intros Hcontra.
            subst.
            simpl in Hbtv_t''. intuition.
          + intros Hcontra.
            subst.
            simpl in H4. intuition.
        - eapply not_btv_dc_lam; eauto.
      }
      intros Hcontra.
      apply ftv_lam_helper in Hcontra.
      contradiction.
  - inversion Ha_t''; subst.
    unfold ftv. fold ftv.
    apply not_in_app.
    split; eauto.
    + eapply IHt'1; eauto; eapply not_btv_dc_appl; eauto.
    + eapply IHt'2; eauto; eapply not_btv_dc_appr; eauto.
  - intros Hcontra.
    inversion Hcontra.
Qed.

(* Renaming contexts generated by R_constr are well-formed*)
Lemma R_constr_lookup_alpha {R1 R2 t s sigma X} :
  (R1, R2) = R_constr t s sigma X ->
  forall x X', lookup x (R1 ++ R2) = Some X' -> AlphaVar (R1 ++ R2) x X'.
Proof.
  intros Hconstr.
  intros x X' Hlookup.
  assert (Hconstr' : (R1, R2) = R_constr t s sigma X) by auto.
  unfold R_constr in Hconstr.
  remember((tv t ++ tv s ++ tv_keys_env sigma) ++
  map fst
    (map (fun x0 : string => (x0, x0))
    (list_diff string_dec (ftv t)
    (btv s ++ btv_env sigma))) ++
  map snd
    (map (fun x0 : string => (x0, x0))
    (list_diff string_dec (ftv t)
    (btv s ++ btv_env sigma)))) as used.
  apply lookup_app_or_extended in Hlookup as [HinR1 | [ HnotInR1 HinR2] ].
  + assert (AlphaVar R1 x X').
    {
      inversion Hconstr. clear H1 Hconstr. subst.
      apply freshen2_alpha_lookup; auto.
    }
    eapply alphavar_extend_ids_right in H; eauto.
    eapply R_constr_R2_IdCtx in Hconstr'; eauto.
  + remember Hconstr' as Hconstr''. clear HeqHconstr''.
    eapply R_constr_R2_IdCtx in Hconstr'; eauto.
    remember HinR2 as HinR2'. clear HeqHinR2'.
    apply lookup_idctx_refl in HinR2; eauto; subst.
    assert (HX'inftvt: In X' (ftv t)).
    {
      inversion Hconstr.
      clear H0. clear Hconstr Hconstr''.
      apply lookup_then_in_map_fst in HinR2'.
      subst.
      apply in_map_iff in HinR2'.
      destruct HinR2' as [x'' [Heq Hin_map]].
      destruct x'' as [x''0 x''1].
      simpl in Heq.
      subst.
      assert (X' = x''1).
      { apply in_id_map_then_id in Hin_map; subst; auto. }
      subst.
      apply in_id_map_then_in_generator in Hin_map.
      apply list_diff_in_first in Hin_map. auto.
    }
    assert (lookup_r X' R1 = None).
    {
      remember((tv t ++ tv s ++ tv_keys_env sigma) ++
  map fst
    (map (fun x0 : string => (x0, x0))
    (list_diff string_dec (ftv t)
    (btv s ++ btv_env sigma))) ++
  map snd
    (map (fun x0 : string => (x0, x0))
    (list_diff string_dec (ftv t)
    (btv s ++ btv_env sigma)))) as used.
      assert (~ In X' (map snd R1)).
      {
        intros Hcontra.
        inversion Hconstr.
        rewrite H0 in Hcontra.
        eapply freshen2__fresh_map_snd in Hcontra; auto.
        subst.
        apply not_in_app in Hcontra as [Hcontra _].
        apply not_in_app in Hcontra as [Hcontra _].
        apply extend_ftv_to_tv in HX'inftvt.
        contradiction.
      }
      apply not_ex__lookup_r_none. auto.
    }
    destruct (@lookup_none_extend_helper _ R2 _ HnotInR1 H) as [Hlookup Hlookup_r].
    apply lookup_some_then_alphavar; auto.
    * rewrite Hlookup. auto.
    * rewrite Hlookup_r. auto.
      apply lookup_id_then_lookup_r; auto.
Qed.

Lemma t_constr_btv_s_not_ftv_t' {t' R t s sigma X} :
  (t', R) = t_constr t s sigma X ->
  forall x, In x (btv s ++ btv_env sigma) -> ~ In x (ftv t').
Proof.
  intros.

  assert ({X' & (AlphaVar R x X') * (x <> X') * (~ In x (map snd R)) }%type) as [X' [ [HAx Hneq] HnotsndR]].
  {
    unfold t_constr in H.
    remember (R_constr t s sigma X) as p.
    destruct p as [R1 R2].
    inversion H.
    eapply R_constr__BU3; eauto.
  }

  eapply ftv_helper_constr.
  - eapply t_constr__a_t; eauto.
  - auto.
  - eauto.
  - eauto.
  -
    intros Hcontra. simpl in H.
    unfold t_constr in H.
    remember (R_constr t s sigma X) as p.
    destruct p as [R1 R2].
    inversion H.
    remember ((to_GU_ (tv t ++ (tv s ++ tv_keys_env sigma) ++ [X])
  (R1 ++ R2) t)) as q.
    destruct q as [ [used' binders'] t''].
    simpl in H2. rewrite <- H2 in *.
    eapply no_btv_in_binders_fst with (used := (tv t ++ (tv s ++ tv_keys_env sigma) ++ [X]))
      (binders' := binders')
      (used' := used')

      (binders := R1 ++ R2) in Hcontra; eauto.
    + rewrite <- H3 in Hcontra.
      subst.
      apply alphavar_models_lookup in HAx.
      destruct HAx as [HAx1 | HAx2].
      * destruct HAx1 as [HAx1].
        apply lookup_then_in_map_fst in HAx1. contradiction.
      * destruct HAx2 as [[_ _] HAx2].
        contradiction.

  - intros Hcontra. simpl in H.
    unfold t_constr in H.
    remember (R_constr t s sigma X) as p.
    destruct p as [R1 R2].
    inversion H.
    remember ((to_GU_ (tv t ++ (tv s ++ tv_keys_env sigma) ++ [X])
  (R1 ++ R2) t)) as q.
    destruct q as [ [used' binders'] t''].
    simpl in H2. rewrite <- H2 in *.
    eapply no_btv_in_binders with (binders := R1 ++ R2) in Hcontra; eauto.
    rewrite <- H3 in Hcontra.
    subst.
    apply alphavar_models_lookup in HAx.
    destruct HAx as [HAx1 | HAx2].
    +
      destruct HAx1 as [HAx1].
      apply lookup_r_then_in_map_snd in e. contradiction.
    + destruct HAx2 as [[_ _] HAx2].
      contradiction.
Qed.


Lemma t_constr__nc_s {t t' R s sigma X} :
  ~ In X (btv s) ->  (* We dont have control over s or X in construction*)
  NC s sigma ->
  (t', R) = t_constr t s sigma X ->
  NC s ((X, t')::sigma).
Proof.
  intros.
  constructor; auto.
  intros.
  split.
  - intros contra.
    inversion H0.
    subst.
    apply H.
    assumption.
    subst. contradiction.
  - eapply t_constr_btv_s_not_ftv_t'. eauto. auto.
    apply in_app_iff. left. auto.
Qed.

Lemma t_constr__nc_subs {t t' R s sigma X} :
  ~ In X (btv s) -> (* We dont have control over s or X in construction*)
  ~ In X (btv_env sigma) -> (* we do not have control over sigma*)
  (t', R) = t_constr t s sigma X ->
  NC (psubs sigma s) ((X, t')::nil).
Proof.
  intros.
  constructor.
  - constructor.
  - intros.
    split.
    + intros Hcontra.
      subst.
      apply in_btv_psubs_then_in_constituents in H2.
      destruct H2 as [Hin_s | [t0 [Ht0_sigma Hin_t0]]].
      * contradiction.
      * contradiction H0.
        {
        clear H1. clear H0. clear H.
        induction sigma.
        - inversion Ht0_sigma.
        - destruct a as [ax a_t].
          simpl.
          rewrite map_cons in Ht0_sigma.
          destruct Ht0_sigma.
          + simpl in H. subst.
            apply in_app_iff.
            left. auto.
          + apply in_app_iff.
            right.
            apply IHsigma.
            auto.
       }
    + apply in_btv_psubs_then_in_constituents in H2.
      destruct H2 as [Hin_s | [t0 [Ht0_sigma Hin_t0]]].
      * apply t_constr_btv_s_not_ftv_t' with (x := y) in H1. auto. auto.
        apply in_app_iff. left. auto.
      * apply (btv_env_helper Hin_t0) in Ht0_sigma.
        apply t_constr_btv_s_not_ftv_t' with (x := y) in H1. auto. auto.
        apply in_app_iff. right. auto.
Qed.

Opaque t_constr.


(*  to_GU' with more subsitutions. *)

Definition s_constr (s : term) (sigma : list (string * term)) : term :=
  (* By adding tvs in X and T, no binders in the resulting term can be equal to tvs in X and T. We do tv, because mostly tv is easier to reason about than ftv*)
  let tvs := tv_keys_env sigma ++ tv s in
  snd (to_GU_ tvs (map (fun x => (x, x)) tvs) s).

Lemma s_constr__a_s {s s' sigma} :
  s' = s_constr s sigma ->
  Alpha [] s s'.
Proof.
  intros Heqs'.
  unfold s_constr in Heqs'.
  remember (map (fun x => (x, x)) (_)) as R.
  rewrite Heqs'.
  assert (Alpha R s s').
  {
    rewrite Heqs'.
    eapply to_GU__alpha_'.
    - intros.
      eapply lookup_some_IdCtx_then_alphavar; eauto.
      rewrite HeqR.
      apply map_creates_IdCtx.
    - intros.
      apply alphavar_refl; auto.
      subst. apply map_creates_IdCtx.
    - intros.
      intuition.
  }
  eapply alpha_weaken_ids with (idCtx := R).
  - subst.
    clear H.
    induction (tv_keys_env sigma ++ tv s); simpl; constructor; auto.
  - subst. auto.
Qed.

Lemma s_constr__gu {s s' sigma} :
  s' = s_constr s sigma ->
  GU s'.
Proof.
  intros Heqs'.
  unfold s_constr in Heqs'.
  subst.
  eapply to_GU__GU_; auto.
  - intros.
    assert (In x (tv_keys_env sigma ++ tv s)).
    {
      apply extend_ftv_to_tv in H.
      auto.
      intuition.
    }
    apply in_map_iff.
    exists (x, x); intuition.
    apply id_map_helper. auto.
  - intros. (* x in tv s, then also x in supserset of tv s*)
    intuition.
Qed.

Lemma s_constr__nc_s {s s' sigma} :
  s' = s_constr s sigma ->
  NC s' sigma.
Proof.
  intros Heqs'; subst.
  unfold s_constr.
  remember (to_GU_ (_) (map (fun x => (x, x)) (_)) s) as p.
  destruct p as [ [used' binders'] s'2].
  subst.
  apply nc_helper.
  intros.

  apply no_binder_used with (x := x) in Heqp; auto.
  intros Hcontra. apply extend_ftv_keys_env_to_tv in Hcontra.
  apply not_in_app in Heqp.
  destruct Heqp as [Heqp _].
  contradiction.
Qed.


Opaque to_GU'.
Opaque to_GU''.

Lemma BU_lam2 {B x A s sigma t t' R} :
  GU (@tmabs B x A s) ->
  (t', R) = t_constr t s sigma x ->

  BU sigma (@tmabs B x A s) -> BU ((x, t')::sigma) s.
Proof.
  intros HGU Htconstr HBU.
  unfold BU in HBU; destruct HBU as [ BU1 BU2].
  split; intros.
  - simpl in H.
    apply in_app_iff in H as [Hinbtvt' | Hinbtvsigma].
    + eapply t_constr__BU1 in Htconstr; eauto.
    + apply BU1 in Hinbtvsigma. apply not_tv_dc_lam in Hinbtvsigma; auto.
  - simpl in H.
    apply in_app_iff in H as [Hinbtvt' | Hinbtvsigma].
    +
      simpl.
      apply de_morgan2.
      split.
      * intros Hcontra; subst.
        eapply t_constr__fresh_X_btv_t'; eauto.
      * apply not_in_app; split.
        -- apply t_constr__GU in Htconstr.
           intros Hcontra.
           apply gu_ftv_then_no_btv in Hcontra; auto.
        -- eapply t_constr__new_btv_not_sigma; eauto.
    + simpl.
      apply de_morgan2.
      split.
      * intros Hcontra; subst.
        apply BU1 in Hinbtvsigma.
        simpl in Hinbtvsigma.
        intuition.
      * apply not_in_app; split.
        -- eapply t_constr_btv_s_not_ftv_t'; eauto.
           apply in_app_iff.
           right. auto.
        -- eapply BU2. eauto.
Qed.

Create HintDb s_constr_db.
Hint Resolve s_constr__a_s : s_constr_db.
Hint Resolve s_constr__gu : s_constr_db.
Hint Resolve s_constr__nc_s : s_constr_db.


Create HintDb gu_nc_db.
Hint Resolve gu_app_r : gu_nc_db.
Hint Resolve gu_app_l : gu_nc_db.
Hint Resolve gu_lam : gu_nc_db.
Hint Resolve nc_app_r : gu_nc_db.
Hint Resolve nc_app_l : gu_nc_db.
Hint Resolve nc_lam : gu_nc_db.
Hint Resolve gu_applam_to_nc : gu_nc_db.
Hint Resolve nc_ftv_env : gu_nc_db.


Create HintDb bu_db.
Hint Resolve BU_appr : bu_db.
Hint Resolve BU_appl : bu_db.
Hint Resolve BU_lam_id : bu_db.

Create HintDb a_constr_db.
Hint Resolve a_constr__s_alpha a_constr__t_alpha : a_constr_db.
