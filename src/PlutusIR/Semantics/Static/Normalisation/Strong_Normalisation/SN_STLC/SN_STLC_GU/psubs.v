Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From PlutusCert Require Import STLC Util.List util variables.

Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.

(* Parallel substitutions and ParSeq, which says we can treat a parallel substitution as a sequential one*)

(* parallel subs *)
Fixpoint psubs (sigma : list (string * term)) (T : term) : term :=
  match T with
  | tmvar x => match lookup x sigma with
              | Some t => t
              | None => tmvar x
              end
  | @tmlam B x A s => @tmlam B x A (psubs sigma s) (* We do not look at binders, see NC x <> y property*)
  | @tmapp B s t => @tmapp B (psubs sigma s) (psubs sigma t)
  | tmbuiltin d => tmbuiltin d
  end.

Lemma psubs_nil s : psubs nil s = s.
Proof.
  induction s; auto.
  - simpl. f_equal. auto.
  - simpl. f_equal; auto.
Qed.

Lemma psubs_extend_new (x : string) s δ:
  ~ In x (map fst δ) -> psubs δ s = psubs ((x, tmvar x)::δ) s.
Proof.
  intros HnotIn.
  induction s; auto.
  - simpl. destr_eqb_eq x s.
    + rewrite not_in__lookup; auto.
    + reflexivity.
  - simpl. f_equal; auto.
  - simpl. f_equal; auto.
Qed.

Lemma in_btv_psubs_then_in_constituents2 x sigma s :
  In x (btv (psubs sigma s)) -> In x (btv s) \/ (In x (btv_env sigma)).
Proof.
  intros Hbtv_psubs.
  induction s.
  - simpl in Hbtv_psubs.
    destruct (lookup s sigma) eqn:Hl.
    + right. eapply btv_env_lookup__in; eauto.
    + left. auto.
  - destr_eqb_eq x s.
    + left. simpl. left. auto.
    + simpl in Hbtv_psubs.
      destruct Hbtv_psubs as [Heq | Hbtv_psubs].
      * symmetry in Heq. contradiction.
      * apply IHs in Hbtv_psubs as [Hbtv_s0 | Hbtv_sigma].
        -- left. simpl. right. auto.
        -- right. auto.
  - simpl in Hbtv_psubs.
    apply in_app_or in Hbtv_psubs as [Hbtv_left | Hbtv_right].
    + apply IHs1 in Hbtv_left as [Hbtv_s1 | Hbtv_sigma].
      * left. simpl. apply in_app_iff. left. auto.
      * right. auto.
    + apply IHs2 in Hbtv_right as [Hbtv_s2 | Hbtv_sigma].
      * left. simpl. apply in_app_iff. right. auto.
      * right. auto.
  - simpl in Hbtv_psubs.
    contradiction.
Qed.

(* This seems like an unnecessary indirection*)
Lemma in_btv_psubs_then_in_constituents x sigma s :
  In x (btv (psubs sigma s)) -> In x (btv s) \/ (exists t, In t (map snd sigma) /\ In x (btv t)).
Proof.
  intros Hbtv_psubs.
  apply in_btv_psubs_then_in_constituents2 in Hbtv_psubs.
  destruct Hbtv_psubs as [Hbtv_s | Hbtv_sigma].
  - left. auto.
  - right. apply In_btv_env__exists; auto.
Qed.

Lemma psubs_does_not_create_btv sigma x s :
  ~ In x (btv s) -> ~ In x (btv_env sigma) -> ~ In x (btv (psubs sigma s)).
Proof.
  intros Hbtv_s Hbtv_sigma.
  intros Hcontra.
  apply in_btv_psubs_then_in_constituents2 in Hcontra.
  destruct Hcontra; auto.
Qed.

Lemma not_in_constituents_then_not_in_ftv_psubs x σ s :
  ~ In x (ftv s) -> ~ In x (flat_map ftv (map snd σ)) -> ~ In x (ftv (psubs σ s)).
Proof.
  intros HNIn_s HNIn_σ.
  induction s.
  - apply not_in_ftv_var in HNIn_s.
    simpl.
    destruct (lookup s σ) eqn:Hl.
    + eapply ftv_env_helper; eauto.
    + simpl. apply de_morgan2. split; auto.
  - simpl.
    destr_eqb_eq x s.
    + apply not_in_remove. right. auto.
    + apply not_in_remove. left.
      apply ftv_lam_negative in HNIn_s; auto.
  - simpl.
    simpl in HNIn_s.
    apply not_in_app in HNIn_s as [HNIn_s1 HNIn_s2].
    apply not_in_app. split.
    + apply IHs1; auto.
    + apply IHs2; auto.
  - auto.
Qed.



Lemma psubs_does_not_create_ftv sigma x s :
  ~ In x (ftv s) -> ~ In x (ftv_keys_env sigma) -> ~ In x (ftv (psubs sigma s)).
Proof.
  intros Hftv_s Hftv_sigma.
  induction s.
  - apply not_in_ftv_var in Hftv_s.
    induction sigma.
    + simpl. unfold not. intros Hcontra.
      destruct Hcontra.
      * symmetry in H. contradiction.
      * contradiction.
    + simpl. destruct a as [y t].
      simpl in Hftv_sigma.
      apply de_morgan2 in Hftv_sigma.
      destruct Hftv_sigma as [ _ Hftv_sigma ].
      apply not_in_app in Hftv_sigma.
      destruct Hftv_sigma as [Hftv_sigma].
      specialize (IHsigma H).
      destr_eqb_eq x y.
      * rewrite <- String.eqb_neq in Hftv_s. rewrite Hftv_s. simpl in IHsigma.
        assumption.
      * 
        (* This should be its own lemma, since it is about sub now, not subs*)
        {
        destr_eqb_eq y s; auto.

        }
        


  -
    destr_eqb_eq x s.
    + apply ftv_lam_no_binder.
    + intros Hcontra.
      apply ftv_lam_helper in Hcontra.
      apply ftv_lam_negative in Hftv_s.
      specialize (IHs Hftv_s).
      contradiction. auto.
  - 
    simpl.
    apply not_in_app. split.
    + apply IHs1. auto. eapply not_ftv_app_not_left; eauto.
    + apply IHs2. auto; eapply not_ftv_app_not_right; eauto.
  - auto.
Qed.

Lemma psubs_vac_var sigma x :
  ~ In x (map fst sigma) ->
  psubs sigma (tmvar x) = (tmvar x).
Proof.
  intros.
  induction sigma.
  - reflexivity.
  - destruct a as [a1 a2].
    simpl in H.
    apply de_morgan2 in H.
    destruct H as [H1 H2].
    specialize (IHsigma H2).
    simpl.

    
    rewrite <- String.eqb_neq in H1.
    simpl.
    rewrite H1.
    unfold psubs in IHsigma.
    assumption.
Qed.

Lemma psubs_vac X T t :
  ~ In X (tv t) ->
  psubs [(X, T)] t = t.
Proof.
  induction t; intros.
  - simpl.
    unfold tv in H.
    apply not_in_cons in H as [H _].
    apply String.eqb_neq in H.
    rewrite H.
    reflexivity.
  - simpl.
    simpl in H.
    apply de_morgan2 in H as [_ H].
    apply IHt in H.
    rewrite H.
    reflexivity.
  - simpl.
    simpl in H.
    apply not_in_app in H as [H1 H2].
    apply IHt1 in H1.
    apply IHt2 in H2.
    rewrite H1.
    rewrite H2.
    reflexivity.
  - simpl. reflexivity.
Qed.

(* substitutions do not introduce new free variables 
*)
Lemma psubs_no_ftv x sigma y:
  ~ In x (ftv_keys_env sigma) -> x <> y -> ~ In x (ftv (psubs sigma (tmvar y))).
Proof.
  intros.
  unfold psubs.
  destruct (lookup y sigma) eqn:lookup_y_sigma.
  - eapply ftv_keys_env__no_values in H; eauto.
    apply lookup_In in lookup_y_sigma.
    apply in_map_iff. exists (y, t). simpl. auto.
  - simpl. intuition.
Qed.


(**************** Remove ids, necessary for ParSeq*)

Fixpoint remove_ids (sigma : list (string * term)) : list (string * term) :=
  match sigma with 
  | nil => nil
  | (x, tmvar y)::sigma' => if String.eqb x y then remove_ids sigma' else (x, tmvar y)::(remove_ids sigma')
  | (x, t)::sigma' => (x, t)::(remove_ids sigma')
  end.


Lemma remove_ids_helper sigma s t :
  In (s, t) sigma -> ~ In s (map fst (remove_ids sigma)) -> t = tmvar s.
Proof.
  intros.
  induction sigma.
  - inversion H.
  - destruct a as [a1 a2].
    inversion H.
    + inversion H1; subst; clear H1.
      simpl in H0.
      induction t; try solve [simpl in H0; apply de_morgan2 in H0 as [H0 _]; contradiction].
      destr_eqb_eq s s0.
      -- reflexivity.
      -- simpl in H0. apply de_morgan2 in H0 as [H0 _].
         contradiction.
    + eapply IHsigma; eauto.
      simpl in H0.
      induction a2; try solve [simpl in H0; apply de_morgan2 in H0 as [_ H0]; auto ].
      destr_eqb_eq a1 s0; auto.
      apply de_morgan2 in H0 as [H0_]; auto.      
Qed.


Lemma remove_ids_helper4 sigma X a1 t:
  ~ In X (ftv_keys_env (remove_ids ((a1, t)::sigma))) -> ~ In X (ftv_keys_env (remove_ids sigma)).
Proof.
  intros.
  simpl in H.
  induction t; simpl in H; intuition.
  destr_eqb_eq a1 s; auto.
  apply not_in_cons in H; auto with *.
Qed.

Lemma remove_ids_helper3 sigma X a1 t:
  ~ In X (ftv_keys_env (remove_ids ((a1, t)::sigma))) -> (t = tmvar X /\ a1 = X) \/ ~ In X (ftv t).
Proof.
  intros.
  induction sigma.
  - induction t.
    + unfold remove_ids in H.
      destr_eqb_eq a1 s.
      destr_eqb_eq s X.
      left. auto.
      right. simpl. intuition.
      destr_eqb_eq X s. 
      simpl in H. intuition.
      right. simpl. intuition.
    + right.
      simpl.
      simpl in H.
      apply de_morgan2 in H as [H H1].
      rewrite app_nil_r in H1.
      assumption.
    + right.
      simpl in H.
      apply de_morgan2 in H as [H H1].
      simpl.
      rewrite app_nil_r in H1.
      assumption.
    + right.
      simpl. auto.
  - eapply IHsigma.
    + simpl.
      induction t.
      * destr_eqb_eq a1 s.
        -- apply remove_ids_helper4 in H.
          destruct a as [a1 a2].
          apply remove_ids_helper4 in H. 
          auto.
        -- simpl.
            apply de_morgan2.
            split.
            intros Hcontra.
            subst.
            simpl remove_ids in H.
            destr_eqb_eq X s; try contradiction.
            simpl in H. intuition.
            apply de_morgan2.
            split.
            intros Hcontra.
            subst.
            simpl remove_ids in H.
            destr_eqb_eq a1 X; try contradiction.
            simpl in H. intuition.
            apply remove_ids_helper4 in H.
            destruct a as [a1' a2].
            apply remove_ids_helper4 in H.
            assumption.
        * remember H as H'. clear HeqH'.
           simpl in H.
          apply de_morgan2 in H as [H H1].
          simpl.
          apply de_morgan2.
          split.
          auto.
          apply not_in_app; split.
          apply not_in_app in H1 as [H1 _]; auto.
          apply remove_ids_helper4 in H'.
          destruct a as [a1' a2].
          apply remove_ids_helper4 in H'.
          assumption.
        * remember H as H'. clear HeqH'.
           simpl in H.
          apply de_morgan2 in H as [H H1].
          simpl.
          apply de_morgan2.
          split.
          auto.
          apply not_in_app; split.
          apply not_in_app in H1 as [H1 _]; auto.
          apply remove_ids_helper4 in H'.
          destruct a as [a1' a2].
          apply remove_ids_helper4 in H'.
          assumption.
        * simpl.
          apply de_morgan2.
          split.
          intros Hcontra.
          subst.
          simpl in H. intuition.
          apply remove_ids_helper4 in H.
          destruct a as [a1' a2].
          apply remove_ids_helper4 in H.
          assumption.
Qed.


Lemma ftv_keys_env_sigma_remove x sigma :
  In x (ftv_keys_env (remove_ids sigma)) -> In x (ftv_keys_env sigma).
Proof.
  intros.
  induction sigma.
  - simpl in H. contradiction.
  - simpl in H.
    destruct a as [y t].
    simpl in H.
    destruct t.
    + destr_eqb_eq y s.
      * simpl. right. right. apply IHsigma. auto.
      * destruct H.
        -- simpl. left. auto.
        -- simpl. apply in_app_or in H. destruct H.
          ++ simpl. right. left. auto. apply ftv_var in H. auto.
          ++ simpl. right. right. apply IHsigma. auto.
    + destruct H.
      * subst. simpl. left. reflexivity.
      * apply in_app_or in H.
        destruct H.
        -- simpl. right. apply in_or_app. left. assumption.
        -- simpl. right. apply in_or_app. right. apply IHsigma. auto.
    + destruct H.
      * subst. simpl. left. reflexivity.
      * apply in_app_or in H.
        destruct H.
        -- simpl. right. apply in_or_app. left. assumption.
        -- simpl. right. apply in_or_app. right. apply IHsigma. auto.
    + simpl in H.
      destruct H.
      simpl. left. auto.
      simpl. right. apply IHsigma. auto.
Qed.


(***** ParSeq *)



Inductive ParSeq : list (string * term) -> Set :=
| ParSeq_nil : ParSeq []
| ParSeq_cons x t sigma :
    ParSeq sigma -> 
    (* ~ In x (List.concat (map ftv (map snd sigma))) ->  *)

    (* we do remove_ids, since identity substitutions have no effect 
      (and can thus not break par <=> seq)
      hence if we have x => t, and there was an x => x before, then in tha par case
        this is ignored of course,
        and in the seq case, it is applied, but since it is id, it is like not applying.
      *)
    ~ In x (ftv_keys_env (remove_ids sigma)) -> (* UPDATE Feb 27: we cannot have that x is a key in sigma either
      look e.g. at (x, a)::(x, b). As a sequential sub applied to tmvar x, we get b.
                                    As a parallel, we get a.

    *)
    ~ In x (btv_env sigma) -> (* Update Mar 6: OTHERWISE WE CAN GET CAPTURE IN sigma *)
    ParSeq ((x, t)::sigma).
(* This says that one subsitutions does not have effect on the next one
  In other word, no substiutions chains, where x -> t, and then t -> y, etc.

  This also means that if we define lookup as right oriented, that
    lookup_left x sigma = Some T   -> subs sigma (tmvar x) = T
*)

(* Say (x, t)::sig2, and sigma =sig1++sig2
  Say y in ftv t. Then we have a problem if y in lhs sig1.
  But, this cannot happen by blabla.

  Also, we will use right-biased lookup.

  TODO: Do we need to enforce that we cannot have twice the same key? 
  For now: righthanded lookup will do the job
*)
Lemma parseq_smaller {sigma x t} :
  ParSeq ((x, t)::sigma) -> ParSeq sigma.
Proof.
  now inversion 1.
Qed.

Lemma single_parseq x t : ParSeq [(x, t)].
Proof.
  now repeat constructor.
Qed.


Lemma psubs_unfold sigma X T s :
  ParSeq ((X, T)::sigma) -> psubs ((X, T)::sigma) s = psubs [(X, T)] (psubs sigma s).
Proof.
  intros.
  induction s.
  - simpl. 
    destr_eqb_eq X s.
    + inversion H; subst.
      destruct (lookup s sigma) eqn:Hl.
      * assert (t = tmvar s).
        {
          apply ftv_keys_env__no_keys in H4.
          apply lookup_In in Hl.
          eapply remove_ids_helper; eauto.
        }
        subst.
        simpl.
        rewrite String.eqb_refl.
        reflexivity.
      * simpl. rewrite String.eqb_refl. reflexivity.
    + destruct (lookup s sigma) eqn:Hl.
      * inversion H; subst.
        assert (~ In X (tv t)).
        {
          clear H H4.
          induction sigma.
          - inversion Hl.
          - destruct a as [a1 a2].
            destr_eqb_eq s a1.
            + rewrite lookup_eq in Hl.
              inversion Hl; subst; clear Hl.
              
              simpl in H6.
              apply remove_ids_helper3 in H5.
              destruct H5 as [[H5 H7] | H5].
              * subst. contradiction.
              * apply not_in_app in H6 as [H6 _].
                apply not_ftv_btv_then_not_tv; auto.
            + eapply IHsigma; eauto.
              * simpl in Hl.
                rewrite <- String.eqb_neq in H.
                rewrite String.eqb_sym in H.
                rewrite H in Hl; auto.
              * apply remove_ids_helper4 in H5; auto.
              * simpl in H6. apply not_in_app in H6 as [_ H6].
                assumption.
        }

        symmetry.
        apply psubs_vac; auto.
      * simpl. rewrite <- String.eqb_neq in H0. rewrite H0.
        reflexivity.
  - simpl. f_equal. eauto.
  - simpl. f_equal; eauto.
  - simpl. reflexivity.
Qed.
