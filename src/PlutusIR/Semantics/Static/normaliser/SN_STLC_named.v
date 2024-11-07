From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import List AutosubstSsr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import STLC_named STLC_named_typing ARS.
From PlutusCert Require Import alpha.


(* Contextual alpha equivalence: kinding contexts that match alpha contexts*)
Inductive CAlpha : list (string * string) -> list (string * type) -> list (string * type) -> Prop :=
  | calpha_nil : CAlpha [] [] []
  | calpha_cons sigma Gamma Gamma' x y K :
    CAlpha sigma Gamma Gamma' ->
    CAlpha ((x, y)::sigma) ((x, K)::Gamma) ((y, K)::Gamma').

(* Exercise and possibly useful *)
Lemma alpha_preserves_typing sigma s t A Gamma Gamma' :
  Alpha sigma s t -> CAlpha sigma Gamma Gamma' -> Gamma |-* s : A -> Gamma' |-* t : A.
Proof.
  intros HAlpha Htype.
  generalize dependent A.
  generalize dependent Gamma.
  generalize dependent Gamma'.
  induction HAlpha.
  - intros Gamma' Gamma HCAlpha A HType.
    inversion HType.
    apply K_Var; subst...
    generalize dependent Gamma.
    generalize dependent Gamma'.
    induction H; subst...
    + intros.
      inversion HCAlpha; subst...
      inversion H2.
    + intros Gamma' Gamma HCAlpha HType Hlookup.
      inversion HCAlpha; subst...
      inversion Hlookup.
      simpl.
      repeat rewrite Coq.Strings.String.eqb_refl.
      reflexivity.
    + intros Gamma' Gamma HCAlpha HType Hlookup.
      inversion HCAlpha; subst...
      simpl.
      destruct (y =? w) eqn:yw.
      * apply String.eqb_eq in yw.
        apply H0 in yw.
        contradiction yw.
      * specialize (IHAlphaVar Gamma'0 Gamma0 H7).
        unfold lookup in Hlookup.
        destruct (x =? z) eqn:xz.
        -- apply String.eqb_eq in xz.
           apply H in xz.
           contradiction xz.
        -- fold (lookup z Gamma0) in Hlookup.
          assert (Gamma0 |-* (tmvar z) : A).
          {
            (* Strengthening typing*)
            apply K_Var.
            assumption.
          }
           specialize (IHAlphaVar H2 Hlookup).
           assumption.
  - intros Gamma' Gamma HCAlpha A0 HType.
    inversion HType.
    specialize (IHHAlpha ((y, A)::Gamma') ((x, A)::Gamma)
      (calpha_cons x y A HCAlpha) K2 H4).
    apply K_Lam.
    assumption.
  - intros Gamma' Gamma HCAlpha A HType. 
    inversion HType.
    specialize (IHHAlpha1 Gamma' Gamma HCAlpha (tp_arrow K1 A) H2).
    specialize (IHHAlpha2 Gamma' Gamma HCAlpha K1 H4).
    apply K_App with (K1 := K1); assumption.
Qed.


(* ********************
      Beta reduction
*)


(* TODO: Used to be Prop. Ask Jacco*)
Inductive step : term -> term -> Set :=
| step_beta (x : string) (A : type) (s t : term) :
    step (tmapp (tmlam x A s) t) ([x := t] s)
| step_appL s1 s2 t :
    step s1 s2 -> step (tmapp s1 t) (tmapp s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (tmapp s t1) (tmapp s t2)
| step_abs x A s1 s2 :
    step s1 s2 -> step (tmlam x A s1) (tmlam x A s2).

Lemma step_ebeta x A s t u : 
  u = ([x := t] s) -> step (tmapp (tmlam x A s) t) u.
Proof. move->. exact: step_beta. Qed.

(* This is not true ... *)
Lemma step_preserves_fresh sigma t1 t2 : 
  step t1 t2 -> fresh2 sigma t1 = fresh2 sigma t2.
Proof.
Admitted.
(* TODO: Not true because of fresh, what conditions do we need? *)
(* e.g. rename X Y (tmlam Y A (tmvar X)) = tmlam Y A (tmvar Y). 
  that case shouldnt be possible. But Y is not in ftv (tmlam Y A (tmvar X))
  should we consider all type variables, not only the free ones for ftv?

*)

Lemma de_morgan2 : forall P Q : Prop, ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
  intros P Q. split.
  - intros H. split.
    + intros HP. apply H. left. assumption.
    + intros HQ. apply H. right. assumption.
  - intros [H1 H2] [HP | HQ].
    + apply H1. assumption.
    + apply H2. assumption.
Qed.

(* For the var case we needed to also alpha t,x,y to make it consistent with ren*)
Lemma ren_sub_compose''_var_fix x x' y y' s t ren ren1 ren2 s' s'':
  AlphaCtxTrans ren1 ren2 ren -> 
  Alpha ren1 s' s -> 
  Alpha ren2 s s'' -> 
  Alpha ren t t -> (* this condition is saying x not in t implicitly if (x,y) in ren????? *)
  AlphaVar ren x y ->
  AlphaVar ren x' y' ->

  ~ In x' (tv ([x := t] s')) -> (* TODO: I dont want this condition! It is saying like x' is " super"  fresh: 
    x' is not equal to any of the fresh variables generated in the subst operation*)
  Alpha ren (rename x x' ([x := t] s')) ([y := rename y y' t] s'').
Proof.
  (* destruct (in_dec (String.string_dec) y (tv t)).
  {
  generalize dependent s'.
  generalize dependent s''.
  generalize dependent ren1.
  generalize dependent ren2.
  generalize dependent ren.
  induction s; intros ren ren2 ren1 s'' s' Htrans Halphas1 Halphas2 Halphat Hmrenx Hmrenx' Hx'Fresh.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_1.
    simpl.
    destr_eqb_eq x x0.
    + (* Since x = x0, we should always have y = y1*)
      assert (AlphaVar ren x0 y1) by admit.
      destr_eqb_eq y y1.
      * rewrite capms_equation_1.
        simpl.
        rewrite String.eqb_refl.
        
        
        
        (*
          Then we are renaming alpha (under ren) terms to alpha (under ren) terms in a term that is alpha (under ren).
          Should be ok?
        *)
        admit.
      * (* contradiction somewhere 
        
          Some lemma that converts    
              mren ren (tmvar x0) = tmvar y 
          to
              AlphaVar ren x0 y

          Then we have
            AlphaVar ren x0 y
            AlphaVar ren x0 y1

          That is only possible if y = y1.
        *)
        admit.
    + 
      (*
        By mren ren (tmvar x) = tmvar y
          then
        AlphaVar ren x y

        By 
          x <> x0
          AlphaVar ren x0 y1
          AlphaVar ren x y
        
        Then:
          y <> y1
        (because otherwise AlphaVar ren x0 y1 and AlphaVar ren x y1, not possible with x0 <> x)
        *)
      destr_eqb_eq y y1.
      * admit. (* by above not possible: contradiction*)
      * rewrite capms_equation_1.
        simpl.
        destr_eqb_eq y y1.
        -- contradiction.
        -- unfold rename. unfold mren.
           simpl.
           destr_eqb_eq x x0.
           ++ contradiction.
           ++ apply alpha_var.
              admit. (* by alpha_trans*)
  - (* Case: Lam *)
    inversion Halphas1.
    inversion Halphas2.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    subst.
    remember (fresh2 [(x, t)] s1) as s0'.
    remember (fresh2 [(y, rename y y' t)] s4) as s0''.
    destr_eqb_eq x s0'.
    + (* contradiction fresh s0' *)
      admit.
    + unfold rename.
      unfold mren. fold mren.
      
      assert (Hdrop: drop s0' [(x, x')] = ((x, x')::nil)) by admit.
      rewrite Hdrop.
      apply alpha_lam.

      assert (Alpha [(s0', x0)] (rename x0 s0' s1) s1).
      {
        apply @alpha_sym with (ren := ((x0, s0')::nil)).
        - apply alpha_sym_cons.
          apply alpha_sym_nil.
        - apply alphaRename.
          (* s0' notin tv s1 follows from s0' = fresh2 [(x, t)] s1*)
          admit.
      }
      assert (HtransRes1: Alpha ((s0', s)::ren1) (rename x0 s0' s1) s0).
      {
        remember (ctx_id_left ren1) as ren_id.

        (* by transitivity and H2: Alpha ((x0, s) :: ren1) s1 s0*)
        apply @alpha_trans with (ren := (s0', x0)::ren_id ) (ren' := (x0, s)::ren1) (t := s1).
        - apply alpha_trans_cons.
          rewrite Heqren_id.
          apply id_left_trans.
        - 
          assert ((s0', x0)::ren_id = ((s0', x0)::nil) ++ ren_id) by reflexivity.
          rewrite H1.
          apply alpha_extend_ids_right.
          + rewrite Heqren_id.
            apply ctx_id_left_is_id.
          + assumption.
        - assumption.
      }

      (* ANALOGOUS*)
      assert (Alpha ((s, y1) :: ren2) s0 s4) by assumption. (* By assumption: This is saying that in s4, we already have s replaced by y0!*)
      assert (Alpha [(y1, s0'')] s4 (rename y1 s0'' s4)) by admit.
      assert (HtransRes2: Alpha ((s, s0'')::ren2) s0 (rename y1 s0'' s4)) by admit. (* Transitivity. then here we replace y0 by s0'', since s4 already has s replaced by y0, we dont have to change the replace arguments*)

      assert (Htrans': AlphaCtxTrans ((s0', s)::ren1) ((s, s0'')::ren2) ((s0', s0'')::ren)) by admit.
      
      specialize (IHs ((s0', s0'')::ren) ((s, s0'')::ren2) ((s0', s)::ren1) (rename y1 s0'' s4) (rename x0 s0' s1) Htrans').
      specialize (IHs HtransRes1 HtransRes2).
      
      assert (HalphatExtend : Alpha ((s0', s0'')::ren) t t) by admit. (* s0' and s0'' fresh over t!*)

      (* here we use that x' is not equal to any of the fresh variables generated by [x := t] (such as s0')*)
      assert (Hx'FreshExtendAndHnots0'x' : s0' <> x' /\ ~ (In x' (tv ([x := t] (rename x0 s0' s1))))).
      {
        rewrite capms_equation_2 in Hx'Fresh.
        simpl in Hx'Fresh.
        rewrite <- Heqs0' in Hx'Fresh.
        (* rewrite not or*)
        rewrite -> de_morgan2 in Hx'Fresh.
        destruct Hx'Fresh as [Hnots0'x' Hx'Fresh].
        split; assumption.
      }
      
      destruct Hx'FreshExtendAndHnots0'x' as [Hnots0'x' Hx'FreshExtend].

      specialize (IHs HalphatExtend).

      assert (HAlphaVarXExtend: AlphaVar ((s0', s0'') :: ren) x y) by admit. (* x, y fresh under s0', s0''*)

      assert (y' <> s0'') by admit. (* By y in tv t and s0'' = fresh2 [(y, rename y y' t)]: TODO: We probably need ftv instead of tv*)

      assert (HAlphaVarYExtend: AlphaVar ((s0', s0'') :: ren) x' y') by admit.

      specialize (IHs HAlphaVarXExtend HAlphaVarYExtend Hx'FreshExtend).

      apply IHs.
  - admit.
  }
  {
    (* y notin tv t, by AlphaVar ren x y, we have [(x, y)] in ren
      hence not x in t.
     *)
    assert (rename y y' t = t) by admit.
    rewrite H.
    intros Htrans HalphaS1 HalphaS2 Halphat HalphaVarx HalphaVarx' Hx'Fresh.
    clear Hx'Fresh.
    clear HalphaVarx'.
    generalize dependent s'.
    generalize dependent s''.
    generalize dependent ren.
    generalize dependent ren1.
    generalize dependent ren2.
    induction s; intros ren2 ren1 ren Htrans Halphat HalphaVarx s'' HalphaS1 s' HalphaS2.
    - admit.
    - intros.
      inversion HalphaS1.
      subst.
      inversion HalphaS2.
      subst.
      rewrite capms_equation_2.
      rewrite capms_equation_2.
      simpl.
      remember (fresh2 [(x, t)] s1) as s0'.
      remember (fresh2 [(y, t)] s2) as s0''.
      assert (Hxs0': x <> s0') by admit.
      assert (HrenLam: rename x x' (tmlam s0' t0 ([x := t] rename x0 s0' s1)) = tmlam s0' t0 (rename x x' ([x := t] (rename x0 s0' s1)))) by admit.
      rewrite HrenLam.
      apply alpha_lam.
      

      assert (Alpha [(s0', x0)] (rename x0 s0' s1) s1).
      {
        apply @alpha_sym with (ren := ((x0, s0')::nil)).
        - apply alpha_sym_cons.
          apply alpha_sym_nil.
        - apply alphaRename.
          (* s0' notin tv s1 follows from s0' = fresh2 [(x, t)] s1*)
          admit.
      }
      assert (HtransRes1: Alpha ((s0', s)::ren1) (rename x0 s0' s1) s0).
      {
        remember (ctx_id_left ren1) as ren_id.

        (* by transitivity and H2: Alpha ((x0, s) :: ren1) s1 s0*)
        apply @alpha_trans with (ren := (s0', x0)::ren_id ) (ren' := (x0, s)::ren1) (t := s1).
        - apply alpha_trans_cons.
          rewrite Heqren_id.
          apply id_left_trans.
        - 
          assert ((s0', x0)::ren_id = ((s0', x0)::nil) ++ ren_id) by reflexivity.
          rewrite H1.
          apply alpha_extend_ids_right.
          + rewrite Heqren_id.
            apply ctx_id_left_is_id.
          + assumption.
        - assumption.
      }

      (* ANALOGOUS*)
      assert (Alpha ((s, y0) :: ren2) s0 s2) by assumption. (* By assumption: This is saying that in s4, we already have s replaced by y0!*)
      assert (Alpha [(y0, s0'')] s2 (rename y0 s0'' s2)) by admit.
      assert (HtransRes2: Alpha ((s, s0'')::ren2) s0 (rename y0 s0'' s2)) by admit. (* Transitivity. then here we replace y0 by s0'', since s4 already has s replaced by y0, we dont have to change the replace arguments*)

      assert (Htrans': AlphaCtxTrans ((s0', s)::ren1) ((s, s0'')::ren2) ((s0', s0'')::ren)) by admit.
      
      specialize (IHs  ((s, s0'')::ren2) ((s0', s)::ren1) ((s0', s0'')::ren) Htrans').
      
      assert (HalphatExtend : Alpha ((s0', s0'')::ren) t t) by admit. (* s0' and s0'' fresh over t!*)

      assert (HalphaVarxExtend : AlphaVar ((s0', s0'') :: ren) x y) by admit.

      specialize (IHs HalphatExtend HalphaVarxExtend (rename y0 s0'' s2) HtransRes2).

      specialize (IHs (rename x0 s0' s1) HtransRes1).

      apply IHs.
    - admit.
  } *)
Admitted.

Lemma ren_lam_vacuous x x' t s0 :
  rename x x' (tmlam x t s0) = tmlam x t s0.
Proof.
  unfold rename.
  simpl. rewrite String.eqb_refl. rewrite mren_id. reflexivity.
Qed.

Lemma ren_lam x x' t s s0 :
  x <> s -> rename x x' (tmlam s t s0) = tmlam s t (rename x x' s0).
Proof.
  intros Hnotxs.
  unfold rename.
  simpl. rewrite <- String.eqb_neq in Hnotxs. rewrite Hnotxs.
  reflexivity.
Qed.

Lemma ren_commute x x' y y' s :
  x <> y ->
  x' <> y ->
  y' <> x ->
  rename x x' (rename y y' s) = rename y y' (rename x x' s).
Proof.
  intros Hxy Hx'y Hy'x.
  induction s.
  - simpl.
    destr_eqb_eq y s.
    + destr_eqb_eq x s.
      * contradiction.
      * unfold rename.
        simpl. rewrite String.eqb_refl. rewrite <- String.eqb_neq in H. rewrite H. simpl.
        rewrite <- String.eqb_neq in Hy'x. rewrite String.eqb_sym in Hy'x. rewrite Hy'x.
        rewrite String.eqb_refl.
        reflexivity.
    + unfold rename. simpl. rewrite <- String.eqb_neq in H. rewrite H.
      destr_eqb_eq x s.
      * simpl. rewrite String.eqb_refl. rewrite <- String.eqb_neq in Hx'y. rewrite String.eqb_sym in Hx'y. rewrite Hx'y.
        reflexivity.
      * simpl. rewrite <- String.eqb_neq in H0. rewrite H0. rewrite H.
        reflexivity.   
  - destr_eqb_eq y s.
    + rewrite ren_lam_vacuous.
      rewrite ren_lam; [|assumption].
      rewrite ren_lam_vacuous.
      reflexivity.
    + destr_eqb_eq x s.
      * rewrite ren_lam_vacuous;
        rewrite ren_lam; [|assumption].
        rewrite ren_lam_vacuous; reflexivity.
      * rewrite ren_lam; [|assumption].
        rewrite ren_lam; [|assumption].
        rewrite ren_lam; [|assumption].
        rewrite ren_lam; [|assumption].
        rewrite IHs.
        reflexivity.
  - unfold rename. simpl.
    unfold rename in IHs1.
    unfold rename in IHs2.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
Qed.

Lemma ren_two_vacuous {x Y' Y s }:
  x <> Y ->
  rename x Y' (rename x Y s) = rename x Y s.
Proof.

Admitted.

Lemma ren_vacuous X Y s :
  ~ In X (tv s) -> rename X Y s = s.
Proof.
Admitted.

Lemma sub_vacuous_stronger X t Y u Y' s s' s'' ren ren1 ren2 :
  AlphaVar ren Y Y' ->
  Alpha ren u u ->
  AlphaCtxTrans ren1 ren2 ren ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  ~ In X (tv s') -> Alpha ren (((X, t)::(Y, u)::nil) [[ s' ]]) (((Y', u)::nil) [[ s'' ]]).
Proof.
  intros HalphaY HalphaU HalphaTrans Halphas1 Halphas2 Hnotins.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.
  generalize dependent s'.
  generalize dependent s''.
  induction s; intros s'' s' HxnotIns' ren2 Halphas2 ren1 Halphas1 ren HalphaY HalphaU HalphaTrans.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_1.
    simpl.
    destr_eqb_eq X x.
    + unfold tv in HxnotIns'.
      rewrite not_in_cons in HxnotIns'.
      destruct HxnotIns'.
      contradiction.
    + (* X <> x *)
            assert (AlphaVar ren x y0).
        {
          eapply alpha_var_trans; eauto.
        }
      destr_eqb_eq Y x.
      * 

        assert (y0 = Y').
        {
          eapply alphavar_unique; eauto.
        }
        rewrite H1.
        rewrite capms_equation_1.
        simpl.
        rewrite String.eqb_refl.
        assumption.
      * (* AlphaVar x y0
          x <> Y and AlphaVar Y Y'. Therefore y0 <> Y'
      *)
        remember H0 as H0_copy.
        clear HeqH0_copy.
        apply (alphavar_unique_not H1 HalphaY) in H0.
        rewrite capms_equation_1.
        simpl.
        rewrite <- String.eqb_neq in H0.
        rewrite H0.
        apply alpha_var.
        assumption.



      (* By AlphaVar ren x y0 and AlphaVar ren x Y' => Y' = y0, then by capms_equation-1 we have ren |- u ~ u, assumption*) 
  - (* By X notin tv (tmlam s t0 s0),   also X notin tv s0, so we can use IHS*)
    inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 ((x, tmvar x) :: (X, t) :: (Y, u)::nil) s1) as s0'.
    remember (fresh2 ((y0, tmvar y0) :: (Y', u) :: nil) s4) as s0''.

    apply alpha_lam.
    eapply IHs.
    + (* X is not s0' by fresh2. and X is not s1 by X notin tv (tmlam x t0 s1)*)
      shelve.
    + eapply @alpha_trans with (ren' := ((y0, s0'')::(ctx_id_right ren2))).
      * apply alpha_trans_cons.
          apply id_right_trans.
      * exact H10.
      * change ((y0, s0''):: (ctx_id_right ren2)) with (((y0, s0'')::nil) ++ (ctx_id_right ren2)). 
          apply alpha_extend_ids_right.    
          -- apply ctx_id_right_is_id.
          -- apply alphaRename. shelve. (* True by s0'' = fresh2 s4*)
    + eapply @alpha_trans with (ren := (s0', x) :: (ctx_id_left ren1)).
      * apply alpha_trans_cons.
        apply id_left_trans.
      *  
        change ((s0', x) :: (ctx_id_left ren1)) with (((s0', x)::nil) ++ (ctx_id_left ren1)).
        apply alpha_extend_ids_right.
        -- apply ctx_id_left_is_id.
        -- eapply alpha_sym.
          ++ apply alpha_sym_cons. apply alpha_sym_nil.
          ++ apply alphaRename. shelve.
      * exact H2.
    + shelve. (* By fresh2 *)
    + shelve. (* By fresh2 *)  
    + apply alpha_trans_cons.
      exact HalphaTrans.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_3.
    rewrite capms_equation_3.
    apply alpha_app.
    + eapply IHs1.
      * shelve.
      * exact H8.
      * exact H3.
      * exact HalphaY.
      * exact HalphaU.
      * exact HalphaTrans.
Admitted.

(* Need alpha because the bigger vacuous substitution is used in fresh variable generation *)
Lemma sub_vacuous X t Y u s :
  ~ In X (tv s) -> Alpha [] (((X, t)::(Y, u)::nil) [[ s ]]) (((Y, u)::nil) [[ s ]]).
Proof.
  intros Hnotins.
  eapply sub_vacuous_stronger; try constructor; try apply alpha_refl; try constructor.
  - assumption.
Qed.


(* Is the above still useful? Yes! *)
Lemma ren_sub_compose''_specific x x' s t :
  ~ In x' (tv ([x := t] s)) -> Alpha [] (rename x x' ([x := t] s)) ([x := rename x x' t] s). 
Proof.
  intros Hfresh.
  eapply ren_sub_compose''_var_fix; eauto;
  try constructor;
  apply alpha_refl;
  constructor.
Qed.

Lemma sub_preserves_alpha Z Z' t s s' s'' ren1 ren2 ren :
  AlphaVar ren Z Z' ->
  AlphaCtxTrans ren1 ren2 ren ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  Alpha ren t t ->
  Alpha ren ([Z := t] s') ([Z' := t] s'').
Proof.
  intros HalphaZ HalphaS HalphaT.
  generalize dependent s'.
  generalize dependent s''.
  generalize dependent ren1.
  generalize dependent ren2.
  generalize dependent ren.
  induction s; intros ren HalphaZ ren2 ren1 HalphaTrans s'' s' Halphas1 Halphas2 Halphat.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_1.
    rewrite capms_equation_1.
    simpl.
          assert (AlphaVar ren x y0).
      {
        eapply alpha_var_trans; eauto. 
      }
    destr_eqb_eq Z x.
    + (* Z = x, but AlphaVar ren x Z' and AlphaVar ren x y0, so Z' = y0*)

      assert (HZ'y0: Z' = y0). { eapply alphavar_unique; eauto. }
      rewrite HZ'y0.
      rewrite String.eqb_refl.
      assumption.
    + (* Z <> x*)
      destruct (Z' =? y0) eqn:HZ'y0.
      * apply String.eqb_eq in HZ'y0.
        (* Then AlphaVar ren x y0   and  AlphaVar ren Z y0     then also *)
        subst.
        exfalso.
        apply (alphavar_unique_not H0 HalphaZ) in H.
        contradiction.
      * apply alpha_var.
        assumption. 

  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 [(x, tmvar x); (Z, t)] s1) as s0'.
    remember (fresh2 [(y0, tmvar y0); (Z', t)] s4) as s0''.
    apply alpha_lam.
    eapply IHs.
    + shelve. (* By fresh2 on Z and Z'*)
    + apply alpha_trans_cons.
      exact HalphaTrans.
    + eapply @alpha_trans with (ren := (s0', x) :: (ctx_id_left ren1)).
      * apply alpha_trans_cons.
        apply id_left_trans.
      *  
        change ((s0', x) :: (ctx_id_left ren1)) with (((s0', x)::nil) ++ (ctx_id_left ren1)).
        apply alpha_extend_ids_right.
        -- apply ctx_id_left_is_id.
        -- eapply alpha_sym.
          ++ apply alpha_sym_cons. apply alpha_sym_nil.
          ++ apply alphaRename. shelve.
      * exact H2.
    + eapply alpha_trans.
      * apply alpha_trans_cons.
          apply id_right_trans.
      * exact H10.
      * change ((y0, s0''):: (ctx_id_right ren2)) with (((y0, s0'')::nil) ++ (ctx_id_right ren2)). 
          apply alpha_extend_ids_right.    
          -- apply ctx_id_right_is_id.
          -- apply alphaRename. shelve. (* True by s0'' = fresh2 s4*)
    + shelve. (* By fresh2 *)
  - admit. 

Admitted.

Lemma ren_sub_compose_stronger_single : forall s s' s'' ren ren1 ren2 Z Z' t X X' Y,
  AlphaCtxTrans ren1 ren2 ren ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  ren ⊢ t ~ t ->
  AlphaVar ren X X'->
  (* AlphaVar ren Y Y' ->  IDEA: Remove this whole condition! Y is "superfresh", so it is not changed by ren is the idea! *)
  AlphaVar ren Y Y ->
  AlphaVar ren Z Z' ->
  (* We can add condition X contained (strings) in Y (some freshness condition) *)
  ~ In Y (tv ([Z := t] s') ++ (Z::nil) ++ (tv s')) -> (* First condition needed for IH, second for var case. 
    Maybe we need here rename X Y s' instead of s'. That sounds circular, but maybe it is not! *)
  (* X string contained in Y: *)
  lt (String.length X) (String.length Y) ->
  ren ⊢ [Z := t] (rename X Y s') ~ ((X', tmvar Y)::(Z', t)::nil) [[s'']].
Proof. 
  intros s s' s'' ren ren1 ren2 Z Z' t X X' Y Htrans HalphaS1 HalphaS2 Halphat HalphaX HalphaY HalphaZ HYfresh Hlength.



  generalize dependent s'.
  generalize dependent s''.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.

  induction s; intros ren2 ren1 ren HalphaTrans Halphat HalphaVarX HalphaVarY HalphaVarZ s'' Halphas2 s' Halphas1 HYfresh.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    assert (AlphaVar ren x y0). {eapply alpha_var_trans; eauto. }
    destr_eqb_eq x X.
    + (* x = X, but alphaVar ren X y0, so alphaVar ren x y0. But AlphaVar ren X X', so y0 = X'*)
      unfold rename. unfold mren. simpl. rewrite String.eqb_refl.
      assert (Hy0X': y0 = X'). { eapply alphavar_unique; eauto. }
      rewrite capms_equation_1.
      simpl.
      rewrite not_in_app in HYfresh.
      destruct HYfresh as [_ HYfresh].
      rewrite not_in_cons in HYfresh.
      destruct HYfresh as [HYfresh _].   (* Here we use that Z <> Y*)
      destr_eqb_eq Z Y.
      * contradiction.
      * rewrite Hy0X'.
        rewrite capms_equation_1. simpl. rewrite String.eqb_refl.

        apply alpha_var.
        assumption.
    + (* x <> X*)
      unfold rename. unfold mren. simpl. rewrite <- String.eqb_neq in H0. assert (X =? x = (x =? X)) by apply String.eqb_sym.
      rewrite <- H1 in H0. rewrite H0.
      (* x <> X, but x ~ y0 and X ~ X', so y0 <> X'*)
      assert (HnotX'y0: X' <> y0). { eapply alphavar_unique_not; eauto. apply String.eqb_neq in H0. assumption. }
      rewrite capms_equation_1. simpl.
      rewrite capms_equation_1. simpl.
      rewrite <- String.eqb_neq in HnotX'y0. rewrite HnotX'y0.
      destr_eqb_eq Z x.
      * (* Z = x, but AlphaVar ren x Z' and AlphaVar ren x y0, so Z' = y0*)
        assert (HZ'y0: Z' = y0). { eapply alphavar_unique; eauto. }
        rewrite HZ'y0.
        rewrite String.eqb_refl.
        assumption.
      * (* By same logic now Z' <> y0*)
        assert (HnotZ'y0: Z' <> y0). { eapply alphavar_unique_not; eauto. }
        rewrite <- String.eqb_neq in HnotZ'y0. rewrite HnotZ'y0.
        apply alpha_var.
        assumption.     

  - inversion Halphas1.
    inversion Halphas2.
    subst.
    destr_eqb_eq X x.
    + assert (HlamRen: rename x Y (tmlam x t0 s1) = tmlam x t0 s1). { unfold rename. unfold mren. fold mren. simpl. rewrite String.eqb_refl. rewrite mren_id. reflexivity. }
      rewrite HlamRen.
      rewrite capms_equation_2. (* This should also make it fresh in x I think! *)
      rewrite capms_equation_2.
      simpl.
      remember (fresh2 [(x, tmvar x); (Z, t)] s1) as s0'.
      remember (fresh2 [(y0, tmvar y0); (X', tmvar Y); (Z', t)] s4) as s0''.
      apply alpha_lam.
      assert (Hnotxs0': x <> s0'). { rewrite Heqs0'. shelve. }
      assert (HrenameVacuous: rename x s0' s1 = rename x Y (rename x s0' s1)). { now rewrite (ren_two_vacuous Hnotxs0'). }
      rewrite HrenameVacuous.

      assert (Htvlam: tv ([Z := t] (tmlam x t0 s1)) = tv (tmlam s0' t0 ([Z := t] (rename x s0' s1)))).
        {
          rewrite capms_equation_2. simpl.
          rewrite <- Heqs0'.
          reflexivity.
        }

      eapply IHs.
      * apply alpha_trans_cons. exact HalphaTrans.
      * shelve. (* s0' and s0'' not in t by fresh2.*)
      * shelve. (* x <> s0' by assumption and X' <> s0'' by fresh2*) 
      * rewrite Htvlam in HYfresh.

         rewrite not_in_cons in HYfresh.  destruct HYfresh as [HYfresh HYfresh2]; simpl. fold tv in HYfresh2. 
         apply alpha_var_diff.
         -- auto.
         -- shelve. (* By s0'' = fresh2 Y'*)
         -- assumption.
      * shelve. (* By fresh2 *)
      * eapply alpha_trans.
        -- apply alpha_trans_cons.
           apply id_right_trans.
        -- exact H10.
        -- change ((y0, s0''):: (ctx_id_right ren2)) with (((y0, s0'')::nil) ++ (ctx_id_right ren2)). 
           apply alpha_extend_ids_right.    
           ++ apply ctx_id_right_is_id.
           ++ apply alphaRename. shelve. (* True by s0'' = fresh2 s4*)
      * eapply @alpha_trans with (ren := (s0', x) :: (ctx_id_left ren1)).
        -- apply alpha_trans_cons.
           apply id_left_trans.
        --  
           change ((s0', x) :: (ctx_id_left ren1)) with (((s0', x)::nil) ++ (ctx_id_left ren1)).
            apply alpha_extend_ids_right.
            ++ apply ctx_id_left_is_id.
            ++ eapply alpha_sym.
              ** apply alpha_sym_cons. apply alpha_sym_nil.
              ** apply alphaRename. shelve. 
        -- assumption.
      * rewrite Htvlam in HYfresh.
        rewrite not_in_cons in HYfresh. destruct HYfresh as [HYfresh HYfresh2]. fold tv in HYfresh2. clear IHs.
        rewrite not_in_app in HYfresh2.
        destruct HYfresh2 as [HYfresh2 HYfresh3].
        rewrite not_in_app.
        split.
        -- assumption.
        -- rewrite not_in_app in HYfresh3. destruct HYfresh3 as [HYfresh3 HYfresh4]; rewrite not_in_app; split.
           ++ assumption.
           ++ admit. (* Not in s1 and not equal to s0', hence not in tv (rename x s0' s1)
           *)

      
      

    + (* x <> X*) 
      rewrite ren_lam; [|assumption].
      rewrite capms_equation_2.
      rewrite capms_equation_2.
      simpl.
      remember (fresh2 [(x, tmvar x); (Z, t)] (rename X Y s1)) as s0'.
      remember (fresh2 [(y0, tmvar y0);(X', tmvar Y); (Z', t)] s4) as s0''.
      apply alpha_lam.

      (* Ok, we seem to have to switch out renamings?
      
      We know x <> X, so I think this is allowed, if Y = x, we have a problem. Similarly if s0' = X.
      Y <> x ? yes, by HYfresh
      s0' = X? Suppose it is. Then no X in (rename X Y s1). Then rename x X s1 yields something with X,
       and then that gets renamed to Y.
      We dont want it to be. ??? This can only happen if X=s0' not in t and X <> Z. 

      We know X <> Y (we should add it as a condition!)
      *)
      destruct (X =? s0').
      * assert (Hxs0': X = s0') by shelve. rewrite Hxs0'.
        (* Maybe we can differentiatie on X in (tmlam x to s1)
          If it is not in there, there is no renaming. Done! 

          If it is in there, it is in tv (tmlam x t0 s1).
          Then it is in tv (s1) since x <> X
          Since X in s1, then Y in rename X Y s1.
          s0' is then fresh2 over Y.

          But we should have some information somewhere that Y is fresh2 over X.

          Hence s0' cannot be X!
        *)
        
        destruct (in_dec String.string_dec X (tv s1)).
        -- assert (HYins1: In Y (tv (rename X Y s1))) by shelve.
           assert (Hlengths0': gt (String.length s0') (String.length Y)) by shelve.
           rewrite Hxs0' in Hlength.
           exfalso.
           lia.
        -- rewrite ren_vacuous in Heqs0'; [|assumption].
           assert (HrenVac: rename s0' Y s1 = s1). { rewrite ren_vacuous. - reflexivity. - rewrite Hxs0' in n. assumption. }
           rewrite HrenVac.
           (*
              X not in s1, so X' not in s4 by s1 ~ s4. Also X' <> s0'', hence X' not in rename y0 s0'' s4

           *)
           assert (HnotX': Alpha [] (((X', tmvar Y):: (Z', t)::nil) [[rename y0 s0'' s4]])  (([Z' := t] (rename y0 s0'' s4)))).
           {
            assert (~ In X' (tv (rename y0 s0'' s4))).
            {
              (*Alpha ren s1 s4. And X not in s1. So X' not in s4.
                
                Then by X' <> s0'': done.
              *)
              admit.
            }
            eapply sub_vacuous in H0.
            exact H0.
           }
           eapply @alpha_trans with (ren' := (ctx_id_right ((s0'', s0'')::ren))).
           ++ apply alpha_trans_cons.
              apply id_right_trans.
           ++ 

          (* If x is  in s1 then y0 is in s4
            s0' ~ s0'', s1 ~ s4, Z ~ Z' t ~ t,   all under (s0', s0'')::ren

            So we can use sub_preserves_alpha
           *)
           {
            eapply sub_preserves_alpha.
            - shelve. (* fresh2 *)
            - apply alpha_trans_cons. exact HalphaTrans.
            - eapply @alpha_trans with (ren := (s0', x) :: (ctx_id_left ren1)).
              + apply alpha_trans_cons.
                apply id_left_trans.
              +  
                change ((s0', x) :: (ctx_id_left ren1)) with (((s0', x)::nil) ++ (ctx_id_left ren1)).
                  apply alpha_extend_ids_right.
                  * apply ctx_id_left_is_id.
                  * eapply alpha_sym.
                    -- apply alpha_sym_cons. apply alpha_sym_nil.
                    -- apply alphaRename. shelve.
              + exact H2.  
        
            - eapply alpha_trans.
              + apply alpha_trans_cons.
                apply id_right_trans.
              + exact H10.
              + change ((y0, s0''):: (ctx_id_right ren2)) with (((y0, s0'')::nil) ++ (ctx_id_right ren2)). 
                apply alpha_extend_ids_right.    
                * apply ctx_id_right_is_id.
                * apply alphaRename. shelve. (* True by s0'' = fresh2 s4*)
            - shelve. (* fresh2 thing *) 
           }    


           ++ change ((ctx_id_right ((s0'', s0'')::ren))) with (nil++  (ctx_id_right ((s0'', s0'')::ren))).
              apply alpha_extend_ids_right.    
              ** apply ctx_id_right_is_id.
              ** apply @alpha_sym with (ren := nil) (ren' := nil) in HnotX'.
                 exact HnotX'.
                 apply alpha_sym_nil.

                   
           

      * assert (Hnotxs0': X <> s0') by shelve.
        rewrite ren_commute; try auto; [|shelve]. (* Y <> x by HYfresh*)
        eapply IHs.
        -- apply alpha_trans_cons. exact HalphaTrans.
        -- shelve. (* s0' and s0'' not in t by fresh2.*)
        -- shelve. (* x <> s0' by assumption and X' <> s0'' by fresh2*)
        -- rewrite not_in_app in HYfresh. destruct HYfresh as [HYfresh _].
           rewrite capms_equation_2 in HYfresh. simpl in HYfresh.
           rewrite de_morgan2 in HYfresh. destruct HYfresh as [HYfresh _].
           assert (HnotYs0': Y <> s0').
           {
              destruct (in_dec String.string_dec X (tv s1)).
              - assert (HXY: X <> Y) by shelve. (* Fresh condition, X in s1 *)
                assert (HYins1: In Y (tv (rename X Y s1))) by shelve.
                shelve. (* Then by freshness condition of Heqs0'*)


              - rewrite ren_vacuous in Heqs0'.
                + rewrite <- Heqs0' in HYfresh. symmetry. assumption.
                + assumption.
           }
           apply alpha_var_diff.
           ++ auto.
           ++ shelve. (* By s0'' = fresh2 Y'*)
           ++ assumption. 
        -- shelve.
      -- eapply alpha_trans.
        ++ apply alpha_trans_cons.
           apply id_right_trans.
        ++ exact H10.
        ++ change ((y0, s0''):: (ctx_id_right ren2)) with (((y0, s0'')::nil) ++ (ctx_id_right ren2)). 
           apply alpha_extend_ids_right.    
           ** apply ctx_id_right_is_id.
           ** apply alphaRename. shelve. (* True by s0'' = fresh2 s4*)
      -- eapply @alpha_trans with (ren := (s0', x) :: (ctx_id_left ren1)).
        ++ apply alpha_trans_cons.
           apply id_left_trans.
        ++  
           change ((s0', x) :: (ctx_id_left ren1)) with (((s0', x)::nil) ++ (ctx_id_left ren1)).
            apply alpha_extend_ids_right.
            ** apply ctx_id_left_is_id.
            ** eapply alpha_sym.
              --- apply alpha_sym_cons. apply alpha_sym_nil.
              --- apply alphaRename. shelve. (* s0' not in rename X Y s1, and also X <> s0' *) 
        ++ assumption.
      -- clear IHs.
                 (* Y not in tv [z := t] rename x (fresh2 x Z t s1) s1 by assumption.
                 Also Y <> s0' ?? *)

        rewrite not_in_app in HYfresh. destruct HYfresh as [HYfresh HYfreshlam].
           rewrite capms_equation_2 in HYfresh. simpl in HYfresh.
           rewrite de_morgan2 in HYfresh. destruct HYfresh as [HYfresh HYfresh2]. (* Not strong enough I think*)
           assert (HnotYs0': Y <> s0').
           {
              destruct (in_dec String.string_dec X (tv s1)).
              - assert (HXY: X <> Y) by shelve. (* Fresh condition, X in s1 *)
                assert (HYins1: In Y (tv (rename X Y s1))) by shelve.
                shelve. (* Then by freshness condition of Heqs0'*)


              - rewrite ren_vacuous in Heqs0'.
                + rewrite <- Heqs0' in HYfresh. symmetry. assumption.
                + assumption.
           }
           admit. (* HORRIBLE! *)
                 
        (*
        tv (rename x s0' s1) <= tv s0' + tv s1, and it is not equal to any of those, except how to know we dont have to check x?

        *)
      
       (* first solve the admit for Y <> s0'*)
       - admit. 
  

Admitted.

Lemma fresh_lemma_4 Y X Z t s:
  Y = (fresh2 ((X, tmvar X)::(Z, t)::nil) s) ->
  ~ In Y (tv ([Z := t] s)).
Proof.
  (* What if s = /X.X
    tv (/X. f(X)) > tv f(X) ???
  then [Z:=t] /X. X = /X'. [Z := t] (rename X X' X) where X' = fresh2 [(X, tmvar X); (Z, t)] X , so yes, not equal!
   *)
Admitted.

Lemma ren_sub_compose_instantiated X Y Z s t :
  Y = (fresh2 ((X, tmvar X)::(Z, t)::nil) s) ->
  nil ⊢ [Z := t] (rename X Y s) ~ ((X, tmvar Y)::(Z, t)::nil) [[s]].
Proof.
  intros HYfresh.
  (* 
    From HYfresh we can conclude: 
    When we have a term [Z := t] (tmlam x A s) we create a fresh var exactly equal to Y.
    and we know Y not in s, Y not in Z, Y not ini t
    
    ~ (In Y (tv ([Z := t] s))). ???
    and therefore 
  *)
  eapply ren_sub_compose_stronger_single; eauto; try constructor.
  - apply alpha_refl. constructor.
  - apply alpha_refl. constructor.
  - apply alpha_refl. constructor.
  - apply not_in_app. split.
    + now apply fresh_lemma_4 with (X := X).
    + apply not_in_app. split.
      * shelve. (* Some fresh property *)
      * shelve. (* Some fresh property *)   
Admitted.     




  (* This is not exactly true, since rename does not create fresh vars and stuff
        But it is "kind of true" , lol.

        So I guess we have to change capms to not unnecessarily rename?
        I would rather not ;) Maybe we can strengthen IHh to include this case.
        Or we change rename to do fresh?

        But it should be true, the fact that x' is fresh is key. that will mean that
        capms and rename should behave the same in the tylam case
        SO: TODO: We have to change capms to not freshen if not necessary

        Will it work with alpha equivalence??? Let's work it out on pen and paper
      *)
Lemma ren_sub_compose : forall sigma x x' s,
  varNotIn x' sigma ->

  nil ⊢ sigma [[rename x x' s]] ~ ((x, tmvar x')::sigma) [[s]].
Proof.
  intros sigma X X' s Hfresh.
  generalize dependent sigma.
  induction s; intros sigma Hfresh.
  - admit.
  - destr_eqb_eq X s.
    + admit.
    + assert (HlamRename: rename X X' (tmlam s t s0) = tmlam s t (rename X X' s0)) by admit.
      rewrite HlamRename.
      rewrite capms_equation_2.
      rewrite capms_equation_2.
      simpl.
      remember (fresh2 ((s, tmvar s)::sigma) (rename X X' s0)) as s0'.
      remember (fresh2 ((s, tmvar s)::(X, tmvar X')::sigma) s0) as s0''.
      apply alpha_lam.
      (* Problem! What if s0' = X*)
      (* IH not strong enough. Need to include alpha contexts and alpha equivalence of s *)
Admitted.


(* We need condition X' not in sigma! 
   Also X' not in s *)
Lemma merge_subst : forall sigma X X' s t,
  nil ⊢ ([X' := t] (((X, tmvar X')::sigma) [[s]])) ~ ((X, t)::sigma) [[s]].
Proof.
Admitted.



(* Why do we need this up to alpha equivalence?

  Because sub lemmas are up to alpha equivalence.

  Let's first prove it as an exercise in alpha equivalence proofs and then show its necessity.
*)
Lemma step_subst {s t} : 
  step s t -> forall sigma : list (string * term), {alphaSigmaT : term & 
  prod (step (sigma [[ s ]]) alphaSigmaT) (Alpha [] alphaSigmaT (sigma [[t]]))} .
Proof.
  intros Hstep. induction Hstep; intros sigma.
  - rewrite capms_equation_3.
    rewrite capms_equation_2. simpl.
    remember (fresh2 ((x, tmvar x)::sigma) s) as x'.
    eexists.
    split.
    + eapply step_beta.
    + 
    (* exists (((x', sigma [[t]])::nil) [[sigma [[rename x x' s]] ]]). *)
    (* split. *)
    + apply step_ebeta. reflexivity.
    + admit.
    (* rewrite ren_sub_compose. *)
        (* rewrite merge_subst.
        rewrite commute_subst.
        apply alpha_refl.
        apply alpha_refl_nil. *)
  - (* Left application *)
    specialize (IHHstep sigma).
    destruct IHHstep as [alphaSigmaS2  [Hs2Step Hs2Alpha]  ].
    exists (tmapp (alphaSigmaS2) (sigma [[t]])).
    split.
    + rewrite capms_equation_3.
      apply step_appL.
      assumption.
    + rewrite capms_equation_3.
      apply alpha_app.
      * assumption.
      * apply alpha_refl.
        apply alpha_refl_nil.
  - (* Right applicaiton *)
    specialize (IHHstep sigma).
    destruct IHHstep as [alphaSigmaT2  [Ht2Step Ht2Alpha] ].
    exists (tmapp (sigma [[s]]) alphaSigmaT2).
    split.
    + rewrite capms_equation_3.
      apply step_appR.
      assumption.
    + rewrite capms_equation_3.
      apply alpha_app.
      * apply alpha_refl.
        apply alpha_refl_nil.
      * assumption.
  - remember (fresh2 ((x, tmvar x)::sigma) s1) as x'.
    specialize (IHHstep ((x, tmvar x')::sigma)).
    destruct IHHstep as [alphaSigmaS2  [Hs2Step Hs2Alpha]  ].
    eexists.
    (* exists (tmlam x' A alphaSigmaS2). *)
    split. 
    + rewrite capms_equation_2. simpl.
      rewrite <- Heqx'.
      apply step_abs.
      (* By ren_sub_compose we know 
        sigma [[rename x x' s1]] ~ ((x, tmvar x')::sigma) [[s1]]

        Then by alpha_preserves_beta we know
        exists ?s2 s.t. sigma [[rename x x' s1]] steps to ?s2 and ?s2 ~ alphaSigmaS2 ~ (x, tmvar x'):: sigma [[s2]]
      *)
      admit.
      (* rewrite ren_sub_compose.
      * assumption.
      * admit. *)
    + rewrite capms_equation_2. simpl.
      assert (Hfresh: (fresh2 sigma s1) = (fresh2 sigma s2)) by apply: step_preserves_fresh Hstep.
      
      (* rewrite <- Hfresh. *)
      (* rewrite <- Heqx'. *)
      apply alpha_lam.
      admit.
      (* rewrite ren_sub_compose.
      * apply alpha_extend_id'.
        assumption.
        apply not_break_shadow_nil.
      * admit. *)
Admitted.


Lemma step_subst_sigma sigma {s t} :
  step s t -> {alphaSigmaT : term & prod (step (sigma [[ s ]]) alphaSigmaT) (Alpha [] alphaSigmaT (sigma [[t]]))}.
Proof.
  intros Hstep.
  apply step_subst.
  assumption.
Qed.

Inductive star {e : term -> term -> Set } (x : term) : term -> Set :=
| starR : star x x
| starSE y z : star x y -> e y z -> star x z.


(** **** Many-Step Reduction *)
Definition red := @star step.



(* Definition sred sigma tau :=
  forall x : var, red (sigma x) (tau x). *)

Lemma red_app s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (tmapp s1 t1) (tmapp s2 t2).
Proof.
  (* move=> A B. apply: (star_trans (tmapp s2 t1)).
  - apply: (star_hom (tmapp^~ t1)) A => x y. exact: step_appL.
  - apply: star_hom B => x y. exact: step_appR. *)
(* Qed. *)
Admitted.

Lemma red_abs x A s1 s2 : 
  red s1 s2 -> red (tmlam x A s1) (tmlam x A s2).
(* Proof. apply: star_hom => x' y'. exact: step_abs. Qed. *)
Proof. Admitted.

(* TODO: Probably need to prove this with strenghtened induction (non-empty context) for the lambda case *)
Lemma step_preserves_alpha_nd {s} {s'} {t} :
  Alpha [] s t -> step s s' -> {t' & prod (step t t') (Alpha [] s' t')}.
Proof.
  (* Non-determinism, so only existence, not for all t'*)
Admitted.

Lemma red_subst sigma {s} {t} : 
  red s t -> {alphaSigmaT : term & prod (red (sigma [[s]]) alphaSigmaT) (Alpha [] alphaSigmaT (sigma [[t]]))}.
Proof. 
  intros Hred.
  induction Hred. 
  - exists (sigma [[s]]). split.
    + apply starR.
    + apply alpha_refl. constructor.
  - 
    apply (step_subst_sigma sigma) in e.
    
    destruct IHHred as [alphaSigmaY [Hred' Halpha] ].
    destruct e as [alphaSigmaZ [Hstep HalphaZ] ].
    eexists.
    admit. (* Doable with some alpha arguments*)
Admitted.

(* Lemma sred_up sigma tau : 
  sred sigma tau -> sred (up sigma) (up tau).
Proof. move=> A [|n] //=. asimpl. apply/red_subst/A. Qed. *)

Global Hint Resolve red_app red_abs 
(* sred_hup  *)
: red_congr.

(* Lemma red_compat sigma tau s :
  sred sigma tau -> red ([x := sigma] s) ([x := tau] s).
Proof.
  elim: s sigma tau; intros; asimpl; eauto with red_congr.
Qed. *)


(* NOTE: A little pen and paper study strongly suggests that this is still true for named. *)
(* NOTE: At first I would expect that it would step on the right hand side (instead of multistep=red)
    but it doesnt because of the following example:
    Let t1 = (\x.x)w and t2 = w (which steps by step_beta)
    Let s = \y. (\z. x) x
    Then [x := t1] s = \y. (\z. t1) t1 = \y. (\z. (\x.x) w) ((\x.x) w)
    And [x := t2] s = \y. (\z. t2) t2 = \y. (\z. w) w

    there is no single step from the first to the second, since we have to perform
    step_beta in two different places.
    *)

(* TODO: cant we make it a relation? mren rho1 (mren rho2 s) in Mren s*)
Lemma ren_comp rho1 rho2 s : exists rho', mren rho1 (mren rho2 s) = mren rho' s.
Proof.
  (* TODO: Figure out on pen and paper first.*)
Admitted.



Lemma rename_preserves_step x x' s t : 
step s t -> step (rename x x' s) (rename x x' t).
Proof.
  intros Hstep.
  induction Hstep.
  - destruct (x =? x0) eqn:xx0.
    + 
      assert (x = x0) by admit.
      subst.
      unfold rename.
      unfold mren. fold mren.
      assert (drop x0 [(x0, x')] = nil) by admit.
      rewrite H.
      rewrite mren_id.
      (* Since all x0 in s are replaced by t, we must turn the rhs into
        rename x0 x' [x0 := rename x0 x' t] s, exactly like lhs
      *)  
      assert (mren [(x0, x')] ([x0 := t] s) = [x0 := mren [(x0, x')] t] s) by admit.
      rewrite H0.
      apply step_beta.

    + 
    unfold rename.
    unfold mren. fold mren.
    assert (drop x0 [(x, x')] = ((x, x')::nil)) by admit.
    rewrite H.

    (* Bulk of the work: This is a special case of commute subst! *)
    assert (mren [(x, x')] ([x0 := t] s) = [x0 := mren [(x, x')] t] (mren [(x, x')] s)) by admit.
    rewrite H0.
    apply step_beta.
  - apply step_appL.
    assumption.
  - apply step_appR.
    assumption.
  - admit.
Admitted.

(* Strengthen IH for red_beta*)
Lemma red_beta_ren x s t1 t2 rho : step t1 t2 -> { someAlpha : term & prod (red ([x := t1] (mren rho s)) someAlpha)
            (Alpha [] someAlpha ([x := t2] (mren rho s))) }.
Proof.
  elim: s rho t1 t2 => [Y|Y K1 T_body IH|T1 IH1 T2 IH2] rho t1 t2 Hstep.
  - unfold mren.
    destruct (lookup Y rho) eqn: Hlookup.
    all: rewrite capms_equation_1.
    all: rewrite capms_equation_1.
    all: simpl.
    (* TODO: The two cases below are identical except for s vs Y*)
    + destruct (string_dec x s).
      * rewrite e.
        unfold lookup.
        rewrite eqb_refl.
        (* apply star1. *)
        (* assumption. *)
        admit.
      * unfold lookup.
        destruct (x =? s);
        admit.
        (* -- apply star1.
           assumption.
        -- apply starR. *)
    + destruct (string_dec x Y).
      * rewrite e.
        unfold lookup.
        rewrite eqb_refl.
        admit.
        (* apply star1.
        assumption. *)
      * unfold lookup.
        destruct (x =? Y);
        admit.
        (* -- apply star1.
           assumption.
        -- apply starR. *)
  - (* lambda abstraction *)
    simpl.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 [(Y, tmvar Y);(x, t1)] (mren (drop Y rho) T_body)) as x'.
    remember (fresh2 [(Y, tmvar Y);(x, t2)] (mren (drop Y rho) T_body)) as x2. (* x' and x2 only equal if we dont look at bound vars*)
    remember (drop Y rho) as rho'.
    specialize (IH ((Y, x')::rho') t1 t2 Hstep).
    destruct IH as [someAlpha [HredAlpha Halpha] ].

    (* exists (tmlam x' K1 someAlpha). *)
    eexists.
    split.

    + apply red_abs.

      (* What if Y is in the RHS of rho' ?*)
      assert (HrenComp: rename Y x' (mren rho' T_body) = mren ((Y, x')::rho') T_body).
      {
        admit.
      }
      rewrite HrenComp.
      exact HredAlpha. 
    + apply alpha_lam.

      admit.
  - rewrite capms_equation_3.
    rewrite capms_equation_3.
    (* apply red_app.
    + apply IH1.
      assumption.
    + apply IH2.
      assumption.  *)
Admitted.

Lemma red_beta x s t1 t2 : step t1 t2 -> red ([x := t1] s) ([x := t2] s).
Proof. 
  intros Hstep.
  induction s.
  - admit.
  - rewrite capms_equation_2. simpl.
    rewrite capms_equation_2. simpl.
    remember (fresh2 [(x, t1)] s0) as s0'.
    remember (fresh2 [(x, t2)] s0) as s0''.
    (* apply red_abs. *)
    
  (* move=> h. 
  apply red_beta_ren with (rho := nil) (x := x) (s := s) in h.
  rewrite mren_id in h. *)
  (* assumption. *)
Admitted.

(* Strong Normalization *)

(* used to be prop *)
Inductive sn {e : term -> term -> Set } x : Set :=
| SNI : (forall y, e x y -> sn y) -> sn x.

(*
Intuition:
h x is strongly normalizing.
then every reduction sequence starting from (h x) is finite.
The first condition (e x y -> e (h x) (h y)) says that each step has a corresponding step under h.
So in extension, each reduction chain starting from x has a corresponding reduction chain starting from h x.

So, since h x is SN, every reduction chain starting from h x is finite.
Then, by the extension, every reduction chain starting from x is finite.
*)
Lemma sn_preimage {e : term -> term -> Set} (h : term -> term) x :
  (forall x y, e x y -> e (h x) (h y)) -> @sn e (h x) -> @sn e x.
Proof.

  move eqn:(h x) => v A B.
  generalize dependent h.
  generalize dependent x.
  elim: B => {} v _ ih x h eqn.
  intros A.
  apply: SNI => y /A.
  

  
  rewrite eqn => /ih. eauto.
  Qed.

Lemma sn_preimage_alpha {e : term -> term -> Set} (h : term -> term) x :
  (forall x y, e x y -> { a : term & prod(Alpha [] (h y) a) (e (h x) a) }) -> 
  @sn e (h x) -> { a2 : term & prod(Alpha [] x a2) (@sn e a2)}.
Proof.
  (* move eqn:(h x) => v A B. elim: B h x A eqn => {} v _ ih h x A eqn.
  eexists.
  split.
  - admit.
  - 
  apply: SNI => y /A. rewrite eqn => /ih. apply/ih; eauto. *)
Admitted.

Notation SN := (@sn step).

Lemma sn_closedL t s : SN (tmapp s t) -> SN s.
Proof. apply: (sn_preimage (h := tmapp^~t)) => x y. exact: step_appL. Qed.

Lemma sn_subst sigma s : SN (sigma [[s]]) -> SN s.
Proof.
Admitted.

(* Not sure yet how to use the step_subst lemma in this*)
Lemma sn_subst_alpha sigma s : SN (sigma [[s]]) -> {alphaS & prod (Alpha [] alphaS s) (SN alphaS)}.
Proof.
  (* intros H.
  apply sn_preimage_alpha in H. 
    - destruct H as [alphaS [Halpha Hsn] ].
    exists alphaS.
      split.
      + eapply alpha_sym.
        * constructor.
        * assumption.
      + assumption.
    - intros x y Hstep.
      apply (@step_subst_sigma x y sigma) in Hstep.
      destruct Hstep as [alphaSigmaT [Hred Halpha] ].
      exists alphaSigmaT.
      split.
      * eapply alpha_sym.
        -- constructor.
        -- assumption.
      * assumption. *)
Admitted.



(* The Reducibility Candidates/Logical Predicate*)

Definition cand := term -> Set.

Definition neutral (s : term) : bool :=
  match s with
    | tmlam _ _ _ => false
    | _ => true
  end.

Record reducible (P : cand) : Set := {
  p_sn : forall s, P s -> SN s;
  p_cl : forall s t, P s -> step s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step s t -> P t) -> P s
}.

(* **** The logical relation for proving Strong normalization, 
        strengthens the IH to say something about labmda bodies*)
Fixpoint L (T : type) : cand :=
  match T with
    | tp_base => SN 
    | tp_arrow A B => fun s => forall t, L A t -> L B (tmapp s t)
  end.

(* TODO: Compare with Inductive instantiation from normalisation in
  PLF: that has a cleaner definition, but restraints the order*)
Definition EL (Gamma : list (string * type)) 
          (sigma : list (string * term)) : Set :=
  forall x T, lookup x Gamma = Some T ->
    { t & prod (lookup x sigma = Some t) (L T t)}.

(* is true! *)
Lemma extend_EL (Gamma : list (string * type)) (sigma : list (string * term)) x T t :
  EL Gamma sigma -> L T t -> EL ((x, T) :: Gamma) ((x, t) :: sigma).
Proof.
Admitted.

(* Facts about reducible sets. *)

Lemma reducible_sn : reducible SN.
Proof. 
  constructor; eauto using ARS.sn. by move=> s t [f] /f. 

  (*
  
  TODO INCOMPLETE
  
  *)
Admitted.
Global Hint Resolve reducible_sn : core.

Lemma reducible_var P x : reducible P -> P (tmvar x).
Proof. move/p_nc. apply=> // t st. inversion st. Qed.

Lemma L_reducible A :
  reducible (L A).
Proof with eauto using step.
  elim: A => /=[|A ih1 B ih2].
  - apply reducible_sn.
  - constructor.
    + move=> s h. apply: (@sn_closedL (tmvar "x")). apply: (p_sn (P := L B))...
      eapply h. eapply reducible_var; eauto.
    + move=> s t h st u la. apply: (p_cl _ (s := tmapp s u))...
    + move=> s ns h t la.
      have snt := p_sn ih1 la.
      elim: snt la => {} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      (* Note: Case L B ([x := t] s0. By using Autosubst's "inv" instead of normal inversion, this goal vanishes. Why? *) (* Todo: Think, this case doesn't happen in db variant*)
      * apply: ih3 => //. exact: (p_cl ih1) la _.
Qed.

Corollary L_sn A s : L A s -> SN s.
Proof. intros Las. assert (reducible (L A)) by apply (L_reducible A).
   apply (p_sn H). assumption.
Qed.

Corollary L_cl T s t : L T s -> step s t -> L T t.
Proof.
  intros Hstep Hst.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_cl H Hstep); assumption.
Qed.

Corollary L_nc T s :
  neutral s -> (forall t, step s t -> L T t) -> L T s.
Proof. 
  intros Hneut Hstep.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_nc H); assumption.
Qed.

Corollary L_var T x : L T (tmvar x).
Proof.
  apply L_nc; first by []. intros t st. inversion st.
Qed. 

Corollary L_cl_star T s t :
  L T s -> red s t -> L T t.
Proof.
  intros Ls red_st. induction red_st.
  - assumption.
  - apply L_cl with y; assumption.
Qed.

(* Closure under beta expansion. *)
Lemma beta_expansion A B x s t :
  SN t -> L A ([x := t] s) ->
  L A (tmapp (tmlam x B s) t).
Proof with eauto.
  move=> snt h. have sns := sn_subst (L_sn h).
  elim: sns t snt h => {} s sns ih1 t. elim=> {} t snt ih2 h.
  apply: L_nc => // u st. inv st => //.
  - inv H2. apply: ih1 => //. apply: L_cl h _. admit. (* exact: step_subst. *) (* need to alphafy this lemma *)
  - apply: ih2 => //. apply: L_cl_star h _. exact: red_beta.
Admitted.

Lemma beta_expansion_subst X t sigma s A B :
  SN t -> L A (((X, t)::sigma) [[s]]) -> L A (tmapp (sigma [[tmlam X B s]]) t).
Proof.
  intros snt H.
  remember (fresh2 ((X, tmvar X)::sigma) s) as X'.
  assert (L A ([X' := t] (sigma [[(rename X X' s)]])) -> L A (tmapp (tmlam X' B (sigma [[rename X X' s]])) t)).
  {
    apply beta_expansion; assumption.
  }

  (* Now we use H to show the assumption of H0 holds. Then we rewrite the conclusion into the goal*)
  assert (HsigIntoLam: tmapp (tmlam X' B (sigma [[rename X X' s]])) t = tmapp (sigma [[tmlam X B s]]) t).
  {
    rewrite capms_lam.
    rewrite HeqX'.
    reflexivity.
  }
  rewrite <- HsigIntoLam.
  apply H0.
  rewrite composeCapms.
  - rewrite capmsRename.
    assumption.
  - rewrite -> HeqX'.
    (* apply freshLemma. easy by freshness*)
    shelve.
Admitted.

(** Kinding of types *)
Reserved Notation "Δ '|-*' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_type : list (string * type) -> term -> type -> Set :=
  | K_Var : forall Δ X K,
      List.lookup X Δ = Some K ->
      Δ |-* (tmvar X) : K
  | K_Lam : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-* T : K2 ->
      Δ |-* (tmlam X K1 T) : (tp_arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-* T1 : (tp_arrow K1 K2) ->
      Δ |-* T2 : K1 ->
      Δ |-* (tmapp T1 T2) : K2
where "Δ '|-*' T ':' K" := (has_type Δ T K).

(* The fundamental theorem. *)
Theorem soundness Gamma s A :
  has_type Gamma s A -> forall sigma,
    EL Gamma sigma -> L A (sigma [[s]]).
Proof with eauto using L_sn. 
  elim=> {Gamma s A} [Gamma X A |Gamma X A s B _ ih sigma EL|Gamma s t A B _ ih1 _ ih2 sigma HEL].
  - intros HlookupGamma sigma HEL.
    unfold EL in HEL.
    specialize (HEL X A HlookupGamma).
    destruct HEL as [t [HlookupSigma LAt] ].
    apply capms_var in HlookupSigma.
    rewrite HlookupSigma.
    assumption.
  - move=> t h.
    specialize (ih ((X, t)::sigma) (extend_EL EL h)).
    apply: beta_expansion_subst...
  - specialize (ih1 _ HEL). specialize (ih2 _ HEL).
    unfold L in ih1. fold L in ih1. specialize (ih1 (sigma [[t]]) ih2).
    rewrite capms_equation_3.
    assumption.
Admitted.

(* Identity substitutions: Given a typing context E, give a list of term substitutions matching this E*)
Fixpoint id_subst (E : list (string * type)) : list (string * term) :=
  match E with
  | nil => nil
  | cons (x, A) E' => cons (x, tmvar x) (id_subst E')
  end.



(* The identity substitution is in the EL relation *)

Lemma id_subst_EL :
  forall (E : list (string * type)),  EL E (id_subst E).
Proof.
Admitted.

(* TODO id_ren E could just be []? *)
Lemma id_subst_alpha_type E s T :
  has_type E s T -> Alpha [] s ((id_subst E) [[s]]).
Proof.
Admitted.

(* The fundamental theorem for named variables. *)
Corollary type_L (E : list (string * type)) s T : has_type E s T -> L T (id_subst E [[s]]).
Proof.
  intros Htype.
  assert (HEL: EL E (id_subst E)) by apply id_subst_EL.
  assert (Hsound: L T ((id_subst E) [[s]])) by apply (soundness Htype HEL).
  assumption.
Qed.

Corollary strong_normalization_alpha E s T : has_type E s T -> SN (id_subst E [[s]]).
Proof.
  intros Hty.
  apply type_L in Hty.
  apply L_sn in Hty.
  assumption.
Qed.

(* Monad maybe*)
(* Define the bind function for option type *)
Definition bind {A B : Type} (xx : option A) (f : A -> option B) : option B :=
  match xx with
  | None => None
  | Some a => f a
  end.

Fixpoint is_normal (t : term) : bool :=
  match t with
  | tmlam X K T => is_normal T
  | tmvar X => true
  | tmapp T1 T2 => is_neutral T1 && is_normal T2
  end

with is_neutral (t : term) : bool :=
  match t with
  | tmvar X => true
  | tmapp T1 T2 => is_neutral T1 && is_normal T2
  | _ => false
  end.

  (** Normal types *)
Inductive normal_Ty : term -> Prop :=
  | NO_TyLam : forall x K T,
      normal_Ty T ->
      normal_Ty (tmlam x K T)
  | NO_neutral : forall T,
      neutral_Ty T ->
      normal_Ty T

with neutral_Ty : term -> Prop :=
  | NE_TyVar : forall X,
      neutral_Ty (tmvar X)
  | NE_TyApp : forall T1 T2,
      neutral_Ty T1 ->
      normal_Ty T2 ->
      neutral_Ty (tmapp T1 T2).

(* Define an infix operator for bind *)
Infix ">>=" := bind (at level 50, left associativity).

(* Deterministic step *)
Fixpoint step_d_f (t : term) : option term :=
    match t with
    | tmvar i => None
    | tmapp s t => 
        if is_normal s then
            if is_normal t then
                match s with
                | tmlam x A s' => Some ([x := t] s')
                | _ => None
                end
            else step_d_f t >>= fun t' => Some (tmapp s t')
        else step_d_f s >>= fun s' => Some (tmapp s' t)
    | tmlam x A s => (* step' s >>= _ does the normality check for us implicitly*)
        step_d_f s >>= fun s' => Some (tmlam x A s')
    end.

Inductive step_d : term -> term -> Set :=
| step_beta_d (x : string) (A : type) (s t : term) :
    normal_Ty s ->
    normal_Ty t ->
    step_d (tmapp (tmlam x A s) t) ([x := t] s)
| step_appL_d s1 s2 t :
    step_d s1 s2 -> step_d (tmapp s1 t) (tmapp s2 t)
| step_appR_d s t1 t2 :
    normal_Ty s ->
    step_d t1 t2 -> step_d (tmapp s t1) (tmapp s t2)
| step_abs_d x A s1 s2 :
    step_d s1 s2 -> step_d (tmlam x A s1) (tmlam x A s2).


(* step_nd is a subset of step
This is not true since step_d should use a different kind of substitution (only freshening when necessary)
*)
Lemma step_d_implies_step t t' : step_d t t' -> step t t'.
Proof.
  (* elim=> H; constructor; try assumption. *)
Abort.

Lemma step_d_implies_step_alpha t t' : step_d t t' -> { t'_alpha : term & prod(Alpha [] t' t'_alpha) (step t t'_alpha)}.
Proof.
  intros Hstep.
  induction Hstep.
  - (* this is proving that if substituteTCA x t s is alpha to [x := t] s (capmsfr)*) admit.
  - admit.
  - admit.
  - destruct IHHstep as [IHHt' [IHHalpha IHHstep'] ].
    exists (tmlam x A IHHt').
    split.
    + apply alpha_lam.
      apply alpha_extend_id'.
      * assumption.
      * apply not_break_shadow_nil.
    + apply step_abs.
      assumption.
Admitted.

(* Does this still work now we no longer have step_d_implies_step?
  Maybe if we make it up to alhpa
 *)
Lemma SN_d : forall t, (@sn step) t -> {t_alpha : term & prod (Alpha [] t t_alpha) ((@sn step_d) t_alpha)}.
Proof.
  intros t HSN.
  induction HSN.
  eexists.
  split.
  - admit.
  - (* oof. I dont know how to prove this. Maybe we need a weaker SN notion or something:
    @sn step_d x -> exists z, Alpha [] x z AND forall y, step z y -> SN y
   *)
Admitted.

(* Main lemma for going from using t alpha t' in SN t' to SN t*)
Lemma step_preserves_alpha_d sigma s t s' t' :
  Alpha sigma s t -> step_d s s' -> step_d t t' -> Alpha sigma s' t'.
Proof.
Admitted.

Require Import Coq.Program.Equality.

(*I do not like these lemmas. Maybe we can change the definition of normality to equal not being able to step? *)
Lemma is_normal_no_step_d t :
  is_normal t = true -> step_d_f t = None.
Proof.
Admitted.

Lemma is_normal_then_step_d t :
  is_normal t = false -> ~ step_d_f t = None.
Proof.
Admitted.

(* We also need this for sound/completeness, so we can assume it is true/a good approach*)
Lemma is_normal_then_normal_Ty t : 
  is_normal t = true -> normal_Ty t.
Proof.
Admitted.


Lemma step_d_f_to_step_d : forall t t', step_d_f t = Some t' -> step_d t t'.
Proof.
  intros t t' Hstep_d_f.
  dependent induction t. (* we needed IH over t' *)
  - discriminate.
  - destruct (is_normal t0) eqn: Hnormal_s.
    + apply is_normal_no_step_d in Hnormal_s.
      inversion Hstep_d_f.
      rewrite Hnormal_s in H0.
      inversion H0.
      (* If t0 is normal, then also tmlam s t t0*)
    + destruct (step_d_f t0) eqn: Hstep_t.
      * inversion Hstep_d_f.
        rewrite Hstep_t in H0.
        inversion H0.
        apply step_abs_d.
        specialize (IHt t1).
        apply IHt.
        reflexivity.
      * apply is_normal_then_step_d in Hnormal_s.
        contradiction.
  - inversion Hstep_d_f.
    destruct (is_normal t1) eqn: Hnormal_s.
    + destruct (is_normal t2) eqn: Hnormal_t.
      * destruct t1. (* case step_beta *)
        -- discriminate.
        -- inversion Hnormal_s.
           inversion Hnormal_t.
           inversion H0.
           apply step_beta_d.
           ++ apply is_normal_then_normal_Ty.
              assumption. (* is_normal -> normal_ty, we need that anyway for sound/completeness*)
           ++ apply is_normal_then_normal_Ty.
              assumption.
        -- discriminate.
      * destruct (step_d_f t2) eqn: Hstep_t. (* IH was not strong enough, so dependent induction *)
        -- inversion H0.
           apply step_appR_d.
           ++ apply is_normal_then_normal_Ty.
              assumption.
           ++ apply IHt2. 
              reflexivity.
        -- discriminate.
    + destruct (step_d_f t1) eqn: Hstep_s.
      * inversion H0.
        apply step_appL_d.
        apply IHt1.
        reflexivity.
      * discriminate.
Qed.

(* eq_refl didnt work, this does, thank Copilot, but I dont understand *)
Lemma eq_proof {A : Type} (x : A) : x = x.
Proof. reflexivity. Qed.

(* Terminating normalization procedure helper.
  We can normalize a term given that we know that an 
  alpha equivalent term is strongly normalizing
*)
Fixpoint normalizer' {sigma : list (string * string)} (t t' : term) (HAlpha : Alpha sigma t t') (HSN : (@sn step_d) t') : term :=
  match step_d_f t as res return (step_d_f t = res -> term) with
  | None => fun _ => t
  | Some t1 => fun Hstep =>
      match step_d_f t' as res' return (step_d_f t' = res' -> term) with
      | None => fun _ => t1 (* Uhm. Cannot happen. How to show this to coq? *)
      | Some t'1 => fun Hstep' =>
          let HStep_d := step_d_f_to_step_d Hstep in
          let HStep_d' := step_d_f_to_step_d Hstep' in
          let HAlpha' := step_preserves_alpha_d HAlpha HStep_d HStep_d' in
          let HSN' := match HSN with
                      | SNI f => f t'1 HStep_d'
                      end in
          @normalizer' sigma t1 t'1 HAlpha' HSN'
      end (eq_proof (step_d_f t'))
  end (eq_proof (step_d_f t)).

(* Normalization procedure for well typed terms *)
Definition normalizer E T (t : term) (Htype : has_type E t T) : term :=
  let t' := id_subst E [[t]] in
  let HAlpha := @id_subst_alpha_type E t T Htype in
  let HSN := strong_normalization_alpha Htype in
  let (t'', p ) := SN_d HSN in
  let (HAlpha', SNstep_d_t'') := p in

    (* HAlpha says Alpha [] t t'
       HAlpha' says Alpha [] t' t''
       
    Hence by transitivity: Alpha [] t t''
    *)
  let HAlphaTrans := alpha_trans alpha_trans_nil HAlpha HAlpha' in
      @normalizer' [] t t'' HAlphaTrans SNstep_d_t''.


(* Local Variables: *)
(* coq-load-path: (("." "Ssr")) *)
(* End: *)


*)