Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.

Require Import Coq.Logic.FunctionalExtensionality.


Definition P_Term (t : Term) :=
  forall Delta Gamma x U Un v T,
    Delta ,, (x |-> U; Gamma) |-+ t : T ->
    normalise U Un ->
    empty ,, empty |-+ v : Un ->
    Delta ,, Gamma |-+ <{ [v / x] t }> : T.

Definition P_Binding (b : Binding) : Prop :=
  forall Delta Gamma x U Un v,
    Delta ,, (x |-> U; Gamma) |-ok_b b ->
    normalise U Un ->
    empty ,, empty |-+ v : Un ->
    Delta ,, Gamma |-ok_b <{ [v / x][b] b }> /\ 
    binds_Delta b = binds_Delta <{ [v / x][b] b }> /\
    binds_Gamma b = binds_Gamma <{ [v / x][b] b}>.

#[export] Hint Unfold
  P_Term
  P_Binding
  : core.

Lemma P_letnonrec : forall bs t Delta Gamma x U Un v T,
    P_Term t ->
    Delta ,, (x |-> U; Gamma) |-+ (Let NonRec bs t) : T ->
    normalise U Un ->
    empty ,, empty |-+ v : Un ->
    Util.ForallP P_Binding bs ->
    Delta ,, Gamma |-+ <{ [v / x] {Let NonRec bs t} }> : T /\ 
    List.map binds_Delta bs = List.map binds_Delta <{ [v / x][bnr] bs }> /\
    List.map binds_Gamma bs = List.map binds_Gamma <{ [v / x][bnr] bs }>.
Proof with (eauto with typing).
  induction bs; intros.
  - simpl.
    split...
    eapply T_Let...
    + simpl.
      eapply H...
      inversion H0. subst.
      simpl in H12.
      simpl in H7.
      inversion H7. subst.
      eauto.
    + inversion H0. subst...
  - admit.
Admitted.

Lemma P_letrec : forall bs t Delta Gamma x U Un v T,
    P_Term t ->
    Delta ,, (x |-> U; Gamma) |-+ (Let Rec bs t) : T ->
    normalise U Un ->
    empty ,, empty |-+ v : Un ->
    Util.ForallP P_Binding bs ->
    Delta ,, Gamma |-+ <{ [v / x] {Let Rec bs t} }> : T /\ 
    List.map binds_Delta bs = List.map binds_Delta <{ [v / x][br] bs }> /\
    List.map binds_Gamma bs = List.map binds_Gamma <{ [v / x][br] bs}>.
Proof with (eauto with typing).
  induction bs; intros.
  - simpl.
    split...
    eapply T_LetRec...
    + simpl.
      eapply H...
      inversion H0. subst.
      simpl in H12.
      simpl in H7.
      inversion H7. subst.
      eauto.
    + inversion H0. subst...
  - admit.
Admitted.

Lemma substitution_preserves_typing : 
  (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof with eauto.
  apply Term__multind with 
    (P := P_Term) 
    (Q := P_Binding).
  all: intros; autounfold; intros.
  all: try solve [try (inversion H || inversion H0 || inversion H1); subst; eauto with typing].
  - destruct rec.
    + simpl.
      all: eapply P_letnonrec; eauto.
    + simpl.
      all: eapply P_letrec; eauto.
  - simpl.
    destruct (x =? s)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      inversion H.
      subst.
      rewrite update_eq in H3.
      inversion H3. subst.
      assert (Un = T) by eauto using normalisation__deterministic.
      subst.
      eapply Typing.weakening_empty; eauto.
    + apply eqb_neq in Heqb as Hneq.
      inversion H. subst.
      eapply T_Var...
      rewrite update_neq in H3...
  - (* LamAbs *)
    inversion H0. subst.
    simpl.
    destruct (x =? s)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq. 
      subst.
      apply T_LamAbs...
      rewrite update_shadow in H11...
    + apply eqb_neq in Heqb as Hneq.
      apply T_LamAbs...
      rewrite update_permute in H11...
Admitted.

Corollary substitution_preserves_typing__Term : forall t Delta Gamma x U Un v T,
    Delta ,, (x |-> U; Gamma)  |-+ t : T ->
    normalise U Un ->
    empty ,, empty |-+ v : Un ->
    Delta ,, Gamma |-+ <{ [v / x] t }> : T.
Proof. apply substitution_preserves_typing. Qed.

Corollary substitution_preserves_typing__Binding : forall b Delta Gamma x U Un v,
    Delta ,, (x |-> U; Gamma) |-ok_b b ->
    normalise U Un ->
    empty ,, empty |-+ v : Un ->
    Delta ,, Gamma |-ok_b <{ [v / x][b] b }> /\ 
    binds_Delta b = binds_Delta <{ [v / x][b] b }> /\
    binds_Gamma b = binds_Gamma <{ [v / x][b] b }>.
Proof. apply substitution_preserves_typing. Qed.