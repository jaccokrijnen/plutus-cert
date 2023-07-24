Require Import PlutusCert.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.


Theorem unique_kinds : forall ctx T K K',
    ctx |-* T : K ->
    ctx |-* T : K' ->
    K = K'.
Proof.
  intros ctx T K K' Hkind1.
  generalize dependent K'.
  induction Hkind1; intros K' Hkind2.
  - (* K_Var *)
    inversion Hkind2. subst.
    rewrite H in H2.
    inversion H2. subst.
    reflexivity.
  - (* K_Fun *)
    inversion Hkind2. subst.
    reflexivity.
  - (* K_IFix *)
    inversion Hkind2. subst.
    reflexivity.
  - (* K_Forall *)
    inversion Hkind2. subst.
    reflexivity.
  - (* K_Builtin *)
    inversion Hkind2. subst.
    reflexivity.
  - (* K_Lam *)
    inversion Hkind2. subst.
    f_equal.
    apply IHHkind1.
    assumption.
  - (* K_App *)
    inversion Hkind2. subst.
    apply IHHkind1_2 in H4.
    subst.
    apply IHHkind1_1 in H2.
    inversion H2.
    subst.
    reflexivity.
Qed.