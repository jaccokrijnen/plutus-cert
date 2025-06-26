Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Static.Kinding.Checker.

Require Import PlutusCert.PlutusIR.Semantics.Static.Normalization.Normalizer_sound_complete.

From PlutusCert Require Import SN_PIR Normalizer.

Theorem strong_normalisation Δ T K :
    Δ |-* T : K ->
    exists Tn, normalise T Tn.
Proof.
    intros Hkind.
    remember Hkind as Hkind'. clear HeqHkind'.
    apply strong_normalization_PIR in Hkind.
    assert ({Tn & normalise T Tn}) as [Tn Hnorm].
    {
        eapply SN_normalise; eauto.
    }
    exists Tn.
    assumption.
Qed.