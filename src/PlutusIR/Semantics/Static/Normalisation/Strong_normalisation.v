From PlutusCert Require Import PlutusIR Type_reduction Kinding.Kinding.

Inductive sn {e : ty -> ty -> Set } x : Set :=
| SNI : (forall y, e x y -> sn y) -> sn x.

Notation SN := (@sn step).

Theorem strong_normalisation {Δ T K} : (Δ |-* T : K) -> SN T.
Admitted.