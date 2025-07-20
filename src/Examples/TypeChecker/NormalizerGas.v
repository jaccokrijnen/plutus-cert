From PlutusCert Require Import PlutusIR Kinding.Kinding Normalizer.

Require Import Lists.List.
Import ListNotations.

Require Import Strings.String.
Open Scope string.

(* A beta reduction *)
Definition ty1 :=
  Ty_App (Ty_Lam "x" Kind_Base (Ty_Var "x")) (Ty_Var "y").

Lemma ty1_kinding : [("y", Kind_Base)] |-* ty1 : Kind_Base.
Proof.
  unfold ty1.
  eauto using has_kind.
Defined.

Goal normalizer_gas 99999999 ty1_kinding = Ty_Var "y".
Proof. reflexivity. Qed.

Import PIRNotations.
Open Scope pir_scope.
(* More advanced beta reduction that requires capture avoidance *)
Definition ty2 :=
  (λ* "X" ★
     λ* "Y" ★
       `* "X") ⋅* (`* "Y").

Lemma ty2_kinding : [("Y", ★)] |-* ty2 : (★ ⇒ ★).
Proof.
  unfold ty2.
  eauto 10 using has_kind.
Defined.


(* Does not fully reduce because substituteTCA_preserves_kinding relies on admitted
 * lemmas. *)
Goal normalizer_gas 2 ty2_kinding = λ* "aXYX" ★ (`* "Y").
Abort.
