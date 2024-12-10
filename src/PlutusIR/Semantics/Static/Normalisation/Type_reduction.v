From PlutusCert Require Import PlutusIR Normalisation.Normalisation.

Require Import Coq.Strings.String.

(* Deterministic step function for PlutusIR type system *)
Inductive step : ty -> ty -> Set :=
    | step_beta (X : string) (K : kind) (S T : ty) :
        normal_Ty S ->
        normal_Ty T ->
        step (Ty_App (Ty_Lam X K S) T) (substituteTCA X T S) (* conservative substitutions *)
    | step_appL S1 S2 T :
        step S1 S2 -> step (Ty_App S1 T) (Ty_App S2 T)
    | step_appR S T1 T2 :
        normal_Ty S ->
        step T1 T2 -> step (Ty_App S T1) (Ty_App S T2)
    | step_funL S1 S2 T :
        step S1 S2 -> step (Ty_Fun S1 T) (Ty_Fun S2 T)
    | step_funR S T1 T2 :
        normal_Ty S ->
        step T1 T2 -> step (Ty_Fun S T1) (Ty_Fun S T2)
    | step_forall bX K S1 S2 :
        step S1 S2 -> step (Ty_Forall bX K S1) (Ty_Forall bX K S2)
    | step_abs bX K T1 T2 :
        step T1 T2 -> step (Ty_Lam bX K T1) (Ty_Lam bX K T2)
    | step_ifixL F1 F2 T :
        step F1 F2 -> step (Ty_IFix F1 T) (Ty_IFix F2 T)
    | step_ifixR F T1 T2 :
        normal_Ty F ->
        step T1 T2 -> step (Ty_IFix F T1) (Ty_IFix F T2).
    