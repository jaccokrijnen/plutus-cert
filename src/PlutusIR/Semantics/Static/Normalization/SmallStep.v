From PlutusCert Require Import PlutusIR Normalization.BigStep Util.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.


(* Deterministic step function for PlutusIR type system *)
Inductive step : ty -> ty -> Set :=
    | step_beta (X : string) (K : kind) (S T : ty) :
        normal_Ty S ->
        normal_Ty T ->
        step (Ty_App (Ty_Lam X K S) T) (substituteTCA X T S)
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
        step T1 T2 -> step (Ty_IFix F T1) (Ty_IFix F T2)
    | step_SOP Tss_normal Tss_sub_normal Tss_sub1 Tss_sub2 Tss_sub_remainder Tss_remainder :
        (* List of list of types, we can reduce if only one of them steps, and everything "before" it is normal *)
        ForallSet2 normal_Ty Tss_normal ->  (* Tss_normal can be empty, so this allows all reductions*)
        ForallSet normal_Ty Tss_sub_normal -> (* The inner list should also have normal types before the type that is stepping*)
        step Tss_sub1 Tss_sub2 ->
        step (Ty_SOP (Tss_normal ++ (Tss_sub_normal ++ Tss_sub1 :: Tss_sub_remainder) :: Tss_remainder))
             (Ty_SOP (Tss_normal ++ (Tss_sub_normal ++ Tss_sub2 :: Tss_sub_remainder) :: Tss_remainder))
    .

(* step as a partial function *)
Function stepf (U : ty) : option ty :=
  match U with
  | Ty_Var _ => None
  | Ty_Builtin _ => None

  | Ty_App T U =>
    match stepf T with
    | Some T' => Some (Ty_App T' U)
    | None =>
      match stepf U with
      | Some U' => Some (Ty_App T U')
      | None =>
        match T with
        | Ty_Lam X _ T => Some (substituteTCA X U T)
        | _ => None (* normal (neutral) *)
        end
      end
    end

  | Ty_Fun T U =>
    match stepf T with
    | Some T' => Some (Ty_Fun T' U)
    | None =>
      match stepf U with
      | Some U' => Some (Ty_Fun T U')
      | None => None (* normal *)
      end
    end

  | Ty_Forall X K T =>
    match stepf T with
    | Some T' => Some (Ty_Forall X K T')
    | None => None (* normal *)
    end

  | Ty_Lam X K T =>
    match stepf T with
    | Some T' => Some (Ty_Lam X K T')
    | None => None (* normal *)
    end

  | Ty_IFix T U =>
    match stepf T with
    | Some T' => Some (Ty_IFix T' U)
    | None =>
      match stepf U with
      | Some U' => Some (Ty_IFix T U')
      | None => None (* normal *)
      end
    end


  | Ty_SOP Tss => None (* TODO *)

  end
.

From PlutusCert Require Import Util.Tactics Kinding.Kinding.

(* If T is well-kinded and stepf returns None, then it was a normal type *)
Lemma stepf_normal T : (exists Δ K, has_kind Δ T K) -> stepf T = None -> normal_Ty T.
Proof.
  destruct 1 as [? [? HWK]]. induction HWK; rewrite stepf_equation; repeat destruct_match.
  all: try now (inversion 1).
  all: try auto using normal_Ty.
  - (* neutral case:
         step (Ty_App (Ty_App _ _) _) _
    *)
    specialize (IHHWK1 eq_refl).
    inversion IHHWK1.
    auto using normal_Ty.
  - admit.
    (* TODO, does not hold yet: implement that case in stepf *)
Admitted.

(* Boiler-plate tactic for passing around well_kinded proofs. Using exists to
 * avoid scoping issues in eapply. This was particularly tricky because step
 * is in Set, whereas has_kind is in Prop.
 *)
Ltac inv_well_kinded :=
  match goal with
  | H : exists _ _, has_kind _ _ _ |- exists _ _, has_kind _ _ _ =>
      now ( destruct H as [? [? H_WK]]
          ; inversion H_WK
          ; repeat eexists
          ; eassumption )
  end.


(* Let eauto use tactic when encoutering well-kinded proof *)
Hint Extern 10 (exists _ _, has_kind _ _ _) => inv_well_kinded : core.

(* stepf is sound with respect to step.

   Since this proof is in Set it is impossible to use inversion on Props, which
   the proof depends on (has_kind and normal_Ty). The way to do this is by using
   specific inversion lemmas, which make it clear that the outcome of the lemma
   will not depend on computation on Prop.
*)
Lemma stepf_sound (T T' : ty) : (exists Δ K, has_kind Δ T K) -> stepf T = Some T' -> step T T'.
Proof.
  revert T'. induction T; intros T' H_WK;
  rewrite stepf_equation; repeat destruct_match.
  all: try now (inversion 1).
  all: intros H; inversion H; subst T'; clear H.
  all: try now eauto using step, stepf_normal.

  (* step_beta *)
  apply step_beta.
  - apply stepf_normal in Heqo.
    inversion Heqo.
    + assumption.
    + inversion H.
    + inv_well_kinded.
  - apply stepf_normal.
    + inv_well_kinded.
    + assumption.
Qed.
