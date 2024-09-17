From PlutusCert Require Import STLC_DB.
From PlutusCert Require Import Normalisation_STLC_DB.
From PlutusCert Require Import SN_F.
From PlutusCert Require Import ARS.

(* Monad maybe*)
(* Define the bind function for option type *)
Definition bind {A B : Type} (xx : option A) (f : A -> option B) : option B :=
  match xx with
  | None => None
  | Some a => f a
  end.

(* Define an infix operator for bind *)
Infix ">>=" := bind (at level 50, left associativity).

Fixpoint step' (t : STLC_DB.term) : option STLC_DB.term :=
    match t with
    | tmvar i => None
    | tmapp s t => 
        if is_normal s then
            if is_normal t then
                match s with
                | tmlam A s' => Some s'.[t/]
                | _ => None
                end
            else step' t >>= fun t' => Some (tmapp s t')
        else step' s >>= fun s' => Some (tmapp s' t)
    | tmlam A s => (* step' s >>= _ does the normality check for us implicitly*)
        step' s >>= fun s' => Some (tmlam A s')
    end.

Lemma step'_implies_step_nd : forall t t',
  step' t = Some t' -> SN_F.step t t'.
Proof. Admitted.

Definition step_with_proof (t : term) : option {t' : term | SN_F.step t t'} :=
  match step' t with
  | None => fun _ => None
  | Some t' => fun Heq => (* Doing this function syntax thing to be able to use the equality hypothesis *)
      let H_step := step'_implies_step_nd t t' Heq in
      Some (exist _ t' H_step)
  end eq_refl.

Fixpoint normalizer' (t : term) (H_sn : SN t) : (forall t, option {t' | SN_F.step t t'}) -> term :=
    fun stepper => match stepper t with
    | None => t
    | Some (exist t' H_step) => match H_sn with
        | SNI f => normalizer' t' (f t' H_step) stepper
        end
end.

(* Step t according to step' until we reach a value, i.e. normalise it*)
Definition normalizer (t : term) (H_sn : SN t) : term :=
    normalizer' t H_sn step_with_proof.