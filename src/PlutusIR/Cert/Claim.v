From PlutusCert Require Import
  Cert.Relation

  PlutusIR
  Dynamic.Bigstep
  SemanticEquivalence.Contextual
.

Require Import Lists.List.
Import ListNotations.

Section Claims.

  Inductive claim :=
    | Unchecked : claim
    | AccordingToSpec  : rel_decidable -> claim
    | Verified : rel_verified -> claim
  .

  (* Interpret a claim as a Prop on terms *)
  Definition claim_prop : claim -> (term -> term -> Prop) := fun c t t' =>
    match c with
    | Verified rv => forall Δ Γ T, Δ ,, Γ |- t =ctx t' : T
    | AccordingToSpec rd  => rd_rel rd t t'
    | Unchecked     => True
    end
  .

  Definition claim_decb : claim -> (term -> term -> bool) := fun c =>
    match c with
    | Verified rv => rd_decb (rv_rd rv)
    | AccordingToSpec rd  => rd_decb rd
    | Unchecked     => fun t t' => true
    end
  .

  Definition claim_decb_eq (c : claim) (t t' : term) : option (claim_decb c t t' = true)
    := match claim_decb c t t' with
      | true  => Some eq_refl
      | false => None
    end.

  Definition claim_dec (c : claim) (t t' : term) : option (claim_prop c t t') :=
    match c return option (claim_prop c t t') with
      | Verified rv => rv_dec rv t t'
      | AccordingToSpec rd  => rd_dec rd t t'
      | Unchecked     => Some I
    end
  .

  Fixpoint claims_prop' (ps : list (pass * term)) :
    (pass -> claim) -> term -> Prop :=
      fun claims t_pre => match ps with
        | [] => True
        | (p, t_post) :: ps => claim_prop (claims p) t_pre t_post /\ claims_prop' ps claims t_post
      end.

  Definition claims_prop : (pass -> claim) -> compilation_trace -> Prop :=
    fun claims ct =>
    match ct with
    | CompilationTrace t0 ps => claims_prop' ps claims t0
    end.

  Fixpoint trace_dec' (claims : pass -> claim) (t : term) (ps : list (pass * term))
    : option (claims_prop' ps claims t) :=
    match ps return option (claims_prop' ps claims t) with
    | [] => Some I
    | (p, t') :: ps =>
      match claim_dec (claims p) t t' with
      | Some proof =>
        match trace_dec' claims t' ps with
        | Some proofs => Some (conj proof proofs)
        | None => None
        end
      | None => None
      end
    end
  .

  Definition trace_dec (claims : pass -> claim) (ct : compilation_trace)
    : option (claims_prop claims ct) :=
    match ct with
    | CompilationTrace t0 ps => trace_dec' claims t0 ps
    end
  .

End Claims.



Definition default_claims : pass -> claim := fun p =>
  match p with
  | PassTypeCheck => AccordingToSpec rd_equal
  (* | PassRename    => AccordingToSpec rd_rename *)
  | PassDeadCode  => AccordingToSpec rd_deadcode
  | PassCompileLetNonRec => Verified let_nonrec
  | _             => Unchecked
  end
.
