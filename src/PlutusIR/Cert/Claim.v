From PlutusCert Require Import
  Cert.Relation

  PlutusIR
  Dynamic.Bigstep
  SemanticEquivalence.Contextual
.

Inductive claim :=
  | Verified : rel_verified -> claim
  | Related  : rel_decidable -> claim
  | Unknown  : claim
.

Definition claim_prop : claim -> (term -> term -> Prop) := fun c t t' =>
  match c with
  | Verified rv => forall Δ Γ T, Δ ,, Γ |- t ≃-ctx t' : T
  | Related rd  => rd_rel rd t t'
  | Unknown     => True
  end
.

Definition claim_decb : claim -> (term -> term -> bool) := fun c =>
  match c with
  | Verified rv => rd_decb (rv_rd rv)
  | Related rd  => rd_decb rd
  | Unknown     => fun t t' => true
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
    | Related rd  => rd_dec rd t t'
    | Unknown     => Some I
  end
.


Require Import Lists.List.
Import ListNotations.

(* Deciding trace claims *)

Fixpoint trace_prop' (ps : list (pass * term)) : forall (claims : pass -> claim) (t : term), Prop :=
    fun claims t => match ps with
      | [] => True
      | (p, t') :: ps => claim_prop (claims p) t t' /\ trace_prop' ps claims t'
    end.

Definition trace_prop : (pass -> claim) -> compilation_trace -> Prop :=
  fun claims ct =>
  match ct with
  | CompilationTrace t0 ps => trace_prop' ps claims t0
  end.

Fixpoint trace_dec' (claims : pass -> claim) (t : term) (ps : list (pass * term))
  : option (trace_prop' ps claims t) :=
  match ps return option (trace_prop' ps claims t) with
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
  : option (trace_prop claims ct) :=
  match ct with
  | CompilationTrace t0 ps => trace_dec' claims t0 ps
  end
.
