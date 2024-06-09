From PlutusCert Require Import
  Equality
  PlutusIR
  Contextual
.

Import Utf8_core.

Record rel_decidable : Type :=
  mk_rel_decidable {
    rd_rel : term -> term -> Prop;
    rd_decb : term -> term -> bool;
    rd_equiv : ∀ s t,
      rd_decb s t = true <-> rd_rel s t;
  }
.

Definition rd_dec (rd : rel_decidable) (t t' : term) : option (rd_rel rd t t') :=
  match rd_decb rd t t' as b return rd_decb rd t t' = b -> option (rd_rel rd t t') with
    | true  => fun H => Some (proj1 (rd_equiv rd t t') H)
    | false => fun _ => None
  end eq_refl.

Record rel_verified : Type :=
  mk_rel_verified {
    rv_rd : rel_decidable;
    rv_correct : ∀ s t,
      rv_rd.(rd_rel) s t -> ∀ Δ Γ T, Δ ,, Γ |- s ≃-ctx t : T
  }
.

Definition rv_dec (rv : rel_verified) (t t' : term) 
: option (∀ Δ Γ T, Δ ,, Γ |- t ≃-ctx t' : T) :=
  match rd_dec (rv_rd rv) t t' with
    | Some deriv => Some (rv_correct rv t t' deriv)
    | None => None
  end
.

(* RELATIONS *)
From PlutusCert Require Import
  LetNonRec.Spec
  LetNonRec.DecideBool
  LetNonRec.DSP
.

Definition let_nonrec : rel_verified :=
  mk_rel_verified
    ( mk_rel_decidable
        CNR_Term
        dec_Term
        dec_Term_equiv
    )
    CNR_Term__sem
.

From PlutusCert Require Import DeadCode DeadCode.DecideBool.
Definition rd_deadcode : rel_decidable :=
  mk_rel_decidable
    elim
    dec_Term
    dec_Term_equiv
.

Definition rv_equal : rel_verified.
Admitted.

Require Import Bool.


Definition dec_correct (rd : rel_verified) t t' :
  rd_decb (rv_rd rd) t t' = true ->
  ∀ Δ Γ T, Δ ,, Γ |- t ≃-ctx t' : T :=
  fun H =>
        let deriv := proj1 (rd_equiv (rv_rd rd) _ _) H in
        let ctx_equiv := (rv_correct rd) _ _ deriv in
        ctx_equiv.

Definition dec_rel (rd : rel_decidable) t t' :
  rd_decb rd t t' = true -> rd_rel rd t t' :=
  fun H => proj1 (rd_equiv rd _ _) H.

From PlutusCert Require
  Dump1
.

Fail Check (dec_correct let_nonrec Dump1.term Dump1.term eq_refl).

From PlutusCert Require TimelockDumps.

Check (dec_correct let_nonrec TimelockDumps.plc_4_inlined TimelockDumps.plc_5_compileNonRecTerms eq_refl).


(* CLAIMS *)

Inductive claim :=
  | Verified : rel_verified -> claim
  | Related  : rel_decidable -> claim
  | Unknown  : claim
.

Definition claim_prop : claim -> (term -> term -> Prop) := fun c =>
  match c with
  | Verified rv => fun t t' => ∀ Δ Γ T, Δ ,, Γ |- t ≃-ctx t' : T
  | Related rd  => rd_rel rd
  | Unknown     => fun t t' => True
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

(* CERTIFICATE *)
Require Import Lists.List.
Import ListNotations.

(* Deciding trace claims *)

Fixpoint trace_prop' (ps : list (pass * term)) : forall (claims : pass -> claim) (t : term), Prop :=
    fun claims t => match ps with
      | [] => True
      | (p, t') :: ps => claim_prop (claims p) t t' ∧ trace_prop' ps claims t'
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

  (*
Definition cert_claims : pass -> claim := fun p =>
  match p with
  | PassLetNonRec => Verified let_nonrec
  | PassDeadCode  => Related rd_deadcode
  | PassTypeCheck => Verified rv_equal
  | _             => Unknown
  end
.
  *)

Definition cert_claims : pass -> claim := fun p =>
  match p with
  | PassLetNonRec => Verified let_nonrec
  | _             => Unknown
  end
.


Import TimelockDumps.

Definition trace : compilation_trace :=
  CompilationTrace
    pir_0_original
    [ (PassRename      , pir_1_renamed)
    ; (PassTypeCheck   , pir_2_typechecked)
    ; (PassDeadCode    , pir_3_deadcode)
    ; (PassInline []   , pir_4_inlined)
    ; (PassThunkRec    , pir_5_thunkrec)
    ; (PassFloatTerm   , pir_6_floatTerm)
    ; (PassLetNonStrict, plc_0_compileNS)
    ; (PassLetTypes    , plc_1_compileTys)
    ; (PassLetRec      , plc_2_compileRecTerms)
    ; (PassDeadCode    , plc_3_dbe)
    ; (PassInline []   , plc_4_inlined)
    ; (PassLetNonRec   , plc_5_compileNonRecTerms)
    ]
.

Eval cbn in (trace_prop cert_claims trace).

Definition mk_proof : forall t,
  (trace_dec cert_claims trace = Some t) -> trace_prop cert_claims trace :=
  fun t eq_refl => t.

Definition proof : trace_prop cert_claims trace := 
  mk_proof _ eq_refl .

(* Eval vm_compute in (trace_dec cert_claims trace). *)

(*
Definition trace_checks_prop' : (pass -> claim) -> term -> list (pass * term) -> Prop :=
  fix f claims t ps :=
    match ps with
      | [] => True
      | (p, t') :: ps => claim_dec (claims p) t t' = true ∧ f claims t' ps
    end.

Definition trace_checks_prop : (pass -> claim) -> compilation_trace -> Prop :=
  fun claims ct =>
  match ct with
  | CompilationTrace t0 ps => trace_checks_prop' claims t0 ps
  end.

Fixpoint trace_check' (claims : pass -> claim) (t : term) (ps : list (pass * term)) :=
  match ps return option (trace_checks_prop' claims t ps) with
  | [] => Some I
  | (p, t') :: ps =>
    match trace_check' claims t' ps with
    | Some proofs =>
      match claim_dec_eq (claims p) t t' with
      | Some H => Some (conj H proofs)
      | None => None
      end
    | None => None
    end
  end
.

Definition trace_check (claims : pass -> claim) (ct : compilation_trace) :
  option (trace_checks_prop claims ct) :=
  match ct with
  | CompilationTrace t0 ps => trace_check' claims t0 ps
  end
.

Fixpoint trace_proof' (claims : pass -> claim) (t : term) (ps : list (pass * term)) :=
  match ps return option (trace_prop' claims t ps) with
  | [] => Some I
  | (p, t') :: ps =>
    match trace_proof' claims t' ps with
    | Some proofs =>
      match claim_dec_eq (claims p) t t' with
      | Some H => Some (conj H proofs)
      | None => None
      end
    | None => None
    end
  end
.

Fixpoint trace_proof' (claims : pass -> claim) (t : term) (ps : list (pass * term))
  : option (trace_prop' claims t ps) :=
    match ps return option (trace_prop' claims t ps) with
      | [] => I
      | (p, t') :: ps => 
        conj p (trace_proof' claims t' ps)
    end
.

Definition trace_proof (claims : pass -> claim) (ct : compilation_trace) :
  trace_prop claims ct :=
  match ct with
  | CompilationTrace t0 ps => trace_proof' claims t0 ps
  end
.
*)



(* Some testing on performance *)
Eval vm_compute in Dump1.term.



Theorem dump1_let_nonrec : ∀ Δ Γ T,
  Δ ,, Γ |- Dump1.term ≃-ctx Dump1.term : T.
Proof.


Qed.

Inductive step : term -> term -> Prop :=
  mk_step
    (t1 t2 : term)
    (R : term -> term -> Prop)
    : R t1 t2 -> step t1 t2
.


Eval vm_compute in Dump1.term.
Theorem valid : elim Dump1.term Dump1.term.
  apply dec_Term_sound.
  vm_compute.
  reflexivity.
Qed.
