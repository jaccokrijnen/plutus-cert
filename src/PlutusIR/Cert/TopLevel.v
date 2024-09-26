From PlutusCert Require Import
  PlutusIR
  Cert.Relation
  Cert.Claim
.

Require Import Bool.


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



Theorem dump1_let_nonrec : forall Δ Γ T,
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
