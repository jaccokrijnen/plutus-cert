From QuickChick Require Import QuickChick.

From Coq Require Import
  Lists.List
  ZArith.BinInt.

From PlutusCert Require Import
  Language.PlutusIR
  FreeVars
  BoundVars
  Equality
  Util
  Util.List
  UniqueBinders
  TimelockDumps
  Timelock.Trace
.


(* Import UniqueTerm. *)
Import ListNotations.

Local Open Scope Z_scope.

Import UniqueTerm.

(* Some utilities*)
Definition var_eqb : string * Z -> string * Z -> bool :=
  fun p1 p2 => match p1, p2 with
    | (_, n), (_, m) => Z.eqb n m
    end.

Definition pass_eqb := fun p1 p2 =>
  match p1, p2 with
    | PassInline _, PassInline _ => true (* hack for lookups *)
    | _, _ =>
      if pass_dec (pair_dec string_dec Z.eq_dec) p1 p2
        then true
        else false
    end.

Definition trace_t0 := fun trace => match trace with
  | CompilationTrace t0 _ => t0
  end : Term.

Definition trace_passes := fun trace => match trace with
  | CompilationTrace _ ps => ps
  end : list (pass name * Term).

Definition t0 := trace_t0 trace.
Definition ps := trace_passes trace.

Example t0_closed : free_vars var_eqb t0 = nil.
  Proof. reflexivity. Qed.

Compute Datatypes.length (bound_vars t0).

(* Get the value out of a Some *)
Definition some_exists {a} : forall {v} (s : option a), (s = Datatypes.Some v) -> a :=
  fun v s H => match H with
    | eq_refl => v
  end.

(* Lookup the AST after a given pass *)
Definition lookup_pass p :=
  option_map
    snd
    (find (fun (x : prod (pass name) Term) => pass_eqb (fst x) p) ps)
    .


Definition t_dce := some_exists (lookup_pass PassDeadCode) eq_refl.
Compute t_dce.
Definition t_inl := some_exists (lookup_pass (PassInline nil)) eq_refl.
Compute (map snd (bound_vars t_dce), map snd (bound_vars t_inl)).
Compute t_inl.
(*
Definition t_interm := inlined_intermediate [77] t_dce t_inl.
Compute t_interm.


From PlutusCert Require Import DeadBindings.
Compute bound_vars t_dce.
Compute map fst (trace_passes trace).
*)
