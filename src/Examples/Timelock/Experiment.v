From Coq Require Import
  Strings.String
  Lists.List
  ZArith.BinInt.

From QuickChick Require Import
  QuickChick.

From PlutusCert Require Import
  Language.PlutusIR
  FreeVars
  BoundVars
  Equality
  Util
  UniqueBinders
  UniqueBinders.DecOpt
  TimelockDumps
.

Import UniqueTerm.
Import ListNotations.

Local Open Scope Z_scope.

Check pir_1_renamed.

Definition dec_unique := (@decOpt (unique_tm pir_1_renamed) (DecOptunique_tm pir_1_renamed)).

Eval cbv in dec_unique 1000.

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



(* Will the let node be replaced by its body? This happens
   when all bindings have been eliminated *)
Definition let_group_eliminated :
  list Z -> list Binding -> bool :=
  fun elims bs => forallb
                   (fun v => elem Z.eqb (snd v) elims)
                   (bound_vars_bindings bs)
  .

Axiom cheat : forall a, a.
(* Builds an intermediate AST where only the inlinings have been performed,
   including any renaming that has taken place in those inlined terms.
  (t' also has dead-code elim) *)
Fixpoint  inlined_intermediate (elims : list Z) (t : Term) : Term -> option Term
  with inlined_intermediate_binding (elims : list Z) (b : Binding) : list Binding -> option Binding.
Proof.
refine (
  fun t' =>
    match t, t' with

      (* We can traverse the ASTs in parallel, except when a complete
         Let node was removed (because all of its bindings were eliminated) *)
      | Let rec bs t_body, t' =>
          if let_group_eliminated elims bs
            then
              Let rec bs <$> inlined_intermediate elims t_body t'
            else
              match t' with

               | Let _ bs' t_body'  =>
                   Let rec <$> sequence_options (map (fun b => inlined_intermediate_binding elims b bs') bs)
                           <*> inlined_intermediate elims t_body t_body'

               | _                  => Nothing
               end

      | Var x, Var y => if snd x =? snd y then pure (Var x) else pure (Var y)
      | Var x, t     => pure t (* it must be inlined *)

      | TyAbs v k t, TyAbs _ _ t' => TyAbs v k <$> inlined_intermediate elims t t'
      | LamAbs v ty t, LamAbs _ _ t' => LamAbs v ty <$> inlined_intermediate elims t t'
      | Apply t1 t2, Apply t1' t2' => Apply <$> inlined_intermediate elims t1 t1' <*> inlined_intermediate elims t2 t2'
      | Constant c, _ => pure (Constant c)
      | Builtin f, _ => pure (Builtin f)
      | TyInst t ty, TyInst t' _ => TyInst <$> inlined_intermediate elims t t' <*> pure ty
      | Error ty, _ => pure (Error ty)
      | IWrap ty1 ty2 t, IWrap _ _ t' => IWrap ty1 ty2 <$> inlined_intermediate elims t t'
      | Unwrap t, Unwrap t' => Unwrap <$> inlined_intermediate elims t t'

      | _, _ => Nothing
    end
).
refine (
fun bs_post => match b with
  | TermBind str (VarDecl v ty) t =>
      let b_post := find
            (fun b' => match b with
              | TermBind _ (VarDecl v' _) _ => snd v =? snd v'
              | _ => false
              end) bs_post

      in match b_post with
        | Just (TermBind _ _ t') =>
            TermBind str (VarDecl v ty) <$> inlined_intermediate elims t t'
        | _ => Nothing
        end
  | TypeBind v ty => pure (TypeBind v ty)
  | DatatypeBind dt => pure (DatatypeBind dt)
  end
).
Defined.


Definition t_dce := some_exists (lookup_pass PassDeadCode) eq_refl.
Compute t_dce.
Definition t_inl := some_exists (lookup_pass (PassInline nil)) eq_refl.
Compute (map snd (bound_vars t_dce), map snd (bound_vars t_inl)).
Compute t_inl.
Definition t_interm := inlined_intermediate [77] t_dce t_inl.

Compute t_interm.


From PlutusCert Require Import DeadBindings.
Compute bound_vars t_dce.
Compute map fst (trace_passes trace).
