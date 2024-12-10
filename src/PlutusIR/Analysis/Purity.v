From Coq Require Import
  Strings.String
  Lists.List
.

From PlutusCert Require Import
  PlutusIR
  Semantics.Dynamic.Values
  Util.List
  .

Import ListNotations.

Open Scope bool_scope.

Inductive binder_info :=
  | let_bound : strictness -> binder_info
  | lambda_bound
.

Definition ctx := list (string * binder_info).

(* Pure terms include values or variables that are known to be bound to values *)
Inductive is_pure (Γ : ctx) : term -> Type :=

  | is_pure_result : forall t,
      result t ->
      ~(is_error t) ->
      is_pure Γ t

  | is_pure_var_let : forall x,
      Lookup x (let_bound Strict) Γ ->
      is_pure Γ (Var x)

  | is_pure_var_lambda : forall x,
      Lookup x lambda_bound Γ ->
      is_pure Γ (Var x)
.


Lemma dec_is_error_not_is_error : forall t,
  is_error_beq t = false -> ~ is_error t.
Proof.
  intros t H.
  destruct t; intros H1; inversion H1.
  inversion H.
Qed.


Definition is_pureb (Γ : ctx) (t : term) : bool :=
  match t with
  | Var x =>
    match lookup x Γ with
      | Datatypes.Some lambda_bound => true
      | Datatypes.Some (let_bound Strict) => true
      | Datatypes.Some (let_bound NonStrict) => false
      | _ => false
    end
  | _     => if result_dec t then true else false && negb (is_error_beq t)
  end
.

(* An approximation of bindings that are pure, they will not diverge when evaluated *)
Inductive pure_binding (Γ : ctx) : binding -> Prop :=

  | pb_term_non_strict : forall vd t,
      pure_binding Γ (TermBind NonStrict vd t)

  | pb_term_strict_val : forall vd t,
      is_pure Γ t ->
      pure_binding Γ (TermBind Strict vd t)

  | pb_data : forall dtd,
      pure_binding Γ (DatatypeBind dtd)

  | pb_type : forall tvd ty,
      pure_binding Γ (TypeBind tvd ty)
.

Definition dec_pure_binding (Γ : ctx) (b : binding) : bool :=
    match b with
      | TermBind NonStrict vd t => true
      | TermBind Strict vd t    => result_beq t
      | DatatypeBind dtd        => true
      | TypeBind tvd ty         => true
    end
.

Lemma sound_dec_pure_binding : forall Γ b, dec_pure_binding Γ b = true -> pure_binding Γ b.
Admitted.
