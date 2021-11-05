Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

Local Open Scope list_scope.
Local Open Scope string_scope.

(** Type mappings

    We denote a type mapping by rho. A type mapping maps type variables [a] to
    triplets of the form [(Chi, T1, T2)].

    [Chi] is the semantic substitution for the type variable [a], wherease [T1]
    and [T2] are, respectively, the ''left'' and ''right'' syntactic substitutions 
    for the type variable [a].
*)
Definition tymapping := list (tyname * ((nat -> Term -> Term -> Prop) * Ty * Ty)).


(* TODO: Rewrite using lookup *)

(** Semantic substitution for the type variable [a] *)
Fixpoint sem (rho : tymapping) (a : tyname) : option (nat -> Term -> Term -> Prop) :=
  match rho with
  | nil => None
  | (a', (Chi, _ , _)) :: rho' => 
      if a =? a' then Datatypes.Some Chi else sem rho' a
  end.

(** (Left) syntactic substitution for the type variable [a] *)
Fixpoint syn1 (rho : tymapping) (a : tyname) : option Ty :=
  match rho with
  | nil => None
  | (a', (_, T1, _)) :: rho' => 
      if a =? a' then Datatypes.Some T1 else syn1 rho' a
  end.

(** (Right) syntactic substitution for the type variable [a] *)
Fixpoint syn2 (rho : tymapping) (a : tyname) : option Ty :=
  match rho with
  | nil => None
  | (a', (_, _, T2)) :: rho' => 
      if a =? a' then Datatypes.Some T2 else syn2 rho' a
  end.

(** (Left) syntactic substitutions in [rho] *)
Fixpoint msyn1 (rho : tymapping) : list (tyname * Ty) :=
  match rho with
  | nil => nil
  | (a', (_, T1, _)) :: rho' => 
      (a', T1) :: msyn1 rho'
  end.

(** (Right) syntactic substitutions in [rho] *)
Fixpoint msyn2 (rho : tymapping) : list (tyname * Ty) :=
  match rho with
  | nil => nil
  | (a', (_, _, T2)) :: rho' => 
      (a', T2) :: msyn2 rho'
  end.