(** * Typing and kinding contexts *)
Require PlutusCert.Language.PlutusIR.

Require Coq.Lists.List.
Require Coq.Strings.String.
Require Coq.Program.Basics.



(** ** Module type for a typing/kinding context*)
Module Type SIG_Context.

Import Coq.Lists.List.
Import PlutusCert.Language.PlutusIR.

(** Types of variables, binders, kinds and types *)
Parameter (Name Tyname : Set). (* Kind Ty : Set*)
Parameter compareT : Name -> Name -> bool.
Parameter compareK : Tyname -> Tyname -> bool.

Definition Kind := kind.
Definition Ty := ty Tyname.

(** The [Context] type and its operations *)
Parameter Context : Set.
Parameter empty : Context.
Parameter lookupK : Context -> Tyname -> option Kind.
Parameter lookupT : Context -> Name -> option Ty.
Parameter extendK : Tyname -> Kind -> Context -> Context.
Parameter extendT : Name -> Ty -> Context -> Context.
Parameter append : Context -> Context -> Context.
Parameter flatten : list Context -> Context.

End SIG_Context.



(** ** Typing contexts with named variables 

    (Type-) variables are strings. The context is a list of
    tuples relating variables to types and type-variables to kinds.
*)
Module NamedContext : SIG_Context.

Import PlutusCert.Language.PlutusIR.

Import Coq.Lists.List.
Import Coq.Strings.String.
Import Coq.Program.Basics.
Import ListNotations.

Local Open Scope string_scope.

Definition Name := string.
Definition Tyname := string.
Definition Kind := kind.
Definition Ty := ty Tyname.

Definition compareT := String.eqb.
Definition compareK := String.eqb.

Definition Context := list (Name * Ty + Tyname * Kind).

Definition empty : Context := nil.

Fixpoint lookupK (ctx : Context) (X : string) : option Kind := 
  match ctx with
  | inr (Y, K) :: ctx'  => if X =? Y then Coq.Init.Datatypes.Some K else lookupK ctx' X
  | inl _ :: ctx' => lookupK ctx' X
  | nil => None
  end.

Fixpoint lookupT (ctx : Context) (x : string) : option Ty :=
  match ctx with
  | inl (y, T) :: ctx' => if x =? y then Coq.Init.Datatypes.Some T else lookupT ctx' x 
  | inr _ :: ctx' => lookupT ctx' x
  | nil => None
  end.

Definition extendK X K (ctx : Context) := cons (inr (X, K)) ctx.
Definition extendT x T (ctx : Context) := cons (inl (x, T)) ctx.
Definition append ctx1 ctx2 : Context := List.app ctx1 ctx2.
Definition flatten (ctxs : list Context) := List.concat (rev ctxs).

End NamedContext.



(** ** Notations for contexts and related operations *)
Declare Scope context_scope.
Open Scope context_scope.

Module NamedContextNotations.

Notation "x ':T:' y" := (NamedContext.extendT (fst x) (snd x) y) (at level 60, right associativity) : context_scope.
Notation "x ':K:' y" := (NamedContext.extendK (fst x) (snd x) y) (at level 60, right associativity) : context_scope.

End NamedContextNotations.