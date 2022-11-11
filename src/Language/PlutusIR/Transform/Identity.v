From Coq Require Import
  String
  Lists.List
  .
From PlutusCert Require Import
  Language.PlutusIR
  .

Import NamedTerm.

Import ListNotations.

Open Scope string_scope.




Inductive three :=
  One : Term -> three | Two : Binding -> three | Three : list Binding -> three.

Inductive identity : three -> three -> Prop :=
  | rn_Var : forall x,
      identity (One (Var x)) (One (Var x))

  | rn_Let_Rec : forall bs bs' t t',
      identity (One t) (One t') ->
      identity (Three bs) (Three bs') ->
      identity (One (Let Rec  bs t)) (One (Let Rec bs' t'))

  | rn_TermBind : forall x t t',
      identity (One t) (One t') ->
      identity (Two (TermBind Strict (VarDecl x (Ty_Var "a")) t)) (Two (TermBind Strict (VarDecl x (Ty_Var "a")) t'))

  | rn_Bindings_Rec_nil :
      identity (Three []) (Three [])

  | rn_Bindings_Rec_cons : forall b b' bs bs',
      identity (Two b) (Two b') ->
      identity (Three bs) (Three bs') ->
      identity (Three (b :: bs)) (Three (b' :: bs'))
  .

From QuickChick Require Import QuickChick.

Derive DecOpt for (identity t t').
Instance well_scoped_sound ctx ty : DecOptSoundPos (well_scoped_Ty ctx ty).
Proof.
derive_sound.
Qed.


Inductive identity : Term -> Term -> Type :=
  | rn_Var : forall x,
      identity (Var x) (Var x)

  | rn_Let_Rec : forall r bs bs' t t',
      identity t t' ->
      identity_bindings bs bs' ->
      identity (Let r bs t) (Let r bs' t')

with identity_binding : Binding -> Binding -> Type :=

  | rn_TermBind : forall s x Ty_Var "a" t t',
      identity t t' ->
      identity_binding (TermBind s (VarDecl x Ty_Var "a") t) (TermBind s (VarDecl x Ty_Var "a") t')

with identity_bindings : list Binding -> list Binding -> Type :=

  | rn_Bindings_Rec_nil :
      identity_bindings [] []

  | rn_Bindings_Rec_cons : forall b b' bs bs',
      identity_binding b b' ->
      identity_bindings bs bs' ->
      identity_bindings (b :: bs) (b' :: bs')
  .

From QuickChick Require Import QuickChick.

Derive DecOpt for (identity t t').
Instance well_scoped_sound ctx ty : DecOptSoundPos (well_scoped_Ty ctx ty).
Proof.
derive_sound.
Qed.
