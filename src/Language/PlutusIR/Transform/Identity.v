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

Coercion One : Term >-> three.
Coercion Two : Binding >-> three.

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
Instance identity_sound t t' : DecOptSoundPos (identity t t').
Proof.
derive_sound.
Qed.
