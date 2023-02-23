From Coq Require Import
  Strings.String
  Lists.List.

From PlutusCert Require Import 
  Language.PlutusIR
  Language.PlutusIR.Analysis.Equality.

Import NamedTerm.



(* A specialized version of In for names *)
Inductive NameIn (x : name) : list name -> Prop :=
  | NI_Here  : forall {xs}, NameIn x (x :: xs)
  | NI_There : forall {x' xs}, x <> x' -> NameIn x xs -> NameIn x (x' :: xs).

Lemma NameIn_In_eq : forall xs x, NameIn x xs <-> @In name x xs.
Proof with auto using NameIn.
  induction xs; split; intros; simpl; inversion H; subst...
    - apply IHxs in H3...
    - destruct (string_dec x a); subst...
      apply NI_There... 
      apply IHxs...
Qed.

Lemma NameIn_In_neq : forall xs x, ~ NameIn x xs <-> ~ @In name x xs.
Proof. intros. apply not_iff_compat. apply NameIn_In_eq. Qed.



(* A specialized version of In for Ty, does not require an Enum Ty instance *)
Inductive TyIn (x : Ty) : list Ty -> Prop :=
  | TI_Here  : forall {xs}, TyIn x (x :: xs)
  | TI_There : forall {x' xs}, x <> x' -> TyIn x xs -> TyIn x (x' :: xs).

Lemma TyIn_In_eq : forall xs x, TyIn x xs <-> @In Ty x xs.
Proof with auto using TyIn.
  induction xs; split; intros; simpl; inversion H; subst...
    - apply IHxs in H3...
    - destruct (Ty_dec x a); subst...
      apply TI_There... 
      apply IHxs...
Qed.

Lemma TyIn_In_neq : forall xs x, ~ TyIn x xs <-> ~ @In Ty x xs.
Proof. intros. apply not_iff_compat. apply TyIn_In_eq. Qed.



(* A specialized version of constructor for constructor *)
Inductive ConstrIn (x : constructor) : list constructor -> Prop :=
  | CI_Here  : forall {xs}, ConstrIn x (x :: xs)
  | CI_There : forall {x' xs}, x <> x' -> ConstrIn x xs -> ConstrIn x (x' :: xs).

Lemma ConstrIn_In_eq : forall xs x, ConstrIn x xs <-> @In constructor x xs.
Proof with auto using ConstrIn.
  induction xs; split; intros; simpl; inversion H; subst...
    - apply IHxs in H3...
    - destruct (constructor_dec x a); subst...
      apply CI_There... 
      apply IHxs...
Qed.

Lemma ConstrIn_In_neq : forall xs x, ~ ConstrIn x xs <-> ~ @In constructor x xs.
Proof. intros. apply not_iff_compat. apply ConstrIn_In_eq. Qed.
