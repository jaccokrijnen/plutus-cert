From Coq Require Import
  String
  List
  Bool
  Program
  Utf8_core
.

From PlutusCert Require Import
  Util
  UniqueBinders
  Purity
  Language.PlutusIR
  Language.PlutusIR.Analysis.Equality
  Language.PlutusIR.Transform.Congruence
  DeadBindings
  Congruence
.
Import Congruence.

Import NamedTerm.
Import ListNotations.


Section Bindings.

  Context (dec_Term : Term -> Term -> bool).
  Context (dec_Term_sound : ∀ s t, dec_Term s t = true -> dead_syn s t).

  Set Diffs "on".


  Fixpoint dec_Binding (b b' : Binding) : bool := match b, b' with
    | TermBind s vd t, TermBind s' vd' t' => Strictness_eqb s s' && VDecl_eqb vd vd' && dec_Term t t'
    | b, b' => Binding_eqb b b'
    end.

  Axiom (String_eqb_eq       : ∀ x y, String.eqb x y = true -> x = y).
  Axiom (Recursivity_eqb_eq  : ∀ x y, Recursivity_eqb x y = true -> x = y).
  Axiom (Strictness_eqb_eq   : ∀ x y, Strictness_eqb x y = true -> x = y).
  Axiom (Kind_eqb_eq         : ∀ x y, Kind_eqb x y = true -> x = y).
  Axiom (Ty_eqb_eq           : ∀ x y, Ty_eqb x y = true -> x = y).
  Axiom (some_valueOf_eqb_eq : ∀ x y, some_valueOf_eqb x y = true -> x = y).
  Axiom (func_eqb_eq         : ∀ x y, func_eqb x y = true -> x = y).
  Axiom (VDecl_eqb_eq        : ∀ x y, VDecl_eqb x y = true -> x = y).
  Axiom (TVDecl_eqb_eq       : ∀ x y, TVDecl_eqb x y = true -> x = y).
  Axiom (DTDecl_eqb_eq       : ∀ x y, DTDecl_eqb x y = true -> x = y).

  Create HintDb Hints_soundness.
  Hint Resolve
    String_eqb_eq
    Recursivity_eqb_eq
    Strictness_eqb_eq
    Kind_eqb_eq
    Ty_eqb_eq
    some_valueOf_eqb_eq
    func_eqb_eq
    VDecl_eqb_eq
    TVDecl_eqb_eq
    DTDecl_eqb_eq
  : Hints_soundness.

  Hint Constructors
    and
  : Hints_soundness.


  Axiom dec_Binding_sound : ∀ b b', dec_Binding b b' = true -> dead_syn_binding b b'.

  Hint Resolve
    dec_Binding_sound
  : Hints_soundness.

  Definition safely_removed b bsn :=
    negb (existsb (String.eqb (name_Binding b)) bsn) &&
    is_pure_binding [] b.

  Definition binding_was_there b' bs : bool :=
    match find (λ b, String.eqb (name_Binding b) (name_Binding b')) bs with
      | Datatypes.Some b => dec_Binding b b'
      | None => false
    end
    .

  (* inlined and specialized `find` for termination checking *)
  Definition find_Binding b' :=
  fix find (bs : list Binding) : bool :=
    match bs with
    | []      => false
    | b :: bs => if String.eqb (name_Binding b) (name_Binding b') then dec_Binding b b' else find bs
    end.

  (* This does not work in the termination checker, it doesn't see that b returned by find 
     is a structural subterm.
     It would have to fuse the result of find (an option string) with the resulting, which is
     what I did in the above definition*)
  Definition find_Binding' b' bs :=
    match find (λ b, String.eqb (name_Binding b) (name_Binding b')) bs with
      | Datatypes.Some b => dec_Binding b b'
      | None => false
    end.


  Definition dec_Bindings (bs bs' : list Binding) : bool :=
    let bsn := map name_Binding bs in
    let bs'n := map name_Binding bs' in
    forallb (fun b => safely_removed b bs'n) bs &&
    forallb (fun b' =>
    find_Binding b' bs
    ) bs'.

  (* this did not pass termination checking *)
  (*
    forallb (fun b' =>
    match find (λ b, String.eqb (name_Binding b) (name_Binding b')) bs with
      | Datatypes.Some b => dec_Binding b b'
      | None => false
    end
    ) bs'
   *)

  Lemma H_safely_removed bs bs':
      forallb (fun b => safely_removed b (map name_Binding bs')) bs = true ->
      ∀ b : Binding, In b bs → name_removed b bs' → pure_binding [] b.
  Proof with eauto with Hints_soundness.
    intros H_dec.
    intros b H_In H_removed.
    unfold safely_removed in H_dec.
    rewrite forallb_forall in H_dec. (* why did rewrite accept a <-> ? was also possible with eapply -> ..., but generated an existential for x *)
    apply H_dec in H_In as H_dec_andb.
    clear H_dec H_In.
    apply andb_true_iff in H_dec_andb.
    destruct H_dec_andb as [_ H_dec_pure_binding].
    apply is_pure_binding_pure_binding.
    assumption.
  Qed.

  Lemma H_find_binding bs bs' :
      forallb (fun b' => find_Binding b' bs) bs' = true ->
      ∀ b', In b' bs' ->
         ∃ x, In x bs /\
           name_Binding x = name_Binding b' /\
           dead_syn_binding x b'
      .
  Proof with eauto with Hints_soundness.
    rewrite forallb_forall.
    intros H_dec b' H_In.
    apply H_dec in H_In.
    clear H_dec.
    induction bs as [ | b ].
    - discriminate H_In.
    - simpl in H_In.
      destruct (String.eqb (name_Binding b) (name_Binding b')) eqn:H_name_eq.

      (* b related to b' *)
      + exists b.
        repeat split...
        * constructor...

      (* a not related to b' *)
      + apply IHbs in H_In. clear IHbs.
        destruct H_In as [x [H_x_In [H_eq_name H_dead_syn]]].
        assert (In x (b :: bs)). { apply in_cons... }
        exists x...
  Qed.

  Create HintDb Hints_bindings.
  Hint Resolve
    H_safely_removed
    H_find_binding.
  Hint Constructors
    dead_syn_bindings.

  Ltac split_hypos :=
    match goal with
    | H : (?x && ?y)%bool = true |- _ => apply andb_true_iff in H; destruct H; split_hypos
    | _ => idtac
    end.

  Lemma dec_Bindings_sound : ∀ bs bs',
    dec_Bindings bs bs' = true -> dead_syn_bindings bs bs'.
  Proof with eauto with Hints_bindings.
    intros bs bs' H.
    simpl in H.
    unfold dec_Bindings in H.
    split_hypos.
    eapply dc_bindings...
  Qed.


End Bindings.

Fixpoint dec_Term (x y : Term) {struct x} : bool := match x, y with

  | Let r bs t   , Let r' bs' t' => if dec_Bindings dec_Term bs bs'
        then Recursivity_eqb r r' && dec_Term t t'
        else forallb (is_pure_binding []) bs && dec_Term t t' (* Check whether the whole let was removed *)

  | _, _ => is_cong dec_Term x y

  end
.

Lemma dec_Term_sound t t' :
  dec_Term t t' = true -> dead_syn t t'.
Proof.
  intros H_dec.
  induction t.
  2: {
    unfold dec_Term in H_dec.
    simpl in H_dec.
  

From Coq Require Import Extraction.
Extraction Language Haskell.
Recursive Extraction dec_Term.
Require Import Strings.Ascii.
Recursive Extraction nat_of_ascii.
Recursive Extraction ascii_of_nat.
