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
  PlutusIR
  PlutusIR.Analysis.Equality
  PlutusIR.Transform.Compat
  DeadCode
  Compat
.

Import NamedTerm.
Import ListNotations.

Section Bindings.

  Context (dec_Term : Term -> Term -> bool).

  Definition dec_Binding (b b' : Binding) : bool := match b, b' with
    | TermBind s vd t, TermBind s' vd' t' => Strictness_eqb s s' && VDecl_eqb vd vd' && dec_Term t t'
    | b, b' => Binding_eqb b b'
    end.

  Definition dec_removed b bs' :=
    if negb (existsb (String.eqb (name_Binding b)) bs')
      then dec_pure_binding [] b
      else true.

  Definition dec_was_present b' bs : bool :=
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
    forallb (fun b => dec_removed b bs'n) bs &&
    forallb (fun b' => find_Binding b' bs) bs'.

  (* this did not pass termination checking *)
  (*
    forallb (fun b' =>
    match find (λ b, String.eqb (name_Binding b) (name_Binding b')) bs with
      | Datatypes.Some b => dec_Binding b b'
      | None => false
    end
    ) bs'
   *)
End Bindings.

Fixpoint dec_Term (x y : Term) {struct x} : bool := match x, y with

  | Let r bs t   , Let r' bs' t' =>
      if dec_Bindings dec_Term bs bs'
      then (* same let block, but bindings were removed *)
        Recursivity_eqb r r' && dec_Term t t'
      else (* t' is another let block, the whole block in the pre-term was removed *)
        forallb (dec_pure_binding []) bs && dec_Term t y (* Check whether the whole let was removed *)
  | Let _ bs t   , _ =>
     forallb (dec_pure_binding []) bs && dec_Term t y (* Check whether the whole let was removed *)
  | TyInst (TyAbs α k t) τ , TyInst (TyAbs α' k' t') τ'  =>
     String.eqb α α' &&
     Kind_eqb k k' &&
     Ty_eqb τ τ' &&
     dec_Term t t'
  | TyInst (TyAbs _ _ t) _ , t' =>
     dec_Term t t'
  | _ , _ => dec_compat dec_Term x y

  end
.


Set Diffs "on".

Definition P_Term t := forall t', dec_Term t t' = true -> elim t t'.
Definition P_Binding b := forall b', dec_Binding dec_Term b b' = true -> elim_binding b b'.

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
#[local]
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

#[local]
Hint Constructors
  and
: Hints_soundness.

Ltac split_hypos :=
  match goal with
  | H : (?x && ?y)%bool = true |- _ => apply andb_true_iff in H; destruct H; split_hypos
  | _ => idtac
  end.


Lemma H_dec_removed bs bs':
    forallb (fun b => dec_removed b (map name_Binding bs')) bs = true ->
    ∀ b : Binding, In b bs → name_removed b bs' → pure_binding [] b.
Proof with eauto with Hints_soundness.
  intros H_dec.
  intros b H_In H_removed.
  unfold dec_removed in H_dec.
  rewrite forallb_forall in H_dec. (* why did rewrite accept a <-> ? was also possible with eapply -> ..., but generated an existential for x *)
  apply H_dec in H_In as H_dec_andb.
  clear H_dec H_In.

  destruct (negb
    (existsb (String.eqb (name_Binding b))
       (map name_Binding bs')))
       eqn:H_1.
  + apply sound_dec_pure_binding...

  (* contradiction *)
  + apply negb_false_iff in H_1.
    unfold name_removed in *.
    apply existsb_exists in H_1.
    destruct H_1 as [x [H_in H_name_b_eq_x]].
    apply String.eqb_eq in H_name_b_eq_x.
    subst.
    contradiction.
Qed.

Lemma H_find_binding' bs bs' :
  (∀ b, In b bs -> P_Binding b) ->
    forallb (fun b' => find_Binding dec_Term b' bs) bs' = true ->
    ∀ b', In b' bs' ->
       ∃ x, In x bs /\
         name_Binding x = name_Binding b' /\
         elim_binding x b'
    .
Proof with eauto with Hints_soundness.
  intro H_P_Binding.
  rewrite forallb_forall.
  intros H_dec b' H_In.
  apply H_dec in H_In as H_find_b'.
  clear H_dec.
  induction bs as [ | b ].
  - discriminate H_find_b'.
  - simpl in H_find_b'.
    destruct (name_Binding b =? name_Binding b')%string
      eqn:H_name_eq.

    (* b related to b' *)
    + exists b.
      repeat split...
      * constructor...
      * assert (H : P_Binding b).
        ++ apply H_P_Binding.
           constructor...
        ++ unfold P_Binding in H...


    (* a not related to b' *)
    + apply IHbs in H_find_b' as H_ex. clear IHbs.
      * destruct H_ex as [x [H_x_In [H_eq_name H_elim]]].
        assert (In x (b :: bs)). { apply in_cons... }
        exists x...
      * intros b0 H_b0_in.
        apply H_P_Binding.
        apply in_cons...
Qed.

Create HintDb Hints_bindings.
#[local]
Hint Resolve
  H_dec_removed : Hints_bindings.
#[local]
Hint Constructors
  elim_bindings : Hints_bindings.
#[local]
Hint Resolve
  H_dec_removed
  H_find_binding' : Hints_bindings.
#[local]
Hint Constructors
  elim
  elim_binding
  elim_bindings
  : Hints_soundness.

Lemma dec_Bindings_sound' : ∀ bs bs',
  (∀ b, In b bs -> P_Binding b) ->
  dec_Bindings dec_Term bs bs' = true -> elim_bindings bs bs'.
Proof with eauto with Hints_bindings.
  intros H_P_bs bs bs' H.
  simpl in H.
  unfold dec_Bindings in H.
  split_hypos.
  eapply elim_bindings_pure...
Qed.


Lemma dec_TermBind_sound : ∀ s v t b b',
  b = TermBind s v t ->
  P_Term t ->
  dec_Binding dec_Term b b' = true ->
  elim_binding b b'.
Proof with eauto with Hints_soundness.
  intros s v t b b' H_eq H_P_Term H_dec.
  unfold P_Term in *.
  subst.
  simpl in H_dec.
  destruct b'.
  all: try discriminate.
  split_hypos.
  assert (s = s0)...
  assert (v = v0)...
  subst...
Qed.

Lemma dec_TypeBind_sound : ∀ v ty b b',
  b = TypeBind v ty ->
  dec_Binding dec_Term b b' = true ->
  elim_binding b b'.
Proof with eauto with Hints_soundness.
  intros v ty b b' H_eq H_dec.
  subst.
  destruct b'.
  all: try discriminate.
  simpl in H_dec.
  split_hypos.
  assert (v = t)... subst.
  assert (ty = t0)... subst...
Qed.

Lemma dec_DatatypeBind_sound : ∀ dtd b b',
  b = DatatypeBind dtd ->
  dec_Binding dec_Term b b' = true ->
  elim_binding b b'.
Proof with eauto with Hints_soundness.
  intros dtd b b' H_eq H_dec.
  subst.
  destruct b'.
  all: try discriminate.
  simpl in H_dec.
  split_hypos.
  assert (dtd = d)... subst...
Qed.

Lemma all_pure : ∀ bs,
  forallb (dec_pure_binding []) bs = true ->
  Forall (pure_binding []) bs.
Proof.
  intros bs H_dec.
  apply Forall_forall.
  intros b H_In.
  rewrite forallb_forall in H_dec.
  auto using sound_dec_pure_binding.
Qed.

#[local]
Hint Resolve all_pure : Hints_soundness.
#[local]
Hint Resolve dec_Bindings_sound' : Hints_soundness.
#[local]
Hint Resolve
  dec_TermBind_sound
  dec_TypeBind_sound
  dec_DatatypeBind_sound
  : Hints_soundness.
#[local]
Hint Constructors Compat : Hints_soundness.

Theorem dec_Term_Binding_sound :
  (∀ t, P_Term t) /\ (∀ b, P_Binding b).
Proof with eauto with Hints_soundness.
  apply Term__multind with (P := P_Term) (Q := P_Binding).
  all: intros.

  (* P_Term (Let rec bs t) *)
  - unfold P_Term in *.
    intros t' H_dec_Term.
    simpl in H_dec_Term.
    destruct t'; simpl in H_dec_Term.
    all: split_hypos.
    {
      destruct (dec_Bindings dec_Term bs l) eqn:H_dec_bs.
      all: split_hypos.
      (* H_dec_Term: then branch *)
      * split_hypos.

        assert (H_bindings : elim_bindings bs l).
        {
          apply ForallP_Forall in H.
          rewrite -> Forall_forall in H...
        }
        assert (H_eq_rec : rec = r)... subst.
        eapply elim_delete_bindings...

      (* H_dec_Term: else branch *)
      * eapply elim_delete_let...
    }
    all: try eapply elim_delete_let...

  - unfold P_Term.
    destruct t'.
    all: intro H_dec; try discriminate H_dec.
    assert (s = s0)... subst...
  - unfold P_Term.
    destruct t'.
    all: intro H_dec; try discriminate H_dec.
    simpl in H_dec. split_hypos.
    assert (s = s0)... subst.
    assert (k = k0)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (s = s0)...
    assert (t = t1)... subst...
  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    idtac...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (s = s0)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (d = d0)... subst...

  - unfold P_Term; destruct t', t; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    all: admit.
    (* assert (t0 = t1)... subst... *)

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (t = t0)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (t = t2)... subst.
    assert (t0 = t3)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    idtac...

  - unfold P_Binding...
  - unfold P_Binding...
  - unfold P_Binding...
Admitted.

Corollary dec_Term_sound : ∀ t t', dec_Term t t' = true -> elim t t'.
Proof.
  apply dec_Term_Binding_sound.
Qed.

Corollary dec_Binding_sound : ∀ t t', dec_Term t t' = true -> elim t t'.
Proof.
  apply dec_Term_Binding_sound.
Qed.

(* TODO, move this in separate files *)
From Coq Require Import Extraction.
Require Import Strings.Ascii.
Extraction Language Haskell.
Extraction "hs-src/PlutusIR/Certifier/Extracted.hs" dec_Term ascii_of_nat.
