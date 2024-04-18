From Coq Require Import
  String
  List
  Bool
  Program
  Datatypes
  Utf8_core
  PeanoNat
.

From PlutusCert Require Import
  Util
  Util.Tactics
  Util.List
  PlutusIR
  PlutusIR.Analysis.Equality
  PlutusIR.Transform.Compat
  PlutusIR.Transform.LetNonRec.Spec.
Import NamedTerm.

Import ListNotations.

(*
   Returns `Just t'` if bindings were desugared correctly, where t' is the rest
   of the desugared term.

   Note that dec_Term has to be passed manually. In this form, the
   termination checker is happy when checking dec_Term (it's probably
   inlining dec_Bindings within dec_Term, and then sees the structural
   recursive call to dec_Term.

   We want this as a separate definition so that proofs don't have to deal with
   a big (fix ...) expression. The termination checker doesn't allow it to be
   part of the mutual recursive binding group of dec_Term, so this is the
   workaround.

   Below is a specialized version dec_Bindings that you do not have to pass
   dec_Term.
*)

Section Bindings.

  Context (dec_Term : Term -> Term -> bool).

  Fixpoint bindings_to_apps (bs : list Binding) : option (list (Term -> Term)) :=
    match bs with
      | []        => Just []
      | TermBind Strict (VarDecl v ty) rhs :: bs =>
          option_map
            (cons (fun t => Apply (LamAbs v ty t) rhs))
            (bindings_to_apps bs)
      |  _ => None
    end.

  Fixpoint dec_Bindings' (bs : list Binding) (t : Term) {struct bs} : option Term :=
    match bs with
      | nil       => Just t
      | cons b bs => match b, t with
        | TermBind Strict (VarDecl v ty) rhs, Apply (LamAbs v' ty' body') rhs' =>
          if (String.eqb v v' && Ty_eqb ty ty' && dec_Term rhs rhs')
            then dec_Bindings' bs body'
            else None
        | _, _ => None
        end
    end.

End Bindings.

(*
  Returns true if the term was desugared correctly.
*)
Fixpoint dec_Term (x y : Term) {struct x} : bool := match x, y with

  (* non-recursive bindings should be desugared *)
  | Let NonRec bs body, t =>
       match dec_Bindings' dec_Term bs t with
        | Just body' => dec_Term body body'
        | Nothing    => false
       end

  (* Other cases should be compatible, i.e. identical constructors
     and recursive Terms recursively desugared *)
  | Let Rec bs t   , Let Rec bs' t'     => forall2b dec_Binding_compat bs bs' && dec_Term t t'
  | Var n          , Var n'             => String.eqb n n'
  | TyAbs n k t    , TyAbs n' k' t'     => String.eqb n n' && Kind_eqb k k' && dec_Term t t'
  | LamAbs n ty t  , LamAbs n' ty' t'   => String.eqb n n' && Ty_eqb ty ty' && dec_Term t t'
  | Apply s t      , Apply s' t'        => dec_Term s s' && dec_Term t t'
  | Constant c     , Constant c'        => some_valueOf_eqb c c'
  | Builtin f      , Builtin f'         => func_eqb f f'
  | TyInst t ty    , TyInst t' ty'      => dec_Term t t' && Ty_eqb ty ty'
  | Error ty       , Error ty'          => Ty_eqb ty ty'
  | IWrap ty1 ty2 t, IWrap ty1' ty2' t' => Ty_eqb ty1 ty1' && Ty_eqb ty2 ty2' && dec_Term t t'
  | Unwrap t       , Unwrap t'          => dec_Term t t'
  | Constr i ts    , Constr i' ts'      => Nat.eqb i i' && list_eqb dec_Term ts ts'
  | Case t ts      , Case t' ts'        => dec_Term t t' && list_eqb dec_Term ts ts'

  | _, _ => false
  end
with dec_Binding_compat (b b' : Binding) : bool := match b, b' with
  (* These cases are only used for recursive let-bindings, i.e.
     equal and recursive Terms should be desugared *)
  | TermBind s vdecl t, TermBind s' vdecl' t' => Strictness_eqb s s' && VDecl_eqb vdecl vdecl' && dec_Term t t'
  | TypeBind tvdecl ty, TypeBind tvdecl' ty'  => TVDecl_eqb tvdecl tvdecl' && Ty_eqb ty ty'
  | DatatypeBind dtd  , DatatypeBind dtd'     => DTDecl_eqb dtd dtd'
  | _, _ => false
  end
.

(* See comment of dec_Bindings' *)
Definition dec_Bindings : list Binding -> Term -> option Term := 
  dec_Bindings' dec_Term.


(*

Note [IH for nested datatypes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Usual IH used by `induction` tactic does not suffice, it only holds
for _direct_ subterms, and not for subterms within a list subterm.

- Define an induction/recursion scheme similarly to dec_Term above.
*)


(*

Note [Refactor VarDecl]
~~~~~~~~~~~~~~~~~~~~~~

VarDecl in Plutus is isomorphic to (string, Ty). Since plutus-cert currently
models Ty as unit, VarDecl is currently defined as string (for convenience).
This should of course change when Ty is taken into account.

This also means that in some cases, a proof or function may "invent" a Ty with
value tt : unit, where in a typed situation it should be part of an assumption
or argument.

*)

Definition P_Term t := ∀ t',
  dec_Term t t' = true <-> CNR_Term t t'.

Definition P_Binding_compat b :=  ∀ b',
    dec_Binding_compat b b' = true <-> CNR_Binding_compat b b'
.

Definition P_Binding_NonRec b := ∀ t t_inner,
  (∃ bs, dec_Bindings (b :: bs) t = Some t_inner) <->
  (∃ f fs,
    CNR_Binding b f /\
    fold_right apply t_inner (f :: fs) = t)
.

Definition P_Binding b :=
  P_Binding_compat b /\ P_Binding_NonRec b
.

Ltac simpl_dec_Term :=
  try match goal with (* Try because not used in Binding cases *)
    | H:dec_Term _ _ = true |- _ => simpl in H
  end;
  repeat (match goal with
    | H : match ?r with _ => _ end = true |- _ => destruct r
    | H : false = true |- _ => inversion H
    | H : _ && _ = true |- _ => rewrite andb_true_iff in H
    | H : _ /\ _ |- _ => destruct H in H
  end).

Ltac rewrite_reflection :=
  repeat (match goal with

    | H : String.eqb _ _ = true |- _ => rewrite String.eqb_eq in H
    | H : Kind_eqb _ _ = true |- _ => rewrite Kind_eqb_eq in H
    | H : Ty_eqb _ _ = true |- _ => rewrite Ty_eqb_eq in H
    | H : some_valueOf_eqb _ _ = true |- _ => rewrite some_valueOf_eqb_eq in H
    | H : func_eqb _ _ = true |- _ => rewrite func_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => rewrite Nat.eqb_eq in H
    | H : Strictness_eqb _ _ = true |- _ => rewrite Strictness_eqb_eq in H
    | H : VDecl_eqb _ _ = true |- _ => rewrite VDecl_eqb_eq in H
    | H : list_eqb ?eqb ?xs _ = true,
      H_elems : ForallP _ ?xs |- _
        => rewrite ForallP_Forall in H_elems;
           rewrite (forall2b_Forall2_Forall _ _ dec_Term xs _ H_elems) in H

    | H : dec_Term ?t ?t' = true ,
      IH : _ -> dec_Term ?t _ = true <-> _ |- _ => rewrite IH in H
  end).


Ltac tac_fwd :=
  intros;
  simpl_dec_Term;
  rewrite_reflection;
  subst;
  auto using CNR_Term.


Ltac simpl_goal :=
  simpl;
  repeat (rewrite andb_true_iff)
.

Ltac bwd_reflection :=
  repeat (match goal with
    | |- String.eqb _ _ = true => rewrite String.eqb_eq; reflexivity
    | |- Kind_eqb _ _ = true   => rewrite Kind_eqb_eq; reflexivity
    | |- Ty_eqb _ _ = true   => rewrite Ty_eqb_eq; reflexivity
    | |- some_valueOf_eqb _ _ = true => rewrite some_valueOf_eqb_eq; reflexivity
    | |- func_eqb _ _ = true => rewrite func_eqb_eq; reflexivity
    | |- Nat.eqb _ _ = true => rewrite Nat.eqb_eq; reflexivity
    | |- Strictness_eqb _ _ = true => rewrite Strictness_eqb_eq; reflexivity
    | |- VDecl_eqb _ _ = true => rewrite VDecl_eqb_eq; reflexivity

    |
      H_elems : ForallP _ ?xs |- list_eqb ?eqb ?xs _ = true =>
        rewrite ForallP_Forall in H_elems;
        rewrite (forall2b_Forall2_Forall _ CNR_Term dec_Term xs _ H_elems);
        assumption
    | IH : _ -> dec_Term ?t _ = true <-> _ |- dec_Term ?t _ = true => rewrite IH; assumption
  end).

Ltac tac_bwd :=
  inversion 1; subst;
  simpl_goal;
  repeat split;
  bwd_reflection.

Ltac dec_tac :=
  unfold P_Term, P_Binding;
  intros;

  (* Split cases, solve impossible ones *)
  match goal with t' : Term |- _ =>
    destruct t'; split; try solve [inversion 1]
  end; [> tac_fwd | tac_bwd].

Definition desugar_fun v ty t_bound : Term -> Term :=
  fun t_inner => Apply (LamAbs v ty t_inner) t_bound.

Lemma dec_Bindings_exists : ∀ bs t t_inner,
  dec_Bindings bs t = Some t_inner ->
  (∃ fs, fold_right apply t_inner fs = t)
.
Proof.
  induction bs as [ | b bs].
  - simpl. intros. inversion H. subst t_inner.
    exists []. auto.
  - intros.
    destruct b;
    try solve [inversion H].
    destruct s; try solve [inversion H].
    destruct v.
    simpl in H.
    destruct t; try solve [inversion H].
    destruct t2; try solve [inversion H].
    destruct ((s =? s0)%string && Ty_eqb t1 t && dec_Term t0 t3); try solve [inversion H].
    specialize (IHbs _ _ H).

    destruct IHbs as [fs H_fs].

    exists (
      desugar_fun s0 t t3
      ::
      fs).
    unfold desugar_fun.
    subst t2.
    simpl.
    reflexivity.
Qed.

Lemma dec_funs_exists : ∀ fs t t_inner,
  Forall (fun f => ∃ v ty t_bound, f = desugar_fun v ty t_bound) fs ->
  fold_right apply t_inner fs = t ->
  ∃ bs, dec_Bindings bs t = Some t_inner
.
Proof.
  admit.
Admitted.

Definition dec_Term_equiv : ∀ t, P_Term t.
Proof.
  apply Term__multind with (P := P_Term) (Q := P_Binding).
  all: try solve [dec_tac].
  - (* P_Term Let *)
    destruct rec.
    + (* NonRec *)
      admit.
    + (* Rec *)
      unfold P_Term, P_Binding;
      intros;

      (* Split cases, solve impossible ones *)
      match goal with t' : Term |- _ =>
        destruct t'; split; try solve [inversion 1]
      end.
      * (*fwd *) 
      intros.
      simpl_dec_Term.
      rewrite ForallP_Forall in *.
      apply (Forall_impl P_Binding_compat (fun b H => proj1 H)) in H.
        unfold P_Binding_compat in *.
      apply (forall2b_Forall2_Forall _ _ dec_Binding_compat _ _ H) in H1.

      apply H0 in H2.
      constructor; auto.
      generalize dependent l.
      induction bs.
      -- intros l H1. inversion H1. constructor.
      -- intros l H1. inversion H1; subst.
         apply Forall_inv_tail in H.
         constructor; eauto.
      (* bwd *)
      * intros H_Let.
        inversion H_Let. subst.
        simpl.
        rewrite andb_true_iff.
        split.
        -- rewrite ForallP_Forall in H.
        apply (Forall_impl P_Binding_compat (fun b H => proj1 H)) in H.
        apply (forall2b_Forall2_Forall _ _ dec_Binding_compat _ _ H).
        generalize dependent l.
        induction bs.
        --- intros l H_Let H_compat.
            inversion H_compat. subst. constructor.
        --- intros l H_Let H_compat. inversion H_compat; subst.
            constructor; auto.
            inversion H_Let; subst.
            inversion H9; subst.
            eapply IHbs; eauto using Forall_inv_tail.
            eauto using CNR_Term.
        -- rewrite H0. assumption.
  - (* P_Binding TermBind *)
  unfold P_Term, P_Binding;
  unfold P_Binding_compat, P_Binding_NonRec.
  intros.
  split.
  + (* compat *)
    split.
    * (* fwd*)
      destruct b'; try solve [inversion 1].
      intros.
      simpl in H0.
      simpl_dec_Term.
      rewrite_reflection.
      subst.
      eauto using CNR_Binding_compat.
    * (* bwd *)
      destruct b'; try solve [inversion 1].
      inversion 1; subst.
      simpl_goal.
      repeat split; bwd_reflection.
  + (* P_Binding_NonRec *)
    intros.
    split.
    * (* ∃ fs *)
      intros.
      destruct H0.
      (* simplify dec_Bindings *)
      destruct s;
        try solve [inversion H0]. (* Impossible case*)
      destruct v.
      simpl in H0.
      repeat (match goal with
        | H : match ?t with _ => _ end = _ |- _ => destruct t
      end); try solve [inversion H0].

      exists (desugar_fun s0 t0 t0_2).
      apply dec_Bindings_exists in H0 as [fs H_fs].
      exists fs.
      split.
      ** admit.
      ** unfold apply, desugar_fun. subst t0_1. simpl. reflexivity.
    * admit.

  - (* P_Binding TypeBind *)
    intros.
    unfold P_Binding, P_Binding_compat, P_Binding_NonRec.
    split; admit.
  - (* P_Binding DatatypeBind *)
    admit.
Admitted.



Definition Binding_soundness (b : Binding) :=
  forall s v t, b = TermBind s v t -> forall t' (H_dec_true : dec_Term t t' = true), CNR_Term t t'.

Definition Term_soundness (t : Term) :=
  forall t', forall (H_dec_true : dec_Term t t' = true), CNR_Term t t'.

(* Prove that dec_Bindings' is sound w.r.t CNR_Bindings *)
Lemma sound_dec_bindings {bs t_let_body' t_result}
  (* Every bound term has sound desugaring *)
  ( IH_bindings : ForallT
      (fun b : Binding => forall s v t,
        b = TermBind s v t -> Term_soundness t
      )
      bs
  )

  ( dec_true : dec_Bindings' dec_Term bs t_result = Just t_let_body' )
  : {bs_fs & CNR_Bindings bs bs_fs
           & fold_right apply t_let_body' bs_fs = t_result}.
Proof. Admitted.
  (*
  generalize dependent t_result.
  induction bs as [ | b bs].
    (* nil *)
    + intros.
      inversion dec_true. (* show that t_let_body' = t_result *)
      refine (existT2 _ _ nil CNR_Nil eq_refl).

    (* b :: bs*)
    + intros t_result dec_b_bs_true.
      destruct b as [s v t_bound | | ] .
      (* b = TermBind*)
      { destruct s.
        (* s = NonStrict*)
        { inversion dec_b_bs_true. }
        (* s = Strict*)
        {

          (* Split IH_bindings in head, tail *)
          inversion IH_bindings.
          subst.
          assert (sound_b := X _ _ _ eq_refl).
          clear X.
          rename X0 into sound_bs.
          clear IH_bindings.

          (* destruct until we hit the right branch of dec_Bindings' in dec_b_bs_true *)
          destruct t_result.
          all: try inversion dec_b_bs_true.
          destruct t_result1 eqn:H_t_result1.
          all: try inversion dec_b_bs_true.
          clear H0 H1.
          rename t_result2 into t_bound'.
          rename t_result1 into t_bs.
          rename t into ty.

          (* reflection *)
          simpl in dec_b_bs_true.
          destruct ((v =? s)%string && dec_Term t_bound t_bound') as []eqn:H_v_eq_t_eq.
            (* = false*)
            2: { inversion dec_b_bs_true. }
          bool_assumptions.
          apply String.eqb_eq in H.
          subst.
          rename dec_b_bs_true into dec_bs_true.
          rename H0 into dec_t_bound_true.
          unfold Term_soundness in *.

          (* Combine IHs with decision results *)
          assert (CNR_b := @CNR_Desugar s _ _ tt (sound_b _ dec_t_bound_true)).
            (* TODO: see Note [Refactor VarDecl]*)
            clear sound_b dec_t_bound_true.
          assert (X := IHbs sound_bs _ dec_bs_true).
            clear sound_bs dec_bs_true.
          destruct X as [bs_fs CNR_bs fold_bs_fs].

          assert (CNR_b_bs := (CNR_Cons CNR_b CNR_bs)).

          (* using let instead of assert here because we have to be able to
             unfold f_b. *)
          refine (let f_b := fun x => Apply (LamAbs s ty x) t_bound' in _).
          assert (fold_b_bs :
            fold_right apply t_let_body' (f_b :: bs_fs) = Apply (LamAbs s ty t0) t_bound'
            ).

          (* This was somehow crucial to get things going below *)
          all: destruct ty.

          {
            simpl.
              rewrite -> fold_bs_fs.
              unfold apply.
              reflexivity.
            }

          exact (existT2 _ _ ( (fun x => Apply (LamAbs s tt x) t_bound') :: bs_fs) CNR_b_bs fold_b_bs).
        }
      }
      all: inversion dec_b_bs_true.
Defined.*)



Definition dec_Term_sound t t' : dec_Term t t' = true -> CNR_Term t t'.
Proof. Admitted. (*
  intro H.
  generalize dependent t'.

  (* Use nested induction scheme *)
  apply (Term_rect' Term_soundness Binding_soundness).
  all: unfold Binding_soundness.
  all: unfold Term_soundness.
  all: intros.

  (* Handle impossible bindings *)
  all: try inversion H; subst.

  (* TermBind *)
  12: { auto. }

  (* Let, t'*)
  { destruct rec.
    (* Let NonRec, t'  (desugaring) *)
    { simpl in H_dec_true.
      rename X into IH_bindings.
      rename X0 into IH_t_let_body.
      rename t0 into t_body.

      assert (ex_dec_bs_true : { t_body & dec_Bindings' dec_Term bs t' = Just t_body}).
        { destruct bs.
          { inversion H_dec_true. }
          { destruct (dec_Bindings' dec_Term (b :: bs) t')
              eqn:dec_b_bs_true.
              2: { inversion H_dec_true. }
              eapply existT.
                { reflexivity. }
          }
        }
      destruct ex_dec_bs_true as [ t_body' dec_bs_true ].

      assert (dec_t_body_true : dec_Term t_body t_body' = true).
        { destruct bs.
          { inversion H_dec_true. }
          { destruct (dec_Bindings' dec_Term (b :: bs) t')
              eqn:dec_b_bs_true.
              2: { inversion H_dec_true. }
            inversion dec_bs_true.
            rewrite -> H0 in H_dec_true.
            assumption.
          }
        }
      clear H_dec_true.

      assert (ex_cnr_bs := sound_dec_bindings IH_bindings dec_bs_true).
      destruct ex_cnr_bs as [ bs_fs CNR_bs fold_right_bs].
      rewrite <- fold_right_bs.

      assert (cnr_t_let_body := IH_t_let_body _ dec_t_body_true).

      exact (CNR_Let cnr_t_let_body CNR_bs).

      }
  shelve.
  }

  Unshelve.
  all: destruct t'.

  (* Handle impossible cases*)
  all: try (inversion H_dec_true);
    clear H0. (* when try fails, it doesn't clean up properly*)

  (* Shelve Let, t cases *)
  all: (try match goal with
    | |- CNR_Term (Let _ _ _) _ => shelve
    end
    ).

  (* Handle all compatibility cases except Let Rec, Let Rec *)
  all:
    constructor;
    bool_assumptions;
    subst;
    eauto with reflection eq_principles.

  Unshelve. (* let's prove the remaining Let Recs*)


  (* Let Rec, Let Rec*)
  { apply CNR_Compat.
    destruct r.
      (* Let Rec, Let NonRec (impossible) *)
      {
        destruct bs.
        all: inversion H_dec_true.
      }
      (* Let Rec, Let Rec*)
      {
        (* simplify in H_dec_true*)
        destruct bs, l; try inversion H_dec_true; clear H0.
        simpl in H_dec_true.
        bool_assumptions.
        rename H into binding_dec_true.
        rename H1 into bindings_dec_true.
        rename H0 into body_dec_true.

        apply C_Let.
          {
            apply Compat_Bindings_Cons.
              (* Compat_Binding CNR_Term b b0*)
              { destruct b, b0.
                all: try inversion binding_dec_true.
                all: bool_assumptions.
                (* TermBind, TermBind *)
                {
                  (* Get the IH for t1 *)
                  inversion X.
                  clear X2.
                  assert (IH_t1 := X1 _ _ _ eq_refl).
                  clear X1.

                  apply C_TermBind'.
                  all: auto with reflection.
                }
                { apply C_TypeBind'.
                  all: auto with reflection.
                }
                { apply C_DatatypeBind'.
                  all: auto with reflection.
                }
             }
             { inversion X . clear X1 binding_dec_true X H0 b b0 l0 H1.
               generalize dependent l.
               induction bs as [ | b bs IHbs].
               all: intros bs' H_bs_true.
                  { destruct bs'.
                    { apply Compat_Bindings_Nil. }
                    { inversion H_bs_true. }
                  }

                  (* TODO: this is duplication from the head case above*)
                  { destruct bs' as [ | b' bs'].
                    { inversion H_bs_true. }
                    { apply Compat_Bindings_Cons.
                      {
                        { destruct b, b'.
                          all: try inversion H_bs_true.
                          (* TermBind, TermBind *)
                          {
                            (* Get the IH for t1 *)
                            inversion X2.
                            assert (IH_t1 := X _ _ _ eq_refl).
                            clear X.

                            apply C_TermBind';
                            bool_assumptions.
                            all: auto with reflection.
                          }
                          { apply C_TypeBind';
                            bool_assumptions.
                            all: auto with reflection.
                          }
                          { apply C_DatatypeBind';
                            bool_assumptions.
                            all: auto with reflection.
                          }
                        }
                      }
                      { inversion X2.
                        apply (IHbs X1).
                        simpl in H_bs_true.
                        bool_assumptions.
                        assumption.
                      }
                    }
                  }
             }
          }
          { auto. }
      }
  }

(* The other impossible (Let Rec, t) cases*)
all:
  destruct bs;
  try destruct b;
  try destruct s0;
  try destruct s;
  inversion H_dec_true.
Defined.*)



Definition Binding_completeness (b : Binding) :=
  forall s v t, b = TermBind s v t -> forall t', CNR_Term t t' -> dec_Term t t' = true.

Definition Term_completeness (t : Term) :=
  forall t', CNR_Term t t' -> dec_Term t t' = true .



Definition dec_Term_complete t : forall t', CNR_Term t t' -> dec_Term t t' = true .
Proof. Admitted.
(*
Proof.
  apply (Term_rect' Term_completeness Binding_completeness).
  { intros.
    unfold Term_completeness.
    destruct t'.
    all: intro cnr_t_t'. try inversion cnr_t_t'.

  intros cnr_t_t'.
  all: unfold Term_completeness.
  all: unfold Binding_completeness.
  { intros.
*)
