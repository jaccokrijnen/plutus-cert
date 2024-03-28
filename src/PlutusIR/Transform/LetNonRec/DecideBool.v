From Coq Require Import
  String
  List
  Bool
  Program.

From PlutusCert Require Import
  Util
  PlutusIR
  PlutusIR.Analysis.Equality
  PlutusIR.Transform.Compat
  PlutusIR.Transform.LetNonRec.Spec.
Import NamedTerm.

(*
   Returns `Just t'` if bindings were desugared correctly, where t' is the rest
   of the desugared term.

   Note that Term_desugar has to be passed manually. In this form, the
   termination checker is happy when checking Term_desugar (it's probably
   inlining Bindings_desugar within Term_desugar, and then sees the structural
   recursive call to Term_desugar.

   We want this as a separate definition so that proofs don't have to deal with
   a big (fix ...) expression. The termination checker doesn't allow it to be
   part of the mutual recursive binding group of Term_desugar, so this is the
   workaround.

   Below is a specialized version Bindings_desugar that you do not have to pass
   Term_desugar.
*)
Definition Bindings_desugar' :=
  fun (Term_desugar : Term -> Term -> bool) =>
    (fix Bindings_desugar'
            (bs : list Binding) (t : Term) {struct bs} := match bs with
            | nil       => Just t
            | cons b bs => match b, t with
              | TermBind Strict (VarDecl v ty) rhs, Apply (LamAbs v' ty' body') rhs' =>
                if (String.eqb v v' && Ty_eqb ty ty' && Term_desugar rhs rhs')
                  then Bindings_desugar' bs body'
                  else None
                (* Notation scope analysis fails, not sure why....*)
              | _, _ => None
              end
            end).

(*
  Returns true if the term was desugared correctly.
*)
Fixpoint Term_desugar (x y : Term) {struct x} : bool := match x, y with

  (* We don't allow empty binding groups. This should be visible
     from the AST type (as it is in plutus implementation)
  *)
  | Let _ nil _ , _ => false

  (* non-recursive bindings should be desugared *)
  | Let NonRec bs body, t =>
       match Bindings_desugar' Term_desugar bs t with
        | Just body' => Term_desugar body body'
        | Nothing    => false
       end

  (* Other cases should be compatible, i.e. identical constructors
     and recursive Terms recursively desugared *)
  | Let Rec bs t, Let Rec bs' t' =>
      list_eqb Binding_desugar bs bs'
        && Term_desugar t t'
  | Var n          , Var n'             => String.eqb n n'
  | TyAbs n k t    , TyAbs n' k' t'     => String.eqb n n' && Kind_eqb k k' && Term_desugar t t'
  | LamAbs n ty t  , LamAbs n' ty' t'   => String.eqb n n' && Ty_eqb ty ty' && Term_desugar t t'
  | Apply s t      , Apply s' t'        => Term_desugar s s' && Term_desugar t t'
  | Constant c     , Constant c'        => some_valueOf_eqb c c'
  | Builtin f      , Builtin f'         => func_eqb f f'
  | TyInst t ty    , TyInst t' ty'      => Term_desugar t t' && Ty_eqb ty ty'
  | Error ty       , Error ty'          => Ty_eqb ty ty'
  | IWrap ty1 ty2 t, IWrap ty1' ty2' t' => Ty_eqb ty1 ty1' && Ty_eqb ty2 ty2' && Term_desugar t t'
  | Unwrap t       , Unwrap t'          => Term_desugar t t'

  | _, _ => false
  end
with Binding_desugar (b b' : Binding) : bool := match b, b' with
  (* These cases are only used for recursive let-bindings, i.e.
     equal and recursive Terms should be desugared *)
  | TermBind s vdecl t, TermBind s' vdecl' t' => Strictness_eqb s s' && VDecl_eqb vdecl vdecl' && Term_desugar t t'
  | TypeBind tvdecl ty, TypeBind tvdecl' ty'  => TVDecl_eqb tvdecl tvdecl' && Ty_eqb ty ty'
  | DatatypeBind dtd  , DatatypeBind dtd'     => DTDecl_eqb dtd dtd'
  | _, _ => false
  end
.

(* See comment of Bindings_desugar' *)
Definition Bindings_desugar
     : list Binding -> Term -> option Term := Bindings_desugar' Term_desugar.


(*

Note [IH for nested datatypes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Usual IH used by `induction` tactic does not suffice, it only holds
for _direct_ subterms, and not for subterms within a list subterm.

- Define an induction/recursion scheme similarly to Term_desugar above.
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

Definition Binding_soundness (b : Binding) :=
  forall s v t, b = TermBind s v t -> forall t' (H_dec_true : Term_desugar t t' = true), CNR_Term t t'.

Definition Term_soundness (t : Term) :=
  forall t', forall (H_dec_true : Term_desugar t t' = true), CNR_Term t t'.

(* Prove that Bindings_desugar' is sound w.r.t CNR_Bindings *)
Lemma sound_dec_bindings {bs t_let_body' t_result}
  (* Every bound term has sound desugaring *)
  ( IH_bindings : ForallT
      (fun b : Binding => forall s v t,
        b = TermBind s v t -> Term_soundness t
      )
      bs
  )

  ( dec_true : Bindings_desugar' Term_desugar bs t_result = Just t_let_body' )
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

          (* destruct until we hit the right branch of Bindings_desugar' in dec_b_bs_true *)
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
          destruct ((v =? s)%string && Term_desugar t_bound t_bound') as []eqn:H_v_eq_t_eq.
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



Definition Term_desugar_sound t t' : Term_desugar t t' = true -> CNR_Term t t'.
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

      assert (ex_dec_bs_true : { t_body & Bindings_desugar' Term_desugar bs t' = Just t_body}).
        { destruct bs.
          { inversion H_dec_true. }
          { destruct (Bindings_desugar' Term_desugar (b :: bs) t')
              eqn:dec_b_bs_true.
              2: { inversion H_dec_true. }
              eapply existT.
                { reflexivity. }
          }
        }
      destruct ex_dec_bs_true as [ t_body' dec_bs_true ].

      assert (dec_t_body_true : Term_desugar t_body t_body' = true).
        { destruct bs.
          { inversion H_dec_true. }
          { destruct (Bindings_desugar' Term_desugar (b :: bs) t')
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
  forall s v t, b = TermBind s v t -> forall t', CNR_Term t t' -> Term_desugar t t' = true.

Definition Term_completeness (t : Term) :=
  forall t', CNR_Term t t' -> Term_desugar t t' = true .



Definition Term_desugar_complete t : forall t', CNR_Term t t' -> Term_desugar t t' = true .
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
