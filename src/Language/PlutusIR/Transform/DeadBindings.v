From Coq Require Import
  Strings.String
  Lists.List.

From Equations Require Import Equations.

From PlutusCert Require Import
  Util
  Language.PlutusIR
  Language.PlutusIR.Analysis.FreeVars
  Language.PlutusIR.Analysis.Equality
  Language.PlutusIR.Analysis.UniqueBinders
  Language.PlutusIR.Transform.Congruence
  Language.PlutusIR.Semantics.Dynamic.Values
  Static.Typing.

Import NamedTerm.
Import UniqueBinders.Term.

Set Implicit Arguments.
Set Equations Transparent.


Notation fv := (free_vars String.eqb).
Notation fv_binding := (free_vars_binding String.eqb).
Notation fv_bindings := (free_vars_bindings String.eqb fv_binding).



(* Bindings that are safe: removing them will not change termination behaviour *)
Inductive safe_binding : Binding -> Prop :=

  | sb_term_non_strict : forall vd t,
      safe_binding (TermBind NonStrict vd t)

  | sb_term_strict_val : forall vd t,
      value t ->
      safe_binding (TermBind Strict vd t)

  | sb_data : forall dtd,
      safe_binding (DatatypeBind dtd)

  | sb_type : forall tvd ty,
      safe_binding (TypeBind tvd ty)
.



Inductive dead_syn : Term -> Term -> Prop :=
  | dc_cong : forall t t',
      Cong dead_syn t t' ->
      dead_syn t t'

  | dc_delete_let : forall rec bs t t',
      dead_syn t t' ->
      Forall safe_binding bs ->
      dead_syn (Let rec bs t) t'

  | dc_delete_bindings : forall rec bs bs' t t',
      dead_syn t t' ->
      dead_syn_bindings bs bs' ->
      dead_syn (Let rec bs t) (Let rec bs' t')


with dead_syn_bindings : list Binding -> list Binding -> Prop :=
  | dc_bindings : forall bs bs',

      (* Any resulting binding has a (related) binding in the original group *)
      forall b, (In b bs' -> exists b', dead_syn_binding b' b /\ In b' bs) ->
      (* any removed binding is a safe_binding *)
      ((In b bs /\ ~In b bs') -> safe_binding b) ->
      dead_syn_bindings bs bs'

with dead_syn_binding : Binding -> Binding -> Prop :=

  | dc_term_bind_cong : forall s vd t t',
      dead_syn t t' ->
      dead_syn_binding (TermBind s vd t) (TermBind s vd t')

  | dc_binding : forall b b',
      dead_syn_binding b b'
  .

(* TODO: define and use well_scoped instead of well_typed *)
Definition dead_code t t' := dead_syn t t' /\ well_typed t' /\ unique t'.


Lemma dead_syn_sym : forall t, dead_syn t t.
Admitted.


(* DBE_Term relates terms t and t' such that t' is the result of eliminating dead bindings in t *)
Inductive DBE_Term : Term -> Term -> Type :=

    | DBE_Congruence : forall {t t'},
        Cong DBE_Term t t' ->
        DBE_Term t t'

    | DBE_RemoveBindings : forall {t_body t_body' bs bs' rec},
        DBE_Term t_body t_body' ->
        DBE_Bindings rec bs' bs bs' t_body' ->
        DBE_Term (Let rec bs t_body) (Let rec bs' t_body')

    | DBE_RemoveLet : forall {t t' bs rec},
        DBE_Term t t' -> DBE_Bindings rec nil bs nil t' ->
        DBE_Term (Let rec bs t) t'

  with DBE_Binding :
    list string -> (* The free variables in the (resulting) terms this binding scopes over *)
    Binding ->
    Type :=
  (* To check if a term-binding `x = e` can be eliminated,
     we check that its variable does not occur freely in
     the _resulting_ terms that the binding scopes over
     (for a letrec, this includes the other bindings of that group)
  *)
    | DBE_RemoveTermBind : forall {v stric t_bound T vars},
        ~ In v vars ->
        (stric = Strict -> value t_bound) -> (* strict bindings may have side-effects and can safely be removed when they are values *)
        DBE_Binding vars (TermBind stric (VarDecl v T) t_bound)

  with DBE_Bindings : Recursivity ->
    list Binding ->  (* resulting bindings before&after this binding (needed for checking free variables in recursive binding groups) *)
    list Binding ->  (* original bindings after this binding *)
    list Binding ->  (* resulting bindings after this binding *)
    Term ->  (* let-body *)
    Type :=

    | DBE_Keep   : forall {rec b bs'_all bs bs' t},
        DBE_Bindings rec bs'_all bs bs' t ->
        DBE_Bindings rec bs'_all (b :: bs) (b :: bs') t

    | DBE_Remove : forall {rec bs'_all b bs bs' t_body' vars},
        DBE_Bindings rec bs'_all bs bs' t_body' ->
        (vars = (fv t_body') ++ (fv_bindings rec
          (match rec with | Rec => bs'_all | NonRec => bs' end))
        ) ->
        DBE_Binding vars b ->
        DBE_Bindings rec bs'_all (b :: bs) (     bs') t_body'

    | DBE_Nil    : forall {bs'_all rec t},
        DBE_Bindings rec bs'_all nil nil t
    .


Local Open Scope string_scope.
(* TODO: Does not consider types, tt is mapped to built-in strings *)
Definition tt := @Ty_Builtin tyname binderTyname (Some (@TypeIn DefaultUniString)).
Definition subTerm : Term :=
       (LamAbs (Name "ds" (Unique 75)) tt
          (LamAbs (Name "ds" (Unique 76)) tt
             (Apply
                (Apply
                   (Apply
                      (TyInst
                         (Apply (Var (Name "EndDate_match" (Unique 74)))
                            (Var (Name "ds" (Unique 75)))) tt)
                      (LamAbs (Name "n" (Unique 78)) tt
                         (LamAbs (Name "thunk" (Unique 79)) tt
                            (Apply
                               (Apply
                                  (Var (Name "lessThanEqInteger" (Unique 30)))
                                  (Var (Name "n" (Unique 78))))
                               (Var (Name "ds" (Unique 76)))))))
                   (LamAbs (Name "thunk" (Unique 80)) tt
                      (Var (Name "False" (Unique 3)))))
                (Var (Name "Unit" (Unique 12)))))).

Lemma test2 : ~(In "trace" (fv subTerm)). notIn2. Qed.

Lemma test : ~(In "trace" (fv subTerm)).
Proof. notIn. Qed.

(* This must be somewhere in the standard lib*)

(*
(* https://github.com/mattam82/Coq-Equations/issues/329 *)
Equations dbe_dec_Term (t1 t2 : Term) : option (DBE_Term t1 t2) :=
  dbe_dec_Term _ _ := None

  where dbe_dec_Binding (b : Binding) (t : Term)  : option (DBE_Binding b t) :=

    dbe_dec_Binding (TermBind stric (VarDecl n ty) t') t    :=
      DBE_RemoveTermBind <$> in_dec_option n (free_vars t);

     dbe_dec_Binding (TypeBind (TyVarDecl n k) ty) t        :=
      pure DBE_RemoveTypeBind;

     dbe_dec_Binding (DatatypeBind (Datatype d ds n vds)) t :=
          pure DBE_RemoveDatatype

  where dbe_dec_Bindings (bs bs' : list Binding) (t : Term) : option (DBE_Bindings bs bs' t) by struct bs:=
    {
    dbe_dec_Bindings nil nil               t                    := Just DBE_Nil;
    dbe_dec_Bindings (b :: bs) nil         t                    := None;
    dbe_dec_Bindings nil (b :: bs)         t                    := None;
    dbe_dec_Bindings (b :: bs) (b' :: bs') t with binding_dec b b' := {
      dbe_dec_Bindings (b :: bs) (?(b) :: bs') t (left eq_refl) := None; (*DBE_Keep <$> dbe_dec_Bindings bs bs' t;*)
      dbe_dec_Bindings _         _             t (right _)      := None
      }
    }
.
*)

Inductive E (A : Type) (x : A) : A -> Type :=
  | EEq : E x x
  | ENeq : forall y, E x y
.

Definition myEq (A : Type) (x y : A) (e : x = y) : E x y:=
match e in (_ = y0) return (E x y0) with
  | eq_refl => EEq x
end.





(* Old decision procedure *)
(*
Fixpoint dbe_dec_Binding (b : Binding) (t : Term) {struct b} : option (DBE_Binding b t) :=
    match b with
      | TermBind stric (VarDecl n T) t'   =>
          DBE_RemoveTermBind <$> in_dec_option n (free_vars t)

      | TypeBind (TyVarDecl n k) ty        =>
          pure DBE_RemoveTypeBind

      | DatatypeBind (Datatype d ds n vds) =>
          pure DBE_RemoveDatatype
    end.

Fixpoint dbe_dec_Bindings (bs bs' : list Binding) (t : Term) {struct bs} :=
  (* : option (DBE_Bindings bs bs' t):= *)
    match bs, bs' with
      | (b :: bs), (b' :: bs') =>
        match binding_dec b b'
          with
          | left e  =>
              match e
                in     _ = x
                return option (DBE_Bindings (b :: bs) (x :: bs') t)
                with
                | eq_refl => DBE_Keep <$> dbe_dec_Bindings bs bs' t
              end
          | _             => (* todo, make sure that dbe_dec_Binding gets evaluated first *)
                             DBE_Remove <$> dbe_dec_Bindings bs (b' :: bs') t <*> dbe_dec_Binding b t
          end
      | (b :: bs), nil    => (* note: I couldn't get this to work when matching on bs instead of nil *)
                             DBE_Remove <$> dbe_dec_Bindings bs nil t <*> dbe_dec_Binding b t
      | nil, nil          => pure DBE_Nil
      | _, _              => None
    end
    .

Equations dbe_dec_Term (t1 t2 : Term) : option (DBE_Term t1 t2) :=
  {
  dbe_dec_Term t1 t2 :=
        dbe_dec_cong t1 t2
    <|> dbe_dec_rmlet t1 t2
    <|> dbe_dec_rmbnd t1 t2
  }

  where
    dbe_dec_cong (t1 t2 : Term) : option (DBE_Term t1 t2) :=
    {
    dbe_dec_cong t t' :=  DBE_Congruence <$> (cong_dec DBE_Term dbe_dec_Term t t')
    }

  where
    dbe_dec_rmlet (t1 t2 : Term) : option (DBE_Term t1 t2) :=
    {
    dbe_dec_rmlet (Let rec bs t) t2 := DBE_RemoveLet <$> dbe_dec_Term t t2 <*> dbe_dec_Bindings bs nil t2;
    dbe_dec_rmlet _ _ := Nothing
    }

  where
    dbe_dec_rmbnd (t1 t2 : Term) : option (DBE_Term t1 t2) :=
    {
    dbe_dec_rmbnd (Let rec bs t) (Let rec' bs' t') :=
      match Recursivity_dec rec rec' with
        (* | left eq_refl => DBE_RemoveBindings <$> dbe_dec_Term t t' <*> dbe_dec_Bindings bs bs' (Let rec bs' t') *)
        (* has type
            "option (DBE_Term (Let rec bs t) (Let rec bs' t'))"
           while it is expected to have type
            "option (DBE_Term (Let rec bs t) (Let rec' bs' t'))".
         *)

        | left e =>
          match e
          (* in (_ = r) *)
          (* return option (DBE_Term (Let rec bs t) (Let r bs' t'))*)
          with
          | eq_refl => DBE_RemoveBindings <$> dbe_dec_Term t t' <*> dbe_dec_Bindings bs bs' (Let rec bs' t')
          end
        | _            => Nothing

        end;
    (*

    (*This breaks. Generated code applies too many arguments *)

    dbe_dec_rmbnd (Let rec bs t) (Let rec' bs' t')
      with Recursivity_dec rec rec' =>
      { | left eq_refl := DBE_RemoveBindings <$> dbe_dec_Term t t' <*> dbe_dec_Bindings bs bs' (Let rec bs' t'); (*Todo @ pattern for t2?*)
        | _            := Nothing};

    *)
    dbe_dec_rmbnd _ _ := Nothing
    }.

*)




Ltac elim_let :=
  apply DBE_RemoveLet; [ | apply DBE_Remove; [ | constructor; notIn2; notIn2]; apply DBE_Nil].

Ltac elim_binds :=
  apply DBE_RemoveBindings; [ | repeat constructor; fail ].

Ltac term_cong :=
  apply DBE_Congruence; constructor.

(* Separate case for let congruence *)
Ltac term_cong_let := apply DBE_Congruence; apply C_Let;
  [ constructor; [constructor|constructor]
  | ].






Tactic Notation "step" hyp(n) :=
  destruct n;
  [ exact Nothing
  | refine (_ )
  ].


(*
Definition is_dbe : forall (n : nat) (t t' : Term) ,
  option (DBE_Term t t').
Proof.

(* The mutually recursive structure *)
refine (
  fix is_dbe (n : nat) : forall t t', option (DBE_Term t t') :=

    let is_dbe_cong (n : nat) : forall t t', option (DBE_Term t t')
      := ?[is_dbe_cong] in
    let is_dbe_var (n : nat) : forall t t', option (DBE_Term t t')
      := ?[is_dbe_remove_bindings] in
    let is_dbe_let (n : nat) : forall t t', option (DBE_Term t t')
      := ?[is_dbe_remove_let] in

    fun t t' => is_dbe_var n t t' <|> is_dbe_let n t t' <|> is_dbe_cong n t t'

  with is_dbe_binding (n : nat) : forall b b', option (DBE_Binding b b') :=
    ?[is_dbe_binding]

  with is_dbe_bindings (n : nat) : forall bs bs' t, option (DBE_Bindings bs bs' t) :=
    ?[is_dbe_bindings]

  with is_cong (n : nat) : forall t t', option (Cong DBE_Term t t') :=
    ?[is_cong]

  with is_cong_binding (n : nat) : forall b b', option (Cong_Binding DBE_Term b b') :=
    ?[is_cong_binding]

  with is_cong_bindings (n : nat) : forall bs bs', option (Cong_Bindings DBE_Term bs bs') :=
    ?[is_cong_bindings]

  for is_dbe
).
Abort.
*)


(*
[is_dbe_remove_let]: {.
intros t t'.
step n.

refine(
  match t with
    | Let r bs t => _
    | _          => Nothing
    end
  ).
Abort.
*)

(* TODO: adapt from inline


[is_dbe_let]: {.
clear is_dbe_var. (* so noisy *)
intros t t'.
step n.

refine (
  match t as p return t = p -> _ with
  | Let r bs b  => fun H1 => match t' as p' return t' = p' -> _ with
    | Let r' bs' b' => fun H2 => match Recursivity_dec r r' with
      | left rH => _
      | _ => Nothing
      end
    | _             => fun _  => Nothing
    end eq_refl
  | _ => fun _ => Nothing
  end eq_refl
); subst.
refine (
  (@Inl_Let _ bs bs' b b' r' eq_refl)
    <$> is_dbe_bindings n bs bs' _
    <*> is_dbe n b b' _
).
}

[is_dbe_cong] : {.
  intros t t'.
  step n.

  refine (
    Inl_Cong <$> is_cong n t t'
  ).
}

[is_dbe_bindings]: {.
  intros bs bs'.
  step n.

  refine (
    (* Coq is clever, do not have to carry eq_refls around*)
    match bs, bs' with
    | (b :: bs), (b' :: bs') => ?[cons]
    | nil      , nil         => ?[nil]
    | _        , _           => Nothing
    end
  ).

  [cons]: {.
    refine (
      Inl_Binding_cons
        <$> is_dbe_binding n b b'
        <*> is_dbe_bindings n bs bs'
    ).
  }

  [nil]: {.
    refine (Just Inl_Binding_nil).
  }
}

[is_dbe_binding]: {.
  intros b b'.
  step n.

  refine (
    match b, b' with
      | TermBind s v t, TermBind s' v' t' => match Strictness_dec s s' with
        | left Hs => match VDecl_dec v v' with
          | left Hv => ?[termbinds]
          | right _ => Nothing
          end
        | right _ => Nothing
        end

      | TypeBind v ty, TypeBind v' ty' => match TVDecl_dec v v', Ty_dec ty ty' with
        | left Hv, left Hty => ?[tyty]
        | _, _ => Nothing
        end

      | DatatypeBind d, DatatypeBind d' => match DTDecl_dec d d' with
        | left Hd => ?[dtdt]
        | _ => Nothing
        end
      | _, _ => Nothing
      end
  ).

  [termbinds]: {.
    subst.
    refine (Inl_TermBind <$> is_dbe n t t').
  }
  [tyty]: {.
    subst.
    refine (Just Inl_OtherBind).
  }
  [dtdt]: {.
    subst.
    refine (Just Inl_OtherBind).
  }
}

[is_cong]: {.
  intros t t'.
  step n.

  refine (
  match t, t' as p with
  | Let r bs t, Let r' bs' t' => ?[letlet]
          <$> (sumbool_to_optionl (Recursivity_dec r r'))
          <*> is_cong_bindings n bs bs'
          <*> is_dbe n t t'

  | Apply s t, Apply s' t' => C_Apply _
          <$> is_dbe n s s'
          <*> is_dbe n t t'

  | Var n, Var m => ?[vars] <$> sumbool_to_optionl (string_dec n m)

  | TyAbs v k t
  , TyAbs v' k' t' => match string_dec v v', Kind_dec k k' with
    | left Hs, left Hk => ?[tyabs]
    | _, _ => Nothing
    end

  | LamAbs v ty t
  , LamAbs v' ty' t' => match string_dec v v', Ty_dec ty ty' with
    | left Hs, left Ht => ?[lamabs]
    | _, _ => Nothing
    end

  | TyInst t ty
  , TyInst t' ty' => match Ty_dec ty ty' with
    | left Hty => ?[tyinst]
    | _ => Nothing
    end

  | IWrap ty1 ty2 t
  , IWrap ty1' ty2' t' => match Ty_dec ty1 ty1', Ty_dec ty2 ty2' with
    | left Hty1, left Hty2 => ?[iwrap]
    | _, _ => Nothing
    end
  | Unwrap t,
    Unwrap t' => ?[unwrap]

  | Constant c,
    Constant c' => match some_dec c c' with
      | left Hs => ?[constant]
      | _ => Nothing
      end

  | Builtin f,
    Builtin f' => match func_dec f f' with
      | left Hb => ?[builtin]
      | _ => Nothing
      end

  | Error ty
  , Error ty' => match Ty_dec ty ty' with
      | left Hty => ?[error]
      | _ => Nothing
      end

  | _, _ => Nothing
  end
  ).

  [letlet]: {.
  intros. subst. constructor; assumption.
  }

  [vars]: {.
  intros. subst. constructor.
  }

  [lamabs]: {.
    subst.
    refine (
      C_LamAbs _ <$> is_dbe n t t'
    ).
  }
  [tyabs]: {.
    subst.
    refine (
      C_TyAbs _ <$> is_dbe n t t'
    ).
  }
  [tyinst]: {.
    subst.
    refine (
      C_TyInst _ <$> is_dbe n t t'
    ).
  }
  [iwrap]: {.
    subst.
    refine (
      C_IWrap _ <$> is_dbe n t t'
    ).
  }
  [unwrap]: {.
    subst.
    refine (
      C_Unwrap _ <$> is_dbe n t t'
    ).
  }
  [constant]: {.
    subst.
    refine (
      Just (C_Constant _)
    ).
  }
  [builtin]: {.
    subst.
    refine (
      Just (C_Builtin _)
    ).
  }

  [error]: {.
    subst.
    refine (
      Just (C_Error _)
    ).
  }
}

[is_cong_binding]: {.
  intros b b'.
  step n.

  refine(
  match b, b' with
    | TermBind s  v  t
    , TermBind s' v' t' => match Strictness_dec s s', string_dec v v' with
      | left Hs, left Hv => ?[termbind]
      | _, _ => Nothing
      end

    | TypeBind v ty
    , TypeBind v' ty' => match TVDecl_dec v v', Ty_dec ty ty' with
      | left Hv, left Hty => ?[typebind]
      | _, _ => Nothing
      end

    | DatatypeBind d
    , DatatypeBind d' => match DTDecl_dec d d' with
      | left Hd => ?[datatypebind]
      | _ => Nothing
      end

    | _, _ => Nothing
    end
  ).

  [termbind]: {.
    subst.
    refine (C_TermBind _ <$> is_dbe n t t'); exact tt. (* fake types*)
    }
  [typebind]: {.
    subst. refine (Just _). constructor.
  }
  [datatypebind]: {.
    subst. refine (Just _). constructor.
  }
}

[is_cong_bindings]: {.
  intros bs bs'.
  step n.

  refine (
    match bs, bs' with
    | (b :: bs), (b' :: bs') => ?[cons]
    | nil      , nil         => ?[nil]
    | _        , _           => Nothing
    end
  ).

  [cons]: {.
    refine (
      Cong_Bindings_Cons (R := DBE)
        <$> is_cong_binding n b b'
        <*> is_cong_bindings n bs bs'
    ).
  }

  [nil]: {.
    refine (Just (Cong_Bindings_Nil _)).
  }
}
Defined.
*)
