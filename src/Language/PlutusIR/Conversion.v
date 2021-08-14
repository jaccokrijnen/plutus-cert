Require PlutusCert.Language.PlutusIR.
From Equations Require Equations.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Strings.String.
Import StringSyntax.

From Coq Require Import Arith.

Open Scope string_scope.

(** * Conversion between terms using different variable representations *)

(** ** Finding index of element 
    These functions facilitate finding the index of the first element in a list 
    that satisfies a predicate. This index finding is used for determining the 
    DeBruijn index that corresponds to a String variable.
*)

Fixpoint find_index' {X : Type} (p : X -> bool) (xs : list X) (ind : nat) : option nat :=
  match xs with
  | [] => None
  | (x :: xs') => if p x then Some ind else find_index' p xs' (S ind)
  end.

Definition find_index {X : Type} (p : X -> bool) (xs : list X) : option nat :=
  find_index' p xs 0. 

(** *** Correctness of [find_index] and [find_index'] 
    The lemmas below relate [nth_error] to [find_index] and [find_index'].
*)

Lemma find_index'_finds_first : forall bs n b i,
    nth_error bs n = Some b ->
    ~(exists m, m < n /\ nth_error bs m = Some b) ->
    find_index' (eqb b) bs i = Some (i + n).
Proof.
  induction bs; intros.
  - destruct n; destruct i; discriminate.
  - destruct n eqn:Hn.
    + simpl.
      inversion H. subst.
      rewrite eqb_refl.
      rewrite <- plus_n_O.
      reflexivity.
    + simpl.
      destruct (b =? a) eqn:Heqb.
      * assert (exists m, m < 0 + S n0 /\ nth_error (a :: bs) m = Some b). {
          exists 0. split.
          + simpl. apply Nat.lt_0_succ.
          + simpl. apply eqb_eq in Heqb. subst. reflexivity.
        }
        apply H0 in H1.
        destruct H1.
      * rewrite <- plus_n_Sm.
        rewrite <- plus_Sn_m.
        apply IHbs.
        -- apply H.
        -- intros Hcon.
           apply H0.
           destruct Hcon as [m [Hlt Hnth]].
           exists (S m).
           split.
           ++ apply -> Nat.succ_lt_mono.
              apply Hlt.
           ++ apply Hnth.
Qed.

Lemma find_index_finds_first : forall bs n b,
    nth_error bs n = Some b ->
    ~(exists m, m < n /\ nth_error bs m = Some b) ->
    find_index (eqb b) bs = Some n.
Proof. 
  intros. unfold find_index. 
  replace n with (0 + n) by reflexivity. 
  apply find_index'_finds_first.
  - apply H.
  - apply H0.
Qed.



Module ConvertFunc.

Import PlutusCert.Language.PlutusIR.

Import Coq.Init.Datatypes.

Import Equations.


Equations ty_to' (vars : list string) (T : NamedTerm.Ty) : option DeBruijnTerm.Ty :=
  ty_to' vars (Ty_Var X) := 
    match find_index (eqb X) vars with
    | Some ind => Some (Ty_Var ind)
    | None => None
    end ;
  ty_to' vars (Ty_Fun T1 T2) :=
    match ty_to' vars T1, ty_to' vars T2 with
    | Some T1', Some T2' => Some (Ty_Fun T1' T2')
    | _, _ => None
    end ;
  ty_to' vars (Ty_IFix F T) :=
    match ty_to' vars F, ty_to' vars T with
    | Some F', Some T' => Some (Ty_IFix F' T')
    | _, _ => None
    end ;
  ty_to' vars (Ty_Forall X K T) :=
    match ty_to' (X :: vars) T with
    | Some T' => Some (Ty_Forall tt K T')
    | _ => None
    end ;
  ty_to' vars (Ty_Builtin u) := Some (Ty_Builtin u) ;
  ty_to' vars (Ty_Lam X K T) :=
    match ty_to' (X :: vars) T with
    | Some T' => Some (Ty_Lam tt K T')
    | _ => None
    end ;
  ty_to' vars (Ty_App T1 T2) :=
    match ty_to' vars T1, ty_to' vars T2 with
    | Some T1', Some T2' => Some (Ty_App T1' T2')
    | _, _ => None
    end.

Definition var_bound_by_constructor (c : NamedTerm.constructor) : string :=
  match c with
  | Constructor (VarDecl x _) _ => x
  end.

Definition vars_bound_by_binding (b : NamedTerm.Binding) : list string :=
  match b with
  | TermBind _ (VarDecl x _) _ => [x]
  | TypeBind (TyVarDecl X _) _ => [X]
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => matchFunc :: (rev (map var_bound_by_constructor cs)) ++ [X]
  end.

Definition var_bound_by_tvdecl (tvd : NamedTerm.TVDecl) : string :=
  match tvd with
  | TyVarDecl X _ => X
  end.

Definition vars_bound_by_bindings (bs : list NamedTerm.Binding) : list string := List.concat (List.rev (map vars_bound_by_binding bs)).

Definition tvdecl_to (tvd : NamedTerm.TVDecl) : DeBruijnTerm.TVDecl := match tvd with | TyVarDecl X K => TyVarDecl tt K end.

Equations term_to' (vars : list string) (t : NamedTerm.Term) : option DeBruijnTerm.Term := {
  term_to' vars (Let NonRec bs t0) =>
    match bindings_to' vars bs, term_to' (vars_bound_by_bindings bs ++ vars) t0 with
    | Some bs', Some t0' => Some (Let NonRec bs' t0') 
    | _, _ => None
    end ;
  term_to' vars (Let Rec bs t0) => 
    match bindings_to' (vars_bound_by_bindings bs ++ vars) bs, term_to' (vars_bound_by_bindings bs ++ vars) t0 with
    | Some bs', Some t0' => Some (Let NonRec bs' t0') 
    | _, _ => None
    end ;
  term_to' vars (Var x) =>
    match find_index (eqb x) vars with 
    | Some ind => Some (Var ind)
    | _ => None
    end ;
  term_to' vars (TyAbs X K t0) => 
    match term_to' (X :: vars) t0 with
    | Some t0' => Some (TyAbs tt K t0')
    | None => None
    end ;
  term_to' vars (LamAbs x T t0) =>
    match ty_to' vars T, term_to' (x :: vars) t0 with
    | Some T', Some t0' => Some (LamAbs tt T' t0')
    | _, _ => None
    end ;
  term_to' vars (Apply t1 t2) => 
    match term_to' vars t1, term_to' vars t2 with
    | Some t1', Some t2' => Some (Apply t1' t2')
    | _, _ => None
    end ;
  term_to' vars (Constant u) => 
    Some (Constant u) ;
  term_to' vars (Builtin d) => 
    Some (Builtin d) ;
  term_to' vars (TyInst t0 T) => 
    match term_to' vars t0, ty_to' vars T with
    | Some t0', Some T' => Some (TyInst t0' T')
    | _, _ => None
    end ;
  term_to' vars (Error T) => 
    match ty_to' vars T with
    | Some T' => Some (Error T')
    | _ => None
    end ;
  term_to' vars (IWrap F T t0) => 
    match ty_to' vars F, ty_to' vars T, term_to' vars t0 with
    | Some F', Some T', Some t0' => Some (IWrap F' T' t0')
    | _, _, _ => None
    end ;
  term_to' vars (Unwrap t0) =>
    match term_to' vars t0 with
    | Some t0' => Some (Unwrap t0')
    | _ => None
    end }

where bindings_to' (vars : list string) (bs : list NamedTerm.Binding) : option (list DeBruijnTerm.Binding) := {
  bindings_to' vars nil => Some nil ;
  bindings_to' vars (TermBind s (VarDecl x T) t :: bs) => 
    match ty_to' vars T, term_to' vars t, bindings_to' vars bs with
    | Some T', Some t', Some bs' => Some (TermBind s (VarDecl tt T') t' :: bs')
    | _, _, _ => None
    end ;
  bindings_to' vars (TypeBind (TyVarDecl X K) T :: bs) =>
    match ty_to' vars T, bindings_to' vars bs with
    | Some T', Some bs' => Some (TypeBind (TyVarDecl tt K) T' :: bs')
    | _, _ => None
    end ;
  bindings_to' vars (DatatypeBind (Datatype X YKs matchFunc cs) :: bs) =>
    match constructors_to' ((rev (map var_bound_by_tvdecl YKs))++ [var_bound_by_tvdecl X] ++ vars) cs, bindings_to' vars bs with
    | Some cs', Some bs' => Some (DatatypeBind (Datatype (tvdecl_to X) (map tvdecl_to YKs) tt cs') :: bs')
    | _, _ => None
    end }

where constructors_to' (vars : list string) (cs : list NamedTerm.constructor) : option (list DeBruijnTerm.constructor) := {
  constructors_to' vars nil => Some nil ;
  constructors_to' vars (Constructor (VarDecl x T) ar :: cs) =>
    match ty_to' vars T, constructors_to' vars cs with
    | Some T', Some cs' => Some (Constructor (VarDecl tt T') ar :: cs')
    | _, _ => None
    end }.

Definition to (t : NamedTerm.Term) : option DeBruijnTerm.Term := term_to' nil t.

End ConvertFunc.



Module ConvertInductive.



End ConvertInductive.