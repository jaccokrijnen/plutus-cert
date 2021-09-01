From PlutusCert Require Import
  Language.PlutusIR
  Language.PlutusIR.Transform.Congruence
  Language.PlutusIR.Analysis.Equality
  Language.PlutusIR.Analysis.FreeVars.
Import NamedTerm.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.


Notation fv := (freeVars String.eqb).

(* Find adjacent lets of given recursivity at the top of the AST *)
Fixpoint adjacentBindings r (t : Term) : list Binding * Term :=
    match t with
      | Let r' bs t => if Recursivity_eqb r' r
          then
            let (bs', t') := adjacentBindings r t
            in (bs ++ bs', t')
          else (nil, t)
      | _            => (nil, t)
    end.


(* Adjacent let-binding groups (with same recursivity) can be merged *)
Inductive LetMerge : Term -> Term -> Type :=
  | LM_Merge : forall bs bs' bs'' r t t' t'',
                   (bs', t') = adjacentBindings r t
                -> ZipWith (BindingBy LetMerge) (bs ++ bs') bs''
                -> LetMerge t' t''
                -> LetMerge (Let r bs   t )
                            (Let r bs'' t'')

  (* Todo: if we want to generalize it so that not all adjacent let-groups are merged (more
     general), we probably need some relation instead of the function adjacentBindings
  *)
  | LM_Cong : forall t t', Cong LetMerge t t' -> LetMerge t t'.



Section SubList.

  Inductive SubList {a} : list a -> list a -> Type :=
    | SL_nil  : forall ys     ,                             SubList nil       ys
    | SL_cons : forall x xs ys, In x ys -> SubList xs ys -> SubList (x :: xs) ys
    .

End SubList.



(* Apply a single swap in a list, given that the elements are related
   through R *)
Inductive SwapIn {a : Type} {R : a -> a -> Type} : list a -> list a -> Type :=

  | Swap_Top : forall {x1 x2 xs},
      R x1 x2 ->
      SwapIn (x1 :: x2 :: xs) (x2 :: x1 :: xs)

  | Swap_Pop  : forall {x xs xs'},
      SwapIn       xs        xs' ->
      SwapIn (x :: xs) (x :: xs')
  .
Arguments SwapIn {_} _.

(* Apply multiple swaps in a a list (transitive closure) *)
Inductive SwapsIn {a : Type} (R : a -> a -> Type) : list a -> list a -> Type :=
  | SwapsIn_cons : forall xs ys zs,
      SwapIn R xs ys ->
      SwapsIn R ys zs ->
      SwapsIn R xs zs
  | SwapsIn_nil  : forall xs, SwapsIn R xs xs.


(*
 Can non-recursive bindings
    { x = xt; y = yt }
 be rewritten to
    { y = yt; x = xt}
 ?
*)
Inductive Bindings_NonRec_Commute : Binding -> Binding -> Type :=
  | BC_NonStrict:  forall x y xt yt T,
       ~ (x = y)         -> (* They can't bind the same name.
                               Although this could be allowed in specific cases,
                               when both are dead bindings, or are binding
                               equivalent terms *)
       ~ (In x (fv yt)) -> (* yt may not depend on x *)
       ~ (In y (fv xt)) -> (* if xt has a free var y, swapping would shadow that variable *)

       Bindings_NonRec_Commute
         (TermBind NonStrict (VarDecl x T) xt)
         (TermBind NonStrict (VarDecl y T) yt)

  | BC_DatatypeL: forall ty args matchf constructors strictness x xt T,
       Forall (fun v => ~(In v (fv xt))) (matchf :: (map constructorName constructors)) ->
       Bindings_NonRec_Commute
         (DatatypeBind (Datatype ty args matchf constructors))
         (TermBind strictness (VarDecl x T) xt)

  (* e.g. BC_DatatypeR := BC_Symm (BC_DatatypeL) *)
  | BC_Symm : forall x y,
       Bindings_NonRec_Commute x y ->
       Bindings_NonRec_Commute y x

  | BC_Datatypes: forall ty ty' args args' matchf matchf' cs cs',
       Bindings_NonRec_Commute
         (DatatypeBind (Datatype ty args matchf cs))
         (DatatypeBind (Datatype ty' args' matchf' cs'))
  .

(* Given two non-recursive term-binding groups bs and cs, where cs is a reordering of bs

    - if cs = (c :: _), c must have a related binding b in bs, that is:

        bs = bs_pre ++ [b] ++ bs_post

      since b was moved to the top of the binding group, that is only correct when:
        + b does not depend on any binding in bs_pre
        + b does not shadow any binding in bs_pre (moving it to the top
      (it commutes with all bindings in bs_pre)

    - if cs = [] then bs = nil
*)

(* Two non-recursive bindings may be reordered if:
   - the latter does not depend on the former
   - the latter does not bind (shadow) a free variable in the former
   - neither are a "let-effectful" (i.e. they strictly bind a non-value expression, which may have
     side effects such as error)
*)


(* Reorder bindings within a non-recursive binding group*)
Inductive LetReorder : Term -> Term -> Type :=
  | LR_Let  : forall t t' bs bs' bs'', LetReorder t t' ->
                 ZipWith (BindingBy LetReorder) bs bs' ->
                 SwapsIn Bindings_NonRec_Commute bs' bs'' ->
                 LetReorder
                   (Let NonRec bs   t )
                   (Let NonRec bs'' t')

  | LR_Cong : forall t t', Cong LetReorder t t' -> LetReorder t t'.
(*
with LetReorder_Binding : Binding -> Binding -> Type :=
  | LR_TermBind  : forall t t' s v,
     LetReorder t t' -> LetReorder_Binding (TermBind s v t) (TermBind s v t')
  | LR_OtherBind : forall b,
     LetReorder_Binding b b.
     *)


Polymorphic Inductive FloatLet : Term -> Term -> Type := .
(* TODO: Allow lets to float up to nearest enclosing binder *)
