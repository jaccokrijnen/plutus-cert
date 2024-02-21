Require Import
  Lists.List
  Strings.String
.
From PlutusCert Require Import
  Util
  PlutusIR
  PlutusIR.Analysis.Equality
  DeadCode2
  Compat
  Purity
  Size
  Analysis.BoundVars
.

Import NamedTerm.
Import ListNotations.

Require Import
  Arith.

Section Bindings.

  Context (dec_Term : Term -> Term -> bool).

  Definition dec_Binding (b b' : Binding) : bool := match b, b' with
    | TermBind s vd t, TermBind s' vd' t' => Strictness_eqb s s' && VDecl_eqb vd vd' && dec_Term t t'
    | b, b' => Binding_eqb b b'
    end.

  Definition unused_in (b : Binding) (t' : Term) : bool :=
    forallb (fun x => negb (existsb (String.eqb x) (fv t'))) (bvb b) &&
    forallb (fun x => negb (existsb (String.eqb x) (ftv t'))) (btvb b)
  .

  (* t' is the post-term let body *)
  Fixpoint dec_Bindings_NonRec (bs bs' : list Binding) (t' : Term) : bool :=
    match bs, bs' with
    | b :: bs, b' :: bs' =>
        if dec_Binding b b'
        then dec_Bindings_NonRec bs bs' t'
        else
          dec_pure_binding [] b &&
          unused_in b (Let NonRec bs' t') &&
          dec_Bindings_NonRec bs (b' :: bs') t'
    | [], [] => true
    | b :: bs, [] =>
          dec_pure_binding [] b &&
          unused_in b t' &&
          dec_Bindings_NonRec bs [] t'
    | [], _ => (* Left-over bindings in post-term, impossible *)
        false
    end.

End Bindings.

Fixpoint dec_Term (t t' : Term) {struct t} :=
  match t, t' with
  | Let NonRec bs t, Let NonRec bs' t' =>
      if dec_Bindings_NonRec dec_Term bs bs' t'
      then dec_Term t t'
      else false
  | _, _ => dec_compat dec_Term t t'
  end.
