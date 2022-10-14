Translation relations boiler-plate
---

Consider a very general relation

    Context
      (inh syn : Type)
      (premise_Apply :
          (inh -> syn -> Term -> Term -> Prop) ->       (* relation for recursive positions *)
          Term -> Term ->                               (* subterms of Apply *)
          inh -> syn ->
          Term ->                                       (* The post-term *)
          Prop
      )
      ...

    r_Term : inh -> syn -> Term -> Term -> Prop :=

      | r_Apply : forall down up s t,
          premise_Apply rel_Term down up s t post ->
          r_Term down up (Apply s t) post

      | ...

which is defined for the whole AST. We can then have default implementations
for `post_Apply` and only add definitions when they are interesting.

In the usual form of translation relations, we sometimes have 
multiple rules for a single "pre" constructor, e.g. in `inline`

    | inl_Var_1 : forall v t t',
        Lookup v (bound_term t) Γ ->
        inline Γ t t' ->
        inline Γ (Var v) t'

    | inl_Var_2 : forall v,
        inline Γ (Var v) (Var v)

This could then become something like:

    Inductive premise_Var r_Term Γ unit v post : Prop :=

      | Var_1 : forall t t',
          Lookup v (bound_term t) Γ ->
          r_term t t' ->
          premise_Var Γ tt v t'

      | Var_2 :
          premise_Var Γ tt v (Var v)

Or

    Definition premise_Var r_Term Γ unit v post : Post :=
      (exists t t', Lookup v (bound_term t) /\ r_term t t' /\ post = t') 
      \/
      (post = Var v)

Perhaps the latter is easier to work with for producing decision procedures

In some cases, there should be a preference for one alternative over another, e.g.
in the inline relation, there is a case (TyInst (TyAbs ...) T) which should be treated
differently from any Other (TyInst (Other...) T). If we could use pattern matching
(functional), perhaps this would be easier? Alternatively

    | R_TyInst_Beta :
        R (TyInst (TyAbs ...) T) ...
    | R_TyInst_Other :
        ~(exists ..., t = TyAbs) ->
        R (TyInst t T) ...


It's probably best to test this out on a smaller AST, no inh/syn etc. (toy compiler?)
