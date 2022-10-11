Simpler translation relations
---
Some relations can be split to be conceptually simpler, e.g.

    dead_code := dead_syn t t' ∧ well_scoped t' ∧ unique_binders t`

the trade-off for the simplicity is two-fold:

  - we now require unique_binders t, which is a stronger assumption
  (but valid in the case of the plutus implementation).

  - In the proof of semantic preservation we need to prove a lemma that would be
  for free in the original translation relation

This did not apply in the α-renaming transformation, where we need to check that
new names of (type) binders do not capture free (type) variables. We could do
something like

    rename_syn ∧ no_shadowing t

but I don't think `no_shadowing` (or `unique_binders`) actually holds: we want this relation
to be as general as possible, because it is used by plutus to rename _to_ unique binders.


Boiler-plate definitions
---

Many inductive translation relations follow a common pattern:

  - They maintain some environment Γ to track information about all bound
  variables
    - Each binder extends Γ for their scope (with special care for scoping in let-recs [1])
  - There are only a few interesting rules which transform the term
  - All other AST constructs are trivial boiler plate (fold-like)

the approach with `Cong` solves simple cases, but breaks down when there are
additional indexes like an environment Γ that needs to be extended at every
binding. Cong would not extend the environment for any binding structures.

Consider ornaments, folds.

[1] each binder individually collects its binder info in a separate index,
  which goes "up", all of these are then combined and pushed "down" as parameter
  to all bindings.


Passes that are re-implemented
---

The scott-encoding is implemented as a function, since it is a very specific transformation
that has no obvious generalisation where relations are useful. So we define

    Definition encode : Term -> Term

which does the same thing the compiler does, but perhaps we only generate α-equivalent code,
then we can define the relation as:

    Definition scott_enc t t' := rename [] [] (encode t) t'

i.e. our encoded term should be α-equivalent with the compiler's term

An additional benefit of re-implementing the pass, is that the search procedure is (mostly, see above)
for free, by calling the function.


Composite passes
---

Similar to the inlining pass, which is a composite of multiple smaller passes,
the ThunkRecursions pass may change the order of bindings in a let-rec (in
addition to thunking recursive bindings). Consider the thunk_rec relation, which only
relates thunked bindings. This relation can only relate post-terms which are equivalent
up to sorting of let-bindings. The complete pass can be defined as a composition:

    thunk_rec_pass t t' := ∃s, thunk_rec t s ∧ let_reorder s t'

but how do we construct the AST `s`, which is not dumped by the compiler? Instead of
outputting extra info to construct s, we can compute a normal form where
all bindings in a let-rec are sorted (e.g. based on identifier name):

    sort_let_recs : Term -> Term
    let_equiv : ∀t, sort_let_recs t ≡-ctx t

and then we could define the pass as

    thunk_rec_pass t t' := thunk_rec (sort_let_recs t) (sort_let_rects t')

similarly, in the case of equivalent-up-to-α-renaming, we could do:

    rename : Term -> Term
    let_equiv : ∀t, rename t ≡-ctx t


Assuming global uniqueness on the pre-term
---

This makes some definitions conceptually simpler (e.g. `dead_code`, see above). Additionally,
some Γ environments in translation relations can become simpler.
For example, in the case of `inline`, we can choose this environment representation:

    Definition binder_info := LetBound Term | LambdaBound.
    Definition ctx := list (string * binder_info).

where we keep track of all bound variables, and shadowing is allowed. However, if we know
uniqueness of binders, we can simply pick:

    Definition ctx := list (string * Term).

and only extend the environment at let bindings. In both cases, lookup would be

    | inline_var : forall x t Γ,
        Lookup (x, t) Γ -> inline Γ (Var x) t

This approach wasn't ideal for `thunk_recursions`, where we need a context for
tracking strict recursive let-bindings. The problem is that we _also_ need an
environment with strictness information of all binders (`list (string * Strictness)`)
to determine if certain terms are pure. These environments could be combined
in a single one, which then requires tracking all variables in scope. That was probably
worth the trade-off, since it doesn't require the unique pre-condition anymore.
