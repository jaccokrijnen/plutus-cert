Simpler translation relations
---
Some relations can be split to be conceptually simpler, e.g. dead_code
  - dead_syn t t' ∧ well_scoped t' ∧ unique_binders t
the trade-off for the simplicity is two-fold:
  - we now require unique_binders t, which is a stronger assumption 
    (but valid in the case of the plutus implementation).
  - In the proof of semantic preservation we need to prove a lemma that would be
    for free in the original translation relation

This did not apply in the rename transformation, where we need to check that
new names of (type) binders do not capture free (type) variables. We could do
something like

  rename_syn ∧ no_shadowing t

but I don't think no_shadowing (or unique_binders) actually holds: we want this relation
to be as general as possible, because it is used by plutus to rename _to_ unique binders.


Boiler-plate definitions
---

Many inductive translation relations follow a common pattern:
  - They maintain some environment Γ to track information about all bound
    variables
    + each binder extends Γ for their scope (with special care for scoping in let-recs [*])
  - There are only a few interesting rules which transform the term
  - All other AST constructs are trivial boiler plate (fold-like)

Consider ornaments, folds.

[*] each binder individually collects its binder info in a separate index, which
    goes "up", all of these are then combined and pushed "down" as parameter to all
    bindings.


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

Similar to the inline pass, the ThunkRecursions pass may change the order of
bindings in a let-rec (in addition to thunking recursive bindings). Consider
the thunk_rec relation, only does the thunking. Then the complete pass can
be defined as a composition:

  thunk_rec_pass t t' := ∃s, thunk_rec t s ∧ let_reorder s t'

but how do we construct s, which is not dumped by the compiler? Instead of
outputting extra info to construct s, an alternative is to consider normal
forms. In this case by sorting all bindings in a let-rec.

  sort_let_recs : Term -> Term
  let_equiv : ∀t, sort_let_recs t ≡-ctx t

and then define

  thunk_rec_pass := thunk_rec (sort_let_recs t) (sort_let_rects t')

