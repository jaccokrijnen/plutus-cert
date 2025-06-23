## Accompanying Codebase  
**Master Thesis**: *A terminating type checker for the Plutus smart contracting language in Rocq*  
**Author**: Richard A. Koetschruyter  

---

### Directory Structure & Contributions

Apart from the files below, I made changes to existing files, such as those in the compatibility lemmas when changing the typing rules.

Many trivial facts unproved.
Some untrivial facts unproved: Admits explain why.

#### `Examples/` - Example PIR programs
- `MaybeFun` - Compiler dumps of the MaybeFun program
- `TypeCheckTest` - Type check term with type computation


#### `Language/STLC/` — Annotated Simply-Typed Lambda Calculus (STLC)
- `Kinding`
  Kinding of annotated STLC: same rules as PIR
- `STLC`
  Annotated STLC definition and capture-avoiding substitutions

##### `/Alpha/` — Alpha Equivalence and Related Operations
- `alpha_freshness`  
  Free and bound variable preservation under α-equivalence
- `alpha_kinding`  
  α-equivalence preserves kinding (typing of types)
- `alpha_rename`  
  Characterization of renaming of α-equivalence
- `alpha_sub`  
  Core substitution rules and their interaction with α-equivalence
- `alpha_subs`  
  α-equivalent multi-substitutions
- `alpha_vacuous`
  α-equivalence and adding vacuous (unnecessary) renamings to contexts. In its own file because it requires construction proofs in `Scoping/`
- `alpha`
  α-equivalence, equivalence relation, lookup behaviour, basic properties. 

##### /`Dynamics/` - Strong normalization proof
- `IdSubst`
  Identity substitutions and relevant properties for strong normalization
- `psubs`
  Parallel multi-substitutions
- `SN_STLC_GU`
  Strong normalization proof using globally uniquifying reductions
- `SN_STLC_nd`
  Strong normalization proof using non-deterministic reductions
- `step_gu`
  Globally uniquifying reductions
- `step_naive`
  Naive reductions

##### `/Scoping/` - Scoping properties and constructing representatives
- `construct_GU_R`
  Constructing representatives with α-equivalence requirements with non-empty renaming context: renaming free variables
- `construct_GU`
  Construction procedures for constructing globally unique representatives with different properties.
- `GU_NC`
  Global uniqueness and No capture judgments and their properties
- `variables`
  Trivial properties about free and bound type variables

#### `Language/PlutusIR/Semantics/Static/` - Static semantics of PIR

##### `/Kinding/` Improved kinding relation and checker

##### `/Normalisation/` - Normalizer and strong normalization for PIR
- `BigStep`
  Big step normalization relation `normalise`
- `Normaliser_sound_complete`
  Sound and completeness proof of the normalizer
- `Normalizer`
  The terminating normalizer
- `Preservation`
  Preservation of the type-language
- `Progress`
  Progress of the type-language
- `SmallStep`
  Small step reduction relation of PIR's type language
- `SN_PIR`
  Strong normalization proof by embedding into ASTLC

##### `/Typing/` - Improved typing relation and checker
- `Binders_wellkinded` 
  All type variables bound in let terms are well-kinded
- `drop_context` 
  Properties of removing variables from context (in TyAbs and Let rules)
- `Typechecker`
  Type checking procedure
- `Typing_sound_complete`
  Sound and completeness of the type checking procedure
- `Typing`
  Improved typing relation

#### `Language/PlutusIR/Semantics/TypeSafety/` - Type safety of PIR

- `Preservation` Formalized preservation up to errors
- `BaseKindedness` The type of a well-typed term is of kind *

##### `/SubstitutionPreservesTyping/` - Preservation of types with different substitutions
- `AnnotationSubstitution` Conjectured formulation of annotation substitution preservation.
- `SubstituteTCA` Preservation of capture-avoiding type substitutions
- `TermSubstitution` Preservation of substitution on the term level
- `TypeSubstitution` Preservation of naive type substitutions


#### `Util/` - Utility files, added many properties on lists and lookup