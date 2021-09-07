Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.


From PlutusCert Require Import
  Language.PlutusIR
  Language.PlutusIR.Transform.Compose
  Language.PlutusIR.Transform.Rename
  Language.PlutusIR.Optimizer.DeadBindings
  Language.PlutusIR.Transform.Inline
  Language.PlutusIR.Transform.Equal
  Language.PlutusIR.Transform.ThunkRecursions
  Language.PlutusIR.Transform.FloatLet
  Language.PlutusIR.Transform.NonStrict
  Language.PlutusIR.Transform.LetNonRec
  (* Language.PlutusIR.Transform.LetNonStrict*)
  Language.PlutusIR.Transform.LetRec
  Language.PlutusIR.Transform.LetTypes
  .
Import NamedTerm.


Definition simplifier : list (Term -> Term -> Type) :=
  [ DBE_Term
  ; Inline []
  ].


(* The sequence of transformations from PIR to Plutus Core*)
Definition pirToCore: list (Term -> Term -> Type) :=
  [ Rename_string
  ; eqT (* typechecking *)
  ]

  ++ simplifier ++

  [ ThunkRecursions
  ; FloatLet
  (* ; LetNonStrict *)
  ; LetTypes
  ; LetTermsRec
  ]

  ++ simplifier ++

  [ CNR_Term
  ; eqT (* "lowers" term, changes AST type *)
  ]
.

(*
pir_0_6
     : compose
         [eq;
          eq;
          DBE_Term;

          compose [Inline []; DBE_Term];

          eq;
          compose [LetMerge; LetReorder];
          eq;
          Scott;
          eq;

          DBE_Term;

          eq;
          CNR_Term]

          pir_2_typechecked
          plc_5_compileNonRecTerms
*)
