From PlutusCert Require Import
  PlutusIR
  Bigstep
  Util
.

Require Import Lists.List.
Require Import Strings.String.
Import ListNotations.
Import PlutusNotations.

Open Scope string.

Definition program : term :=
  Let Rec
    [ DatatypeBind (Datatype
        (TyVarDecl 
          "List"
          (Kind_Arrow Kind_Base Kind_Base)
        )
        [ TyVarDecl "a" Kind_Base ]
        "matchList"
        [ VarDecl "nil" (Ty_App (Ty_Var "List") (Ty_Var "a"))
        ; VarDecl "cons" 
            (Ty_Fun (Ty_Var "a")
              (Ty_Fun (Ty_App (Ty_Var "List") (Ty_Var "a")) (Ty_App (Ty_Var "List") (Ty_Var "a"))))
        ]
      )
    ]
    <{ {Var "cons"} @ bool ⋅ true ⋅ ({Var "nil"} @ bool) }>
    .


Example fact_term_evaluates : exists k v,
  program =[k]=> v.
Proof.
  eexists.
  eexists.
  unfold program.
  eapply E_LetRec_Data; try reflexivity.
  simpl.
  eapply E_Apply.
Abort.
