From PlutusCert Require Import Language.PlutusIR.
Import NamedTerm.
From PlutusCert Require Import Language.PlutusIR.Semantics.Static.

Open Scope string_scope.

Definition pir_0_original_shadowfix     := Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("ByteString") (Unique (0)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (11)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (12))) (cons (Constructor (VarDecl (Name ("True") (Unique (13))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (0)) (cons (Constructor (VarDecl (Name ("False") (Unique (14))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (0)) (nil))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("verifySignature") (Unique (57))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11))))))))) (LamAbs (Name ("arg") (Unique (53))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (54))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (55))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (56))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (56))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Apply (Builtin (VerifySignature)) (Var (Name ("arg") (Unique (53))))) (Var (Name ("arg") (Unique (54))))) (Var (Name ("arg") (Unique (55)))))))))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("String") (Unique (2)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniString))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (60)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (61))) (cons (Constructor (VarDecl (Name ("Unit") (Unique (62))) (Ty_Var (TyName (Name ("Unit") (Unique (60)))))) (0)) (nil)))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("trace") (Unique (70))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))))) (LamAbs (Name ("arg") (Unique (68))) (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Apply (LamAbs (Name ("b") (Unique (69))) (Ty_Builtin (Some (TypeIn (DefaultUniUnit)))) (Var (Name ("Unit") (Unique (62))))) (Apply (Builtin (Trace)) (Var (Name ("arg") (Unique (68)))))))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Integer") (Unique (1)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("takeByteString") (Unique (5))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (TakeByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("subtractInteger") (Unique (27))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (SubtractInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha3_") (Unique (8))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))))) (Builtin (SHA3))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha2_") (Unique (7))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))))) (Builtin (SHA2))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("remainderInteger") (Unique (32))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (RemainderInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("quotientInteger") (Unique (31))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (QuotientInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("multiplyInteger") (Unique (28))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (MultiplyInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("modInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (ModInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanInteger") (Unique (44))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (41))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (42))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (43))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (43))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (LessThanInteger)) (Var (Name ("arg") (Unique (41))))) (Var (Name ("arg") (Unique (42))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (48))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (45))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (46))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (47))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (47))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (45))))) (Var (Name ("arg") (Unique (46))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanByteString") (Unique (20))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (17))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (18))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (19))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (19))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (LtByteString)) (Var (Name ("arg") (Unique (17))))) (Var (Name ("arg") (Unique (18))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanInteger") (Unique (36))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (34))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (35))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (35))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (GreaterThanInteger)) (Var (Name ("arg") (Unique (33))))) (Var (Name ("arg") (Unique (34))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanEqInteger") (Unique (40))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (37))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (38))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (39))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (39))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (GreaterThanEqInteger)) (Var (Name ("arg") (Unique (37))))) (Var (Name ("arg") (Unique (38))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanByteString") (Unique (24))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (21))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (22))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (23))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (23))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (GtByteString)) (Var (Name ("arg") (Unique (21))))) (Var (Name ("arg") (Unique (22))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("error") (Unique (64))) (Ty_Forall (TyName (Name ("a") (Unique (63)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Ty_Var (TyName (Name ("a") (Unique (63)))))))) (TyAbs (TyName (Name ("e") (Unique (58)))) (Kind_Base) (LamAbs (Name ("thunk") (Unique (59))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Error (Ty_Var (TyName (Name ("e") (Unique (58))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsInteger") (Unique (52))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (49))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (50))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (51))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (51))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (EqInteger)) (Var (Name ("arg") (Unique (49))))) (Var (Name ("arg") (Unique (50))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsByteString") (Unique (16))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (9))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (10))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (15))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (15))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (EqByteString)) (Var (Name ("arg") (Unique (9))))) (Var (Name ("arg") (Unique (10))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyString") (Unique (66))) (Ty_Builtin (Some (TypeIn (DefaultUniString))))) (Constant (Some (ValueOf (DefaultUniString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyByteString") (Unique (25))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))) (Constant (Some (ValueOf (DefaultUniByteString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("dropByteString") (Unique (6))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (DropByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("divideInteger") (Unique (29))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (DivideInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("concatenate") (Unique (4))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (Concatenate))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Char") (Unique (3)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniChar))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("charToString") (Unique (67))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniChar)))) (Ty_Builtin (Some (TypeIn (DefaultUniString)))))) (Builtin (CharToString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("appendString") (Unique (65))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Builtin (Some (TypeIn (DefaultUniString))))))) (Builtin (Append))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("addInteger") (Unique (26))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (AddInteger))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (72))) (cons (Constructor (VarDecl (Name ("Fixed") (Unique (73))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))))) (1)) (cons (Constructor (VarDecl (Name ("Never") (Unique (74))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (0)) (nil))))) (nil)) (LamAbs (Name ("ds1") (Unique (75))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("ds2") (Unique (76))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("keep") (Unique (77))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("False") (Unique (14))))) (nil)) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("wild") (Unique (78))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (Var (Name ("ds1") (Unique (75))))) (nil)) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (72)))) (Var (Name ("ds1") (Unique (75))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Ty_Var (TyName (Name ("Bool") (Unique (11))))))) (LamAbs (Name ("n") (Unique (79))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (80))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (48)))) (Var (Name ("n") (Unique (79))))) (Var (Name ("ds2") (Unique (76)))))))) (LamAbs (Name ("thunk") (Unique (81))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Var (Name ("keep") (Unique (77)))))) (Var (Name ("Unit") (Unique (62)))))))))))))))))))))))))))))))))))))))))).


Ltac solve__map_normalise :=
  match goal with
  | |- map_normalise ?l ?l' =>
      unfold flatten; simpl; try solve [repeat (econstructor; eauto)]
  end.

Ltac solve__splitTy :=
  match goal with
  | |- (?Targs, ?Tr) = splitTy ?T =>
      try solve [simpl; eauto]
  end.

Ltac solve__kindTargs :=
  match goal with
  |- forall U, List.In U ?Us -> ?Delta |-* U : Kind_Base =>
      let U := fresh in
      let H := fresh in
      intros U H; repeat (destruct H; subst; eauto with typing)
  end.

Ltac solve__constructor :=
  match goal with
  | H : List.In ?c nil |- ?P =>
      destruct H
  | H : List.In ?c ?cs |- ?Delta |-ok_c ?c : ?Tr =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [H1 | H2]; subst; (try (econstructor; solve__kindTargs || solve__splitTy ))
  end.

Ltac solve__constructors :=
  match goal with
  | |- forall c : constructor, List.In c ?cs -> ?Delta |-ok_c c : ?Tr =>
      let H := fresh in
      intros c H; simpl; repeat solve__constructor
  end.
  
Ltac solve__kinding :=
  match goal with
  | |- ?Delta |-* ?T : ?K =>
      try solve [repeat (econstructor; eauto with typing)]
  end.

Ltac solve__TVar :=
  match goal with
  | |- ?Delta ,, ?Gamma |-+ (Var ?x) : ?T =>
      unfold update; unfold t_update; simpl; eapply T_Var; try solve [reflexivity || eauto with typing]
  end.

Ltac solve__TBuiltin :=
  match goal with
  | |- ?Delta ,, ?Gamma |-+ (Builtin ?f) : ?T =>
      eapply T_Builtin; unfold lookupBuiltinTy; eauto
  end.

Ltac solve__normalise_substituteTCA :=
  match goal with
  | |- normalise (substituteTCA ?X ?U ?T) ?S =>
      autorewrite with substituteTCA; simpl; econstructor; eauto
  end.

Ltac repeat__econstructor :=
  repeat (econstructor; try (solve__TVar || solve__TBuiltin || solve__normalise_substituteTCA || eauto with typing)).

Ltac solve__TermBind :=
  match goal with
  | |- ?Delta ,, ?Gamma |-ok_b (TermBind ?str ?vd ?t) =>
      eapply W_Term; try solve [eauto with typing || repeat__econstructor]
  end.

Ltac solve__DatatypeBind :=
  match goal with
  | |- ?Delta ,, ?Gamma |-ok_b (DatatypeBind ?dtd) =>
      eapply W_Data; try solve [eauto with typing || solve__constructors || solve__kinding]
  end.

Ltac solve__BindingsNonRec :=
  match goal with
  | |- ?Delta ,, ?Gamma |-oks_nr (?b :: ?bs) =>
      eapply W_ConsB_NonRec; try solve [ eauto with typing || solve__map_normalise || solve__DatatypeBind || solve__TermBind]
  end.
  
Ltac solve__Let :=
  match goal with
  | |- ?Delta ,, ?Gamma |-+ (Let ?rec ?bs ?t) : ?T =>
      eapply T_Let; try solve [eauto with typing || solve__map_normalise || solve__BindingsNonRec ]
  end.

Ltac solve__typing :=
  repeat (simpl; (solve__Let || solve__BindingsNonRec || solve__DatatypeBind || solve__TermBind)).


Example pir_0_original_shadowfix__typable :
  empty ,, empty |-+ pir_0_original_shadowfix : (Ty_Fun (Ty_Var "EndDate") (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniInteger))) (Ty_Var "Bool"))).
Proof with (eauto with typing || (try solve [solve__map_normalise || solve__TVar])).
  unfold pir_0_original_shadowfix.
  unfold Name, TyName. simpl.
  solve__typing. {
    admit.
  }
  repeat__econstructor.
  solve__normalise_substituteTCA.
Admitted.
