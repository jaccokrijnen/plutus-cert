From PlutusCert Require Import Language.PlutusIR.

From Coq Require Import Strings.String.

Open Scope string_scope.
Open Scope context_scope.

Definition pir_0_original_shadowfix     := Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("ByteString") (Unique (0)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (11)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (12))) (cons (Constructor (VarDecl (Name ("True") (Unique (13))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (0)) (cons (Constructor (VarDecl (Name ("False") (Unique (14))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (0)) (nil))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("verifySignature") (Unique (57))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11))))))))) (LamAbs (Name ("arg") (Unique (53))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (54))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (55))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (56))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (56))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Apply (Builtin (VerifySignature)) (Var (Name ("arg") (Unique (53))))) (Var (Name ("arg") (Unique (54))))) (Var (Name ("arg") (Unique (55)))))))))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("String") (Unique (2)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniString))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (60)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (61))) (cons (Constructor (VarDecl (Name ("Unit") (Unique (62))) (Ty_Var (TyName (Name ("Unit") (Unique (60)))))) (0)) (nil)))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("trace") (Unique (70))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))))) (LamAbs (Name ("arg") (Unique (68))) (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Apply (LamAbs (Name ("b") (Unique (69))) (Ty_Builtin (Some (TypeIn (DefaultUniUnit)))) (Var (Name ("Unit") (Unique (62))))) (Apply (Builtin (Trace)) (Var (Name ("arg") (Unique (68)))))))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Integer") (Unique (1)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("takeByteString") (Unique (5))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (TakeByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("subtractInteger") (Unique (27))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (SubtractInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha3_") (Unique (8))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))))) (Builtin (SHA3))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha2_") (Unique (7))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))))) (Builtin (SHA2))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("remainderInteger") (Unique (32))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (RemainderInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("quotientInteger") (Unique (31))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (QuotientInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("multiplyInteger") (Unique (28))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (MultiplyInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("modInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (ModInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanInteger") (Unique (44))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (41))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (42))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (43))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (43))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (LessThanInteger)) (Var (Name ("arg") (Unique (41))))) (Var (Name ("arg") (Unique (42))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (48))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (45))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (46))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (47))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (47))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (45))))) (Var (Name ("arg") (Unique (46))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanByteString") (Unique (20))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (17))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (18))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (19))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (19))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (LtByteString)) (Var (Name ("arg") (Unique (17))))) (Var (Name ("arg") (Unique (18))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanInteger") (Unique (36))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (34))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (35))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (35))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (GreaterThanInteger)) (Var (Name ("arg") (Unique (33))))) (Var (Name ("arg") (Unique (34))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanEqInteger") (Unique (40))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (37))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (38))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (39))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (39))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (GreaterThanEqInteger)) (Var (Name ("arg") (Unique (37))))) (Var (Name ("arg") (Unique (38))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanByteString") (Unique (24))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (21))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (22))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (23))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (23))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (GtByteString)) (Var (Name ("arg") (Unique (21))))) (Var (Name ("arg") (Unique (22))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("error") (Unique (64))) (Ty_Forall (TyName (Name ("a") (Unique (63)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Ty_Var (TyName (Name ("a") (Unique (63)))))))) (TyAbs (TyName (Name ("e") (Unique (58)))) (Kind_Base) (LamAbs (Name ("thunk") (Unique (59))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Error (Ty_Var (TyName (Name ("e") (Unique (58))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsInteger") (Unique (52))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (49))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (50))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (51))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (51))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (EqInteger)) (Var (Name ("arg") (Unique (49))))) (Var (Name ("arg") (Unique (50))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsByteString") (Unique (16))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (9))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (10))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (15))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (15))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (EqByteString)) (Var (Name ("arg") (Unique (9))))) (Var (Name ("arg") (Unique (10))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyString") (Unique (66))) (Ty_Builtin (Some (TypeIn (DefaultUniString))))) (Constant (Some (ValueOf (DefaultUniString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyByteString") (Unique (25))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))) (Constant (Some (ValueOf (DefaultUniByteString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("dropByteString") (Unique (6))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (DropByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("divideInteger") (Unique (29))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (DivideInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("concatenate") (Unique (4))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (Concatenate))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Char") (Unique (3)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniChar))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("charToString") (Unique (67))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniChar)))) (Ty_Builtin (Some (TypeIn (DefaultUniString)))))) (Builtin (CharToString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("appendString") (Unique (65))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Builtin (Some (TypeIn (DefaultUniString))))))) (Builtin (Append))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("addInteger") (Unique (26))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (AddInteger))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (72))) (cons (Constructor (VarDecl (Name ("Fixed") (Unique (73))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))))) (1)) (cons (Constructor (VarDecl (Name ("Never") (Unique (74))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (0)) (nil))))) (nil)) (LamAbs (Name ("ds1") (Unique (75))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("ds2") (Unique (76))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("keep") (Unique (77))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("False") (Unique (14))))) (nil)) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("wild") (Unique (78))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (Var (Name ("ds1") (Unique (75))))) (nil)) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (72)))) (Var (Name ("ds1") (Unique (75))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Ty_Var (TyName (Name ("Bool") (Unique (11))))))) (LamAbs (Name ("n") (Unique (79))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (80))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (48)))) (Var (Name ("n") (Unique (79))))) (Var (Name ("ds2") (Unique (76)))))))) (LamAbs (Name ("thunk") (Unique (81))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Var (Name ("keep") (Unique (77)))))) (Var (Name ("Unit") (Unique (62)))))))))))))))))))))))))))))))))))))))))).

Definition endDateTy := dataTy (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (72))) (cons (Constructor (VarDecl (Name ("Fixed") (Unique (73))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))))) (1)) (cons (Constructor (VarDecl (Name ("Never") (Unique (74))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (0)) (nil)))).
Definition boolTy := dataTy ((Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (11)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (12))) (cons (Constructor (VarDecl (Name ("True") (Unique (13))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (0)) (cons (Constructor (VarDecl (Name ("False") (Unique (14))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (0)) (nil))))).

Axiom cheat: forall P, P.
(* TODO: Should the context be non-empty? *)
Example pir_0_original_shadowfix__typable :
  (("Bool", Kind_Base) :K: ("EndDate", Kind_Base) :K: Nil) |-+ pir_0_original_shadowfix : (Ty_Fun (Ty_Var "EndDate") (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniInteger))) (Ty_Var "Bool"))).
Proof.
  eapply T_Let. {
    auto.
  }{
    intros. simpl in H. destruct H.
    - subst.
      eauto.
    - inversion H. 
  }
  simpl. eapply T_Let. {
    auto.
  }{
    intros. simpl in H. destruct H.
    - subst.
      eapply W_Data. eauto. intros. inversion H. subst.
      + simpl. apply W_Con. intros. inversion H0.
      + inversion H0.
        * subst. simpl. apply W_Con. intros. inversion H1.
        * inversion H1.
    - inversion H. 
  }
  simpl. eapply T_Let. {
    auto.
  }{
    simpl. intros.
    inversion H. {
      subst. apply W_Term. {
        eauto.
      }
      constructor; eauto.
      constructor; eauto.
      constructor; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. {
        constructor; eauto.
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11)))); eauto.
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11)))); eauto.
        apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto.
        replace (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Var (TyName (Name "Bool" (Unique 11))))))) with (substituteT "a" (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Var (TyName (Name "a" (Unique 0)))))))) by reflexivity.
        apply T_TyInst with Kind_Base; eauto.
      }
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniByteString))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniByteString))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniByteString))); eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    } 
    inversion H0. 
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. { 
      subst. eapply W_Data; eauto.
      intros. inversion H0. {
        subst. simpl. apply W_Con. intros.
        inversion H1.
      }
      inversion H1.
    }
    inversion H0. 
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eapply W_Term; eauto.
      apply T_LamAbs; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniUnit))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniString))); eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst.
      apply W_Term; eauto.
      apply T_LamAbs; eauto.
      apply T_LamAbs; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. { 
        apply T_LamAbs; eauto.
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11))) ); eauto. 
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11)))); eauto. 
        apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. 
        replace (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Var (TyName (Name "Bool" (Unique 11))))))) with (substituteT "a" (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Var (TyName (Name "a" (Unique 0)))))))) by reflexivity.
        apply T_TyInst with Kind_Base; eauto.
      }
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto. 
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst.
      apply W_Term; eauto.
      apply T_LamAbs; eauto.
      apply T_LamAbs; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. { 
        apply T_LamAbs; eauto.
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11))) ); eauto. 
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11)))); eauto. 
        apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. 
        replace (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Var (TyName (Name "Bool" (Unique 11))))))) with (substituteT "a" (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Var (TyName (Name "a" (Unique 0)))))))) by reflexivity.
        apply T_TyInst with Kind_Base; eauto.
      }
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto. 
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst.
      apply W_Term; eauto.
      apply T_LamAbs; eauto.
      apply T_LamAbs; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. { 
        apply T_LamAbs; eauto.
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11))) ); eauto. 
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11)))); eauto. 
        apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. 
        replace (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Var (TyName (Name "Bool" (Unique 11))))))) with (substituteT "a" (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Var (TyName (Name "a" (Unique 0)))))))) by reflexivity.
        apply T_TyInst with Kind_Base; eauto.
      }
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniByteString))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniByteString))); eauto. 
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst.
      apply W_Term; eauto.
      apply T_LamAbs; eauto.
      apply T_LamAbs; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. { 
        apply T_LamAbs; eauto.
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11))) ); eauto. 
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11)))); eauto. 
        apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. 
        replace (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Var (TyName (Name "Bool" (Unique 11))))))) with (substituteT "a" (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Var (TyName (Name "a" (Unique 0)))))))) by reflexivity.
        apply T_TyInst with Kind_Base; eauto.
      }
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto. 
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst.
      apply W_Term; eauto.
      apply T_LamAbs; eauto.
      apply T_LamAbs; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. { 
        apply T_LamAbs; eauto.
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11))) ); eauto. 
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11)))); eauto. 
        apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. 
        replace (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Var (TyName (Name "Bool" (Unique 11))))))) with (substituteT "a" (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Var (TyName (Name "a" (Unique 0)))))))) by reflexivity.
        apply T_TyInst with Kind_Base; eauto.
      }
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto. 
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst.
      apply W_Term; eauto.
      apply T_LamAbs; eauto.
      apply T_LamAbs; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. { 
        apply T_LamAbs; eauto.
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11))) ); eauto. 
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11)))); eauto. 
        apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. 
        replace (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Var (TyName (Name "Bool" (Unique 11))))))) with (substituteT "a" (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 0)))) (Ty_Var (TyName (Name "a" (Unique 0)))))))) by reflexivity.
        apply T_TyInst with Kind_Base; eauto.
      }
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniByteString))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniByteString))); eauto. 
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst.
      apply W_Term; eauto.
      apply T_Eq with (Ty_Forall (TyName (Name "e" (Unique 58))) Kind_Base (Ty_Fun (Ty_Var (TyName (Name "Unit" (Unique 60)))) (Ty_Var (TyName (Name "e" (Unique 58)))))). {
        apply T_TyAbs.
        apply T_LamAbs; eauto.
      }
      apply cheat. (* TODO: alpha-equivalence *)
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst.
      apply W_Term; eauto.
      apply T_LamAbs; eauto.
      apply T_LamAbs; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. { 
        apply T_LamAbs; eauto.
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11))) ); eauto. 
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11)))); eauto. 
        apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. 
        replace (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Var (TyName (Name "Bool" (Unique 11))))))) with (substituteT "a" (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 11)))) (Ty_Var (TyName (Name "a" (Unique 11)))))))) by reflexivity.
        apply T_TyInst with Kind_Base; eauto.
      }
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto. 
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst.
      apply W_Term; eauto.
      apply T_LamAbs; eauto.
      apply T_LamAbs; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. { 
        apply T_LamAbs; eauto.
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11))) ); eauto. 
        apply T_Apply with (Ty_Var (TyName (Name "Bool" (Unique 11)))); eauto. 
        apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniBool))); eauto. 
        replace (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Var (TyName (Name "Bool" (Unique 11))))))) with (substituteT "a" (Ty_Var (TyName (Name "Bool" (Unique 11)))) (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 11)))) (Ty_Fun (Ty_Var (TyName (Name "a" (Unique 11)))) (Ty_Var (TyName (Name "a" (Unique 11)))))))) by reflexivity.
        apply T_TyInst with Kind_Base; eauto.
      }
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniByteString))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniByteString))); eauto. 
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.
  }{
    intros. inversion H. {
      subst. 
      eapply W_Data; eauto. 
      simpl. intros.
      inversion H0. {
        subst. apply W_Con.
        intros. inversion H1. {
          subst. eauto.
        }
        inversion H2.
      }
      inversion H1. {
        subst. apply W_Con.
        intros. inversion H2.
      }
      inversion H2.
    }
    inversion H0.
  }
  apply T_LamAbs; eauto.
  apply T_LamAbs; auto.
  simpl. apply T_Let. {
    auto.    
  }{
    intros. inversion H. {
      subst. eauto.
    }
    inversion H0.
  }
  simpl. apply T_Let. {
    auto.    
  }{
    intros. inversion H. {
      subst. eauto. 
    }
    inversion H0.
  }
  simpl.
  apply T_Apply with (Ty_Var "Unit"). {
    apply T_Apply with (Ty_Fun (Ty_Var (TyName (Name "Unit" (Unique 60)))) (Ty_Var (TyName (Name "Bool" (Unique 11))))). {
      apply T_Apply with (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniInteger))) (Ty_Fun (Ty_Var (TyName (Name "Unit" (Unique 60)))) (Ty_Var (TyName (Name "Bool" (Unique 11)))))). {
        replace (Ty_Fun
                  (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniInteger)))
                    (Ty_Fun (Ty_Var (TyName (Name "Unit" (Unique 60))))
                        (Ty_Var (TyName (Name "Bool" (Unique 11))))))
                  (Ty_Fun
                    (Ty_Fun (Ty_Var (TyName (Name "Unit" (Unique 60))))
                        (Ty_Var (TyName (Name "Bool" (Unique 11)))))
                    (Ty_Fun (Ty_Var "Unit") (Ty_Var "Bool"))))
          with (substituteT "R" (Ty_Fun (Ty_Var (TyName (Name "Unit" (Unique 60)))) (Ty_Var (TyName (Name "Bool" (Unique 11)))))
                (Ty_Fun
                  (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniInteger)))
                    (Ty_Var "R"))
                  (Ty_Fun
                    (Ty_Var "R")
                    (Ty_Var "R")))) by reflexivity.
        eapply T_TyInst; eauto.
        apply T_Apply with (Ty_Var "EndDate"); eauto.
      }
      apply T_LamAbs; eauto.
      apply T_LamAbs; eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto.
      apply T_Apply with (Ty_Builtin (Some (TypeIn DefaultUniInteger))); eauto.
    }
    apply T_LamAbs; eauto.
  }
  eauto.
Qed.