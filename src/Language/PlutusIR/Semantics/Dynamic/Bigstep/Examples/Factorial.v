Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Definition fact_term (n : Z) : Term :=
  Let 
    Rec
    [ TermBind 
        Strict 
        (VarDecl 
          "fact" 
          (Ty_Fun 
            (Ty_Builtin (Some (TypeIn DefaultUniInteger))) 
            (Ty_Builtin (Some (TypeIn DefaultUniInteger)))
          )
        ) 
        (LamAbs 
          "x" 
          (Ty_Builtin (Some (TypeIn DefaultUniInteger)))
          (Apply
            (Apply
              (Apply
                (TyInst
                  (Builtin IfThenElse)
                  (Ty_Builtin (Some (TypeIn DefaultUniInteger)))  
                )
                (Apply
                  (Apply
                    (Builtin EqInteger)
                    (Var "x")
                  )
                  (Constant (Some (ValueOf DefaultUniInteger 0)))
                )
              )
              (Constant (Some (ValueOf DefaultUniInteger 1)))
            )
            (Apply
              (Apply
                (Builtin MultiplyInteger)
                (Var "x")
              )
              (Apply
                (Var "fact")
                (Apply
                  (Apply
                    (Builtin SubtractInteger)
                    (Var "x")
                  )
                  (Constant (Some (ValueOf DefaultUniInteger 1)))
                )
              )
            )
          )
        )
    ] 
    (Apply
      (Var "fact")
      (Constant (Some (ValueOf DefaultUniInteger n)))  
    ).

Ltac invert_contra := let Hcon := fresh "Hcon" in intros Hcon; inversion Hcon.
Ltac destruct_invert_contra := let Hcon := fresh "Hcon" in intros Hcon; destruct Hcon as [Hcon | Hcon]; try solve [inversion Hcon || destruct Hcon].
Ltac solve_substitute := repeat (econstructor || eauto || invert_contra || destruct_invert_contra).
Ltac solve_value_builtin := repeat econstructor.

(*
Example fact_term_evaluates : exists k,
  fact_term 2 =[k]=> Constant (Some (ValueOf DefaultUniInteger 2)).
Proof with eauto.
  eexists.
  apply E_LetRec.
  eapply E_ConsB_Rec. {
    apply S_LetRec2. {
      invert_contra.
    } {    
      solve_substitute.
    }
  }
  apply E_NilB_Rec.
  eapply E_Apply. {
    eapply E_LetRec.
    eapply E_ConsB_Rec. {
      apply S_LetRec2. {
        invert_contra.
      } {    
        solve_substitute.
      }
    }
    apply E_NilB_Rec.
    apply E_LamAbs.
  } {
    apply E_Constant.
  } {
    apply S_Apply.
    - apply S_Apply.
      + apply S_Apply.
        * apply S_TyInst.
          apply S_Builtin.
        * apply S_Apply.
          -- apply S_Apply.
             ++ apply S_Builtin.
             ++ apply S_Var1.
          -- apply S_Constant.
      + apply S_Constant.
    - apply S_Apply. 
      + apply S_Apply.
        * apply S_Builtin.
        * apply S_Var1.
      + apply S_Apply.
        * apply S_LetRec2.
          -- intros Hcon.
             simpl in Hcon.
             destruct Hcon.
             ++ inversion H.
             ++ destruct H.
          -- apply S_ConsB_Rec.
             ++ apply S_TermBind.
                apply S_LamAbs1.
             ++ apply S_NilB_Rec.
                apply S_LamAbs1.
        * apply S_Apply.
          -- apply S_Apply.
             ++ apply S_Builtin.
             ++ apply S_Var1.
          -- apply S_Constant.
  }
  eapply E_IfFalse. { 
    eapply E_IfThenBranch. {
      eapply E_IfCondition. {
        eapply E_IfTyInst. {
          apply E_Builtin.
        }
      } {
        eapply E_ApplyBuiltin2. {
          eapply E_ApplyBuiltin1. {
            apply E_Builtin.
          } {
            eapply V_Builtin0.
            apply PeanoNat.Nat.lt_0_succ.
          } {
            apply E_Constant.
          } {
            apply V_Builtin1.
            - apply le_n.
            - apply V_Constant.
          }
        } {
          eapply V_Builtin1.
          - apply le_n.
          - apply V_Constant.
        } {
          apply E_Constant.
        } {
          intros Hcon.
          inversion Hcon. subst.
          apply PeanoNat.Nat.lt_irrefl in H2.
          destruct H2.
        } 
        reflexivity.
      }
    }
  } 
  eapply E_ApplyBuiltin2. {
    eapply E_ApplyBuiltin1. {
      apply E_Builtin.
    } {
      eapply V_Builtin0.
      apply PeanoNat.Nat.lt_0_succ.
    } {
      eapply E_Constant.
    } {
      eapply V_Builtin1. {
        apply le_n.
      } {
        eapply V_Constant.
      }
    }
  } {
    eapply V_Builtin1. {
      apply le_n.
    } {
      eapply V_Constant.
    }
  } {
    eapply E_Apply. {
      eapply E_LetRec. {
        eapply E_ConsB_Rec. {
          apply S_LetRec2. {
            invert_contra.
          } {    
            solve_substitute.
          }
        }
        eapply E_NilB_Rec.
        eapply E_LamAbs.
      }
    } {
      eapply E_ApplyBuiltin2. {
        eapply E_ApplyBuiltin1. {
          eapply E_Builtin.
        } {
          eapply V_Builtin0.
          apply PeanoNat.Nat.lt_0_succ.
        } {
          eapply E_Constant.
        } {
          eapply V_Builtin1. {
            eapply le_n.
          } {
            eapply V_Constant.
          }
        }
      } {
        eapply V_Builtin1. {
          eapply le_n.
        } {
          eapply V_Constant.
        }
      } {
        eapply E_Constant.
      } {
        intros Hcon.
        inversion Hcon. subst.
        apply PeanoNat.Nat.lt_irrefl in H2.
        destruct H2.
      } {
        reflexivity.
      }
    } {
      eapply S_Apply. {
        eapply S_Apply. {
          eapply S_Apply. {
            solve_substitute.
          } {
            solve_substitute.
          }
        } {
          solve_substitute.
        }
      } {
        eapply S_Apply. {
          solve_substitute.
        } {
          eapply S_Apply. {
            eapply S_LetRec2. {
              destruct_invert_contra.
            } {
              solve_substitute.
            }
          } {
            solve_substitute.
          }
        }
      }
    } {
      eapply E_IfFalse. {
        eapply E_IfThenBranch. {
          eapply E_IfCondition. {
            eapply E_IfTyInst.
            eapply E_Builtin.
          } {
            eapply E_ApplyBuiltin2. {
              eapply E_ApplyBuiltin1. {
                eapply E_Builtin.
              } {
                eapply V_Builtin0.
                apply PeanoNat.Nat.lt_0_succ.
              } {
                eapply E_Constant.
              } {
                eapply V_Builtin1. {
                  eapply le_n.
                } {
                  eapply V_Constant.
                }
              }
            } {
              eapply V_Builtin1. {
                eapply le_n.
              } {
                eapply V_Constant.
              }
            } {
              eapply E_Constant.
            } {
              invert_contra.
              apply PeanoNat.Nat.lt_irrefl in H2.
              destruct H2.
            } {
              reflexivity.
            }
          }
        }
      } {
        eapply E_ApplyBuiltin2. {
          eapply E_ApplyBuiltin1. {
            eapply E_Builtin.
          } {
            solve_value_builtin.
          } {
            eapply E_Constant.
          } {
            solve_value_builtin.
          }
        } {
          solve_value_builtin.
        } {
          eapply E_Apply. {
            eapply E_LetRec. {
              eapply E_ConsB_Rec. {
                apply S_LetRec2. {
                  invert_contra.
                } {
                  solve_substitute.
                }
              }
              eapply E_NilB_Rec.
              eapply E_LamAbs.
            }
          } {
            eapply E_ApplyBuiltin2. {
              eapply E_ApplyBuiltin1. {
                eapply E_Builtin.
              } {
                solve_value_builtin.
              } {
                eapply E_Constant.
              } {
                solve_value_builtin.
              }
            } {
              solve_value_builtin.
            } {
              eapply E_Constant.
            } {
              invert_contra.
              apply PeanoNat.Nat.lt_irrefl in H2.
              destruct H2.
            } {
              reflexivity.
            }
          } {
            eapply S_Apply. {
              solve_substitute.
            } {
              eapply S_Apply... {
                eapply S_Apply... {
                  eapply S_LetRec2. {
                    destruct_invert_contra.
                  } {
                    solve_substitute.
                  }
                }
              }
            }
          } {
            eapply E_IfTrue. {
              eapply E_IfThenBranch. {
                eapply E_IfCondition. {
                  eapply E_IfTyInst. 
                  eapply E_Builtin.
                } {
                  eapply E_ApplyBuiltin2. {
                    eapply E_ApplyBuiltin1. {
                      eapply E_Builtin.
                    } {
                      solve_substitute.
                    } {
                      eapply E_Constant.
                    } {
                      solve_value_builtin.
                    }
                  } {
                    solve_value_builtin.
                  } {
                    eapply E_Constant.
                  } {
                    invert_contra.
                    apply PeanoNat.Nat.lt_irrefl in H2.
                    destruct H2.
                  } {
                    reflexivity.
                  }
                }
              }
            } {
              apply E_Constant.
            }
          }
        } {
          invert_contra.
          apply PeanoNat.Nat.lt_irrefl in H2.
          destruct H2.
        } {
          reflexivity.
        }
      }
    }
  } {
    invert_contra.
    apply PeanoNat.Nat.lt_irrefl in H2.
    destruct H2.
  } {
    reflexivity.
  }
Qed.*)