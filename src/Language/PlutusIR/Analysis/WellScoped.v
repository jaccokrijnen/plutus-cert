From PlutusCert Require Import
  Util.List
  Language.PlutusIR
  Analysis.BoundVars.
Import NamedTerm.

Require Import
  Strings.String
  Lists.List
.

From QuickChick Require Import QuickChick.


Definition ctx := list string.

Reserved Notation "Δ '|-*' T" (at level 40, T at level 0).
Inductive well_scoped_ty (Δ : ctx) : Ty -> Prop :=
  | WST_Var : forall X,
      NameIn X Δ ->
      Δ |-* (Ty_Var X)
  | WST_Fun : forall T1 T2,
      Δ |-* T1 ->
      Δ |-* T2 ->
      Δ |-* (Ty_Fun T1 T2)
  | WST_IFix  : forall F T,
      Δ |-* T ->
      Δ |-* F ->
      Δ |-* (Ty_IFix F T)
  | WST_Forall : forall X K T,
      (X :: Δ) |-* T ->
      Δ |-* (Ty_Forall X K T)
  | WST_Lam : forall X K1 T,
      (X :: Δ) |-* T ->
      Δ |-* (Ty_Lam X K1 T)
  | WST_App : forall T1 T2,
      Δ |-* T1 ->
      Δ |-* T2 ->
      Δ |-* (Ty_App T1 T2)
  (* TODO: I rewrote this constructor to be able to derive a checker
   *  is this rewrite fine? *)
  | WST_Builtin : forall u (x : typeIn u),
      Δ |-* (Ty_Builtin (@Some' typeIn u x))
where "Δ '|-*' T " := (well_scoped_ty Δ T).

QCDerive DecOpt for (well_scoped_ty Δ T).

Instance well_scoped_ty_DecOpt_sound Δ T : DecOptSoundPos (well_scoped_ty Δ T).
Proof. idtac "Admitted: well_scoped_ty_DecOpt_sound". Admitted. (* derive_sound. Qed. *)

Instance well_scoped_ty_DecOpt_complete Δ T : DecOptCompletePos (well_scoped_ty Δ T).
Proof. idtac "Admitted: well_scoped_ty_DecOpt_complete". Admitted. (* derive_complete. Qed. *)

Instance well_scoped_ty_DecOpt_monotonic Δ T: DecOptSizeMonotonic (well_scoped_ty Δ T).
Proof. idtac "Admitted: well_scoped_ty_DecOpt_monotonic". Admitted. (* derive_mon. Qed. *)




Reserved Notation "Δ ',,' Γ '|-+' t " (at level 101, t at level 0, no associativity).
Reserved Notation "Δ '|-ok_c' c " (at level 101, c at level 0).
Reserved Notation "Δ '|-ok_cs' cs " (at level 101, cs at level 0).

Inductive constructor_well_formed (Δ : ctx) : constructor -> Prop :=
  | W_Con : forall x T ar,
      Δ |-* T ->
      Δ |-ok_c (Constructor (VarDecl x T) ar)
  where 
    "Δ '|-ok_c' c" := (constructor_well_formed Δ c).

QCDerive DecOpt for (constructor_well_formed Δ c).

Instance constructor_well_formed_DecOpt_sound Δ c : DecOptSoundPos (constructor_well_formed Δ c).
Proof. idtac "Admitted: constructor_well_formed_DecOpt_sound". Admitted. (* derive_sound. Qed. *)

Instance constructor_well_formed_DecOpt_complete Δ c : DecOptCompletePos (constructor_well_formed Δ c).
Proof. idtac "Admitted: constructor_well_formed_DecOpt_complete". Admitted. (* derive_complete. Qed. *)

Instance constructor_well_formed_DecOpt_monotonic Δ c : DecOptSizeMonotonic (constructor_well_formed Δ c).
Proof. idtac "Admitted: constructor_well_formed_DecOpt_monotonic". Admitted. (* derive_mon. Qed. *)





Inductive constructors_well_formed (Δ : ctx) : list constructor -> Prop :=
  | W_Nil :
      Δ |-ok_cs nil
  | W_Cons : forall c cs,
      Δ |-ok_c c ->
      Δ |-ok_cs cs ->
      Δ |-ok_cs (c :: cs)
  where 
    "Δ '|-ok_cs' cs" := (constructors_well_formed Δ cs).

QCDerive DecOpt for (constructors_well_formed Δ c).

Instance constructors_well_formed_DecOpt_sound Δ cs : DecOptSoundPos (constructors_well_formed Δ cs).
Proof. idtac "Admitted: constructors_well_formed_DecOpt_sound". Admitted. (* derive_sound. Qed. *)

Instance constructors_well_formed_DecOpt_complete Δ cs : DecOptCompletePos (constructors_well_formed Δ cs).
Proof. idtac "Admitted: constructors_well_formed_DecOpt_complete". Admitted. (* derive_complete. Qed. *)

Instance constructors_well_formed_DecOpt_monotonic Δ cs : DecOptSizeMonotonic (constructors_well_formed Δ cs).
Proof. idtac "Admitted: constructors_well_formed_DecOpt_monotonic". Admitted. (* derive_mon. Qed. *)





Definition tvd_name (tvd : tvdecl tyname) : tyname :=
  match tvd with
  | TyVarDecl v K => v
  end.

(* Quick cannot hanle function applications with implicit arguments. It ends up generating a function 
   application, where it tries to non-implicitly apply the implicit argument implicitly... :|.
   For example: the function application 'rev ls' has as implicit argument the type of the list ls.

   Quick chick would derive an computation that does not do '@rev type ls', but istead does 'rev (@type) ls'
   which is the exact inverse of what it should do?
 *)
Definition rev_map_tvd_name_app YKs Δ := rev (map tvd_name YKs) ++ Δ.
Definition rev_btvbs_app bs Δ := rev (@btvbs string string bs) ++ Δ.
Definition rev_bvbs_app bs Γ := rev (@btvbs string string bs) ++ Γ.
Definition rev_bvbs_data_app c cs bs Γ := rev (rev (map (@bvc string string)  cs) ++ @bvbs string string bs) ++ (c :: Γ).
Definition rev_bvc_app c cs Γ := c :: (rev (map (@bvc string string) cs)) ++ Γ.

Inductive well_scoped_tm (Δ Γ: ctx) : Term -> Prop :=  
  | WS_Var : forall x,
      NameIn x Γ ->
      Δ ,, Γ |-+ (Var x)
  | WS_LamAbs : forall x T t,
      Δ |-* T ->
      Δ ,, (x :: Γ) |-+ t ->
      Δ ,, Γ |-+ (LamAbs x T t)
  | WS_Apply : forall t1 t2,
      Δ ,, Γ |-+ t1 ->
      Δ ,, Γ |-+ t2 ->
      Δ ,, Γ |-+ (Apply t1 t2)
  (* Universal types *)
  | WS_TyAbs : forall X K t,
      (X :: Δ) ,, Γ |-+ t ->
      Δ ,, Γ |-+ (TyAbs X K t)
  | WS_TyInst : forall t T,
      Δ ,, Γ |-+ t ->
      Δ |-* T ->
      Δ ,, Γ |-+ (TyInst t T)
  | WS_IWrap : forall F T M,
      Δ |-* F ->
      Δ |-* T ->
      Δ ,, Γ |-+ M ->
      Δ ,, Γ |-+ (IWrap F T M)
  | WS_Unwrap : forall M,
      Δ ,, Γ |-+ M ->
      Δ ,, Γ |-+ (Unwrap M) 
  | WS_Constant : forall u (a : valueOf u),
      Δ ,, Γ |-+ (Constant (Some' a))
  | WS_Builtin : forall f,
      Δ ,, Γ |-+ (Builtin f)
  (* The original argument 'S' collides with the constructor 'S' in nat*)
  | WS_Error : forall S',
      Δ |-* S' ->
      Δ ,, Γ |-+ (Error S')
  | WS_Let_NonRec_Nil : forall t,
      Δ ,, Γ |-+ t ->
      Δ ,, Γ |-+ (Let NonRec nil t)
  | WS_Let_NonRec_TermBind : forall bs t t' s x T,
      Δ |-* T ->
      Δ ,, Γ |-+ t' ->
      rev_btvbs_app bs Δ ,, rev_btvbs_app bs (x :: Γ) |-+ t ->
      (* The term 't' only needs to be checked once here. The constant is a hack to be able to check the
       * bindings in bs, without causing further checks of 't', and a constant is always well-bounded *)
      Δ ,, Γ |-+ (Let Rec bs (Constant (Some' (ValueOf DefaultUniBool true)))) ->
      Δ ,, Γ |-+ (Let NonRec ((TermBind s (VarDecl x T) t') :: bs) t)
  | WS_Let_NonRec_TypeBind : forall bs t X K T,
      Δ |-* T ->
      rev_btvbs_app bs (X :: Δ) ,, rev_bvbs_app bs Γ |-+ t ->
      (* The term 't' only needs to be checked once here. The constant is a hack to be able to check the
       * bindings in bs, without causing further checks of 't', and a constant is always well-bounded *)
      Δ ,, Γ |-+ (Let Rec bs (Constant (Some' (ValueOf DefaultUniBool true)))) ->
      Δ ,, Γ |-+ (Let NonRec ((TypeBind (TyVarDecl X K) T) :: bs) t)
  | WS_Let_NonRec_DatatypeBind : forall bs t X K YKs c cs,
      constructors_well_formed (rev_map_tvd_name_app YKs Δ) cs ->
      rev_btvbs_app bs (X :: Δ) ,, rev_bvbs_data_app c cs bs Γ |-+ t ->
      (* The term 't' only needs to be checked once here. The constant is a hack to be able to check the
       * bindings in bs, without causing further checks of 't', and a constant is always well-bounded *)
      Δ ,, Γ |-+ (Let Rec bs (Constant (Some' (ValueOf DefaultUniBool true)))) ->
      Δ ,, Γ |-+ (Let NonRec ((DatatypeBind (Datatype (TyVarDecl X K) YKs c cs)) :: bs) t)
  | WS_Let_Rec_Nil : forall t,
      Δ ,, Γ |-+ t ->
      Δ ,, Γ |-+ (Let Rec nil t)
  | WS_Let_Rec_TermBind : forall bs t t' s x T,
      Δ |-* T ->
      Δ ,, Γ |-+ t' ->
      Δ ,, (x :: Γ) |-+ (Let NonRec bs t) ->
      Δ ,, Γ |-+ (Let Rec ((TermBind s (VarDecl x T) t') :: bs) t)
  | WS_Let_Rec_TypeBind : forall bs t X K T,
      Δ |-* T ->
      (X :: Δ) ,, Γ |-+ (Let NonRec bs t) ->
      Δ ,, Γ |-+ (Let Rec ((TypeBind (TyVarDecl X K) T) :: bs) t)
  | WS_Let_Rec_DatabindType : forall bs t X K YKs c cs,
      constructors_well_formed (rev_map_tvd_name_app YKs Δ) cs ->
      (X :: Δ) ,, rev_bvc_app c cs Γ |-+ (Let NonRec bs t) ->
      Δ ,, Γ |-+ (Let Rec ((DatatypeBind (Datatype (TyVarDecl X K) YKs c cs)) :: bs) t) 
  where "Δ ',,' Γ '|-+' t" := (well_scoped_tm Δ Γ t).
           
(*
 * (rev (btvbs bs) ++ Δ) ,, (rev (bvbs bs) ++ (x :: Γ)) |-+ t
 *
 * let unkn_1859_ := btvbs (@string) (@string) bs in
 * let unkn_1860_ := rev (@string) unkn_1859_ in
 * let unkn_1861_ := app (@string) unkn_1860_ Δ_ in
 * let unkn_1862_ := bvbs (@string) (@string) bs in
 * let unkn_1863_ := rev (@string) unkn_1862_
 *)

QCDerive DecOpt for (well_scoped_tm Δ Γ tm).

Instance well_scoped_tm_DecOpt_sound Δ Γ tm : DecOptSoundPos (well_scoped_tm Δ Γ tm).
Proof. idtac "Admitted: well_scoped_tm_DecOpt_sound". Admitted. (* derive_sound. Qed. *)

Instance well_scoped_tm_DecOpt_complete Δ Γ tm : DecOptCompletePos (well_scoped_tm Δ Γ tm).
Proof. idtac "Admitted: well_scoped_tm_DecOpt_complete". Admitted. (* derive_complete. Qed. *)

Instance well_scoped_tm_DecOpt_monotonic Δ Γ tm: DecOptSizeMonotonic (well_scoped_tm Δ Γ tm).
Proof. idtac "Admitted: well_scoped_tm_DecOpt_monotonic". Admitted. (* derive_mon. Qed. *)

(* Original well_scoped definition, including mutual recursion *)

Reserved Notation "Δ ',,' Γ '|-old' t " (at level 101, t at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-ok_b' b" (at level 101, b at level 0, no associativity).


Inductive well_scoped_old (Δ Γ: ctx) : Term -> Prop :=
  | WS_Var' : forall x,
      In x Γ ->
      Δ ,, Γ |-old (Var x)
  | WS_LamAbs' : forall x T t,
      Δ |-* T ->
      Δ ,, (x :: Γ) |-old t ->
      Δ ,, Γ |-old (LamAbs x T t)
  | WS_Apply' : forall t1 t2,
      Δ ,, Γ |-old t1 ->
      Δ ,, Γ |-old t2 ->
      Δ ,, Γ |-old (Apply t1 t2)
  (* Universal types *)
  | WS_TyAbs' : forall X K t,
      (X :: Δ) ,, Γ |-old t ->
      Δ ,, Γ |-old (TyAbs X K t)
  | WS_TyInst' : forall t T,
      Δ ,, Γ |-old t ->
      Δ |-* T ->
      Δ ,, Γ |-old (TyInst t T)
  | WS_IWrap' : forall F T M,
      Δ |-* F ->
      Δ |-* T ->
      Δ ,, Γ |-old M ->
      Δ ,, Γ |-old (IWrap F T M)
  | WS_Unwrap' : forall M,
      Δ ,, Γ |-old M ->
      Δ ,, Γ |-old (Unwrap M)
  | WS_Constant' : forall u a,
      Δ ,, Γ |-old (Constant (Some' (ValueOf u a)))
  | WS_Builtin' : forall f,
      Δ ,, Γ |-old (Builtin f)
  | WS_Error' : forall S,
      Δ |-* S ->
      Δ ,, Γ |-old (Error S)
  | WS_Let' : forall bs t Δ' Γ',
      Δ' = rev (btvbs bs) ++ Δ ->
      Γ' = rev (bvbs bs) ++ Γ ->
      Δ ,, Γ |-oks_nr bs ->
      Δ' ,, Γ' |-old t ->
      Δ ,, Γ |-old (Let NonRec bs t)
  | WS_LetRec' : forall bs t Δ' Γ',
      Δ' = rev (btvbs bs) ++ Δ ->
      Γ' = rev (bvbs bs) ++ Γ ->
      Δ' ,, Γ' |-oks_r bs ->
      Δ' ,, Γ' |-old t ->
      Δ ,, Γ |-old (Let Rec bs t)

with bindings_well_formed_nonrec (Δ Γ : ctx) : list Binding -> Prop :=
  | W_NilB_NonRec :
    Δ ,, Γ |-oks_nr nil
  | W_ConsB_NonRec : forall b bs,
      Δ ,, Γ |-ok_b b ->
      (btvb b ++ Δ) ,, (bvb b ++ Γ) |-oks_nr bs ->
      Δ ,, Γ |-oks_nr (b :: bs)

with bindings_well_formed_rec (Δ Γ : ctx) : list Binding -> Prop :=
  | W_NilB_Rec :
      Δ ,, Γ |-oks_r nil
  | W_ConsB_Rec : forall b bs,
      Δ ,, Γ |-ok_b b ->
      Δ ,, Γ |-oks_r bs ->
      Δ ,, Γ |-oks_r (b :: bs)

with binding_well_formed (Δ Γ : ctx) : Binding -> Prop :=
  | W_Term : forall s x T t,
      Δ |-* T ->
      Δ ,, Γ |-old t ->
      Δ ,, Γ |-ok_b (TermBind s (VarDecl x T) t)
  | W_Type : forall X K T,
      Δ |-* T ->
      Δ ,, Γ |-ok_b (TypeBind (TyVarDecl X K) T)
  | W_Data : forall X YKs cs matchFunc Δ',
      Δ' = rev (map tvd_name YKs) ++ Δ  ->
      (forall c, In c cs -> Δ' |-ok_c c) ->
      Δ ,, Γ |-ok_b (DatatypeBind (Datatype X YKs matchFunc cs))

  where "Δ ',,' Γ '|-old' t" := (well_scoped_old Δ Γ t)
  and "Δ ',,' Γ '|-oks_nr' bs" := (bindings_well_formed_nonrec Δ Γ bs)
  and "Δ ',,' Γ '|-oks_r' bs" := (bindings_well_formed_rec Δ Γ bs)
  and "Δ ',,' Γ '|-ok_b' b" := (binding_well_formed Δ Γ b).

(* TODO: not finished, but is this necessary? *)
Lemma well_scoped_eq : forall Δ Γ tm,
  well_scoped_tm Δ Γ tm <-> well_scoped_old Δ Γ tm.
Proof.
  intros Δ Γ tm; split; revert Δ Γ.
  - induction tm; intros;
    try (inversion H; constructor; try apply NameIn_In_string_equal; try apply IHtm1; try apply IHtm2; try apply IHtm; assumption; reflexivity).
    + admit.
    + inversion H; induction a; constructor. 
  - induction tm; intros;
    try (inversion H; constructor; try apply IHtm; try apply IHtm1; try apply IHtm2; assumption; reflexivity).
    + admit.
    + constructor. inversion H. apply NameIn_In_string_equal. apply H1.
Admitted.
