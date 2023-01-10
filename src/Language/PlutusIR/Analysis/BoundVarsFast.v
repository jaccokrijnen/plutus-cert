From Coq Require Import
  Strings.String
  Lists.List
  Arith.PeanoNat
  Strings.Ascii
  Program.Basics
  .

Import ListNotations.
Local Open Scope string_scope.

From PlutusCert Require Import
  Util
  Util.List
  Language.PlutusIR
  Language.PlutusIR.Folds
  Language.PlutusIR.Analysis.BoundVars.

Import NamedTerm.

From QuickChick Require Import QuickChick.





Fixpoint to_names_ty (ty : Ty) : list string :=
  match ty with
  | Ty_Fun T1 T2 => 
      to_names_ty T1 ++ to_names_ty T2
  | Ty_IFix F T =>
      to_names_ty F ++ to_names_ty T
  | Ty_Forall X K T =>
      X :: to_names_ty T
  | Ty_Lam X K T =>
      X :: to_names_ty T
  | Ty_App T1 T2 =>
    to_names_ty T1 ++ to_names_ty T2
  | _ => []
  end.

(* Uses more efficient list concatination, but since the list is lazily
 *  evaluated, I dont using this function is much faster.
 *)
Fixpoint to_names_ty' (ty : Ty) : list string -> list string :=
  match ty with
  | Ty_Fun T1 T2 => fun ls =>
      to_names_ty' T1 (to_names_ty' T2 ls)
  | Ty_IFix F T => fun ls =>
      to_names_ty' F (to_names_ty' T ls)
  | Ty_Forall X K T => fun ls =>
      X :: to_names_ty' T ls
  | Ty_Lam X K T => fun ls =>
      X :: to_names_ty' T ls
  | Ty_App T1 T2 => fun ls =>
    to_names_ty' T1 (to_names_ty' T2 ls)
  | _ => fun ls => ls
  end.

Lemma to_names_ty_app_equal : forall ty (xs : list string),
  app (to_names_ty ty) xs = to_names_ty' ty xs.
Proof.
  induction ty; intros; simpl; auto;
  try (rewrite <- app_assoc; rewrite IHty1; rewrite IHty2; reflexivity);
  f_equal; apply IHty.
Qed.

Lemma to_names_ty_equal : forall ty,
  to_names_ty ty = to_names_ty' ty [].
Proof. intros. rewrite <- to_names_ty_app_equal. rewrite <- app_nil_end. reflexivity. Qed.



(* 'accelerated' using a function evaluation, instead of a bunch of constructors defining
 *  what it means to be 'in' a type.
 *)
Inductive appears_bound_in_ty' (X: tyname) (T : Ty) : Prop :=
  | ABITYF :
      NameIn X (to_names_ty T) ->
      appears_bound_in_ty' X T.

QCDerive DecOpt for (appears_bound_in_ty' x ty).  

Instance appears_bound_in_ty'_DecOpt_sound x ty: DecOptSoundPos (appears_bound_in_ty' x ty).
Proof. derive_sound. Qed.

Instance appears_bound_in_ty'_DecOpt_complete x ty: DecOptCompletePos (appears_bound_in_ty' x ty).
Proof. derive_complete. Qed.

Instance appears_bound_in_ty'_DecOpt_monotonicity x ty: DecOptSizeMonotonic (appears_bound_in_ty' x ty).
Proof. derive_mon. Qed.

Ltac app_tac H IHL IHR L R := 
  apply NameIn_app in H as [H | H]; [ apply L; apply IHL | apply R; apply IHR]; apply H.

Lemma appears_bound_in_ty_in_to_name_ty : forall ty x,
  appears_bound_in_ty x ty <-> NameIn x (to_names_ty ty).
Proof.
  intros ty x; split; revert x.
  - induction ty; intros x H;
    try (inversion H; reflexivity);
    try (inversion H; apply NameIn_app; [left; apply IHty1 | right; apply IHty2 ]; apply H1);
    try (inversion H; try constructor; [try apply H2 | apply IHty; apply H4 ]).
  - induction ty; intros x H; simpl in H;
    try (inversion H; reflexivity);
    try (inversion H; constructor; [ apply H2 | apply IHty; apply H3]).
    + app_tac H IHty1 IHty2 ABITY_TyFun1 ABITY_TyFun2.
    + app_tac H IHty1 IHty2 ABITY_TyIFix1 ABITY_TyIFix2.
    + app_tac H IHty1 IHty2 ABITY_TyApp1 ABITY_TyApp2.
Qed.

Lemma appears_bound_in_ty_equal : forall ty x, 
  appears_bound_in_ty x ty <-> appears_bound_in_ty' x ty.
Proof. split; intros; try constructor; apply appears_bound_in_ty_in_to_name_ty; apply H. Qed.





Fixpoint bv_constructors (cs : list constructor) : list string :=
  match cs with
  | [] => []
  | (Constructor (VarDecl x _) _) :: cs' => x :: bv_constructors cs'
  end.

Fixpoint to_names_tm (tm : Term) : list string :=
  match tm with
  | LamAbs x T t => x :: to_names_tm t
  | Apply t1 t2 => to_names_tm t1 ++ to_names_tm t2
  | TyAbs X K t => to_names_tm t
  | TyInst t T => to_names_tm t
  | IWrap F T t => to_names_tm t
  | Unwrap t => to_names_tm t
  | Let r bs t0 => flat_map to_names_tm_binding bs ++ to_names_tm t0
  | _ => []
  end
with
  to_names_tm_binding b := 
    match b with 
    | TermBind _ (VarDecl x T) t => x :: to_names_tm t
    | DatatypeBind (Datatype XK YKs c cs) => c :: bv_constructors cs
    | _ => []
    end.


Inductive appears_bound_in_tm' (x : name) : Term -> Prop :=
  | ABITM : forall tm,
      NameIn x (to_names_tm tm) ->
      appears_bound_in_tm' x tm.  


QCDerive DecOpt for (appears_bound_in_tm' x tm).

Instance appears_bound_in_tm'_DecOpt_sound x tm: DecOptSoundPos (appears_bound_in_tm' x tm).
Proof. derive_sound. Qed.

Instance appears_bound_in_tm'_DecOpt_complete x ty: DecOptCompletePos (appears_bound_in_tm' x ty).
Proof. derive_complete. Qed.

Instance appears_bound_in_tm'_DecOpt_monotonicity x ty: DecOptSizeMonotonic (appears_bound_in_tm' x ty).
Proof. derive_mon. Qed.


Definition ABITM_P_Term (t : Term) := forall v,
  appears_bound_in_tm v t <-> appears_bound_in_tm' v t.

Definition ABITM_P_Binding (b : Binding) := forall v t bs recty,
  appears_bound_in_tm v (Let recty (b :: bs) t) <-> appears_bound_in_tm' v (Let recty (b :: bs) t).

Ltac inv_abitm :=
  match goal with
    H: appears_bound_in_tm ?v ?t
    |- _ => inversion H
  end.

Ltac find_abi :=
  match goal with
    H: appears_bound_in_tm ?v ?t,
    Himpl: forall v, appears_bound_in_tm v ?t -> appears_bound_in_tm' v ?t
    |- _ => apply Himpl in H; inversion H
  end.


Definition P_Term_abitm_abitm' (t : Term) := forall v,
  appears_bound_in_tm v t -> appears_bound_in_tm' v t.

Lemma abi_tm_abi_tm' : forall t, P_Term_abitm_abitm' t. 
Proof with eauto using appears_bound_in_tm, appears_bound_in_tm', NameIn.
  apply term_ind with (P := P_Term_abitm_abitm');
  unfold P_Term_abitm_abitm'; intros; try inv_abitm;
  try (constructor; find_abi; assumption); subst...
  - induction H2.
    * apply H in H3. inversion H3. constructor. simpl. apply NameIn_app...
    * subst.
  1, 2, 3, 4: subst; inversion H as [| x l Hx Hl Heq]; unfold P_Binding_abitm_abitm' in Hx; apply Hx; assumption.
  1, 2, 3, 4: constructor; try find_abi.
    - constructor. assumption. assumption.
    - apply NameIn_app...
    - apply NameIn_app...
    - induction H0; simpl; try (constructor; inversion IHappears_bound_in_tm)...
      5: rewrite H2.
      3, 4, 5: rewrite <- app_assoc.
      1, 2, 3, 4, 5: apply NameIn_app...
      destruct (string_dec v0 mfunc); subst; constructor. assumption.
      rewrite <- app_assoc. apply NameIn_app. left.
      inversion H0; [exfalso; apply n| simpl]; assumption.
    - unfold P_Binding_abitm_abitm'. intros.



      destruct v. destruct (string_dec v0 s0); 
      constructor; subst; simpl; constructor. assumption.
      inversion H0.
Admitted.      


Fixpoint to_names_ann (tm : Term) : list string :=
  match tm with
  | LamAbs x T tm => to_names_ty T ++ to_names_ann tm
  | Apply tm1 tm2 => to_names_ann tm1 ++ to_names_ann tm2
  | TyAbs X K tm => X :: to_names_ann tm
  | TyInst tm T => to_names_ann tm ++ to_names_ty T
  | IWrap F T tm => to_names_ty F ++ to_names_ty T ++ to_names_ann tm
  | Unwrap t => to_names_ann t
  | Error T => to_names_ty T
  | Let r bs t0 => flat_map to_names_ann_binding bs ++ to_names_ann t0
  | _ => []
  end
with
  to_names_ann_binding b := 
    match b with 
    | TermBind sTy (VarDecl x T) t => x :: to_names_ty T ++ to_names_ann t
    | TypeBind (TyVarDecl X K) T => X :: to_names_ty T
    | DatatypeBind (Datatype (TyVarDecl X K) YKs c cs) => [X]
    end.

Inductive appears_bound_in_ann' (X : tyname) : Term -> Prop :=
  | ABIA : forall tm,
      NameIn X (to_names_ann tm) ->
      appears_bound_in_ann' X tm.

QCDerive DecOpt for (appears_bound_in_ann' x tm).

Instance appears_bound_in_ann'_DecOpt_sound x tm: DecOptSoundPos (appears_bound_in_ann' x tm).
Proof. derive_sound. Qed.

Instance appears_bound_in_ann'_DecOpt_complete x tm: DecOptCompletePos (appears_bound_in_ann' x tm).
Proof. derive_complete. Qed.

Instance appears_bound_in_ann'_DecOpt_monotonic x tm: DecOptSizeMonotonic (appears_bound_in_ann' x tm).
Proof. derive_mon. Qed.

Lemma appears_bound_in_ann_in_to_name_ann : forall tm X,
  appears_bound_in_ann X tm <-> NameIn X (to_names_ann tm).
Proof with auto using 
  appears_bound_in_ann,
  NameIn.
  intros tm x; split; revert x.
  - induction tm; intros x H;
    try (inversion H; try apply NameIn_app; try constructor; auto; reflexivity).
    + admit.
    + inversion H; apply NameIn_app.
      * left. apply appears_bound_in_ty_equal. apply H1.
      * right. apply IHtm. apply H1.
    + inversion H; apply NameIn_app.
      * left. apply IHtm. apply H1.
      * right. apply appears_bound_in_ty_equal. apply H1.
    + inversion H. simpl. apply appears_bound_in_ty_equal. apply H1.
    + admit.
  - admit.
Admitted.
