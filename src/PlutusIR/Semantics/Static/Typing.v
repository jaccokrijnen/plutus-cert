Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
From PlutusCert Require Import Analysis.BoundVars.

Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.Normalisation.Normalisation.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Static.Builtins.Signatures.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Export PlutusCert.PlutusIR.Analysis.FreeVars.

From PlutusCert Require Import util.


Import Coq.Lists.List.
Import ListNotations.
Import Coq.Strings.String.
Local Open Scope string_scope.

(* Common built-in types *)
Definition Ty_Int := Ty_Builtin DefaultUniInteger.
Definition Ty_Bool := Ty_Builtin DefaultUniBool.
Definition Ty_String := Ty_Builtin DefaultUniString.
Definition Ty_Unit := Ty_Builtin DefaultUniUnit.
Definition Ty_BS := Ty_Builtin DefaultUniByteString.

Definition Ty_BinOp t := Ty_Fun t (Ty_Fun t t).
Definition Ty_BinPred t := Ty_Fun t (Ty_Fun t Ty_Bool).

(** Types of builtin functions *)
Definition lookupBuiltinTy f := to_ty (to_sig f).


(** Helper funcitons*)
Definition flatten {A : Type} (l : list (list A)) := List.concat (rev l).

Open Scope list_scope.
Lemma flatten_cons {A} x (xs : list (list A)) :
  flatten (x :: xs) = flatten xs ++ x.
Proof.
  unfold flatten. simpl.
  rewrite concat_app. simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Definition fromDecl (tvd : tvdecl) : string * kind :=
  match tvd with
  | TyVarDecl v K => (v, K)
  end.

(* TODO:

well-kinded?
normalisation preserves kinding.
T has kind K 
F has kind (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base))

(Ty_IFix F (Ty_Var "X") has kind Kind_Base if (Ty_Var "X") has kind K.

Then (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X"))) has kind (Kind_Arrow K Kind_Base)

We apply F to this type to get the same kind back (see kind F), so then we have
(Ty_App F (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X")))) has kind (Kind_Arrow K Kind_Base)

T has kind K, so this is well kinded with kind Kind_Base and for every context.
*)
Definition unwrapIFix (F : ty) (K : kind) (T : ty) : ty := (Ty_App (Ty_App F (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X")))) T).

(* TODO: Do we really need bound variables? *)
Definition freshUnwrapIFix (F : ty) : string :=
  "a" ++ String.concat EmptyString (FreeVars.Ty.ftv F).



Definition unwrapIFixFresh (F : ty) (K : kind) (T : ty) : ty :=
  let b := freshUnwrapIFix F in 
 (Ty_App (Ty_App F (Ty_Lam b K (Ty_IFix F (Ty_Var b)))) T).

(* TODO: See also Theorems/Weakening
*)
Lemma weakening : forall T T2 K X Δ,
      ~ In X (FreeVars.Ty.ftv T) ->
      Δ |-* T : K ->
      ((X, T2)::Δ) |-* T : K.
Proof.
Admitted.

Lemma unwrapIFixFresh_ftv_helper F :
  ~ In (freshUnwrapIFix F) (FreeVars.Ty.ftv F).
Admitted.

Lemma unwrapIFixFresh__well_kinded F K T Δ :
  Δ |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
  Δ |-* T : K ->
  Δ |-* (unwrapIFixFresh F K T) : Kind_Base.
Proof.
  intros.
  unfold unwrapIFix.
  eapply K_App with (K1 := K); auto.
  eapply K_App with (K1 := Kind_Arrow K Kind_Base); auto.
  eapply K_Lam.
  eapply K_IFix with (K := K); auto.
  - remember (freshUnwrapIFix F) as X.
    constructor.
    simpl.
    rewrite String.eqb_refl.
    reflexivity.
  - remember (freshUnwrapIFix F) as x.
    (* Now weaken *)
    eapply weakening with (Δ := Δ); auto.
    unfold List.inclusion.
    (* By definition of freshUnwrapIFix *)
    subst.
    apply unwrapIFixFresh_ftv_helper.
Qed.

(** Typing of terms *)
Reserved Notation "Delta ',,' Gamma '|-+' t ':' T" (at level 101, t at level 0, T at level 0, no associativity).
Reserved Notation "Delta '|-ok_c' c ':' T" (at level 101, c at level 0, T at level 0).
Reserved Notation "Delta ',,' Gamma  '|-oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-ok_b' rec ## b" (at level 101, b at level 0, no associativity).

Local Open Scope list_scope.

Fixpoint insert_deltas_rec (xs : list (string * ty)) (Δ : list (string * kind)) := 
match xs with
  | nil => nil
  | (X, T):: xs' => (X, T, Δ) :: insert_deltas_rec xs' Δ
end.

Lemma insert_deltas_rec_app xs ys Δ :
  insert_deltas_rec (xs ++ ys) Δ = insert_deltas_rec xs Δ ++ insert_deltas_rec ys Δ.
Proof.
  induction xs.
  - reflexivity.
  - simpl. rewrite IHxs. 
    destruct a.
    reflexivity.
Qed.

Inductive has_type : list (string * kind) -> list (string * ty) -> term -> ty -> Prop :=
  (* Simply typed lambda caclulus *)
  | T_Var : forall Γ Δ x T Tn K,
      lookup x Γ = Coq.Init.Datatypes.Some T ->
      Δ |-* T : K -> (* Added *)
      normalise T Tn ->
      Δ ,, Γ |-+ (Var x) : Tn
  | T_LamAbs : forall Δ Γ x T1 t T2n T1n,
      Δ |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Δ ,, (x, T1n) :: Γ |-+ t : T2n ->
      Δ ,, Γ |-+ (LamAbs x T1 t) : (Ty_Fun T1n T2n)
  | T_Apply : forall Δ Γ t1 t2 T1n T2n,
      Δ ,, Γ |-+ t1 : (Ty_Fun T1n T2n) ->
      Δ ,, Γ |-+ t2 : T1n ->
      Δ ,, Γ |-+ (Apply t1 t2) : T2n
  (* Universal types *)
  | T_TyAbs : forall Δ Γ X K t Tn,
      ((X, K) :: Δ) ,, Γ |-+ t : Tn ->
      Δ ,, Γ |-+ (TyAbs X K t) : (Ty_Forall X K Tn)
  | T_TyInst : forall Δ Γ t1 T2 T1n X K2 T0n T2n,
      Δ ,, Γ |-+ t1 : (Ty_Forall X K2 T1n) ->
      ((X, K2)::Δ) |-* T1n : Kind_Base -> (* Richard: Added *)
      Δ |-* T2 : K2 ->
      normalise T2 T2n ->
      normalise (substituteTCA X T2n T1n) T0n ->
      Δ ,, Γ |-+ (TyInst t1 T2) : T0n
  (* Recursive types *)
  | T_IWrap : forall Δ Γ F T M K Tn Fn T0n,
      Δ |-* T : K ->
      normalise T Tn ->
      Δ |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      normalise F Fn ->
      normalise (unwrapIFixFresh Fn K Tn) T0n -> (* Richard: Changed to fresh!*)
      Δ ,, Γ |-+ M : T0n ->
      Δ ,, Γ |-+ (IWrap F T M) : (Ty_IFix Fn Tn)
  | T_Unwrap : forall Δ Γ M Fn K Tn T0n,
      Δ ,, Γ |-+ M : (Ty_IFix Fn Tn) ->
      Δ |-* Fn : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) -> (* Richard: Added *)
      Δ |-* Tn : K ->
      normalise (unwrapIFixFresh Fn K Tn) T0n -> (* Richard: Changed to fresh*)
      Δ ,, Γ |-+ (Unwrap M) : T0n
  (* Additional constructs *)
  | T_Constant : forall Δ Γ T a,
      Δ ,, Γ |-+ (Constant (ValueOf T a)) : (Ty_Builtin T)
  | T_Builtin : forall Δ Γ f T Tn,
      T = lookupBuiltinTy f ->
      normalise T Tn ->
      Δ ,, Γ |-+ (Builtin f) : Tn
  | T_Error : forall Δ Γ S Sn,
      Δ |-* S : Kind_Base ->
      normalise S Sn -> (* S Sn (denk aan preservation. T Tn hadden we geimplementeerd omdat dat makkelijk is voor preservation mss, maar dat werkt niet voor completeness ), maak pull request*)
      Δ ,, Γ |-+ (Error S) : Sn
  (** Let-bindings
      Note: The rules for let-constructs differ significantly from the paper definitions
      because we had to adapt the typing rules to the compiler implementation of type checking.
      Reference: The Haskell module PlutusIR.TypeCheck.Internal in the
      iohk/plutus/plutus-core/plutus-ir project.
  **)
  | T_Let : forall Δ Γ bs t Tn Δ' Γ' bsGn,
      (* New type variable names may not already occur in the environment, 
       * see Teams discussion Jacco Mar 26, add Either example to thesis 
       *)
      NoDup (btvbs bs ++ (map fst Δ)) ->

      Δ' = flatten (map binds_Delta bs) ++ Δ -> (* TODO: flatten reverses. Should it? *)
      map_normalise (flatten (map binds_Gamma bs)) bsGn ->
      Γ' = bsGn ++ Γ ->
      Δ ,, Γ |-oks_nr bs ->
      Δ' ,, Γ' |-+ t : Tn ->
      Δ |-* Tn : Kind_Base ->
      Δ ,, Γ |-+ (Let NonRec bs t) : Tn
  | T_LetRec : forall Δ Γ bs t Tn Δ' Γ' bsGn,
      NoDup (btvbs bs ++ (map fst Δ)) ->
      (* There can be no duplicate bound variables in a let-rec *)
      NoDup (btvbs bs) ->
      NoDup (bvbs bs) ->

      Δ' = flatten (map binds_Delta bs) ++ Δ ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn -> (* TODO: Why do we need this to be normalised? Create a counterexample that shows things go wrong without normalisation here*)
      Γ' = bsGn ++ Γ->
      Δ' ,, Γ' |-oks_r bs ->
      Δ' ,, Γ' |-+ t : Tn ->
      Δ |-* Tn : Kind_Base ->
      Δ ,, Γ |-+ (Let Rec bs t) : Tn

(* Constructors are well-formed if their result type equals the fully applied
 * datatype (e.g. Either a b), and all parameter types are well-kinded
*)
with constructor_well_formed : list (string * kind) -> vdecl -> ty -> Prop :=
  | W_Con : forall Δ x T Targs Tr Tres,
      (Targs, Tres) = splitTy T ->
      (* We don't check the well-kindedness of Tres, this happens in
         W_Data (since the kind context needs to be slightly larger) *)
      (forall Ta, In Ta Targs -> Δ |-* Ta : Kind_Base) ->
      Tres = Tr ->
      Δ |-ok_c (VarDecl x T) : Tr

with bindings_well_formed_nonrec : list (string * kind) -> list (string * ty) -> list binding -> Prop :=
  | W_NilB_NonRec : forall Δ Γ,
      Δ ,, Γ |-oks_nr nil
  | W_ConsB_NonRec : forall Δ Γ b bs bsGn,
      Δ ,, Γ |-ok_b NonRec ## b ->
      map_normalise (binds_Gamma b) bsGn ->
      ((binds_Delta b) ++ Δ) ,, (bsGn ++ Γ) |-oks_nr bs ->
      Δ ,, Γ |-oks_nr (b :: bs)

with bindings_well_formed_rec : list (string * kind) -> list (string * ty) -> list binding -> Prop :=
  | W_NilB_Rec : forall Δ Γ,
      Δ ,, Γ |-oks_r nil
  | W_ConsB_Rec : forall Δ Γ b bs,
      Δ ,, Γ |-ok_b Rec ## b ->
      Δ ,, Γ |-oks_r bs ->
      Δ ,, Γ |-oks_r (b :: bs)

with binding_well_formed : list (string * kind) -> list (string * ty) -> recursivity -> binding -> Prop :=
  | W_Term : forall Δ Γ s x T t Tn rec,
      Δ |-* T : Kind_Base ->
      normalise T Tn ->
      Δ ,, Γ |-+ t : Tn ->
      Δ ,, Γ |-ok_b rec ## (TermBind s (VarDecl x T) t)
  | W_Type : forall Δ Γ X K T rec,
      Δ |-* T : K ->
      Δ ,, Γ |-ok_b rec ## (TypeBind (TyVarDecl X K) T)
   | W_Data : forall Δ Γ dtd XK YKs matchFunc cs X Ys Δ' Tres rec,
      dtd = Datatype XK YKs matchFunc cs ->
      X = tvdecl_name XK ->
      Ys = map tvdecl_name YKs ->

      (* No duplicate bound type variables *)
      NoDup (X :: Ys) ->

      (* No duplicate constructor names*)
      NoDup (map vdecl_name cs) ->

      (* Well-formedness of constructors *)
      Δ' = rev (map fromDecl YKs) ++ Δ -> 
      Tres = constrLastTyExpected dtd -> (* The expected result type for each constructor *)
      (forall c, In c cs -> Δ' |-ok_c c : Tres) ->

      (* The expected result type is well-kinded *)
      (* In the case that this DatatypeBind is in a let-rec, X will already be
       * in Δ, hence we check for this to keep our NoDup invariant on Delta
       *)

       match rec with
       | NonRec => (fromDecl XK :: Δ') |-* Tres : Kind_Base
       | Rec => (Δ' |-* Tres : Kind_Base)
       end   ->

      Δ ,, Γ |-ok_b rec ## (DatatypeBind dtd)

  where "Δ ',,' Γ '|-+' t ':' T" := (has_type Δ Γ t T)
  and  "Δ '|-ok_c' c ':' T" := (constructor_well_formed Δ c T)
  and "Δ ',,' Γ '|-oks_nr' bs" := (bindings_well_formed_nonrec Δ Γ bs)
  and "Δ ',,' Γ '|-oks_r' bs" := (bindings_well_formed_rec Δ Γ bs)
  and "Δ ',,' Γ '|-ok_b' rec ## b" := (binding_well_formed Δ Γ rec b).

Scheme has_type__ind := Minimality for has_type Sort Prop
  with constructor_well_formed__ind := Minimality for constructor_well_formed Sort Prop
  with bindings_well_formed_nonrec__ind := Minimality for bindings_well_formed_nonrec Sort Prop
  with bindings_well_formed_rec__ind := Minimality for bindings_well_formed_rec Sort Prop
  with binding_well_formed__ind := Minimality for binding_well_formed Sort Prop.

Combined Scheme has_type__multind from
  has_type__ind,
  bindings_well_formed_nonrec__ind,
  bindings_well_formed_rec__ind,
  binding_well_formed__ind.

Lemma lookupBuiltinTy__well_kinded f Δ :
  Δ |-* (lookupBuiltinTy f) : Kind_Base.
Proof.
  destruct f; repeat constructor.
Qed.


Opaque dtdecl_freshR.


Inductive FreshOver : string -> list string -> Prop :=
  | FreshOver_nil : forall fr, FreshOver fr []
  | FreshOver_cons : forall fr x xs, ~ In fr (x :: xs) -> FreshOver fr xs -> FreshOver fr (x :: xs).

(* Opaque dtdecl_freshR. *)

(* Prototype with only one type variable*)
Lemma b_wf__wk Δ Γ b rec:
  Δ ,, Γ |-ok_b rec ## b -> (rec = NonRec -> NoDup (btvb b ++ (map fst Δ))) -> forall T _x, In (_x, T) (binds_Gamma b) -> exists K Δ', Δ' |-* T : K.
Proof.
  (* intros Hb_wf H_ns T _x Hin_b.
  inversion Hb_wf;  subst.
  - admit.
  - admit.
  - 
    clear Hb_wf.
    unfold binds_Gamma in Hin_b.
    destruct Hin_b as [Hm_bind | Hc_bind].
    + clear H_ns.
     (*Case: match bind*)

      (* Idea, we prove the lemma for all strings that are fresh, (not this specific one)
          because for that we can do induction. (equality of fresh vars stopped us before from using the IH.)
       *)

      simpl in Hm_bind.
      inversion Hm_bind; subst.
      clear Hm_bind.
      exists Kind_Base.
      destruct YKs.
      exists ((b, k)::Δ).
      constructor.
      simpl.
      clear H7.


      remember (dtdecl_freshR (Datatype XK [TyVarDecl b k] _x cs)) as fr.
      clear H3. clear H2.
      

      destruct XK.
      simpl.
      simpl in H6.
      assert (
        forall fr',
        (~ In fr' (b0 :: b :: 
            flat_map (fun c => Ty.ftv (vdecl_ty c)) cs))
        -> ((fr', Kind_Base) :: (b, k) :: Δ)
              |-* (fold_right Ty_Fun (Ty_Var fr')
              (map (fun c : vdecl => replaceRetTy (vdecl_ty c) (Ty_Var fr')) cs))
            : Kind_Base)
        .
        {
          clear Heqfr.
          clear fr.
          intros.
          generalize dependent fr'.

          simpl in H6.

          induction cs; intros.
          - simpl. constructor. simpl. rewrite String.eqb_refl. auto.
          - assert (fr'
              ∉ (b0
              :: b
              :: flat_map
                (fun c : vdecl => Ty.ftv (vdecl_ty c))
                (cs))) by admit.
            assert (Hc_wf_smaller: (forall c : vdecl,
              c ∈ cs ->
              (b, k) :: Δ |-ok_c c
              : (Ty_App (Ty_Var (b0))
                (Ty_Var (b))))).
            {
              intros.
              eapply H6. apply in_cons. auto.
            }
            specialize (IHcs Hc_wf_smaller fr' H0).
            simpl.
            constructor.
            + specialize (H6 a).
              assert (In a (a :: cs)) by now apply in_eq.
              specialize (H6 H1).
              inversion H6; subst.
              assert (exists Targ1, T = Ty_Fun Targ1 (Ty_App (Ty_Var b0) (Ty_Var b))) by admit.
              (* Assuming one argument for now*)
              destruct H4 as [Targ1 H4]; subst.
              simpl.
              constructor.
              * inversion H2. subst.
                specialize (H3 Targ1). 
                (* fr' fresh over Δ? We can see it cannot be in Targ1 by fr' not in ftv Targ1
                  it can be in Δ, but that is no issue
                *)

                admit.
              * constructor. simpl. rewrite String.eqb_refl. auto.
            + eapply IHcs.
        }

        eapply H.
        (* by definition of freshness!*)
        
        
        admit. 

        
    + (*Case: constr bind*)
      unfold constrBinds in Hc_bind.
      rewrite <- in_rev in Hc_bind.
      apply in_map_iff in Hc_bind.
      destruct Hc_bind as [c [HconstrBind Hxincs]].
      specialize (H6 c Hxincs).
      
      unfold constrBind in HconstrBind.
      destruct_match; subst. simpl in HconstrBind.
      (* unfold constrTy in HconstrBind. *)
      inversion HconstrBind; subst.
      exists Kind_Base. (* Ty_Forall always has Kind_Base, so also Ty_Foralls *)
      
      
      remember (Datatype XK [YKs] matchFunc cs) as d.
      destruct YKs.
      unfold fromDecl in H6.
      simpl in H6.
      destruct XK.
      destruct rec.
      {
          inversion H6; subst.
          exists ((b0, k0)::Δ).

          constructor.
          simpl in H6.
          remember (
            (Datatype (TyVarDecl b0 k0)
            [TyVarDecl b k] matchFunc
            cs)) as  d.
          assert (exists targ1, t = Ty_Fun targ1 (constrLastTyExpected d)) by admit.
          destruct H as [Htarg H]; subst.
          constructor; eauto.
          * simpl.
            simpl in H1.
            inversion H1.
            subst.


            (* By NoDup (b :: map fst Δ), we have b not in Delta, and by H2, we have b not b0, hence we can add it without fearign shadowing, kind of like weakening *)

          
          admit.
          * simpl.  
            simpl in H7.
        (* Now only rearrange in H7*)
        admit.
      
      }
      { 

                (* Rec *)
        inversion H6; subst.
        exists (Δ).

        remember ((Datatype (TyVarDecl b0 k0)
          [TyVarDecl b k] matchFunc
          cs)) as d.
        assert (exists targ1, t = Ty_Fun targ1 (constrLastTyExpected d)) by admit.
        destruct H as [Htarg H]; subst.
        constructor.
        constructor.
        * inversion H6; subst.
          simpl.
          eapply H9.
          unfold splitTy in H4.
          simpl in H4.
          inversion H4.
          subst.
          apply in_eq.
        * simpl.
          simpl in H7.
          auto.
    } *)
    admit.
Admitted.


(* We need this because we need to normalise every type in binds_Gamma b, and for normalisation we
    need well-kindedness
*)
(* Lemma b_wf__wk Δ Γ b :
  Δ ,, Γ |-ok_b b -> (forall x K, In (x, K) (binds_Delta b) -> lookup x (Δ ++ (x, K)::nil) = Some K) -> forall T _x, In (_x, T) (binds_Gamma b) -> exists K Δ', Δ' |-* T : K.
Proof.
  (* intros.
  inversion H; subst.
  - inversion H0; intuition.
    inversion H4; subst; clear H4.
    exists Kind_Base.
    exists Δ.
    auto.
  - inversion H0; intuition.
  - clear H.
    unfold binds_Gamma in H0.
    destruct H0.
    + inversion H.
      exists Kind_Base.
      clear H1.
      
      assert ((rev (map fromDecl YKs) ++ Δ) |-* (Ty_Fun
          (Ty_Apps (Ty_Var (getTyname X))
          (map (Basics.compose Ty_Var getTyname) YKs))
          (Ty_Apps
          (Ty_Lams YKs
          (Ty_Forall "R" Kind_Base
          (fold_right Ty_Fun (Ty_Var "R")
          (map
          (fun c : vdecl =>
        branchTy c (Ty_Var "R"))
          cs))))
          (map (Basics.compose Ty_Var getTyname) YKs))) : Kind_Base).
      {
          constructor.
          - 
          (* hmm. what is the X *) admit.
          - assert ((rev (map fromDecl YKs) ++ Δ) |-* (Ty_Forall "R" Kind_Base
  (fold_right Ty_Fun (Ty_Var "R")
  (map (fun c : vdecl => branchTy c (Ty_Var "R"))
  cs))) : Kind_Base).
          {
            constructor.
            assert (forall c, In c cs -> ((("R", Kind_Base) :: rev (map fromDecl YKs) ++ Δ)
              |-* (Ty_Fun (Ty_Var "R") (branchTy c (Ty_Var "R")))
              : Kind_Base)).
            {
              intros.
              constructor.
              - constructor. auto.
              - unfold branchTy; fold branchTy.
                destruct c.
                (* By constructor well formed,
                  we have that if the type of the branch is a Fun
                  then all the arguments are base-kinded
                  so this should hold
                *)

                admit.
            }

            (* Having proven it for one constructor, we prove it for all constructors folded together*)

            clear H.
            clear H2.
            clear H3.
            induction cs.
            - simpl. now constructor.
            - simpl.
              constructor.
              + specialize (H0 a).
                assert (a ∈ (a :: cs)).
                {
                  left. auto.
                }
                specialize (H0 H).
                inversion H0; subst.
                auto.
              + apply IHcs; auto.
                intros.
                specialize (H0 c).
                eapply H0.
                apply in_cons. auto.
          }
      

          (* I feel like here we can remove the Ty_Apps and Ty_Lams
          *) 
          
          admit.
      }

    + unfold constrBinds in H.
      rewrite <- in_rev in H.
      apply in_map_iff in H.
      destruct H as [c [HconstrBind Hxincs]].
      specialize (H2 c Hxincs).
      remember (Datatype X YKs matchFunc cs) as d.
      unfold constrBind in HconstrBind.
      destruct_match; subst.
      (* unfold constrTy in HconstrBind. *)
      inversion HconstrBind; subst.
      exists Kind_Base. (* Ty_Forall always has Kind_Base, so also Ty_Foralls *)
      inversion H2; subst.
      assert ((rev (map fromDecl YKs) ++ Δ) |-* t : Kind_Base).
      {
        (* By H3 we know t = Fun targ1 (Fun targ2 ... (Fun targ_n (Ty_Var (getTyname X))))
          And by H5, all Targs are Kind_Base. Hence by type rule of Fun, the whole Fun is Tybased
          if X : Kind_Base, which we can add to Delta'.
        *)
        admit.
      }
 *)


Admitted. *)

Require Import Coq.Program.Equality.

Lemma b_wf__map_wk Δ Γ b rec:
  Δ ,, Γ |-ok_b rec ## b -> (rec = NonRec -> NoDup (btvb b ++ map fst Δ)) -> map_wk (insert_deltas_rec (binds_Gamma b) Δ).
Proof.
  intros.

    assert ((forall x T, In (x, T) (binds_Gamma b) -> exists K Δ, Δ |-* T : K)).
    {
      intros.
      eapply b_wf__wk; eauto.
    }
    generalize dependent Δ.
  induction (binds_Gamma b); intros.
  - simpl.
    constructor.
  - simpl.
    destruct a as [a1 a2].
    assert(exists K Δ, Δ |-* a2 : K).
    { 
      eapply H1.
      left.
      auto.
    }
    destruct H2 as [K [Δ' H2] ].
    apply MW_cons with (K := K); auto.
    + apply IHl.
      * simpl in H1.
        intros.
        eapply H1.
        right. eauto.
      * auto.
      * auto.
    + admit.
Admitted.

Lemma bs_wf_r__map_wk (Δ : list (string * kind)) Γ bs :
  Δ ,, Γ |-oks_r bs -> (NoDup (map fst Δ)) -> map_wk (insert_deltas_rec (flatten (map (binds_Gamma) bs)) Δ).
Proof.
  intros H H_ns.
  induction H.
  - constructor.
  - simpl.
    rewrite flatten_cons.
    rewrite insert_deltas_rec_app.
    apply map_wk_app.
    + apply b_wf__map_wk in H; eauto.
      intros. inversion H1.
    + apply b_wf__map_wk in H; eauto.
      intros. inversion H1.
Qed.

Fixpoint insert_deltas_bind_Gamma_nr (bs : list binding) (Δ : list (binderTyname * kind)) : list (binderName * ty * list (binderTyname * kind)) :=
  match bs with
  | [] => []
  | (b :: bs') => (insert_deltas_bind_Gamma_nr bs' (binds_Delta b ++ Δ)) ++ (insert_deltas_rec (binds_Gamma b) Δ)
  (* we do it in reverse to match the "flatten" from the definition of T_Let*)
  end.

Lemma bs_wf_nr__map_wk Δ Γ bs :
  Δ ,, Γ |-oks_nr bs -> (NoDup (btvbs bs ++ map fst Δ)) -> map_wk (insert_deltas_bind_Gamma_nr bs Δ). (* Hmm, should we have nonrec insertion here?*)
Proof.
  intros H H_ns.
  induction H.
  - constructor.
  - simpl.
    apply map_wk_app.
    + eapply IHbindings_well_formed_nonrec; eauto.
      assert (map fst (binds_Delta b) = btvb b).
      {
        clear.
        induction b.
        - simpl. destruct v. auto.
        - simpl. destruct t. auto.
        - simpl. destruct d. destruct t. auto.
      }
      (* so just rearranged from H_ns, so yes!*)
      admit.
    + eapply b_wf__map_wk.
      * eauto.
      * intros. (* subset preserves NoDup*) admit.
Admitted.


Definition well_typed t := exists T, [] ,, [] |-+ t : T.

Lemma T_Let__cons Δ Γ Γ_b b bs t Tn rec:
  Δ ,, Γ |-ok_b rec ## b ->
  Δ |-* Tn : Kind_Base -> (* Tn may not mention types bound in b (escaping) *)
  map_normalise (binds_Gamma b) Γ_b ->
  binds_Delta b ++ Δ ,, Γ_b ++ Γ |-+ (Let NonRec bs t) : Tn ->
  Δ ,, Γ |-+ (Let NonRec (b :: bs) t) : Tn
.
Proof.
  (* intros H_typing_b H_kind H_mn H_ty.
  inversion H_ty; subst.

  econstructor.
  - exact eq_refl.
  - unfold flatten.
    simpl.
    rewrite concat_app.
    simpl.
    rewrite app_nil_r.
    apply MN_app.
    + eassumption.
    + eassumption.
  - exact eq_refl.
  - econstructor.
    + assumption.
    + eassumption.
    + eassumption.
  - simpl.
    rewrite flatten_cons.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    assumption.
  - assumption. *)
Admitted.

Lemma has_type__normal : forall Delta Gamma t T,
    Delta ,, Gamma |-+ t : T ->
    normal_Ty T.
Proof with eauto.
  induction 1; intros; eauto using normalise_to_normal...
  - inversion IHhas_type1; subst...
    inversion H1.
Qed.



(* Notation for types of holes *)
Notation "Δ ',,' Γ '▷' T" := (Δ, Γ, T) (at level 101).

Reserved Notation "Δ₁ ',,' Γ₁ '|-C' C ':' HTy ↝ T₁" (at level 101, C at level 0, T₁ at level 0, no associativity).

(* Typing rules for one-hole contexts *)
Inductive context_has_type : list (string * kind) -> list (string * ty) -> context -> ((list (string * kind)) * list (string * ty) * ty) -> ty -> Prop :=

  | T_C_Hole : forall Δ Γ Tn,
      normal_Ty Tn ->
      Δ ,, Γ |-C C_Hole : (Δ ,, Γ ▷ Tn) ↝ Tn

  | T_C_LamAbs : forall Δ₁ Γ₁ x T1 C Δ Γ Tn T2n T1n,
      Δ₁ |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Δ₁ ,, (x, T1n) :: Γ₁ |-C C                 : (Δ ,, Γ ▷ Tn) ↝ T2n ->
      Δ₁ ,,             Γ₁ |-C (C_LamAbs x T1 C) : (Δ ,, Γ ▷ Tn) ↝ (Ty_Fun T1n T2n)

  | T_C_Apply_L : forall Δ₁ Γ₁ Δ Γ C t Tn T1n T2n,
      Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ Tn) ↝ (Ty_Fun T1n T2n) ->
      Δ₁ ,, Γ₁ |-+ t : T1n ->
      Δ₁ ,, Γ₁ |-C (C_Apply_L C t) : (Δ ,, Γ ▷ Tn) ↝ T2n

  | T_C_Apply_R : forall Δ₁ Γ₁ Δ Γ C t Tn T1n T2n,
      Δ₁ ,, Γ₁ |-+ t : (Ty_Fun T1n T2n) ->
      Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ Tn) ↝ T1n ->
      Δ₁ ,, Γ₁ |-C (C_Apply_R t C) : (Δ ,, Γ ▷ Tn) ↝ T2n

  where
    "Δ₁ ',,' Γ₁ '|-C' C ':' Hty ↝ T₁" := (context_has_type Δ₁ Γ₁ C Hty T₁)
.

Lemma context_has_type__normal : forall Δ₁ Γ₁ C Δ Γ T T₁,
    Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ T) ↝ T₁ ->
    normal_Ty T₁.
Proof with eauto using normalise_to_normal.
  intros Δ₁ Γ₁ C Δ Γ T T₁ Cty.
  induction Cty...

  (* C_App_L *)
  - inversion IHCty...
    (* NO_Neutral *)
    + inversion H0.

  (* C_App_R *)
  - apply has_type__normal in H.
    inversion H...
    (* NO_Neutral *)
    + inversion H0.
Qed.

Lemma context_has_type__hole_normal : forall Δ₁ Γ₁ C Δ Γ T T₁,
    Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ T) ↝ T₁ ->
    normal_Ty T.
Proof.
  intros Δ₁ Γ₁ C Δ Γ T T₁ Cty.
  Require Import Coq.Program.Equality.
  dependent induction Cty.
  all: eauto.
Qed.


Lemma context_has_type__apply : forall C t Δ₁ Γ₁ Δ Γ T T₁,
  (Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ T) ↝ T₁) ->
  (Δ ,, Γ |-+ t : T) ->
  (Δ₁ ,, Γ₁ |-+ (context_apply C t) : T₁).
Admitted.
