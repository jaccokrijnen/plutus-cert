{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Main where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

main :: Prelude.IO ()
main = Prelude.undefined

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rec :: a1
false_rec =
  Prelude.error "absurd case"

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r _ h _ =
  h

data Bool =
   True
 | False deriving (Prelude.Show)

bool_rect :: a1 -> a1 -> Bool -> a1
bool_rect f f0 b =
  case b of {
   True -> f;
   False -> f0}

bool_rec :: a1 -> a1 -> Bool -> a1
bool_rec =
  bool_rect

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None deriving (Prelude.Show)

data Sum a b =
   Inl a
 | Inr b

data Prod a b =
   Pair a b deriving (Prelude.Show)

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a) deriving (Prelude.Show)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data SigT a p =
   ExistT a p

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

bool_dec :: Bool -> Bool -> Sumbool
bool_dec b1 b2 =
  bool_rec (\x -> case x of {
                   True -> Left;
                   False -> Right}) (\x ->
    case x of {
     True -> Right;
     False -> Left}) b1 b2

eqb :: Bool -> Bool -> Bool
eqb b1 b2 =
  case b1 of {
   True -> b2;
   False -> case b2 of {
             True -> False;
             False -> True}}

in_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
in_dec h a l =
  list_rec Right (\a0 _ iHl ->
    let {s = h a0 a} in case s of {
                         Left -> Left;
                         Right -> iHl}) l

remove :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> List a1
remove eq_dec x l =
  case l of {
   Nil -> Nil;
   Cons y tl ->
    case eq_dec x y of {
     Left -> remove eq_dec x tl;
     Right -> Cons y (remove eq_dec x tl)}}

rev :: (List a1) -> List a1
rev l =
  case l of {
   Nil -> Nil;
   Cons x l' -> app (rev l') (Cons x Nil)}

concat :: (List (List a1)) -> List a1
concat l =
  case l of {
   Nil -> Nil;
   Cons x l0 -> app x (concat l0)}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

fold_left :: (a1 -> a2 -> a1) -> (List a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   Nil -> a0;
   Cons b t -> fold_left f t (f a0 b)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (List a2) -> a1
fold_right f a0 l =
  case l of {
   Nil -> a0;
   Cons b t -> f b (fold_right f a0 t)}

existsb :: (a1 -> Bool) -> (List a1) -> Bool
existsb f l =
  case l of {
   Nil -> False;
   Cons a l0 -> orb (f a) (existsb f l0)}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool deriving (Prelude.Show)

ascii_rect :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
              -> a1) -> Ascii0 -> a1
ascii_rect f a =
  case a of {
   Ascii b b0 b1 b2 b3 b4 b5 b6 -> f b b0 b1 b2 b3 b4 b5 b6}

ascii_rec :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool ->
             a1) -> Ascii0 -> a1
ascii_rec =
  ascii_rect

ascii_dec :: Ascii0 -> Ascii0 -> Sumbool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x ->
    case x of {
     Ascii b8 b9 b10 b11 b12 b13 b14 b15 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ -> Left) (\_ -> Right) (bool_dec b7 b15))
                    (\_ -> Right) (bool_dec b6 b14)) (\_ -> Right)
                  (bool_dec b5 b13)) (\_ -> Right) (bool_dec b4 b12)) (\_ ->
              Right) (bool_dec b3 b11)) (\_ -> Right) (bool_dec b2 b10))
          (\_ -> Right) (bool_dec b1 b9)) (\_ -> Right) (bool_dec b0 b8)}) a
    b

eqb0 :: Ascii0 -> Ascii0 -> Bool
eqb0 a b =
  case a of {
   Ascii a0 a1 a2 a3 a4 a5 a6 a7 ->
    case b of {
     Ascii b0 b1 b2 b3 b4 b5 b6 b7 ->
      case case case case case case case eqb a0 b0 of {
                                     True -> eqb a1 b1;
                                     False -> False} of {
                                True -> eqb a2 b2;
                                False -> False} of {
                           True -> eqb a3 b3;
                           False -> False} of {
                      True -> eqb a4 b4;
                      False -> False} of {
                 True -> eqb a5 b5;
                 False -> False} of {
            True -> eqb a6 b6;
            False -> False} of {
       True -> eqb a7 b7;
       False -> False}}}

data String =
   EmptyString
 | String0 Ascii0 String deriving (Prelude.Show)

string_rect :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rect f f0 s =
  case s of {
   EmptyString -> f;
   String0 a s0 -> f0 a s0 (string_rect f f0 s0)}

string_rec :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rec =
  string_rect

string_dec :: String -> String -> Sumbool
string_dec s1 s2 =
  string_rec (\x -> case x of {
                     EmptyString -> Left;
                     String0 _ _ -> Right}) (\a _ x x0 ->
    case x0 of {
     EmptyString -> Right;
     String0 a0 s ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (x s)) (\_ ->
        Right) (ascii_dec a a0)}) s1 s2

eqb1 :: String -> String -> Bool
eqb1 s1 s2 =
  case s1 of {
   EmptyString -> case s2 of {
                   EmptyString -> True;
                   String0 _ _ -> False};
   String0 c1 s1' ->
    case s2 of {
     EmptyString -> False;
     String0 c2 s2' ->
      case eqb0 c1 c2 of {
       True -> eqb1 s1' s2';
       False -> False}}}

append :: String -> String -> String
append s1 s2 =
  case s1 of {
   EmptyString -> s2;
   String0 c s1' -> String0 c (append s1' s2)}

concat0 :: String -> (List String) -> String
concat0 sep ls =
  case ls of {
   Nil -> EmptyString;
   Cons x xs ->
    case xs of {
     Nil -> x;
     Cons _ _ -> append x (append sep (concat0 sep xs))}}

map2 :: (a1 -> a2) -> (List (List a1)) -> List (List a2)
map2 f ll =
  map (map f) ll

data ForallSet a p =
   ForallS_nil
 | ForallS_cons a (List a) p (ForallSet a p)

data ForallSet2 a p =
   ForallS2_nil
 | ForallS2_cons (List a) (List (List a)) (ForallSet a p) (ForallSet2 a p)

flatmap2 :: (a1 -> List a2) -> (List (List a1)) -> List a2
flatmap2 f l =
  fold_right (\ts acc ->
    app (fold_right (\t acc2 -> app (f t) acc2) Nil ts) acc) Nil l

data Recursivity =
   NonRec
 | Rec

data Strictness =
   NonStrict
 | Strict

data DefaultUni =
   DefaultUniInteger
 | DefaultUniByteString
 | DefaultUniString
 | DefaultUniUnit
 | DefaultUniBool
 | DefaultUniProtoList
 | DefaultUniProtoPair
 | DefaultUniData
 | DefaultUniBLS12_381_G1_Element
 | DefaultUniBLS12_381_G2_Element
 | DefaultUniBLS12_381_MlResult
 | DefaultUniApply DefaultUni DefaultUni deriving (Prelude.Show)

defaultUni_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
                   -> a1 -> (DefaultUni -> a1 -> DefaultUni -> a1 -> a1) ->
                   DefaultUni -> a1
defaultUni_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 d =
  case d of {
   DefaultUniInteger -> f;
   DefaultUniByteString -> f0;
   DefaultUniString -> f1;
   DefaultUniUnit -> f2;
   DefaultUniBool -> f3;
   DefaultUniProtoList -> f4;
   DefaultUniProtoPair -> f5;
   DefaultUniData -> f6;
   DefaultUniBLS12_381_G1_Element -> f7;
   DefaultUniBLS12_381_G2_Element -> f8;
   DefaultUniBLS12_381_MlResult -> f9;
   DefaultUniApply d0 d1 ->
    f10 d0 (defaultUni_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 d0) d1
      (defaultUni_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 d1)}

defaultUni_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
                  a1 -> (DefaultUni -> a1 -> DefaultUni -> a1 -> a1) ->
                  DefaultUni -> a1
defaultUni_rec =
  defaultUni_rect

type UniType = Any

data Constant =
   ValueOf DefaultUni UniType

data DefaultFun =
   AddInteger
 | SubtractInteger
 | MultiplyInteger
 | DivideInteger
 | QuotientInteger
 | RemainderInteger
 | ModInteger
 | EqualsInteger
 | LessThanInteger
 | LessThanEqualsInteger
 | AppendByteString
 | ConsByteString
 | SliceByteString
 | LengthOfByteString
 | IndexByteString
 | EqualsByteString
 | LessThanByteString
 | LessThanEqualsByteString
 | Sha2_256
 | Sha3_256
 | Blake2b_256
 | VerifyEd25519Signature
 | VerifyEcdsaSecp256k1Signature
 | VerifySchnorrSecp256k1Signature
 | AppendString
 | EqualsString
 | EncodeUtf8
 | DecodeUtf8
 | IfThenElse
 | ChooseUnit
 | Trace
 | FstPair
 | SndPair
 | ChooseList
 | MkCons
 | HeadList
 | TailList
 | NullList
 | ChooseData
 | ConstrData
 | MapData
 | ListData
 | IData
 | BData
 | UnConstrData
 | UnMapData
 | UnListData
 | UnIData
 | UnBData
 | EqualsData
 | SerialiseData
 | MkPairData
 | MkNilData
 | MkNilPairData
 | Bls12_381_G1_add
 | Bls12_381_G1_neg
 | Bls12_381_G1_scalarMul
 | Bls12_381_G1_equal
 | Bls12_381_G1_hashToGroup
 | Bls12_381_G1_compress
 | Bls12_381_G1_uncompress
 | Bls12_381_G2_add
 | Bls12_381_G2_neg
 | Bls12_381_G2_scalarMul
 | Bls12_381_G2_equal
 | Bls12_381_G2_hashToGroup
 | Bls12_381_G2_compress
 | Bls12_381_G2_uncompress
 | Bls12_381_millerLoop
 | Bls12_381_mulMlResult
 | Bls12_381_finalVerify
 | Keccak_256
 | Blake2b_224
 | IntegerToByteString
 | ByteStringToInteger

type Name = String

type Tyname = String

type BinderName = String

type BinderTyname = String

data Kind =
   Kind_Base
 | Kind_Arrow Kind Kind deriving (Prelude.Show)

kind_rect :: a1 -> (Kind -> a1 -> Kind -> a1 -> a1) -> Kind -> a1
kind_rect f f0 k =
  case k of {
   Kind_Base -> f;
   Kind_Arrow k0 k1 -> f0 k0 (kind_rect f f0 k0) k1 (kind_rect f f0 k1)}

kind_rec :: a1 -> (Kind -> a1 -> Kind -> a1 -> a1) -> Kind -> a1
kind_rec =
  kind_rect

data Ty =
   Ty_Var Tyname
 | Ty_Fun Ty Ty
 | Ty_IFix Ty Ty
 | Ty_Forall BinderTyname Kind Ty
 | Ty_Builtin DefaultUni
 | Ty_Lam BinderTyname Kind Ty
 | Ty_App Ty Ty
 | Ty_SOP (List (List Ty)) deriving (Prelude.Show)

ty_rect :: (Tyname -> a1) -> (Ty -> a1 -> Ty -> a1 -> a1) -> (Ty -> a1 -> Ty
           -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
           (DefaultUni -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
           (Ty -> a1 -> Ty -> a1 -> a1) -> ((List (List Ty)) -> a1) -> Ty ->
           a1
ty_rect f f0 f1 f2 f3 f4 f5 f6 t =
  case t of {
   Ty_Var t0 -> f t0;
   Ty_Fun t0 t1 ->
    f0 t0 (ty_rect f f0 f1 f2 f3 f4 f5 f6 t0) t1
      (ty_rect f f0 f1 f2 f3 f4 f5 f6 t1);
   Ty_IFix t0 t1 ->
    f1 t0 (ty_rect f f0 f1 f2 f3 f4 f5 f6 t0) t1
      (ty_rect f f0 f1 f2 f3 f4 f5 f6 t1);
   Ty_Forall b k t0 -> f2 b k t0 (ty_rect f f0 f1 f2 f3 f4 f5 f6 t0);
   Ty_Builtin d -> f3 d;
   Ty_Lam b k t0 -> f4 b k t0 (ty_rect f f0 f1 f2 f3 f4 f5 f6 t0);
   Ty_App t0 t1 ->
    f5 t0 (ty_rect f f0 f1 f2 f3 f4 f5 f6 t0) t1
      (ty_rect f f0 f1 f2 f3 f4 f5 f6 t1);
   Ty_SOP l -> f6 l}

ty_rec :: (Tyname -> a1) -> (Ty -> a1 -> Ty -> a1 -> a1) -> (Ty -> a1 -> Ty
          -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
          (DefaultUni -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
          (Ty -> a1 -> Ty -> a1 -> a1) -> ((List (List Ty)) -> a1) -> Ty ->
          a1
ty_rec =
  ty_rect

data Vdecl =
   VarDecl BinderName Ty

data Tvdecl =
   TyVarDecl BinderTyname Kind

data Dtdecl =
   Datatype Tvdecl (List Tvdecl) BinderName (List Vdecl)

data Term =
   Let Recursivity (List Binding) Term
 | Var Name
 | TyAbs BinderTyname Kind Term
 | LamAbs BinderName Ty Term
 | Apply Term Term
 | Constant0 Constant
 | Builtin DefaultFun
 | TyInst Term Ty
 | Error Ty
 | IWrap Ty Ty Term
 | Unwrap Term
 | Constr Ty Nat (List Term)
 | Case Ty Term (List Term)
data Binding =
   TermBind Strictness Vdecl Term
 | TypeBind Tvdecl Ty
 | DatatypeBind Dtdecl

vdecl_name :: Vdecl -> BinderName
vdecl_name c =
  case c of {
   VarDecl n _ -> n}

vdecl_ty :: Vdecl -> Ty
vdecl_ty c =
  case c of {
   VarDecl _ ty -> ty}

tvdecl_name :: Tvdecl -> BinderTyname
tvdecl_name tvd =
  case tvd of {
   TyVarDecl v _ -> v}

splitTy :: Ty -> Prod (List Ty) Ty
splitTy t =
  case t of {
   Ty_Fun targ t' -> Pair (Cons targ (fst (splitTy t'))) (snd (splitTy t'));
   _ -> Pair Nil t}

lookup :: String -> (List (Prod String a1)) -> Option a1
lookup k l =
  case l of {
   Nil -> None;
   Cons p l' ->
    case p of {
     Pair j x -> case eqb1 j k of {
                  True -> Some x;
                  False -> lookup k l'}}}

data Has_kind_uni =
   K_DefaultUniInteger
 | K_DefaultUniByteString
 | K_DefaultUniString
 | K_DefaultUniUnit
 | K_DefaultUniBool
 | K_DefaultUniData
 | K_DefaultUniBLS12_381_G1_Element
 | K_DefaultUniBLS12_381_G2_Element
 | K_DefaultUniBLS12_381_MlResult
 | K_DefaultUniApply Kind Kind DefaultUni DefaultUni Has_kind_uni Has_kind_uni
 | K_DefaultUniProtoPair
 | K_DefaultUniProtoList

data Has_kind =
   K_Var (List (Prod String Kind)) String Kind
 | K_Fun (List (Prod BinderName Kind)) Ty Ty Has_kind Has_kind
 | K_IFix (List (Prod BinderName Kind)) Ty Ty Kind Has_kind Has_kind
 | K_Forall (List (Prod BinderName Kind)) BinderName Kind Ty Has_kind
 | K_Builtin (List (Prod BinderName Kind)) DefaultUni Has_kind_uni
 | K_Lam (List (Prod BinderName Kind)) BinderName Kind Ty Kind Has_kind
 | K_App (List (Prod BinderName Kind)) Ty Ty Kind Kind Has_kind Has_kind
 | K_SOP (List (Prod BinderName Kind)) (List (List Ty)) ForallSet2_has_kind
data ForallSet2_has_kind =
   ForallSet2_nil (List (Prod BinderName Kind))
 | ForallSet2_cons (List (Prod BinderName Kind)) (List Ty) (List (List Ty)) 
 ForallSet_has_kind ForallSet2_has_kind
data ForallSet_has_kind =
   ForallSet_nil (List (Prod BinderName Kind))
 | ForallSet_cons (List (Prod BinderName Kind)) Ty (List Ty) Has_kind 
 ForallSet_has_kind

substituteT :: String -> Ty -> Ty -> Ty
substituteT x u t =
  case t of {
   Ty_Var y -> case eqb1 x y of {
                True -> u;
                False -> Ty_Var y};
   Ty_Fun t1 t2 -> Ty_Fun (substituteT x u t1) (substituteT x u t2);
   Ty_IFix f t0 -> Ty_IFix (substituteT x u f) (substituteT x u t0);
   Ty_Forall y k t' ->
    case eqb1 x y of {
     True -> Ty_Forall y k t';
     False -> Ty_Forall y k (substituteT x u t')};
   Ty_Builtin u0 -> Ty_Builtin u0;
   Ty_Lam y k1 t' ->
    case eqb1 x y of {
     True -> Ty_Lam y k1 t';
     False -> Ty_Lam y k1 (substituteT x u t')};
   Ty_App t1 t2 -> Ty_App (substituteT x u t1) (substituteT x u t2);
   Ty_SOP tss -> Ty_SOP (map2 (substituteT x u) tss)}

ftv :: Ty -> List String
ftv t =
  case t of {
   Ty_Var x -> Cons x Nil;
   Ty_Fun t1 t2 -> app (ftv t1) (ftv t2);
   Ty_IFix f t0 -> app (ftv f) (ftv t0);
   Ty_Forall x _ t' -> remove string_dec x (ftv t');
   Ty_Builtin _ -> Nil;
   Ty_Lam x _ t' -> remove string_dec x (ftv t');
   Ty_App t1 t2 -> app (ftv t1) (ftv t2);
   Ty_SOP tss -> flatmap2 ftv tss}

plutusTv :: Ty -> List String
plutusTv t =
  case t of {
   Ty_Var x -> Cons x Nil;
   Ty_Fun t1 t2 -> app (plutusTv t1) (plutusTv t2);
   Ty_IFix f1 t1 -> app (plutusTv f1) (plutusTv t1);
   Ty_Forall x _ t0 -> Cons x (plutusTv t0);
   Ty_Builtin _ -> Nil;
   Ty_Lam x _ t0 -> Cons x (plutusTv t0);
   Ty_App t1 t2 -> app (plutusTv t1) (plutusTv t2);
   Ty_SOP tss -> flatmap2 plutusTv tss}

fresh :: String -> Ty -> Ty -> String
fresh x u t =
  append (String0 (Ascii True False False False False True True False)
    EmptyString)
    (append x
      (append (concat0 EmptyString (plutusTv u))
        (concat0 EmptyString (plutusTv t))))

rename :: String -> String -> Ty -> Ty
rename x y t =
  substituteT x (Ty_Var y) t

map' :: (List a1) -> (a1 -> () -> a2) -> List a2
map' xs x =
  case xs of {
   Nil -> Nil;
   Cons x0 xs0 -> Cons (x x0 __) (map' xs0 (\y _ -> x y __))}

substituteTCA :: String -> Ty -> Ty -> Ty
substituteTCA a a0 b =
  let {
   fix_F x =
     let {x0 = case x of {
                (,) pr1 _ -> pr1}} in
     let {u = case case x of {
                    (,) _ pr2 -> pr2} of {
               (,) pr1 _ -> pr1}} in
     let {
      substituteTCA0 = \a1 a2 b0 ->
       let {y = (,) a1 ((,) a2 b0)} in (\_ -> fix_F y)}
     in
     case case case x of {
                (,) _ pr2 -> pr2} of {
           (,) _ pr2 -> pr2} of {
      Ty_Var t -> case eqb1 x0 t of {
                   True -> u;
                   False -> Ty_Var t};
      Ty_Fun t t0 -> Ty_Fun (substituteTCA0 x0 u t __)
       (substituteTCA0 x0 u t0 __);
      Ty_IFix t t0 -> Ty_IFix (substituteTCA0 x0 u t __)
       (substituteTCA0 x0 u t0 __);
      Ty_Forall b0 k t ->
       case eqb1 x0 b0 of {
        True -> Ty_Forall b0 k t;
        False ->
         case existsb (eqb1 b0) (ftv u) of {
          True ->
           let {y' = fresh x0 u t} in
           let {t' = rename b0 y' t} in
           Ty_Forall y' k (substituteTCA0 x0 u t' __);
          False -> Ty_Forall b0 k (substituteTCA0 x0 u t __)}};
      Ty_Builtin d -> Ty_Builtin d;
      Ty_Lam b0 k t ->
       case eqb1 x0 b0 of {
        True -> Ty_Lam b0 k t;
        False ->
         case existsb (eqb1 b0) (ftv u) of {
          True ->
           let {y' = fresh x0 u t} in
           let {t' = rename b0 y' t} in
           Ty_Lam y' k (substituteTCA0 x0 u t' __);
          False -> Ty_Lam b0 k (substituteTCA0 x0 u t __)}};
      Ty_App t t0 -> Ty_App (substituteTCA0 x0 u t __)
       (substituteTCA0 x0 u t0 __);
      Ty_SOP l -> Ty_SOP
       (map' l (\ts _ -> map' ts (\t _ -> substituteTCA0 x0 u t __)))}}
  in fix_F ((,) a ((,) a0 b))

type EqDec a = a -> a -> Sumbool

kind_dec :: EqDec Kind
kind_dec x y =
  kind_rec (\x0 -> case x0 of {
                    Kind_Base -> Left;
                    Kind_Arrow _ _ -> Right}) (\_ x0 _ x1 x2 ->
    case x2 of {
     Kind_Base -> Right;
     Kind_Arrow k k0 ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (x1 k0))
        (\_ -> Right) (x0 k)}) x y

ty_dec :: EqDec Ty
ty_dec =
  Prelude.error "AXIOM TO BE REALIZED"

type Eqb x = x -> x -> Bool

eq_dec_to_eqb :: (EqDec a1) -> Eqb a1
eq_dec_to_eqb dec_eq x y =
  case dec_eq x y of {
   Left -> True;
   Right -> False}

kind_eqb :: Eqb Kind
kind_eqb =
  eq_dec_to_eqb kind_dec

ty_eqb :: Eqb Ty
ty_eqb =
  eq_dec_to_eqb ty_dec

kind_check_default_uni :: DefaultUni -> Option Kind
kind_check_default_uni d =
  case d of {
   DefaultUniProtoList -> Some (Kind_Arrow Kind_Base Kind_Base);
   DefaultUniProtoPair -> Some (Kind_Arrow Kind_Base (Kind_Arrow Kind_Base
    Kind_Base));
   DefaultUniApply t t' ->
    let {o = kind_check_default_uni t} in
    let {o0 = kind_check_default_uni t'} in
    case o of {
     Some k0 ->
      case k0 of {
       Kind_Base -> None;
       Kind_Arrow k k' ->
        case o0 of {
         Some k'' -> case kind_eqb k'' k of {
                      True -> Some k';
                      False -> None};
         None -> None}};
     None -> None};
   _ -> Some Kind_Base}

kind_checking_default_uni_sound :: DefaultUni -> Kind -> Has_kind_uni
kind_checking_default_uni_sound d k =
  defaultUni_rec (\_ _ -> K_DefaultUniInteger) (\_ _ ->
    K_DefaultUniByteString) (\_ _ -> K_DefaultUniString) (\_ _ ->
    K_DefaultUniUnit) (\_ _ -> K_DefaultUniBool) (\_ _ ->
    K_DefaultUniProtoList) (\_ _ -> K_DefaultUniProtoPair) (\_ _ ->
    K_DefaultUniData) (\_ _ -> K_DefaultUniBLS12_381_G1_Element) (\_ _ ->
    K_DefaultUniBLS12_381_G2_Element) (\_ _ ->
    K_DefaultUniBLS12_381_MlResult) (\d1 iHd1 d2 iHd2 k0 _ ->
    let {o = kind_check_default_uni d1} in
    case o of {
     Some k1 ->
      case k1 of {
       Kind_Base -> false_rec;
       Kind_Arrow k2 _ ->
        let {o0 = kind_check_default_uni d2} in
        case o0 of {
         Some k3 ->
          let {b = kind_eqb k3 k2} in
          case b of {
           True ->
            eq_rec_r k2 (\_ iHd3 -> K_DefaultUniApply k2 k0 d1 d2
              (iHd1 (Kind_Arrow k2 k0) __) (iHd3 k2 __)) k3 __ iHd2;
           False -> false_rec};
         None -> false_rec}};
     None -> false_rec}) d k __

kind_check :: (List (Prod BinderTyname Kind)) -> Ty -> Option Kind
kind_check delta ty =
  case ty of {
   Ty_Var x -> lookup x delta;
   Ty_Fun t1 t2 ->
    let {o = kind_check delta t1} in
    let {o0 = kind_check delta t2} in
    case o of {
     Some k ->
      case k of {
       Kind_Base ->
        case o0 of {
         Some k0 ->
          case k0 of {
           Kind_Base -> Some Kind_Base;
           Kind_Arrow _ _ -> None};
         None -> None};
       Kind_Arrow _ _ -> None};
     None -> None};
   Ty_IFix f t ->
    case kind_check delta t of {
     Some k ->
      case kind_check delta f of {
       Some k0 ->
        case k0 of {
         Kind_Base -> None;
         Kind_Arrow k1 k2 ->
          case k1 of {
           Kind_Base -> None;
           Kind_Arrow k3 k4 ->
            case k4 of {
             Kind_Base ->
              case k2 of {
               Kind_Base -> None;
               Kind_Arrow k5 k6 ->
                case k6 of {
                 Kind_Base ->
                  case andb (kind_eqb k k3) (kind_eqb k k5) of {
                   True -> Some Kind_Base;
                   False -> None};
                 Kind_Arrow _ _ -> None}};
             Kind_Arrow _ _ -> None}}};
       None -> None};
     None -> None};
   Ty_Forall x k t ->
    case kind_check (Cons (Pair x k) delta) t of {
     Some k0 ->
      case k0 of {
       Kind_Base -> Some Kind_Base;
       Kind_Arrow _ _ -> None};
     None -> None};
   Ty_Builtin d ->
    case kind_check_default_uni d of {
     Some k ->
      case k of {
       Kind_Base -> Some Kind_Base;
       Kind_Arrow _ _ -> None};
     None -> None};
   Ty_Lam x k1 t ->
    case kind_check (Cons (Pair x k1) delta) t of {
     Some k2 -> Some (Kind_Arrow k1 k2);
     None -> None};
   Ty_App t1 t2 ->
    let {o = kind_check delta t1} in
    let {o0 = kind_check delta t2} in
    case o of {
     Some k ->
      case k of {
       Kind_Base -> None;
       Kind_Arrow k11 k2 ->
        case o0 of {
         Some k12 ->
          case kind_eqb k11 k12 of {
           True -> Some k2;
           False -> None};
         None -> None}};
     None -> None};
   Ty_SOP _ -> None}

kind_checking_sound :: (List (Prod BinderTyname Kind)) -> Ty -> Kind ->
                       Has_kind
kind_checking_sound delta ty kind =
  ty_rec (\t delta0 kind0 _ -> K_Var delta0 t kind0)
    (\ty1 iHty1 ty2 iHty2 delta0 _ _ ->
    let {o = kind_check delta0 ty1} in
    case o of {
     Some k ->
      case k of {
       Kind_Base ->
        let {o0 = kind_check delta0 ty2} in
        case o0 of {
         Some k0 ->
          case k0 of {
           Kind_Base -> K_Fun delta0 ty1 ty2 (iHty1 delta0 Kind_Base __)
            (iHty2 delta0 Kind_Base __);
           Kind_Arrow _ _ -> false_rec};
         None -> false_rec};
       Kind_Arrow _ _ -> false_rec};
     None -> false_rec}) (\ty1 iHty1 ty2 iHty2 delta0 _ _ ->
    let {o = kind_check delta0 ty2} in
    case o of {
     Some k ->
      let {o0 = kind_check delta0 ty1} in
      case o0 of {
       Some k0 ->
        case k0 of {
         Kind_Base -> false_rec;
         Kind_Arrow k1 k2 ->
          case k1 of {
           Kind_Base -> false_rec;
           Kind_Arrow k3 k4 ->
            case k4 of {
             Kind_Base ->
              case k2 of {
               Kind_Base -> false_rec;
               Kind_Arrow k5 k6 ->
                case k6 of {
                 Kind_Base ->
                  let {b = andb (kind_eqb k k3) (kind_eqb k k5)} in
                  case b of {
                   True -> K_IFix delta0 ty1 ty2 k (iHty2 delta0 k __)
                    (iHty1 delta0 (Kind_Arrow (Kind_Arrow k Kind_Base)
                      (Kind_Arrow k Kind_Base)) __);
                   False -> false_rec};
                 Kind_Arrow _ _ -> false_rec}};
             Kind_Arrow _ _ -> false_rec}}};
       None -> false_rec};
     None -> false_rec}) (\b k ty0 iHty delta0 _ _ ->
    let {o = kind_check (Cons (Pair b k) delta0) ty0} in
    case o of {
     Some k0 ->
      case k0 of {
       Kind_Base -> K_Forall delta0 b k ty0
        (iHty (Cons (Pair b k) delta0) Kind_Base __);
       Kind_Arrow _ _ -> false_rec};
     None -> false_rec}) (\d delta0 _ _ ->
    let {o = kind_check_default_uni d} in
    case o of {
     Some k ->
      case k of {
       Kind_Base ->
        let {heqo = kind_checking_default_uni_sound d Kind_Base} in
        K_Builtin delta0 d heqo;
       Kind_Arrow _ _ -> false_rec};
     None -> false_rec}) (\b k ty0 iHty delta0 _ _ ->
    let {o = kind_check (Cons (Pair b k) delta0) ty0} in
    case o of {
     Some k0 -> K_Lam delta0 b k ty0 k0 (iHty (Cons (Pair b k) delta0) k0 __);
     None -> false_rec}) (\ty1 iHty1 ty2 iHty2 delta0 kind0 _ ->
    let {k1 = kind_check delta0 ty2} in
    case k1 of {
     Some k ->
      let {o = kind_check delta0 ty1} in
      case o of {
       Some k0 ->
        case k0 of {
         Kind_Base -> false_rec;
         Kind_Arrow k2 _ ->
          let {b = kind_eqb k2 k} in
          case b of {
           True -> K_App delta0 ty1 ty2 k kind0
            (iHty1 delta0 (Kind_Arrow k kind0) __) (iHty2 delta0 k __);
           False -> false_rec}};
       None -> false_rec};
     None -> false_rec}) (\_ _ _ _ -> false_rec) ty delta kind __

data Step =
   Step_beta String Kind Ty Ty
 | Step_appL Ty Ty Ty Step
 | Step_appR Ty Ty Ty Step
 | Step_funL Ty Ty Ty Step
 | Step_funR Ty Ty Ty Step
 | Step_forall BinderTyname Kind Ty Ty Step
 | Step_abs BinderTyname Kind Ty Ty Step
 | Step_ifixL Ty Ty Ty Step
 | Step_ifixR Ty Ty Ty Step
 | Step_SOP (List (List Ty)) (List Ty) Ty Ty (List Ty) (List (List Ty)) 
 (ForallSet2 Ty ()) (ForallSet Ty ()) Step

step_rect :: (String -> Kind -> Ty -> Ty -> () -> () -> a1) -> (Ty -> Ty ->
             Ty -> Step -> a1 -> a1) -> (Ty -> Ty -> Ty -> () -> Step -> a1
             -> a1) -> (Ty -> Ty -> Ty -> Step -> a1 -> a1) -> (Ty -> Ty ->
             Ty -> () -> Step -> a1 -> a1) -> (BinderTyname -> Kind -> Ty ->
             Ty -> Step -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> Ty ->
             Step -> a1 -> a1) -> (Ty -> Ty -> Ty -> Step -> a1 -> a1) -> (Ty
             -> Ty -> Ty -> () -> Step -> a1 -> a1) -> ((List (List Ty)) ->
             (List Ty) -> Ty -> Ty -> (List Ty) -> (List (List Ty)) ->
             (ForallSet2 Ty ()) -> (ForallSet Ty ()) -> Step -> a1 -> a1) ->
             Ty -> Ty -> Step -> a1
step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 _ _ s =
  case s of {
   Step_beta x k s0 t -> f x k s0 t __ __;
   Step_appL s1 s2 t s0 ->
    f0 s1 s2 t s0 (step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 s1 s2 s0);
   Step_appR s0 t1 t2 s1 ->
    f1 s0 t1 t2 __ s1 (step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 t1 t2 s1);
   Step_funL s1 s2 t s0 ->
    f2 s1 s2 t s0 (step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 s1 s2 s0);
   Step_funR s0 t1 t2 s1 ->
    f3 s0 t1 t2 __ s1 (step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 t1 t2 s1);
   Step_forall bX k s1 s2 s0 ->
    f4 bX k s1 s2 s0 (step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 s1 s2 s0);
   Step_abs bX k t1 t2 s0 ->
    f5 bX k t1 t2 s0 (step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 t1 t2 s0);
   Step_ifixL f9 f10 t s0 ->
    f6 f9 f10 t s0 (step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s0);
   Step_ifixR f9 t1 t2 s0 ->
    f7 f9 t1 t2 __ s0 (step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 t1 t2 s0);
   Step_SOP tss_normal tss_sub_normal tss_sub1 tss_sub2 tss_sub_remainder
    tss_remainder f9 f10 s0 ->
    f8 tss_normal tss_sub_normal tss_sub1 tss_sub2 tss_sub_remainder
      tss_remainder f9 f10 s0
      (step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 tss_sub1 tss_sub2 s0)}

step_rec :: (String -> Kind -> Ty -> Ty -> () -> () -> a1) -> (Ty -> Ty -> Ty
            -> Step -> a1 -> a1) -> (Ty -> Ty -> Ty -> () -> Step -> a1 ->
            a1) -> (Ty -> Ty -> Ty -> Step -> a1 -> a1) -> (Ty -> Ty -> Ty ->
            () -> Step -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> Ty ->
            Step -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> Ty -> Step ->
            a1 -> a1) -> (Ty -> Ty -> Ty -> Step -> a1 -> a1) -> (Ty -> Ty ->
            Ty -> () -> Step -> a1 -> a1) -> ((List (List Ty)) -> (List 
            Ty) -> Ty -> Ty -> (List Ty) -> (List (List Ty)) -> (ForallSet2
            Ty ()) -> (ForallSet Ty ()) -> Step -> a1 -> a1) -> Ty -> Ty ->
            Step -> a1
step_rec =
  step_rect

bind :: (Option a1) -> (a1 -> Option a2) -> Option a2
bind xx f =
  case xx of {
   Some a -> f a;
   None -> None}

substituteTCA_preserves_kinding :: Ty -> (List (Prod BinderName Kind)) ->
                                   BinderName -> Kind -> Ty -> Kind ->
                                   Has_kind -> Has_kind -> Has_kind
substituteTCA_preserves_kinding =
  Prelude.error "AXIOM TO BE REALIZED"

step_dec :: Ty -> (List (Prod BinderName Kind)) -> Kind -> Has_kind -> Sum
            (SigT Ty Step) ()
step_dec t =
  ty_rec (\_ _ _ _ -> Inr __) (\t1 iHT1 t2 iHT2 _UU0394_ _ _ ->
    let {o = kind_check _UU0394_ t1} in
    case o of {
     Some k ->
      case k of {
       Kind_Base ->
        let {o0 = kind_check _UU0394_ t2} in
        case o0 of {
         Some k0 ->
          case k0 of {
           Kind_Base ->
            let {heqo = kind_checking_sound _UU0394_ t1 Kind_Base} in
            let {heqo0 = kind_checking_sound _UU0394_ t2 Kind_Base} in
            let {s = iHT1 _UU0394_ Kind_Base heqo} in
            case s of {
             Inl s0 -> Inl
              (case s0 of {
                ExistT x s1 -> ExistT (Ty_Fun x t2) (Step_funL t1 x t2 s1)});
             Inr _ ->
              let {s0 = iHT2 _UU0394_ Kind_Base heqo0} in
              case s0 of {
               Inl s1 -> Inl
                (case s1 of {
                  ExistT x s2 -> ExistT (Ty_Fun t1 x) (Step_funR t1 t2 x s2)});
               Inr _ -> Inr __}};
           Kind_Arrow _ _ -> false_rec};
         None -> false_rec};
       Kind_Arrow _ _ -> false_rec};
     None -> false_rec}) (\t1 iHT1 t2 iHT2 _UU0394_ _ _ ->
    let {o = kind_check _UU0394_ t2} in
    case o of {
     Some k ->
      let {o0 = kind_check _UU0394_ t1} in
      case o0 of {
       Some k0 ->
        case k0 of {
         Kind_Base -> false_rec;
         Kind_Arrow k1 k2 ->
          case k1 of {
           Kind_Base -> false_rec;
           Kind_Arrow k3 k4 ->
            case k4 of {
             Kind_Base ->
              case k2 of {
               Kind_Base -> false_rec;
               Kind_Arrow k5 k6 ->
                case k6 of {
                 Kind_Base ->
                  let {b = andb (kind_eqb k k3) (kind_eqb k k5)} in
                  case b of {
                   True ->
                    let {heqo = kind_checking_sound _UU0394_ t2 k} in
                    let {
                     heqo0 = kind_checking_sound _UU0394_ t1 (Kind_Arrow
                               (Kind_Arrow k3 Kind_Base) (Kind_Arrow k5
                               Kind_Base))}
                    in
                    let {
                     s = iHT1 _UU0394_ (Kind_Arrow (Kind_Arrow k3 Kind_Base)
                           (Kind_Arrow k5 Kind_Base)) heqo0}
                    in
                    case s of {
                     Inl s0 -> Inl
                      (case s0 of {
                        ExistT x s1 -> ExistT (Ty_IFix x t2) (Step_ifixL t1 x
                         t2 s1)});
                     Inr _ ->
                      let {s0 = iHT2 _UU0394_ k heqo} in
                      case s0 of {
                       Inl s1 -> Inl
                        (case s1 of {
                          ExistT x s2 -> ExistT (Ty_IFix t1 x) (Step_ifixR t1
                           t2 x s2)});
                       Inr _ -> Inr __}};
                   False -> false_rec};
                 Kind_Arrow _ _ -> false_rec}};
             Kind_Arrow _ _ -> false_rec}}};
       None -> false_rec};
     None -> false_rec}) (\b k t0 iHT _UU0394_ _ _ ->
    let {o = kind_check (Cons (Pair b k) _UU0394_) t0} in
    case o of {
     Some k0 ->
      case k0 of {
       Kind_Base ->
        let {
         heqo = kind_checking_sound (Cons (Pair b k) _UU0394_) t0 Kind_Base}
        in
        let {s = iHT (Cons (Pair b k) _UU0394_) Kind_Base heqo} in
        case s of {
         Inl s0 -> Inl
          (case s0 of {
            ExistT x s1 -> ExistT (Ty_Forall b k x) (Step_forall b k t0 x s1)});
         Inr _ -> Inr __};
       Kind_Arrow _ _ -> false_rec};
     None -> false_rec}) (\_ _ _ _ -> Inr __) (\b k t0 iHT _UU0394_ _ _ ->
    let {o = kind_check (Cons (Pair b k) _UU0394_) t0} in
    case o of {
     Some k0 ->
      let {heqo = kind_checking_sound (Cons (Pair b k) _UU0394_) t0 k0} in
      let {s = iHT (Cons (Pair b k) _UU0394_) k0 heqo} in
      case s of {
       Inl s0 -> Inl
        (case s0 of {
          ExistT x s1 -> ExistT (Ty_Lam b k x) (Step_abs b k t0 x s1)});
       Inr _ -> Inr __};
     None -> false_rec}) (\t1 iHT1 t2 iHT2 _UU0394_ _ _ ->
    let {o = kind_check _UU0394_ t1} in
    case o of {
     Some k ->
      case k of {
       Kind_Base -> false_rec;
       Kind_Arrow k0 k1 ->
        let {o0 = kind_check _UU0394_ t2} in
        case o0 of {
         Some k2 ->
          let {b = kind_eqb k0 k2} in
          case b of {
           True ->
            let {heqo = kind_checking_sound _UU0394_ t1 (Kind_Arrow k0 k1)}
            in
            let {s = iHT1 _UU0394_ (Kind_Arrow k0 k1) heqo} in
            case s of {
             Inl s0 -> Inl
              (case s0 of {
                ExistT x s1 -> ExistT (Ty_App x t2) (Step_appL t1 x t2 s1)});
             Inr _ ->
              let {o1 = kind_check _UU0394_ t1} in
              case o1 of {
               Some k3 ->
                case k3 of {
                 Kind_Base -> false_rec;
                 Kind_Arrow k4 _ ->
                  let {o2 = kind_check _UU0394_ t2} in
                  case o2 of {
                   Some k5 ->
                    let {b0 = kind_eqb k4 k5} in
                    case b0 of {
                     True ->
                      let {heqo2 = kind_checking_sound _UU0394_ t2 k5} in
                      let {s0 = iHT2 _UU0394_ k5 heqo2} in
                      case s0 of {
                       Inl s1 -> Inl
                        (case s1 of {
                          ExistT x s2 -> ExistT (Ty_App t1 x) (Step_appR t1
                           t2 x s2)});
                       Inr _ ->
                        ty_rec (\_ _ _ _ _ _ _ -> Inr __)
                          (\_ _ _ _ _ _ _ _ _ _ -> false_rec)
                          (\_ _ _ _ _ _ _ _ _ _ -> false_rec)
                          (\_ _ _ _ _ _ _ _ _ _ -> false_rec)
                          (\_ _ _ _ _ _ _ -> false_rec)
                          (\b1 k6 t3 _ _ _ _ _ _ _ -> Inl (ExistT
                          (substituteTCA b1 t2 t3) (Step_beta b1 k6 t3 t2)))
                          (\_ _ _ _ _ _ _ _ _ _ -> Inr __)
                          (\l _ _ _ heqo0 _ _ ->
                          case heqo0 of {
                           K_Var _UU0394_0 _ _ ->
                            eq_rec_r _UU0394_ (\_ -> false_rec) _UU0394_0 __
                              __ __;
                           K_Fun _UU0394_0 _ _ x x0 ->
                            eq_rec_r _UU0394_ (\_ -> false_rec) _UU0394_0 __
                              __ x x0;
                           K_IFix _UU0394_0 _ _ _ x x0 ->
                            eq_rec_r _UU0394_ (\_ -> false_rec) _UU0394_0 __
                              __ x x0;
                           K_Forall _UU0394_0 _ _ _ x ->
                            eq_rec_r _UU0394_ (\_ -> false_rec) _UU0394_0 __
                              __ x;
                           K_Builtin _UU0394_0 _ x ->
                            eq_rec_r _UU0394_ (\_ -> false_rec) _UU0394_0 __
                              __ x;
                           K_Lam _UU0394_0 _ _ _ _ x ->
                            eq_rec_r _UU0394_ (\_ -> false_rec) _UU0394_0 __
                              __ x;
                           K_App _UU0394_0 _ _ _ _ x x0 ->
                            eq_rec_r _UU0394_ (\_ -> false_rec) _UU0394_0 __
                              __ x x0;
                           K_SOP _UU0394_0 tss x ->
                            eq_rec_r _UU0394_ (\_ ->
                              eq_rec_r l (\_ -> false_rec) tss) _UU0394_0 __
                              __ x}) t1 iHT1 __ __ heqo __ __};
                     False -> false_rec};
                   None -> false_rec}};
               None -> false_rec}};
           False -> false_rec};
         None -> false_rec}};
     None -> false_rec}) (\_ _ _ _ -> Inr __) t

step_preserves_kinding_SOP_axiom :: (List (List Ty)) -> (List
                                    (Prod BinderName Kind)) -> Has_kind
step_preserves_kinding_SOP_axiom =
  Prelude.error "AXIOM TO BE REALIZED"

step_preserves_kinding :: Ty -> Ty -> (List (Prod BinderName Kind)) -> Kind
                          -> Has_kind -> Step -> Has_kind
step_preserves_kinding t t' _UU0394_ k x x0 =
  step_rec (\x1 k0 s t0 _ _ _UU0394_0 k1 hkind_T ->
    case hkind_T of {
     K_Var _UU0394_1 _ _ ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ __;
     K_Fun _UU0394_1 _ _ x2 x3 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x2 x3;
     K_IFix _UU0394_1 _ _ _ x2 x3 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x2 x3;
     K_Forall _UU0394_1 _ _ _ x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x2;
     K_Builtin _UU0394_1 _ x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x2;
     K_Lam _UU0394_1 _ _ _ _ x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x2;
     K_App _UU0394_1 t1 t2 k2 k3 x2 x3 ->
      eq_rec_r _UU0394_0 (\_ ->
        eq_rec_r (Ty_Lam x1 k0 s) (\_ ->
          eq_rec_r t0 (\_ ->
            eq_rec_r k1 (\h2 h4 ->
              case h2 of {
               K_Var _UU0394_2 _ _ ->
                eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_2 __ __ __;
               K_Fun _UU0394_2 _ _ x4 x5 ->
                eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_2 __ __ x4 x5;
               K_IFix _UU0394_2 _ _ _ x4 x5 ->
                eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_2 __ __ x4 x5;
               K_Forall _UU0394_2 _ _ _ x4 ->
                eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_2 __ __ x4;
               K_Builtin _UU0394_2 _ x4 ->
                eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_2 __ __ x4;
               K_Lam _UU0394_2 x4 k4 t3 k5 x5 ->
                eq_rec_r _UU0394_0 (\_ ->
                  eq_rec_r x1 (\_ ->
                    eq_rec_r k0 (\_ ->
                      eq_rec_r s (\_ ->
                        eq_rec_r k2 (\_ ->
                          eq_rec_r k1 (\h1 ->
                            eq_rec_r k2 (\_ _ ->
                              substituteTCA_preserves_kinding s _UU0394_0 x1
                                k1 t0 k2 h1 h4) k0 hkind_T h2) k5) k0 __) t3)
                      k4) x4 __ __) _UU0394_2 __ __ x5;
               K_App _UU0394_2 _ _ _ _ x4 x5 ->
                eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_2 __ __ x4 x5;
               K_SOP _UU0394_2 _ x4 ->
                eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_2 __ __ x4}) k3)
            t2) t1 __) _UU0394_1 __ __ x2 x3;
     K_SOP _UU0394_1 _ x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x2})
    (\s1 s2 t0 _ iHstep _UU0394_0 k0 hkind_T ->
    case hkind_T of {
     K_Var _UU0394_1 _ _ ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ __;
     K_Fun _UU0394_1 _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_IFix _UU0394_1 _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_Forall _UU0394_1 _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Builtin _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Lam _UU0394_1 _ _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_App _UU0394_1 t1 t2 k1 k2 x1 x2 ->
      eq_rec_r _UU0394_0 (\_ ->
        eq_rec_r s1 (\_ ->
          eq_rec_r t0 (\_ ->
            eq_rec_r k0 (\h3 h5 -> K_App _UU0394_0 s2 t0 k1 k0
              (iHstep _UU0394_0 (Kind_Arrow k1 k0) h3) h5) k2) t2) t1 __)
        _UU0394_1 __ __ x1 x2;
     K_SOP _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1})
    (\s t1 t2 _ _ iHstep _UU0394_0 k0 hkind_T ->
    case hkind_T of {
     K_Var _UU0394_1 _ _ ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ __;
     K_Fun _UU0394_1 _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_IFix _UU0394_1 _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_Forall _UU0394_1 _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Builtin _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Lam _UU0394_1 _ _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_App _UU0394_1 t3 t4 k1 k2 x1 x2 ->
      eq_rec_r _UU0394_0 (\_ ->
        eq_rec_r s (\_ ->
          eq_rec_r t1 (\_ ->
            eq_rec_r k0 (\h3 h5 -> K_App _UU0394_0 s t2 k1 k0 h3
              (iHstep _UU0394_0 k1 h5)) k2) t4) t3 __) _UU0394_1 __ __ x1 x2;
     K_SOP _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1})
    (\s1 s2 t0 _ iHstep _UU0394_0 _ hkind_T ->
    case hkind_T of {
     K_Var _UU0394_1 _ _ ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ __;
     K_Fun _UU0394_1 t1 t2 x1 x2 ->
      eq_rec_r _UU0394_0 (\_ ->
        eq_rec_r s1 (\_ ->
          eq_rec_r t0 (\_ h3 h5 -> K_Fun _UU0394_0 s2 t0
            (iHstep _UU0394_0 Kind_Base h3) h5) t2) t1 __) _UU0394_1 __ __ x1
        x2;
     K_IFix _UU0394_1 _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_Forall _UU0394_1 _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Builtin _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Lam _UU0394_1 _ _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_App _UU0394_1 _ _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_SOP _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1})
    (\s t1 t2 _ _ iHstep _UU0394_0 _ hkind_T ->
    case hkind_T of {
     K_Var _UU0394_1 _ _ ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ __;
     K_Fun _UU0394_1 t3 t4 x1 x2 ->
      eq_rec_r _UU0394_0 (\_ ->
        eq_rec_r s (\_ ->
          eq_rec_r t1 (\_ h3 h5 -> K_Fun _UU0394_0 s t2 h3
            (iHstep _UU0394_0 Kind_Base h5)) t4) t3 __) _UU0394_1 __ __ x1 x2;
     K_IFix _UU0394_1 _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_Forall _UU0394_1 _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Builtin _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Lam _UU0394_1 _ _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_App _UU0394_1 _ _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_SOP _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1})
    (\bX k0 s1 s2 _ iHstep _UU0394_0 _ hkind_T ->
    case hkind_T of {
     K_Var _UU0394_1 _ _ ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ __;
     K_Fun _UU0394_1 _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_IFix _UU0394_1 _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_Forall _UU0394_1 x1 k1 t0 x2 ->
      eq_rec_r _UU0394_0 (\_ ->
        eq_rec_r bX (\_ ->
          eq_rec_r k0 (\_ ->
            eq_rec_r s1 (\_ h5 -> K_Forall _UU0394_0 bX k0 s2
              (iHstep (Cons (Pair bX k0) _UU0394_0) Kind_Base h5)) t0) k1) x1
          __ __) _UU0394_1 __ __ x2;
     K_Builtin _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Lam _UU0394_1 _ _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_App _UU0394_1 _ _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_SOP _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1})
    (\bX k0 t1 t2 _ iHstep _UU0394_0 _ hkind_T ->
    case hkind_T of {
     K_Var _UU0394_1 _ _ ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ __;
     K_Fun _UU0394_1 _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_IFix _UU0394_1 _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_Forall _UU0394_1 _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Builtin _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Lam _UU0394_1 x1 k1 t0 k2 x2 ->
      eq_rec_r _UU0394_0 (\_ ->
        eq_rec_r bX (\_ ->
          eq_rec_r k0 (\_ ->
            eq_rec_r t1 (\_ h5 -> K_Lam _UU0394_0 bX k0 t2 k2
              (iHstep (Cons (Pair bX k0) _UU0394_0) k2 h5)) t0) k1) x1 __ __)
        _UU0394_1 __ __ x2;
     K_App _UU0394_1 _ _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_SOP _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1})
    (\f1 f2 t0 _ iHstep _UU0394_0 _ hkind_T ->
    case hkind_T of {
     K_Var _UU0394_1 _ _ ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ __;
     K_Fun _UU0394_1 _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_IFix _UU0394_1 f t1 k0 x1 x2 ->
      eq_rec_r _UU0394_0 (\_ ->
        eq_rec_r f1 (\_ ->
          eq_rec_r t0 (\_ h3 h5 -> K_IFix _UU0394_0 f2 t0 k0 h3
            (iHstep _UU0394_0 (Kind_Arrow (Kind_Arrow k0 Kind_Base)
              (Kind_Arrow k0 Kind_Base)) h5)) t1) f __) _UU0394_1 __ __ x1 x2;
     K_Forall _UU0394_1 _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Builtin _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Lam _UU0394_1 _ _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_App _UU0394_1 _ _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_SOP _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1})
    (\f t1 t2 _ _ iHstep _UU0394_0 _ hkind_T ->
    case hkind_T of {
     K_Var _UU0394_1 _ _ ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ __;
     K_Fun _UU0394_1 _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_IFix _UU0394_1 f0 t0 k0 x1 x2 ->
      eq_rec_r _UU0394_0 (\_ ->
        eq_rec_r f (\_ ->
          eq_rec_r t1 (\_ h3 h5 -> K_IFix _UU0394_0 f t2 k0
            (iHstep _UU0394_0 k0 h3) h5) t0) f0 __) _UU0394_1 __ __ x1 x2;
     K_Forall _UU0394_1 _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Builtin _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Lam _UU0394_1 _ _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_App _UU0394_1 _ _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_SOP _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1})
    (\tss_normal tss_sub_normal tss_sub1 tss_sub2 tss_sub_remainder tss_remainder _ _ _ _ _UU0394_0 _ hkind_T ->
    case hkind_T of {
     K_Var _UU0394_1 _ _ ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ __;
     K_Fun _UU0394_1 _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_IFix _UU0394_1 _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_Forall _UU0394_1 _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Builtin _UU0394_1 _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_Lam _UU0394_1 _ _ _ _ x1 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1;
     K_App _UU0394_1 _ _ _ _ x1 x2 ->
      eq_rec_r _UU0394_0 (\_ -> false_rec) _UU0394_1 __ __ x1 x2;
     K_SOP _UU0394_1 tss x1 ->
      eq_rec_r _UU0394_0 (\_ ->
        eq_rec_r
          (app tss_normal (Cons
            (app tss_sub_normal (Cons tss_sub1 tss_sub_remainder))
            tss_remainder)) (\_ _ ->
          step_preserves_kinding_SOP_axiom
            (app tss_normal (Cons
              (app tss_sub_normal (Cons tss_sub2 tss_sub_remainder))
              tss_remainder)) _UU0394_0) tss) _UU0394_1 __ __ x1}) t t' x0
    _UU0394_ k x

normaliser_gas :: Nat -> Ty -> (List (Prod BinderName Kind)) -> Kind ->
                  Has_kind -> Ty
normaliser_gas n t _UU0394_ k hwk =
  case n of {
   O -> t;
   S n' ->
    case step_dec t _UU0394_ k hwk of {
     Inl s ->
      case s of {
       ExistT t' p ->
        let {hwk' = step_preserves_kinding t t' _UU0394_ k hwk p} in
        normaliser_gas n' t' _UU0394_ k hwk'};
     Inr _ -> t}}

normaliser :: Ty -> (List (Prod BinderName Kind)) -> Kind -> Has_kind -> Ty
normaliser t _UU0394_ k hwk =
  normaliser_gas (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    t _UU0394_ k hwk

normaliser_Jacco :: (List (Prod BinderTyname Kind)) -> Ty -> Option Ty
normaliser_Jacco _UU0394_ t =
  case kind_check _UU0394_ t of {
   Some k -> Some
    (normaliser t _UU0394_ k (kind_checking_sound _UU0394_ t k));
   None -> None}

map_normaliser :: (List (Prod (Prod String Ty) (List (Prod String Kind)))) ->
                  Option (List (Prod String Ty))
map_normaliser xs =
  case xs of {
   Nil -> Some Nil;
   Cons p xs' ->
    case p of {
     Pair p0 _UU0394_ ->
      case p0 of {
       Pair x t ->
        bind (normaliser_Jacco _UU0394_ t) (\tn ->
          bind (map_normaliser xs') (\xs'' -> Some (Cons (Pair x tn) xs'')))}}}

bvc :: Vdecl -> Name
bvc c =
  case c of {
   VarDecl x _ -> x}

bvb :: Binding -> List BinderName
bvb b =
  case b of {
   TermBind _ v _ -> case v of {
                      VarDecl x _ -> Cons x Nil};
   TypeBind _ _ -> Nil;
   DatatypeBind d ->
    case d of {
     Datatype _ _ matchFunc cs -> Cons matchFunc (rev (map bvc cs))}}

bvbs :: (List Binding) -> List Name
bvbs bs =
  concat (map bvb bs)

btvb :: Binding -> List Tyname
btvb b =
  case b of {
   TermBind _ _ _ -> Nil;
   TypeBind t _ -> case t of {
                    TyVarDecl x _ -> Cons x Nil};
   DatatypeBind d ->
    case d of {
     Datatype t _ _ _ -> case t of {
                          TyVarDecl x _ -> Cons x Nil}}}

btvbs :: (List Binding) -> List Tyname
btvbs bs =
  concat (map btvb bs)

ftv0 :: Ty -> List String
ftv0 t =
  case t of {
   Ty_Var x -> Cons x Nil;
   Ty_Fun t1 t2 -> app (ftv0 t1) (ftv0 t2);
   Ty_IFix f t0 -> app (ftv0 f) (ftv0 t0);
   Ty_Forall x _ t' -> remove string_dec x (ftv0 t');
   Ty_Builtin _ -> Nil;
   Ty_Lam x _ t' -> remove string_dec x (ftv0 t');
   Ty_App t1 t2 -> app (ftv0 t1) (ftv0 t2);
   Ty_SOP tss -> flatmap2 ftv0 tss}

getTyname :: Tvdecl -> BinderTyname
getTyname tvd =
  case tvd of {
   TyVarDecl x _ -> x}

getKind :: Tvdecl -> Kind
getKind tvd =
  case tvd of {
   TyVarDecl _ k -> k}

ty_Apps :: Ty -> (List Ty) -> Ty
ty_Apps f xs =
  fold_left (\x x0 -> Ty_App x x0) xs f

ty_Foralls :: (List Tvdecl) -> Ty -> Ty
ty_Foralls xs t =
  fold_right (\yK t' -> Ty_Forall (getTyname yK) (getKind yK) t') t xs

replaceRetTy :: Ty -> Ty -> Ty
replaceRetTy t r =
  case t of {
   Ty_Fun s1 s2 -> Ty_Fun s1 (replaceRetTy s2 r);
   _ -> r}

dtdecl_freshR :: Dtdecl -> String
dtdecl_freshR d =
  case d of {
   Datatype _ _ _ cs ->
    concat0 EmptyString (concat (map (\c -> ftv0 (vdecl_ty c)) cs))}

constrLastTyExpected :: Dtdecl -> Ty
constrLastTyExpected dtd =
  case dtd of {
   Datatype xK yKs _ _ ->
    let {x = tvdecl_name xK} in
    let {ys = map tvdecl_name yKs} in
    ty_Apps (Ty_Var x) (map (\x0 -> Ty_Var x0) ys)}

matchTy :: Dtdecl -> Ty
matchTy d =
  let {r = dtdecl_freshR d} in
  case d of {
   Datatype _ yKs _ cs ->
    let {branchTypes = map (\c -> replaceRetTy (vdecl_ty c) (Ty_Var r)) cs}
    in
    let {
     branchTypesFolded = fold_right (\x x0 -> Ty_Fun x x0) (Ty_Var r)
                           branchTypes}
    in
    ty_Foralls yKs (Ty_Fun (constrLastTyExpected d) (Ty_Forall r Kind_Base
      branchTypesFolded))}

constrTy :: Dtdecl -> Vdecl -> Ty
constrTy d c =
  case d of {
   Datatype _ yKs _ _ -> case c of {
                          VarDecl _ t -> ty_Foralls yKs t}}

constrBind :: Dtdecl -> Vdecl -> Prod String Ty
constrBind d c =
  case c of {
   VarDecl x _ -> Pair x (constrTy d c)}

constrBinds :: Dtdecl -> List (Prod String Ty)
constrBinds d =
  case d of {
   Datatype _ _ _ cs -> rev (map (constrBind d) cs)}

matchBind :: Dtdecl -> Prod String Ty
matchBind d =
  case d of {
   Datatype _ _ matchFunc _ -> Pair matchFunc (matchTy d)}

binds_Delta :: Binding -> List (Prod String Kind)
binds_Delta b =
  case b of {
   TermBind _ _ _ -> Nil;
   TypeBind t _ -> case t of {
                    TyVarDecl x k -> Cons (Pair x k) Nil};
   DatatypeBind d ->
    case d of {
     Datatype t _ _ _ -> case t of {
                          TyVarDecl x k -> Cons (Pair x k) Nil}}}

binds_Gamma :: Binding -> List (Prod String Ty)
binds_Gamma b =
  case b of {
   TermBind _ v _ -> case v of {
                      VarDecl x t -> Cons (Pair x t) Nil};
   TypeBind _ _ -> Nil;
   DatatypeBind d ->
    let {constrBs = constrBinds d} in
    let {matchB = matchBind d} in Cons matchB constrBs}

data Builtin_sig =
   BS_Forall String Kind Builtin_sig
 | BS_Fun Ty Builtin_sig
 | BS_Result Ty

to_ty :: Builtin_sig -> Ty
to_ty s =
  case s of {
   BS_Forall x k s0 -> Ty_Forall x k (to_ty s0);
   BS_Fun t s0 -> Ty_Fun t (to_ty s0);
   BS_Result t -> t}

to_sig :: DefaultFun -> Builtin_sig
to_sig f =
  case f of {
   AddInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun (Ty_Builtin
    DefaultUniInteger) (BS_Result (Ty_Builtin DefaultUniInteger)));
   SubtractInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun
    (Ty_Builtin DefaultUniInteger) (BS_Result (Ty_Builtin
    DefaultUniInteger)));
   MultiplyInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun
    (Ty_Builtin DefaultUniInteger) (BS_Result (Ty_Builtin
    DefaultUniInteger)));
   DivideInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun (Ty_Builtin
    DefaultUniInteger) (BS_Result (Ty_Builtin DefaultUniInteger)));
   QuotientInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun
    (Ty_Builtin DefaultUniInteger) (BS_Result (Ty_Builtin
    DefaultUniInteger)));
   EqualsInteger -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Fun (Ty_Builtin
    DefaultUniInteger) (BS_Result (Ty_Builtin DefaultUniBool)));
   AppendByteString -> BS_Fun (Ty_Builtin DefaultUniByteString) (BS_Fun
    (Ty_Builtin DefaultUniByteString) (BS_Result (Ty_Builtin
    DefaultUniByteString)));
   IfThenElse -> BS_Forall (String0 (Ascii True False False False False False
    True False) EmptyString) Kind_Base (BS_Fun (Ty_Builtin DefaultUniBool)
    (BS_Fun (Ty_Var (String0 (Ascii True False False False False False True
    False) EmptyString)) (BS_Fun (Ty_Var (String0 (Ascii True False False
    False False False True False) EmptyString)) (BS_Result (Ty_Var (String0
    (Ascii True False False False False False True False) EmptyString))))));
   _ -> BS_Fun (Ty_Builtin DefaultUniInteger) (BS_Result (Ty_Builtin
    DefaultUniInteger))}

lookupBuiltinTy :: DefaultFun -> Ty
lookupBuiltinTy f =
  to_ty (to_sig f)

flatten :: (List (List a1)) -> List a1
flatten l =
  concat (rev l)

fromDecl :: Tvdecl -> Prod String Kind
fromDecl tvd =
  case tvd of {
   TyVarDecl v k -> Pair v k}

freshUnwrapIFix :: Ty -> String
freshUnwrapIFix f =
  append (String0 (Ascii True False False False False True True False)
    EmptyString) (concat0 EmptyString (ftv0 f))

unwrapIFixFresh :: Ty -> Kind -> Ty -> Ty
unwrapIFixFresh f k t =
  let {b = freshUnwrapIFix f} in
  Ty_App (Ty_App f (Ty_Lam b k (Ty_IFix f (Ty_Var b)))) t

insert_deltas_rec :: (List (Prod String Ty)) -> (List (Prod String Kind)) ->
                     List (Prod (Prod String Ty) (List (Prod String Kind)))
insert_deltas_rec xs _UU0394_ =
  case xs of {
   Nil -> Nil;
   Cons p xs' -> Cons (Pair p _UU0394_) (insert_deltas_rec xs' _UU0394_)}

insert_deltas_bind_Gamma_nr :: (List Binding) -> (List
                               (Prod BinderTyname Kind)) -> List
                               (Prod (Prod BinderName Ty)
                               (List (Prod BinderTyname Kind)))
insert_deltas_bind_Gamma_nr bs _UU0394_ =
  case bs of {
   Nil -> Nil;
   Cons b bs' ->
    app (insert_deltas_bind_Gamma_nr bs' (app (binds_Delta b) _UU0394_))
      (insert_deltas_rec (binds_Gamma b) (app (binds_Delta b) _UU0394_))}

allbmap :: (a1 -> Bool) -> (List a1) -> Bool
allbmap f bs =
  case bs of {
   Nil -> True;
   Cons b bs0 -> andb (f b) (allbmap f bs0)}

no_dup_fun :: (List String) -> Bool
no_dup_fun xs =
  case xs of {
   Nil -> True;
   Cons x xs0 ->
    case in_dec string_dec x xs0 of {
     Left -> False;
     Right -> no_dup_fun xs0}}

is_KindBase :: (Option Kind) -> Bool
is_KindBase k =
  case k of {
   Some k0 -> case k0 of {
               Kind_Base -> True;
               Kind_Arrow _ _ -> False};
   None -> False}

constructor_well_formed_check :: (List (Prod BinderTyname Kind)) -> Vdecl ->
                                 Ty -> Bool
constructor_well_formed_check _UU0394_ v tr =
  case v of {
   VarDecl _ t ->
    case splitTy t of {
     Pair targs tr' ->
      andb (ty_eqb tr tr')
        (allbmap (\u -> is_KindBase (kind_check _UU0394_ u)) targs)}}

binding_well_formed_check :: ((List (Prod BinderTyname Kind)) -> (List
                             (Prod BinderName Ty)) -> Term -> Option 
                             Ty) -> (List (Prod BinderTyname Kind)) -> (List
                             (Prod BinderName Ty)) -> Recursivity -> Binding
                             -> Bool
binding_well_formed_check type_check' _UU0394_ _UU0393_ rec0 binding =
  case binding of {
   TermBind _ v t ->
    case v of {
     VarDecl _ t0 ->
      case kind_check _UU0394_ t0 of {
       Some k ->
        case k of {
         Kind_Base ->
          case type_check' _UU0394_ _UU0393_ t of {
           Some tn ->
            case normaliser_Jacco _UU0394_ t0 of {
             Some tn' -> ty_eqb tn tn';
             None -> False};
           None -> False};
         Kind_Arrow _ _ -> False};
       None -> False}};
   TypeBind t t0 ->
    case t of {
     TyVarDecl _ k ->
      case kind_check _UU0394_ t0 of {
       Some k' -> kind_eqb k k';
       None -> False}};
   DatatypeBind d ->
    case d of {
     Datatype xK yKs matchFunc cs ->
      let {dtd = Datatype xK yKs matchFunc cs} in
      let {x = tvdecl_name xK} in
      let {ys = map tvdecl_name yKs} in
      case andb (no_dup_fun (Cons x ys)) (no_dup_fun (map vdecl_name cs)) of {
       True ->
        let {_UU0394_' = app (rev (map fromDecl yKs)) _UU0394_} in
        let {tres = constrLastTyExpected dtd} in
        andb
          (allbmap (\c -> constructor_well_formed_check _UU0394_' c tres) cs)
          (case rec0 of {
            NonRec ->
             case kind_check (Cons (fromDecl xK) _UU0394_') tres of {
              Some k ->
               case k of {
                Kind_Base -> True;
                Kind_Arrow _ _ -> False};
              None -> False};
            Rec ->
             case kind_check _UU0394_' tres of {
              Some k ->
               case k of {
                Kind_Base -> True;
                Kind_Arrow _ _ -> False};
              None -> False}});
       False -> False}}}

bindings_well_formed_nonrec_check :: ((List (Prod BinderTyname Kind)) ->
                                     (List (Prod BinderName Ty)) ->
                                     Recursivity -> Binding -> Bool) -> (List
                                     (Prod BinderTyname Kind)) -> (List
                                     (Prod BinderName Ty)) -> (List Binding)
                                     -> Bool
bindings_well_formed_nonrec_check b_wf _UU0394_ _UU0393_ bs =
  case bs of {
   Nil -> True;
   Cons b bs' ->
    case map_normaliser
           (insert_deltas_rec (binds_Gamma b) (app (binds_Delta b) _UU0394_)) of {
     Some bsGn ->
      andb (b_wf _UU0394_ _UU0393_ NonRec b)
        (bindings_well_formed_nonrec_check b_wf
          (app (binds_Delta b) _UU0394_) (app bsGn _UU0393_) bs');
     None -> False}}

bindings_well_formed_rec_check :: (Binding -> Bool) -> (List Binding) -> Bool
bindings_well_formed_rec_check b_wf bs =
  case bs of {
   Nil -> True;
   Cons b bs' -> andb (b_wf b) (bindings_well_formed_rec_check b_wf bs')}

type_check :: (List (Prod BinderTyname Kind)) -> (List (Prod BinderName Ty))
              -> Term -> Option Ty
type_check _UU0394_ _UU0393_ term =
  case term of {
   Let r bs t ->
    case r of {
     NonRec ->
      case no_dup_fun (app (btvbs bs) (map fst _UU0394_)) of {
       True ->
        let {_UU0394_' = app (flatten (map binds_Delta bs)) _UU0394_} in
        let {xs = insert_deltas_bind_Gamma_nr bs _UU0394_} in
        bind (map_normaliser xs) (\bsgn ->
          let {_UU0393_' = app bsgn _UU0393_} in
          case bindings_well_formed_nonrec_check
                 (binding_well_formed_check type_check) _UU0394_ _UU0393_ bs of {
           True ->
            bind (type_check _UU0394_' _UU0393_' t) (\t0 ->
              case kind_check _UU0394_ t0 of {
               Some k ->
                case k of {
                 Kind_Base -> Some t0;
                 Kind_Arrow _ _ -> None};
               None -> None});
           False -> None});
       False -> None};
     Rec ->
      case no_dup_fun (app (btvbs bs) (map fst _UU0394_)) of {
       True ->
        case andb (no_dup_fun (btvbs bs)) (no_dup_fun (bvbs bs)) of {
         True ->
          let {_UU0394_' = app (flatten (map binds_Delta bs)) _UU0394_} in
          let {
           xs = insert_deltas_rec (flatten (map binds_Gamma bs)) _UU0394_'}
          in
          bind (map_normaliser xs) (\bsgn ->
            let {_UU0393_' = app bsgn _UU0393_} in
            case bindings_well_formed_rec_check
                   (binding_well_formed_check type_check _UU0394_' _UU0393_'
                     Rec) bs of {
             True ->
              bind (type_check _UU0394_' _UU0393_' t) (\t0 ->
                case kind_check _UU0394_ t0 of {
                 Some k ->
                  case k of {
                   Kind_Base -> Some t0;
                   Kind_Arrow _ _ -> None};
                 None -> None});
             False -> None});
         False -> None};
       False -> None}};
   Var x -> bind (lookup x _UU0393_) (\t -> normaliser_Jacco _UU0394_ t);
   TyAbs x k t ->
    case type_check (Cons (Pair x k) _UU0394_) _UU0393_ t of {
     Some t0 -> Some (Ty_Forall x k t0);
     None -> None};
   LamAbs x t1 t ->
    bind (normaliser_Jacco _UU0394_ t1) (\t1n ->
      case type_check _UU0394_ (Cons (Pair x t1n) _UU0393_) t of {
       Some t2 ->
        case kind_check _UU0394_ t1 of {
         Some k ->
          case k of {
           Kind_Base -> Some (Ty_Fun t1n t2);
           Kind_Arrow _ _ -> None};
         None -> None};
       None -> None});
   Apply t1 t2 ->
    case type_check _UU0394_ _UU0393_ t1 of {
     Some t ->
      case t of {
       Ty_Fun t3 t4 ->
        case type_check _UU0394_ _UU0393_ t2 of {
         Some t1' -> case ty_eqb t3 t1' of {
                      True -> Some t4;
                      False -> None};
         None -> None};
       _ -> None};
     None -> None};
   Constant0 c -> case c of {
                   ValueOf t _ -> Some (Ty_Builtin t)};
   Builtin f ->
    let {t = lookupBuiltinTy f} in
    bind (normaliser_Jacco _UU0394_ t) (\tn -> Some tn);
   TyInst t1 t2 ->
    case type_check _UU0394_ _UU0393_ t1 of {
     Some t ->
      case t of {
       Ty_Forall x k2 t3 ->
        case kind_check _UU0394_ t2 of {
         Some k2' ->
          case kind_check (Cons (Pair x k2) _UU0394_) t3 of {
           Some k ->
            case k of {
             Kind_Base ->
              case kind_eqb k2 k2' of {
               True ->
                bind (normaliser_Jacco _UU0394_ t2) (\t2n ->
                  bind (normaliser_Jacco _UU0394_ (substituteTCA x t2n t3))
                    (\t0n -> Some t0n));
               False -> None};
             Kind_Arrow _ _ -> None};
           None -> None};
         None -> None};
       _ -> None};
     None -> None};
   Error s' ->
    bind (normaliser_Jacco _UU0394_ s') (\s'n ->
      case kind_check _UU0394_ s' of {
       Some k -> case k of {
                  Kind_Base -> Some s'n;
                  Kind_Arrow _ _ -> None};
       None -> None});
   IWrap f t m ->
    case kind_check _UU0394_ t of {
     Some k ->
      case kind_check _UU0394_ f of {
       Some k0 ->
        case k0 of {
         Kind_Base -> None;
         Kind_Arrow k1 k2 ->
          case k1 of {
           Kind_Base -> None;
           Kind_Arrow k' k3 ->
            case k3 of {
             Kind_Base ->
              case k2 of {
               Kind_Base -> None;
               Kind_Arrow k'' k4 ->
                case k4 of {
                 Kind_Base ->
                  case type_check _UU0394_ _UU0393_ m of {
                   Some t0n ->
                    case andb (kind_eqb k k') (kind_eqb k k'') of {
                     True ->
                      bind (normaliser_Jacco _UU0394_ t) (\tn ->
                        bind (normaliser_Jacco _UU0394_ f) (\fn ->
                          bind
                            (normaliser_Jacco _UU0394_
                              (unwrapIFixFresh fn k tn)) (\t0n' ->
                            case ty_eqb t0n t0n' of {
                             True -> Some (Ty_IFix fn tn);
                             False -> None})));
                     False -> None};
                   None -> None};
                 Kind_Arrow _ _ -> None}};
             Kind_Arrow _ _ -> None}}};
       None -> None};
     None -> None};
   Unwrap m ->
    case type_check _UU0394_ _UU0393_ m of {
     Some t ->
      case t of {
       Ty_IFix f t0 ->
        case kind_check _UU0394_ t0 of {
         Some k ->
          case kind_check _UU0394_ f of {
           Some k0 ->
            case k0 of {
             Kind_Base -> None;
             Kind_Arrow k1 k2 ->
              case k1 of {
               Kind_Base -> None;
               Kind_Arrow k' k3 ->
                case k3 of {
                 Kind_Base ->
                  case k2 of {
                   Kind_Base -> None;
                   Kind_Arrow k'' k4 ->
                    case k4 of {
                     Kind_Base ->
                      case andb (kind_eqb k k') (kind_eqb k k'') of {
                       True ->
                        bind
                          (normaliser_Jacco _UU0394_
                            (unwrapIFixFresh f k t0)) (\t0n -> Some t0n);
                       False -> None};
                     Kind_Arrow _ _ -> None}};
                 Kind_Arrow _ _ -> None}}};
           None -> None};
         None -> None};
       _ -> None};
     None -> None};
   _ -> None}


